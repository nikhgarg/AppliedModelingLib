import AppliedModelingLib.Foundations.Probability.GaussianShiftHazardIntegral
import LG21TestOptionalPolicies.SelectedGaussianUpperTailFormula

/-!
# Literal selected-Gaussian cutoff boundary for LG21

The report-required cutoff equation must use the posterior induced by the
candidate's selected reporting branch.  This module reduces its boundary
payoff to an affine term plus a Gaussian hazard expectation, which gives a
checked continuity route for the literal equation.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology
open AppliedModelingLib Probability

/-- A standard-Gaussian hazard after an affine Gaussian input is integrable. -/
theorem lg21_integrable_standardGaussianHazard_affine_gaussianReal
    (inputSlope inputIntercept mean : ℝ) (variance : ℝ≥0) :
    Integrable
      (fun sample : ℝ =>
        standardGaussianHazard (inputSlope * sample + inputIntercept))
      (gaussianReal mean variance) := by
  let law : Measure ℝ := gaussianReal mean variance
  have hid : Integrable (fun sample : ℝ => sample) law := by
    change Integrable (fun sample : ℝ => sample)
      (gaussianReal mean variance)
    exact
      (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
  have haffine : Integrable
      (fun sample : ℝ => inputSlope * sample + inputIntercept) law := by
    exact (hid.const_mul inputSlope).add (integrable_const inputIntercept)
  have hbound : Integrable
      (fun sample : ℝ =>
        ‖inputSlope * sample + inputIntercept‖ +
          ‖standardGaussianHazard 0‖) law := by
    exact haffine.norm.add (integrable_const _)
  apply Integrable.mono' hbound
  · have haffineContinuous : Continuous
        (fun sample : ℝ => inputSlope * sample + inputIntercept) := by
        fun_prop
    exact
      (standardGaussianHazard_continuous.comp haffineContinuous).stronglyMeasurable
        |>.aestronglyMeasurable
  · filter_upwards with sample
    have hlip := standardGaussianHazard_lipschitzWith_one.norm_sub_le
      (inputSlope * sample + inputIntercept) 0
    calc
      ‖standardGaussianHazard (inputSlope * sample + inputIntercept)‖ ≤
          ‖standardGaussianHazard (inputSlope * sample + inputIntercept) -
              standardGaussianHazard 0‖ +
            ‖standardGaussianHazard 0‖ := by
              calc
                ‖standardGaussianHazard (inputSlope * sample + inputIntercept)‖ =
                    ‖(standardGaussianHazard (inputSlope * sample + inputIntercept) -
                        standardGaussianHazard 0) + standardGaussianHazard 0‖ := by
                      congr 1
                      ring
                _ ≤ ‖standardGaussianHazard (inputSlope * sample + inputIntercept) -
                      standardGaussianHazard 0‖ +
                    ‖standardGaussianHazard 0‖ := norm_add_le _ _
      _ ≤ ‖inputSlope * sample + inputIntercept‖ +
            ‖standardGaussianHazard 0‖ := by
              simpa using add_le_add_right hlip ‖standardGaussianHazard 0‖

/-- The posterior standard deviation in the one-score Gaussian update. -/
def lg21GaussianSignalPosteriorScale
    (priorVariance noiseVariance : ℝ) : ℝ :=
  Real.sqrt (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ)

/--
The cutoff's literal reporter payoff evaluated at the same latent cutoff,
written after translating the additive test noise to a centered Gaussian.
-/
def lg21SelectedGaussianCutoffBoundaryPayoff
    (priorMean priorVariance noiseVariance cutoff : ℝ) : ℝ :=
  let responseSlope := gaussianSignalWeight priorVariance noiseVariance
  let responseIntercept :=
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean
  let posteriorScale :=
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance
  responseIntercept + responseSlope * cutoff +
    posteriorScale *
      gaussianShiftHazardIntegral
        (gaussianReal 0 noiseVariance.toNNReal)
        ((1 - responseSlope) / posteriorScale)
        (fun noise =>
          -responseIntercept / posteriorScale -
            responseSlope * noise / posteriorScale)
        cutoff

/-- The literal selected-Gaussian cutoff boundary payoff is continuous. -/
theorem lg21SelectedGaussianCutoffBoundaryPayoff_continuous
    (priorMean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    Continuous
      (lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance) := by
  let responseSlope := gaussianSignalWeight priorVariance noiseVariance
  let responseIntercept :=
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean
  let posteriorScale :=
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let coefficient : ℝ := (1 - responseSlope) / posteriorScale
  let shift : ℝ → ℝ := fun noise =>
    -responseIntercept / posteriorScale -
      responseSlope * noise / posteriorScale
  have hintegrable : ∀ cutoff,
      Integrable (fun noise =>
        standardGaussianHazard (coefficient * cutoff + shift noise)) noiseLaw := by
    intro cutoff
    have hbase := lg21_integrable_standardGaussianHazard_affine_gaussianReal
      (-responseSlope / posteriorScale)
      (coefficient * cutoff - responseIntercept / posteriorScale)
      0 noiseVariance.toNNReal
    change Integrable (fun noise =>
      standardGaussianHazard (coefficient * cutoff + shift noise)) noiseLaw
    convert hbase using 1
    ext noise
    congr 1
    dsimp [coefficient, shift]
    ring
  have hhazard : Continuous
      (gaussianShiftHazardIntegral noiseLaw coefficient shift) :=
    gaussianShiftHazardIntegral_continuous
      noiseLaw coefficient shift hintegrable
  have haffine : Continuous (fun cutoff : ℝ =>
      responseIntercept + responseSlope * cutoff) := by
    fun_prop
  change Continuous (fun cutoff : ℝ =>
    responseIntercept + responseSlope * cutoff +
      posteriorScale *
        gaussianShiftHazardIntegral noiseLaw coefficient shift cutoff)
  exact haffine.add (continuous_const.mul hhazard)

/--
The literal selected-reporter boundary payoff tends to `-∞` at a low cutoff.
The selected restriction contributes a positive-coefficient hazard expectation;
that term vanishes at the low endpoint by dominated convergence, while the
unselected affine posterior term tends to `-∞`.
-/
theorem lg21SelectedGaussianCutoffBoundaryPayoff_tendsto_atBot
    (priorMean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    Tendsto
      (lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance)
      atBot atBot := by
  let responseSlope := gaussianSignalWeight priorVariance noiseVariance
  let responseIntercept :=
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean
  let posteriorScale :=
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let coefficient : ℝ := (1 - responseSlope) / posteriorScale
  let shift : ℝ → ℝ := fun noise =>
    -responseIntercept / posteriorScale - responseSlope * noise / posteriorScale
  have hposteriorScale_pos : 0 < posteriorScale := by
    dsimp [posteriorScale, lg21GaussianSignalPosteriorScale]
    apply Real.sqrt_pos.2
    exact lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hresponseSlope_pos : 0 < responseSlope := by
    dsimp [responseSlope, gaussianSignalWeight]
    exact div_pos hpriorVariance (add_pos hpriorVariance hnoiseVariance)
  have hresponseSlope_lt_one : responseSlope < 1 := by
    dsimp [responseSlope, gaussianSignalWeight]
    rw [div_lt_one₀ (add_pos hpriorVariance hnoiseVariance)]
    linarith
  have hcoefficient : 0 < coefficient := by
    exact div_pos (sub_pos.mpr hresponseSlope_lt_one) hposteriorScale_pos
  have hshiftMeasurable : AEStronglyMeasurable shift noiseLaw := by
    dsimp [shift]
    fun_prop
  have hshiftHazardIntegrable : Integrable
      (fun noise => standardGaussianHazard (shift noise)) noiseLaw := by
    have hbase := lg21_integrable_standardGaussianHazard_affine_gaussianReal
      (-responseSlope / posteriorScale) (-responseIntercept / posteriorScale)
      0 noiseVariance.toNNReal
    change Integrable
      (fun noise => standardGaussianHazard (shift noise)) noiseLaw
    convert hbase using 1
    ext noise
    congr 1
    dsimp [shift]
    ring
  have hhazard : Tendsto
      (gaussianShiftHazardIntegral noiseLaw coefficient shift)
      atBot (𝓝 0) :=
    gaussianShiftHazardIntegral_tendsto_atBot_zero
      noiseLaw coefficient shift hcoefficient hshiftMeasurable hshiftHazardIntegrable
  have haffine : Tendsto
      (fun cutoff : ℝ => responseIntercept + responseSlope * cutoff)
      atBot atBot := by
    have hlinear : Tendsto
        (fun cutoff : ℝ => responseSlope * cutoff + responseIntercept)
        atBot atBot :=
      ((Filter.tendsto_const_mul_atBot_of_pos hresponseSlope_pos).2 tendsto_id).atBot_add
        tendsto_const_nhds
    convert hlinear using 1
    ext cutoff
    ring
  have hcorrection : Tendsto
      (fun cutoff : ℝ => posteriorScale *
        gaussianShiftHazardIntegral noiseLaw coefficient shift cutoff)
      atBot (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hhazard)
  have hsum := haffine.atBot_add hcorrection
  simpa [lg21SelectedGaussianCutoffBoundaryPayoff, responseSlope,
    responseIntercept, posteriorScale, noiseLaw, coefficient, shift] using hsum

set_option maxHeartbeats 1200000 in
/--
Translating the Gaussian prior mean translates the literal selected-reporter
boundary payoff by the same amount.  Consequently the cutoff equation can use
one common offset from every public-base conditional mean.
-/
theorem lg21SelectedGaussianCutoffBoundaryPayoff_translate
    (priorMean priorVariance noiseVariance gap : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    lg21SelectedGaussianCutoffBoundaryPayoff
      priorMean priorVariance noiseVariance (priorMean + gap) =
      priorMean + lg21SelectedGaussianCutoffBoundaryPayoff
        0 priorVariance noiseVariance gap := by
  let responseSlope := gaussianSignalWeight priorVariance noiseVariance
  let responseIntercept :=
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean
  let posteriorScale :=
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let coefficient : ℝ := (1 - responseSlope) / posteriorScale
  let shiftedArgument : ℝ → ℝ := fun noise =>
    -responseIntercept / posteriorScale - responseSlope * noise / posteriorScale
  let centeredArgument : ℝ → ℝ := fun noise =>
    -(responseSlope * noise / posteriorScale)
  have hposteriorScale_pos : 0 < posteriorScale := by
    dsimp [posteriorScale, lg21GaussianSignalPosteriorScale]
    apply Real.sqrt_pos.2
    exact lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hsumWeights :
      gaussianSignalPriorWeight priorVariance noiseVariance + responseSlope = 1 := by
    dsimp [responseSlope, gaussianSignalPriorWeight, gaussianSignalWeight]
    field_simp [ne_of_gt (add_pos hpriorVariance hnoiseVariance)]
    ring
  have hcoefficientNumerator : 1 - responseSlope =
      gaussianSignalPriorWeight priorVariance noiseVariance := by
    linarith
  have hintegral :
      gaussianShiftHazardIntegral noiseLaw coefficient shiftedArgument
        (priorMean + gap) =
      gaussianShiftHazardIntegral noiseLaw coefficient centeredArgument gap := by
    unfold gaussianShiftHazardIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun noise => by
      apply congrArg standardGaussianHazard
      dsimp [coefficient, shiftedArgument, centeredArgument,
        responseIntercept]
      rw [hcoefficientNumerator]
      field_simp [ne_of_gt hposteriorScale_pos]
      ring_nf
  simp only [lg21SelectedGaussianCutoffBoundaryPayoff, mul_zero, neg_zero,
    zero_div, zero_add, zero_sub]
  change responseIntercept + responseSlope * (priorMean + gap) +
      posteriorScale *
        gaussianShiftHazardIntegral noiseLaw coefficient shiftedArgument
          (priorMean + gap) =
    priorMean + (responseSlope * gap +
      posteriorScale *
        gaussianShiftHazardIntegral noiseLaw coefficient centeredArgument gap)
  rw [hintegral]
  have hresponseIntercept : responseIntercept =
      gaussianSignalPriorWeight priorVariance noiseVariance * priorMean := rfl
  rw [hresponseIntercept]
  calc
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean +
        responseSlope * (priorMean + gap) +
        posteriorScale *
          gaussianShiftHazardIntegral noiseLaw coefficient centeredArgument gap =
      (gaussianSignalPriorWeight priorVariance noiseVariance + responseSlope) *
          priorMean + responseSlope * gap +
        posteriorScale *
          gaussianShiftHazardIntegral noiseLaw coefficient centeredArgument gap := by
            ring
    _ = priorMean + (responseSlope * gap +
        posteriorScale *
          gaussianShiftHazardIntegral noiseLaw coefficient centeredArgument gap) := by
            rw [hsumWeights]
            ring

/--
The literal posterior PBO on a selected upper tail has the explicit affine
posterior-plus-hazard form at every observed score.
-/
def lg21SelectedGaussianUpperTailReporterPBO
    (priorMean priorVariance noiseVariance cutoff observedScore : ℝ) : ℝ :=
  gaussianSignalWeight priorVariance noiseVariance * observedScore +
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean +
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance *
      standardGaussianHazard
        ((cutoff -
          (gaussianSignalWeight priorVariance noiseVariance * observedScore +
            gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)) /
          lg21GaussianSignalPosteriorScale priorVariance noiseVariance)

theorem lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
    (priorMean priorVariance noiseVariance observedScore cutoff : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            priorMean priorVariance noiseVariance observedScore)
          (Set.Ici cutoff)) =
      lg21SelectedGaussianUpperTailReporterPBO
        priorMean priorVariance noiseVariance cutoff observedScore := by
  simpa [lg21GaussianSignalPosteriorScaleLaw,
    lg21GaussianScaleLawOfNNRealVariance,
    lg21SelectedGaussianUpperTailReporterPBO,
    lg21GaussianSignalPosteriorScale, GaussianScaleLaw.standardize] using
    (lg21_gaussianSignalPosterior_selectedUpperTailMean_eq
      priorMean priorVariance noiseVariance observedScore cutoff
      hpriorVariance hnoiseVariance)

/-- The explicit selected reporter PBO is integrable under every Gaussian test-score shift. -/
theorem lg21SelectedGaussianUpperTailReporterPBO_integrable
    (priorMean priorVariance noiseVariance cutoff skill : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    Integrable
      (lg21SelectedGaussianUpperTailReporterPBO
        priorMean priorVariance noiseVariance cutoff)
      (gaussianReal skill noiseVariance.toNNReal) := by
  let responseSlope := gaussianSignalWeight priorVariance noiseVariance
  let responseIntercept :=
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean
  let posteriorScale :=
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance
  have hposteriorScale_pos : 0 < posteriorScale := by
    dsimp [posteriorScale, lg21GaussianSignalPosteriorScale]
    apply Real.sqrt_pos.2
    exact lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hposteriorScale_ne : posteriorScale ≠ 0 := ne_of_gt hposteriorScale_pos
  have hhazard := lg21_integrable_standardGaussianHazard_affine_gaussianReal
    (-responseSlope / posteriorScale)
    ((cutoff - responseIntercept) / posteriorScale)
    skill noiseVariance.toNNReal
  have hselectedHazard : Integrable (fun observedScore : ℝ =>
      standardGaussianHazard
        ((cutoff -
          (responseSlope * observedScore + responseIntercept)) /
          posteriorScale))
      (gaussianReal skill noiseVariance.toNNReal) := by
    convert hhazard using 1
    ext observedScore
    congr 1
    field_simp [hposteriorScale_ne]
    ring
  have haffine : Integrable (fun observedScore : ℝ =>
      responseSlope * observedScore + responseIntercept)
      (gaussianReal skill noiseVariance.toNNReal) := by
    exact
      (((ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl).const_mul responseSlope).add
          (integrable_const responseIntercept)
  change Integrable (fun observedScore : ℝ =>
    responseSlope * observedScore + responseIntercept +
      posteriorScale *
        standardGaussianHazard
          ((cutoff -
            (responseSlope * observedScore + responseIntercept)) /
            posteriorScale))
      (gaussianReal skill noiseVariance.toNNReal)
  exact haffine.add (hselectedHazard.const_mul posteriorScale)

/-- Every score-contingent selected upper-tail posterior exceeds its cutoff. -/
theorem lg21SelectedGaussianUpperTailReporterPBO_gt_cutoff
    (priorMean priorVariance noiseVariance cutoff observedScore : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    cutoff < lg21SelectedGaussianUpperTailReporterPBO
      priorMean priorVariance noiseVariance cutoff observedScore := by
  simpa [lg21SelectedGaussianUpperTailReporterPBO,
    lg21GaussianSignalPosteriorScaleLaw,
    lg21GaussianScaleLawOfNNRealVariance,
    lg21GaussianSignalPosteriorScale,
    GaussianHazardCertificate.normalUpperTailMean,
    standardGaussianHazardInverseCertificate,
    GaussianScaleLaw.standardize] using
    (standardGaussian_normalUpperTailMean_gt_threshold
      (lg21GaussianSignalPosteriorScaleLaw
        priorMean priorVariance noiseVariance observedScore
        hpriorVariance hnoiseVariance)
      cutoff)

/--
At the latent cutoff itself, the literal expected selected-posterior payoff
is exactly `lg21SelectedGaussianCutoffBoundaryPayoff`.  The proof only changes
coordinates from the score law `cutoff + noise` to centered test noise.
-/
theorem lg21SelectedGaussianCutoffBoundaryPayoff_eq_actual
    (priorMean priorVariance noiseVariance cutoff : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (∫ observedScore,
      ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            priorMean priorVariance noiseVariance observedScore)
          (Set.Ici cutoff)
      ∂gaussianReal cutoff noiseVariance.toNNReal) =
      lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance cutoff := by
  let responseSlope := gaussianSignalWeight priorVariance noiseVariance
  let responseIntercept :=
    gaussianSignalPriorWeight priorVariance noiseVariance * priorMean
  let posteriorScale :=
    lg21GaussianSignalPosteriorScale priorVariance noiseVariance
  let baseNoiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let coefficient : ℝ := (1 - responseSlope) / posteriorScale
  let shift : ℝ → ℝ := fun noise =>
    -responseIntercept / posteriorScale -
      responseSlope * noise / posteriorScale
  have hposteriorScale_pos : 0 < posteriorScale := by
    dsimp [posteriorScale, lg21GaussianSignalPosteriorScale]
    apply Real.sqrt_pos.2
    exact lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hposteriorScale_ne : posteriorScale ≠ 0 := ne_of_gt hposteriorScale_pos
  have hhazardIntegrable :
      Integrable (fun noise =>
        standardGaussianHazard (coefficient * cutoff + shift noise))
        baseNoiseLaw := by
    have hbase := lg21_integrable_standardGaussianHazard_affine_gaussianReal
      (-responseSlope / posteriorScale)
      (coefficient * cutoff - responseIntercept / posteriorScale)
      0 noiseVariance.toNNReal
    change Integrable (fun noise =>
      standardGaussianHazard (coefficient * cutoff + shift noise))
      baseNoiseLaw
    convert hbase using 1
    ext noise
    congr 1
    dsimp [coefficient, shift]
    ring
  have hnoiseIntegrable :
      Integrable (fun noise : ℝ => responseSlope * noise) baseNoiseLaw := by
    change Integrable (fun noise : ℝ => responseSlope * noise)
      (gaussianReal 0 noiseVariance.toNNReal)
    exact
      ((ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl).const_mul responseSlope
  have hnoiseMean :
      (∫ noise, responseSlope * noise ∂baseNoiseLaw) = 0 := by
    change (∫ noise, responseSlope * noise ∂
      gaussianReal 0 noiseVariance.toNNReal) = 0
    rw [MeasureTheory.integral_const_mul, integral_id_gaussianReal]
    ring
  have hpoint : ∀ observedScore,
      (∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            priorMean priorVariance noiseVariance observedScore)
          (Set.Ici cutoff)) =
        responseSlope * observedScore + responseIntercept +
          posteriorScale *
            standardGaussianHazard
              ((cutoff -
                (responseSlope * observedScore + responseIntercept)) /
                posteriorScale) := by
    intro observedScore
    simpa [responseSlope, responseIntercept, posteriorScale] using
      (lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
        priorMean priorVariance noiseVariance observedScore cutoff
        hpriorVariance hnoiseVariance)
  calc
    (∫ observedScore,
      ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            priorMean priorVariance noiseVariance observedScore)
          (Set.Ici cutoff)
      ∂gaussianReal cutoff noiseVariance.toNNReal) =
        ∫ observedScore,
          responseSlope * observedScore + responseIntercept +
            posteriorScale *
              standardGaussianHazard
                ((cutoff -
                  (responseSlope * observedScore + responseIntercept)) /
                  posteriorScale)
          ∂gaussianReal cutoff noiseVariance.toNNReal := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = ∫ noise,
          responseSlope * (noise + cutoff) + responseIntercept +
            posteriorScale *
              standardGaussianHazard
                ((cutoff -
                  (responseSlope * (noise + cutoff) + responseIntercept)) /
                  posteriorScale)
          ∂baseNoiseLaw := by
            have hmap :
                baseNoiseLaw.map (fun noise : ℝ => noise + cutoff) =
                  gaussianReal cutoff noiseVariance.toNNReal := by
              simpa [baseNoiseLaw] using
                (ProbabilityTheory.gaussianReal_map_add_const
                  (μ := (0 : ℝ)) (v := noiseVariance.toNNReal) cutoff)
            have hmeasurable : AEStronglyMeasurable
                (fun observedScore : ℝ =>
                  responseSlope * observedScore + responseIntercept +
                    posteriorScale *
                      standardGaussianHazard
                        ((cutoff -
                          (responseSlope * observedScore + responseIntercept)) /
                          posteriorScale))
                (baseNoiseLaw.map (fun noise : ℝ => noise + cutoff)) := by
              have hcontinuous : Continuous
                  (fun observedScore : ℝ =>
                    responseSlope * observedScore + responseIntercept +
                      posteriorScale *
                        standardGaussianHazard
                          ((cutoff -
                            (responseSlope * observedScore + responseIntercept)) /
                            posteriorScale)) := by
                have haffine : Continuous (fun observedScore : ℝ =>
                    responseSlope * observedScore + responseIntercept) := by
                  fun_prop
                have hargument : Continuous (fun observedScore : ℝ =>
                    (cutoff -
                      (responseSlope * observedScore + responseIntercept)) /
                      posteriorScale) := by
                  fun_prop
                exact haffine.add
                  (continuous_const.mul
                    (standardGaussianHazard_continuous.comp hargument))
              exact hcontinuous.stronglyMeasurable.aestronglyMeasurable
            rw [← hmap, MeasureTheory.integral_map
              (by fun_prop : AEMeasurable (fun noise : ℝ => noise + cutoff)
                baseNoiseLaw)
              hmeasurable]
    _ = ∫ noise,
          responseSlope * noise +
            (responseIntercept + responseSlope * cutoff +
            posteriorScale *
              standardGaussianHazard (coefficient * cutoff + shift noise))
          ∂baseNoiseLaw := by
            apply integral_congr_ae
            filter_upwards with noise
            have harg :
                (cutoff -
                  (responseSlope * (noise + cutoff) + responseIntercept)) /
                    posteriorScale =
                  coefficient * cutoff + shift noise := by
              dsimp [coefficient, shift]
              field_simp [hposteriorScale_ne]
              ring
            rw [harg]
            ring
    _ = responseIntercept + responseSlope * cutoff +
        posteriorScale *
          gaussianShiftHazardIntegral baseNoiseLaw coefficient shift cutoff := by
            let noiseTerm : ℝ → ℝ := fun noise => responseSlope * noise
            let constantTerm : ℝ → ℝ := fun _noise =>
              responseIntercept + responseSlope * cutoff
            let hazardTerm : ℝ → ℝ := fun noise =>
              posteriorScale *
                standardGaussianHazard (coefficient * cutoff + shift noise)
            have hnoiseTermIntegrable : Integrable noiseTerm baseNoiseLaw := by
              simpa [noiseTerm] using hnoiseIntegrable
            have hconstantTermIntegrable :
                Integrable constantTerm baseNoiseLaw := by
              simpa [constantTerm] using
                (integrable_const (responseIntercept + responseSlope * cutoff))
            have hhazardTermIntegrable : Integrable hazardTerm baseNoiseLaw := by
              simpa [hazardTerm] using
                (hhazardIntegrable.const_mul posteriorScale)
            have hnoiseTermMean : (∫ noise, noiseTerm noise ∂baseNoiseLaw) = 0 := by
              simpa [noiseTerm] using hnoiseMean
            change (∫ noise,
              (noiseTerm + (constantTerm + hazardTerm)) noise ∂baseNoiseLaw) = _
            calc
              (∫ noise,
                (noiseTerm + (constantTerm + hazardTerm)) noise ∂baseNoiseLaw) =
                  (∫ noise, noiseTerm noise ∂baseNoiseLaw) +
                    ∫ noise, (constantTerm + hazardTerm) noise ∂baseNoiseLaw := by
                      exact MeasureTheory.integral_add hnoiseTermIntegrable
                        (hconstantTermIntegrable.add hhazardTermIntegrable)
              _ = 0 + ∫ noise, (constantTerm + hazardTerm) noise ∂baseNoiseLaw := by
                    rw [hnoiseTermMean]
              _ = 0 + ((∫ noise, constantTerm noise ∂baseNoiseLaw) +
                    ∫ noise, hazardTerm noise ∂baseNoiseLaw) := by
                      congr 1
                      exact MeasureTheory.integral_add hconstantTermIntegrable
                        hhazardTermIntegrable
              _ = responseIntercept + responseSlope * cutoff +
                    posteriorScale *
                      gaussianShiftHazardIntegral
                        baseNoiseLaw coefficient shift cutoff := by
                      simp only [constantTerm, hazardTerm,
                        MeasureTheory.integral_const,
                        MeasureTheory.integral_const_mul,
                        MeasureTheory.measureReal_def, measure_univ,
                        ENNReal.toReal_one, one_smul, zero_add,
                        gaussianShiftHazardIntegral]
    _ = lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance cutoff := by
          rfl

/-- The literal selected reporter's expected payoff at its own cutoff is strictly above it. -/
theorem lg21SelectedGaussianCutoffBoundaryPayoff_gt_cutoff
    (priorMean priorVariance noiseVariance cutoff : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    cutoff < lg21SelectedGaussianCutoffBoundaryPayoff
      priorMean priorVariance noiseVariance cutoff := by
  let scoreLaw : Measure ℝ := gaussianReal cutoff noiseVariance.toNNReal
  letI : IsProbabilityMeasure scoreLaw := by
    dsimp [scoreLaw]
    infer_instance
  have hreportIntegrable : Integrable
      (lg21SelectedGaussianUpperTailReporterPBO
        priorMean priorVariance noiseVariance cutoff) scoreLaw := by
    simpa [scoreLaw] using
      (lg21SelectedGaussianUpperTailReporterPBO_integrable
        priorMean priorVariance noiseVariance cutoff cutoff
        hpriorVariance hnoiseVariance)
  have hstrict :
      (∫ observedScore, cutoff ∂scoreLaw) <
        ∫ observedScore,
          lg21SelectedGaussianUpperTailReporterPBO
            priorMean priorVariance noiseVariance cutoff observedScore
          ∂scoreLaw := by
    apply lg21_integral_lt_integral_of_ae_lt_probability
      scoreLaw (integrable_const cutoff) hreportIntegrable
    exact Filter.Eventually.of_forall fun observedScore =>
      lg21SelectedGaussianUpperTailReporterPBO_gt_cutoff
        priorMean priorVariance noiseVariance cutoff observedScore
        hpriorVariance hnoiseVariance
  have hactual :
      (∫ observedScore,
        ∫ latentSkill, latentSkill ∂
          lg21NormalizedRestriction
            (gaussianSignalPosteriorKernel
              priorMean priorVariance noiseVariance observedScore)
            (Set.Ici cutoff)
        ∂scoreLaw) =
        ∫ observedScore,
          lg21SelectedGaussianUpperTailReporterPBO
            priorMean priorVariance noiseVariance cutoff observedScore
          ∂scoreLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun observedScore =>
      lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
        priorMean priorVariance noiseVariance observedScore cutoff
        hpriorVariance hnoiseVariance
  calc
    cutoff = ∫ observedScore, cutoff ∂scoreLaw := by
      rw [MeasureTheory.integral_const]
      simp [scoreLaw]
    _ < ∫ observedScore,
          lg21SelectedGaussianUpperTailReporterPBO
            priorMean priorVariance noiseVariance cutoff observedScore
          ∂scoreLaw := hstrict
    _ = ∫ observedScore,
          ∫ latentSkill, latentSkill ∂
            lg21NormalizedRestriction
              (gaussianSignalPosteriorKernel
                priorMean priorVariance noiseVariance observedScore)
              (Set.Ici cutoff)
          ∂scoreLaw := hactual.symm
    _ = lg21SelectedGaussianCutoffBoundaryPayoff
          priorMean priorVariance noiseVariance cutoff := by
          simpa [scoreLaw] using
            (lg21SelectedGaussianCutoffBoundaryPayoff_eq_actual
              priorMean priorVariance noiseVariance cutoff
              hpriorVariance hnoiseVariance)

/-- A no-report PBO below a finite cutoff yields the literal high endpoint sign. -/
theorem lg21SelectedGaussianCutoff_high_sign_of_noReport_lt_cutoff
    (priorMean priorVariance noiseVariance cutoff noReportPBO : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hnoReport : noReportPBO < cutoff) :
    noReportPBO < lg21SelectedGaussianCutoffBoundaryPayoff
      priorMean priorVariance noiseVariance cutoff :=
  hnoReport.trans
    (lg21SelectedGaussianCutoffBoundaryPayoff_gt_cutoff
      priorMean priorVariance noiseVariance cutoff
      hpriorVariance hnoiseVariance)

/--
The literal selected-posterior payoff gap at a cutoff.  `noReportPBO` is left
as an explicit function because the source bridge must derive it from the
candidate's actual `X = 0` population, including the hidden no-access
component when access is unobserved.
-/
def lg21SelectedGaussianCutoffGap
    (priorMean priorVariance noiseVariance : ℝ)
    (noReportPBO : ℝ → ℝ) (cutoff : ℝ) : ℝ :=
  lg21SelectedGaussianCutoffBoundaryPayoff
    priorMean priorVariance noiseVariance cutoff - noReportPBO cutoff

/-- The literal selected-posterior gap is continuous when the actual no-report PBO is. -/
theorem lg21SelectedGaussianCutoffGap_continuous
    (priorMean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noReportPBO : ℝ → ℝ) (hnoReportPBO : Continuous noReportPBO) :
    Continuous
      (lg21SelectedGaussianCutoffGap
        priorMean priorVariance noiseVariance noReportPBO) := by
  unfold lg21SelectedGaussianCutoffGap
  exact (lg21SelectedGaussianCutoffBoundaryPayoff_continuous
    priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance).sub
      hnoReportPBO

/--
Finite literal endpoint signs yield a selected-posterior cutoff root.  The
sign premises deliberately concern the actual no-report PBO rather than an
unselected affine posterior expression.
-/
theorem lg21SelectedGaussianCutoff_exists_root_of_finite_signs
    (priorMean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noReportPBO : ℝ → ℝ) (hnoReportPBO : Continuous noReportPBO)
    {low high : ℝ} (hlowHigh : low < high)
    (hlow :
      lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance low < noReportPBO low)
    (hhigh :
      noReportPBO high <
        lg21SelectedGaussianCutoffBoundaryPayoff
          priorMean priorVariance noiseVariance high) :
    ∃ cutoff ∈ Set.Icc low high,
      lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance cutoff = noReportPBO cutoff := by
  let gap := lg21SelectedGaussianCutoffGap
    priorMean priorVariance noiseVariance noReportPBO
  have hcontinuous : Continuous gap := by
    exact lg21SelectedGaussianCutoffGap_continuous
      priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance
      noReportPBO hnoReportPBO
  have hlowGap : gap low < 0 := by
    exact sub_neg.mpr hlow
  have hhighGap : 0 < gap high := by
    exact sub_pos.mpr hhigh
  have hzero : (0 : ℝ) ∈ Set.Icc (gap low) (gap high) :=
    ⟨le_of_lt hlowGap, le_of_lt hhighGap⟩
  rcases intermediate_value_Icc (le_of_lt hlowHigh)
      hcontinuous.continuousOn hzero with ⟨cutoff, hcutoff, hroot⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  exact sub_eq_zero.mp hroot

/--
For a report-required candidate that reports exactly its selected upper tail,
the literal posterior formula gives strict monotonicity of the pre-score
payoff in latent skill.  This is the action-closure ingredient for the
hidden-access cutoff construction: it is stated in payoff space and does not
assume that a source action function has any particular name.
-/
theorem lg21_reportRequired_takeExpectedPayoff_strictMono_of_literalSelectedUpperTailPBO
    {Base : Type*}
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) (base : Base)
    (priorMean priorVariance noiseVariance cutoff : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (htestLaw : ∀ skill,
      E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal)
    (hreportedPBO : ∀ observedScore,
      E.reportedPayoff base observedScore =
        lg21SelectedGaussianUpperTailReporterPBO
          priorMean priorVariance noiseVariance cutoff observedScore) :
    StrictMono (fun skill =>
      lg21ReportRequiredSequentialTakeExpectedPayoff E skill base) := by
  apply lg21_reportRequired_takeExpectedPayoff_strictMono_of_selectedGaussianPBO
    E base priorMean priorVariance noiseVariance (Set.Ici cutoff)
    hpriorVariance hnoiseVariance measurableSet_Ici
  · have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
    exact lt_of_lt_of_le
      (lg21_gaussianReal_Ioi_pos priorMean cutoff hpriorVarianceNN)
      (measure_mono Set.Ioi_subset_Ici_self)
  · exact htestLaw
  · intro observedScore
    exact (hreportedPBO observedScore).trans
      (lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
        priorMean priorVariance noiseVariance observedScore cutoff
        hpriorVariance hnoiseVariance).symm
  · intro skill
    refine (lg21SelectedGaussianUpperTailReporterPBO_integrable
      priorMean priorVariance noiseVariance cutoff skill
      hpriorVariance hnoiseVariance).congr ?_
    exact Filter.Eventually.of_forall fun observedScore =>
      (hreportedPBO observedScore).symm

end

end LG21TestOptionalPolicies

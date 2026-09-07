import KR21Monoculture.GumbelVarianceTransport
import KR21Monoculture.PositiveScaleGumbelTransport
import KR21Monoculture.UnitVarianceNormalization

/-!
# Literal unit-variance Gumbel source model for KR21

Section 3.1 first fixes an iid noise law `E` of unit variance and then ranks
`value i + epsilon i / theta`.  This module gives that source-facing model for
the literal common-location Gumbel construction.  The only analytic premise is
spelled out at each variance endpoint:

`Var[-log T] = pi^2 / 6` for `T ~ Exp(1)`.

It is not inferred from the word "Gumbel".  Conditional on that special-value
identity, the noise vector is an actual iid product law with unit-variance
coordinates, its score map has exactly the source form, and its ranking PMF is
the independently constructed Plackett--Luce PMF at `theta / (sqrt 6 / pi)`.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

noncomputable section

/-- The literal common-location Gumbel innovation law at the displayed scale
`sqrt(6) / pi`.  Its unit-variance status is proved below only from the
explicit base-variance identity. -/
noncomputable def sourceUnitVarianceGumbelMeasure (location : ℝ) : Measure ℝ :=
  commonLocationPositiveScaleGumbelMeasure location unitVarianceGumbelScale

/-- The iid finite noise-vector law used by the source RUM.  Equality to this
product law is the formal iid assertion, rather than a naming convention. -/
noncomputable def sourceUnitVarianceGumbelNoiseLaw {n : ℕ}
    (location : ℝ) : Measure (Candidate n → ℝ) :=
  Measure.pi (fun _ : Candidate n => sourceUnitVarianceGumbelMeasure location)

theorem sourceUnitVarianceGumbelMeasure_isProbabilityMeasure (location : ℝ) :
    IsProbabilityMeasure (sourceUnitVarianceGumbelMeasure location) := by
  unfold sourceUnitVarianceGumbelMeasure
  exact commonLocationPositiveScaleGumbelMeasure_isProbabilityMeasure
    location unitVarianceGumbelScale

theorem sourceUnitVarianceGumbelNoiseLaw_isProbabilityMeasure {n : ℕ}
    (location : ℝ) :
    IsProbabilityMeasure (sourceUnitVarianceGumbelNoiseLaw (n := n) location) := by
  letI : ∀ _ : Candidate n,
      IsProbabilityMeasure (sourceUnitVarianceGumbelMeasure location) := fun _ =>
    sourceUnitVarianceGumbelMeasure_isProbabilityMeasure location
  unfold sourceUnitVarianceGumbelNoiseLaw
  infer_instance

/-- The literal source score expression `value i + epsilon i / theta`. -/
noncomputable def sourceUnitVarianceGumbelScores {n : ℕ}
    (theta : ℝ) (value epsilon : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => value i + epsilon i / theta

/-- The source ranking map applied to a fixed iid noise vector. -/
noncomputable def sourceUnitVarianceGumbelRank {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    (Candidate n → ℝ) → Ranking n :=
  fun epsilon => rankByScore (sourceUnitVarianceGumbelScores theta value epsilon)

theorem measurable_sourceUnitVarianceGumbelRank {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    Measurable (sourceUnitVarianceGumbelRank theta value) := by
  unfold sourceUnitVarianceGumbelRank sourceUnitVarianceGumbelScores
  exact paper_appendixA_scaledNoise_rankByScore_measurable
    (fun epsilon : Candidate n → ℝ => fun i => epsilon i)
    (fun i => measurable_pi_apply i) value theta

/-- The finite ranking PMF of the literal source-form RUM under its iid noise
law. -/
noncomputable def sourceUnitVarianceGumbelRUMRankingPMF {n : ℕ}
    (location theta : ℝ) (value : Candidate n → ℝ) : PMF (Ranking n) := by
  letI : IsProbabilityMeasure (sourceUnitVarianceGumbelNoiseLaw (n := n) location) :=
    sourceUnitVarianceGumbelNoiseLaw_isProbabilityMeasure location
  exact rankingPMFOfMeasure
    (sourceUnitVarianceGumbelNoiseLaw (n := n) location)
    (sourceUnitVarianceGumbelRank theta value)
    (measurable_sourceUnitVarianceGumbelRank theta value)

/-- The common-location displayed-scale innovation is measurable coordinatewise. -/
theorem measurable_commonLocationPositiveScaleGumbelNoise {n : ℕ}
    (location s : ℝ) :
    Measurable (commonLocationPositiveScaleGumbelNoise (n := n) location s) := by
  apply measurable_pi_lambda _
  intro i
  exact (measurable_commonLocationPositiveScaleGumbelInnovation location s).comp
    (measurable_pi_apply i)

/-- The actual exponential-arrival construction has exactly the iid product
noise law declared for the source RUM. -/
theorem commonLocationUnitVarianceGumbelNoise_law {n : ℕ}
    (location : ℝ) :
    Measure.map
        (commonLocationPositiveScaleGumbelNoise (n := n)
          location unitVarianceGumbelScale)
        (gumbelArrivalLaw n) =
      sourceUnitVarianceGumbelNoiseLaw (n := n) location := by
  simpa only [sourceUnitVarianceGumbelNoiseLaw, sourceUnitVarianceGumbelMeasure]
    using commonLocationPositiveScaleGumbelNoise_law
      (n := n) location unitVarianceGumbelScale

/-- The RUM based on the literal iid product law is the same random ranking
experiment as the exponential-arrival Gumbel construction. -/
theorem commonLocationPositiveScaleGumbelRUMRankingPMF_eq_sourceUnitVarianceGumbel
    {n : ℕ} (location theta : ℝ) (value : Candidate n → ℝ) :
    commonLocationPositiveScaleGumbelRUMRankingPMF
      location unitVarianceGumbelScale theta value =
      sourceUnitVarianceGumbelRUMRankingPMF location theta value := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  letI : IsProbabilityMeasure (sourceUnitVarianceGumbelNoiseLaw (n := n) location) :=
    sourceUnitVarianceGumbelNoiseLaw_isProbabilityMeasure location
  let noise : (Candidate n → ℝ) → Candidate n → ℝ :=
    commonLocationPositiveScaleGumbelNoise location unitVarianceGumbelScale
  have hnoise : Measurable noise := by
    exact measurable_commonLocationPositiveScaleGumbelNoise
      location unitVarianceGumbelScale
  have hnoiseLaw : Measure.map noise (gumbelArrivalLaw n) =
      sourceUnitVarianceGumbelNoiseLaw (n := n) location := by
    exact commonLocationUnitVarianceGumbelNoise_law location
  let hpres : MeasurePreserving noise (gumbelArrivalLaw n)
      (sourceUnitVarianceGumbelNoiseLaw (n := n) location) :=
    ⟨hnoise, hnoiseLaw⟩
  change rankingPMFOfMeasure (gumbelArrivalLaw n)
      (commonLocationPositiveScaleGumbelRank location unitVarianceGumbelScale theta value)
      (measurable_commonLocationPositiveScaleGumbelRank
        location unitVarianceGumbelScale theta value) =
    rankingPMFOfMeasure (sourceUnitVarianceGumbelNoiseLaw (n := n) location)
      (sourceUnitVarianceGumbelRank theta value)
      (measurable_sourceUnitVarianceGumbelRank theta value)
  apply rankingPMFOfMeasure_eq_of_measurePreserving
    (gumbelArrivalLaw n)
    (sourceUnitVarianceGumbelNoiseLaw (n := n) location)
    noise hpres
    (commonLocationPositiveScaleGumbelRank location unitVarianceGumbelScale theta value)
    (measurable_commonLocationPositiveScaleGumbelRank
      location unitVarianceGumbelScale theta value)
    (sourceUnitVarianceGumbelRank theta value)
    (measurable_sourceUnitVarianceGumbelRank theta value)
  intro arrival
  rfl

/-- Conditional on the explicit Gamma special-value obligation, every scalar
coordinate of the actual iid source noise law has variance one. -/
theorem sourceUnitVarianceGumbelMeasure_variance_eq_one
    (location : ℝ)
    (hbaseVariance :
      Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6) :
    Var[id; sourceUnitVarianceGumbelMeasure location] = 1 := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  change Var[id;
    commonLocationPositiveScaleGumbelMeasure location unitVarianceGumbelScale] = 1
  rw [commonLocationPositiveScaleGumbelMeasure]
  rw [ProbabilityTheory.variance_id_map
    (measurable_commonLocationPositiveScaleGumbelInnovation
      location unitVarianceGumbelScale).aemeasurable]
  have hbase : Var[scaleOneGumbelInnovation; expMeasure 1] =
      Real.pi ^ 2 / 6 := by
    rw [← scaleOneGumbelMeasure_variance_eq_innovationVariance]
    exact hbaseVariance
  have hinnovation :
      (fun arrival : ℝ =>
        commonLocationPositiveScaleGumbelInnovation
          location unitVarianceGumbelScale arrival) =
        fun arrival => location +
          unitVarianceGumbelScale * scaleOneGumbelInnovation arrival := by
    funext arrival
    unfold commonLocationPositiveScaleGumbelInnovation
      positiveScaleGumbelInnovation
      scaleOneGumbelInnovation
    ring
  change Var[(fun arrival : ℝ =>
    commonLocationPositiveScaleGumbelInnovation
      location unitVarianceGumbelScale arrival); expMeasure 1] = 1
  rw [hinnovation]
  rw [ProbabilityTheory.variance_const_add
    ((measurable_const.mul measurable_scaleOneGumbelInnovation).aestronglyMeasurable)
    location]
  rw [ProbabilityTheory.variance_const_mul, hbase]
  unfold unitVarianceGumbelScale
  have hsqrt : Real.sqrt (6 : ℝ) ^ 2 = 6 := by
    norm_num
  calc
    (Real.sqrt 6 / Real.pi) ^ 2 * (Real.pi ^ 2 / 6) =
        Real.sqrt 6 ^ 2 / 6 := by
      field_simp [Real.pi_ne_zero]
    _ = 1 := by
      rw [hsqrt]
      norm_num

/-- Conditional on the same explicit special-value obligation, each coordinate
of the iid product law has variance one. -/
theorem sourceUnitVarianceGumbelNoiseLaw_coordinate_variance_eq_one
    {n : ℕ} (location : ℝ) (i : Candidate n)
    (hbaseVariance :
      Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6) :
    Var[(fun epsilon : Candidate n → ℝ => epsilon i);
      sourceUnitVarianceGumbelNoiseLaw (n := n) location] = 1 := by
  have heval : MeasurePreserving (Function.eval i)
      (sourceUnitVarianceGumbelNoiseLaw (n := n) location)
      (sourceUnitVarianceGumbelMeasure location) := by
    unfold sourceUnitVarianceGumbelNoiseLaw
    exact @measurePreserving_eval
      (Candidate n)
      (fun _ : Candidate n => ℝ)
      _ _
      (fun _ : Candidate n => sourceUnitVarianceGumbelMeasure location)
      (fun _ => sourceUnitVarianceGumbelMeasure_isProbabilityMeasure location)
      i
  have hvariance := heval.variance_fun_comp measurable_id.aemeasurable
  simpa only [Function.comp_apply, id_eq] using hvariance.trans
    (sourceUnitVarianceGumbelMeasure_variance_eq_one location hbaseVariance)

/-- The literal displayed-scale source RUM has the corrected
Plackett--Luce inverse temperature.  This ranking-law calculation is
independent of the scalar variance calculation. -/
theorem sourceUnitVarianceGumbelRUMRankingPMF_eq_plackettLuce_corrected
    {n : ℕ} (location : ℝ) {theta : ℝ} (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    sourceUnitVarianceGumbelRUMRankingPMF location theta value =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value := by
  rw [← commonLocationPositiveScaleGumbelRUMRankingPMF_eq_sourceUnitVarianceGumbel
    location theta value]
  exact commonLocationPositiveScaleGumbelRUMRankingPMF_eq_plackettLuce
    unitVarianceGumbelScale_pos htheta value

/-- Complete source-facing endpoint for Section 3.1's Gumbel instance.
Conditional on the one displayed Gamma special-value identity, the source
noise is iid by `sourceUnitVarianceGumbelNoiseLaw`, every coordinate has unit
variance, the score map is literally `value i + epsilon i / theta`, and the
induced ranking law is Plackett--Luce at the corrected temperature
`theta / (sqrt 6 / pi)`. -/
theorem sourceUnitVarianceGumbelRUM_source_model
    {n : ℕ} (location : ℝ) {theta : ℝ} (htheta : 0 < theta)
    (value : Candidate n → ℝ)
    (hbaseVariance :
      Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6) :
    (∀ i : Candidate n,
      Var[(fun epsilon : Candidate n → ℝ => epsilon i);
        sourceUnitVarianceGumbelNoiseLaw (n := n) location] = 1) ∧
      sourceUnitVarianceGumbelRUMRankingPMF location theta value =
        plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value := by
  constructor
  · intro i
    exact sourceUnitVarianceGumbelNoiseLaw_coordinate_variance_eq_one
      location i hbaseVariance
  · exact sourceUnitVarianceGumbelRUMRankingPMF_eq_plackettLuce_corrected
      location htheta value

end

end KR21Monoculture

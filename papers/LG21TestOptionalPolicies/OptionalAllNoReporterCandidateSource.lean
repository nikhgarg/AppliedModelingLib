import AppliedModelingLib.Foundations.Probability.FiniteGaussianSignalKernelRCD
import AppliedModelingLib.Foundations.Probability.KernelCompProdDensity
import LG21TestOptionalPolicies.OptionalZeroReporterActiveEntry
import LG21TestOptionalPolicies.PositiveMassDeviation

/-!
# Literal high-score candidate at the optional all-no-reporter endpoint

This module isolates the candidate-profile argument needed at the optional
all-no-reporter endpoint of LG21 Lemma 4.1.  It is deliberately written in
terms of measures, action events, and conditional means rather than fields
called `PBO` or a presumed cutoff equilibrium.

At a fixed full base profile, take the raw Gaussian score posterior as the
reported-score value.  A candidate profile has every access student test,
reports precisely scores at least `anchor`, and gives the score-lower-tail
action its literal conditional mean.  The lower tail has a mean strictly
below the score posterior at `anchor`, so the candidate reports are weakly
valuable and every latent skill has a strictly valuable upper-tail outcome.

The source-facing theorem below keeps the remaining RCD transport explicit:
the actual source `(score, skill)` law must factor through the displayed raw
Gaussian posterior on the relevant full-base fibre.  No value on the
predecessor's null reporter fibre is used.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability

/-! ## Candidate actions and continuation law -/

/-- The candidate reports a realized score exactly on the weak upper tail. -/
def lg21OptionalHighScoreCandidateReports (anchor score : ℝ) : Bool :=
  decide (anchor ≤ score)

/-- The candidate's literal no-report action event. -/
def lg21OptionalHighScoreCandidateNoReportEvent (anchor : ℝ) : Set ℝ :=
  Set.Iio anchor

/-- A source-timed candidate in which every access student tests and only the
displayed score upper tail is reported.  Its values are supplied as explicit
conditional-mean functions, not read from an equilibrium object. -/
def lg21OptionalHighScoreCandidate
    {Base : Type*}
    (anchor noReportValue : ℝ) (reportedValue : ℝ → ℝ)
    (noiseVariance : NNReal)
    (hcontinuationIntegrable : ∀ skill : ℝ,
      Integrable (fun score =>
        if anchor ≤ score then reportedValue score else noReportValue)
        (gaussianReal skill noiseVariance)) :
    LG21OptionalCandidateBranchData ℝ Base ℝ where
  testLaw := fun skill _base => gaussianReal skill noiseVariance
  testLaw_isProbability := by
    intro skill base
    infer_instance
  reportDecision := fun _base score =>
    lg21OptionalHighScoreCandidateReports anchor score
  reportedValue := fun _base score => reportedValue score
  noReportValue := fun _base => noReportValue
  continuationValue_integrable := by
    intro skill base
    simpa [lg21OptionalCandidateContinuationValue,
      lg21OptionalHighScoreCandidateReports] using hcontinuationIntegrable skill

/-- The continuation integrability obligation for the affine raw Gaussian
posterior is discharged from Gaussian first-moment integrability. -/
theorem lg21_optional_highScoreCandidate_continuation_integrable_of_affine
    (anchor noReportValue intercept slope : ℝ) (noiseVariance : NNReal) :
    ∀ skill : ℝ,
      Integrable (fun score =>
        if anchor ≤ score then intercept + slope * score else noReportValue)
        (gaussianReal skill noiseVariance) := by
  intro skill
  let law := gaussianReal skill noiseVariance
  letI : IsFiniteMeasure law := by infer_instance
  have hid : Integrable (fun score : ℝ => score) law := by
    exact (ProbabilityTheory.memLp_id_gaussianReal'
      (μ := skill) (v := noiseVariance) (p := 1) (by norm_num)).integrable le_rfl
  have haffine : Integrable (fun score : ℝ => intercept + slope * score) law := by
    simpa [mul_comm] using
      ((integrable_const intercept).add (hid.const_mul slope))
  have hconst : Integrable (fun _score : ℝ => noReportValue) law :=
    integrable_const noReportValue
  have hsplit :
      (fun score : ℝ =>
        if anchor ≤ score then intercept + slope * score else noReportValue) =
        (Set.Ici anchor).indicator (fun score => intercept + slope * score) +
          (Set.Iio anchor).indicator (fun _score => noReportValue) := by
    funext score
    by_cases hscore : anchor ≤ score
    · simp [Set.indicator, hscore]
    · simp [Set.indicator, hscore]
  rw [hsplit]
  exact (haffine.indicator measurableSet_Ici).add
    (hconst.indicator measurableSet_Iio)

/-! ## Literal lower-score conditional mean -/

/-- The candidate's no-report value formed from a literal score-selected
source law.  The score action event is visible in the definition. -/
def lg21OptionalLiteralNoReportMean
    {Omega : Type*} [MeasurableSpace Omega]
    (sourceLaw : Measure Omega) (score skill : Omega → ℝ)
    (anchor : ℝ) : ℝ :=
  ∫ omega, skill omega ∂lg21NormalizedRestriction sourceLaw
    (score ⁻¹' lg21OptionalHighScoreCandidateNoReportEvent anchor)

/-- The corresponding score-posterior tower expression. -/
def lg21OptionalScorePosteriorLowerTailMean
    (scoreLaw : Measure ℝ) (posterior : Kernel ℝ ℝ) (anchor : ℝ) : ℝ :=
  ∫ score, (∫ skill, skill ∂posterior score) ∂
    lg21NormalizedRestriction scoreLaw
      (lg21OptionalHighScoreCandidateNoReportEvent anchor)

/-- Normalizing a literal preimage action event commutes with mapping to the
public score/skill observation. -/
theorem lg21_optional_normalizedRestriction_map_preimage
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (law : Measure Alpha) (f : Alpha → Beta) (hf : Measurable f)
    (event : Set Beta) (hevent : MeasurableSet event) :
    (lg21NormalizedRestriction law (f ⁻¹' event)).map f =
      lg21NormalizedRestriction (law.map f) event := by
  unfold lg21NormalizedRestriction
  calc
    ((law (f ⁻¹' event))⁻¹ • law.restrict (f ⁻¹' event)).map f =
        (law (f ⁻¹' event))⁻¹ • (law.restrict (f ⁻¹' event)).map f := by
          rw [Measure.map_smul]
    _ = (law (f ⁻¹' event))⁻¹ • (law.map f).restrict event := by
          rw [← Measure.restrict_map hf hevent]
    _ = ((law.map f) event)⁻¹ • (law.map f).restrict event := by
          rw [Measure.map_apply hf hevent]

/-- A score-only candidate action event commutes with the raw
score/posterior factorization.  This is measure algebra, not a PBO axiom. -/
theorem lg21_optional_normalizedRestriction_compProd_score_lowerTail
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (posterior : Kernel ℝ ℝ) [IsMarkovKernel posterior]
    (anchor : ℝ) :
    lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior)
      (lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ) =
      lg21NormalizedRestriction scoreLaw
        (lg21OptionalHighScoreCandidateNoReportEvent anchor) ⊗ₘ posterior := by
  let lower : Set ℝ := lg21OptionalHighScoreCandidateNoReportEvent anchor
  have hlower : MeasurableSet lower := measurableSet_Iio
  have hmass : (scoreLaw ⊗ₘ posterior) (lower ×ˢ Set.univ) = scoreLaw lower := by
    calc
      (scoreLaw ⊗ₘ posterior) (lower ×ˢ Set.univ) =
          ((scoreLaw ⊗ₘ posterior).map Prod.fst) lower := by
            rw [Measure.map_apply measurable_fst hlower]
            congr
            ext pair
            simp
      _ = scoreLaw lower := by
            change (scoreLaw ⊗ₘ posterior).fst lower = scoreLaw lower
            rw [Measure.fst_compProd]
  have hrestrict : (scoreLaw.restrict lower) ⊗ₘ posterior =
      (scoreLaw ⊗ₘ posterior).restrict (lower ×ˢ Set.univ) := by
    calc
      (scoreLaw.restrict lower) ⊗ₘ posterior =
          (scoreLaw.withDensity (lower.indicator 1)) ⊗ₘ posterior := by
            rw [withDensity_indicator_one hlower]
      _ = (scoreLaw ⊗ₘ posterior).withDensity
          (fun pair => lower.indicator 1 pair.1) := by
            rw [Measure.compProd_withDensity_left
              (measurable_one.indicator hlower)]
      _ = (scoreLaw ⊗ₘ posterior).withDensity
          ((lower ×ˢ Set.univ).indicator 1) := by
            congr 2
            funext pair
            by_cases h : pair.1 ∈ lower <;> simp [Set.indicator, h]
      _ = (scoreLaw ⊗ₘ posterior).restrict (lower ×ˢ Set.univ) := by
            rw [withDensity_indicator_one (hlower.prod MeasurableSet.univ)]
  unfold lg21NormalizedRestriction
  rw [hmass, Measure.compProd_smul_left, hrestrict]

/-- The literal score-selected no-report action has positive source mass when
the observed score/skill law factors through a Markov posterior and the
corresponding score event has positive mass. -/
theorem lg21_optional_source_lowerTail_positive_of_rawRCD
    {Omega : Type*} [MeasurableSpace Omega]
    (sourceLaw : Measure Omega)
    (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (posterior : Kernel ℝ ℝ) [IsMarkovKernel posterior]
    (hrawRCD : sourceLaw.map (fun omega => (score omega, skill omega)) =
      scoreLaw ⊗ₘ posterior)
    (anchor : ℝ)
    (hlowerPositive : 0 < scoreLaw
      (lg21OptionalHighScoreCandidateNoReportEvent anchor)) :
    0 < sourceLaw
      (score ⁻¹' lg21OptionalHighScoreCandidateNoReportEvent anchor) := by
  let scoreSkill : Omega → ℝ × ℝ := fun omega => (score omega, skill omega)
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  have hscoreMarginal : sourceLaw.map score = scoreLaw := by
    calc
      sourceLaw.map score = (sourceLaw.map scoreSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hscoreSkill]
        rfl
      _ = (scoreLaw ⊗ₘ posterior).map Prod.fst := by rw [hrawRCD]
      _ = scoreLaw := by
        change (scoreLaw ⊗ₘ posterior).fst = scoreLaw
        rw [Measure.fst_compProd]
  change 0 < sourceLaw (score ⁻¹' Set.Iio anchor)
  rw [← Measure.map_apply hscore measurableSet_Iio, hscoreMarginal]
  simpa [lg21OptionalHighScoreCandidateNoReportEvent] using hlowerPositive

/-- A literal candidate no-report mean transports through an explicit raw
source score/skill RCD factorization only together with the proof that its
own score-selected action event has positive mass.  The hypothesis is a law
equality, so this result does not trust a name or an arbitrary null-fibre
version of a conditional distribution. -/
theorem lg21_optional_literalNoReportMean_positive_and_eq_scorePosteriorLowerTailMean_of_rawRCD
    {Omega : Type*} [MeasurableSpace Omega]
    (sourceLaw : Measure Omega)
    (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (posterior : Kernel ℝ ℝ) [IsMarkovKernel posterior]
    (hrawRCD : sourceLaw.map (fun omega => (score omega, skill omega)) =
      scoreLaw ⊗ₘ posterior)
    (anchor : ℝ)
    (hlowerPositive : 0 < scoreLaw
      (lg21OptionalHighScoreCandidateNoReportEvent anchor))
    (hintegrable : Integrable Prod.snd
      (lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior)
        (lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ))) :
    0 < sourceLaw
        (score ⁻¹' lg21OptionalHighScoreCandidateNoReportEvent anchor) ∧
      lg21OptionalLiteralNoReportMean sourceLaw score skill anchor =
        lg21OptionalScorePosteriorLowerTailMean scoreLaw posterior anchor := by
  refine ⟨lg21_optional_source_lowerTail_positive_of_rawRCD
    sourceLaw score skill hscore hskill scoreLaw posterior hrawRCD anchor
    hlowerPositive, ?_⟩
  let scoreSkill : Omega → ℝ × ℝ := fun omega => (score omega, skill omega)
  let lower : Set ℝ := lg21OptionalHighScoreCandidateNoReportEvent anchor
  let publicEvent : Set (ℝ × ℝ) := lower ×ˢ Set.univ
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  have hpublicEvent : MeasurableSet publicEvent :=
    measurableSet_Iio.prod MeasurableSet.univ
  have hpreimage : scoreSkill ⁻¹' publicEvent = score ⁻¹' lower := by
    ext omega
    simp [scoreSkill, publicEvent, lower]
  have hmap :
      (lg21NormalizedRestriction sourceLaw (scoreSkill ⁻¹' publicEvent)).map
          scoreSkill =
        lg21NormalizedRestriction (sourceLaw.map scoreSkill) publicEvent :=
    lg21_optional_normalizedRestriction_map_preimage
      sourceLaw scoreSkill hscoreSkill publicEvent hpublicEvent
  have hfactor :
      lg21NormalizedRestriction (sourceLaw.map scoreSkill) publicEvent =
        lg21NormalizedRestriction scoreLaw lower ⊗ₘ posterior := by
    rw [hrawRCD]
    exact lg21_optional_normalizedRestriction_compProd_score_lowerTail
      scoreLaw posterior anchor
  have hintegrable' : Integrable Prod.snd
      (lg21NormalizedRestriction scoreLaw lower ⊗ₘ posterior) := by
    rw [← lg21_optional_normalizedRestriction_compProd_score_lowerTail
      scoreLaw posterior anchor]
    exact hintegrable
  letI : IsFiniteMeasure scoreLaw := ⟨by simp⟩
  letI : SFinite (lg21NormalizedRestriction scoreLaw lower) := by
    unfold lg21NormalizedRestriction
    infer_instance
  unfold lg21OptionalLiteralNoReportMean
    lg21OptionalScorePosteriorLowerTailMean
  rw [← hpreimage]
  calc
    (∫ omega, skill omega ∂lg21NormalizedRestriction sourceLaw
        (scoreSkill ⁻¹' publicEvent)) =
        ∫ pair, pair.2 ∂
          (lg21NormalizedRestriction sourceLaw
            (scoreSkill ⁻¹' publicEvent)).map scoreSkill := by
          symm
          simpa [scoreSkill] using
            (integral_map_of_stronglyMeasurable hscoreSkill
              measurable_snd.stronglyMeasurable)
    _ = ∫ pair, pair.2 ∂lg21NormalizedRestriction scoreLaw lower ⊗ₘ posterior := by
          rw [hmap, hfactor]
    _ = ∫ observedScore, (∫ latentSkill, latentSkill ∂posterior observedScore) ∂
        lg21NormalizedRestriction scoreLaw lower := by
          simpa using (Measure.integral_compProd hintegrable')

/-! ## Gaussian posterior candidate -/

/-- The raw Gaussian posterior mean at one fixed full base profile. -/
def lg21OptionalRawGaussianPosteriorMean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (base : Base) (score : ℝ) : ℝ :=
  ∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance (base, score)

theorem lg21_optional_rawGaussianPosteriorMean_eq_affine
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (base : Base) (score : ℝ) :
    lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean priorVariance noiseVariance base score =
      gaussianSignalWeight priorVariance noiseVariance * score +
        gaussianSignalPriorWeight priorVariance noiseVariance * baseMean base := by
  exact gaussianSignalPosteriorBaseKernel_integral_id
    baseMean hbaseMean priorVariance noiseVariance base score

theorem lg21_optional_rawGaussianPosteriorMean_strictMono
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : Base) :
    StrictMono (lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean priorVariance noiseVariance base) := by
  exact strictMono_gaussianSignalPosteriorBaseKernel_integral_id
    baseMean hbaseMean priorVariance noiseVariance
    hpriorVariance hnoiseVariance base

theorem lg21_optional_rawGaussianPosteriorMean_integrable_under_test
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (base : Base)
    (testVariance : NNReal) (skill : ℝ) :
    Integrable (lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean priorVariance noiseVariance base)
      (gaussianReal skill testVariance) := by
  rw [show lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean priorVariance noiseVariance base =
      fun score => gaussianSignalWeight priorVariance noiseVariance * score +
        gaussianSignalPriorWeight priorVariance noiseVariance * baseMean base by
        funext score
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean priorVariance noiseVariance base score]
  have hlinear : Integrable (fun score : ℝ =>
      gaussianSignalWeight priorVariance noiseVariance * score)
      (gaussianReal skill testVariance) := by
    simpa only [id_eq] using
      ((ProbabilityTheory.memLp_id_gaussianReal'
        (μ := skill) (v := testVariance) (p := 1) (by norm_num)).integrable le_rfl |>.const_mul
        (gaussianSignalWeight priorVariance noiseVariance))
  exact hlinear.add (integrable_const
    (gaussianSignalPriorWeight priorVariance noiseVariance * baseMean base))

/-- The source-faithful high-score candidate using the displayed Gaussian
posterior mean.  The only off-equilibrium object here is the candidate's own
positive-mass action profile; its no-report value is an explicit argument
that the source-RCD bridge identifies with the relevant conditional mean. -/
def lg21OptionalRawGaussianHighScoreCandidate
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (base : Base)
    (anchor noReportValue : ℝ) (testVariance : NNReal) :
    LG21OptionalCandidateBranchData ℝ Base ℝ :=
  lg21OptionalHighScoreCandidate anchor noReportValue
    (lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean priorVariance noiseVariance base)
    testVariance (by
      intro skill
      have hpAffine : lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean priorVariance noiseVariance base = fun score =>
          gaussianSignalPriorWeight priorVariance noiseVariance * baseMean base +
            gaussianSignalWeight priorVariance noiseVariance * score := by
        funext score
        rw [lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean priorVariance noiseVariance base score]
        ring
      rw [hpAffine]
      exact lg21_optional_highScoreCandidate_continuation_integrable_of_affine
        anchor noReportValue
        (gaussianSignalPriorWeight priorVariance noiseVariance * baseMean base)
        (gaussianSignalWeight priorVariance noiseVariance) testVariance skill)

/-! ## Integrability of the canonical source branch -/

/-- The canonical full-base score/latent Gaussian joint law has an integrable
latent coordinate.  This derives the analytic condition from the underlying
independent latent/noise Gaussian pair, rather than accepting it as a model
field. -/
theorem lg21_optional_canonicalGaussianScorePosterior_joint_integrable
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : Base) :
    Integrable Prod.snd
      (gaussianReal (baseMean base)
        (baseVariance + noiseVariance).toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) base) := by
  let primitive := gaussianSignalPair
    (baseMean base) baseVariance noiseVariance
  let pairMap : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (gaussianSignalScore pair, pair.1)
  have hpairMap : Measurable pairMap := by
    exact (measurable_fst.add measurable_snd).prodMk measurable_fst
  have hlatentMap : primitive.map Prod.fst =
      gaussianReal (baseMean base) baseVariance.toNNReal := by
    change Measure.map Prod.fst
      ((gaussianReal (baseMean base) baseVariance.toNNReal).prod
        (gaussianReal 0 noiseVariance.toNNReal)) = _
    rw [Measure.map_fst_prod]
    simp
  have hlatentIntegrable : Integrable Prod.fst primitive := by
    have hgaussian : Integrable id
        (gaussianReal (baseMean base) baseVariance.toNNReal) := by
      exact (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := baseMean base) (v := baseVariance.toNNReal)
        (p := 1) (by norm_num)).integrable le_rfl
    rw [← hlatentMap] at hgaussian
    exact (integrable_map_measure
      stronglyMeasurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mp (by
        simpa [Function.comp_def] using hgaussian)
  have hmapIntegrable : Integrable Prod.snd (primitive.map pairMap) := by
    apply (integrable_map_measure
      measurable_snd.stronglyMeasurable.aestronglyMeasurable
      hpairMap.aemeasurable).mpr
    simpa [Function.comp_def, pairMap, gaussianSignalScore] using hlatentIntegrable
  have hfactor : primitive.map pairMap =
      gaussianReal (baseMean base)
        (baseVariance + noiseVariance).toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) base := by
    calc
      primitive.map pairMap =
          gaussianReal (baseMean base)
            (baseVariance + noiseVariance).toNNReal ⊗ₘ
            gaussianSignalPosteriorKernel
              (baseMean base) baseVariance noiseVariance := by
            exact gaussianSignalPair_score_latent_joint_factorization
              (baseMean base) baseVariance noiseVariance
              hbaseVariance hnoiseVariance
      _ = gaussianReal (baseMean base)
            (baseVariance + noiseVariance).toNNReal ⊗ₘ
            Kernel.sectR (gaussianSignalPosteriorBaseKernel
              baseMean hbaseMean baseVariance noiseVariance) base := by
            rw [gaussianSignalPosteriorBaseKernel_sectR]
  rw [← hfactor]
  exact hmapIntegrable

/-- The latent-skill marginal of the canonical fixed-full-base score/skill
law is the displayed Gaussian base posterior. -/
theorem lg21_optional_canonicalGaussianScorePosterior_skill_marginal
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : Base) :
    (gaussianReal (baseMean base)
      (baseVariance + noiseVariance).toNNReal ⊗ₘ
      Kernel.sectR (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) base).map Prod.snd =
      gaussianReal (baseMean base) baseVariance.toNNReal := by
  let primitive := gaussianSignalPair
    (baseMean base) baseVariance noiseVariance
  let pairMap : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (gaussianSignalScore pair, pair.1)
  have hpairMap : Measurable pairMap := by
    exact (measurable_fst.add measurable_snd).prodMk measurable_fst
  have hlatentMap : primitive.map Prod.fst =
      gaussianReal (baseMean base) baseVariance.toNNReal := by
    change Measure.map Prod.fst
      ((gaussianReal (baseMean base) baseVariance.toNNReal).prod
        (gaussianReal 0 noiseVariance.toNNReal)) = _
    rw [Measure.map_fst_prod]
    simp
  have hfactor : primitive.map pairMap =
      gaussianReal (baseMean base)
        (baseVariance + noiseVariance).toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) base := by
    calc
      primitive.map pairMap =
          gaussianReal (baseMean base)
            (baseVariance + noiseVariance).toNNReal ⊗ₘ
            gaussianSignalPosteriorKernel
              (baseMean base) baseVariance noiseVariance := by
            exact gaussianSignalPair_score_latent_joint_factorization
              (baseMean base) baseVariance noiseVariance
              hbaseVariance hnoiseVariance
      _ = gaussianReal (baseMean base)
            (baseVariance + noiseVariance).toNNReal ⊗ₘ
            Kernel.sectR (gaussianSignalPosteriorBaseKernel
              baseMean hbaseMean baseVariance noiseVariance) base := by
            rw [gaussianSignalPosteriorBaseKernel_sectR]
  calc
    (gaussianReal (baseMean base)
      (baseVariance + noiseVariance).toNNReal ⊗ₘ
      Kernel.sectR (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) base).map Prod.snd =
        (primitive.map pairMap).map Prod.snd := by rw [hfactor]
    _ = primitive.map (Prod.snd ∘ pairMap) := by
      rw [Measure.map_map measurable_snd hpairMap]
    _ = primitive.map Prod.fst := by rfl
    _ = gaussianReal (baseMean base) baseVariance.toNNReal := hlatentMap

/-- Transport the actual fixed-fibre skill marginal through an explicit raw
score/skill factorization.  This closes the gap between a synthetic Gaussian
law and the source law used by the entry certificate. -/
theorem lg21_optional_skillMarginal_eq_of_fullBaseGaussian_rawRCD
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : Base)
    (hrawRCD : sourceLaw.map (fun omega => (score omega, skill omega)) =
      gaussianReal (baseMean base) (baseVariance + noiseVariance).toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) base) :
    sourceLaw.map skill = gaussianReal (baseMean base) baseVariance.toNNReal := by
  let scoreSkill : Omega → ℝ × ℝ := fun omega => (score omega, skill omega)
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  calc
    sourceLaw.map skill = (sourceLaw.map scoreSkill).map Prod.snd := by
      rw [Measure.map_map measurable_snd hscoreSkill]
      rfl
    _ = (gaussianReal (baseMean base)
          (baseVariance + noiseVariance).toNNReal ⊗ₘ
          Kernel.sectR (gaussianSignalPosteriorBaseKernel
            baseMean hbaseMean baseVariance noiseVariance) base).map Prod.snd := by
          rw [hrawRCD]
    _ = gaussianReal (baseMean base) baseVariance.toNNReal :=
      lg21_optional_canonicalGaussianScorePosterior_skill_marginal
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance base

/-- The literal lower-score candidate branch is integrable under the
canonical full-base Gaussian source law.  Its positive mass is proved from
Gaussian lower-tail support before normalizing. -/
theorem lg21_optional_canonicalGaussianScorePosterior_lowerTail_integrable
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (base : Base) (anchor : ℝ) :
    Integrable Prod.snd
      (lg21NormalizedRestriction
        (gaussianReal (baseMean base)
          (baseVariance + noiseVariance).toNNReal ⊗ₘ
          Kernel.sectR (gaussianSignalPosteriorBaseKernel
            baseMean hbaseMean baseVariance noiseVariance) base)
        (lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ)) := by
  let scoreLaw := gaussianReal (baseMean base)
    (baseVariance + noiseVariance).toNNReal
  let posterior := Kernel.sectR (gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean baseVariance noiseVariance) base
  let joint := scoreLaw ⊗ₘ posterior
  let lower := lg21OptionalHighScoreCandidateNoReportEvent anchor
  have hscoreVariancePos : 0 < baseVariance + noiseVariance := by linarith
  have hscoreVarianceNN : (baseVariance + noiseVariance).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hscoreVariancePos)
  have hlowerPositive : 0 < scoreLaw lower := by
    exact lg21_gaussianReal_Iio_pos (baseMean base) anchor hscoreVarianceNN
  have hlowerMeasurable : MeasurableSet lower := measurableSet_Iio
  letI : IsMarkovKernel (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hmass : joint (lower ×ˢ Set.univ) = scoreLaw lower := by
    calc
      joint (lower ×ˢ Set.univ) = (joint.map Prod.fst) lower := by
        symm
        rw [Measure.map_apply measurable_fst hlowerMeasurable]
        congr 1
        ext pair
        simp
      _ = scoreLaw lower := by
        change joint.fst lower = scoreLaw lower
        rw [Measure.fst_compProd]
  have hjointIntegrable : Integrable Prod.snd joint := by
    exact lg21_optional_canonicalGaussianScorePosterior_joint_integrable
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance base
  unfold lg21NormalizedRestriction
  exact hjointIntegrable.restrict.smul_measure
    (ENNReal.inv_ne_top.mpr (by rw [hmass]; exact ne_of_gt hlowerPositive))

/-! ## Candidate entry from literal lower-tail calibration -/

/-- A literal lower-score conditional mean is strictly below the raw Gaussian
posterior at the report boundary.  This is the analytic high-score anchor; it
uses no equilibrium-cutoff premise. -/
theorem lg21_optional_scorePosteriorLowerTailMean_lt_rawGaussianAt_anchor
    {Base : Type*} [MeasurableSpace Base]
    (scoreMean : ℝ) (scoreVariance : NNReal)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : Base) (anchor : ℝ)
    (hlowerTailPositive : 0 < gaussianReal scoreMean scoreVariance
      (lg21OptionalHighScoreCandidateNoReportEvent anchor)) :
    lg21OptionalScorePosteriorLowerTailMean
      (gaussianReal scoreMean scoreVariance)
      (Kernel.sectR (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance) base)
      anchor <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean priorVariance noiseVariance base anchor := by
  let scoreLaw := gaussianReal scoreMean scoreVariance
  let posterior := Kernel.sectR (gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance) base
  let p := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean priorVariance noiseVariance base
  let lower : Set ℝ := lg21OptionalHighScoreCandidateNoReportEvent anchor
  have hlowerPositive : 0 < scoreLaw lower := by
    simpa [scoreLaw, lower] using hlowerTailPositive
  have hpIntegrable : Integrable p (lg21NormalizedRestriction scoreLaw lower) := by
    have hpFull : Integrable p scoreLaw := by
      exact lg21_optional_rawGaussianPosteriorMean_integrable_under_test
        baseMean hbaseMean priorVariance noiseVariance base scoreVariance scoreMean
    unfold lg21NormalizedRestriction
    exact hpFull.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hlowerPositive))
  have hpStrict : StrictMono p := by
    exact lg21_optional_rawGaussianPosteriorMean_strictMono
      baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance base
  have hmeanLt : (∫ score, p score ∂lg21NormalizedRestriction scoreLaw lower) <
      p anchor := by
    apply lg21NormalizedRestriction_mean_lt_upper scoreLaw lower p (p anchor)
      measurableSet_Iio hlowerPositive hpIntegrable
    intro score hscore
    exact hpStrict hscore
  change (∫ score, (∫ skill, skill ∂posterior score) ∂
      lg21NormalizedRestriction scoreLaw lower) < p anchor
  have hposteriorMean : ∀ score,
      (∫ skill, skill ∂posterior score) = p score := by
    intro score
    change (∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance (base, score)) = p score
    rfl
  rw [show (fun score => ∫ skill, skill ∂posterior score) = p by
    funext score
    exact hposteriorMean score]
  exact hmeanLt

/-- The high-score candidate has a source-faithful positive-mass entry as
soon as its no-report value is the literal score-selected conditional mean.
The result uses the candidate's own action event and values, never a value
attached to the predecessor's null reporter fibre. -/
theorem lg21_optional_allNoReport_has_entry_of_rawGaussian_lowerTailMean
    {Base : Type*} [MeasurableSpace Base]
    (skillLaw : Measure ℝ) [IsProbabilityMeasure skillLaw]
    (scoreMean : ℝ) (scoreVariance testVariance : NNReal)
    (htestVariance : testVariance ≠ 0)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (base : Base) (anchor : ℝ)
    (noReportValue : ℝ)
    (hlowerTailPositive : 0 < gaussianReal scoreMean scoreVariance
      (lg21OptionalHighScoreCandidateNoReportEvent anchor))
    (hnoReportValue :
      let posterior := Kernel.sectR (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance) base
      noReportValue = lg21OptionalScorePosteriorLowerTailMean
        (gaussianReal scoreMean scoreVariance) posterior anchor) :
    LG21OptionalAllNoReportHasActiveEntry skillLaw
      (lg21OptionalRawGaussianHighScoreCandidate
        baseMean hbaseMean priorVariance noiseVariance base
        anchor noReportValue testVariance)
      base := by
  let p := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean priorVariance noiseVariance base
  let candidate := lg21OptionalRawGaussianHighScoreCandidate
    baseMean hbaseMean priorVariance noiseVariance base
    anchor noReportValue testVariance
  have hstrict : StrictMono p := by
    exact lg21_optional_rawGaussianPosteriorMean_strictMono
      baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance base
  have hanchor : noReportValue < p anchor := by
    rw [hnoReportValue]
    exact lg21_optional_scorePosteriorLowerTailMean_lt_rawGaussianAt_anchor
      scoreMean scoreVariance baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance base anchor hlowerTailPositive
  have hweak : ∀ score,
      candidate.reportDecision base score = true →
        candidate.noReportValue base ≤ candidate.reportedValue base score := by
    intro score hreport
    have hge : anchor ≤ score := by
      simpa [candidate, lg21OptionalRawGaussianHighScoreCandidate,
        lg21OptionalHighScoreCandidate,
        lg21OptionalHighScoreCandidateReports] using hreport
    have hmono : p anchor ≤ p score := hstrict.monotone hge
    change noReportValue ≤ p score
    exact le_trans (le_of_lt hanchor) hmono
  have hreportsAbove : ∀ score, anchor < score →
      candidate.reportDecision base score = true := by
    intro score hscore
    simp [candidate, lg21OptionalRawGaussianHighScoreCandidate,
      lg21OptionalHighScoreCandidate,
      lg21OptionalHighScoreCandidateReports, le_of_lt hscore]
  have htestLaw : ∀ skill,
      candidate.testLaw skill base = gaussianReal skill testVariance := by
    intro skill
    rfl
  exact lg21_optional_allNoReport_has_positiveMass_entry_of_candidate_gaussian_report_gain
    skillLaw candidate base testVariance htestVariance htestLaw hweak hstrict
    anchor hanchor hreportsAbove

/-- Source-facing optional all-no-reporter bridge at one full base profile.

The `hrawRCD` premise is the actual law factorization of the source
conditional population, not an equation merely naming a belief.  It makes
the candidate's score lower-tail action event a literal conditional-mean
branch.  From that factorization, the Gaussian posterior supplies the strict
high-score anchor and every latent skill has positive probability of a
profitable report.  No value from the predecessor's null reporter event is
consulted.
-/
theorem lg21_optional_allNoReport_has_entry_of_fullBaseGaussian_rawRCD
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (base : Base) (anchor : ℝ)
    (hrawRCD : sourceLaw.map (fun omega => (score omega, skill omega)) =
      gaussianReal (baseMean base) (baseVariance + noiseVariance).toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) base) :
    LG21OptionalAllNoReportHasActiveEntry
      (sourceLaw.map skill)
      (lg21OptionalRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance base anchor
        (lg21OptionalLiteralNoReportMean sourceLaw score skill anchor)
        noiseVariance.toNNReal)
      base := by
  have hscoreVariancePos : 0 < (baseVariance + noiseVariance) := by linarith
  have hscoreVarianceNN : (baseVariance + noiseVariance).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hscoreVariancePos)
  have hnoiseVarianceNN : noiseVariance.toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hnoiseVariance)
  have hscoreLowerTailPositive : 0 <
      gaussianReal (baseMean base) (baseVariance + noiseVariance).toNNReal
        (lg21OptionalHighScoreCandidateNoReportEvent anchor) := by
    exact lg21_gaussianReal_Iio_pos (baseMean base) anchor hscoreVarianceNN
  letI : IsMarkovKernel (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hskillMarginal : sourceLaw.map skill =
      gaussianReal (baseMean base) baseVariance.toNNReal := by
    exact lg21_optional_skillMarginal_eq_of_fullBaseGaussian_rawRCD
      sourceLaw score skill hscore hskill baseMean hbaseMean
      baseVariance noiseVariance hbaseVariance hnoiseVariance base hrawRCD
  letI : IsProbabilityMeasure (sourceLaw.map skill) := by
    rw [hskillMarginal]
    infer_instance
  have hliteralNoReport :=
    lg21_optional_literalNoReportMean_positive_and_eq_scorePosteriorLowerTailMean_of_rawRCD
      sourceLaw score skill hscore hskill
      (gaussianReal (baseMean base) (baseVariance + noiseVariance).toNNReal)
      (Kernel.sectR (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) base)
      hrawRCD anchor hscoreLowerTailPositive
      (lg21_optional_canonicalGaussianScorePosterior_lowerTail_integrable
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance base anchor)
  apply lg21_optional_allNoReport_has_entry_of_rawGaussian_lowerTailMean
    (sourceLaw.map skill)
    (baseMean base) (baseVariance + noiseVariance).toNNReal
    noiseVariance.toNNReal hnoiseVarianceNN
    baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance base anchor
    (lg21OptionalLiteralNoReportMean sourceLaw score skill anchor)
    hscoreLowerTailPositive
  exact hliteralNoReport.2

end

end LG21TestOptionalPolicies

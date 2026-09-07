import LG21TestOptionalPolicies.ContinuousResampling
import AppliedModelingLib.Foundations.Probability.GaussianSignalRCD
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Actual Gaussian measure repair for LG21 Proposition 4.2

This module formalizes the source-faithful *observed-score* route for
Proposition 4.2.  It does not inherit the paper's general Lemma 4.1 claim.
Instead, it applies when a mandatory-given-access protocol (or another valid
source route) makes every access student's realized test score available to
the PBO estimator.

At a fixed first-`K - 1`-feature profile and latent skill `q`, the construction
draws `theta_K = q + epsilon_K` from a nondegenerate Gaussian law and maps the
actual score through the positive-slope Gaussian posterior mean.  A no-access
policy is an arbitrary Markov kernel indexed only by observed base features,
so it cannot vary with `q`.  Two distinct latent skills therefore produce two
different actual Gaussian access laws but the same no-access law, contradicting
Definition 2.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/--
Source Gaussian observed-score data for Proposition 4.2.

`noAccessEstimateKernel` has domain `Base`, not `Base × ℝ`.  This makes the
paper's information restriction explicit while allowing arbitrary randomized
no-access policies.  Conditional on the first `K - 1` features, latent skill is
Gaussian with the displayed base posterior mean and positive variance.  The
test is an independent additive Gaussian observation with positive variance.
The PBO coefficients and the two skill-indexed access estimate laws below are
therefore derived from these source parameters rather than supplied as an
arbitrary affine carrier.
-/
structure LG21P42ObservedScoreGaussianPBOModel (Base : Type*)
    [MeasurableSpace Base] where
  /-- Posterior mean after the first `K - 1` Gaussian features. -/
  basePosteriorMean : Base → ℝ
  basePosteriorMean_measurable : Measurable basePosteriorMean
  /-- Posterior variance after the first `K - 1` Gaussian features. -/
  basePosteriorVariance : NNReal
  basePosteriorVariance_pos : 0 < (basePosteriorVariance : ℝ)
  latentSkillGivenBaseLaw : Base → Measure ℝ
  latentSkillGivenBaseLaw_eq_gaussian :
    forall base,
      latentSkillGivenBaseLaw base =
        gaussianReal (basePosteriorMean base) basePosteriorVariance
  /-- Variance of the independent test noise `epsilon_K`. -/
  testNoiseVariance : NNReal
  testNoiseVariance_pos : 0 < (testNoiseVariance : ℝ)
  testScoreGivenSkillLaw : ℝ → Measure ℝ
  testScoreGivenSkillLaw_eq_gaussian :
    forall skill,
      testScoreGivenSkillLaw skill = gaussianReal skill testNoiseVariance
  /-- Any deterministic or randomized no-access estimation policy. -/
  noAccessEstimateKernel : Kernel Base ℝ
  noAccessEstimateKernel_isMarkov : IsMarkovKernel noAccessEstimateKernel

/-- Coefficient on the base posterior mean in the source Gaussian update. -/
def LG21P42ObservedScoreGaussianPBOModel.pboIntercept
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) : Base → ℝ :=
  fun base =>
    gaussianSignalPriorWeight (M.basePosteriorVariance : ℝ)
      (M.testNoiseVariance : ℝ) * M.basePosteriorMean base

/-- Coefficient on the observed score in the source Gaussian update. -/
def LG21P42ObservedScoreGaussianPBOModel.pboSlope
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (_base : Base) : ℝ :=
  gaussianSignalWeight (M.basePosteriorVariance : ℝ)
    (M.testNoiseVariance : ℝ)

theorem LG21P42ObservedScoreGaussianPBOModel.pboIntercept_measurable
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Measurable M.pboIntercept := by
  unfold LG21P42ObservedScoreGaussianPBOModel.pboIntercept
  exact measurable_const.mul M.basePosteriorMean_measurable

theorem LG21P42ObservedScoreGaussianPBOModel.pboSlope_measurable
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Measurable M.pboSlope := measurable_const

theorem LG21P42ObservedScoreGaussianPBOModel.pboSlope_pos
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base) :
    0 < M.pboSlope base := by
  unfold LG21P42ObservedScoreGaussianPBOModel.pboSlope gaussianSignalWeight
  exact div_pos M.basePosteriorVariance_pos
    (add_pos M.basePosteriorVariance_pos M.testNoiseVariance_pos)

/-- Exact Gaussian law of latent skill after the first `K - 1` features. -/
def lg21P42LatentSkillGivenBaseLaw
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base) : Measure ℝ :=
  M.latentSkillGivenBaseLaw base

/-- Exact Gaussian test law `theta_K | q = N(q, sigma_K^2)`. -/
def lg21P42TestScoreGivenSkillLaw
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (skill : ℝ) : Measure ℝ :=
  M.testScoreGivenSkillLaw skill

/-- The paper's displayed conditional mean for an access student's estimate. -/
def lg21P42SourceAccessEstimateMean
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base)
    (base : Base) (skill : ℝ) : ℝ :=
  (M.basePosteriorMean base / (M.basePosteriorVariance : ℝ) +
      skill / (M.testNoiseVariance : ℝ)) /
    (1 / (M.basePosteriorVariance : ℝ) +
      1 / (M.testNoiseVariance : ℝ))

/--
The common variance printed for the two access groups in Proposition 4.2,
written after the first `K - 1` features have been summarized by their
posterior variance.
-/
def lg21P42SourceDisplayedAccessEstimateVariance
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) : NNReal :=
  NNReal.mk
    ((1 / (M.basePosteriorVariance : ℝ) +
        2 / (M.testNoiseVariance : ℝ)) /
      (1 / (M.basePosteriorVariance : ℝ) +
        1 / (M.testNoiseVariance : ℝ)) ^ 2)
    (div_nonneg
      (add_nonneg
        (one_div_nonneg.mpr (le_of_lt M.basePosteriorVariance_pos))
        (div_nonneg (by norm_num)
          (le_of_lt M.testNoiseVariance_pos)))
      (sq_nonneg _))

/--
The two source-displayed access-side estimate laws at a fixed base profile and
latent skill.  Both use the same displayed variance, while their exact
Gaussian-posterior means depend on skill.
-/
def lg21P42SourceAccessEstimateLaw
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base)
    (base : Base) (skill : ℝ) : Measure ℝ :=
  gaussianReal
    (lg21P42SourceAccessEstimateMean M base skill)
    (lg21P42SourceDisplayedAccessEstimateVariance M)

/-- The displayed source mean is the usual affine Gaussian update. -/
theorem lg21P42SourceAccessEstimateMean_eq_affine
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base)
    (base : Base) (skill : ℝ) :
    lg21P42SourceAccessEstimateMean M base skill =
      M.pboIntercept base + M.pboSlope base * skill := by
  unfold lg21P42SourceAccessEstimateMean
    LG21P42ObservedScoreGaussianPBOModel.pboIntercept
    LG21P42ObservedScoreGaussianPBOModel.pboSlope
    gaussianSignalPriorWeight gaussianSignalWeight
  have hv : (M.basePosteriorVariance : ℝ) ≠ 0 :=
    ne_of_gt M.basePosteriorVariance_pos
  have hn : (M.testNoiseVariance : ℝ) ≠ 0 :=
    ne_of_gt M.testNoiseVariance_pos
  have hsum : (M.basePosteriorVariance : ℝ) +
      (M.testNoiseVariance : ℝ) ≠ 0 :=
    ne_of_gt (add_pos M.basePosteriorVariance_pos M.testNoiseVariance_pos)
  field_simp
  ring

/-- The displayed access estimate mean is strictly increasing in true skill. -/
theorem lg21P42SourceAccessEstimateMean_strictMono
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base) :
    StrictMono (lg21P42SourceAccessEstimateMean M base) := by
  intro skillLow skillHigh hskill
  rw [lg21P42SourceAccessEstimateMean_eq_affine,
    lg21P42SourceAccessEstimateMean_eq_affine]
  simpa [add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_left hskill (M.pboSlope_pos base))
    (M.pboIntercept base)

/-- State after conditioning on a base profile and latent skill. -/
abbrev LG21P42ApplicantState (Base : Type*) := Base × ℝ

/-- Centered Gaussian test-noise kernel indexed by applicant state. -/
def lg21P42TestNoiseKernel
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Kernel (LG21P42ApplicantState Base) ℝ :=
  Kernel.const (LG21P42ApplicantState Base)
    (gaussianReal 0 M.testNoiseVariance)

/-- The source test-noise construction is Markov. -/
theorem lg21P42TestNoiseKernel_isMarkov
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    IsMarkovKernel (lg21P42TestNoiseKernel M) := by
  unfold lg21P42TestNoiseKernel
  infer_instance

/-- Joint kernel retaining applicant state and adding independent Gaussian noise. -/
def lg21P42AccessTestNoiseJointKernel
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Kernel (LG21P42ApplicantState Base)
      (LG21P42ApplicantState Base × ℝ) :=
  Kernel.id ×ₖ lg21P42TestNoiseKernel M

/-- Actual test-score kernel for `theta_K = q + epsilon_K`. -/
def lg21P42ActualTestScoreKernel
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Kernel (LG21P42ApplicantState Base) ℝ :=
  (lg21P42AccessTestNoiseJointKernel M).map
    (fun pair : LG21P42ApplicantState Base × ℝ => pair.1.2 + pair.2)

/-- Measurability of the source test-score equation. -/
theorem lg21P42ActualTestScore_measurable
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Measurable (fun pair : LG21P42ApplicantState Base × ℝ => pair.1.2 + pair.2) :=
  (measurable_snd.comp measurable_fst).add measurable_snd

/-- The actual test-score kernel is Markov. -/
theorem lg21P42ActualTestScoreKernel_isMarkov
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    IsMarkovKernel (lg21P42ActualTestScoreKernel M) := by
  letI : IsMarkovKernel (lg21P42TestNoiseKernel M) :=
    lg21P42TestNoiseKernel_isMarkov M
  unfold lg21P42ActualTestScoreKernel lg21P42AccessTestNoiseJointKernel
  exact Kernel.IsMarkovKernel.map _ (lg21P42ActualTestScore_measurable M)

/--
Conditional score law under the mandatory/observed-score route:
`theta_K | (base, q) = N(q, sigma_K^2)`.
-/
theorem lg21P42ActualTestScoreKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base) (skill : ℝ) :
    lg21P42ActualTestScoreKernel M (base, skill) =
      gaussianReal skill M.testNoiseVariance := by
  let score : LG21P42ApplicantState Base × ℝ → ℝ :=
    fun pair => pair.1.2 + pair.2
  have hscore : Measurable score := lg21P42ActualTestScore_measurable M
  letI : IsMarkovKernel (lg21P42TestNoiseKernel M) :=
    lg21P42TestNoiseKernel_isMarkov M
  calc
    lg21P42ActualTestScoreKernel M (base, skill) =
        (gaussianReal 0 M.testNoiseVariance).map
          (fun noise => skill + noise) := by
      ext target htarget
      rw [lg21P42ActualTestScoreKernel,
        Kernel.map_apply' _ hscore (base, skill) htarget]
      rw [lg21P42AccessTestNoiseJointKernel,
        Kernel.id_prod_apply'
          (lg21P42TestNoiseKernel M) (base, skill) (hscore htarget)]
      rw [lg21P42TestNoiseKernel, Kernel.const_apply]
      rw [Measure.map_apply (by fun_prop) htarget]
      rfl
    _ = gaussianReal skill M.testNoiseVariance := by
      simpa using
        (gaussianReal_map_const_add
          (μ := (0 : ℝ)) (v := M.testNoiseVariance) skill)

/-- Gaussian posterior-mean estimator after the score is observed. -/
def lg21P42GaussianPBOEstimate
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) : Base → ℝ → ℝ :=
  fun base score => M.pboIntercept base + M.pboSlope base * score

/-- Joint estimator map used after retaining state and observed score. -/
def lg21P42AccessEstimateMap
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    LG21P42ApplicantState Base × ℝ → ℝ :=
  fun pair => lg21P42GaussianPBOEstimate M pair.1.1 pair.2

/-- Measurability of the PBO estimator on state/score pairs. -/
theorem lg21P42AccessEstimateMap_measurable
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Measurable (lg21P42AccessEstimateMap M) := by
  unfold lg21P42AccessEstimateMap lg21P42GaussianPBOEstimate
  let hbase : Measurable (fun pair : LG21P42ApplicantState Base × ℝ => pair.1.1) :=
    measurable_fst.fst
  exact
    (M.pboIntercept_measurable.comp hbase).add
      ((M.pboSlope_measurable.comp hbase).mul measurable_snd)

/--
Actual access estimate kernel: retain state, draw the real Gaussian test score,
then apply the PBO estimator.
-/
def lg21P42AccessEstimateKernel
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    Kernel (LG21P42ApplicantState Base) ℝ :=
  (Kernel.id ×ₖ lg21P42ActualTestScoreKernel M).map
    (lg21P42AccessEstimateMap M)

/-- The access estimate construction is Markov. -/
theorem lg21P42AccessEstimateKernel_isMarkov
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) :
    IsMarkovKernel (lg21P42AccessEstimateKernel M) := by
  letI : IsMarkovKernel (lg21P42ActualTestScoreKernel M) :=
    lg21P42ActualTestScoreKernel_isMarkov M
  unfold lg21P42AccessEstimateKernel
  exact Kernel.IsMarkovKernel.map _ (lg21P42AccessEstimateMap_measurable M)

/-- Access estimate is the affine PBO image of the actual conditional test law. -/
theorem lg21P42AccessEstimateKernel_apply_as_score_map
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base) (skill : ℝ) :
    lg21P42AccessEstimateKernel M (base, skill) =
      (lg21P42ActualTestScoreKernel M (base, skill)).map
        (lg21P42GaussianPBOEstimate M base) := by
  let estimate : LG21P42ApplicantState Base × ℝ → ℝ :=
    lg21P42AccessEstimateMap M
  have hestimate : Measurable estimate :=
    lg21P42AccessEstimateMap_measurable M
  have hscoreEstimate : Measurable (lg21P42GaussianPBOEstimate M base) := by
    unfold lg21P42GaussianPBOEstimate
    exact measurable_const.add (measurable_const.mul measurable_id)
  letI : IsMarkovKernel (lg21P42ActualTestScoreKernel M) :=
    lg21P42ActualTestScoreKernel_isMarkov M
  ext target htarget
  rw [lg21P42AccessEstimateKernel,
    Kernel.map_apply' _ hestimate (base, skill) htarget]
  rw [Kernel.id_prod_apply'
    (lg21P42ActualTestScoreKernel M) (base, skill) (hestimate htarget)]
  rw [Measure.map_apply hscoreEstimate htarget]
  rfl

/--
Actual conditional access estimate law.  Its mean changes strictly with latent
skill because the Gaussian PBO test coefficient is positive.
-/
theorem lg21P42AccessEstimateKernel_apply_gaussian
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base) (skill : ℝ) :
    lg21P42AccessEstimateKernel M (base, skill) =
      gaussianReal
        (M.pboIntercept base + M.pboSlope base * skill)
        (NNReal.mk ((M.pboSlope base) ^ 2)
          (sq_nonneg (M.pboSlope base)) * M.testNoiseVariance) := by
  calc
    lg21P42AccessEstimateKernel M (base, skill) =
        (lg21P42ActualTestScoreKernel M (base, skill)).map
          (lg21P42GaussianPBOEstimate M base) :=
      lg21P42AccessEstimateKernel_apply_as_score_map M base skill
    _ = (gaussianReal skill M.testNoiseVariance).map
          (lg21P42GaussianPBOEstimate M base) := by
      rw [lg21P42ActualTestScoreKernel_apply]
    _ = gaussianReal
          (M.pboIntercept base + M.pboSlope base * skill)
          (NNReal.mk ((M.pboSlope base) ^ 2)
            (sq_nonneg (M.pboSlope base)) * M.testNoiseVariance) := by
      exact lg21_gaussianReal_map_affine
        skill M.testNoiseVariance
        (M.pboIntercept base) (M.pboSlope base)

/-- Distinct latent skills yield distinct actual PBO access measures. -/
theorem lg21P42AccessEstimateLaws_ne_of_skill_lt
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base)
    {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    lg21P42AccessEstimateKernel M (base, skillLow) ≠
      lg21P42AccessEstimateKernel M (base, skillHigh) := by
  intro hEq
  rw [lg21P42AccessEstimateKernel_apply_gaussian,
    lg21P42AccessEstimateKernel_apply_gaussian] at hEq
  have hmeans := (gaussianReal_ext_iff.mp hEq).1
  have hstrict :
      M.pboIntercept base + M.pboSlope base * skillLow <
        M.pboIntercept base + M.pboSlope base * skillHigh := by
    simpa [add_comm] using
      add_lt_add_left
        (mul_lt_mul_of_pos_left hskill (M.pboSlope_pos base))
        (M.pboIntercept base)
  exact (ne_of_lt hstrict) hmeans

/-- Distinct skills yield distinct source Gaussian access estimate laws. -/
theorem lg21P42SourceAccessEstimateLaws_ne_of_skill_lt
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base)
    {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    lg21P42SourceAccessEstimateLaw M base skillLow ≠
      lg21P42SourceAccessEstimateLaw M base skillHigh := by
  intro hEq
  have hmeans := (gaussianReal_ext_iff.mp hEq).1
  exact (ne_of_lt (lg21P42SourceAccessEstimateMean_strictMono M base hskill))
    hmeans

/--
Actual-kernel form of latent-skill fairness for the observed-score protocol.
No-access output is deliberately independent of latent skill.
-/
def lg21P42ObservedScoreLatentSkillFair
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) : Prop :=
  ∀ base skill,
    lg21P42SourceAccessEstimateLaw M base skill =
      M.noAccessEstimateKernel base

/-- The observed-score Gaussian PBO protocol is not latent-skill fair. -/
theorem paper_proposition4_2_actual_observed_score_not_latent_skill_fair_at
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base) (base : Base)
    {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    ¬ lg21P42ObservedScoreLatentSkillFair M := by
  intro hfair
  apply lg21P42SourceAccessEstimateLaws_ne_of_skill_lt M base hskill
  exact (hfair base skillLow).trans (hfair base skillHigh).symm

/--
Transfer to the paper's `LG21SourceLawPolicySurface`: one equilibrium with the
actual observed-score access kernel and a base-only no-access kernel witnesses
failure of Definition 2.
-/
theorem paper_proposition4_2_actual_observed_score_source_law_not_latent_skill_fair
    {Base : Type*} [MeasurableSpace Base]
    (M : LG21P42ObservedScoreGaussianPBOModel Base)
    {S : LG21SourceLawPolicySurface ℝ Base ℝ (Measure ℝ)}
    (e : S.Equilibrium)
    (hAccess : ∀ skill base,
      S.latentAccessLaw e skill base =
        lg21P42AccessEstimateKernel M (base, skill))
    (hNoAccess : ∀ skill base,
      S.latentNoAccessLaw e skill base = M.noAccessEstimateKernel base)
    (base : Base) {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair S := by
  intro hfair
  have hlow := hfair e skillLow base
  have hhigh := hfair e skillHigh base
  rw [hAccess skillLow base, hNoAccess skillLow base] at hlow
  rw [hAccess skillHigh base, hNoAccess skillHigh base] at hhigh
  apply lg21P42AccessEstimateLaws_ne_of_skill_lt M base hskill
  exact hlow.trans hhigh.symm

end

end LG21TestOptionalPolicies

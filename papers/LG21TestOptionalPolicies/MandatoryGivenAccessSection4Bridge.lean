import LG21TestOptionalPolicies.Proposition42ActualGaussianMeasureRepair
import LG21TestOptionalPolicies.Proposition43ActualGaussianMeasureRepair
import LG21TestOptionalPolicies.Theorem44SourceGaussianResamplingRepair

/-!
# Mandatory-given-access Section 4 bridge for LG21

This module isolates a candidate *corrected* Section 4 target.  It uses only
the source-listed mandatory-given-access requirement policy `Z = Y = X`; it
does not certify the archival all-three-protocol Lemma 4.1.

The construction records one finite Gaussian base-signal family, one positive
test-noise variance, and one independent access law alongside the following
checked routes:

* Proposition 4.2's actual observed-score latent-skill gap;
* Proposition 4.3's actual conditional and marginal Gaussian-measure gaps;
* Theorem 4.4's actual/synthetic Gaussian resampling equality.

The posterior-summary population used for the resampling route is constructed
from the source Gaussian parameters, rather than passed in as a matching-law
premise.  The remaining raw-feature bridge is deliberately not assumed here:
one still has to derive, from the literal finite Gaussian population,
`theta_K | theta_<K = N(m(theta_<K), V_post + sigma_K^2)` and identify its
PBO affine output with the posterior-summary experiment.  Nothing in this
module treats that conditional-disintegration/PBO identity as a conclusion or
an input.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/--
The source primitives needed by the mandatory Section 4 repair.

The two positive access-mass fields make the source's comparisons between the
`Z = 0` and `Z = 1` populations meaningful.  They are population regularity
conditions, not fairness or conclusion-bearing assumptions.
-/
structure LG21MandatorySection4Source (Feature : Type*) [Fintype Feature] where
  /-- The first `K - 1` Gaussian features from the source model. -/
  baseSignals : GaussianOffsetSignalFamily Feature
  /-- The paper's displayed feature noises are centered. -/
  baseNoiseMean_zero : ∀ feature, baseSignals.noiseMean feature = 0
  /-- Variance of the final test noise. -/
  testNoiseVariance : ℝ
  testNoiseVariance_pos : 0 < testNoiseVariance
  /-- Preset access is independent because the population is constructed as a product. -/
  accessLaw : Measure Bool
  accessLaw_isProbability : IsProbabilityMeasure accessLaw
  access_mass_pos : 0 < accessLaw {true}
  noAccess_mass_pos : 0 < accessLaw {false}

namespace LG21MandatorySection4Source

variable {Feature : Type*} [Fintype Feature]

/-- The source test variance in mathlib's nonnegative-real representation. -/
def testNoiseVarianceNNReal (S : LG21MandatorySection4Source Feature) : NNReal :=
  NNReal.mk S.testNoiseVariance S.testNoiseVariance_pos.le

theorem testNoiseVarianceNNReal_pos
    (S : LG21MandatorySection4Source Feature) :
    0 < (S.testNoiseVarianceNNReal : ℝ) := by
  simpa [testNoiseVarianceNNReal] using S.testNoiseVariance_pos

/-- The posterior variance of skill after the non-test source features. -/
def posteriorBaseVarianceNNReal (S : LG21MandatorySection4Source Feature) : NNReal :=
  NNReal.mk S.baseSignals.centeredFamily.posteriorVariance
    S.baseSignals.centeredFamily.posteriorVariance_pos.le

theorem posteriorBaseVarianceNNReal_pos
    (S : LG21MandatorySection4Source Feature) :
    0 < (S.posteriorBaseVarianceNNReal : ℝ) := by
  simpa [posteriorBaseVarianceNNReal] using
    S.baseSignals.centeredFamily.posteriorVariance_pos

/-!
## Mandatory behavior

No PBO payoff completion is needed under the source-listed mandatory policy:
feasibility itself fixes every access student's action.
-/

theorem mandatory_access_action_eq_takeAndReport
    (action : LG21AccessAction)
    (hfeasible : LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredGivenAccess LG21AccessStatus.access action) :
    action = LG21AccessAction.takeAndReport :=
  (LG21RequirementPolicy.feasibleAction_access_reportRequiredGivenAccess_iff
    action).mp hfeasible

theorem mandatory_noAccess_action_eq_noTake
    (action : LG21AccessAction)
    (hfeasible : LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredGivenAccess LG21AccessStatus.noAccess action) :
    action = LG21AccessAction.noTake :=
  (LG21RequirementPolicy.feasibleAction_noAccess_iff
    LG21RequirementPolicy.reportRequiredGivenAccess action).mp hfeasible

/-!
## One source-parameterized posterior-summary experiment

For Section 4's PBO and resampling policies, the first `K - 1` features enter
only through their Gaussian posterior mean.  The carrier below is that
sufficient statistic.  Its law is the checked Gaussian posterior-mean law of
the finite source signal family.
-/

/-- The actual Gaussian law of the non-test posterior sufficient statistic. -/
def posteriorSummaryLaw [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) : Measure ℝ :=
  S.baseSignals.posteriorMeanScaleLaw.toMeasure

theorem posteriorSummaryLaw_isProbability [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) :
    IsProbabilityMeasure S.posteriorSummaryLaw := by
  unfold posteriorSummaryLaw
  infer_instance

/--
The concrete Section 4 population on access status and the non-test posterior
sufficient statistic.  It is a product by construction, matching the source
assumption that access is preset and unrelated to skill/features.
-/
def posteriorSummaryPopulationLaw [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) : Measure (Bool × ℝ) :=
  S.accessLaw.prod S.posteriorSummaryLaw

theorem posteriorSummaryPopulationLaw_isProbability [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) :
    IsProbabilityMeasure S.posteriorSummaryPopulationLaw := by
  letI : IsProbabilityMeasure S.accessLaw := S.accessLaw_isProbability
  letI : IsProbabilityMeasure S.posteriorSummaryLaw :=
    S.posteriorSummaryLaw_isProbability
  unfold posteriorSummaryPopulationLaw
  infer_instance

/-- Access and posterior-summary events factor in the concrete Section 4 population. -/
theorem posteriorSummaryPopulationLaw_access_summary_factorization [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature)
    (accessEvent : Set Bool) (summaryEvent : Set ℝ) :
    S.posteriorSummaryPopulationLaw (accessEvent ×ˢ summaryEvent) =
      S.accessLaw accessEvent * S.posteriorSummaryLaw summaryEvent := by
  letI : IsProbabilityMeasure S.accessLaw := S.accessLaw_isProbability
  letI : IsProbabilityMeasure S.posteriorSummaryLaw :=
    S.posteriorSummaryLaw_isProbability
  unfold posteriorSummaryPopulationLaw
  exact Measure.prod_prod accessEvent summaryEvent

/--
The source-shaped experiment for Definition 6 after reducing the observed
base profile to its posterior sufficient statistic.
-/
def gaussianPBOResamplingSource [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) :
    LG21GaussianPBOResamplingSource ℝ where
  baseLaw := S.posteriorSummaryLaw
  baseLaw_isProbability := S.posteriorSummaryLaw_isProbability
  posteriorBaseMean := id
  posteriorBaseMean_measurable := measurable_id
  posteriorBaseVariance := S.posteriorBaseVarianceNNReal
  posteriorBaseVariance_pos := S.posteriorBaseVarianceNNReal_pos
  testNoiseVariance := S.testNoiseVarianceNNReal
  testNoiseVariance_pos := S.testNoiseVarianceNNReal_pos

/-- The positive PBO coefficient on the mandatory observed test score. -/
theorem gaussianPBOResamplingSource_weight_pos [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) :
    0 < lg21D6PosteriorTestWeight S.gaussianPBOResamplingSource := by
  unfold lg21D6PosteriorTestWeight
  exact div_pos S.posteriorBaseVarianceNNReal_pos
    (add_pos S.posteriorBaseVarianceNNReal_pos
      S.testNoiseVarianceNNReal_pos)

/--
An arbitrary randomized policy for students without test access.  Proposition
4.2 quantifies over this entire class; no PBO, equality, or fairness condition
is imposed on the kernel.  The kernel is indexed by the literal vector of the
first `K - 1` features, not only by a posterior-summary quotient.
-/
structure ArbitraryNoAccessPolicy (Feature : Type*) [Fintype Feature] where
  estimateKernel : Kernel (Feature → ℝ) ℝ
  estimateKernel_isMarkov : IsMarkovKernel estimateKernel

/--
The actual observed-score model used by Proposition 4.2, instantiated from
the same access-side source parameters as the Section 4 resampling
construction.  Its no-access policy remains arbitrary, as in the source
quantifier of Proposition 4.2.
-/
def observedScorePBOModel [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature)
    (noAccessPolicy : ArbitraryNoAccessPolicy Feature) :
    LG21P42ObservedScoreGaussianPBOModel (Feature → ℝ) where
  basePosteriorMean := S.baseSignals.posteriorMean
  basePosteriorMean_measurable := by
    unfold GaussianOffsetSignalFamily.posteriorMean
    unfold GaussianSignalFamily.posteriorMean
    unfold GaussianOffsetSignalFamily.centeredSignal
    fun_prop
  basePosteriorVariance := S.posteriorBaseVarianceNNReal
  basePosteriorVariance_pos := S.posteriorBaseVarianceNNReal_pos
  latentSkillGivenBaseLaw := fun base =>
    gaussianReal (S.baseSignals.posteriorMean base)
      S.posteriorBaseVarianceNNReal
  latentSkillGivenBaseLaw_eq_gaussian := fun _ => rfl
  testNoiseVariance := S.testNoiseVarianceNNReal
  testNoiseVariance_pos := S.testNoiseVarianceNNReal_pos
  testScoreGivenSkillLaw := fun skill =>
    gaussianReal skill S.testNoiseVarianceNNReal
  testScoreGivenSkillLaw_eq_gaussian := fun _ => rfl
  noAccessEstimateKernel := noAccessPolicy.estimateKernel
  noAccessEstimateKernel_isMarkov := noAccessPolicy.estimateKernel_isMarkov

/--
The Proposition 4.2 PBO estimator and the Theorem 4.4 resampling estimator
are literally the same affine posterior update under the shared source
parameters.
-/
theorem observedScorePBOEstimate_eq_resamplingPBOEstimate [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature)
    (noAccessPolicy : ArbitraryNoAccessPolicy Feature)
    (base : Feature → ℝ) (score : ℝ) :
    lg21P42GaussianPBOEstimate
        (S.observedScorePBOModel noAccessPolicy) base score =
      lg21D6GaussianPBOEstimate S.gaussianPBOResamplingSource
        (S.baseSignals.posteriorMean base, score) := by
  unfold lg21P42GaussianPBOEstimate observedScorePBOModel
    LG21P42ObservedScoreGaussianPBOModel.pboIntercept
    LG21P42ObservedScoreGaussianPBOModel.pboSlope
    lg21D6GaussianPBOEstimate lg21D6PosteriorTestWeight
    gaussianPBOResamplingSource
    gaussianSignalPriorWeight gaussianSignalWeight
  have hsum : (S.posteriorBaseVarianceNNReal : ℝ) +
      (S.testNoiseVarianceNNReal : ℝ) ≠ 0 :=
    ne_of_gt (add_pos S.posteriorBaseVarianceNNReal_pos
      S.testNoiseVarianceNNReal_pos)
  field_simp
  simp only [id_eq]
  ring

/-!
## Proposition 4.2: arbitrary no-access policy

This route keeps the source quantifier honest: its access branch is PBO, while
its no-access branch is an arbitrary Markov kernel indexed by the literal
first-`K - 1` feature vector.  No law identity is passed as a premise.
-/

theorem proposition42_mandatory_for_any_noAccessPolicy [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature)
    (noAccessPolicy : ArbitraryNoAccessPolicy Feature) :
    ¬ lg21P42ObservedScoreLatentSkillFair
      (S.observedScorePBOModel noAccessPolicy) :=
  paper_proposition4_2_actual_observed_score_not_latent_skill_fair_at
    (S.observedScorePBOModel noAccessPolicy) (fun _ => 0)
    (skillLow := 0) (skillHigh := 1) (by norm_num)

/-!
## Proposition 4.3 all-PBO and Theorem 4.4 resampling scopes

Proposition 4.3 uses the literal finite base-feature family, because its
statement compares the raw observed-feature fibres and their Gaussian marginal
posterior laws.  Its no-access policy is PBO, represented by the deterministic
posterior base summary rather than the arbitrary policy permitted by
Proposition 4.2.  Theorem 4.4 uses its distinct resampling policy.  Both
constructions are generated by `baseSignals` and the same test variance.
-/

theorem proposition43_mandatory_actual_measure_gaps [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) :
    (∀ base : Feature → ℝ,
      (lg21P43ConditionalAccessOutputLaw S.baseSignals base 0
        S.testNoiseVariance S.testNoiseVariance_pos).toMeasure ≠
        Measure.dirac (S.baseSignals.posteriorMean base)) ∧
      S.baseSignals.posteriorMeanScaleLaw.toMeasure ≠
        (GaussianOffsetSignalFamily.posteriorMeanScaleLaw
          (S.baseSignals.withExtraSignal 0 S.testNoiseVariance
            S.testNoiseVariance_pos)).toMeasure := by
  exact paper_proposition4_3_actual_gaussian_measure_observable_and_demographic_gaps
    S.baseSignals 0 S.testNoiseVariance S.testNoiseVariance_pos

theorem theorem44_mandatory_source_gaussian_resampling_fair [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature) :
    (∀ base,
      lg21D6ActualAccessEstimateKernel S.gaussianPBOResamplingSource base =
        lg21D6NoAccessResamplingEstimateKernel S.gaussianPBOResamplingSource base) ∧
      lg21D6ActualAccessEstimateLaw S.gaussianPBOResamplingSource =
        lg21D6NoAccessResamplingEstimateLaw S.gaussianPBOResamplingSource :=
  paper_theorem4_4_source_gaussian_pbo_resampling_fair
    S.gaussianPBOResamplingSource

/--
The checked Section 4 consequences available under the explicit mandatory
correction.  This is an output record: its only extra input is an arbitrary
well-formed no-access policy kernel for Proposition 4.2, not a law equality or
any conclusion-bearing fairness condition.  Proposition 4.3 and Theorem 4.4
remain explicitly separate all-PBO and resampling policy scopes.

It intentionally stops short of a raw-feature conditional-disintegration
claim.  That claim is the remaining proof obligation for a full archival
source bridge, not a premise hidden in this result.
-/
structure MandatorySection4Consequences [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature)
    (noAccessPolicy : ArbitraryNoAccessPolicy Feature) : Prop where
  mandatory_access_forced :
    ∀ action,
      LG21RequirementPolicy.feasibleAction
          LG21RequirementPolicy.reportRequiredGivenAccess
          LG21AccessStatus.access action →
        action = LG21AccessAction.takeAndReport
  proposition42_any_noAccess_policy_not_latentSkillFair :
    ¬ lg21P42ObservedScoreLatentSkillFair
      (S.observedScorePBOModel noAccessPolicy)
  proposition43_actual_measure_gaps :
    (∀ base : Feature → ℝ,
      (lg21P43ConditionalAccessOutputLaw S.baseSignals base 0
        S.testNoiseVariance S.testNoiseVariance_pos).toMeasure ≠
        Measure.dirac (S.baseSignals.posteriorMean base)) ∧
      S.baseSignals.posteriorMeanScaleLaw.toMeasure ≠
        (GaussianOffsetSignalFamily.posteriorMeanScaleLaw
          (S.baseSignals.withExtraSignal 0 S.testNoiseVariance
            S.testNoiseVariance_pos)).toMeasure
  theorem44_actual_resampling_fair :
    (∀ base,
      lg21D6ActualAccessEstimateKernel S.gaussianPBOResamplingSource base =
        lg21D6NoAccessResamplingEstimateKernel S.gaussianPBOResamplingSource base) ∧
      lg21D6ActualAccessEstimateLaw S.gaussianPBOResamplingSource =
        lg21D6NoAccessResamplingEstimateLaw S.gaussianPBOResamplingSource

theorem mandatorySection4Consequences [Nonempty Feature]
    (S : LG21MandatorySection4Source Feature)
    (noAccessPolicy : ArbitraryNoAccessPolicy Feature) :
    MandatorySection4Consequences S noAccessPolicy := by
  refine ⟨?_, ?_,
    S.proposition43_mandatory_actual_measure_gaps,
    S.theorem44_mandatory_source_gaussian_resampling_fair⟩
  · intro action hfeasible
    exact mandatory_access_action_eq_takeAndReport action hfeasible
  · exact paper_proposition4_2_actual_observed_score_not_latent_skill_fair_at
      (S.observedScorePBOModel noAccessPolicy) (fun _ => 0)
      (skillLow := 0) (skillHigh := 1) (by norm_num)

end LG21MandatorySection4Source

end

end LG21TestOptionalPolicies

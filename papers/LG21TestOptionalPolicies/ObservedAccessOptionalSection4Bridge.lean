import LG21TestOptionalPolicies.ObservedAccessOptionalD6OutputBridge
import LG21TestOptionalPolicies.Proposition42ActualGaussianMeasureRepair
import LG21TestOptionalPolicies.Section4LiteralGaussianMeanLawBridge

/-!
# Literal observed-access Section 4 bridge for LG21

This module keeps the two Section 4 layers separate.  The access-side PBO
experiment is constructed from the literal full non-test profile and its
derived Gaussian factorization.  The actual optional output is then linked to
that experiment only after the approved all-take/all-report source closeout.
The arbitrary no-access policy in Proposition 4.2 remains a kernel on the
full non-test profile.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The Proposition 4.2 observed-score model obtained from the same Gaussian
source used by Definition 6.  The no-access branch is an arbitrary policy on
the literal full non-test profile. -/
def lg21P42ObservedScoreModelOfD6Source
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21P42ObservedScoreGaussianPBOModel Base where
  basePosteriorMean := S.posteriorBaseMean
  basePosteriorMean_measurable := S.posteriorBaseMean_measurable
  basePosteriorVariance := S.posteriorBaseVariance
  basePosteriorVariance_pos := S.posteriorBaseVariance_pos
  latentSkillGivenBaseLaw := fun base =>
    gaussianReal (S.posteriorBaseMean base) S.posteriorBaseVariance
  latentSkillGivenBaseLaw_eq_gaussian := fun _ => rfl
  testNoiseVariance := S.testNoiseVariance
  testNoiseVariance_pos := S.testNoiseVariance_pos
  testScoreGivenSkillLaw := fun skill =>
    gaussianReal skill S.testNoiseVariance
  testScoreGivenSkillLaw_eq_gaussian := fun _ => rfl
  noAccessEstimateKernel := noAccessEstimateKernel
  noAccessEstimateKernel_isMarkov := inferInstance

/-- The Proposition 4.2 estimator constructed from the source factorization
is exactly the Definition 6 affine posterior estimator on the access branch. -/
theorem lg21P42ObservedScoreModelOfD6Source_estimate_eq_d6
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel]
    (base : Base) (score : ℝ) :
    lg21P42GaussianPBOEstimate
        (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel)
        base score =
      lg21D6GaussianPBOEstimate S (base, score) := by
  unfold lg21P42GaussianPBOEstimate lg21P42ObservedScoreModelOfD6Source
    LG21P42ObservedScoreGaussianPBOModel.pboIntercept
    LG21P42ObservedScoreGaussianPBOModel.pboSlope
    lg21D6GaussianPBOEstimate lg21D6PosteriorTestWeight
    gaussianSignalPriorWeight gaussianSignalWeight
  have hsum : (S.posteriorBaseVariance : ℝ) +
      (S.testNoiseVariance : ℝ) ≠ 0 :=
    ne_of_gt (lg21D6PosteriorVarianceSum_pos S)
  field_simp
  ring

/-- Proposition 4.2's conditional-law conclusion for the literal source
experiment.  The no-access policy remains arbitrary and base-indexed; no
matching law is an input. -/
theorem lg21P42ObservedScoreModelOfD6Source_not_latent_skill_fair
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel]
    (base : Base) {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    ¬ lg21P42ObservedScoreLatentSkillFair
      (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel) := by
  exact paper_proposition4_2_actual_observed_score_not_latent_skill_fair_at
    (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel)
    base hskill

/-- PBO for a student without the test: condition only on the literal full
non-test profile.  This is distinct from Definition 6, which deliberately
draws a synthetic test score. -/
def lg21D6NoAccessPBOEstimateKernel
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) : Kernel Base ℝ :=
  Kernel.deterministic S.posteriorBaseMean S.posteriorBaseMean_measurable

theorem lg21D6NoAccessPBOEstimateKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) (base : Base) :
    lg21D6NoAccessPBOEstimateKernel S base =
      Measure.dirac (S.posteriorBaseMean base) :=
  Kernel.deterministic_apply S.posteriorBaseMean_measurable base

/-- The conditional access estimate has positive residual variation because
the additional observed test has positive posterior weight and variance. -/
theorem lg21D6CommonEstimateVariance_pos
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) :
    0 < (lg21D6CommonEstimateVariance S : ℝ) := by
  have hweight : 0 < lg21D6PosteriorTestWeight S :=
    div_pos S.posteriorBaseVariance_pos (lg21D6PosteriorVarianceSum_pos S)
  have htest : 0 < (lg21D6ConditionalTestVariance S : ℝ) := by
    change 0 < (S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ)
    exact lg21D6PosteriorVarianceSum_pos S
  change 0 < (lg21D6PosteriorTestWeight S) ^ 2 *
    (lg21D6ConditionalTestVariance S : ℝ)
  exact mul_pos (sq_pos_of_pos hweight) htest

/-- The actual access PBO and the no-access PBO are observably different at
every literal full non-test profile.  This compares their concrete kernels,
not just two named Gaussian-law records. -/
theorem lg21D6ActualAccessEstimateKernel_ne_noAccessPBOEstimateKernel
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) (base : Base) :
    lg21D6ActualAccessEstimateKernel S base ≠
      lg21D6NoAccessPBOEstimateKernel S base := by
  intro heq
  have happly := congrArg (fun law : Measure ℝ =>
    law ({S.posteriorBaseMean base} : Set ℝ)) heq
  rw [lg21D6ActualAccessEstimateKernel_apply_gaussian,
    lg21D6NoAccessPBOEstimateKernel_apply] at happly
  have hvariance : lg21D6CommonEstimateVariance S ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast lg21D6CommonEstimateVariance_pos S)
  change gaussianReal (S.posteriorBaseMean base)
      (lg21D6CommonEstimateVariance S) ({S.posteriorBaseMean base} : Set ℝ) =
    Measure.dirac (S.posteriorBaseMean base)
      ({S.posteriorBaseMean base} : Set ℝ) at happly
  rw [gaussianReal_singleton_eq_zero
    (S.posteriorBaseMean base) hvariance] at happly
  norm_num at happly

/-- Once literal optional behavior has collapsed to all taking and reporting,
the actual source output law is the actual access estimate law of the same
Definition 6 Gaussian experiment. -/
theorem lg21_optional_actualOutputLaw_eq_d6ActualAccessEstimateLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    law.map (lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
      lg21D6ActualAccessEstimateLaw S := by
  intro S law
  have hactual :=
    lg21ContinuousGaussianAccessPopulation_optional_actualOutputLaw_eq_d6
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfullBaseFactorization
  have hsource :=
    lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  calc
    law.map (lg21OptionalSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
        (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
          simpa [law, observation] using hactual
    _ = (lg21D6ActualAccessTestLaw S).map (lg21D6GaussianPBOEstimate S) := by
          rw [show law.map observation = lg21D6ActualAccessTestLaw S by
            simpa [law, observation] using hsource]
    _ = lg21D6ActualAccessEstimateLaw S := rfl

/-- Source-timed optional counterpart of the actual access-output law.  This
uses the literal optional action and its on-path PBO transport, not the legacy
sequential-equilibrium wrapper. -/
theorem lg21_optional_sourceTimed_actualOutputLaw_eq_d6ActualAccessEstimateLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    law.map (lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
      lg21D6ActualAccessEstimateLaw S := by
  intro S law
  have hactual :=
    lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutputLaw_eq_d6
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfullBaseFactorization
  have hsource :=
    lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  calc
    law.map (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
        (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
          simpa [law, observation] using hactual
    _ = (lg21D6ActualAccessTestLaw S).map (lg21D6GaussianPBOEstimate S) := by
          rw [show law.map observation = lg21D6ActualAccessTestLaw S by
            simpa [law, observation] using hsource]
    _ = lg21D6ActualAccessEstimateLaw S := rfl

/-- Literal optional-policy Theorem 4.4 transport.  The access-side output is
the actual school output of the source equilibrium after the proved behavioral
closeout; the no-access output is Definition 6's literal conditional
resampling policy over the actual no-access base population. -/
theorem lg21ContinuousGaussianPopulation_optional_actualOutput_eq_noAccessResampling
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    (accessLaw.map (lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data)) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
  intro S accessLaw noAccessLaw
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  have hactual :=
    lg21_optional_actualOutputLaw_eq_d6ActualAccessEstimateLaw
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfullBaseFactorization
  have hd6 :=
    lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  calc
    accessLaw.map (lg21OptionalSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
        lg21D6ActualAccessEstimateLaw S := by
          simpa [accessLaw] using hactual
    _ = (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
          rw [lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
            M haccess testFeature baseLaw baseMean hbaseMean baseVariance
            hbaseVariance htestNoiseVariance hfullBaseFactorization]
          rfl
    _ = Measure.bind (noAccessLaw.map
          (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
          simpa [accessLaw, noAccessLaw, observation] using hd6

/-- Source-timed optional Theorem 4.4 transport.  The access output remains
the literal realized optional action output; its equality with the Definition
6 experiment is obtained only through the source-timed all-report/PBO path. -/
theorem lg21ContinuousGaussianPopulation_optional_sourceTimed_actualOutput_eq_noAccessResampling
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    accessLaw.map (lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
  intro S accessLaw noAccessLaw
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  have hactual :=
    lg21_optional_sourceTimed_actualOutputLaw_eq_d6ActualAccessEstimateLaw
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfullBaseFactorization
  have hd6 :=
    lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  calc
    accessLaw.map (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
        lg21D6ActualAccessEstimateLaw S := by
          simpa [accessLaw] using hactual
    _ = (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
          rw [lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
            M haccess testFeature baseLaw baseMean hbaseMean baseVariance
            hbaseVariance htestNoiseVariance hfullBaseFactorization]
          rfl
    _ = Measure.bind (noAccessLaw.map
          (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
          simpa [accessLaw, noAccessLaw, observation] using hd6

/-- The actual no-access PBO output law is the pushforward of the literal
no-access base marginal by its Gaussian posterior mean.  It is not inferred
from the access policy and does not use a synthetic score. -/
theorem lg21ContinuousGaussianNoAccessPopulation_pboOutputLaw_eq_baseMean
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    (lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (fun student => baseMean (lg21ContinuousPopulationBase testFeature student)) =
      baseLaw.map baseMean := by
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hbaseAccess :=
    lg21ContinuousGaussianAccessPopulation_baseLaw_eq_of_factorization
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  have hbaseNoAccess : noAccessLaw.map
      (lg21ContinuousPopulationBase testFeature) = baseLaw := by
    calc
      noAccessLaw.map (lg21ContinuousPopulationBase testFeature) =
          accessLaw.map (lg21ContinuousPopulationBase testFeature) := by
            simpa [accessLaw, noAccessLaw] using
              (lg21ContinuousGaussianAccess_noAccess_baseLaw_eq
                M haccess hnoAccess testFeature).symm
      _ = baseLaw := by simpa [accessLaw] using hbaseAccess
  calc
    (lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (fun student => baseMean (lg21ContinuousPopulationBase testFeature student)) =
        (noAccessLaw.map (lg21ContinuousPopulationBase testFeature)).map baseMean := by
          rw [Measure.map_map hbaseMean hbase]
          rfl
    _ = baseLaw.map baseMean := by rw [hbaseNoAccess]

/-- Literal optional-policy Proposition 4.3 endpoint.  The observable gap is
the pointwise distinction between the actual test-score PBO and the literal
no-access base PBO.  The demographic gap is proved separately from the
source-derived marginal Gaussian laws: the actual access output has the
strictly larger one-step variance, while the no-access output is the literal
base posterior-mean pushforward. -/
theorem lg21ContinuousGaussianPopulation_optional_proposition43_actual_gaps
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
             (LG21NonTestFeature Feature testFeature → ℝ) :=
           { baseLaw := baseLaw
             baseLaw_isProbability := inferInstance
             posteriorBaseMean := baseMean
             posteriorBaseMean_measurable := hbaseMean
             posteriorBaseVariance := baseVariance.toNNReal
             posteriorBaseVariance_pos := by
               rw [NNReal.coe_pos, Real.toNNReal_pos]
               exact hbaseVariance
             testNoiseVariance := M.noiseVariance testFeature
             testNoiseVariance_pos := htestNoiseVariance }
         (∀ base,
           lg21D6ActualAccessEstimateKernel S base ≠
             lg21D6NoAccessPBOEstimateKernel S base) ∧
         (lg21ContinuousGaussianAccessPopulationLaw M).map
             (lg21OptionalSequentialActualOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousPopulationFeature testFeature)
               (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) ≠
           (lg21ContinuousGaussianNoAccessPopulationLaw M).map
             (fun student => baseMean
               (lg21ContinuousPopulationBase testFeature student))) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hmeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature → ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := hbaseLaw
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  change
    (∀ base,
      lg21D6ActualAccessEstimateKernel S base ≠
        lg21D6NoAccessPBOEstimateKernel S base) ∧
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21OptionalSequentialActualOutput
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) ≠
        (lg21ContinuousGaussianNoAccessPopulationLaw M).map
          (fun student => baseMean
            (lg21ContinuousPopulationBase testFeature student))
  refine ⟨?_, ?_⟩
  · intro base
    exact lg21D6ActualAccessEstimateKernel_ne_noAccessPBOEstimateKernel S base
  · intro heq
    apply (lg21D6ActualAccessEstimateLaw_ne_baseMeanLaw
      S M.priorMean baseMeanVariance hbaseMeanVariance hmeanLaw)
    calc
      lg21D6ActualAccessEstimateLaw S =
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21OptionalSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) := by
              symm
              exact lg21_optional_actualOutputLaw_eq_d6ActualAccessEstimateLaw
                M haccess testFeature hpriorVariance hnonTestNoiseVariance
                htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
                hbaseVariance hfactorization
      _ = (lg21ContinuousGaussianNoAccessPopulationLaw M).map
          (fun student => baseMean
            (lg21ContinuousPopulationBase testFeature student)) := heq
      _ = baseLaw.map baseMean :=
          lg21ContinuousGaussianNoAccessPopulation_pboOutputLaw_eq_baseMean
            M haccess hnoAccess testFeature baseLaw baseMean hbaseMean
            baseVariance hbaseVariance htestNoiseVariance hfactorization

/-- Source-timed optional Proposition 4.3 endpoint.  The access output in the
law comparison is the literal source action output, not a legacy equilibrium
wrapper's reported-payoff projection. -/
theorem lg21ContinuousGaussianPopulation_optional_sourceTimed_proposition43_actual_gaps
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
             (LG21NonTestFeature Feature testFeature → ℝ) :=
           { baseLaw := baseLaw
             baseLaw_isProbability := inferInstance
             posteriorBaseMean := baseMean
             posteriorBaseMean_measurable := hbaseMean
             posteriorBaseVariance := baseVariance.toNNReal
             posteriorBaseVariance_pos := by
               rw [NNReal.coe_pos, Real.toNNReal_pos]
               exact hbaseVariance
             testNoiseVariance := M.noiseVariance testFeature
             testNoiseVariance_pos := htestNoiseVariance }
         (∀ base,
           lg21D6ActualAccessEstimateKernel S base ≠
             lg21D6NoAccessPBOEstimateKernel S base) ∧
         (lg21ContinuousGaussianAccessPopulationLaw M).map
             (lg21OptionalSourceTimedActualOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousPopulationFeature testFeature)
               (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) ≠
           (lg21ContinuousGaussianNoAccessPopulationLaw M).map
             (fun student => baseMean
               (lg21ContinuousPopulationBase testFeature student))) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hmeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature → ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := hbaseLaw
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  change
    (∀ base,
      lg21D6ActualAccessEstimateKernel S base ≠
        lg21D6NoAccessPBOEstimateKernel S base) ∧
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) ≠
        (lg21ContinuousGaussianNoAccessPopulationLaw M).map
          (fun student => baseMean
            (lg21ContinuousPopulationBase testFeature student))
  refine ⟨?_, ?_⟩
  · intro base
    exact lg21D6ActualAccessEstimateKernel_ne_noAccessPBOEstimateKernel S base
  · intro heq
    apply (lg21D6ActualAccessEstimateLaw_ne_baseMeanLaw
      S M.priorMean baseMeanVariance hbaseMeanVariance hmeanLaw)
    calc
      lg21D6ActualAccessEstimateLaw S =
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) := by
              symm
              exact lg21_optional_sourceTimed_actualOutputLaw_eq_d6ActualAccessEstimateLaw
                M haccess testFeature hpriorVariance hnonTestNoiseVariance
                htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
                hbaseVariance hfactorization
      _ = (lg21ContinuousGaussianNoAccessPopulationLaw M).map
          (fun student => baseMean
            (lg21ContinuousPopulationBase testFeature student)) := heq
      _ = baseLaw.map baseMean :=
          lg21ContinuousGaussianNoAccessPopulation_pboOutputLaw_eq_baseMean
            M haccess hnoAccess testFeature baseLaw baseMean hbaseMean
            baseVariance hbaseVariance htestNoiseVariance hfactorization

/-- Literal finite-source Proposition 4.2 endpoint.  It contains both the
actual behavior/output transport and the policy-level latent-skill gap.  The
only no-access input is the arbitrary raw-base kernel quantified by the
source proposition. -/
theorem lg21ContinuousGaussianPopulation_optional_proposition42
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
    (noAccessEstimateKernel :
      Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean) (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
            (LG21NonTestFeature Feature testFeature -> ℝ) :=
          { baseLaw := baseLaw
            baseLaw_isProbability := inferInstance
            posteriorBaseMean := baseMean
            posteriorBaseMean_measurable := hbaseMean
            posteriorBaseVariance := baseVariance.toNNReal
            posteriorBaseVariance_pos := by
              rw [NNReal.coe_pos, Real.toNNReal_pos]
              exact hbaseVariance
            testNoiseVariance := M.noiseVariance testFeature
            testNoiseVariance_pos := htestNoiseVariance }
         ¬ lg21P42ObservedScoreLatentSkillFair
            (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel) ∧
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21OptionalSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
            lg21D6ActualAccessEstimateLaw S) := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseLaw, hbaseMean,
    hbaseVariance, hfactorization, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := hbaseLaw
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  change ¬ lg21P42ObservedScoreLatentSkillFair
      (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel) ∧
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21OptionalSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
      lg21D6ActualAccessEstimateLaw S
  refine ⟨?_, ?_⟩
  · exact lg21P42ObservedScoreModelOfD6Source_not_latent_skill_fair
      S noAccessEstimateKernel (fun _ => 0)
      (skillLow := 0) (skillHigh := 1) (by norm_num)
  · exact lg21_optional_actualOutputLaw_eq_d6ActualAccessEstimateLaw
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization

/-- Source-timed optional Proposition 4.2 endpoint.  The realized access law
is transported from the literal actual optional output, while the no-access
policy remains the arbitrary source kernel quantified by the proposition. -/
theorem lg21ContinuousGaussianPopulation_optional_sourceTimed_proposition42
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (noAccessEstimateKernel :
      Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean) (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
            (LG21NonTestFeature Feature testFeature -> ℝ) :=
          { baseLaw := baseLaw
            baseLaw_isProbability := inferInstance
            posteriorBaseMean := baseMean
            posteriorBaseMean_measurable := hbaseMean
            posteriorBaseVariance := baseVariance.toNNReal
            posteriorBaseVariance_pos := by
              rw [NNReal.coe_pos, Real.toNNReal_pos]
              exact hbaseVariance
            testNoiseVariance := M.noiseVariance testFeature
            testNoiseVariance_pos := htestNoiseVariance }
         ¬ lg21P42ObservedScoreLatentSkillFair
            (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel) ∧
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
            lg21D6ActualAccessEstimateLaw S) := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseLaw, hbaseMean,
    hbaseVariance, hfactorization, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := hbaseLaw
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  change ¬ lg21P42ObservedScoreLatentSkillFair
      (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel) ∧
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
      lg21D6ActualAccessEstimateLaw S
  refine ⟨?_, ?_⟩
  · exact lg21P42ObservedScoreModelOfD6Source_not_latent_skill_fair
      S noAccessEstimateKernel (fun _ => 0)
      (skillLow := 0) (skillHigh := 1) (by norm_num)
  · exact lg21_optional_sourceTimed_actualOutputLaw_eq_d6ActualAccessEstimateLaw
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization

end

end LG21TestOptionalPolicies

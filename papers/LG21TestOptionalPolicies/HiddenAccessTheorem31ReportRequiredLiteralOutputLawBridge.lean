import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredSourceCloseout
/- The imported literal-output module is used below only for source-PBO
   integrability and population/primitive measure transport.  This file never
   invokes its optional-report behavioral or fairness theorems. -/
import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralOutputLawBridge
import LG21TestOptionalPolicies.StrategicDominanceContinuous

/-!
# Actual-output-law bridge for report-required LG21 Theorem 3.1

The report-required protocol has one strategic decision: whether to take the
test before its score is realized.  A taker must report the realized score.
Consequently the relevant fairness object is the law of the *actual public
output*.  A strict ex-ante gain need not give pointwise dominance of realized
outputs, so this file derives law inequality through expectations (or through
a positive actual-output event), never through FOSD.

Nothing here invokes an optional score-stage report/withhold deviation.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Actual output functions -/

/-- Actual public output for an access student in the report-required
protocol.  Taking is decided before observing the score; reporting is forced
after taking. -/
def lg21HiddenAccessReportRequiredSourceOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (score : ℝ) : ℝ :=
  if E.source.takeDecision skill publicBase = true then
    E.source.reportedPayoff publicBase score
  else E.source.noReportPayoff publicBase

/-- Actual report-required output on the literal primitive source student. -/
def lg21HiddenAccessReportRequiredPrimitiveAccessOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (primitive : ℝ × (Feature → ℝ)) : ℝ :=
  lg21HiddenAccessReportRequiredSourceOutput E primitive.1
    (lg21HiddenAccessStudentBase testFeature primitive)
    (lg21HiddenAccessStudentScore testFeature primitive)

/-- The actual output for a no-access source student. -/
def lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (primitive : ℝ × (Feature → ℝ)) : ℝ :=
  E.source.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive)

/-- Actual output law conditional on a fixed latent skill and non-test base. -/
def lg21HiddenAccessReportRequiredLatentAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    Measure ℝ :=
  (E.source.testLaw skill publicBase).map
    (lg21HiddenAccessReportRequiredSourceOutput E skill publicBase)

/-- At a fixed non-test base, no access yields the no-report point mass. -/
def lg21HiddenAccessReportRequiredNoAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ) : Measure ℝ :=
  Measure.dirac (E.source.noReportPayoff publicBase)

/-- Actual output law at a fixed observable non-test base, before conditioning
on the unobserved latent skill.  The joint source law is ordered
`(observed score, latent skill)`. -/
def lg21HiddenAccessReportRequiredObservableAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ) : Measure ℝ :=
  (gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ) publicBase).map
      (fun scoreSkill =>
        lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
          scoreSkill.1)

/-- Actual access demographic output law.  This uses the literal primitive
population, which is transported to the true access-conditioned population
below. -/
def lg21HiddenAccessReportRequiredDemographicAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Measure ℝ :=
  (lg21ContinuousGaussianStudentPrimitiveLaw M).map
    (lg21HiddenAccessReportRequiredPrimitiveAccessOutput E)

/-- Actual no-access demographic output law on the shared literal primitive
population. -/
def lg21HiddenAccessReportRequiredDemographicNoAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Measure ℝ :=
  (lg21ContinuousGaussianStudentPrimitiveLaw M).map
    (lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E)

/-- The actual access-conditioned population output law in the forced-report
protocol.  The underlying public-output map is the literal source map; the
forced-report wrapper below records why it is the report-required map. -/
def lg21HiddenAccessReportRequiredActualDemographicAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Measure ℝ :=
  lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E.source

/-- The actual no-access population output law in the forced-report protocol. -/
def lg21HiddenAccessReportRequiredActualDemographicNoAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Measure ℝ :=
  lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E.source

/-! ## Measurability and elementary law separation -/

theorem lg21HiddenAccessReportRequiredSourceOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    Measurable (lg21HiddenAccessReportRequiredSourceOutput E skill publicBase) := by
  unfold lg21HiddenAccessReportRequiredSourceOutput
  apply Measurable.ite
    ((measurableSet_singleton true).preimage
      (E.source.takeDecision_measurable.comp
        (measurable_const.prodMk measurable_const)))
  · exact E.source.reportedPayoff_measurable.comp
      (measurable_const.prodMk measurable_id)
  · exact measurable_const

theorem lg21HiddenAccessReportRequiredObservableAccessOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    Measurable (fun scoreSkill : ℝ × ℝ =>
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1) := by
  unfold lg21HiddenAccessReportRequiredSourceOutput
  apply Measurable.ite
    ((measurableSet_singleton true).preimage
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_const)))
  · exact E.source.reportedPayoff_measurable.comp
      (measurable_const.prodMk measurable_fst)
  · exact measurable_const

theorem lg21HiddenAccessReportRequiredPrimitiveAccessOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Measurable (lg21HiddenAccessReportRequiredPrimitiveAccessOutput E) := by
  unfold lg21HiddenAccessReportRequiredPrimitiveAccessOutput
  unfold lg21HiddenAccessReportRequiredSourceOutput
  have hbase : Measurable (lg21HiddenAccessStudentBase (Feature := Feature) testFeature) :=
    lg21HiddenAccessStudentBase_measurable testFeature
  have hscore : Measurable (lg21HiddenAccessStudentScore (Feature := Feature) testFeature) :=
    lg21HiddenAccessStudentScore_measurable testFeature
  apply Measurable.ite
    ((measurableSet_singleton true).preimage
      (E.source.takeDecision_measurable.comp (measurable_fst.prodMk hbase)))
  · exact E.source.reportedPayoff_measurable.comp (hbase.prodMk hscore)
  · exact E.source.noReportPayoff_measurable.comp hbase

theorem lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Measurable (lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E) := by
  unfold lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput
  exact E.source.noReportPayoff_measurable.comp
    (lg21HiddenAccessStudentBase_measurable testFeature)

/-! ## Forced-report reduction and source-PBO integrability -/

/-- The shared literal source output reduces to the forced-report output when
the only feasible post-score action is reporting. -/
theorem lg21HiddenAccessReportRequiredSourceOutput_eq_optional
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (score : ℝ) :
    lg21HiddenAccessReportRequiredSourceOutput E skill publicBase score =
      lg21HiddenAccessOptionalSourceOutput E.source skill publicBase score := by
  simp [lg21HiddenAccessReportRequiredSourceOutput,
    lg21HiddenAccessOptionalSourceOutput, E.reportDecision_eq_true]

theorem lg21HiddenAccessReportRequiredPrimitiveAccessOutput_eq_optional
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    lg21HiddenAccessReportRequiredPrimitiveAccessOutput E =
      lg21HiddenAccessOptionalPrimitiveAccessOutput E.source := by
  funext primitive
  simp only [lg21HiddenAccessReportRequiredPrimitiveAccessOutput,
    lg21HiddenAccessOptionalPrimitiveAccessOutput]
  exact lg21HiddenAccessReportRequiredSourceOutput_eq_optional E _ _ _

theorem lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput_eq_optional
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E =
      lg21HiddenAccessOptionalPrimitiveNoAccessOutput E.source := by
  rfl

/-- Finiteness of the forced-report access output is inherited from the
literal public PBO.  This invokes only the measure-theoretic source-PBO lemma
from the shared carrier, not an optional-reporting best response. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.primitiveAccessOutput_integrable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    Integrable (lg21HiddenAccessReportRequiredPrimitiveAccessOutput E)
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
  rw [lg21HiddenAccessReportRequiredPrimitiveAccessOutput_eq_optional]
  exact E.source.primitiveAccessOutput_integrable

/-- The same source-PBO argument supplies integrability of the no-access
actual output whenever that population has positive mass. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.primitiveNoAccessOutput_integrable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    Integrable (lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E)
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
  rw [lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput_eq_optional]
  exact E.source.primitiveNoAccessOutput_integrable hnoAccess

/-- The literal primitive-law output is exactly the actual access-conditioned
population output in the forced-report protocol. -/
theorem lg21HiddenAccessReportRequired_actualDemographicAccessOutputLaw_eq_primitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    lg21HiddenAccessReportRequiredActualDemographicAccessOutputLaw E =
      lg21HiddenAccessReportRequiredDemographicAccessOutputLaw E := by
  change lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E.source =
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map
      (lg21HiddenAccessReportRequiredPrimitiveAccessOutput E)
  rw [lg21HiddenAccessOptional_actualDemographicAccessOutputLaw_eq_primitive E.source,
    lg21HiddenAccessReportRequiredPrimitiveAccessOutput_eq_optional]
  rfl

/-- The literal primitive-law no-access output is exactly the true no-access
population output; the positive-mass condition is required only to form the
conditioned no-access law. -/
theorem lg21HiddenAccessReportRequired_actualDemographicNoAccessOutputLaw_eq_primitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    lg21HiddenAccessReportRequiredActualDemographicNoAccessOutputLaw E =
      lg21HiddenAccessReportRequiredDemographicNoAccessOutputLaw E := by
  change lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E.source =
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map
      (lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E)
  rw [lg21HiddenAccessOptional_actualDemographicNoAccessOutputLaw_eq_primitive
    E.source hnoAccess,
    lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput_eq_optional]
  rfl

/-- A difference of integrable actual-output means proves output-law
inequality.  This is intentionally semantic: it depends only on the output
map and the probability law, not on names or strategy representations. -/
theorem lg21_outputLaw_ne_dirac_of_integral_ne
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) [IsProbabilityMeasure outcomeLaw]
    (output : Outcome → ℝ) (houtput : Measurable output)
    (hintegrable : Integrable output outcomeLaw) (noReportValue : ℝ)
    (hmean : (∫ outcome, output outcome ∂outcomeLaw) ≠ noReportValue) :
    outcomeLaw.map output ≠ Measure.dirac noReportValue := by
  have hne := lg21_map_ne_of_integral_ne outcomeLaw output (fun _ : Outcome => noReportValue)
    houtput measurable_const hintegrable (integrable_const noReportValue)
  have hconstant : outcomeLaw.map (fun _ : Outcome => noReportValue) =
      Measure.dirac noReportValue := by
    simpa using (Measure.map_const outcomeLaw noReportValue)
  rw [hconstant] at hne
  apply hne
  simpa using hmean

/-! ## Fixed latent-skill witness -/

/-- A strict pre-score expected gain for a taker yields a genuine inequality
of *actual output laws* at that latent skill and base.  This does not claim
that every realized test output exceeds the no-report output. -/
theorem lg21HiddenAccessReportRequired_latentOutputLaw_ne_of_strictExpectedGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (htake : E.source.takeDecision skill publicBase = true)
    (hstrict : E.source.noReportPayoff publicBase <
      ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw skill publicBase) :
    lg21HiddenAccessReportRequiredLatentAccessOutputLaw E skill publicBase ≠
      lg21HiddenAccessReportRequiredNoAccessOutputLaw E publicBase := by
  letI : IsProbabilityMeasure (E.source.testLaw skill publicBase) :=
    E.source.testLaw_isProbability skill publicBase
  have hintegrable : Integrable (E.source.reportedPayoff publicBase)
      (E.source.testLaw skill publicBase) := by
    simpa only [E.reportDecision_eq_true, if_true] using
      E.source.continuationPayoff_integrable skill publicBase
  have houtput : lg21HiddenAccessReportRequiredSourceOutput E skill publicBase =
      E.source.reportedPayoff publicBase := by
    funext score
    simp [lg21HiddenAccessReportRequiredSourceOutput, htake]
  change (E.source.testLaw skill publicBase).map
      (lg21HiddenAccessReportRequiredSourceOutput E skill publicBase) ≠
    Measure.dirac (E.source.noReportPayoff publicBase)
  rw [houtput]
  exact lg21_outputLaw_ne_dirac_of_integral_ne
    (E.source.testLaw skill publicBase) (E.source.reportedPayoff publicBase)
    (E.source.reportedPayoff_measurable.comp
      (measurable_const.prodMk measurable_id)) hintegrable
    (E.source.noReportPayoff publicBase) (ne_of_gt hstrict)

/-! ## Semantic strict-gain extraction -/

/-- Under an atomless source law, a positive mass of chosen actions has a
strict rather than merely weak expected gain whenever the chosen payoff is
strictly monotone.  This is a semantic binary-choice fact; it does not depend
on a threshold representation or a name for the action. -/
theorem lg21_positive_strictChosenGain_of_strictMono
    (law : Measure ℝ) [NoAtoms law]
    (decision : ℝ → Bool) (chosenPayoff : ℝ → ℝ) (outside : ℝ)
    (hbest : NoProfitableBinaryChoiceDeviationAE law
      (fun skill => decision skill = true) chosenPayoff (fun _ => outside))
    (hstrict : StrictMono chosenPayoff)
    (hchosen : 0 < law {skill | decision skill = true}) :
    0 < law {skill | decision skill = true ∧ outside < chosenPayoff skill} := by
  by_contra hnotPositive
  have hbadZero : law {skill |
      ¬ (decision skill = true -> outside ≤ chosenPayoff skill)} = 0 :=
    ae_iff.mp hbest.1
  have htieZero : law {skill | chosenPayoff skill = outside} = 0 :=
    lg21_strictMono_tieLevel_null law chosenPayoff hstrict outside
  have hstrictZero : law
      {skill | decision skill = true ∧ outside < chosenPayoff skill} = 0 := by
    exact bot_unique (le_of_not_gt hnotPositive)
  have hsubset : {skill | decision skill = true} ⊆
      {skill | ¬ (decision skill = true -> outside ≤ chosenPayoff skill)} ∪
        {skill | chosenPayoff skill = outside} ∪
          {skill | decision skill = true ∧ outside < chosenPayoff skill} := by
    intro skill hchoose
    by_cases hbad : ¬ (decision skill = true -> outside ≤ chosenPayoff skill)
    · exact Or.inl (Or.inl hbad)
    · have hle : outside ≤ chosenPayoff skill := (not_not.mp hbad) hchoose
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr ⟨hchoose, hlt⟩
      · exact Or.inl (Or.inr heq.symm)
  have hunionZero : law
      ({skill | ¬ (decision skill = true -> outside ≤ chosenPayoff skill)} ∪
        {skill | chosenPayoff skill = outside} ∪
          {skill | decision skill = true ∧ outside < chosenPayoff skill}) = 0 := by
    exact measure_union_null (measure_union_null hbadZero htieZero) hstrictZero
  have hchosenZero : law {skill | decision skill = true} = 0 :=
    measure_mono_null hsubset hunionZero
  exact (ne_of_gt hchosen) hchosenZero

/-! ## Gaussian actual-output tower -/

/-- The actual report-required output mean on one observable base fibre is
the pre-score mean: a type that takes contributes its score-average reported
output, while a type that declines contributes its no-report output.  The
proof expands the Gaussian joint law into latent skill plus independent noise
and applies Fubini.  It makes no pointwise comparison between a realized
score output and the no-report output. -/
theorem lg21HiddenAccessReportRequired_observableOutput_integral_eq_preScoreMean
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hintegrable : Integrable (fun scoreSkill : ℝ × ℝ =>
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1)
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase)) :
    (∫ scoreSkill,
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1
      ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase) =
      ∫ latentSkill,
        if E.source.takeDecision latentSkill publicBase = true then
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase
        else E.source.noReportPayoff publicBase
      ∂gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
  let skillLaw : Measure ℝ :=
    gaussianReal (baseMean publicBase) baseVariance.toNNReal
  let noiseLaw : Measure ℝ := gaussianReal 0 (M.noiseVariance testFeature)
  let stage : ℝ × ℝ → ℝ × ℝ := fun skillNoise =>
    (skillNoise.1 + skillNoise.2, skillNoise.1)
  let output : ℝ × ℝ → ℝ := fun scoreSkill =>
    lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
      scoreSkill.1
  have hstage : Measurable stage := by
    dsimp [stage]
    fun_prop
  have houtputMeasurable : Measurable output := by
    exact lg21HiddenAccessReportRequiredObservableAccessOutput_measurable E publicBase
  have houtput : StronglyMeasurable output := houtputMeasurable.stronglyMeasurable
  have hjoint : gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) publicBase =
      (skillLaw.prod noiseLaw).map stage := by
    rw [gaussianSignalJointKernel_apply]
    simp [skillLaw, noiseLaw, stage, gaussianSignalPair]
  have hstageIntegrable : Integrable (fun skillNoise => output (stage skillNoise))
      (skillLaw.prod noiseLaw) := by
    rw [hjoint] at hintegrable
    exact hintegrable.comp_measurable hstage
  have hinner : ∀ latentSkill,
      (∫ noise,
        output (stage (latentSkill, noise)) ∂noiseLaw) =
        if E.source.takeDecision latentSkill publicBase = true then
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase
        else E.source.noReportPayoff publicBase := by
    intro latentSkill
    by_cases htake : E.source.takeDecision latentSkill publicBase = true
    · have hadd : Measurable (fun noise : ℝ => latentSkill + noise) := by fun_prop
      have hnoiseMap : noiseLaw.map (fun noise : ℝ => latentSkill + noise) =
          E.source.testLaw latentSkill publicBase := by
        have haddComm : (fun noise : ℝ => latentSkill + noise) =
            fun noise => noise + latentSkill := by
          funext noise
          ring
        rw [haddComm]
        rw [E.source.raw_test_law latentSkill publicBase]
        simpa [noiseLaw] using
          (gaussianReal_map_add_const (μ := (0 : ℝ))
            (v := M.noiseVariance testFeature) latentSkill)
      simp only [output, stage, lg21HiddenAccessReportRequiredSourceOutput,
        htake, if_true]
      calc
        (∫ noise, E.source.reportedPayoff publicBase (latentSkill + noise)
            ∂noiseLaw) =
            ∫ score, E.source.reportedPayoff publicBase score
              ∂noiseLaw.map (fun noise : ℝ => latentSkill + noise) := by
                symm
                exact integral_map_of_stronglyMeasurable hadd
                  (E.source.reportedPayoff_measurable.comp
                    (measurable_const.prodMk measurable_id)).stronglyMeasurable
        _ = ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase := by rw [hnoiseMap]
    · letI : IsProbabilityMeasure noiseLaw := by
        dsimp [noiseLaw]
        infer_instance
      simp [output, stage, lg21HiddenAccessReportRequiredSourceOutput, htake]
  calc
    (∫ scoreSkill, output scoreSkill
      ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase) =
        ∫ skillNoise, output (stage skillNoise) ∂(skillLaw.prod noiseLaw) := by
          rw [hjoint]
          exact integral_map_of_stronglyMeasurable hstage houtput
    _ = ∫ latentSkill, ∫ noise,
          output (stage (latentSkill, noise)) ∂noiseLaw ∂skillLaw := by
          exact integral_prod _ hstageIntegrable
    _ = ∫ latentSkill,
        if E.source.takeDecision latentSkill publicBase = true then
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase
        else E.source.noReportPayoff publicBase ∂skillLaw := by
          apply integral_congr_ae
          filter_upwards with latentSkill
          exact hinner latentSkill
    _ = ∫ latentSkill,
        if E.source.takeDecision latentSkill publicBase = true then
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase
        else E.source.noReportPayoff publicBase
        ∂gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
          rfl

/-- The Fubini argument for the report-required observable output also
supplies integrability of its pre-score mixture.  Keeping this certificate
beside the tower identity prevents a later comparison from treating a formal
integral as an automatically finite expected output. -/
theorem lg21HiddenAccessReportRequired_observableOutput_preScoreMean_tower
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hintegrable : Integrable (fun scoreSkill : ℝ × ℝ =>
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1)
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase)) :
    Integrable (fun latentSkill =>
      if E.source.takeDecision latentSkill publicBase = true then
        ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase
      else E.source.noReportPayoff publicBase)
      (gaussianReal (baseMean publicBase) baseVariance.toNNReal) ∧
    (∫ scoreSkill,
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1
      ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase) =
      ∫ latentSkill,
        if E.source.takeDecision latentSkill publicBase = true then
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase
        else E.source.noReportPayoff publicBase
      ∂gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
  let skillLaw : Measure ℝ :=
    gaussianReal (baseMean publicBase) baseVariance.toNNReal
  let noiseLaw : Measure ℝ := gaussianReal 0 (M.noiseVariance testFeature)
  let stage : ℝ × ℝ → ℝ × ℝ := fun skillNoise =>
    (skillNoise.1 + skillNoise.2, skillNoise.1)
  let output : ℝ × ℝ → ℝ := fun scoreSkill =>
    lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
      scoreSkill.1
  have hstage : Measurable stage := by
    dsimp [stage]
    fun_prop
  have houtputMeasurable : Measurable output := by
    exact lg21HiddenAccessReportRequiredObservableAccessOutput_measurable E publicBase
  have houtput : StronglyMeasurable output := houtputMeasurable.stronglyMeasurable
  have hjoint : gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) publicBase =
      (skillLaw.prod noiseLaw).map stage := by
    rw [gaussianSignalJointKernel_apply]
    simp [skillLaw, noiseLaw, stage, gaussianSignalPair]
  have hstageIntegrable : Integrable (fun skillNoise => output (stage skillNoise))
      (skillLaw.prod noiseLaw) := by
    rw [hjoint] at hintegrable
    exact hintegrable.comp_measurable hstage
  have hinner : ∀ latentSkill,
      (∫ noise,
        output (stage (latentSkill, noise)) ∂noiseLaw) =
        if E.source.takeDecision latentSkill publicBase = true then
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase
        else E.source.noReportPayoff publicBase := by
    intro latentSkill
    by_cases htake : E.source.takeDecision latentSkill publicBase = true
    · have hadd : Measurable (fun noise : ℝ => latentSkill + noise) := by fun_prop
      have hnoiseMap : noiseLaw.map (fun noise : ℝ => latentSkill + noise) =
          E.source.testLaw latentSkill publicBase := by
        have haddComm : (fun noise : ℝ => latentSkill + noise) =
            fun noise => noise + latentSkill := by
          funext noise
          ring
        rw [haddComm]
        rw [E.source.raw_test_law latentSkill publicBase]
        simpa [noiseLaw] using
          (gaussianReal_map_add_const (μ := (0 : ℝ))
            (v := M.noiseVariance testFeature) latentSkill)
      simp only [output, stage, lg21HiddenAccessReportRequiredSourceOutput,
        htake, if_true]
      calc
        (∫ noise, E.source.reportedPayoff publicBase (latentSkill + noise)
            ∂noiseLaw) =
            ∫ score, E.source.reportedPayoff publicBase score
              ∂noiseLaw.map (fun noise : ℝ => latentSkill + noise) := by
                symm
                exact integral_map_of_stronglyMeasurable hadd
                  (E.source.reportedPayoff_measurable.comp
                    (measurable_const.prodMk measurable_id)).stronglyMeasurable
        _ = ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase := by rw [hnoiseMap]
    · letI : IsProbabilityMeasure noiseLaw := by
        dsimp [noiseLaw]
        infer_instance
      simp [output, stage, lg21HiddenAccessReportRequiredSourceOutput, htake]
  have hpreScoreIntegrableRaw : Integrable (fun latentSkill =>
      ∫ noise, output (stage (latentSkill, noise)) ∂noiseLaw) skillLaw :=
    hstageIntegrable.integral_prod_left
  have hpreScoreIntegrable : Integrable (fun latentSkill =>
      if E.source.takeDecision latentSkill publicBase = true then
        ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase
      else E.source.noReportPayoff publicBase) skillLaw := by
    exact hpreScoreIntegrableRaw.congr (Filter.Eventually.of_forall hinner)
  refine ⟨?_, ?_⟩
  · simpa [skillLaw] using hpreScoreIntegrable
  · calc
      (∫ scoreSkill, output scoreSkill
        ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) publicBase) =
          ∫ skillNoise, output (stage skillNoise) ∂(skillLaw.prod noiseLaw) := by
            rw [hjoint]
            exact integral_map_of_stronglyMeasurable hstage houtput
      _ = ∫ latentSkill, ∫ noise,
            output (stage (latentSkill, noise)) ∂noiseLaw ∂skillLaw := by
            exact integral_prod _ hstageIntegrable
      _ = ∫ latentSkill,
          if E.source.takeDecision latentSkill publicBase = true then
            ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase
          else E.source.noReportPayoff publicBase ∂skillLaw := by
            apply integral_congr_ae
            filter_upwards with latentSkill
            exact hinner latentSkill
      _ = ∫ latentSkill,
          if E.source.takeDecision latentSkill publicBase = true then
            ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase
          else E.source.noReportPayoff publicBase
          ∂gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
            rfl

/-- On one nondegenerate Gaussian base fibre, a positive mass of students who
choose testing and receive a strict *pre-score* gain makes the mean of the
actual forced-report output strictly exceed the no-report output.  The proof
uses only the taking best response and the pre-score tower; it does not make a
pointwise claim about realized score outputs. -/
theorem lg21HiddenAccessReportRequired_observableOutput_integral_gt_noReport_of_localFacts
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hintegrable : Integrable (fun scoreSkill : ℝ × ℝ =>
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1)
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase))
    (hbest : NoProfitableBinaryChoiceDeviationAE
      (gaussianReal (baseMean publicBase) baseVariance.toNNReal)
      (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
      (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase)
      (fun _ => E.source.noReportPayoff publicBase))
    (hstrict : StrictMono (fun latentSkill =>
      ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase))
    (hchosen : 0 < gaussianReal (baseMean publicBase) baseVariance.toNNReal
      {latentSkill | E.source.takeDecision latentSkill publicBase = true}) :
    E.source.noReportPayoff publicBase <
      ∫ scoreSkill,
        lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
          scoreSkill.1
      ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase := by
  let skillLaw : Measure ℝ :=
    gaussianReal (baseMean publicBase) baseVariance.toNNReal
  let preScoreOutput : ℝ → ℝ := fun latentSkill =>
    if E.source.takeDecision latentSkill publicBase = true then
      ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase
    else E.source.noReportPayoff publicBase
  letI : IsProbabilityMeasure skillLaw := by
    dsimp [skillLaw]
    infer_instance
  letI : NoAtoms skillLaw := by
    dsimp [skillLaw]
    exact ProbabilityTheory.noAtoms_gaussianReal
      (ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance))
  have hpreScoreIntegrable : Integrable preScoreOutput skillLaw := by
    simpa [preScoreOutput, skillLaw] using
      (lg21HiddenAccessReportRequired_observableOutput_preScoreMean_tower
        E publicBase baseMean hbaseMean baseVariance hintegrable).1
  have hstrictChosen : 0 < skillLaw
      {latentSkill | E.source.takeDecision latentSkill publicBase = true ∧
        E.source.noReportPayoff publicBase <
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase} := by
    simpa [skillLaw] using
      (lg21_positive_strictChosenGain_of_strictMono skillLaw
        (fun latentSkill => E.source.takeDecision latentSkill publicBase)
        (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase)
        (E.source.noReportPayoff publicBase) hbest hstrict (by simpa [skillLaw] using hchosen))
  have hle : (fun _ : ℝ => E.source.noReportPayoff publicBase) ≤ᵐ[skillLaw]
      preScoreOutput := by
    filter_upwards [hbest.1] with latentSkill hbestAt
    by_cases htake : E.source.takeDecision latentSkill publicBase = true
    · simpa [preScoreOutput, htake] using hbestAt htake
    · simp [preScoreOutput, htake]
  have hstrictPre : skillLaw
      {latentSkill | E.source.noReportPayoff publicBase <
        preScoreOutput latentSkill} ≠ 0 := by
    apply ne_of_gt
    apply lt_of_lt_of_le hstrictChosen
    apply measure_mono
    intro latentSkill hgain
    rcases hgain with ⟨htake, hstrictGain⟩
    simpa [preScoreOutput, htake] using hstrictGain
  have hmeanLe :
      (∫ _ : ℝ, E.source.noReportPayoff publicBase ∂skillLaw) ≤
        ∫ latentSkill, preScoreOutput latentSkill ∂skillLaw :=
    integral_mono_ae (integrable_const _) hpreScoreIntegrable hle
  have hmeanNe :
      (∫ _ : ℝ, E.source.noReportPayoff publicBase ∂skillLaw) ≠
        ∫ latentSkill, preScoreOutput latentSkill ∂skillLaw := by
    intro heq
    have hae : (fun _ : ℝ => E.source.noReportPayoff publicBase) =ᵐ[skillLaw]
        preScoreOutput :=
      (integral_eq_iff_of_ae_le (integrable_const _) hpreScoreIntegrable hle).1 heq
    have hzero : skillLaw
        {latentSkill | E.source.noReportPayoff publicBase ≠
          preScoreOutput latentSkill} = 0 :=
      ae_iff.mp hae
    apply hstrictPre
    apply measure_mono_null
      (t := {latentSkill | E.source.noReportPayoff publicBase ≠
        preScoreOutput latentSkill})
    · intro latentSkill hstrictGain
      exact ne_of_lt hstrictGain
    · exact hzero
  have hpreMean : E.source.noReportPayoff publicBase <
      ∫ latentSkill, preScoreOutput latentSkill ∂skillLaw := by
    have hmean : (∫ _ : ℝ, E.source.noReportPayoff publicBase ∂skillLaw) <
        ∫ latentSkill, preScoreOutput latentSkill ∂skillLaw :=
      lt_of_le_of_ne hmeanLe hmeanNe
    simpa using hmean
  have htower :=
    (lg21HiddenAccessReportRequired_observableOutput_preScoreMean_tower
      E publicBase baseMean hbaseMean baseVariance hintegrable).2
  simpa [preScoreOutput, skillLaw] using hpreMean.trans_eq htower.symm

/-- A strict actual-output mean on a fixed observable base fibre gives a
literal inequality of the corresponding forced-report output law and the
no-report point mass. -/
theorem lg21HiddenAccessReportRequired_observableOutputLaw_ne_of_localFacts
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hintegrable : Integrable (fun scoreSkill : ℝ × ℝ =>
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1)
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase))
    (hbest : NoProfitableBinaryChoiceDeviationAE
      (gaussianReal (baseMean publicBase) baseVariance.toNNReal)
      (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
      (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase)
      (fun _ => E.source.noReportPayoff publicBase))
    (hstrict : StrictMono (fun latentSkill =>
      ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase))
    (hchosen : 0 < gaussianReal (baseMean publicBase) baseVariance.toNNReal
      {latentSkill | E.source.takeDecision latentSkill publicBase = true}) :
    lg21HiddenAccessReportRequiredObservableAccessOutputLaw E publicBase
      baseMean hbaseMean baseVariance ≠
        lg21HiddenAccessReportRequiredNoAccessOutputLaw E publicBase := by
  let jointLaw := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ) publicBase
  letI : IsMarkovKernel (gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)) :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure jointLaw :=
    IsMarkovKernel.isProbabilityMeasure publicBase
  apply lg21_outputLaw_ne_dirac_of_integral_ne jointLaw
    (fun scoreSkill =>
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1)
  · exact lg21HiddenAccessReportRequiredObservableAccessOutput_measurable E publicBase
  · exact hintegrable
  · exact ne_of_gt
      (lg21HiddenAccessReportRequired_observableOutput_integral_gt_noReport_of_localFacts
        E publicBase baseMean hbaseMean baseVariance hbaseVariance hintegrable
        hbest hstrict hchosen)

end

end LG21TestOptionalPolicies

import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralSourceEquilibrium
import LG21TestOptionalPolicies.HiddenAccessTheorem31ComponentConditionalBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31OptionalThresholdClassification
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate
import LG21TestOptionalPolicies.StrategicDominanceContinuous

/-!
# Literal output-law bridge for LG21 Theorem 3.1

The fairness clauses in Definitions 2--4 compare laws of the *actual school
output*, not a strategy label, an expected payoff, or a posterior chosen on an
unreached information set.  This module fixes that comparison object for the
hidden-access source model.

The access-side output is evaluated after the literal pre-score taking action,
the literal post-score reporting action, and the actual public payoff.  The
no-access side is the literal `X = 0` public payoff.  The witness lemmas below
only turn an explicit positive strict-gain branch into an unequal law; they do
not infer first-order stochastic dominance.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Literal output functions -/

/-- The output produced for an access student with a fixed latent skill,
non-test profile, and realized test score. -/
def lg21HiddenAccessOptionalSourceOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (score : ℝ) : ℝ :=
  if E.takeDecision skill publicBase = true then
    if E.reportDecision publicBase score = true then
      E.reportedPayoff publicBase score
    else E.noReportPayoff publicBase
  else E.noReportPayoff publicBase

/-- The same actual output, evaluated on the literal primitive source
student.  This is the access-side demographic comparison object. -/
def lg21HiddenAccessOptionalPrimitiveAccessOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (primitive : ℝ × (Feature → ℝ)) : ℝ :=
  lg21HiddenAccessOptionalSourceOutput E primitive.1
    (lg21HiddenAccessStudentBase testFeature primitive)
    (lg21HiddenAccessStudentScore testFeature primitive)

/-- A no-access student cannot generate a reported-score record, so their
actual public output is the no-report value at the literal non-test profile. -/
def lg21HiddenAccessOptionalPrimitiveNoAccessOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (primitive : ℝ × (Feature → ℝ)) : ℝ :=
  E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive)

/-- The literal school output after the post-score decision has been reached.
This is kept separate from `lg21HiddenAccessOptionalSourceOutput`: the latter
also contains the pre-score taking branch, while this one is a function only
of the public `(base, score)` record. -/
def lg21HiddenAccessOptionalBaseScoreOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (profile : (LG21NonTestFeature Feature testFeature → ℝ) × ℝ) : ℝ :=
  if E.reportDecision profile.1 profile.2 = true then
    E.reportedPayoff profile.1 profile.2
  else E.noReportPayoff profile.1

/-- The literal primitive source observation in the order used by the Gaussian
source factorization: public base, then realized score and latent skill. -/
def lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (primitive : ℝ × (Feature → ℝ)) :
    (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) :=
  (lg21HiddenAccessStudentBase testFeature primitive,
    (lg21HiddenAccessStudentScore testFeature primitive, primitive.1))

/-- The source-record event on which an access student's actual output is
strictly above the no-access public output at the same non-test base. -/
def lg21HiddenAccessOptionalStrictSourceOutputEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Set ((LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ)) :=
  {record | E.noReportPayoff record.1 <
    lg21HiddenAccessOptionalSourceOutput E record.2.2 record.1 record.2.1}

/-- Fixed-(skill, base) output law for an access student.  This is the law
which belongs in a latent-skill fairness witness. -/
def lg21HiddenAccessOptionalLatentAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    Measure ℝ :=
  (E.testLaw skill publicBase).map
    (lg21HiddenAccessOptionalSourceOutput E skill publicBase)

/-- At a fixed non-test profile, the no-access output law is the literal
no-report point mass. -/
def lg21HiddenAccessOptionalNoAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ) : Measure ℝ :=
  Measure.dirac (E.noReportPayoff publicBase)

/-- Fixed-base output law after mixing the literal `(skill, score)` source
law.  A later source-factorization theorem must identify its argument with the
actual conditional access population; this definition itself performs no
such identification. -/
def lg21HiddenAccessOptionalObservableAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (skillScoreLaw : Measure (ℝ × ℝ)) : Measure ℝ :=
  skillScoreLaw.map (fun profile =>
    lg21HiddenAccessOptionalSourceOutput E profile.1 publicBase profile.2)

/-- Demographic access output law, defined on the literal source primitive
population.  Product-law transport below connects it to the actual
access-conditioned public population. -/
def lg21HiddenAccessOptionalDemographicAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Measure ℝ :=
  (lg21ContinuousGaussianStudentPrimitiveLaw M).map
    (lg21HiddenAccessOptionalPrimitiveAccessOutput E)

/-- Demographic no-access output law on the same literal primitive source
population. -/
def lg21HiddenAccessOptionalDemographicNoAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Measure ℝ :=
  (lg21ContinuousGaussianStudentPrimitiveLaw M).map
    (lg21HiddenAccessOptionalPrimitiveNoAccessOutput E)

/-- The demographic access output law directly on the actual population
conditional on access.  The following transport theorem shows that it is the
primitive-law object above, so no group-law equality is assumed. -/
def lg21HiddenAccessOptionalActualDemographicAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Measure ℝ :=
  (lg21ContinuousGaussianAccessPopulationLaw M).map
    (lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision E.reportDecision
      E.reportedPayoff E.noReportPayoff)

/-- The demographic no-access output law directly on the actual population
conditional on no access. -/
def lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Measure ℝ :=
  (lg21HiddenAccessNoAccessLaw M).map
    (lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision E.reportDecision
      E.reportedPayoff E.noReportPayoff)

/-! ## Measurability -/

theorem lg21HiddenAccessOptionalSourceOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    Measurable (lg21HiddenAccessOptionalSourceOutput E skill publicBase) := by
  unfold lg21HiddenAccessOptionalSourceOutput
  apply Measurable.ite
    ((measurableSet_singleton true).preimage
      (E.takeDecision_measurable.comp (measurable_const.prodMk measurable_const)))
  · apply Measurable.ite
      ((measurableSet_singleton true).preimage
        (E.reportDecision_measurable.comp (measurable_const.prodMk measurable_id)))
    · exact E.reportedPayoff_measurable.comp (measurable_const.prodMk measurable_id)
    · exact measurable_const
  · exact measurable_const

theorem lg21HiddenAccessOptionalPrimitiveAccessOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Measurable (lg21HiddenAccessOptionalPrimitiveAccessOutput E) := by
  unfold lg21HiddenAccessOptionalPrimitiveAccessOutput
  unfold lg21HiddenAccessOptionalSourceOutput
  have hbase : Measurable (lg21HiddenAccessStudentBase (Feature := Feature) testFeature) :=
    lg21HiddenAccessStudentBase_measurable testFeature
  have hscore : Measurable (lg21HiddenAccessStudentScore (Feature := Feature) testFeature) :=
    lg21HiddenAccessStudentScore_measurable testFeature
  apply Measurable.ite
    ((measurableSet_singleton true).preimage
      (E.takeDecision_measurable.comp (measurable_fst.prodMk hbase)))
  · apply Measurable.ite
      ((measurableSet_singleton true).preimage
        (E.reportDecision_measurable.comp (hbase.prodMk hscore)))
    · exact E.reportedPayoff_measurable.comp (hbase.prodMk hscore)
    · exact E.noReportPayoff_measurable.comp hbase
  · exact E.noReportPayoff_measurable.comp hbase

theorem lg21HiddenAccessOptionalPrimitiveNoAccessOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Measurable (lg21HiddenAccessOptionalPrimitiveNoAccessOutput E) := by
  unfold lg21HiddenAccessOptionalPrimitiveNoAccessOutput
  exact E.noReportPayoff_measurable.comp
    (lg21HiddenAccessStudentBase_measurable testFeature)

theorem lg21HiddenAccessOptionalBaseScoreOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Measurable (lg21HiddenAccessOptionalBaseScoreOutput E) := by
  unfold lg21HiddenAccessOptionalBaseScoreOutput
  apply Measurable.ite
    ((measurableSet_singleton true).preimage E.reportDecision_measurable)
  · exact E.reportedPayoff_measurable
  · exact E.noReportPayoff_measurable.comp measurable_fst

theorem lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation
      (Feature := Feature) testFeature) := by
  exact (lg21HiddenAccessStudentBase_measurable testFeature).prodMk
    ((lg21HiddenAccessStudentScore_measurable testFeature).prodMk measurable_fst)

/-- Measurability of actual optional output on the literal source record. -/
theorem lg21HiddenAccessOptionalSourceOutput_joint_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Measurable (fun record :
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) =>
      lg21HiddenAccessOptionalSourceOutput E record.2.2 record.1 record.2.1) := by
  unfold lg21HiddenAccessOptionalSourceOutput
  have htake : Measurable (fun record :
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) =>
      E.takeDecision record.2.2 record.1) :=
    E.takeDecision_measurable.comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  have hreport : Measurable (fun record :
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) =>
      E.reportDecision record.1 record.2.1) :=
    E.reportDecision_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hreported : Measurable (fun record :
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) =>
      E.reportedPayoff record.1 record.2.1) :=
    E.reportedPayoff_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hnoReport : Measurable (fun record :
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) =>
      E.noReportPayoff record.1) :=
    E.noReportPayoff_measurable.comp measurable_fst
  apply Measurable.ite ((measurableSet_singleton true).preimage htake)
  · apply Measurable.ite ((measurableSet_singleton true).preimage hreport)
    · exact hreported
    · exact hnoReport
  · exact hnoReport

theorem lg21HiddenAccessOptionalStrictSourceOutputEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    MeasurableSet (lg21HiddenAccessOptionalStrictSourceOutputEvent E) := by
  exact measurableSet_lt (E.noReportPayoff_measurable.comp measurable_fst)
    (lg21HiddenAccessOptionalSourceOutput_joint_measurable E)

/-- Once the pre-score action is take, the literal source output is exactly
the post-score public-output function. -/
theorem lg21HiddenAccessOptionalSourceOutput_eq_baseScoreOutput_of_take
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (score : ℝ)
    (htake : E.takeDecision skill publicBase = true) :
    lg21HiddenAccessOptionalSourceOutput E skill publicBase score =
      lg21HiddenAccessOptionalBaseScoreOutput E (publicBase, score) := by
  simp [lg21HiddenAccessOptionalSourceOutput,
    lg21HiddenAccessOptionalBaseScoreOutput, htake]

/-! ## Literal action/PBO transport -/

/-- The full source factorization may be read under the positive-access
population because access is an independent source draw. -/
theorem lg21HiddenAccessOptional_accessBaseScoreSkill_factorization_of_sourceFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
      baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        (lg21ContinuousGaussianPopulationLaw M).map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
          simpa [lg21HiddenAccessBaseScoreSkillObservation] using
            (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
              M haccess testFeature).symm
    _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) :=
      hsourceFactor

/-- The same Gaussian source factorization, read directly on the primitive
student population.  This is the transport used for fairness witnesses; no
condition is selected by a strategy name. -/
theorem lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map
      (lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature) =
      baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let primitiveObservation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  let accessObservation : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) :=
    fun student =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        (lg21HiddenAccessStudentScore testFeature student.2,
          lg21ContinuousPopulationSkill student))
  have hprimitiveObservation : Measurable primitiveObservation := by
    simpa [primitiveObservation] using
      lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation_measurable
        (Feature := Feature) testFeature
  have haccessObservation : Measurable accessObservation := by
    exact ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd).prodMk
      (((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd).prodMk
        (measurable_fst.comp measurable_snd))
  calc
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map primitiveObservation =
        (accessLaw.map Prod.snd).map primitiveObservation := by
          rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    _ = accessLaw.map accessObservation := by
          rw [Measure.map_map hprimitiveObservation measurable_snd]
          rfl
    _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
          simpa [accessLaw, accessObservation] using
            (lg21HiddenAccessOptional_accessBaseScoreSkill_factorization_of_sourceFactor
              M haccess testFeature baseLaw baseMean hbaseMean baseVariance hsourceFactor)

/-- Literal stability supplies a positive on-path reported-score population.
The local-entry premise is rebuilt from the source candidate construction;
this theorem does not posit a reporter mass as an equilibrium field. -/
theorem lg21HiddenAccessOptional_actualReportEvent_positive_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  have hentry : ∀ region : Set (LG21NonTestFeature Feature testFeature → ℝ),
      ∀ hregion : MeasurableSet region,
      ∀ hpositive : 0 < rawLaw
        (lg21HiddenAccessBaseRegionEvent testFeature region),
      ∀ hzero : rawLaw (lg21HiddenAccessBaseRegionEvent testFeature region ∩
          lg21HiddenAccessActualReportEvent E) = 0,
      LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess := by
    intro region hregion hpositive hzero
    exact lg21HiddenAccess_sourceLocalCandidateEntry_of_zeroReporterBaseRegion
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E region hregion (by simpa [rawLaw] using hpositive)
      (by simpa [rawLaw] using hzero)
  simpa [lg21HiddenAccessActualReportEvent] using
    (E.actualReportEvent_positive_of_stable hnoAccess hstable hentry)

/-- The a.e. literal reporter PBO transports all the way to the primitive
source population.  It is still guarded by the actual two-stage action, so
this gives no value to an unreached score-report history. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.primitive_reportedPayoff_eq_rawGaussianPosterior_ae_on_take_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ primitive ∂lg21ContinuousGaussianStudentPrimitiveLaw M,
      E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive) = true →
        E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = true →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  let accessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | student.1 = true}
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have haccessFactor :
      accessLaw.map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
    simpa [accessLaw, rawLaw] using
      lg21HiddenAccessOptional_accessBaseScoreSkill_factorization_of_sourceFactor
        M E.access_positive testFeature baseLaw baseMean hbaseMean baseVariance
        (by simpa [rawLaw] using hsourceFactor)
  have hreportValueRestricted :=
    E.reportedPayoff_eq_rawGaussianPosterior_ae_on_actualReport
      hactiveNoTakeZero hreporterPositive baseLaw baseMean hbaseMean
      baseVariance hbaseVariance hnoiseVariance haccessFactor
  have hreportEventMeasurable : MeasurableSet reportEvent := by
    simpa [reportEvent] using
      (lg21HiddenAccessOptionalReportEvent_measurable testFeature
        E.takeDecision E.reportDecision E.takeDecision_measurable
        E.reportDecision_measurable)
  rw [ae_restrict_iff' hreportEventMeasurable] at hreportValueRestricted
  have hreportValueRaw : ∀ᵐ student ∂rawLaw,
      student ∈ reportEvent →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
        scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
    simpa [rawLaw, reportEvent, scoreValue] using hreportValueRestricted
  have haccessAC : accessLaw ≪ rawLaw := by
    change (rawLaw accessEvent)⁻¹ • rawLaw.restrict accessEvent ≪ rawLaw
    exact Measure.smul_absolutelyContinuous.trans
      Measure.absolutelyContinuous_restrict
  have hreportValueAccess := haccessAC.ae_le hreportValueRaw
  have haccessTrue : ∀ᵐ student ∂accessLaw, student.1 = true := by
    change ∀ᵐ student ∂lg21NormalizedRestriction rawLaw accessEvent,
      student.1 = true
    apply lg21NormalizedRestriction_ae_mem rawLaw accessEvent
    · change MeasurableSet {student : Bool × (ℝ × (Feature → ℝ)) |
        student.1 = true}
      exact (measurableSet_singleton true).preimage measurable_fst
    · exact measure_ne_top _ _
  let primitiveValue : ℝ × (Feature → ℝ) → Prop := fun primitive =>
    E.takeDecision primitive.1
        (lg21HiddenAccessStudentBase testFeature primitive) = true →
      E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive) = true →
      E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive) =
        scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)
  have hprimitiveValueMeasurable : MeasurableSet {primitive | primitiveValue primitive} := by
    have hbase : Measurable (lg21HiddenAccessStudentBase
        (Feature := Feature) testFeature) :=
      lg21HiddenAccessStudentBase_measurable testFeature
    have hscore : Measurable (lg21HiddenAccessStudentScore
        (Feature := Feature) testFeature) :=
      lg21HiddenAccessStudentScore_measurable testFeature
    have htake : Measurable (fun primitive : ℝ × (Feature → ℝ) =>
        E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive)) :=
      E.takeDecision_measurable.comp (measurable_fst.prodMk hbase)
    have hreport : Measurable (fun primitive : ℝ × (Feature → ℝ) =>
        E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)) :=
      E.reportDecision_measurable.comp (hbase.prodMk hscore)
    have hreported : Measurable (fun primitive : ℝ × (Feature → ℝ) =>
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)) :=
      E.reportedPayoff_measurable.comp (hbase.prodMk hscore)
    have hscoreValue : Measurable (fun primitive : ℝ × (Feature → ℝ) =>
        scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)) := by
      rw [show (fun primitive : ℝ × (Feature → ℝ) =>
          scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive)) =
          (fun primitive =>
            gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) *
                lg21HiddenAccessStudentScore testFeature primitive +
              gaussianSignalPriorWeight baseVariance
                (M.noiseVariance testFeature : ℝ) *
                  baseMean (lg21HiddenAccessStudentBase testFeature primitive)) by
          funext primitive
          exact lg21_optional_rawGaussianPosteriorMean_eq_affine
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive)]
      fun_prop
    let takeSet : Set (ℝ × (Feature → ℝ)) := {primitive |
        E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive) = true}
    let reportSet : Set (ℝ × (Feature → ℝ)) := {primitive |
        E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = true}
    let eqSet : Set (ℝ × (Feature → ℝ)) := {primitive |
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
          scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive)}
    have htakeSet : MeasurableSet takeSet := by
      change MeasurableSet ((fun primitive : ℝ × (Feature → ℝ) =>
        E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive)) ⁻¹'
        ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage htake
    have hreportSet : MeasurableSet reportSet := by
      change MeasurableSet ((fun primitive : ℝ × (Feature → ℝ) =>
        E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)) ⁻¹'
        ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage hreport
    have heqSet : MeasurableSet eqSet := by
      simpa [eqSet] using
      measurableSet_eq_fun hreported hscoreValue
    have hset : {primitive : ℝ × (Feature → ℝ) | primitiveValue primitive} =
        takeSetᶜ ∪ (reportSetᶜ ∪ eqSet) := by
      ext primitive
      change
        (E.takeDecision primitive.1
            (lg21HiddenAccessStudentBase testFeature primitive) = true →
          E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true →
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) =
            scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive)) ↔
          (¬ E.takeDecision primitive.1
              (lg21HiddenAccessStudentBase testFeature primitive) = true ∨
            (¬ E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive) = true ∨
              E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive) =
                scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
                  (lg21HiddenAccessStudentScore testFeature primitive)))
      constructor
      · intro hvalue
        by_cases htake : E.takeDecision primitive.1
            (lg21HiddenAccessStudentBase testFeature primitive) = true
        · by_cases hreport : E.reportDecision
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive) = true
          · exact Or.inr (Or.inr (hvalue htake hreport))
          · exact Or.inr (Or.inl hreport)
        · exact Or.inl htake
      · intro hcases htakeTrue hreportTrue
        rcases hcases with hnotTake | hrest
        · exact (hnotTake htakeTrue).elim
        rcases hrest with hnotReport | heq
        · exact (hnotReport hreportTrue).elim
        · exact heq
    rw [hset]
    exact htakeSet.compl.union (hreportSet.compl.union heqSet)
  have hvalueAccess : ∀ᵐ student ∂accessLaw, primitiveValue student.2 := by
    filter_upwards [hreportValueAccess, haccessTrue] with student hvalue haccessTrue
      htake hreport
    apply hvalue
    rcases student with ⟨access, primitive⟩
    cases access <;>
      simp_all [reportEvent, lg21HiddenAccessOptionalReportEvent,
        lg21HiddenAccessOptionalObservedAction, lg21HiddenAccessStudentTake,
        lg21HiddenAccessStudentReport, lg21ContinuousPopulationSkill]
  have hvaluePrimitive : ∀ᵐ primitive ∂accessLaw.map Prod.snd,
      primitiveValue primitive :=
    (MeasureTheory.ae_map_iff measurable_snd.aemeasurable
      hprimitiveValueMeasurable).2 hvalueAccess
  rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M E.access_positive]
    at hvaluePrimitive
  simpa [primitiveValue, scoreValue] using hvaluePrimitive

/-- The source-derived cutoff classification can be read directly on literal
primitive students, where the output functions are evaluated. -/
theorem lg21HiddenAccessOptional_reportDecision_eq_rawPosteriorCutoff_ae_on_primitive_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    ∀ᵐ primitive ∂lg21ContinuousGaussianStudentPrimitiveLaw M,
      E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
        decide (affineCutoff
          (gaussianSignalPriorWeight baseVariance
            (M.noiseVariance testFeature : ℝ) *
              baseMean (lg21HiddenAccessStudentBase testFeature primitive))
          (gaussianSignalWeight baseVariance
            (M.noiseVariance testFeature : ℝ))
          (E.noReportPayoff
            (lg21HiddenAccessStudentBase testFeature primitive)) ≤
          lg21HiddenAccessStudentScore testFeature primitive) := by
  have hcutoff :=
    lg21HiddenAccess_optional_reportDecision_eq_rawPosteriorCutoff_ae_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable
  rw [lg21HiddenAccessAccessBaseScoreLaw_eq_primitiveBaseScoreLaw
    M haccess testFeature] at hcutoff
  simpa [lg21HiddenAccessPrimitiveBaseScoreObservation] using
    (ae_of_ae_map
      (lg21HiddenAccessPrimitiveBaseScoreObservation_measurable testFeature).aemeasurable
      hcutoff)

/-- The raw posterior can tie the literal no-report payoff only on a null
score graph under the source Gaussian factorization.  This is a fact about the
actual primitive population, not a choice of an off-path PBO version. -/
theorem lg21HiddenAccessOptional_rawPosteriorTie_null_on_primitive_of_sourceFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
          E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive)} = 0 := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  let baseScoreSkill := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let dropSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun profile => (profile.1, profile.2.1)
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ))
  have hbaseScoreSkill : Measurable baseScoreSkill := by
    simpa [baseScoreSkill] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hdropSkill : Measurable dropSkill := by
    exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hscoreValue : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      scoreValue profile.1 profile.2) := by
    rw [show (fun profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        scoreValue profile.1 profile.2) =
        (fun profile =>
          gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) *
              profile.2 +
            gaussianSignalPriorWeight baseVariance
              (M.noiseVariance testFeature : ℝ) * baseMean profile.1) by
        funext profile
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          profile.1 profile.2]
    fun_prop
  have hscoreMarginal : joint.map Prod.fst = scoreKernel := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_fst,
      gaussianSignalJointKernel_apply,
      Measure.map_map measurable_fst (by fun_prop)]
    rw [show Prod.fst ∘ (fun pair : ℝ × ℝ =>
        (pair.1 + pair.2, pair.1)) = gaussianSignalScore by rfl]
    rw [show scoreKernel publicBase = gaussianReal (baseMean publicBase)
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal by
      exact gaussianLocationKernel_apply baseMean hbaseMean
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal publicBase]
    rw [gaussianSignalPair_score_marginal (baseMean publicBase) baseVariance
      (M.noiseVariance testFeature : ℝ) hbaseVariance hnoiseVariance]
  have haccessBaseScoreFactor :
      lg21HiddenAccessAccessBaseScoreLaw M testFeature = baseLaw ⊗ₘ scoreKernel := by
    calc
      lg21HiddenAccessAccessBaseScoreLaw M testFeature =
          (accessLaw.map baseScoreSkill).map dropSkill := by
            rw [Measure.map_map hdropSkill hbaseScoreSkill]
            rfl
      _ = (rawLaw.map baseScoreSkill).map dropSkill := by
            rw [lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
              M haccess testFeature]
      _ = (baseLaw ⊗ₘ joint).map dropSkill := by
            rw [show rawLaw.map baseScoreSkill = baseLaw ⊗ₘ joint by
              simpa [rawLaw, baseScoreSkill, joint] using hsourceFactor]
      _ = baseLaw ⊗ₘ joint.map Prod.fst := by
            change (baseLaw ⊗ₘ joint).map (Prod.map id Prod.fst) = _
            rw [← Measure.compProd_map measurable_fst]
      _ = baseLaw ⊗ₘ scoreKernel := by rw [hscoreMarginal]
  have hscoreVariance : 0 < baseVariance + (M.noiseVariance testFeature : ℝ) := by
    linarith
  have hscoreVarianceNN :
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hscoreVariance)
  have htieAccess : lg21HiddenAccessAccessBaseScoreLaw M testFeature
      {publicScore |
        scoreValue publicScore.1 publicScore.2 = E.noReportPayoff publicScore.1} = 0 := by
    rw [haccessBaseScoreFactor]
    exact lg21_fibrewise_strictMono_graph_null baseLaw scoreKernel
      (fun publicScore => scoreValue publicScore.1 publicScore.2)
      E.noReportPayoff hscoreValue E.noReportPayoff_measurable
      (fun publicBase =>
        lg21_optional_rawGaussianPosteriorMean_strictMono
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          hbaseVariance hnoiseVariance publicBase)
      (fun publicBase score => by
        rw [show scoreKernel publicBase =
          gaussianReal (baseMean publicBase)
            (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal by
          exact gaussianLocationKernel_apply baseMean hbaseMean
            (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal publicBase]
        exact gaussianReal_singleton_eq_zero (baseMean publicBase)
          hscoreVarianceNN score)
  rw [lg21HiddenAccessAccessBaseScoreLaw_eq_primitiveBaseScoreLaw
    M haccess testFeature] at htieAccess
  have htieSet : MeasurableSet {publicScore :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
      scoreValue publicScore.1 publicScore.2 = E.noReportPayoff publicScore.1} := by
    simpa only [Function.comp_apply] using
      (measurableSet_eq_fun hscoreValue
        (E.noReportPayoff_measurable.comp measurable_fst))
  rw [Measure.map_apply
    (lg21HiddenAccessPrimitiveBaseScoreObservation_measurable testFeature)
    htieSet] at htieAccess
  simpa [scoreValue, lg21HiddenAccessPrimitiveBaseScoreObservation] using htieAccess

/-- Positive literal reporter mass transports to the semantic primitive event
on which an access student both takes and reports. -/
theorem lg21HiddenAccessOptional_primitiveActualReportEvent_positive_of_raw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    0 < lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        E.takeDecision primitive.1
            (lg21HiddenAccessStudentBase testFeature primitive) = true ∧
          E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true} := by
  let primitiveReportEvent : Set (ℝ × (Feature → ℝ)) := {primitive |
    E.takeDecision primitive.1
        (lg21HiddenAccessStudentBase testFeature primitive) = true ∧
      E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive) = true}
  have hreportEvent :
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision =
        ({true} : Set Bool) ×ˢ primitiveReportEvent := by
    ext student
    rcases student with ⟨access, primitive⟩
    cases access <;>
      simp [primitiveReportEvent, lg21HiddenAccessOptionalReportEvent,
        lg21HiddenAccessOptionalObservedAction, lg21HiddenAccessStudentTake,
        lg21HiddenAccessStudentReport]
  rw [hreportEvent, lg21ContinuousGaussianPopulation_access_student_factorization]
    at hreporterPositive
  exact (ENNReal.mul_pos_iff.mp hreporterPositive).2

/-- A semantic action/PBO bridge for the optional regime.  The hypotheses
refer to literal student actions, the actual report branch, and the raw
posterior comparison.  They imply weak actual-output benefit everywhere up to
the source null set and a non-null strict benefit; no stochastic-order
conclusion is used. -/
theorem lg21HiddenAccessOptional_primitiveOutput_benefit_of_rawPosteriorActionFacts
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hcutoff : ∀ᵐ primitive ∂lg21ContinuousGaussianStudentPrimitiveLaw M,
      E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
        decide (affineCutoff
          (gaussianSignalPriorWeight baseVariance
            (M.noiseVariance testFeature : ℝ) *
              baseMean (lg21HiddenAccessStudentBase testFeature primitive))
          (gaussianSignalWeight baseVariance
            (M.noiseVariance testFeature : ℝ))
          (E.noReportPayoff
            (lg21HiddenAccessStudentBase testFeature primitive)) ≤
          lg21HiddenAccessStudentScore testFeature primitive))
    (hreported : ∀ᵐ primitive ∂lg21ContinuousGaussianStudentPrimitiveLaw M,
      E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive) = true →
        E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = true →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive))
    (hactualReportPositive : 0 < lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        E.takeDecision primitive.1
            (lg21HiddenAccessStudentBase testFeature primitive) = true ∧
          E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true})
    (htie : lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) =
          E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive)} = 0) :
    lg21HiddenAccessOptionalPrimitiveNoAccessOutput E ≤ᵐ[
      lg21ContinuousGaussianStudentPrimitiveLaw M]
        lg21HiddenAccessOptionalPrimitiveAccessOutput E ∧
      lg21ContinuousGaussianStudentPrimitiveLaw M
        {primitive |
          lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
            lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive} ≠ 0 := by
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  let cutoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ :=
    fun publicBase => affineCutoff
      (gaussianSignalPriorWeight baseVariance
        (M.noiseVariance testFeature : ℝ) * baseMean publicBase)
      (gaussianSignalWeight baseVariance
        (M.noiseVariance testFeature : ℝ))
      (E.noReportPayoff publicBase)
  have hweight : 0 < gaussianSignalWeight baseVariance
      (M.noiseVariance testFeature : ℝ) :=
    gaussianSignalWeight_pos hbaseVariance hnoiseVariance
  have hreportedGain : ∀ᵐ primitive ∂lg21ContinuousGaussianStudentPrimitiveLaw M,
      E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive) = true →
        E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = true →
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive) ≤
          scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) := by
    filter_upwards [hcutoff] with primitive hcut htake hreport
    have hcutoffLe : cutoff
        (lg21HiddenAccessStudentBase testFeature primitive) ≤
        lg21HiddenAccessStudentScore testFeature primitive := by
      simpa [cutoff, hreport] using hcut.symm
    rw [show scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive) =
        gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) *
            lg21HiddenAccessStudentScore testFeature primitive +
          gaussianSignalPriorWeight baseVariance
            (M.noiseVariance testFeature : ℝ) *
              baseMean (lg21HiddenAccessStudentBase testFeature primitive) by
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)]
    simpa [cutoff, add_comm] using
      (threshold_le_affine_iff_cutoff_le
        (intercept := gaussianSignalPriorWeight baseVariance
          (M.noiseVariance testFeature : ℝ) *
            baseMean (lg21HiddenAccessStudentBase testFeature primitive))
        (slope := gaussianSignalWeight baseVariance
          (M.noiseVariance testFeature : ℝ))
        (threshold := E.noReportPayoff
          (lg21HiddenAccessStudentBase testFeature primitive))
        (x := lg21HiddenAccessStudentScore testFeature primitive) hweight).2
        hcutoffLe
  have hweak : lg21HiddenAccessOptionalPrimitiveNoAccessOutput E ≤ᵐ[
      lg21ContinuousGaussianStudentPrimitiveLaw M]
        lg21HiddenAccessOptionalPrimitiveAccessOutput E := by
    filter_upwards [hreportedGain, hreported] with primitive hgain hvalue
    by_cases htake : E.takeDecision primitive.1
        (lg21HiddenAccessStudentBase testFeature primitive) = true
    · by_cases hreport : E.reportDecision
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = true
      · have hvalueAt := hvalue htake hreport
        have hgainAt := hgain htake hreport
        change E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive) ≤
          lg21HiddenAccessOptionalSourceOutput E primitive.1
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive)
        rw [lg21HiddenAccessOptionalSourceOutput_eq_baseScoreOutput_of_take
          E primitive.1 (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) htake]
        simp [lg21HiddenAccessOptionalBaseScoreOutput, hreport, hvalueAt]
        exact hgainAt
      · simp [lg21HiddenAccessOptionalPrimitiveNoAccessOutput,
          lg21HiddenAccessOptionalPrimitiveAccessOutput,
          lg21HiddenAccessOptionalSourceOutput, htake, hreport]
    · simp [lg21HiddenAccessOptionalPrimitiveNoAccessOutput,
        lg21HiddenAccessOptionalPrimitiveAccessOutput,
        lg21HiddenAccessOptionalSourceOutput, htake]
  refine ⟨hweak, ?_⟩
  let actualReport : Set (ℝ × (Feature → ℝ)) := {primitive |
    E.takeDecision primitive.1
        (lg21HiddenAccessStudentBase testFeature primitive) = true ∧
      E.reportDecision (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive) = true}
  let strictGain : Set (ℝ × (Feature → ℝ)) := {primitive |
    lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
      lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive}
  let tie : Set (ℝ × (Feature → ℝ)) := {primitive |
    scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
      (lg21HiddenAccessStudentScore testFeature primitive) =
      E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive)}
  have hsplit : ∀ᵐ primitive ∂lg21ContinuousGaussianStudentPrimitiveLaw M,
      primitive ∈ actualReport → primitive ∈ strictGain ∪ tie := by
    filter_upwards [hreportedGain, hreported] with primitive hgain hvalue hactual
    rcases hactual with ⟨htake, hreport⟩
    have hgainAt := hgain htake hreport
    rcases hgainAt.lt_or_eq with hstrict | heq
    · left
      have hvalueAt := hvalue htake hreport
      change lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
        lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive
      change E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive) <
        lg21HiddenAccessOptionalSourceOutput E primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive)
      rw [lg21HiddenAccessOptionalSourceOutput_eq_baseScoreOutput_of_take
        E primitive.1 (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive) htake]
      simp [lg21HiddenAccessOptionalBaseScoreOutput, hreport, hvalueAt]
      exact hstrict
    · right
      exact heq.symm
  have htiezero : lg21ContinuousGaussianStudentPrimitiveLaw M tie = 0 := by
    simpa [tie, scoreValue] using htie
  intro hstrictZero
  have hstrictGainZero : lg21ContinuousGaussianStudentPrimitiveLaw M strictGain = 0 := by
    simpa [strictGain] using hstrictZero
  have hbadZero : lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive | ¬ (primitive ∈ actualReport → primitive ∈ strictGain ∪ tie)} = 0 := by
    simpa only [ae_iff] using hsplit
  have hactualZero : lg21ContinuousGaussianStudentPrimitiveLaw M actualReport = 0 := by
    apply measure_mono_null
      (t := (strictGain ∪ tie) ∪
        {primitive | ¬ (primitive ∈ actualReport → primitive ∈ strictGain ∪ tie)})
    · intro primitive hactual
      by_cases hgood : primitive ∈ strictGain ∪ tie
      · exact Or.inl hgood
      · exact Or.inr (by
          intro himp
          exact hgood (himp hactual))
    · exact measure_union_null
        (measure_union_null hstrictGainZero htiezero) hbadZero
  exact (ne_of_gt hactualReportPositive) (by
    simpa [actualReport] using hactualZero)

/-- Literal source stability supplies every semantic premise of the
actual-output bridge.  In particular, this conclusion is about the school
output induced by the source actions, rather than a named equilibrium label or
a counterfactual payoff on an unreached history. -/
theorem lg21HiddenAccessOptional_primitiveOutput_benefit_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    lg21HiddenAccessOptionalPrimitiveNoAccessOutput E ≤ᵐ[
      lg21ContinuousGaussianStudentPrimitiveLaw M]
        lg21HiddenAccessOptionalPrimitiveAccessOutput E ∧
      lg21ContinuousGaussianStudentPrimitiveLaw M
        {primitive |
          lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
            lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive} ≠ 0 := by
  have hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0 :=
    (lg21HiddenAccess_optional_allTake_and_positiveWithholding_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hreportBest hstable).1
  have hreporterPositive :=
    lg21HiddenAccessOptional_actualReportEvent_positive_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hstable
  exact lg21HiddenAccessOptional_primitiveOutput_benefit_of_rawPosteriorActionFacts
    E baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
    (lg21HiddenAccessOptional_reportDecision_eq_rawPosteriorCutoff_ae_on_primitive_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable)
    (E.primitive_reportedPayoff_eq_rawGaussianPosterior_ae_on_take_report
      hactiveNoTakeZero hreporterPositive baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hsourceFactor)
    (lg21HiddenAccessOptional_primitiveActualReportEvent_positive_of_raw
      E hreporterPositive)
    (lg21HiddenAccessOptional_rawPosteriorTie_null_on_primitive_of_sourceFactor
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hsourceFactor E)

theorem lg21HiddenAccessOptionalObservableAccessOutput_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    Measurable (fun profile : ℝ × ℝ =>
      lg21HiddenAccessOptionalSourceOutput E profile.1 publicBase profile.2) := by
  unfold lg21HiddenAccessOptionalSourceOutput
  apply Measurable.ite
    ((measurableSet_singleton true).preimage
      (E.takeDecision_measurable.comp (measurable_fst.prodMk measurable_const)))
  · apply Measurable.ite
      ((measurableSet_singleton true).preimage
        (E.reportDecision_measurable.comp (measurable_const.prodMk measurable_snd)))
    · exact E.reportedPayoff_measurable.comp (measurable_const.prodMk measurable_snd)
    · exact measurable_const
  · exact measurable_const

/-! ## Actual-population transport -/

/-- The actual access-conditioned public output law is exactly the source
primitive output law.  This uses only the source product population and the
literal `Z = 1` support of the conditioned measure. -/
theorem lg21HiddenAccessOptional_actualDemographicAccessOutputLaw_eq_primitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E =
      lg21HiddenAccessOptionalDemographicAccessOutputLaw E := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | student.1 = true}
  let publicOutput := lg21HiddenAccessOptionalPublicPayoff testFeature
    E.takeDecision E.reportDecision E.reportedPayoff E.noReportPayoff
  let primitiveOutput := lg21HiddenAccessOptionalPrimitiveAccessOutput E
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  have haccessEvent : MeasurableSet accessEvent := by
    exact (measurableSet_singleton true).preimage measurable_fst
  have hsupported : ∀ᵐ student ∂accessLaw, student ∈ accessEvent := by
    change ∀ᵐ student ∂lg21NormalizedRestriction rawLaw accessEvent,
      student ∈ accessEvent
    exact Measure.ae_smul_measure (ae_restrict_mem haccessEvent) _
  have houtput : publicOutput =ᵐ[accessLaw]
      fun student => primitiveOutput student.2 := by
    filter_upwards [hsupported] with student hstudent
    rcases student with ⟨access, primitive⟩
    cases haccess : access
    · simp [accessEvent, haccess] at hstudent
    · by_cases htake : E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive) = true
      · by_cases hreport : E.reportDecision
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true
        · simp [publicOutput, primitiveOutput,
            lg21HiddenAccessOptionalPrimitiveAccessOutput,
            lg21HiddenAccessOptionalSourceOutput,
            lg21HiddenAccessOptionalPublicPayoff,
            lg21HiddenAccessOptionalObservedAction,
            lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
            htake, hreport]
        · simp [publicOutput, primitiveOutput,
            lg21HiddenAccessOptionalPrimitiveAccessOutput,
            lg21HiddenAccessOptionalSourceOutput,
            lg21HiddenAccessOptionalPublicPayoff,
            lg21HiddenAccessOptionalObservedAction,
            lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
            htake, hreport]
      · simp [publicOutput, primitiveOutput,
          lg21HiddenAccessOptionalPrimitiveAccessOutput,
          lg21HiddenAccessOptionalSourceOutput,
          lg21HiddenAccessOptionalPublicPayoff,
          lg21HiddenAccessOptionalObservedAction,
          lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport, htake]
  calc
    lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E =
        accessLaw.map publicOutput := by rfl
    _ = accessLaw.map (fun student => primitiveOutput student.2) :=
      Measure.map_congr houtput
    _ = (accessLaw.map Prod.snd).map primitiveOutput := by
      rw [Measure.map_map
        (lg21HiddenAccessOptionalPrimitiveAccessOutput_measurable E) measurable_snd]
      rfl
    _ = lg21HiddenAccessOptionalDemographicAccessOutputLaw E := by
      rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M E.access_positive]
      rfl

/-- The actual no-access public output law is exactly the source primitive
no-report output law. -/
theorem lg21HiddenAccessOptional_actualDemographicNoAccessOutputLaw_eq_primitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E =
      lg21HiddenAccessOptionalDemographicNoAccessOutputLaw E := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noAccessLaw := lg21HiddenAccessNoAccessLaw M
  let noAccessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let publicOutput := lg21HiddenAccessOptionalPublicPayoff testFeature
    E.takeDecision E.reportDecision E.reportedPayoff E.noReportPayoff
  let primitiveOutput := lg21HiddenAccessOptionalPrimitiveNoAccessOutput E
  have hnoAccessEvent : MeasurableSet noAccessEvent := by
    change MeasurableSet ((fun student : Bool × (ℝ × (Feature → ℝ)) => student.1) ⁻¹'
      ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage measurable_fst
  have hsupported : ∀ᵐ student ∂noAccessLaw, student ∈ noAccessEvent := by
    change ∀ᵐ student ∂lg21NormalizedRestriction rawLaw noAccessEvent,
      student ∈ noAccessEvent
    exact Measure.ae_smul_measure (ae_restrict_mem hnoAccessEvent) _
  have houtput : publicOutput =ᵐ[noAccessLaw]
      fun student => primitiveOutput student.2 := by
    filter_upwards [hsupported] with student hstudent
    rcases student with ⟨access, primitive⟩
    cases haccess : access
    · simp [publicOutput, primitiveOutput,
        lg21HiddenAccessOptionalPrimitiveNoAccessOutput,
        lg21HiddenAccessOptionalPublicPayoff,
        lg21HiddenAccessOptionalObservedAction, haccess]
    · simp [noAccessEvent, lg21HiddenAccessNoAccessEvent, haccess] at hstudent
  calc
    lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E =
        noAccessLaw.map publicOutput := by rfl
    _ = noAccessLaw.map (fun student => primitiveOutput student.2) :=
      Measure.map_congr houtput
    _ = (noAccessLaw.map Prod.snd).map primitiveOutput := by
      rw [Measure.map_map
        (lg21HiddenAccessOptionalPrimitiveNoAccessOutput_measurable E) measurable_snd]
      rfl
    _ = lg21HiddenAccessOptionalDemographicNoAccessOutputLaw E := by
      rw [lg21HiddenAccessNoAccessLaw_map_student_eq M hnoAccess]
      rfl

/-- The literal full public output is integrable without an additional
economic assumption: the source PBO identifies it almost everywhere with a
conditional expectation of integrable latent skill. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.publicOutput_integrable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Integrable
      (lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision E.reportDecision
        E.reportedPayoff E.noReportPayoff)
      (lg21ContinuousGaussianPopulationLaw M) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let publicObservation := lg21HiddenAccessOptionalPublicObservation testFeature
    E.takeDecision E.reportDecision
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hPBO : lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision
      E.reportDecision E.reportedPayoff E.noReportPayoff =ᵐ[rawLaw]
      rawLaw[lg21ContinuousPopulationSkill |
        MeasurableSpace.comap publicObservation inferInstance] := by
    simpa [rawLaw, publicObservation] using E.public_pbo
  exact MeasureTheory.integrable_condExp.congr hPBO.symm

/-- Integrability of the access-side primitive output follows from the actual
public PBO, after conditioning the source population on `Z = 1`. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.primitiveAccessOutput_integrable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Integrable (lg21HiddenAccessOptionalPrimitiveAccessOutput E)
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | student.1 = true}
  let publicOutput := lg21HiddenAccessOptionalPublicPayoff testFeature
    E.takeDecision E.reportDecision E.reportedPayoff E.noReportPayoff
  let primitiveOutput := lg21HiddenAccessOptionalPrimitiveAccessOutput E
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  have hrawIntegrable : Integrable publicOutput rawLaw := by
    simpa [rawLaw, publicOutput] using E.publicOutput_integrable
  have haccessMass : rawLaw accessEvent = M.accessLaw ({true} : Set Bool) := by
    rw [show accessEvent = ({true} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [accessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    rw [IsProbabilityMeasure.measure_univ, mul_one]
  have haccessPositive : 0 < rawLaw accessEvent := by
    rw [haccessMass]
    simpa using E.access_positive
  have haccessIntegrable : Integrable publicOutput accessLaw := by
    change Integrable publicOutput
      ((rawLaw accessEvent)⁻¹ • rawLaw.restrict accessEvent)
    exact hrawIntegrable.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt haccessPositive))
  have haccessEvent : MeasurableSet accessEvent := by
    exact (measurableSet_singleton true).preimage measurable_fst
  have hsupported : ∀ᵐ student ∂accessLaw, student ∈ accessEvent := by
    change ∀ᵐ student ∂lg21NormalizedRestriction rawLaw accessEvent,
      student ∈ accessEvent
    exact Measure.ae_smul_measure (ae_restrict_mem haccessEvent) _
  have houtput : publicOutput =ᵐ[accessLaw]
      fun student => primitiveOutput student.2 := by
    filter_upwards [hsupported] with student hstudent
    rcases student with ⟨access, primitive⟩
    cases haccess : access
    · simp [accessEvent, haccess] at hstudent
    · by_cases htake : E.takeDecision primitive.1
          (lg21HiddenAccessStudentBase testFeature primitive) = true
      · by_cases hreport : E.reportDecision
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true
        · simp [publicOutput, primitiveOutput,
            lg21HiddenAccessOptionalPrimitiveAccessOutput,
            lg21HiddenAccessOptionalSourceOutput,
            lg21HiddenAccessOptionalPublicPayoff,
            lg21HiddenAccessOptionalObservedAction,
            lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
            htake, hreport]
        · simp [publicOutput, primitiveOutput,
            lg21HiddenAccessOptionalPrimitiveAccessOutput,
            lg21HiddenAccessOptionalSourceOutput,
            lg21HiddenAccessOptionalPublicPayoff,
            lg21HiddenAccessOptionalObservedAction,
            lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
            htake, hreport]
      · simp [publicOutput, primitiveOutput,
          lg21HiddenAccessOptionalPrimitiveAccessOutput,
          lg21HiddenAccessOptionalSourceOutput,
          lg21HiddenAccessOptionalPublicPayoff,
          lg21HiddenAccessOptionalObservedAction,
          lg21HiddenAccessStudentTake, htake]
  have hcomposed : Integrable (fun student => primitiveOutput student.2) accessLaw :=
    haccessIntegrable.congr houtput
  have hmapped : Integrable primitiveOutput (accessLaw.map Prod.snd) := by
    apply (integrable_map_measure
      (lg21HiddenAccessOptionalPrimitiveAccessOutput_measurable E).aestronglyMeasurable
      measurable_snd.aemeasurable).mpr
    simpa only [Function.comp_apply] using hcomposed
  rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M E.access_positive] at hmapped
  exact hmapped

/-- Integrability of the no-access primitive output follows by the same
conditional-expectation argument on the literal `Z = 0` population. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.primitiveNoAccessOutput_integrable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    Integrable (lg21HiddenAccessOptionalPrimitiveNoAccessOutput E)
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noAccessLaw := lg21HiddenAccessNoAccessLaw M
  let noAccessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let publicOutput := lg21HiddenAccessOptionalPublicPayoff testFeature
    E.takeDecision E.reportDecision E.reportedPayoff E.noReportPayoff
  let primitiveOutput := lg21HiddenAccessOptionalPrimitiveNoAccessOutput E
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  have hrawIntegrable : Integrable publicOutput rawLaw := by
    simpa [rawLaw, publicOutput] using E.publicOutput_integrable
  have hnoAccessMass : rawLaw noAccessEvent = M.accessLaw ({false} : Set Bool) := by
    rw [show noAccessEvent = ({false} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [noAccessEvent, lg21HiddenAccessNoAccessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    rw [IsProbabilityMeasure.measure_univ, mul_one]
  have hnoAccessPositive : 0 < rawLaw noAccessEvent := by
    rw [hnoAccessMass]
    simpa using hnoAccess
  have hnoAccessIntegrable : Integrable publicOutput noAccessLaw := by
    change Integrable publicOutput
      ((rawLaw noAccessEvent)⁻¹ • rawLaw.restrict noAccessEvent)
    exact hrawIntegrable.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hnoAccessPositive))
  have hnoAccessEvent : MeasurableSet noAccessEvent := by
    change MeasurableSet ((fun student : Bool × (ℝ × (Feature → ℝ)) => student.1) ⁻¹'
      ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage measurable_fst
  have hsupported : ∀ᵐ student ∂noAccessLaw, student ∈ noAccessEvent := by
    change ∀ᵐ student ∂lg21NormalizedRestriction rawLaw noAccessEvent,
      student ∈ noAccessEvent
    exact Measure.ae_smul_measure (ae_restrict_mem hnoAccessEvent) _
  have houtput : publicOutput =ᵐ[noAccessLaw]
      fun student => primitiveOutput student.2 := by
    filter_upwards [hsupported] with student hstudent
    rcases student with ⟨access, primitive⟩
    cases haccess : access
    · simp [publicOutput, primitiveOutput,
        lg21HiddenAccessOptionalPrimitiveNoAccessOutput,
        lg21HiddenAccessOptionalPublicPayoff,
        lg21HiddenAccessOptionalObservedAction, haccess]
    · simp [noAccessEvent, lg21HiddenAccessNoAccessEvent, haccess] at hstudent
  have hcomposed : Integrable (fun student => primitiveOutput student.2) noAccessLaw :=
    hnoAccessIntegrable.congr houtput
  have hmapped : Integrable primitiveOutput (noAccessLaw.map Prod.snd) := by
    apply (integrable_map_measure
      (lg21HiddenAccessOptionalPrimitiveNoAccessOutput_measurable E).aestronglyMeasurable
      measurable_snd.aemeasurable).mpr
    simpa only [Function.comp_apply] using hcomposed
  rw [lg21HiddenAccessNoAccessLaw_map_student_eq M hnoAccess] at hmapped
  exact hmapped

/-! ## Law witnesses -/

/-- A positive event under a source composition product has a genuine positive
conditional fibre.  This is the semantic Fubini step used to turn a
population-level strict-gain witness into a source fairness witness; it does
not inspect strategy names or representations. -/
theorem lg21_exists_positive_fibre_of_compProd_positive
    {Base Outcome : Type*} [MeasurableSpace Base] [MeasurableSpace Outcome]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (outcomeKernel : Kernel Base Outcome) [IsMarkovKernel outcomeKernel]
    (event : Set (Base × Outcome)) (hevent : MeasurableSet event)
    (hpositive : 0 < (baseLaw ⊗ₘ outcomeKernel) event) :
    ∃ base, 0 < outcomeKernel base (Prod.mk base ⁻¹' event) := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ base, outcomeKernel base (Prod.mk base ⁻¹' event) = 0 := by
    intro base
    exact le_antisymm (hnone base) (zero_le _)
  rw [Measure.compProd_apply hevent] at hpositive
  have hfunction : (fun base => outcomeKernel base (Prod.mk base ⁻¹' event)) =
      fun _ => 0 := by
    funext base
    exact hzero base
  rw [hfunction, lintegral_zero] at hpositive
  exact (lt_irrefl 0 hpositive)

/-- A non-null primitive strict-gain set has a genuine public-base fibre with
positive strict actual-output mass under the source score/skill law. -/
theorem lg21HiddenAccessOptional_exists_observableStrictOutputWitness_of_primitive_strictGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstrict : lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
          lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive} ≠ 0) :
    ∃ publicBase,
      0 < gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase
        {scoreSkill | E.noReportPayoff publicBase <
          lg21HiddenAccessOptionalSourceOutput E scoreSkill.2 publicBase scoreSkill.1} := by
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
  let strictEvent := lg21HiddenAccessOptionalStrictSourceOutputEvent E
  let primitiveObservation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ))
  have hprimitiveObservation : Measurable primitiveObservation := by
    simpa [primitiveObservation] using
      lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation_measurable
        (Feature := Feature) testFeature
  have hstrictEvent : MeasurableSet strictEvent := by
    simpa [strictEvent] using
      lg21HiddenAccessOptionalStrictSourceOutputEvent_measurable E
  have hprimitiveFactor :
      (lg21ContinuousGaussianStudentPrimitiveLaw M).map primitiveObservation =
        baseLaw ⊗ₘ joint := by
    simpa [primitiveObservation, joint] using
      (lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance hsourceFactor)
  have hstrictPrimitive : lg21ContinuousGaussianStudentPrimitiveLaw M
      (primitiveObservation ⁻¹' strictEvent) ≠ 0 := by
    simpa [primitiveObservation, strictEvent,
      lg21HiddenAccessOptionalPrimitiveNoAccessOutput,
      lg21HiddenAccessOptionalPrimitiveAccessOutput] using hstrict
  have hstrictJoint : (baseLaw ⊗ₘ joint) strictEvent ≠ 0 := by
    rw [← hprimitiveFactor, Measure.map_apply hprimitiveObservation hstrictEvent]
    exact hstrictPrimitive
  rcases lg21_exists_positive_fibre_of_compProd_positive
      baseLaw joint strictEvent hstrictEvent (pos_iff_ne_zero.mpr hstrictJoint) with
    ⟨publicBase, hpositive⟩
  refine ⟨publicBase, ?_⟩
  simpa [joint, strictEvent] using hpositive

/-- A non-null primitive strict-gain set also has a genuine fixed
`(publicBase, latentSkill)` source fibre with positive strict actual-output
mass.  The proof first disintegrates the source population by public base and
then the source Gaussian pair by latent skill and additive test noise. -/
theorem lg21HiddenAccessOptional_exists_latentStrictOutputWitness_of_primitive_strictGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstrict : lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
          lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive} ≠ 0) :
    ∃ publicBase latentSkill,
      0 < E.testLaw latentSkill publicBase {score |
        E.noReportPayoff publicBase <
          lg21HiddenAccessOptionalSourceOutput E latentSkill publicBase score} := by
  rcases lg21HiddenAccessOptional_exists_observableStrictOutputWitness_of_primitive_strictGain
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hsourceFactor E
      hstrict with ⟨publicBase, hpositive⟩
  let strictEvent : Set (ℝ × ℝ) := {scoreSkill |
    E.noReportPayoff publicBase <
      lg21HiddenAccessOptionalSourceOutput E scoreSkill.2 publicBase scoreSkill.1}
  let stage : ℝ × ℝ → ℝ × ℝ := fun skillNoise =>
    (skillNoise.1 + skillNoise.2, skillNoise.1)
  have hstrictEvent : MeasurableSet strictEvent := by
    exact measurableSet_lt measurable_const
      ((lg21HiddenAccessOptionalSourceOutput_joint_measurable E).comp
        (measurable_const.prodMk measurable_id))
  have hstage : Measurable stage := by fun_prop
  have hpairPositive :
      0 < gaussianSignalPair (baseMean publicBase) baseVariance
        (M.noiseVariance testFeature : ℝ) (stage ⁻¹' strictEvent) := by
    change 0 < gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) publicBase strictEvent at hpositive
    rw [gaussianSignalJointKernel_apply, Measure.map_apply hstage hstrictEvent] at hpositive
    exact hpositive
  let skillLaw : Measure ℝ := gaussianReal (baseMean publicBase) baseVariance.toNNReal
  let noiseLaw : Measure ℝ := gaussianReal 0 (M.noiseVariance testFeature)
  let noiseKernel : Kernel ℝ ℝ := Kernel.const ℝ noiseLaw
  letI : IsProbabilityMeasure skillLaw := by
    dsimp [skillLaw]
    infer_instance
  letI : IsProbabilityMeasure noiseLaw := by
    dsimp [noiseLaw]
    infer_instance
  letI : IsMarkovKernel noiseKernel := by
    dsimp [noiseKernel]
    infer_instance
  have hcompPositive : 0 < (skillLaw ⊗ₘ noiseKernel) (stage ⁻¹' strictEvent) := by
    rw [Measure.compProd_const]
    simpa [skillLaw, noiseLaw, gaussianSignalPair] using hpairPositive
  rcases lg21_exists_positive_fibre_of_compProd_positive
      skillLaw noiseKernel (stage ⁻¹' strictEvent)
      (hstrictEvent.preimage hstage) hcompPositive with ⟨latentSkill, hnoisePositive⟩
  refine ⟨publicBase, latentSkill, ?_⟩
  have hnoisePositive' :
      0 < noiseLaw {noise |
        E.noReportPayoff publicBase <
          lg21HiddenAccessOptionalSourceOutput E latentSkill publicBase
            (latentSkill + noise)} := by
    simpa [noiseKernel, strictEvent, stage] using hnoisePositive
  let scoreStrictEvent : Set ℝ := {score |
    E.noReportPayoff publicBase <
      lg21HiddenAccessOptionalSourceOutput E latentSkill publicBase score}
  have hscoreStrictEvent : MeasurableSet scoreStrictEvent := by
    exact measurableSet_lt measurable_const
      (lg21HiddenAccessOptionalSourceOutput_measurable E latentSkill publicBase)
  have hadd : Measurable (fun noise : ℝ => noise + latentSkill) := by fun_prop
  have hshift : noiseLaw.map (fun noise : ℝ => noise + latentSkill) =
      gaussianReal latentSkill (M.noiseVariance testFeature) := by
    simpa [noiseLaw] using
      (gaussianReal_map_add_const (μ := (0 : ℝ))
        (v := M.noiseVariance testFeature) latentSkill)
  have hmapPositive :
      0 < (noiseLaw.map (fun noise : ℝ => noise + latentSkill)) scoreStrictEvent := by
    rw [Measure.map_apply hadd hscoreStrictEvent]
    simpa [scoreStrictEvent, add_comm] using hnoisePositive'
  rw [E.raw_test_law latentSkill publicBase, ← hshift]
  exact hmapPositive

/-- A positive strict-above branch proves that an output law is not the
no-report point mass.  This is intentionally a law inequality, not an FOSD
claim. -/
theorem lg21_outputLaw_ne_dirac_of_positive_strict_above
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) (output : Outcome → ℝ)
    (houtput : Measurable output) (noReportValue : ℝ)
    (hpositive : 0 < outcomeLaw {outcome | noReportValue < output outcome}) :
    outcomeLaw.map output ≠ Measure.dirac noReportValue := by
  intro hEq
  have hmap : outcomeLaw.map output (Set.Ioi noReportValue) =
      outcomeLaw {outcome | noReportValue < output outcome} := by
    rw [Measure.map_apply houtput measurableSet_Ioi]
    rfl
  rw [hEq] at hmap
  have hzero : outcomeLaw {outcome | noReportValue < output outcome} = 0 := by
    simpa using hmap.symm
  exact (ne_of_gt hpositive) hzero

/-- Literal demographic output laws differ whenever actual access weakly
improves the common primitive population and does so strictly on a non-null
set.  The conclusion is only unequal laws; no stochastic-order claim is
made. -/
theorem lg21HiddenAccessOptional_actualDemographicOutputLaw_ne_of_ae_strict_benefit
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hle : lg21HiddenAccessOptionalPrimitiveNoAccessOutput E ≤ᵐ[
      lg21ContinuousGaussianStudentPrimitiveLaw M]
        lg21HiddenAccessOptionalPrimitiveAccessOutput E)
    (hstrict : lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
          lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive} ≠ 0) :
    lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E ≠
      lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E := by
  rw [lg21HiddenAccessOptional_actualDemographicAccessOutputLaw_eq_primitive E,
    lg21HiddenAccessOptional_actualDemographicNoAccessOutputLaw_eq_primitive E hnoAccess]
  exact lg21_map_accessEstimate_ne_noAccessEstimate_of_ae_strict_benefit
    (lg21ContinuousGaussianStudentPrimitiveLaw M)
    (lg21HiddenAccessOptionalPrimitiveAccessOutput E)
    (lg21HiddenAccessOptionalPrimitiveNoAccessOutput E)
    (lg21HiddenAccessOptionalPrimitiveAccessOutput_measurable E)
    (lg21HiddenAccessOptionalPrimitiveNoAccessOutput_measurable E)
    E.primitiveAccessOutput_integrable
    (E.primitiveNoAccessOutput_integrable hnoAccess)
    hle hstrict

/-- The literal source model directly yields unequal actual demographic output
laws under optional reporting.  The proof only compares the two source
populations through their public output functions. -/
theorem lg21HiddenAccessOptional_actualDemographicOutputLaw_ne_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E ≠
      lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E := by
  rcases lg21HiddenAccessOptional_primitiveOutput_benefit_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable with ⟨hle, hstrict⟩
  exact lg21HiddenAccessOptional_actualDemographicOutputLaw_ne_of_ae_strict_benefit
    E hnoAccess hle hstrict

/-- The literal source-law surface for optional testing.  Every field is a
concrete law of the same source equilibrium: score laws conditional on latent
skill and public base, the corresponding source Gaussian joint law at a base,
or the literal access/no-access population output law. -/
def lg21HiddenAccessOptionalLiteralOutputLawSurface
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ) :
    LG21SourceLawPolicySurface ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ (Measure ℝ) where
  Equilibrium := LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature
  latentAccessLaw := fun E skill publicBase =>
    lg21HiddenAccessOptionalLatentAccessOutputLaw E skill publicBase
  latentNoAccessLaw := fun E _skill publicBase =>
    lg21HiddenAccessOptionalNoAccessOutputLaw E publicBase
  observableAccessLaw := fun E publicBase =>
    (gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) publicBase).map
      (fun scoreSkill =>
        lg21HiddenAccessOptionalSourceOutput E scoreSkill.2 publicBase scoreSkill.1)
  observableNoAccessLaw := fun E publicBase =>
    lg21HiddenAccessOptionalNoAccessOutputLaw E publicBase
  demographicAccessLaw := fun E =>
    lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E
  demographicNoAccessLaw := fun E =>
    lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E
  baseOnlyLaw := fun E publicBase =>
    lg21HiddenAccessOptionalNoAccessOutputLaw E publicBase
  fullFeatureLaw := fun E publicBase score =>
    Measure.dirac (lg21HiddenAccessOptionalBaseScoreOutput E (publicBase, score))

/-- Definition 2 evaluated at one supplied optional-reporting equilibrium. -/
def lg21HiddenAccessOptionalLatentSkillFairAt
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Prop :=
  ∀ latentSkill publicBase,
    lg21HiddenAccessOptionalLatentAccessOutputLaw E latentSkill publicBase =
      lg21HiddenAccessOptionalNoAccessOutputLaw E publicBase

/-- Definition 3 evaluated at one supplied optional-reporting equilibrium. -/
def lg21HiddenAccessOptionalObservablyFairAt
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ) : Prop :=
  ∀ publicBase,
    (gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) publicBase).map
        (fun scoreSkill =>
          lg21HiddenAccessOptionalSourceOutput E scoreSkill.2 publicBase scoreSkill.1) =
      lg21HiddenAccessOptionalNoAccessOutputLaw E publicBase

/-- Definition 4 evaluated at one supplied optional-reporting equilibrium. -/
def lg21HiddenAccessOptionalDemographicallyFairAt
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Prop :=
  lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E =
    lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E

/-- On the concrete optional source-law surface, a literal primitive strict
gain yields a genuine observable-base output-law witness. -/
theorem lg21HiddenAccessOptionalLiteralOutputLawSurface_not_observablyFairAt_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    ¬ lg21HiddenAccessOptionalObservablyFairAt E
      baseMean hbaseMean baseVariance := by
  rcases lg21HiddenAccessOptional_primitiveOutput_benefit_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable with ⟨_hle, hstrict⟩
  rcases lg21HiddenAccessOptional_exists_observableStrictOutputWitness_of_primitive_strictGain
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hsourceFactor E
      hstrict with ⟨publicBase, hpositive⟩
  intro hfair
  have hne : (gaussianSignalJointKernel baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) publicBase).map
      (fun scoreSkill =>
        lg21HiddenAccessOptionalSourceOutput E scoreSkill.2 publicBase scoreSkill.1) ≠
      Measure.dirac (E.noReportPayoff publicBase) := by
    apply lg21_outputLaw_ne_dirac_of_positive_strict_above
    · exact (lg21HiddenAccessOptionalSourceOutput_joint_measurable E).comp
        (measurable_const.prodMk measurable_id)
    · exact hpositive
  exact hne (hfair publicBase)

/-- On the concrete optional source-law surface, literal source stability has
a fixed latent-skill and public-base witness against latent-skill fairness.
The witness is obtained from the literal Gaussian source factorization, rather
than being supplied as an equality between abstract policy fields. -/
theorem lg21HiddenAccessOptionalLiteralOutputLawSurface_not_latentSkillFairAt_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    ¬ lg21HiddenAccessOptionalLatentSkillFairAt E := by
  rcases lg21HiddenAccessOptional_primitiveOutput_benefit_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable with ⟨_hle, hstrict⟩
  rcases lg21HiddenAccessOptional_exists_latentStrictOutputWitness_of_primitive_strictGain
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hsourceFactor E
      hstrict with ⟨publicBase, latentSkill, hpositive⟩
  intro hfair
  have hne : (E.testLaw latentSkill publicBase).map
      (lg21HiddenAccessOptionalSourceOutput E latentSkill publicBase) ≠
      Measure.dirac (E.noReportPayoff publicBase) :=
    lg21_outputLaw_ne_dirac_of_positive_strict_above
    (E.testLaw latentSkill publicBase)
    (lg21HiddenAccessOptionalSourceOutput E latentSkill publicBase)
    (lg21HiddenAccessOptionalSourceOutput_measurable E latentSkill publicBase)
    (E.noReportPayoff publicBase) hpositive
  exact hne (hfair latentSkill publicBase)

/-- On the concrete optional source-law surface, literal source stability
refutes demographic fairness at the very equilibrium whose actions generated
the compared laws.  There are no abstract surface-field equalities among the
hypotheses. -/
theorem lg21HiddenAccessOptionalLiteralOutputLawSurface_not_demographicallyFairAt_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    ¬ lg21HiddenAccessOptionalDemographicallyFairAt E := by
  exact lg21HiddenAccessOptional_actualDemographicOutputLaw_ne_of_literalSourceStability
    M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
    htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
    hsourceFactor E hreportBest hstable

/-- A literal latent-skill output witness is sufficient to refute source
Definition 2, once the policy surface has been identified with the literal
actual output laws. -/
theorem lg21_not_lawLatentSkillFair_of_literal_optional_output_witness
    {Feature Skill Base Test : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (equilibrium : S.Equilibrium) (skill : Skill) (publicBase : Base)
    (sourceSkill : ℝ)
    (sourceBase : LG21NonTestFeature Feature testFeature → ℝ)
    (hAccessLaw : S.latentAccessLaw equilibrium skill publicBase =
      lg21HiddenAccessOptionalLatentAccessOutputLaw E sourceSkill sourceBase)
    (hNoAccessLaw : S.latentNoAccessLaw equilibrium skill publicBase =
      lg21HiddenAccessOptionalNoAccessOutputLaw E sourceBase)
    (hstrict : 0 < E.testLaw sourceSkill sourceBase {score |
      E.noReportPayoff sourceBase <
        lg21HiddenAccessOptionalSourceOutput E sourceSkill sourceBase score}) :
    ¬ lg21SourceLawLatentSkillFair S := by
  apply lg21_not_lawLatentSkillFair_of_witness equilibrium skill publicBase
  rw [hAccessLaw, hNoAccessLaw]
  exact lg21_outputLaw_ne_dirac_of_positive_strict_above
    (E.testLaw sourceSkill sourceBase)
    (lg21HiddenAccessOptionalSourceOutput E sourceSkill sourceBase)
    (lg21HiddenAccessOptionalSourceOutput_measurable E sourceSkill sourceBase)
    (E.noReportPayoff sourceBase) hstrict

/-- A literal fixed-base output witness is sufficient to refute source
Definition 3.  Its `skillScoreLaw` is required explicitly so that the
conditional population law cannot be silently replaced by a named strategy
fibre. -/
theorem lg21_not_lawObservablyFair_of_literal_optional_output_witness
    {Feature Skill Base Test : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (equilibrium : S.Equilibrium) (publicBase : Base)
    (sourceBase : LG21NonTestFeature Feature testFeature → ℝ)
    (skillScoreLaw : Measure (ℝ × ℝ))
    (hAccessLaw : S.observableAccessLaw equilibrium publicBase =
      lg21HiddenAccessOptionalObservableAccessOutputLaw E sourceBase skillScoreLaw)
    (hNoAccessLaw : S.observableNoAccessLaw equilibrium publicBase =
      lg21HiddenAccessOptionalNoAccessOutputLaw E sourceBase)
    (hstrict : 0 < skillScoreLaw {profile |
      E.noReportPayoff sourceBase <
        lg21HiddenAccessOptionalSourceOutput E profile.1 sourceBase profile.2}) :
    ¬ lg21SourceLawObservablyFair S := by
  apply lg21_not_lawObservablyFair_of_witness equilibrium publicBase
  rw [hAccessLaw, hNoAccessLaw]
  exact lg21_outputLaw_ne_dirac_of_positive_strict_above
    skillScoreLaw
    (fun profile =>
      lg21HiddenAccessOptionalSourceOutput E profile.1 sourceBase profile.2)
    (lg21HiddenAccessOptionalObservableAccessOutput_measurable E sourceBase)
    (E.noReportPayoff sourceBase) hstrict

/-- The literal demographic law inequality above is a direct witness against
source Definition 4 once the policy surface fields are tied to the actual
access/no-access public-output laws. -/
theorem lg21_not_lawDemographicallyFair_of_literal_optional_output_witness
    {Feature Skill Base Test : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (equilibrium : S.Equilibrium) (hnoAccess : 0 < M.accessLaw {false})
    (hAccessLaw : S.demographicAccessLaw equilibrium =
      lg21HiddenAccessOptionalActualDemographicAccessOutputLaw E)
    (hNoAccessLaw : S.demographicNoAccessLaw equilibrium =
      lg21HiddenAccessOptionalActualDemographicNoAccessOutputLaw E)
    (hle : lg21HiddenAccessOptionalPrimitiveNoAccessOutput E ≤ᵐ[
      lg21ContinuousGaussianStudentPrimitiveLaw M]
        lg21HiddenAccessOptionalPrimitiveAccessOutput E)
    (hstrict : lg21ContinuousGaussianStudentPrimitiveLaw M
      {primitive |
        lg21HiddenAccessOptionalPrimitiveNoAccessOutput E primitive <
          lg21HiddenAccessOptionalPrimitiveAccessOutput E primitive} ≠ 0) :
    ¬ lg21SourceLawDemographicallyFair S := by
  apply lg21_not_lawDemographicallyFair_of_witness equilibrium
  rw [hAccessLaw, hNoAccessLaw]
  exact lg21HiddenAccessOptional_actualDemographicOutputLaw_ne_of_ae_strict_benefit
    E hnoAccess hle hstrict

end

end LG21TestOptionalPolicies

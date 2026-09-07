import KR21Monoculture.UniformOrderStatisticsBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic

open MeasureTheory
open scoped BigOperators

namespace KR21Monoculture

/-!
# Independent true-rank / cardinal-utility bridge for the KR21 four-candidate instance

The existing rank-mean reduction uses `sourceExpectedOrderStatisticValue`.
This module gives that table an actual probability-law interpretation for one
selected candidate: a finite true-rank draw is sampled independently of the
four iid Uniform cardinal values.  It deliberately proves no statement about
how the sequential ranking process selects that candidate.
-/

noncomputable def sourceFourUniformValueLaw : Measure (Fin 4 → ℝ) :=
  Measure.pi (fun _ : Fin 4 => PRPKG24AccuracyDiversity.uniform01Measure)

noncomputable def sourceFourRankValueJointLaw
    (rankLaw : PMF SourceFourCandidate) :
    Measure (SourceFourCandidate × (Fin 4 → ℝ)) :=
  rankLaw.toMeasure.prod sourceFourUniformValueLaw

noncomputable def sourceFourSelectedUniformUtility
    (outcome : SourceFourCandidate × (Fin 4 → ℝ)) : ℝ :=
  if outcome.1 = 0 then
    AppliedModelingLib.Probability.upperOrderStatistic outcome.2 0
  else if outcome.1 = 1 then
    AppliedModelingLib.Probability.upperOrderStatistic outcome.2 1
  else if outcome.1 = 2 then
    AppliedModelingLib.Probability.upperOrderStatistic outcome.2 2
  else
    AppliedModelingLib.Probability.upperOrderStatistic outcome.2 3

/-- The true-rank coordinate and the four iid Uniform cardinal-value sample
are independent because the joint source law is their actual product measure. -/
theorem sourceFourRankValue_indepFun
    (rankLaw : PMF SourceFourCandidate) :
    ProbabilityTheory.IndepFun
      (fun outcome : SourceFourCandidate × (Fin 4 → ℝ) => outcome.1)
      (fun outcome : SourceFourCandidate × (Fin 4 → ℝ) => outcome.2)
      (sourceFourRankValueJointLaw rankLaw) := by
  unfold sourceFourRankValueJointLaw sourceFourUniformValueLaw
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

theorem sourceFourSelectedUniformUtility_eq_upperOrderStatistic
    (outcome : SourceFourCandidate × (Fin 4 → ℝ)) :
    sourceFourSelectedUniformUtility outcome =
      AppliedModelingLib.Probability.upperOrderStatistic outcome.2 outcome.1 := by
  rcases outcome with ⟨rank, sample⟩
  fin_cases rank <;>
    simp [sourceFourSelectedUniformUtility, Fin.ext_iff]

private theorem sourceFourSelectedUniformUtility_measurable :
    Measurable sourceFourSelectedUniformUtility := by
  unfold sourceFourSelectedUniformUtility
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_fst measurable_const
  · exact (AppliedModelingLib.Probability.upperOrderStatistic_measurable 0).comp measurable_snd
  · apply Measurable.ite
    · exact measurableSet_eq_fun measurable_fst measurable_const
    · exact (AppliedModelingLib.Probability.upperOrderStatistic_measurable 1).comp measurable_snd
    · apply Measurable.ite
      · exact measurableSet_eq_fun measurable_fst measurable_const
      · exact (AppliedModelingLib.Probability.upperOrderStatistic_measurable 2).comp measurable_snd
      · exact (AppliedModelingLib.Probability.upperOrderStatistic_measurable 3).comp measurable_snd

/-- The independent true-rank/cardinal-value utility is integrable under the
explicit finite-PMF times iid-Uniform product law. -/
theorem sourceFourSelectedUniformUtility_integrable
    (rankLaw : PMF SourceFourCandidate) :
    Integrable sourceFourSelectedUniformUtility
      (sourceFourRankValueJointLaw rankLaw) := by
  unfold sourceFourRankValueJointLaw sourceFourUniformValueLaw
  apply (MeasureTheory.integrable_prod_iff
    sourceFourSelectedUniformUtility_measurable.aestronglyMeasurable).2
  constructor
  · filter_upwards with candidate
    simpa only [sourceFourSelectedUniformUtility_eq_upperOrderStatistic] using
      (PRPKG24AccuracyDiversity.uniform01ProductMeasure_upperOrderStatistic_integrable
        candidate)
  · exact Integrable.of_finite

/-- Under the explicitly independent product law, the selected cardinal
utility has exactly the finite true-rank mixture of the iid-Uniform
order-statistic table. -/
theorem sourceFourSelectedUniformUtility_integral_eq_pmfExp
    (rankLaw : PMF SourceFourCandidate) :
    (∫ outcome, sourceFourSelectedUniformUtility outcome
      ∂sourceFourRankValueJointLaw rankLaw) =
      AppliedModelingLib.pmfExp rankLaw
        (fun candidate => (sourceExpectedOrderStatisticValue candidate : ℝ)) := by
  unfold sourceFourRankValueJointLaw sourceFourUniformValueLaw
  letI : SFinite sourceFourUniformValueLaw := by
    unfold sourceFourUniformValueLaw
    infer_instance
  calc
    (∫ outcome, sourceFourSelectedUniformUtility outcome
      ∂sourceFourRankValueJointLaw rankLaw) =
        ∫ candidate, ∫ sample,
          sourceFourSelectedUniformUtility (candidate, sample)
          ∂Measure.pi (fun _ : Fin 4 => PRPKG24AccuracyDiversity.uniform01Measure)
          ∂rankLaw.toMeasure := by
          exact MeasureTheory.integral_prod _
            (sourceFourSelectedUniformUtility_integrable rankLaw)
    _ = ∫ candidate,
          (sourceExpectedOrderStatisticValue candidate : ℝ)
          ∂rankLaw.toMeasure := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with candidate
          calc
            (∫ sample, sourceFourSelectedUniformUtility (candidate, sample)
              ∂Measure.pi (fun _ : Fin 4 => PRPKG24AccuracyDiversity.uniform01Measure)) =
                AppliedModelingLib.Probability.expectedUpperOrderStatistic
                  (Measure.pi (fun _ : Fin 4 => PRPKG24AccuracyDiversity.uniform01Measure))
                  candidate := by
                    unfold AppliedModelingLib.Probability.expectedUpperOrderStatistic
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with sample
                    exact sourceFourSelectedUniformUtility_eq_upperOrderStatistic
                      (candidate, sample)
            _ = (sourceExpectedOrderStatisticValue candidate : ℝ) := by
              exact
                (sourceExpectedOrderStatisticValue_eq_uniform01_expectedUpperOrderStatistic
                  candidate).symm
    _ = AppliedModelingLib.pmfExp rankLaw
          (fun candidate => (sourceExpectedOrderStatisticValue candidate : ℝ)) := by
          symm
          exact AppliedModelingLib.pmfExp_eq_integral_toMeasure rankLaw _

/-- The preceding product-law expectation written as the finite weighted
true-rank table.  The weights are the atom probabilities of `rankLaw`. -/
theorem sourceFourSelectedUniformUtility_integral_eq_weighted_rank_table
    (rankLaw : PMF SourceFourCandidate) :
    (∫ outcome, sourceFourSelectedUniformUtility outcome
      ∂sourceFourRankValueJointLaw rankLaw) =
      ∑ candidate : SourceFourCandidate,
        (rankLaw candidate).toReal *
          (sourceExpectedOrderStatisticValue candidate : ℝ) := by
  rw [sourceFourSelectedUniformUtility_integral_eq_pmfExp]
  rfl

/-! ## Finite ranking-conditioned selectors -/

section FiniteOutcome

variable {Outcome : Type*} [Fintype Outcome]
  [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]

/-- Select the Uniform cardinal value at a deterministic true-rank chosen
from a finite outcome. -/
noncomputable def sourceFourSelectedUniformUtilityOf
    (select : Outcome → SourceFourCandidate)
    (outcome : Outcome × (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtility (select outcome.1, outcome.2)

omit [Fintype Outcome] [MeasurableSpace Outcome]
  [MeasurableSingletonClass Outcome] in
theorem sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic
    (select : Outcome → SourceFourCandidate)
    (outcome : Outcome × (Fin 4 → ℝ)) :
    sourceFourSelectedUniformUtilityOf select outcome =
      AppliedModelingLib.Probability.upperOrderStatistic outcome.2 (select outcome.1) := by
  exact sourceFourSelectedUniformUtility_eq_upperOrderStatistic
    (select outcome.1, outcome.2)

private theorem sourceFourSelectedUniformUtilityOf_measurable
    (select : Outcome → SourceFourCandidate) :
    Measurable (sourceFourSelectedUniformUtilityOf select) := by
  unfold sourceFourSelectedUniformUtilityOf
  apply sourceFourSelectedUniformUtility_measurable.comp
  exact ((measurable_of_finite select).comp measurable_fst).prodMk measurable_snd

/-- A finite ranking-conditioned true-rank selector remains independent of
the iid Uniform cardinal sample under the explicitly constructed product law. -/
theorem sourceFourSelectedRankValue_indepFun
    (outcomeLaw : PMF Outcome) (select : Outcome → SourceFourCandidate) :
    ProbabilityTheory.IndepFun
      (fun outcome : Outcome × (Fin 4 → ℝ) => select outcome.1)
      (fun outcome : Outcome × (Fin 4 → ℝ) => outcome.2)
      (outcomeLaw.toMeasure.prod sourceFourUniformValueLaw) := by
  unfold sourceFourUniformValueLaw
  exact ProbabilityTheory.indepFun_prod (measurable_of_finite select) measurable_id

/-- Integrability of a finite-outcome rank selector against the actual
outcome-times-iid-Uniform product measure. -/
theorem sourceFourSelectedUniformUtilityOf_integrable
    (outcomeLaw : PMF Outcome) (select : Outcome → SourceFourCandidate) :
    Integrable (sourceFourSelectedUniformUtilityOf select)
      (outcomeLaw.toMeasure.prod sourceFourUniformValueLaw) := by
  unfold sourceFourUniformValueLaw
  apply (MeasureTheory.integrable_prod_iff
    (sourceFourSelectedUniformUtilityOf_measurable select).aestronglyMeasurable).2
  constructor
  · filter_upwards with outcome
    simpa only [sourceFourSelectedUniformUtilityOf,
      sourceFourSelectedUniformUtility_eq_upperOrderStatistic] using
      (PRPKG24AccuracyDiversity.uniform01ProductMeasure_upperOrderStatistic_integrable
        (select outcome))
  · exact Integrable.of_finite

/-- A finite outcome law, independent of iid Uniform cardinal values, has
expected selected utility equal to the finite mixture of the four exact
order-statistic means. -/
theorem sourceFourSelectedUniformUtilityOf_integral_eq_pmfExp
    [DecidableEq Outcome] (outcomeLaw : PMF Outcome)
    (select : Outcome → SourceFourCandidate) :
    (∫ outcome, sourceFourSelectedUniformUtilityOf select outcome
      ∂outcomeLaw.toMeasure.prod sourceFourUniformValueLaw) =
      AppliedModelingLib.pmfExp outcomeLaw
        (fun outcome => (sourceExpectedOrderStatisticValue (select outcome) : ℝ)) := by
  letI : SFinite sourceFourUniformValueLaw := by
    unfold sourceFourUniformValueLaw
    infer_instance
  calc
    (∫ outcome, sourceFourSelectedUniformUtilityOf select outcome
      ∂outcomeLaw.toMeasure.prod sourceFourUniformValueLaw) =
        ∫ finiteOutcome, ∫ sample,
          sourceFourSelectedUniformUtilityOf select (finiteOutcome, sample)
          ∂sourceFourUniformValueLaw ∂outcomeLaw.toMeasure := by
          exact MeasureTheory.integral_prod _
            (sourceFourSelectedUniformUtilityOf_integrable outcomeLaw select)
    _ = ∫ finiteOutcome,
          (sourceExpectedOrderStatisticValue (select finiteOutcome) : ℝ)
          ∂outcomeLaw.toMeasure := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with finiteOutcome
          calc
            (∫ sample,
              sourceFourSelectedUniformUtilityOf select (finiteOutcome, sample)
              ∂sourceFourUniformValueLaw) =
                AppliedModelingLib.Probability.expectedUpperOrderStatistic
                  sourceFourUniformValueLaw (select finiteOutcome) := by
                    unfold AppliedModelingLib.Probability.expectedUpperOrderStatistic
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with sample
                    exact sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic
                      select (finiteOutcome, sample)
            _ = (sourceExpectedOrderStatisticValue (select finiteOutcome) : ℝ) := by
              exact
                (sourceExpectedOrderStatisticValue_eq_uniform01_expectedUpperOrderStatistic
                  (select finiteOutcome)).symm
    _ = AppliedModelingLib.pmfExp outcomeLaw
          (fun finiteOutcome =>
            (sourceExpectedOrderStatisticValue (select finiteOutcome) : ℝ)) := by
          symm
          exact AppliedModelingLib.pmfExp_eq_integral_toMeasure outcomeLaw _

/-- The generic finite-outcome product-law identity written as an explicit
weighted sum of deterministic true-rank choices. -/
theorem sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table
    [DecidableEq Outcome] (outcomeLaw : PMF Outcome)
    (select : Outcome → SourceFourCandidate) :
    (∫ outcome, sourceFourSelectedUniformUtilityOf select outcome
      ∂outcomeLaw.toMeasure.prod sourceFourUniformValueLaw) =
      ∑ finiteOutcome : Outcome,
        (outcomeLaw finiteOutcome).toReal *
          (sourceExpectedOrderStatisticValue (select finiteOutcome) : ℝ) := by
  rw [sourceFourSelectedUniformUtilityOf_integral_eq_pmfExp]
  rfl

end FiniteOutcome

end KR21Monoculture

import LG21TestOptionalPolicies.ReportRequiredFullPublicPositiveMassUnraveling

/-!
# Explicit best-response bridge for report-required LG21 paths

The source-facing records use Definition 1's actual taking comparison
directly.  These variants keep the positive-mass and selected-PBO arguments
independent of the legacy sequential record's opaque consistency component.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- The full-public taking set is upward closed when the literal taking
best-response implication and strict expected-payoff monotonicity hold. -/
theorem lg21_reportRequired_fullPublic_takeSet_upperClosed_of_takeBestResponse
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (htakeBestResponse : ∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun skill => E.takeDecision skill base = true)
        (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
        (fun _skill => E.noReportPayoff base))
    (hstrict : ∀ base, StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)) :
    ∀ ⦃low high : Base × ℝ⦄,
      low.1 = high.1 -> low.2 ≤ high.2 ->
        low ∈ lg21ReportRequiredFullPublicTakeSet
          (fun base skill => E.takeDecision skill base) ->
        high ∈ lg21ReportRequiredFullPublicTakeSet
          (fun base skill => E.takeDecision skill base) := by
  intro low high hbase hskill hlow
  rcases low with ⟨lowBase, lowSkill⟩
  rcases high with ⟨highBase, highSkill⟩
  change lowBase = highBase at hbase
  change lowSkill ≤ highSkill at hskill
  change E.takeDecision lowSkill lowBase = true at hlow
  subst highBase
  change E.takeDecision highSkill lowBase = true
  exact bool_choice_upperClosed_of_noProfitableBinaryChoiceDeviation_strictMono
    (E.takeDecision · lowBase) (htakeBestResponse lowBase) (hstrict lowBase)
    hskill hlow

/-- The complementary exact no-take action set is downward closed under the
same literal taking best-response implication. -/
theorem lg21_reportRequired_fullPublic_noTakeSet_downwardClosed_of_takeBestResponse
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (htakeBestResponse : ∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun skill => E.takeDecision skill base = true)
        (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
        (fun _skill => E.noReportPayoff base))
    (hstrict : ∀ base, StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)) :
    ∀ ⦃low high : Base × ℝ⦄,
      low.1 = high.1 -> low.2 ≤ high.2 ->
        high ∈ lg21ReportRequiredFullPublicNoTakeSet
          (fun base skill => E.takeDecision skill base) ->
        low ∈ lg21ReportRequiredFullPublicNoTakeSet
          (fun base skill => E.takeDecision skill base) := by
  intro low high hbase hskill hhigh
  by_contra hnot
  have hlowTake : low ∈ lg21ReportRequiredFullPublicTakeSet
      (fun base skill => E.takeDecision skill base) := by
    change E.takeDecision low.2 low.1 = true
    simpa [lg21ReportRequiredFullPublicNoTakeSet] using hnot
  have hhighTake : high ∈ lg21ReportRequiredFullPublicTakeSet
      (fun base skill => E.takeDecision skill base) :=
    lg21_reportRequired_fullPublic_takeSet_upperClosed_of_takeBestResponse
      htakeBestResponse hstrict hbase hskill hlowTake
  change E.takeDecision high.2 high.1 = false at hhigh
  change E.takeDecision high.2 high.1 = true at hhighTake
  simp [hhigh] at hhighTake

/-- A global strict expected gain on literal no-takers makes the no-take
event null using only the displayed Definition 1 taking comparison. -/
theorem lg21_reportRequired_fullPublic_noPositiveMassNoTake_of_globalStrictGain_of_takeBestResponse
    {Omega Base Test : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (htakeBestResponse : ∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun skill => E.takeDecision skill base = true)
        (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
        (fun _skill => E.noReportPayoff base))
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (hstrictGain : ∀ᵐ omega ∂rawLaw,
      E.takeDecision (skill omega) (base omega) = false ->
        E.noReportPayoff (base omega) <
          lg21ReportRequiredSequentialTakeExpectedPayoff E
            (skill omega) (base omega)) :
    rawLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  have himpossible : ∀ᵐ omega ∂rawLaw,
      E.takeDecision (skill omega) (base omega) ≠ false := by
    filter_upwards [hstrictGain] with omega hgain hnoTake
    have hbest := (htakeBestResponse (base omega)).2 (skill omega) (by
      simpa [hnoTake])
    exact (not_le_of_gt (hgain hnoTake)) hbest
  have hzero := ae_iff.mp himpossible
  simpa only [Set.mem_setOf_eq, not_not] using hzero

end

end LG21TestOptionalPolicies

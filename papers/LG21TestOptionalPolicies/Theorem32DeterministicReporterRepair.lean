import LG21TestOptionalPolicies.Theorem32RandomizedPolicy

/-!
# Deterministic-reporter repair for LG21 Theorem 3.2

The printed Theorem 3.2 permits arbitrary randomized policies.  That is too
weak: equal expected estimates do not identify output laws.  This module
isolates a smaller repair that is sufficient for the optional-reporting
decision stage.  A person who reports receives a deterministic point estimate;
the no-report branch may still be an arbitrary law.

The key conclusion is operational.  When one score is reported with positive
probability and every score has positive probability, observable fairness and
ex-post best response force the arbitrary no-report law to collapse to the
same point mass as every reported outcome.  Thus the proof does not silently
assume deterministic behavior for people who do not report.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib

/-- The actual optional-reporting output law at a realized score. -/
def lg21OptionalDeterministicReporterOperationalLaw
    {Test Estimate : Type*}
    (baseLaw : PMF Estimate)
    (reportedValue : Test -> Estimate)
    (reports : Test -> Bool) (test : Test) : PMF Estimate :=
  if reports test = true then PMF.pure (reportedValue test) else baseLaw

/-!
The proof below is deliberately phrased over finite score and estimate spaces.
It is the finite, fully operational version of the source's optional-reporting
decision stage.  The continuous source model requires the corresponding
almost-everywhere/regularity bridge; no such bridge is hidden here.
-/

theorem lg21_optional_reporting_operational_blank_of_deterministic_reporters
    {Test Estimate : Type*}
    [Fintype Test] [DecidableEq Test]
    [Fintype Estimate] [DecidableEq Estimate]
    (testLaw : PMF Test)
    (baseLaw : PMF Estimate)
    (reportedValue : Test -> Estimate)
    (reports : Test -> Bool)
    (estimateValue : Estimate -> Real)
    (hEstimateValueInjective : Function.Injective estimateValue)
    (hFullSupport : forall test, 0 < (testLaw test).toReal)
    (hSomeReporter : exists test, reports test = true)
    (hOperationalFair :
      testLaw.bind
          (lg21OptionalDeterministicReporterOperationalLaw
            baseLaw reportedValue reports) =
        baseLaw)
    (hReportedBestResponse : forall test, reports test = true ->
      pmfExp baseLaw estimateValue <= estimateValue (reportedValue test)) :
    exists commonEstimate,
      baseLaw = PMF.pure commonEstimate /\
      (forall test,
        lg21OptionalDeterministicReporterOperationalLaw
            baseLaw reportedValue reports test = PMF.pure commonEstimate) := by
  classical
  rcases hSomeReporter with ⟨reporter, hreporter⟩
  let operationalLaw : Test -> PMF Estimate :=
    lg21OptionalDeterministicReporterOperationalLaw
      baseLaw reportedValue reports
  let baseMean : Real := pmfExp baseLaw estimateValue
  have hMeanFair :
      pmfExp testLaw (fun test => pmfExp (operationalLaw test) estimateValue) =
        baseMean := by
    calc
      pmfExp testLaw (fun test => pmfExp (operationalLaw test) estimateValue) =
          pmfExp (testLaw.bind operationalLaw) estimateValue :=
        (pmfExp_bind testLaw operationalLaw estimateValue).symm
      _ = pmfExp baseLaw estimateValue := by rw [hOperationalFair]
      _ = baseMean := rfl
  have hOperationalMeanGe : forall test,
      baseMean <= pmfExp (operationalLaw test) estimateValue := by
    intro test
    by_cases hreports : reports test = true
    · simpa [operationalLaw,
        lg21OptionalDeterministicReporterOperationalLaw, hreports, baseMean]
        using hReportedBestResponse test hreports
    · simp [operationalLaw,
        lg21OptionalDeterministicReporterOperationalLaw, hreports, baseMean]
  have hReporterOperationalMeanEq : forall test, reports test = true ->
      pmfExp (operationalLaw test) estimateValue = baseMean := by
    intro test hreports
    apply le_antisymm
    · by_contra hnot
      have hstrict :
          baseMean < pmfExp (operationalLaw test) estimateValue :=
        lt_of_not_ge hnot
      have havg_strict :
          baseMean <
            pmfExp testLaw
              (fun other => pmfExp (operationalLaw other) estimateValue) :=
        lg21_pmfExp_gt_const_of_forall_ge_exists_gt
          testLaw
          (fun other => pmfExp (operationalLaw other) estimateValue)
          baseMean hOperationalMeanGe
          ⟨test, hFullSupport test, hstrict⟩
      rw [hMeanFair] at havg_strict
      exact False.elim (lt_irrefl _ havg_strict)
    · exact hOperationalMeanGe test
  have hReporterValueEq : forall test, reports test = true ->
      reportedValue test = reportedValue reporter := by
    intro test hreports
    apply hEstimateValueInjective
    have htest := hReporterOperationalMeanEq test hreports
    have href := hReporterOperationalMeanEq reporter hreporter
    simpa [operationalLaw,
      lg21OptionalDeterministicReporterOperationalLaw, hreports,
      hreporter, baseMean] using htest.trans href.symm
  let commonEstimate := reportedValue reporter
  let pointIndicator : Estimate -> Real :=
    fun estimate => if estimate = commonEstimate then 1 else 0
  let basePointMass : Real := pmfExp baseLaw pointIndicator
  have hPointFair :
      pmfExp testLaw (fun test => pmfExp (operationalLaw test) pointIndicator) =
        basePointMass := by
    calc
      pmfExp testLaw (fun test => pmfExp (operationalLaw test) pointIndicator) =
          pmfExp (testLaw.bind operationalLaw) pointIndicator :=
        (pmfExp_bind testLaw operationalLaw pointIndicator).symm
      _ = pmfExp baseLaw pointIndicator := by rw [hOperationalFair]
      _ = basePointMass := rfl
  have hBasePointMassLeOne : basePointMass <= 1 := by
    apply pmfExp_le_of_forall_le baseLaw pointIndicator 1
    intro estimate
    dsimp [pointIndicator]
    split <;> norm_num
  have hOperationalPointMassGe : forall test,
      basePointMass <= pmfExp (operationalLaw test) pointIndicator := by
    intro test
    by_cases hreports : reports test = true
    · have hvalue : reportedValue test = commonEstimate := by
        simpa [commonEstimate] using hReporterValueEq test hreports
      simp [operationalLaw,
        lg21OptionalDeterministicReporterOperationalLaw, hreports,
        hvalue, pointIndicator, hBasePointMassLeOne]
    · simp [operationalLaw,
        lg21OptionalDeterministicReporterOperationalLaw, hreports,
        basePointMass]
  have hBasePointMassEqOne : basePointMass = 1 := by
    apply le_antisymm hBasePointMassLeOne
    by_contra hnot
    have hstrict :
        basePointMass < pmfExp (operationalLaw reporter) pointIndicator := by
      have : pmfExp (operationalLaw reporter) pointIndicator = 1 := by
        simp [operationalLaw,
          lg21OptionalDeterministicReporterOperationalLaw, hreporter,
          commonEstimate, pointIndicator]
      rw [this]
      exact lt_of_not_ge hnot
    have havg_strict :
        basePointMass <
          pmfExp testLaw
            (fun test => pmfExp (operationalLaw test) pointIndicator) :=
      lg21_pmfExp_gt_const_of_forall_ge_exists_gt
        testLaw
        (fun test => pmfExp (operationalLaw test) pointIndicator)
        basePointMass hOperationalPointMassGe
        ⟨reporter, hFullSupport reporter, hstrict⟩
    rw [hPointFair] at havg_strict
    exact False.elim (lt_irrefl _ havg_strict)
  have hBaseMassEqOne : baseLaw commonEstimate = 1 := by
    have hPointMass :
        basePointMass = (baseLaw commonEstimate).toReal := by
      simp [basePointMass, pointIndicator, commonEstimate, pmfExp]
    apply (ENNReal.toReal_eq_one_iff _).mp
    linarith [hPointMass, hBasePointMassEqOne]
  have hBaseLaw : baseLaw = PMF.pure commonEstimate := by
    apply PMF.ext
    intro estimate
    by_cases hestimate : estimate = commonEstimate
    · subst estimate
      simp [hBaseMassEqOne]
    · have hnotMem : estimate ∉ baseLaw.support := by
        intro hmem
        have hsupp : baseLaw.support = {commonEstimate} :=
          (PMF.apply_eq_one_iff baseLaw commonEstimate).1 hBaseMassEqOne
        rw [hsupp] at hmem
        exact hestimate (by simpa using hmem)
      have hzero : baseLaw estimate = 0 :=
        (PMF.apply_eq_zero_iff baseLaw estimate).2 hnotMem
      simp [hzero, PMF.pure_apply, hestimate]
  refine ⟨commonEstimate, hBaseLaw, ?_⟩
  intro test
  by_cases hreports : reports test = true
  · have hvalue : reportedValue test = commonEstimate := by
      simpa [commonEstimate] using hReporterValueEq test hreports
    simp [lg21OptionalDeterministicReporterOperationalLaw, hreports, hvalue]
  · simp [lg21OptionalDeterministicReporterOperationalLaw, hreports, hBaseLaw]

end

end LG21TestOptionalPolicies

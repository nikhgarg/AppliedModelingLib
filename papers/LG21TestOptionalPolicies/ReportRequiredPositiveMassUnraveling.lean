import LG21TestOptionalPolicies.PositiveMassDeviation
import LG21TestOptionalPolicies.ReportRequiredPublicActionPBOBridge
import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Semantic positive-mass unraveling for report-required LG21 testing

This file proves the central report-required step of the repaired Lemma 4.1
argument.  It is deliberately expressed in terms of the semantic facts that
the source states, rather than an API field whose name suggests a posterior:

* a positive-mass no-take branch has its literal conditional skill mean;
* a positive-mass reported branch uses the conditional skill law induced by
  the public taking decision;
* the expected reported PBO is strictly increasing in latent skill; and
* students satisfy Definition 1 binary best responses.

From those facts, a positive-mass no-take cohort is impossible whenever a
positive-mass reporter cohort exists.  The proof derives the order of action
sets from best responses; it does not assume a cutoff.  The remaining Gaussian
source bridge has to prove the displayed selected-posterior and strict-payoff
facts for the literal population.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set

/-! ## Best responses order the public taking action -/

/--
With a strictly increasing take payoff and a common no-take payoff, Definition
1 best responses cannot place a no-taker weakly above a taker.  This is the
semantic source of the threshold shape; no cutoff representation is assumed.
-/
theorem lg21_reportRequired_noTake_lt_take_of_strictExpectedPayoff_of_bestResponse
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (base : Base)
    (hbest : NoProfitableBinaryChoiceDeviation
      (fun skill ↦ E.takeDecision skill base = true)
      (fun skill ↦ lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
      (fun _skill ↦ E.noReportPayoff base))
    (hstrict : StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base))
    {noTake take : ℝ}
    (hnoTake : E.takeDecision noTake base = false)
    (htake : E.takeDecision take base = true) :
    noTake < take := by
  by_contra hnot
  have htake_le_noTake : take ≤ noTake := le_of_not_gt hnot
  rcases htake_le_noTake.lt_or_eq with hlt | heq
  · have htakeBR := hbest.1 take htake
    have hnoTakeBR := hbest.2 noTake (by simp [hnoTake])
    exact (not_lt_of_ge hnoTakeBR)
      (lt_of_le_of_lt htakeBR (hstrict hlt))
  · subst take
    simp [hnoTake] at htake

/-- Compatibility form of the direct best-response ordering lemma. -/
theorem lg21_reportRequired_noTake_lt_take_of_strictExpectedPayoff
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E) (base : Base)
    (hstrict : StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base))
    {noTake take : ℝ}
    (hnoTake : E.takeDecision noTake base = false)
    (htake : E.takeDecision take base = true) :
    noTake < take := by
  exact lg21_reportRequired_noTake_lt_take_of_strictExpectedPayoff_of_bestResponse
    base (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base)
    hstrict hnoTake htake

/-! ## Positive-mass report-required closure -/

/--
Under the public-action PBO semantics, a report-required candidate with a
positive-mass reporter branch cannot retain a positive-mass no-take branch.

The selected-posterior equality is stated directly as a conditional mean of
the raw score posterior restricted to the action event.  Thus the theorem
cannot be discharged merely by supplying a field named `PBO`: the caller must
prove the conditional-law identity from the public action rule.  The action
order used below is derived from Definition 1 and strict expected payoff.
-/
theorem lg21_reportRequired_positiveMassPBO_no_positiveMass_noTake
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : Measure ℝ)
    [IsProbabilityMeasure skillLaw] [IsFiniteMeasure skillLaw]
    (htakeMeasurable : Measurable (E.takeDecision · base))
    (hreporterPositive :
      0 < skillLaw {skill | E.takeDecision skill base = true})
    (hnoTakePBO : E.noReportPayoff base =
      ∫ skill, skill ∂lg21NormalizedRestriction skillLaw
        {skill | E.takeDecision skill base = false})
    (hnoTakeIntegrable : Integrable (fun skill : ℝ => skill)
      (lg21NormalizedRestriction skillLaw
        {skill | E.takeDecision skill base = false}))
    (rawPosterior : Test → Measure ℝ)
    (hrawPosteriorFinite : ∀ test, IsFiniteMeasure (rawPosterior test))
    (hselectedPositive :
      0 < skillLaw {skill | E.takeDecision skill base = true} →
        ∀ test,
          0 < rawPosterior test {skill | E.takeDecision skill base = true})
    (hselectedIntegrable : ∀ test,
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction (rawPosterior test)
          {skill | E.takeDecision skill base = true}))
    (hreportedPBO : ∀ test,
      E.reportedPayoff base test =
        ∫ skill, skill ∂lg21NormalizedRestriction (rawPosterior test)
          {skill | E.takeDecision skill base = true})
    (hstrictExpected : StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)) :
    ¬ 0 < skillLaw {skill | E.takeDecision skill base = false} := by
  intro hnoTakePositive
  let noTakeSet : Set ℝ := {skill | E.takeDecision skill base = false}
  let takeSet : Set ℝ := {skill | E.takeDecision skill base = true}
  have hnoTakeMeasurable : MeasurableSet noTakeSet := by
    change MeasurableSet ((E.takeDecision · base) ⁻¹' ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage htakeMeasurable
  have htakeMeasurableSet : MeasurableSet takeSet := by
    change MeasurableSet ((E.takeDecision · base) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage htakeMeasurable
  have hnoTakePBO' : E.noReportPayoff base =
      ∫ skill, skill ∂lg21NormalizedRestriction skillLaw noTakeSet := by
    simpa [noTakeSet] using hnoTakePBO
  have hnoTakeIntegrable' : Integrable (fun skill : ℝ => skill)
      (lg21NormalizedRestriction skillLaw noTakeSet) := by
    simpa [noTakeSet] using hnoTakeIntegrable
  have horder : ∀ noTake take,
      noTake ∈ noTakeSet → take ∈ takeSet → noTake < take := by
    intro noTake take hnoTake htake
    exact lg21_reportRequired_noTake_lt_take_of_strictExpectedPayoff
      hEq base hstrictExpected hnoTake htake
  have hnoTakeMean_lt_take : ∀ take, take ∈ takeSet →
      E.noReportPayoff base < take := by
    intro take htake
    rw [hnoTakePBO']
    exact lg21NormalizedRestriction_mean_lt_upper
      skillLaw noTakeSet (fun skill : ℝ => skill) take
      hnoTakeMeasurable hnoTakePositive hnoTakeIntegrable'
      (fun noTake hnoTake => horder noTake take hnoTake htake)
  have hreportedAboveNoTake : ∀ test,
      E.noReportPayoff base < E.reportedPayoff base test := by
    intro test
    letI : IsFiniteMeasure (rawPosterior test) := hrawPosteriorFinite test
    rw [hreportedPBO test]
    exact lg21NormalizedRestriction_mean_gt_lower
      (rawPosterior test) takeSet (fun skill : ℝ => skill)
      (E.noReportPayoff base) htakeMeasurableSet
      (by simpa [takeSet] using hselectedPositive hreporterPositive test)
      (by simpa [takeSet] using hselectedIntegrable test)
      (fun skill htake => hnoTakeMean_lt_take skill htake)
  have htakeAboveNoTake : ∀ skill,
      E.noReportPayoff base <
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base := by
    intro skill
    letI : IsProbabilityMeasure (E.testLaw skill base) :=
      E.testLaw_isProbability skill base
    have hstrictIntegral := lg21_integral_lt_integral_of_ae_lt_probability
      (E.testLaw skill base)
      (integrable_const (E.noReportPayoff base))
      (E.reportedPayoff_integrable skill base)
      (Filter.Eventually.of_forall (hreportedAboveNoTake))
    simpa [lg21ReportRequiredSequentialTakeExpectedPayoff] using hstrictIntegral
  have hnoTakeNonempty : noTakeSet.Nonempty := by
    by_contra hempty
    have hempty' : noTakeSet = ∅ := not_nonempty_iff_eq_empty.mp hempty
    have hzero : skillLaw noTakeSet = 0 := by simp [hempty']
    exact (ne_of_gt hnoTakePositive) hzero
  rcases hnoTakeNonempty with ⟨skill, hnoTake⟩
  have hnoTakeBR :=
    (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base).2
      skill (by simpa [noTakeSet] using hnoTake)
  exact (not_le_of_gt (htakeAboveNoTake skill)) hnoTakeBR

end

end LG21TestOptionalPolicies

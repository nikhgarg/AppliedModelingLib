import LG21TestOptionalPolicies.StrategicDominanceContinuous

/-!
# Continuous source-shaped repair of LG21 Theorem 3.2

The unrestricted randomized-policy statement of Theorem 3.2 is false.  This
file records a corrected positive result over continuous estimate laws while
keeping the two source decision times separate.

For optional reporting, the strategic comparison is made after the score is
observed.  Equality of expected estimates is therefore required to identify
the base-only and score-conditioned estimate laws pointwise.  For reporting
required after testing, the taking decision is made before the score noise is
drawn.  Its repair consequently uses the expected estimate of the entire
test-given-skill output law and an explicitly stronger ex-ante identification
condition.

Two further hypotheses are stated rather than hidden.  First, a score or type
that has a strict gain must be detected by positive population mass; this is
the continuous-support/regularity replacement for finite full support.
Second, the unused test option is weakly no worse than the base-only option.
That off-path condition is needed to conclude the source's pointwise
test-blankness, rather than only an almost-everywhere on-path statement.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open MeasureTheory
open ProbabilityTheory

/-- Expected numerical estimate under a continuous estimate law. -/
def lg21ContinuousEstimateLawMean (law : Measure ℝ) : ℝ :=
  ∫ estimate, estimate ∂law

/--
Continuous-law mean identification for the optional-reporting decision.
Integrability is explicit so a nonintegrable law cannot satisfy the condition
merely through the Bochner integral's default value.
-/
def LG21ContinuousExpectedEstimateIdentifiesPolicyLaw
    {Skill Base Test : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)) : Prop :=
  ∀ e base test,
    Integrable id (S.baseOnlyLaw e base) →
      Integrable id (S.fullFeatureLaw e base test) →
        lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) =
            lg21ContinuousEstimateLawMean
              (S.fullFeatureLaw e base test) →
          S.baseOnlyLaw e base = S.fullFeatureLaw e base test

/--
Ex-ante mean identification for reporting required after testing.  Equality
of the base-only mean and the mean of the whole test-given-skill output law
identifies those two estimate laws.  This is the direct ex-ante analogue of
the optional-reporting mean-identification condition.
-/
def LG21ReportRequiredExAnteExpectedEstimateIdentifiesTakeLaw
    {Skill Base Test : Type*}
    [MeasurableSpace Skill] [MeasurableSpace Test]
    (S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ))
    (testGivenSkill : S.Equilibrium → Base → Kernel Skill Test)
    (fullFeatureKernel : S.Equilibrium → Base → Kernel Test ℝ) : Prop :=
  ∀ e skill base,
    Integrable id (S.baseOnlyLaw e base) →
      Integrable id
          ((testGivenSkill e base skill).bind
            (fullFeatureKernel e base)) →
        lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) =
            lg21ContinuousEstimateLawMean
              ((testGivenSkill e base skill).bind
                (fullFeatureKernel e base)) →
          S.baseOnlyLaw e base =
            (testGivenSkill e base skill).bind
              (fullFeatureKernel e base)

/--
Operational mixture identification needed to recover pointwise test blankness
from a report-required ex-ante law.  Equality of a test-mixture law with the
base law does not identify its score-conditioned components in general, so
this condition is separate from (and not hidden inside) expected-estimate
identification.
-/
def LG21ReportRequiredTestMixtureIdentifiesScoreLaws
    {Skill Base Test : Type*}
    [MeasurableSpace Skill] [MeasurableSpace Test]
    (S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ))
    (testGivenSkill : S.Equilibrium → Base → Kernel Skill Test)
    (fullFeatureKernel : S.Equilibrium → Base → Kernel Test ℝ) : Prop :=
  ∀ e skill base,
    S.baseOnlyLaw e base =
        (testGivenSkill e base skill).bind (fullFeatureKernel e base) →
      ∀ test,
        S.baseOnlyLaw e base = fullFeatureKernel e base test

/-!
## A binary-choice population lemma

Both source regimes reduce to this argument after selecting the correct actor
and selected-action law.  Optional reporting uses the realized score as the
actor.  Report-required testing uses latent skill and makes the selected law
the test-noise mixture formed before the taking decision.
-/

/--
If the actual chosen-law mixture equals the base law, no detected actor can
obtain a strict expected gain.  Weak no-downside and binary best response then
force equality of the base and selected expected estimates for every actor,
including actors who do not select the action on path.
-/
theorem lg21_continuous_binary_choice_selected_mean_eq_base_of_fairness
    {Actor : Type*} [MeasurableSpace Actor]
    (actorLaw : Measure Actor)
    (baseLaw : Measure ℝ)
    (selectedKernel chosenKernel : Kernel Actor ℝ)
    (choose : Actor → Bool)
    (hActorLawProbability : IsProbabilityMeasure actorLaw)
    (hChosenLaw :
      ∀ actor,
        chosenKernel actor =
          if choose actor = true then selectedKernel actor else baseLaw)
    (hChosenMeanTower :
      lg21ContinuousEstimateLawMean (actorLaw.bind chosenKernel) =
        ∫ actor,
          lg21ContinuousEstimateLawMean (chosenKernel actor) ∂actorLaw)
    (hChosenMeanIntegrable :
      Integrable
        (fun actor ↦ lg21ContinuousEstimateLawMean (chosenKernel actor))
        actorLaw)
    (hBestResponse :
      NoProfitableBinaryChoiceDeviation
        (fun actor ↦ choose actor = true)
        (fun actor ↦
          lg21ContinuousEstimateLawMean (selectedKernel actor))
        (fun _actor ↦ lg21ContinuousEstimateLawMean baseLaw))
    (hNoDownside :
      ∀ actor,
        lg21ContinuousEstimateLawMean baseLaw ≤
          lg21ContinuousEstimateLawMean (selectedKernel actor))
    (hStrictGainDetected :
      ∀ actor,
        lg21ContinuousEstimateLawMean baseLaw <
            lg21ContinuousEstimateLawMean (chosenKernel actor) →
          actorLaw
              {other |
                lg21ContinuousEstimateLawMean baseLaw <
                  lg21ContinuousEstimateLawMean
                    (chosenKernel other)} ≠ 0)
    (hFairOperationalLaw : actorLaw.bind chosenKernel = baseLaw) :
    ∀ actor,
      lg21ContinuousEstimateLawMean baseLaw =
        lg21ContinuousEstimateLawMean (selectedKernel actor) := by
  letI : IsProbabilityMeasure actorLaw := hActorLawProbability
  have hIntegralEq :
      (∫ actor,
          lg21ContinuousEstimateLawMean (chosenKernel actor) ∂actorLaw) =
        lg21ContinuousEstimateLawMean baseLaw := by
    calc
      (∫ actor,
          lg21ContinuousEstimateLawMean (chosenKernel actor) ∂actorLaw) =
          lg21ContinuousEstimateLawMean (actorLaw.bind chosenKernel) :=
        hChosenMeanTower.symm
      _ = lg21ContinuousEstimateLawMean baseLaw := by
        rw [hFairOperationalLaw]
  have hChosenMeanGe :
      ∀ actor,
        lg21ContinuousEstimateLawMean baseLaw ≤
          lg21ContinuousEstimateLawMean (chosenKernel actor) := by
    intro actor
    by_cases hchoose : choose actor = true
    · rw [hChosenLaw actor, if_pos hchoose]
      exact hBestResponse.1 actor hchoose
    · rw [hChosenLaw actor, if_neg hchoose]
  have hChosenMeanNotGt :
      ∀ actor,
        ¬ lg21ContinuousEstimateLawMean baseLaw <
          lg21ContinuousEstimateLawMean (chosenKernel actor) := by
    intro actor hstrict
    have hIntegralStrict :=
      lg21_integral_accessEstimate_gt_noAccessEstimate
        actorLaw
        (fun other ↦
          lg21ContinuousEstimateLawMean (chosenKernel other))
        (fun _other ↦ lg21ContinuousEstimateLawMean baseLaw)
        hChosenMeanIntegrable
        (integrable_const (lg21ContinuousEstimateLawMean baseLaw))
        hChosenMeanGe
        (hStrictGainDetected actor hstrict)
    have :
        lg21ContinuousEstimateLawMean baseLaw <
          ∫ other,
            lg21ContinuousEstimateLawMean (chosenKernel other) ∂actorLaw := by
      simpa using hIntegralStrict
    rw [hIntegralEq] at this
    exact (lt_irrefl _ this)
  intro actor
  by_cases hchoose : choose actor = true
  · have hChosenEq :
        lg21ContinuousEstimateLawMean baseLaw =
          lg21ContinuousEstimateLawMean (chosenKernel actor) :=
      le_antisymm (hChosenMeanGe actor)
        (le_of_not_gt (hChosenMeanNotGt actor))
    rw [hChosenLaw actor, if_pos hchoose] at hChosenEq
    exact hChosenEq
  · exact
      le_antisymm (hNoDownside actor)
        (hBestResponse.2 actor hchoose)

/-! ## Optional reporting: the score is observed before the binary choice -/

/--
Corrected continuous optional-reporting Theorem 3.2.

`chosenEstimateKernel` is the actual operational law after the reporting
choice, and the observable access law is its mixture under the continuous
test law.  The best-response premise is ex post in the realized test.  The
no-downside and positive-mass-detection premises are the explicit conditions
that upgrade an on-path continuous argument to the source's pointwise
test-blank quantifiers.
-/
theorem paper_theorem3_2_continuous_optional_fair_implies_test_blank_of_mean_identifiable_policy
    {Skill Base Test : Type*}
    [MeasurableSpace Test]
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)}
    (testLaw : S.Equilibrium → Base → Measure Test)
    (fullFeatureKernel chosenEstimateKernel :
      S.Equilibrium → Base → Kernel Test ℝ)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (hTestLawProbability :
      ∀ e base, IsProbabilityMeasure (testLaw e base))
    (hBaseOnlyProbability :
      ∀ e base, IsProbabilityMeasure (S.baseOnlyLaw e base))
    (hFullFeatureKernelMarkov :
      ∀ e base, IsMarkovKernel (fullFeatureKernel e base))
    (hChosenEstimateKernelMarkov :
      ∀ e base, IsMarkovKernel (chosenEstimateKernel e base))
    (hFullFeatureKernel :
      ∀ e base test,
        fullFeatureKernel e base test = S.fullFeatureLaw e base test)
    (hChosenEstimateKernel :
      ∀ e base test,
        chosenEstimateKernel e base test =
          if reportDecision e base test = true then
            fullFeatureKernel e base test
          else
            S.baseOnlyLaw e base)
    (hObservableAccessOperational :
      ∀ e base,
        S.observableAccessLaw e base =
          (testLaw e base).bind (chosenEstimateKernel e base))
    (hObservableNoAccessBaseOnly :
      ∀ e base,
        S.observableNoAccessLaw e base = S.baseOnlyLaw e base)
    (hChosenMeanTower :
      ∀ e base,
        lg21ContinuousEstimateLawMean
            ((testLaw e base).bind (chosenEstimateKernel e base)) =
          ∫ test,
            lg21ContinuousEstimateLawMean
              (chosenEstimateKernel e base test) ∂testLaw e base)
    (hChosenMeanIntegrable :
      ∀ e base,
        Integrable
          (fun test ↦
            lg21ContinuousEstimateLawMean
              (chosenEstimateKernel e base test))
          (testLaw e base))
    (hBestResponse :
      ∀ e base,
        NoProfitableBinaryChoiceDeviation
          (fun test ↦ reportDecision e base test = true)
          (fun test ↦
            lg21ContinuousEstimateLawMean
              (fullFeatureKernel e base test))
          (fun _test ↦
            lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base)))
    (hNoDownside :
      ∀ e base test,
        lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) ≤
          lg21ContinuousEstimateLawMean
            (fullFeatureKernel e base test))
    (hStrictGainDetected :
      ∀ e base test,
        lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) <
            lg21ContinuousEstimateLawMean
              (chosenEstimateKernel e base test) →
          testLaw e base
              {other |
                lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) <
                  lg21ContinuousEstimateLawMean
                    (chosenEstimateKernel e base other)} ≠ 0)
    (hBaseIntegrable :
      ∀ e base, Integrable id (S.baseOnlyLaw e base))
    (hFullFeatureIntegrable :
      ∀ e base test, Integrable id (S.fullFeatureLaw e base test))
    (hIdentifies : LG21ContinuousExpectedEstimateIdentifiesPolicyLaw S)
    (hLatentToObservable :
      lg21SourceLawLatentSkillFair S → lg21SourceLawObservablyFair S)
    (hFair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    lg21SourceLawTestBlank S := by
  have hObservableFair : lg21SourceLawObservablyFair S :=
    hFair.elim hLatentToObservable id
  intro e base test
  letI : IsProbabilityMeasure (S.baseOnlyLaw e base) :=
    hBaseOnlyProbability e base
  letI : IsMarkovKernel (fullFeatureKernel e base) :=
    hFullFeatureKernelMarkov e base
  letI : IsMarkovKernel (chosenEstimateKernel e base) :=
    hChosenEstimateKernelMarkov e base
  have hFairOperationalLaw :
      (testLaw e base).bind (chosenEstimateKernel e base) =
        S.baseOnlyLaw e base := by
    calc
      (testLaw e base).bind (chosenEstimateKernel e base) =
          S.observableAccessLaw e base :=
        (hObservableAccessOperational e base).symm
      _ = S.observableNoAccessLaw e base := hObservableFair e base
      _ = S.baseOnlyLaw e base := hObservableNoAccessBaseOnly e base
  have hMeanEq :=
    lg21_continuous_binary_choice_selected_mean_eq_base_of_fairness
      (testLaw e base) (S.baseOnlyLaw e base)
      (fullFeatureKernel e base) (chosenEstimateKernel e base)
      (reportDecision e base)
      (hTestLawProbability e base)
      (hChosenEstimateKernel e base)
      (hChosenMeanTower e base)
      (hChosenMeanIntegrable e base)
      (hBestResponse e base)
      (hNoDownside e base)
      (hStrictGainDetected e base)
      hFairOperationalLaw test
  rw [hFullFeatureKernel e base test] at hMeanEq
  exact
    hIdentifies e base test
      (hBaseIntegrable e base) (hFullFeatureIntegrable e base test) hMeanEq

/-! ## Report required: taking is chosen before test noise -/

/--
Corrected continuous report-required Theorem 3.2.

Here the selected-action kernel is the full test-given-skill output law, so
the binary best response compares ex-ante expected estimates.  Ex-ante mean
identification first equates that mixture law with the base law.  A distinct,
explicit mixture-identification premise then recovers every realized test
law; the optional-reporting pointwise condition would not suffice at this
decision time.
-/
theorem paper_theorem3_2_continuous_report_required_fair_implies_test_blank_of_ex_ante_mean_identifiable_policy
    {Skill Base Test : Type*}
    [Nonempty Skill] [MeasurableSpace Skill] [MeasurableSpace Test]
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)}
    (skillLaw : S.Equilibrium → Base → Measure Skill)
    (testGivenSkill : S.Equilibrium → Base → Kernel Skill Test)
    (fullFeatureKernel : S.Equilibrium → Base → Kernel Test ℝ)
    (takeEstimateKernel chosenEstimateKernel :
      S.Equilibrium → Base → Kernel Skill ℝ)
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (hSkillLawProbability :
      ∀ e base, IsProbabilityMeasure (skillLaw e base))
    (hBaseOnlyProbability :
      ∀ e base, IsProbabilityMeasure (S.baseOnlyLaw e base))
    (hTestGivenSkillMarkov :
      ∀ e base, IsMarkovKernel (testGivenSkill e base))
    (hFullFeatureKernelMarkov :
      ∀ e base, IsMarkovKernel (fullFeatureKernel e base))
    (hTakeEstimateKernelMarkov :
      ∀ e base, IsMarkovKernel (takeEstimateKernel e base))
    (hChosenEstimateKernelMarkov :
      ∀ e base, IsMarkovKernel (chosenEstimateKernel e base))
    (hFullFeatureKernel :
      ∀ e base test,
        fullFeatureKernel e base test = S.fullFeatureLaw e base test)
    (hTakeEstimateKernel :
      ∀ e base skill,
        takeEstimateKernel e base skill =
          (testGivenSkill e base skill).bind
            (fullFeatureKernel e base))
    (hChosenEstimateKernel :
      ∀ e base skill,
        chosenEstimateKernel e base skill =
          if takeDecision e skill base = true then
            takeEstimateKernel e base skill
          else
            S.baseOnlyLaw e base)
    (hObservableAccessOperational :
      ∀ e base,
        S.observableAccessLaw e base =
          (skillLaw e base).bind (chosenEstimateKernel e base))
    (hObservableNoAccessBaseOnly :
      ∀ e base,
        S.observableNoAccessLaw e base = S.baseOnlyLaw e base)
    (hChosenMeanTower :
      ∀ e base,
        lg21ContinuousEstimateLawMean
            ((skillLaw e base).bind (chosenEstimateKernel e base)) =
          ∫ skill,
            lg21ContinuousEstimateLawMean
              (chosenEstimateKernel e base skill) ∂skillLaw e base)
    (hChosenMeanIntegrable :
      ∀ e base,
        Integrable
          (fun skill ↦
            lg21ContinuousEstimateLawMean
              (chosenEstimateKernel e base skill))
          (skillLaw e base))
    (hBestResponse :
      ∀ e base,
        NoProfitableBinaryChoiceDeviation
          (fun skill ↦ takeDecision e skill base = true)
          (fun skill ↦
            lg21ContinuousEstimateLawMean
              (takeEstimateKernel e base skill))
          (fun _skill ↦
            lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base)))
    (hNoDownside :
      ∀ e base skill,
        lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) ≤
          lg21ContinuousEstimateLawMean
            (takeEstimateKernel e base skill))
    (hStrictGainDetected :
      ∀ e base skill,
        lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) <
            lg21ContinuousEstimateLawMean
              (chosenEstimateKernel e base skill) →
          skillLaw e base
              {other |
                lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) <
                  lg21ContinuousEstimateLawMean
                    (chosenEstimateKernel e base other)} ≠ 0)
    (hBaseIntegrable :
      ∀ e base, Integrable id (S.baseOnlyLaw e base))
    (hTakeEstimateIntegrable :
      ∀ e base skill,
        Integrable id (takeEstimateKernel e base skill))
    (hMeanIdentifiesTakeLaw :
      LG21ReportRequiredExAnteExpectedEstimateIdentifiesTakeLaw
        S testGivenSkill fullFeatureKernel)
    (hTestMixtureIdentifiesScoreLaws :
      LG21ReportRequiredTestMixtureIdentifiesScoreLaws
        S testGivenSkill fullFeatureKernel)
    (hLatentToObservable :
      lg21SourceLawLatentSkillFair S → lg21SourceLawObservablyFair S)
    (hFair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    lg21SourceLawTestBlank S := by
  have hObservableFair : lg21SourceLawObservablyFair S :=
    hFair.elim hLatentToObservable id
  intro e base test
  letI : IsProbabilityMeasure (S.baseOnlyLaw e base) :=
    hBaseOnlyProbability e base
  letI : IsMarkovKernel (testGivenSkill e base) :=
    hTestGivenSkillMarkov e base
  letI : IsMarkovKernel (fullFeatureKernel e base) :=
    hFullFeatureKernelMarkov e base
  letI : IsMarkovKernel (takeEstimateKernel e base) :=
    hTakeEstimateKernelMarkov e base
  letI : IsMarkovKernel (chosenEstimateKernel e base) :=
    hChosenEstimateKernelMarkov e base
  have hFairOperationalLaw :
      (skillLaw e base).bind (chosenEstimateKernel e base) =
        S.baseOnlyLaw e base := by
    calc
      (skillLaw e base).bind (chosenEstimateKernel e base) =
          S.observableAccessLaw e base :=
        (hObservableAccessOperational e base).symm
      _ = S.observableNoAccessLaw e base := hObservableFair e base
      _ = S.baseOnlyLaw e base := hObservableNoAccessBaseOnly e base
  let skill : Skill := Classical.choice inferInstance
  have hMeanEq :=
    lg21_continuous_binary_choice_selected_mean_eq_base_of_fairness
      (skillLaw e base) (S.baseOnlyLaw e base)
      (takeEstimateKernel e base) (chosenEstimateKernel e base)
      (fun skill ↦ takeDecision e skill base)
      (hSkillLawProbability e base)
      (hChosenEstimateKernel e base)
      (hChosenMeanTower e base)
      (hChosenMeanIntegrable e base)
      (hBestResponse e base)
      (hNoDownside e base)
      (hStrictGainDetected e base)
      hFairOperationalLaw skill
  have hTakeMeanEq :
      lg21ContinuousEstimateLawMean (S.baseOnlyLaw e base) =
        lg21ContinuousEstimateLawMean
          ((testGivenSkill e base skill).bind
            (fullFeatureKernel e base)) := by
    rw [← hTakeEstimateKernel e base skill]
    exact hMeanEq
  have hBaseEqTakeLaw :=
    hMeanIdentifiesTakeLaw e skill base
      (hBaseIntegrable e base)
      (by
        rw [← hTakeEstimateKernel e base skill]
        exact hTakeEstimateIntegrable e base skill)
      hTakeMeanEq
  have hBaseEqKernel :=
    hTestMixtureIdentifiesScoreLaws e skill base hBaseEqTakeLaw test
  calc
    S.baseOnlyLaw e base = fullFeatureKernel e base test := hBaseEqKernel
    _ = S.fullFeatureLaw e base test := hFullFeatureKernel e base test

end

end LG21TestOptionalPolicies

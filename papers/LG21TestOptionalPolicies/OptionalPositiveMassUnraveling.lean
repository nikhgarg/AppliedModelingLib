import LG21TestOptionalPolicies.PositiveMassDeviation
import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Semantic positive-mass unraveling for optional reporting

This module isolates the ex-post optional-reporting step in the LG21 Lemma
4.1 repair.  It deliberately does not assume a cutoff or inspect the name of
an action function.  Instead it works with the literal no-report event and
the two semantic conditions stated by Definition 1:

* an agent assigned to the no-report event weakly prefers its branch PBO to
  reporting; and
* when that event has positive mass, its PBO is the conditional mean of the
  reported PBO over the *actual* event.

For an atomless score law and a strictly increasing reported PBO, those two
conditions are incompatible with positive no-report mass.  The proof is the
conditional-mean argument directly: an integrable random variable cannot be
almost surely at most its own mean on a probability space unless it equals
that mean almost surely, while strict monotonicity makes that level fibre a
singleton and hence null.

No value is imposed on a null no-report fibre.  Thus this is a positive-branch
calibration result, rather than an off-path-belief completion.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set

/-! ## Generic semantic closure -/

/--
A literal positive-mass unchosen branch cannot be calibrated to its own
conditional mean when the chosen payoff is strictly increasing and the
underlying law is atomless.

`unchosen` is an event, not a presumed interval or threshold.  The partition
condition merely says that it is the actual alternative action to `chosen`.
The conclusion is therefore semantic and applies to any measurable action
rule satisfying Definition 1's binary best-response condition.
-/
theorem no_positive_mass_unchosen_of_literal_conditional_mean
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw] [NoAtoms scoreLaw]
    (chosen : ℝ → Prop) (unchosen : Set ℝ)
    (hunchosenMeasurable : MeasurableSet unchosen)
    (hpartition : ∀ score, score ∈ unchosen ↔ ¬ chosen score)
    (reportedPBO : ℝ → ℝ) (unchosenPBO : ℝ)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE scoreLaw chosen reportedPBO
        (fun _score => unchosenPBO))
    (hstrict : StrictMono reportedPBO)
    (hintegrable :
      Integrable reportedPBO
        (lg21NormalizedRestriction scoreLaw unchosen))
    (hcalibrated : unchosenPBO =
      ∫ score, reportedPBO score ∂lg21NormalizedRestriction scoreLaw unchosen) :
    ¬ 0 < scoreLaw unchosen := by
  intro hunchosenPositive
  let branchLaw : Measure ℝ := lg21NormalizedRestriction scoreLaw unchosen
  letI : IsProbabilityMeasure branchLaw := by
    dsimp [branchLaw]
    exact lg21NormalizedRestriction_isProbability scoreLaw unchosen
      (ne_of_gt hunchosenPositive) (measure_ne_top _ _)
  have hunchosenBR_restrict :
      ∀ᵐ score ∂scoreLaw.restrict unchosen,
        reportedPBO score ≤ unchosenPBO := by
    rw [ae_restrict_iff' hunchosenMeasurable]
    filter_upwards [hbest.2] with score hbestScore hscoreUnchosen
    exact hbestScore ((hpartition score).1 hscoreUnchosen)
  have hunchosenBR :
      ∀ᵐ score ∂branchLaw,
        reportedPBO score ≤ unchosenPBO := by
    change ∀ᵐ score ∂(scoreLaw unchosen)⁻¹ • scoreLaw.restrict unchosen,
      reportedPBO score ≤ unchosenPBO
    exact Measure.ae_smul_measure hunchosenBR_restrict _
  let meanLevel : ℝ := ∫ score, reportedPBO score ∂branchLaw
  have hcalibrated' : unchosenPBO = meanLevel := by
    simpa [branchLaw, meanLevel] using hcalibrated
  have hlevelSubsingleton :
      ({score | reportedPBO score = meanLevel} : Set ℝ).Subsingleton := by
    intro left hleft right hright
    apply hstrict.injective
    change reportedPBO left = meanLevel at hleft
    change reportedPBO right = meanLevel at hright
    rw [hleft, hright]
  have hlevelNull :
      branchLaw {score | reportedPBO score = meanLevel} = 0 := by
    by_cases hempty : {score | reportedPBO score = meanLevel} = ∅
    · simp [hempty]
    · obtain ⟨score, hscore⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      apply measure_mono_null
        (fun candidate hcandidate =>
          Set.mem_singleton_iff.mpr (hlevelSubsingleton hcandidate hscore))
      change lg21NormalizedRestriction scoreLaw unchosen {score} = 0
      rw [lg21NormalizedRestriction_apply scoreLaw
        (event := unchosen) (target := {score})
        (measurableSet_singleton score)]
      rw [measure_mono_null inter_subset_left (measure_singleton score)]
      simp
  have haboveMean :
      0 < branchLaw {score | meanLevel < reportedPBO score} := by
    exact positive_mass_above_mean_of_null_level branchLaw reportedPBO
      (by simpa [branchLaw] using hintegrable)
      meanLevel rfl hlevelNull
  have haboveMeanNull :
      branchLaw {score | meanLevel < reportedPBO score} = 0 := by
    rw [ae_iff] at hunchosenBR
    simpa only [Set.mem_setOf_eq, hcalibrated', not_le] using hunchosenBR
  exact (ne_of_gt haboveMean) haboveMeanNull

/-! ## Optional-reporting presentation -/

/--
The generic conditional-mean closure instantiated with the optional-reporting
Boolean action.  This wrapper records the actual score event explicitly; it
does not infer a threshold from the implementation of `reportDecision`.
-/
theorem lg21_optional_no_positive_mass_nonreport_of_literal_conditional_mean
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw] [NoAtoms scoreLaw]
    (reportDecision : ℝ → Bool)
    (hnoReportMeasurable :
      MeasurableSet {score | reportDecision score = false})
    (reportedPBO : ℝ → ℝ) (noReportPBO : ℝ)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE scoreLaw
        (fun score => reportDecision score = true)
        reportedPBO (fun _score => noReportPBO))
    (hstrict : StrictMono reportedPBO)
    (hintegrable :
      Integrable reportedPBO
        (lg21NormalizedRestriction scoreLaw
          {score | reportDecision score = false}))
    (hcalibrated : noReportPBO =
      ∫ score, reportedPBO score ∂lg21NormalizedRestriction scoreLaw
        {score | reportDecision score = false}) :
    ¬ 0 < scoreLaw {score | reportDecision score = false} := by
  apply no_positive_mass_unchosen_of_literal_conditional_mean
    (scoreLaw := scoreLaw)
    (chosen := fun score => reportDecision score = true)
    (unchosen := {score | reportDecision score = false})
    (reportedPBO := reportedPBO) (unchosenPBO := noReportPBO)
    hnoReportMeasurable
  · intro score
    cases hdecision : reportDecision score <;> simp [hdecision]
  · exact hbest
  · exact hstrict
  · exact hintegrable
  · exact hcalibrated

/--
Source-timed Definition 1 supplies the optional-reporting best-response
premise.  The remaining inputs are exactly the positive-branch calibration,
strict score monotonicity, integrability, and score-law regularity that must
be established from the literal source population.
-/
theorem lg21_optional_source_timed_no_positive_mass_nonreport
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base)
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw] [NoAtoms scoreLaw]
    (hnoReportMeasurable :
      MeasurableSet {score | E.reportDecision base score = false})
    (hstrict : StrictMono (E.reportedPayoff base))
    (hintegrable :
      Integrable (E.reportedPayoff base)
        (lg21NormalizedRestriction scoreLaw
          {score | E.reportDecision base score = false}))
    (hcalibrated : E.noReportPayoff base =
      ∫ score, E.reportedPayoff base score
        ∂lg21NormalizedRestriction scoreLaw
          {score | E.reportDecision base score = false}) :
    ¬ 0 < scoreLaw {score | E.reportDecision base score = false} := by
  apply lg21_optional_no_positive_mass_nonreport_of_literal_conditional_mean
    scoreLaw (E.reportDecision base) hnoReportMeasurable
    (E.reportedPayoff base) (E.noReportPayoff base)
  · exact noProfitableBinaryChoiceDeviationAE_of_pointwise
      (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base)
  · exact hstrict
  · exact hintegrable
  · exact hcalibrated

end

end LG21TestOptionalPolicies

import LG21TestOptionalPolicies.MainTheorems

/-!
# Theorem 3.1 Source-Equilibrium Bridges

Small source-equilibrium constructors for the hidden-access strategic
withholding theorem.  These keep the final theorem work out of the very large
`MainTheorems.lean` file while reusing its closed mixture/cutoff endpoints.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability

/--
Optional-reporting Theorem 3.1 source-equilibrium bridge.  The closed
no-report-mixture fixed-point theorem supplies a cutoff witness; this theorem
turns that witness into the concrete base-indexed Definition 1 source
equilibrium by choosing exactly when the reported-score payoff weakly dominates
the no-report mixture payoff.

This closes the optional-reporting "there is such an equilibrium threshold"
step at the source-model level.  The remaining inputs are the paper's strict
mixture bound `accessFraction < 1` and the abstract estimation-consistency
proposition used by `LG21SourceEquilibriumData`.
-/
theorem paper_theorem3_1_optional_reporting_source_equilibrium_of_no_report_mixture
    {Feature Base Skill : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        ∃ reportDecision : Base → ℝ → Bool,
        let reportedEstimate : Base → ℝ → ℝ := fun base score =>
          (M base).posteriorMean (Function.update (theta base) k score)
        let noReportEstimate : Base → ℝ := fun base =>
          lg21OptionalNoReportMixtureEstimate
            (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
            (fun cutoff : ℝ =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
            (reportCutoff base)
        lg21SourceEquilibrium
          (lg21OptionalReportingBaseSourceEquilibriumData
            (Skill := Skill)
            (fun _skill : Skill => fun _base : Base => true)
            reportDecision reportedEstimate noReportEstimate
            estimationConsistent) ∧
          (∀ base,
            noReportEstimate base = reportedEstimate base (reportCutoff base)) ∧
            (∀ base score,
              reportDecision base score = true ↔
                noReportEstimate base ≤ reportedEstimate base score) ∧
              (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                (∀ base, ∃ score, reportDecision base score = true) ∧
                  (∀ base, ∃ score, reportDecision base score = false) ∧
                    (∀ base, ∃ cutoff : ℝ,
                      ∀ score : ℝ,
                        reportDecision base score = true ↔ cutoff ≤ score) := by
  rcases
      paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture
        M theta k accessFraction baseOnlyEstimate scoreLaw hC_nonneg
        hC_lt_one with
    ⟨W, reportCutoff, hindiff, hreports, htakes, hthreshold⟩
  classical
  let reportedEstimate : Base → ℝ → ℝ := fun base score =>
    (M base).posteriorMean (Function.update (theta base) k score)
  let noReportEstimate : Base → ℝ := fun base =>
    lg21OptionalNoReportMixtureEstimate
      (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
      (fun cutoff : ℝ =>
        (M base).posteriorMean
          (Function.update (theta base) k
            (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
      (reportCutoff base)
  let reportDecision : Base → ℝ → Bool := fun base score =>
    if W.reports base score then true else false
  refine ⟨W, reportCutoff, reportDecision, ?_⟩
  have hdecision_iff_report :
      ∀ base score, reportDecision base score = true ↔ W.reports base score := by
    intro base score
    dsimp [reportDecision]
    by_cases h : W.reports base score
    · simp [h]
    · simp [h]
  have hdecision_payoff :
      ∀ base score,
        reportDecision base score = true ↔
          noReportEstimate base ≤ reportedEstimate base score := by
    intro base score
    exact (hdecision_iff_report base score).trans (hreports base score)
  have hbest :
      ∀ base,
        lg21NoProfitableBinaryChoiceDeviation
          (fun score : ℝ => reportDecision base score = true)
          (reportedEstimate base) (fun _score : ℝ => noReportEstimate base) := by
    intro base
    exact
      AppliedModelingLib.noProfitableBinaryChoiceDeviation_of_choice_iff_payoff_le
        (fun score => hdecision_payoff base score)
  have hEq :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          (Skill := Skill)
          (fun _skill : Skill => fun _base : Base => true)
          reportDecision reportedEstimate noReportEstimate
          estimationConsistent) :=
    lg21SourceEquilibrium_of_base_optional_reporting_all_take_binary_choice
      (Skill := Skill) reportDecision reportedEstimate noReportEstimate
      estimationConsistent hbest hconsistent
  have hreport_each :
      ∀ base, ∃ score, reportDecision base score = true := by
    intro base
    rcases
        paper_theorem3_1_optional_reporting_report_at_each_base_of_source_witness
          W base with
      ⟨score, hscore⟩
    exact ⟨score, (hdecision_iff_report base score).2 hscore⟩
  have hnoreport_each :
      ∀ base, ∃ score, reportDecision base score = false := by
    intro base
    rcases
        paper_theorem3_1_optional_reporting_no_report_at_each_base_of_source_witness
          W base with
      ⟨score, hscore⟩
    refine ⟨score, ?_⟩
    cases hdec : reportDecision base score
    · rfl
    · exact False.elim (hscore ((hdecision_iff_report base score).1 hdec))
  have hdecision_threshold :
      ∀ base, ∃ cutoff : ℝ,
        ∀ score : ℝ, reportDecision base score = true ↔ cutoff ≤ score := by
    intro base
    rcases hthreshold base with ⟨cutoff, hcutoff⟩
    refine ⟨cutoff, ?_⟩
    intro score
    exact (hdecision_iff_report base score).trans (hcutoff score)
  exact
    ⟨hEq, hindiff, hdecision_payoff,
      htakes, hreport_each, hnoreport_each,
      hdecision_threshold⟩

/--
Optional-reporting Theorem 3.1 source-equilibrium bridge in the paper's
Bayesian-optimal threshold notation.  This is the same source-equilibrium
construction as `paper_theorem3_1_optional_reporting_source_equilibrium_of_no_report_mixture`,
but the reported and no-report estimates are written through an abstract `PBO`
identified with the Gaussian posterior mean, and the reporting decision is
exposed as a `PBO` threshold rule.
-/
theorem paper_theorem3_1_optional_reporting_pbo_threshold_source_equilibrium_of_no_report_mixture
    {Feature Base Skill : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        ∃ pboThreshold : Base → ℝ,
          ∃ reportDecision : Base → ℝ → Bool,
            let reportedEstimate : Base → ℝ → ℝ := fun base score =>
              PBO base (Function.update (theta base) k score)
            let noReportEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                (fun cutoff : ℝ =>
                  PBO base
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                (reportCutoff base)
            lg21SourceEquilibrium
              (lg21OptionalReportingBaseSourceEquilibriumData
                (Skill := Skill)
                (fun _skill : Skill => fun _base : Base => true)
                reportDecision reportedEstimate noReportEstimate
                estimationConsistent) ∧
              (∀ base, pboThreshold base = noReportEstimate base) ∧
                (∀ base score,
                  reportDecision base score = true ↔
                    pboThreshold base ≤
                      PBO base (Function.update (theta base) k score)) ∧
                  (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                    (∀ base, ∃ score, reportDecision base score = true) ∧
                      (∀ base, ∃ score, reportDecision base score = false) ∧
                        (∀ base, ∃ cutoff : ℝ,
                          ∀ score : ℝ,
                            reportDecision base score = true ↔ cutoff ≤ score) := by
  rcases
      paper_theorem3_1_optional_reporting_source_equilibrium_of_no_report_mixture
        (Skill := Skill) M theta k accessFraction baseOnlyEstimate scoreLaw
        hC_nonneg hC_lt_one estimationConsistent hconsistent with
    ⟨W, reportCutoff, reportDecision, hEq, hindiff, hdecision,
      htakes, hreport_each, hnoreport_each, hthreshold⟩
  let pboThreshold : Base → ℝ := fun base =>
    lg21OptionalNoReportMixtureEstimate
      (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
      (fun cutoff : ℝ =>
        PBO base
          (Function.update (theta base) k
            (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
      (reportCutoff base)
  refine ⟨W, reportCutoff, pboThreshold, reportDecision, ?_⟩
  have hEqPBO :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          (Skill := Skill)
          (fun _skill : Skill => fun _base : Base => true)
          reportDecision
          (fun base score => PBO base (Function.update (theta base) k score))
          (fun base =>
            lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
              (fun cutoff : ℝ =>
                PBO base
                  (Function.update (theta base) k
                    (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
              (reportCutoff base))
          estimationConsistent) := by
    simpa [hPBO] using hEq
  have hthresholdPBO :
      ∀ base score,
        reportDecision base score = true ↔
          pboThreshold base ≤ PBO base (Function.update (theta base) k score) := by
    intro base score
    simpa [pboThreshold, hPBO] using hdecision base score
  exact
    ⟨hEqPBO, (fun base => rfl), hthresholdPBO, htakes,
      hreport_each, hnoreport_each, hthreshold⟩

/--
Optional-reporting Theorem 3.1 source-equilibrium bridge with the access
fraction instantiated as a finite PMF event share.  Positive complement mass at
each base profile supplies the strict mixture bound `C < 1`.
-/
theorem paper_theorem3_1_optional_reporting_source_equilibrium_of_event_share_no_report_mixture
    {Feature Base Skill Student : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Student] [DecidableEq Student] [Nonempty Base]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        ∃ reportDecision : Base → ℝ → Bool,
        let accessFraction : Base → ℝ := fun base =>
          ((@lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
        let reportedEstimate : Base → ℝ → ℝ := fun base score =>
          (M base).posteriorMean (Function.update (theta base) k score)
        let noReportEstimate : Base → ℝ := fun base =>
          lg21OptionalNoReportMixtureEstimate
            (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
            (fun cutoff : ℝ =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
            (reportCutoff base)
        lg21SourceEquilibrium
          (lg21OptionalReportingBaseSourceEquilibriumData
            (Skill := Skill)
            (fun _skill : Skill => fun _base : Base => true)
            reportDecision reportedEstimate noReportEstimate
            estimationConsistent) ∧
          (∀ base,
            noReportEstimate base = reportedEstimate base
              (reportCutoff base)) ∧
            (∀ base score,
              reportDecision base score = true ↔
                noReportEstimate base ≤ reportedEstimate base score) ∧
              (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                (∀ base, ∃ score, reportDecision base score = true) ∧
                  (∀ base, ∃ score, reportDecision base score = false) ∧
                    (∀ base, ∃ cutoff : ℝ,
                      ∀ score : ℝ,
                        reportDecision base score = true ↔ cutoff ≤ score) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_optional_reporting_source_equilibrium_of_no_report_mixture
      (Skill := Skill) M theta k accessFraction baseOnlyEstimate scoreLaw
      hC_nonneg hC_lt_one estimationConsistent hconsistent)

/--
Optional-reporting Theorem 3.1 finite-event-share source-equilibrium bridge in
the paper's Bayesian-optimal threshold notation.
-/
theorem paper_theorem3_1_optional_reporting_pbo_threshold_source_equilibrium_of_event_share_no_report_mixture
    {Feature Base Skill Student : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Student] [DecidableEq Student] [Nonempty Base]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        ∃ pboThreshold : Base → ℝ,
          ∃ reportDecision : Base → ℝ → Bool,
            let accessFraction : Base → ℝ := fun base =>
              ((@lg21PMFEventShare Student _ _ (studentLaw base)
                (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
            let reportedEstimate : Base → ℝ → ℝ := fun base score =>
              PBO base (Function.update (theta base) k score)
            let noReportEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                (fun cutoff : ℝ =>
                  PBO base
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                (reportCutoff base)
            lg21SourceEquilibrium
              (lg21OptionalReportingBaseSourceEquilibriumData
                (Skill := Skill)
                (fun _skill : Skill => fun _base : Base => true)
                reportDecision reportedEstimate noReportEstimate
                estimationConsistent) ∧
              (∀ base, pboThreshold base = noReportEstimate base) ∧
                (∀ base score,
                  reportDecision base score = true ↔
                    pboThreshold base ≤
                      PBO base (Function.update (theta base) k score)) ∧
                  (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                    (∀ base, ∃ score, reportDecision base score = true) ∧
                      (∀ base, ∃ score, reportDecision base score = false) ∧
                        (∀ base, ∃ cutoff : ℝ,
                          ∀ score : ℝ,
                            reportDecision base score = true ↔ cutoff ≤ score) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_optional_reporting_pbo_threshold_source_equilibrium_of_no_report_mixture
      (Skill := Skill) PBO M theta k hPBO accessFraction baseOnlyEstimate
      scoreLaw hC_nonneg hC_lt_one estimationConsistent hconsistent)

/--
Optional-reporting Theorem 3.1 Section 3 source-equilibrium endpoint with the
concrete source-shaped Gaussian posterior law surface.  This bundles the
hidden-access information-set claim, the Definition 1 source equilibrium
obtained from the no-report mixture fixed point, and the failures of latent,
observable, and demographic fairness for the base/skill-mixture law surface.
-/
theorem paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_no_report_mixture
    {Feature Base : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
        ∃ reportCutoff : Base → ℝ,
          ∃ reportDecision : Base → ℝ → Bool,
          let reportedEstimate : Base → ℝ → ℝ := fun base score =>
            (M base).posteriorMean (Function.update (theta base) k score)
          let noReportEstimate : Base → ℝ := fun base =>
            lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
              (fun cutoff : ℝ =>
                (M base).posteriorMean
                  (Function.update (theta base) k
                    (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
              (reportCutoff base)
          lg21SourceEquilibrium
            (lg21OptionalReportingBaseSourceEquilibriumData
              (Skill := ℝ)
              (fun _skill : ℝ => fun _base : Base => true)
              reportDecision reportedEstimate noReportEstimate
              estimationConsistent) ∧
            (∀ base,
              noReportEstimate base = reportedEstimate base (reportCutoff base)) ∧
              (∀ base score,
                reportDecision base score = true ↔
                  noReportEstimate base ≤ reportedEstimate base score) ∧
                (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                  (∀ base, ∃ score, reportDecision base score = true) ∧
                    (∀ base, ∃ score, reportDecision base score = false) ∧
                      (∀ base, ∃ cutoff : ℝ,
                        ∀ score : ℝ,
                          reportDecision base score = true ↔ cutoff ≤ score) ∧
                        ¬ lg21SourceLawLatentSkillFair
                          (lg21BaseMixedGaussianPosteriorLawSurface
                            skillGivenBase baseProfile M theta k scoreLaw
                            baseOnlyEstimate) ∧
                          ¬ lg21SourceLawObservablyFair
                            (lg21BaseMixedGaussianPosteriorLawSurface
                              skillGivenBase baseProfile M theta k scoreLaw
                              baseOnlyEstimate) ∧
                            ¬ lg21SourceLawDemographicallyFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                skillGivenBase baseProfile M theta k scoreLaw
                                baseOnlyEstimate) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · rcases
        paper_theorem3_1_optional_reporting_source_equilibrium_of_no_report_mixture
          (Skill := ℝ) M theta k accessFraction baseOnlyEstimate scoreLaw
          hC_nonneg hC_lt_one estimationConsistent hconsistent with
      ⟨W, reportCutoff, reportDecision, hsource⟩
    have hfair :=
      paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_fair
        skillGivenBase baseProfile
        (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
        (fun base => (M base).centeredFamily.signalWeight k)
        (fun base => (scoreLaw base).scale)
        baseOnlyEstimate
        (fun base => (M base).centeredFamily.signalWeight_pos k)
        (fun base => (scoreLaw base).scale_pos)
    exact
      ⟨W, reportCutoff, reportDecision,
        hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2.1,
        hsource.2.2.2.2.1, hsource.2.2.2.2.2.1,
        hsource.2.2.2.2.2.2, hfair.1, hfair.2.1, hfair.2.2⟩

/--
Optional-reporting Theorem 3.1 Section 3 source-equilibrium endpoint with the
access fraction instantiated as a finite event share.  This is the concrete
finite-cohort version of the no-report-mixture source-equilibrium/law-unfairness
bridge.
-/
theorem paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_event_share_no_report_mixture
    {Feature Base Student : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Student] [DecidableEq Student] [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
        ∃ reportCutoff : Base → ℝ,
          ∃ reportDecision : Base → ℝ → Bool,
          let accessFraction : Base → ℝ := fun base =>
            ((@lg21PMFEventShare Student _ _ (studentLaw base)
              (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
          let reportedEstimate : Base → ℝ → ℝ := fun base score =>
            (M base).posteriorMean (Function.update (theta base) k score)
          let noReportEstimate : Base → ℝ := fun base =>
            lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
              (fun cutoff : ℝ =>
                (M base).posteriorMean
                  (Function.update (theta base) k
                    (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
              (reportCutoff base)
          lg21SourceEquilibrium
            (lg21OptionalReportingBaseSourceEquilibriumData
              (Skill := ℝ)
              (fun _skill : ℝ => fun _base : Base => true)
              reportDecision reportedEstimate noReportEstimate
              estimationConsistent) ∧
            (∀ base,
              noReportEstimate base = reportedEstimate base
                (reportCutoff base)) ∧
              (∀ base score,
                reportDecision base score = true ↔
                  noReportEstimate base ≤ reportedEstimate base score) ∧
                (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                  (∀ base, ∃ score, reportDecision base score = true) ∧
                    (∀ base, ∃ score, reportDecision base score = false) ∧
                      (∀ base, ∃ cutoff : ℝ,
                        ∀ score : ℝ,
                          reportDecision base score = true ↔
                            cutoff ≤ score) ∧
                        ¬ lg21SourceLawLatentSkillFair
                          (lg21BaseMixedGaussianPosteriorLawSurface
                            skillGivenBase baseProfile M theta k scoreLaw
                            baseOnlyEstimate) ∧
                          ¬ lg21SourceLawObservablyFair
                            (lg21BaseMixedGaussianPosteriorLawSurface
                              skillGivenBase baseProfile M theta k scoreLaw
                              baseOnlyEstimate) ∧
                            ¬ lg21SourceLawDemographicallyFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                skillGivenBase baseProfile M theta k scoreLaw
                                baseOnlyEstimate) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_no_report_mixture
      skillGivenBase baseProfile M theta k accessFraction baseOnlyEstimate
      scoreLaw hC_nonneg hC_lt_one estimationConsistent hconsistent)

/--
Optional-reporting Theorem 3.1 Section 3 endpoint in Gaussian `P_BO`
threshold notation.  This is the paper-facing version of the no-report-mixture
source-equilibrium/law-unfairness bridge with the reporting cutoff written as a
Bayesian-optimal posterior threshold.
-/
theorem paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_no_report_mixture
    {Feature Base : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
        ∃ reportCutoff : Base → ℝ,
          ∃ pboThreshold : Base → ℝ,
            ∃ reportDecision : Base → ℝ → Bool,
            let reportedEstimate : Base → ℝ → ℝ := fun base score =>
              PBO base (Function.update (theta base) k score)
            let noReportEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                (fun cutoff : ℝ =>
                  PBO base
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                (reportCutoff base)
            lg21SourceEquilibrium
              (lg21OptionalReportingBaseSourceEquilibriumData
                (Skill := ℝ)
                (fun _skill : ℝ => fun _base : Base => true)
                reportDecision reportedEstimate noReportEstimate
                estimationConsistent) ∧
              (∀ base, pboThreshold base = noReportEstimate base) ∧
                (∀ base score,
                  reportDecision base score = true ↔
                    pboThreshold base ≤
                      PBO base (Function.update (theta base) k score)) ∧
                  (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                    (∀ base, ∃ score, reportDecision base score = true) ∧
                      (∀ base, ∃ score, reportDecision base score = false) ∧
                        (∀ base, ∃ cutoff : ℝ,
                          ∀ score : ℝ,
                            reportDecision base score = true ↔ cutoff ≤ score) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedGaussianPosteriorLawSurface
                              skillGivenBase baseProfile M theta k scoreLaw
                              baseOnlyEstimate) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                skillGivenBase baseProfile M theta k scoreLaw
                                baseOnlyEstimate) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedGaussianPosteriorLawSurface
                                  skillGivenBase baseProfile M theta k scoreLaw
                                  baseOnlyEstimate) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · rcases
        paper_theorem3_1_optional_reporting_pbo_threshold_source_equilibrium_of_no_report_mixture
          (Skill := ℝ) PBO M theta k hPBO accessFraction baseOnlyEstimate
          scoreLaw hC_nonneg hC_lt_one estimationConsistent hconsistent with
      ⟨W, reportCutoff, pboThreshold, reportDecision, hsource⟩
    have hfair :=
      paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_fair
        skillGivenBase baseProfile
        (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
        (fun base => (M base).centeredFamily.signalWeight k)
        (fun base => (scoreLaw base).scale)
        baseOnlyEstimate
        (fun base => (M base).centeredFamily.signalWeight_pos k)
        (fun base => (scoreLaw base).scale_pos)
    exact
      ⟨W, reportCutoff, pboThreshold, reportDecision,
        hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2.1,
        hsource.2.2.2.2.1, hsource.2.2.2.2.2.1,
        hsource.2.2.2.2.2.2, hfair.1, hfair.2.1, hfair.2.2⟩

/--
Optional-reporting Theorem 3.1 Section 3 finite-event-share endpoint in
Gaussian `P_BO` threshold notation.
-/
theorem paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_event_share_no_report_mixture
    {Feature Base Student : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Student] [DecidableEq Student] [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
        ∃ reportCutoff : Base → ℝ,
          ∃ pboThreshold : Base → ℝ,
            ∃ reportDecision : Base → ℝ → Bool,
            let accessFraction : Base → ℝ := fun base =>
              ((@lg21PMFEventShare Student _ _ (studentLaw base)
                (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
            let reportedEstimate : Base → ℝ → ℝ := fun base score =>
              PBO base (Function.update (theta base) k score)
            let noReportEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                (fun cutoff : ℝ =>
                  PBO base
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                (reportCutoff base)
            lg21SourceEquilibrium
              (lg21OptionalReportingBaseSourceEquilibriumData
                (Skill := ℝ)
                (fun _skill : ℝ => fun _base : Base => true)
                reportDecision reportedEstimate noReportEstimate
                estimationConsistent) ∧
              (∀ base, pboThreshold base = noReportEstimate base) ∧
                (∀ base score,
                  reportDecision base score = true ↔
                    pboThreshold base ≤
                      PBO base (Function.update (theta base) k score)) ∧
                  (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                    (∀ base, ∃ score, reportDecision base score = true) ∧
                      (∀ base, ∃ score, reportDecision base score = false) ∧
                        (∀ base, ∃ cutoff : ℝ,
                          ∀ score : ℝ,
                            reportDecision base score = true ↔ cutoff ≤ score) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedGaussianPosteriorLawSurface
                              skillGivenBase baseProfile M theta k scoreLaw
                              baseOnlyEstimate) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                skillGivenBase baseProfile M theta k scoreLaw
                                baseOnlyEstimate) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedGaussianPosteriorLawSurface
                                  skillGivenBase baseProfile M theta k scoreLaw
                                  baseOnlyEstimate) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_no_report_mixture
      skillGivenBase baseProfile PBO M theta k hPBO accessFraction
      baseOnlyEstimate scoreLaw hC_nonneg hC_lt_one
      estimationConsistent hconsistent)

/--
Every-equilibrium optional-reporting Theorem 3.1 source-equilibrium/law
unfairness endpoint in Gaussian `P_BO` threshold notation.
-/
theorem paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_for_every_equilibrium_of_no_report_mixture
    {Feature Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (accessFraction baseOnlyEstimate : Equilibrium → Base → ℝ)
    (scoreLaw : Equilibrium → Base → GaussianScaleLaw)
    (hC_nonneg : ∀ e base, 0 ≤ accessFraction e base)
    (hC_lt_one : ∀ e base, accessFraction e base < 1)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
          ∃ reportCutoff : Base → ℝ,
            ∃ pboThreshold : Base → ℝ,
              ∃ reportDecision : Base → ℝ → Bool,
              let reportedEstimate : Base → ℝ → ℝ := fun base score =>
                PBO base (Function.update (theta base) k score)
              let noReportEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction e base) (baseOnlyEstimate e base)
                  (scoreLaw e base)
                  (fun cutoff : ℝ =>
                    PBO base
                      (Function.update (theta base) k
                        (standardGaussianLowerTailMean
                          (scoreLaw e base) cutoff)))
                  (reportCutoff base)
              lg21SourceEquilibrium
                (lg21OptionalReportingBaseSourceEquilibriumData
                  (Skill := ℝ)
                  (fun _skill : ℝ => fun _base : Base => true)
                  reportDecision reportedEstimate noReportEstimate
                  (estimationConsistent e)) ∧
                (∀ base, pboThreshold base = noReportEstimate base) ∧
                  (∀ base score,
                    reportDecision base score = true ↔
                      pboThreshold base ≤
                        PBO base (Function.update (theta base) k score)) ∧
                    (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                      (∀ base, ∃ score, reportDecision base score = true) ∧
                        (∀ base, ∃ score, reportDecision base score = false) ∧
                          (∀ base, ∃ cutoff : ℝ,
                            ∀ score : ℝ,
                              reportDecision base score = true ↔
                                cutoff ≤ score) ∧
                            ¬ lg21SourceLawLatentSkillFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e) M theta k
                                (scoreLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawObservablyFair
                                (lg21BaseMixedGaussianPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e) M theta k
                                  (scoreLaw e) (baseOnlyEstimate e)) ∧
                                ¬ lg21SourceLawDemographicallyFair
                                  (lg21BaseMixedGaussianPosteriorLawSurface
                                    (skillGivenBase e) (baseProfile e) M theta k
                                    (scoreLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_no_report_mixture
        (skillGivenBase e) (baseProfile e) PBO M theta k hPBO
        (accessFraction e) (baseOnlyEstimate e) (scoreLaw e)
        (hC_nonneg e) (hC_lt_one e) (estimationConsistent e)
        (hconsistent e)).2

/--
Every-equilibrium optional-reporting Theorem 3.1 finite-event-share
source-equilibrium/law-unfairness endpoint in Gaussian `P_BO` threshold
notation.
-/
theorem paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_for_every_equilibrium_of_event_share_no_report_mixture
    {Feature Base Student Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Student] [DecidableEq Student] [Nonempty Base]
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (studentLaw : Equilibrium → Base → PMF Student)
    (accessEvent : Equilibrium → Base → Student → Prop)
    (decAccessEvent : ∀ e base, DecidablePred (accessEvent e base))
    (hnoAccessMass :
      ∀ e base, ∃ student, ¬ accessEvent e base student ∧
        0 < (studentLaw e base student).toReal)
    (baseOnlyEstimate : Equilibrium → Base → ℝ)
    (scoreLaw : Equilibrium → Base → GaussianScaleLaw)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
          ∃ reportCutoff : Base → ℝ,
            ∃ pboThreshold : Base → ℝ,
              ∃ reportDecision : Base → ℝ → Bool,
              let accessFraction : Base → ℝ := fun base =>
                ((@lg21PMFEventShare Student _ _ (studentLaw e base)
                  (accessEvent e base) (decAccessEvent e base) : NNReal) : ℝ)
              let reportedEstimate : Base → ℝ → ℝ := fun base score =>
                PBO base (Function.update (theta base) k score)
              let noReportEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate e base)
                  (scoreLaw e base)
                  (fun cutoff : ℝ =>
                    PBO base
                      (Function.update (theta base) k
                        (standardGaussianLowerTailMean
                          (scoreLaw e base) cutoff)))
                  (reportCutoff base)
              lg21SourceEquilibrium
                (lg21OptionalReportingBaseSourceEquilibriumData
                  (Skill := ℝ)
                  (fun _skill : ℝ => fun _base : Base => true)
                  reportDecision reportedEstimate noReportEstimate
                  (estimationConsistent e)) ∧
                (∀ base, pboThreshold base = noReportEstimate base) ∧
                  (∀ base score,
                    reportDecision base score = true ↔
                      pboThreshold base ≤
                        PBO base (Function.update (theta base) k score)) ∧
                    (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                      (∀ base, ∃ score, reportDecision base score = true) ∧
                        (∀ base, ∃ score, reportDecision base score = false) ∧
                          (∀ base, ∃ cutoff : ℝ,
                            ∀ score : ℝ,
                              reportDecision base score = true ↔
                                cutoff ≤ score) ∧
                            ¬ lg21SourceLawLatentSkillFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e) M theta k
                                (scoreLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawObservablyFair
                                (lg21BaseMixedGaussianPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e) M theta k
                                  (scoreLaw e) (baseOnlyEstimate e)) ∧
                                ¬ lg21SourceLawDemographicallyFair
                                  (lg21BaseMixedGaussianPosteriorLawSurface
                                    (skillGivenBase e) (baseProfile e) M theta k
                                    (scoreLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_optional_reporting_pbo_threshold_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_event_share_no_report_mixture
        (skillGivenBase e) (baseProfile e) PBO M theta k hPBO
        (studentLaw e) (accessEvent e) (decAccessEvent e) (hnoAccessMass e)
        (baseOnlyEstimate e) (scoreLaw e) (estimationConsistent e)
        (hconsistent e)).2

/--
Every-equilibrium optional-reporting Theorem 3.1 source-equilibrium endpoint.
This is the paper-facing indexed form of the single-equilibrium bridge above:
for each equilibrium index, the no-report-mixture fixed point yields a
Definition 1 source equilibrium, nontrivial threshold reporting, and failure of
all three fairness definitions on the corresponding Gaussian posterior law
surface.
-/
theorem paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_for_every_equilibrium_of_no_report_mixture
    {Feature Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Equilibrium → Base → ℝ)
    (scoreLaw : Equilibrium → Base → GaussianScaleLaw)
    (hC_nonneg : ∀ e base, 0 ≤ accessFraction e base)
    (hC_lt_one : ∀ e base, accessFraction e base < 1)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
          ∃ reportCutoff : Base → ℝ,
            ∃ reportDecision : Base → ℝ → Bool,
            let reportedEstimate : Base → ℝ → ℝ := fun base score =>
              (M base).posteriorMean (Function.update (theta base) k score)
            let noReportEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction e base) (baseOnlyEstimate e base)
                (scoreLaw e base)
                (fun cutoff : ℝ =>
                  (M base).posteriorMean
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean
                        (scoreLaw e base) cutoff)))
                (reportCutoff base)
            lg21SourceEquilibrium
              (lg21OptionalReportingBaseSourceEquilibriumData
                (Skill := ℝ)
                (fun _skill : ℝ => fun _base : Base => true)
                reportDecision reportedEstimate noReportEstimate
                (estimationConsistent e)) ∧
              (∀ base,
                noReportEstimate base = reportedEstimate base
                  (reportCutoff base)) ∧
                (∀ base score,
                  reportDecision base score = true ↔
                    noReportEstimate base ≤ reportedEstimate base score) ∧
                  (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                    (∀ base, ∃ score, reportDecision base score = true) ∧
                      (∀ base, ∃ score, reportDecision base score = false) ∧
                        (∀ base, ∃ cutoff : ℝ,
                          ∀ score : ℝ,
                            reportDecision base score = true ↔
                              cutoff ≤ score) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedGaussianPosteriorLawSurface
                              (skillGivenBase e) (baseProfile e) M theta k
                              (scoreLaw e) (baseOnlyEstimate e)) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e) M theta k
                                (scoreLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedGaussianPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e) M theta k
                                  (scoreLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_no_report_mixture
        (skillGivenBase e) (baseProfile e) M theta k
        (accessFraction e) (baseOnlyEstimate e) (scoreLaw e)
        (hC_nonneg e) (hC_lt_one e) (estimationConsistent e)
        (hconsistent e)).2

/--
Every-equilibrium optional-reporting Theorem 3.1 source-equilibrium endpoint
with the access fraction instantiated as a finite event share at each
equilibrium/base profile.
-/
theorem paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_for_every_equilibrium_of_event_share_no_report_mixture
    {Feature Base Student Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Student] [DecidableEq Student] [Nonempty Base]
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (studentLaw : Equilibrium → Base → PMF Student)
    (accessEvent : Equilibrium → Base → Student → Prop)
    (decAccessEvent : ∀ e base, DecidablePred (accessEvent e base))
    (hnoAccessMass :
      ∀ e base, ∃ student, ¬ accessEvent e base student ∧
        0 < (studentLaw e base student).toReal)
    (baseOnlyEstimate : Equilibrium → Base → ℝ)
    (scoreLaw : Equilibrium → Base → GaussianScaleLaw)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
          ∃ reportCutoff : Base → ℝ,
            ∃ reportDecision : Base → ℝ → Bool,
            let accessFraction : Base → ℝ := fun base =>
              ((@lg21PMFEventShare Student _ _ (studentLaw e base)
                (accessEvent e base) (decAccessEvent e base) : NNReal) : ℝ)
            let reportedEstimate : Base → ℝ → ℝ := fun base score =>
              (M base).posteriorMean (Function.update (theta base) k score)
            let noReportEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate e base)
                (scoreLaw e base)
                (fun cutoff : ℝ =>
                  (M base).posteriorMean
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean
                        (scoreLaw e base) cutoff)))
                (reportCutoff base)
            lg21SourceEquilibrium
              (lg21OptionalReportingBaseSourceEquilibriumData
                (Skill := ℝ)
                (fun _skill : ℝ => fun _base : Base => true)
                reportDecision reportedEstimate noReportEstimate
                (estimationConsistent e)) ∧
              (∀ base,
                noReportEstimate base = reportedEstimate base
                  (reportCutoff base)) ∧
                (∀ base score,
                  reportDecision base score = true ↔
                    noReportEstimate base ≤ reportedEstimate base score) ∧
                  (∀ (base : Base) (skill : ℝ), W.takes base skill) ∧
                    (∀ base, ∃ score, reportDecision base score = true) ∧
                      (∀ base, ∃ score, reportDecision base score = false) ∧
                        (∀ base, ∃ cutoff : ℝ,
                          ∀ score : ℝ,
                            reportDecision base score = true ↔
                              cutoff ≤ score) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedGaussianPosteriorLawSurface
                              (skillGivenBase e) (baseProfile e) M theta k
                              (scoreLaw e) (baseOnlyEstimate e)) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedGaussianPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e) M theta k
                                (scoreLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedGaussianPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e) M theta k
                                  (scoreLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_optional_reporting_source_equilibrium_and_base_mixed_gaussian_posterior_law_unfair_of_event_share_no_report_mixture
        (skillGivenBase e) (baseProfile e) M theta k (studentLaw e)
        (accessEvent e) (decAccessEvent e) (hnoAccessMass e)
        (baseOnlyEstimate e) (scoreLaw e) (estimationConsistent e)
        (hconsistent e)).2

end

end LG21TestOptionalPolicies

import LG21TestOptionalPolicies.ObservedAccessReportRequiredSelectedGaussianClosure
import LG21TestOptionalPolicies.ReportRequiredFullPublicPositiveMassUnraveling
import AppliedModelingLib.Foundations.Probability.GaussianSignalKernelRCD

/-!
# Base-mass promotion for observed-access report-required testing

These lemmas retain the base marginal when lifting a fixed-base result.  They
make no claim that global positive reporter mass gives reporter mass at every
base fibre.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib Probability
open scoped ENNReal ProbabilityTheory

/-- A positive global report-required no-take event has a positive-mass set
of base fibres with positive conditional no-take mass. -/
theorem lg21_reportRequired_positive_noTake_mass_has_positive_baseFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (hpositive : 0 < (baseLaw ⊗ₘ skillKernel)
      (lg21ReportRequiredFullPublicNoTakeSet take)) :
    0 < baseLaw (Function.support
      (selectionMass skillKernel (lg21ReportRequiredFullPublicNoTakeSet take))) := by
  let event : Set (Base × ℝ) := lg21ReportRequiredFullPublicNoTakeSet take
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21ReportRequiredFullPublicNoTakeSet_measurable take htake)
  have hmassMeasurable : Measurable (selectionMass skillKernel event) :=
    selectionMass_measurable hevent
  change 0 < (baseLaw ⊗ₘ skillKernel) event at hpositive
  rw [Measure.compProd_apply hevent] at hpositive
  exact (lintegral_pos_iff_support hmassMeasurable).mp hpositive

/-- A global positive no-take mass splits into the only two valid base-level
cases: positive no-take mass at reporter-positive fibres, or positive no-take
mass at reporter-zero fibres.  The second case must be handled by a separate
active-entry argument; it cannot be discharged using an on-path reporter PBO.
-/
theorem lg21_reportRequired_positive_noTake_mass_split_reporterFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (hpositive : 0 < (baseLaw ⊗ₘ skillKernel)
      (lg21ReportRequiredFullPublicNoTakeSet take)) :
    (0 < baseLaw
      (Function.support
        (selectionMass skillKernel (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        Function.support
          (selectionMass skillKernel (lg21ReportRequiredFullPublicTakeSet take)))) ∨
    (0 < baseLaw
      (Function.support
        (selectionMass skillKernel (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        {base | selectionMass skillKernel
          (lg21ReportRequiredFullPublicTakeSet take) base = 0})) := by
  let noTakeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicNoTakeSet take
  let takeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicTakeSet take
  let noTakeMass : Base → ℝ≥0∞ := selectionMass skillKernel noTakeEvent
  let takeMass : Base → ℝ≥0∞ := selectionMass skillKernel takeEvent
  have hnoTakePositive : 0 < baseLaw (Function.support noTakeMass) := by
    simpa [noTakeEvent, noTakeMass] using
      (lg21_reportRequired_positive_noTake_mass_has_positive_baseFibres
        baseLaw skillKernel take htake hpositive)
  by_cases hcoexist : 0 < baseLaw
      (Function.support noTakeMass ∩ Function.support takeMass)
  · exact Or.inl (by simpa [noTakeEvent, takeEvent, noTakeMass, takeMass] using hcoexist)
  · right
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hcoexistZero : baseLaw
        (Function.support noTakeMass ∩ Function.support takeMass) = 0 := by
      exact le_antisymm (not_lt.mp hcoexist) (zero_le _)
    have hpartition : Function.support noTakeMass =
        (Function.support noTakeMass ∩ Function.support takeMass) ∪
          (Function.support noTakeMass ∩ {base | takeMass base = 0}) := by
      ext base
      simp only [Function.mem_support, Set.mem_union, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · intro hnoTake
        by_cases htakeMass : takeMass base = 0
        · exact Or.inr ⟨hnoTake, htakeMass⟩
        · exact Or.inl ⟨hnoTake, htakeMass⟩
      · intro h
        exact h.elim (fun hleft => hleft.1) (fun hright => hright.1)
    have hnoTakeZero : baseLaw (Function.support noTakeMass) = 0 := by
      rw [hpartition]
      exact measure_union_null hcoexistZero hzero
    exact (ne_of_gt hnoTakePositive) hnoTakeZero

/-- An almost-everywhere identity under the selected base marginal transfers
to almost every original base with positive selected fibre mass.  This is the
correct scope for an on-path reporter PBO after base disintegration. -/
theorem lg21_reportRequired_ae_selectedBase_to_ae_positiveFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (event : Set (Base × ℝ)) (hevent : MeasurableSet event)
    {P : Base → Prop}
    (hP : ∀ᵐ base ∂normalizedSelectedBase baseLaw skillKernel event, P base) :
    ∀ᵐ base ∂baseLaw,
      selectionMass skillKernel event base ≠ 0 → P base := by
  have hnormalizer_ne_zero : ((baseLaw ⊗ₘ skillKernel) event)⁻¹ ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    exact measure_ne_top _ _
  rw [normalizedSelectedBase,
    Measure.ae_ennreal_smul_measure_iff hnormalizer_ne_zero] at hP
  exact (ae_withDensity_iff (selectionMass_measurable hevent)).mp hP

/-- Gaussian-location specialization of the no-take fibre split. -/
theorem lg21_reportRequired_gaussianLocation_positive_noTake_mass_split_reporterFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (hpositive : 0 < (baseLaw ⊗ₘ
      AppliedModelingLib.Probability.gaussianLocationKernel baseMean hbaseMean baseVariance)
      (lg21ReportRequiredFullPublicNoTakeSet take)) :
    (0 < baseLaw
      (Function.support
        (selectionMass
          (AppliedModelingLib.Probability.gaussianLocationKernel
            baseMean hbaseMean baseVariance)
          (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        Function.support
          (selectionMass
            (AppliedModelingLib.Probability.gaussianLocationKernel
              baseMean hbaseMean baseVariance)
            (lg21ReportRequiredFullPublicTakeSet take)))) ∨
    (0 < baseLaw
      (Function.support
        (selectionMass
          (AppliedModelingLib.Probability.gaussianLocationKernel
            baseMean hbaseMean baseVariance)
          (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        {base | selectionMass
          (AppliedModelingLib.Probability.gaussianLocationKernel
            baseMean hbaseMean baseVariance)
          (lg21ReportRequiredFullPublicTakeSet take) base = 0})) := by
  letI : IsMarkovKernel
      (AppliedModelingLib.Probability.gaussianLocationKernel
        baseMean hbaseMean baseVariance) :=
    AppliedModelingLib.Probability.gaussianLocationKernel_isMarkov
      baseMean hbaseMean baseVariance
  exact lg21_reportRequired_positive_noTake_mass_split_reporterFibres
    baseLaw
    (AppliedModelingLib.Probability.gaussianLocationKernel
      baseMean hbaseMean baseVariance)
    take htake hpositive

/-! ## Coexisting-fibre closure -/

/-- On a Gaussian base fibre, the global full-public taking event reduces to
the literal taking set for that fixed public base. -/
theorem lg21_reportRequired_gaussianLocation_take_selectionMass
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance : NNReal)
    (take : Base → ℝ → Bool) (base : Base) :
    selectionMass
      (AppliedModelingLib.Probability.gaussianLocationKernel
        baseMean hbaseMean priorVariance)
      (lg21ReportRequiredFullPublicTakeSet take) base =
      gaussianReal (baseMean base) priorVariance
        {skill | take base skill = true} := by
  rw [selectionMass,
    AppliedModelingLib.Probability.gaussianLocationKernel_apply]
  congr 1

/-- On a Gaussian base fibre, the global full-public no-take event reduces to
the literal no-take set for that fixed public base. -/
theorem lg21_reportRequired_gaussianLocation_noTake_selectionMass
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance : NNReal)
    (take : Base → ℝ → Bool) (base : Base) :
    selectionMass
      (AppliedModelingLib.Probability.gaussianLocationKernel
        baseMean hbaseMean priorVariance)
      (lg21ReportRequiredFullPublicNoTakeSet take) base =
      gaussianReal (baseMean base) priorVariance
        {skill | take base skill = false} := by
  rw [selectionMass,
    AppliedModelingLib.Probability.gaussianLocationKernel_apply]
  congr 1

/--
On all base fibres that have both reporters and no-takers, the literal
Gaussian source PBO equations force a contradiction.  The PBO equations are
assumed only almost everywhere under their respective *selected base laws*;
they are first transported to positive fibres and only then passed to the
fixed-base closure.

This intentionally proves only that coexistence fibres are null.  A positive
no-take population can still be concentrated on reporter-zero fibres, whose
PBO is off path and therefore needs the separate candidate-entry argument.
-/
theorem lg21_reportRequired_coexistingFibres_null_of_ae_selectedGaussianPBO
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (hbest : ∀ publicBase,
      NoProfitableBinaryChoiceDeviation
        (fun skill ↦ E.takeDecision skill publicBase = true)
        (fun skill ↦
          lg21ReportRequiredSequentialTakeExpectedPayoff E skill publicBase)
        (fun _skill ↦ E.noReportPayoff publicBase))
    (haction : Measurable (fun profileSkill : Base × ℝ =>
      E.takeDecision profileSkill.2 profileSkill.1))
    (htestLaw : ∀ skill base,
      E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal)
    (hreportedPBO : ∀ᵐ base ∂normalizedSelectedBase baseLaw
      (AppliedModelingLib.Probability.gaussianLocationKernel
        baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
      E.reportedPayoff base =ᵐ[
        normalizedSelectedBase
          (gaussianReal (baseMean base)
            (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel
            (baseMean base) priorVariance noiseVariance)
          (Set.univ ×ˢ {skill | E.takeDecision skill base = true})]
        fun score => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            (baseMean base) priorVariance noiseVariance score)
          {skill | E.takeDecision skill base = true})
    (hnoTakePBO : ∀ᵐ base ∂normalizedSelectedBase baseLaw
      (AppliedModelingLib.Probability.gaussianLocationKernel
        baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicNoTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
      E.noReportPayoff base = ∫ skill, skill ∂lg21NormalizedRestriction
        (gaussianReal (baseMean base) priorVariance.toNNReal)
        {skill | E.takeDecision skill base = false}) :
    baseLaw
      (Function.support
        (selectionMass
          (AppliedModelingLib.Probability.gaussianLocationKernel
            baseMean hbaseMean priorVariance.toNNReal)
          (lg21ReportRequiredFullPublicNoTakeSet
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase))) ∩
        Function.support
          (selectionMass
            (AppliedModelingLib.Probability.gaussianLocationKernel
              baseMean hbaseMean priorVariance.toNNReal)
            (lg21ReportRequiredFullPublicTakeSet
              (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)))) = 0 := by
  let skillKernel : Kernel Base ℝ :=
    AppliedModelingLib.Probability.gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := by
    dsimp [skillKernel]
    exact AppliedModelingLib.Probability.gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
  let take : Base → ℝ → Bool := fun publicBase latentSkill =>
    E.takeDecision latentSkill publicBase
  let takeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicTakeSet take
  let noTakeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicNoTakeSet take
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent, take] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take haction)
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent, take] using
      (lg21ReportRequiredFullPublicNoTakeSet_measurable take haction)
  have hreportedLocal : ∀ᵐ base ∂baseLaw,
      selectionMass skillKernel takeEvent base ≠ 0 →
        E.reportedPayoff base =ᵐ[
          normalizedSelectedBase
            (gaussianReal (baseMean base)
              (priorVariance + noiseVariance).toNNReal)
            (gaussianSignalPosteriorKernel
              (baseMean base) priorVariance noiseVariance)
            (Set.univ ×ˢ {skill | E.takeDecision skill base = true})]
          fun score => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
            (gaussianSignalPosteriorKernel
              (baseMean base) priorVariance noiseVariance score)
            {skill | E.takeDecision skill base = true} := by
    simpa [skillKernel, takeEvent, take] using
      (lg21_reportRequired_ae_selectedBase_to_ae_positiveFibres
        baseLaw skillKernel takeEvent htakeEvent hreportedPBO)
  have hnoTakeLocal : ∀ᵐ base ∂baseLaw,
      selectionMass skillKernel noTakeEvent base ≠ 0 →
        E.noReportPayoff base = ∫ skill, skill ∂lg21NormalizedRestriction
          (gaussianReal (baseMean base) priorVariance.toNNReal)
          {skill | E.takeDecision skill base = false} := by
    simpa [skillKernel, noTakeEvent, take] using
      (lg21_reportRequired_ae_selectedBase_to_ae_positiveFibres
        baseLaw skillKernel noTakeEvent hnoTakeEvent hnoTakePBO)
  have hnoCoexistAE : ∀ᵐ base ∂baseLaw,
      base ∉ Function.support (selectionMass skillKernel noTakeEvent) ∩
        Function.support (selectionMass skillKernel takeEvent) := by
    filter_upwards [hreportedLocal, hnoTakeLocal] with base hreported hnoTake
    intro hcoexist
    rw [Set.mem_inter_iff, Function.mem_support,
      Function.mem_support] at hcoexist
    have htakePositive : 0 < gaussianReal (baseMean base)
        priorVariance.toNNReal {skill | E.takeDecision skill base = true} := by
      rw [← lg21_reportRequired_gaussianLocation_take_selectionMass
        baseMean hbaseMean priorVariance.toNNReal take base]
      exact pos_iff_ne_zero.mpr hcoexist.2
    have hnoTakePositive : 0 < gaussianReal (baseMean base)
        priorVariance.toNNReal {skill | E.takeDecision skill base = false} := by
      rw [← lg21_reportRequired_gaussianLocation_noTake_selectionMass
        baseMean hbaseMean priorVariance.toNNReal take base]
      exact pos_iff_ne_zero.mpr hcoexist.1
    have htakeMeasurable : Measurable (E.takeDecision · base) := by
      simpa [Function.comp_def, take] using
        haction.comp (measurable_const.prodMk measurable_id)
    have himpossible :=
      lg21_observedAccess_reportRequired_selectedGaussianPBO_ae_no_positiveMass_noTake
        base (hbest base) (baseMean base) priorVariance noiseVariance
        hpriorVariance hnoiseVariance htakeMeasurable htakePositive
        (fun _ => hnoTake hcoexist.1) (hreported hcoexist.2)
        (fun skill => htestLaw skill base)
    exact himpossible hnoTakePositive
  have hnull : baseLaw
      (Function.support (selectionMass skillKernel noTakeEvent) ∩
        Function.support (selectionMass skillKernel takeEvent)) = 0 := by
    simpa only [ae_iff, not_not] using hnoCoexistAE
  simpa [skillKernel, takeEvent, noTakeEvent, take] using hnull

/-- Once coexistence fibres are closed, the global positive-mass split leaves
only reporter-zero fibres.  This is the exact handoff to active entry; no
off-path reported payoff is inferred here. -/
theorem lg21_reportRequired_positive_noTake_mass_forces_reporterZeroFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (hcoexistingFibresNull : baseLaw
      (Function.support
        (selectionMass skillKernel (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        Function.support
          (selectionMass skillKernel (lg21ReportRequiredFullPublicTakeSet take))) = 0)
    (hpositive : 0 < (baseLaw ⊗ₘ skillKernel)
      (lg21ReportRequiredFullPublicNoTakeSet take)) :
    0 < baseLaw
      (Function.support
        (selectionMass skillKernel (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        {base | selectionMass skillKernel
          (lg21ReportRequiredFullPublicTakeSet take) base = 0}) := by
  rcases lg21_reportRequired_positive_noTake_mass_split_reporterFibres
      baseLaw skillKernel take htake hpositive with hcoexist | hreporterZero
  · rw [hcoexistingFibresNull] at hcoexist
    exact False.elim (lt_irrefl _ hcoexist)
  · exact hreporterZero

end

end LG21TestOptionalPolicies

import LG21TestOptionalPolicies.OptionalSourceLocalRecalibratedEntry
import LG21TestOptionalPolicies.OptionalPartialReporterRecalibratedEntry
import LG21TestOptionalPolicies.OptionalFibrewisePositiveMassUnraveling
import LG21TestOptionalPolicies.OptionalAllNoReporterGlobalSource
import LG21TestOptionalPolicies.ContinuousObservedAccessSequentialActionBridge
import LG21TestOptionalPolicies.PositiveReporterStrictGain

/-!
# Literal observed-access optional-reporting closeout

This module keeps `X = 0` as the literal sequential action event until the
all-taking conclusion has been established.  It then reduces that event to the
post-score no-report event and applies the two-PBO/tower argument only on that
reduced carrier.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-- The complete observed public action event for sequential optional
reporting.  The latent skill coordinate determines the pre-score action. -/
def lg21OptionalSequentialFullPublicReportSet
    {Base : Type*} (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) :
    Set (Base × (ℝ × ℝ)) :=
  {profile | take profile.2.2 profile.1 = true ∧
    report profile.1 profile.2.1 = true}

/-- The literal complement of the complete observed report action. -/
def lg21OptionalSequentialFullPublicNoReportSet
    {Base : Type*} (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) :
    Set (Base × (ℝ × ℝ)) :=
  {profile | take profile.2.2 profile.1 = false ∨
    report profile.1 profile.2.1 = false}

theorem lg21OptionalSequentialFullPublicReportSet_measurable
    {Base : Type*} [MeasurableSpace Base]
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool)
    (htake : Measurable (fun profile : Base × (ℝ × ℝ) =>
      take profile.2.2 profile.1))
    (hreport : Measurable (fun profile : Base × (ℝ × ℝ) =>
      report profile.1 profile.2.1)) :
    MeasurableSet (lg21OptionalSequentialFullPublicReportSet take report) := by
  change MeasurableSet {profile : Base × (ℝ × ℝ) |
    take profile.2.2 profile.1 = true ∧ report profile.1 profile.2.1 = true}
  exact ((measurableSet_singleton true).preimage htake).inter
    ((measurableSet_singleton true).preimage hreport)

theorem lg21OptionalSequentialFullPublicNoReportSet_eq_compl
    {Base : Type*} [MeasurableSpace Base]
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) :
    lg21OptionalSequentialFullPublicNoReportSet take report =
      (lg21OptionalSequentialFullPublicReportSet take report)ᶜ := by
  ext profile
  cases htake : take profile.2.2 profile.1 <;>
    cases hreport : report profile.1 profile.2.1 <;>
    simp [lg21OptionalSequentialFullPublicNoReportSet,
      lg21OptionalSequentialFullPublicReportSet, htake, hreport]

theorem lg21OptionalSequentialFullPublicNoReportSet_measurable
    {Base : Type*} [MeasurableSpace Base]
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool)
    (htake : Measurable (fun profile : Base × (ℝ × ℝ) =>
      take profile.2.2 profile.1))
    (hreport : Measurable (fun profile : Base × (ℝ × ℝ) =>
      report profile.1 profile.2.1)) :
    MeasurableSet (lg21OptionalSequentialFullPublicNoReportSet take report) := by
  rw [lg21OptionalSequentialFullPublicNoReportSet_eq_compl]
  exact (lg21OptionalSequentialFullPublicReportSet_measurable
    take report htake hreport).compl

theorem lg21OptionalSourceReportEvent_eq_sequentialFullPublic_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) :
    lg21OptionalSourceReportEvent base score skill take report =
      (fun omega => (base omega, (score omega, skill omega))) ⁻¹'
        lg21OptionalSequentialFullPublicReportSet take report := by
  rfl

theorem lg21OptionalSourceNoReportEvent_eq_sequentialFullPublic_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) :
    lg21OptionalSourceNoReportEvent base score skill take report =
      (fun omega => (base omega, (score omega, skill omega))) ⁻¹'
        lg21OptionalSequentialFullPublicNoReportSet take report := by
  rfl

/-- Only after the pre-score action has been proved almost surely true may
the literal sequential no-report event be replaced by the post-score
withholding event. -/
theorem lg21OptionalSourceNoReportEvent_ae_eq_scoreNoReport_of_allTake
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool)
    (hallTake : ∀ᵐ omega ∂sourceLaw,
      take (skill omega) (base omega) = true) :
    lg21OptionalSourceNoReportEvent base score skill take report =ᵐ[sourceLaw]
      {omega | report (base omega) (score omega) = false} := by
  filter_upwards [hallTake] with omega htake
  apply propext
  change (take (skill omega) (base omega) = false ∨
      report (base omega) (score omega) = false) ↔
    report (base omega) (score omega) = false
  rw [htake]
  simp

/-- Normalized laws of literal sequential no-reporters and post-score
withholders agree after all taking has been derived. -/
theorem lg21NormalizedRestriction_sourceNoReport_eq_scoreNoReport_of_allTake
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool)
    (hallTake : ∀ᵐ omega ∂sourceLaw,
      take (skill omega) (base omega) = true) :
    lg21NormalizedRestriction sourceLaw
        (lg21OptionalSourceNoReportEvent base score skill take report) =
      lg21NormalizedRestriction sourceLaw
        {omega | report (base omega) (score omega) = false} := by
  have hevent := lg21OptionalSourceNoReportEvent_ae_eq_scoreNoReport_of_allTake
    sourceLaw base score skill take report hallTake
  unfold lg21NormalizedRestriction
  rw [measure_congr hevent, Measure.restrict_congr_set hevent]

/-- A source-independent positive-mass split: a positive bad action mass is
either present at bases with a positive good-action fibre or at bases whose
good-action fibre is zero. -/
theorem lg21_positive_mass_split_positive_and_zero_fibres
    {Base Outcome : Type*} [MeasurableSpace Base] [MeasurableSpace Outcome]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (kernel : Kernel Base Outcome) [IsMarkovKernel kernel]
    (badEvent goodEvent : Set (Base × Outcome))
    (hbad : MeasurableSet badEvent)
    (hpositive : 0 < (baseLaw ⊗ₘ kernel) badEvent) :
    (0 < baseLaw
      (Function.support (selectionMass kernel badEvent) ∩
        Function.support (selectionMass kernel goodEvent))) ∨
      (0 < baseLaw
        (Function.support (selectionMass kernel badEvent) ∩
          {base | selectionMass kernel goodEvent base = 0})) := by
  let badMass : Base -> ℝ≥0∞ := selectionMass kernel badEvent
  let goodMass : Base -> ℝ≥0∞ := selectionMass kernel goodEvent
  have hbadPositive : 0 < baseLaw (Function.support badMass) := by
    have hmassMeasurable : Measurable badMass :=
      selectionMass_measurable hbad
    change 0 < (baseLaw ⊗ₘ kernel) badEvent at hpositive
    rw [Measure.compProd_apply hbad] at hpositive
    exact (lintegral_pos_iff_support hmassMeasurable).mp hpositive
  by_cases hcoexist : 0 < baseLaw
      (Function.support badMass ∩ Function.support goodMass)
  · exact Or.inl (by simpa [badMass, goodMass] using hcoexist)
  · right
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hcoexistZero : baseLaw
        (Function.support badMass ∩ Function.support goodMass) = 0 :=
      le_antisymm (not_lt.mp hcoexist) (zero_le _)
    have hpartition : Function.support badMass =
        (Function.support badMass ∩ Function.support goodMass) ∪
          (Function.support badMass ∩ {base | goodMass base = 0}) := by
      ext base
      simp only [Function.mem_support, Set.mem_union, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · intro hbadMass
        by_cases hgoodMass : goodMass base = 0
        · exact Or.inr ⟨hbadMass, hgoodMass⟩
        · exact Or.inl ⟨hbadMass, hgoodMass⟩
      · intro h
        exact h.elim (fun hleft => hleft.1) (fun hright => hright.1)
    have hbadZero : baseLaw (Function.support badMass) = 0 := by
      rw [hpartition]
      exact measure_union_null hcoexistZero hzero
    exact (ne_of_gt hbadPositive) hbadZero

/-- Bases at which the literal complete report action has zero conditional
mass.  This is a semantic fibre predicate, not a strategy-name convention. -/
def lg21OptionalZeroActualReporterBaseRegion
    {Base Outcome : Type*} [MeasurableSpace Base] [MeasurableSpace Outcome]
    (kernel : Kernel Base Outcome) (reportEvent : Set (Base × Outcome)) : Set Base :=
  {base | selectionMass kernel reportEvent base = 0}

theorem lg21OptionalZeroActualReporterBaseRegion_measurable
    {Base Outcome : Type*} [MeasurableSpace Base] [MeasurableSpace Outcome]
    (kernel : Kernel Base Outcome) [IsMarkovKernel kernel]
    (reportEvent : Set (Base × Outcome)) (hreportEvent : MeasurableSet reportEvent) :
    MeasurableSet (lg21OptionalZeroActualReporterBaseRegion kernel reportEvent) := by
  change MeasurableSet {base | selectionMass kernel reportEvent base = 0}
  convert (measurableSet_singleton 0).preimage
    (selectionMass_measurable (κ := kernel) hreportEvent) using 1

/-- Restricting a factorized source law to zero-reporter base fibres gives
zero report mass.  This is the measure-theoretic connector needed before the
local positive-mass entry theorem can be applied. -/
theorem lg21_source_zeroReporterRegion_report_mass_zero
    {Omega Base Outcome : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Outcome]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (kernel : Kernel Base Outcome) [IsMarkovKernel kernel]
    (observation : Omega -> Base × Outcome) (base : Omega -> Base)
    (hobs : Measurable observation)
    (hbaseObservation : ∀ omega, (observation omega).1 = base omega)
    (hfactor : sourceLaw.map observation = baseLaw ⊗ₘ kernel)
    (reportEvent : Set (Base × Outcome)) (hreportEvent : MeasurableSet reportEvent) :
    sourceLaw
      (base ⁻¹' (lg21OptionalZeroActualReporterBaseRegion kernel reportEvent) ∩
        observation ⁻¹' reportEvent) = 0 := by
  let zeroRegion : Set Base :=
    lg21OptionalZeroActualReporterBaseRegion kernel reportEvent
  have hzeroRegion : MeasurableSet zeroRegion := by
    exact lg21OptionalZeroActualReporterBaseRegion_measurable
      kernel reportEvent hreportEvent
  let target : Set (Base × Outcome) :=
    (zeroRegion ×ˢ Set.univ) ∩ reportEvent
  have htarget : MeasurableSet target :=
    (hzeroRegion.prod MeasurableSet.univ).inter hreportEvent
  have hpreimage : observation ⁻¹' target =
      base ⁻¹' zeroRegion ∩ observation ⁻¹' reportEvent := by
    ext omega
    simp [target, hbaseObservation omega]
  have hintegrand : (fun publicBase =>
      kernel publicBase (Prod.mk publicBase ⁻¹' target)) = 0 := by
    funext publicBase
    by_cases hzero : publicBase ∈ zeroRegion
    · have hfibre : Prod.mk publicBase ⁻¹' target =
        Prod.mk publicBase ⁻¹' reportEvent := by
        ext outcome
        simp [target, hzero]
      rw [hfibre]
      exact hzero
    · have hfibre : Prod.mk publicBase ⁻¹' target = ∅ := by
        ext outcome
        simp [target, hzero]
      simp [hfibre]
  calc
    sourceLaw (base ⁻¹' zeroRegion ∩ observation ⁻¹' reportEvent) =
        sourceLaw (observation ⁻¹' target) := by rw [hpreimage]
    _ = sourceLaw.map observation target := by
        rw [Measure.map_apply hobs htarget]
    _ = (baseLaw ⊗ₘ kernel) target := by rw [hfactor]
    _ = ∫⁻ publicBase, kernel publicBase
        (Prod.mk publicBase ⁻¹' target) ∂baseLaw := by
        rw [Measure.compProd_apply htarget]
    _ = 0 := by
      rw [hintegrand]
      exact lintegral_zero

theorem lg21_source_base_preimage_measure_eq_of_factorization
    {Omega Base Outcome : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Outcome]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (kernel : Kernel Base Outcome) [IsMarkovKernel kernel]
    (observation : Omega -> Base × Outcome) (base : Omega -> Base)
    (hobs : Measurable observation) (hbase : Measurable base)
    (hbaseObservation : ∀ omega, (observation omega).1 = base omega)
    (hfactor : sourceLaw.map observation = baseLaw ⊗ₘ kernel)
    (region : Set Base) (hregion : MeasurableSet region) :
    sourceLaw (base ⁻¹' region) = baseLaw region := by
  have hbaseMarginal : sourceLaw.map base = baseLaw := by
    calc
      sourceLaw.map base = sourceLaw.map (fun omega => (observation omega).1) := by
        congr 1
        funext omega
        exact (hbaseObservation omega).symm
      _ = (sourceLaw.map observation).map Prod.fst := by
        exact (Measure.map_map measurable_fst hobs).symm
      _ = (baseLaw ⊗ₘ kernel).map Prod.fst := by rw [hfactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ kernel).fst = baseLaw
        rw [Measure.fst_compProd]
  rw [← hbaseMarginal, Measure.map_apply hbase hregion]

/-- The score marginal of a source law with the literal Gaussian
`(base, score, skill)` factorization is the corresponding base-indexed
Gaussian score kernel.  This is a law identity, not a PBO assertion. -/
theorem lg21_source_base_score_factorization_of_gaussianSignalJoint
    {Omega Base : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    sourceLaw.map (fun omega => (base omega, score omega)) =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        (baseVariance + noiseVariance).toNNReal := by
  let observation : Omega -> Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let associatedObservation : Omega -> (Base × ℝ) × ℝ :=
    fun omega => ((base omega, score omega), skill omega)
  have hobs : Measurable observation := hbase.prodMk (hscore.prodMk hskill)
  have hassocObs : Measurable associatedObservation :=
    (hbase.prodMk hscore).prodMk hskill
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean
        (baseVariance + noiseVariance).toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (baseVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hassociated : sourceLaw.map associatedObservation =
      gaussianSignalBaseScoreLatentLaw
        baseLaw baseMean hbaseMean baseVariance noiseVariance := by
    calc
      sourceLaw.map associatedObservation =
          (sourceLaw.map observation).map MeasurableEquiv.prodAssoc.symm := by
            rw [Measure.map_map (MeasurableEquiv.measurable _) hobs]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance).map
            MeasurableEquiv.prodAssoc.symm := by
            rw [hsourceFactor]
      _ = gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean baseVariance noiseVariance := rfl
  calc
    sourceLaw.map (fun omega => (base omega, score omega)) =
        (sourceLaw.map associatedObservation).map Prod.fst := by
          rw [Measure.map_map measurable_fst hassocObs]
          rfl
    _ = (gaussianSignalBaseScoreLatentLaw
        baseLaw baseMean hbaseMean baseVariance noiseVariance).map Prod.fst := by
          rw [hassociated]
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        (baseVariance + noiseVariance).toNNReal := by
          rw [gaussianSignalBaseScoreLatentLaw_factorization
            baseLaw baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance]
          exact Measure.fst_compProd _ _

/-- Local positive-mass stability rules out a positive base-mass region with
zero *actual sequential* reporter mass. -/
theorem lg21_optional_zeroActualReporterBaseRegion_source_mass_zero_of_stability
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (hcurrentTake : Measurable (fun omega => currentTake (skill omega) (base omega)))
    (hcurrentReport : Measurable (fun omega => currentReport (base omega) (score omega)))
    (hcurrentTakePublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      currentTake profile.2.2 profile.1))
    (hcurrentReportPublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      currentReport profile.1 profile.2.1))
    (hstable : LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      currentTake currentReport)
    (anchor : ℝ) :
    sourceLaw (base ⁻¹'
      (lg21OptionalZeroActualReporterBaseRegion
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalSequentialFullPublicReportSet currentTake currentReport))) = 0 := by
  let observation : Omega -> Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let reportEvent : Set (Base × (ℝ × ℝ)) :=
    lg21OptionalSequentialFullPublicReportSet currentTake currentReport
  let zeroRegion : Set Base := lg21OptionalZeroActualReporterBaseRegion
    (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
    reportEvent
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hobs : Measurable observation := hbase.prodMk (hscore.prodMk hskill)
  have hreportEvent : MeasurableSet reportEvent := by
    exact lg21OptionalSequentialFullPublicReportSet_measurable
      currentTake currentReport hcurrentTakePublic hcurrentReportPublic
  have hzeroReport : sourceLaw (base ⁻¹' zeroRegion ∩
      lg21OptionalSourceReportEvent base score skill currentTake currentReport) = 0 := by
    simpa [observation, reportEvent, zeroRegion,
      lg21OptionalSourceReportEvent_eq_sequentialFullPublic_preimage] using
      (lg21_source_zeroReporterRegion_report_mass_zero
        sourceLaw baseLaw
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        observation base hobs
        (fun omega => rfl) hsourceFactor reportEvent hreportEvent)
  have hzeroRegion : MeasurableSet zeroRegion := by
    exact lg21OptionalZeroActualReporterBaseRegion_measurable
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
      reportEvent hreportEvent
  by_contra hnonzero
  have hpositive : 0 < sourceLaw (base ⁻¹' zeroRegion) :=
    pos_iff_ne_zero.mpr hnonzero
  exact (lg21_optional_localGaussian_not_stable_of_positive_zeroReporter_region
    sourceLaw base score skill hbase hscore hskill baseLaw
    baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
    hsourceFactor currentTake currentReport hcurrentTake hcurrentReport
    zeroRegion hzeroRegion hpositive hzeroReport anchor) hstable

/-- Once zero-reporter fibres are eliminated, the positive-reporter
selected-Gaussian conclusion rules out every literal no-taker. -/
theorem lg21_optional_source_noTake_mass_zero_of_positiveReporter_allTake
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (hcurrentTake : Measurable (fun omega => currentTake (skill omega) (base omega)))
    (hcurrentReport : Measurable (fun omega => currentReport (base omega) (score omega)))
    (hcurrentTakePublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      currentTake profile.2.2 profile.1))
    (hcurrentReportPublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      currentReport profile.1 profile.2.1))
    (hstable : LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      currentTake currentReport)
    (hpositiveReporterAllTake : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalSequentialFullPublicReportSet currentTake currentReport)
        publicBase ≠ 0 ->
      ∀ latentSkill, currentTake latentSkill publicBase = true)
    (anchor : ℝ) :
    sourceLaw {omega | currentTake (skill omega) (base omega) = false} = 0 := by
  let reportEvent : Set (Base × (ℝ × ℝ)) :=
    lg21OptionalSequentialFullPublicReportSet currentTake currentReport
  let zeroRegion : Set Base := lg21OptionalZeroActualReporterBaseRegion
    (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
    reportEvent
  have hzeroRegionMass : sourceLaw (base ⁻¹' zeroRegion) = 0 := by
    simpa [reportEvent, zeroRegion] using
      (lg21_optional_zeroActualReporterBaseRegion_source_mass_zero_of_stability
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
        hsourceFactor currentTake currentReport hcurrentTake hcurrentReport
        hcurrentTakePublic hcurrentReportPublic hstable anchor)
  apply measure_mono_null (s := {omega |
      currentTake (skill omega) (base omega) = false})
    (t := base ⁻¹' zeroRegion) _ hzeroRegionMass
  intro omega hnoTake
  change currentTake (skill omega) (base omega) = false at hnoTake
  change base omega ∈ zeroRegion
  change selectionMass
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
      reportEvent (base omega) = 0
  by_contra hreporterPositive
  have htake := hpositiveReporterAllTake (base omega) hreporterPositive (skill omega)
  simp [hnoTake] at htake

/-!
## Literal source-facing specialization data

The two records below are deliberately made of the actual action, conditional
mean, and best-response obligations used by the proof.  In particular, the
positive-reporter field is not an ``all take'' certificate: it records the
selected latent population and its attained reporter PBO, from which the
selected-Gaussian strict-gain theorem derives all taking.
-/

/-- The literal selected-Gaussian PBO calculation at one public base with an
attained complete sequential report action.  The selected set is explicitly
identified with the pre-score taking action; no cutoff representation or
off-path reporter value occurs here. -/
structure LG21OptionalPositiveReporterFibrePBO
    {Base : Type*} [MeasurableSpace Base]
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ)
    (publicBase : Base) (priorMean priorVariance noiseVariance : ℝ)
    (selected : Set ℝ) : Prop where
  selected_measurable : MeasurableSet selected
  selected_eq_actual_takers : ∀ latentSkill,
    latentSkill ∈ selected ↔ E.takeDecision latentSkill publicBase = true
  selected_positive : 0 < gaussianReal priorMean priorVariance.toNNReal selected
  report_measurable : MeasurableSet
    {score | E.reportDecision publicBase score = true}
  reporter_positive :
    0 < normalizedSelectedBase
      (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ selected)
      {score | E.reportDecision publicBase score = true}
  reported_pbo :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    E.reportedPayoff publicBase =ᵐ[
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected))
        {score | E.reportDecision publicBase score = true}]
      fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score

namespace LG21OptionalPositiveReporterFibrePBO

/-- An attained literal reporter fibre gives all taking at that base.  The
reporting best response is projected from Definition 1 rather than supplied
as a closure certificate. -/
theorem all_take
    {Base : Type*} [MeasurableSpace Base]
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    {publicBase : Base} {priorMean priorVariance noiseVariance : ℝ}
    {selected : Set ℝ}
    (H : LG21OptionalPositiveReporterFibrePBO E publicBase
      priorMean priorVariance noiseVariance selected)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (htestLaw : ∀ latentSkill,
      E.testLaw latentSkill publicBase =
        gaussianReal latentSkill noiseVariance.toNNReal) :
    ∀ latentSkill, E.takeDecision latentSkill publicBase = true := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  apply lg21_positive_reporter_selectedGaussian_all_take_at_base
    E hEq publicBase priorMean priorVariance noiseVariance selected
  · exact hpriorVariance
  · exact hnoiseVariance
  · exact H.selected_measurable
  · exact H.selected_positive
  · exact H.report_measurable
  · exact H.reporter_positive
  · exact htestLaw
  · exact H.reported_pbo
  · let reportLaw : Measure ℝ :=
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected))
        {score | E.reportDecision publicBase score = true}
    have hreportAction : ∀ᵐ score ∂reportLaw,
        E.reportDecision publicBase score = true := by
      change ∀ᵐ score ∂
          (normalizedSelectedBase
            (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
            (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
            (Set.univ ×ˢ selected)
            {score | E.reportDecision publicBase score = true})⁻¹ •
            (normalizedSelectedBase
              (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
              (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
              (Set.univ ×ˢ selected)).restrict
              {score | E.reportDecision publicBase score = true},
          E.reportDecision publicBase score = true
      apply Measure.ae_smul_measure
      rw [ae_restrict_iff' H.report_measurable]
      exact Filter.Eventually.of_forall fun score hscore => hscore
    filter_upwards [hreportAction] with score hreport
    exact (lg21OptionalSequentialEquilibrium_report_bestResponse hEq publicBase).1
      score hreport

end LG21OptionalPositiveReporterFibrePBO

/-- Literal source closeout under the paper's candidate-PBO semantics.  A
positive current no-report population yields a literal high-score candidate
with positive changed-to-report mass and both branches recalibrated on their
own action laws.  Thus the report stage does not reuse a hypothetical
reported payoff on the predecessor's no-report population. -/
theorem lg21_optional_source_all_take_and_report_ae_of_recalibrated_entries
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ)
    (hEq : lg21OptionalSequentialEquilibrium E)
    (htake : Measurable (fun omega => E.takeDecision (skill omega) (base omega)))
    (hreport : Measurable (fun omega => E.reportDecision (base omega) (score omega)))
    (htakePublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      E.takeDecision profile.2.2 profile.1))
    (hreportPublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      E.reportDecision profile.1 profile.2.1))
    (hzeroReporterStable : LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      E.takeDecision E.reportDecision)
    (hpartialReporterStable :
      LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
        sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
          E.takeDecision E.reportDecision)
    (hpositiveReporterFibre : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalSequentialFullPublicReportSet
          E.takeDecision E.reportDecision)
        publicBase ≠ 0 ->
      ∃ selected,
        LG21OptionalPositiveReporterFibrePBO E publicBase
          (baseMean publicBase) baseVariance noiseVariance selected)
    (htestLaw : ∀ publicBase latentSkill,
      E.testLaw latentSkill publicBase =
        gaussianReal latentSkill noiseVariance.toNNReal) :
    ∀ᵐ omega ∂sourceLaw,
      E.takeDecision (skill omega) (base omega) = true ∧
        E.reportDecision (base omega) (score omega) = true := by
  let reportEvent : Set (Base × (ℝ × ℝ)) :=
    lg21OptionalSequentialFullPublicReportSet E.takeDecision E.reportDecision
  have hpositiveReporterAllTake : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        reportEvent publicBase ≠ 0 ->
      ∀ latentSkill, E.takeDecision latentSkill publicBase = true := by
    intro publicBase hpositive
    rcases hpositiveReporterFibre publicBase
        (by simpa [reportEvent] using hpositive) with ⟨selected, H⟩
    apply H.all_take hEq hbaseVariance hnoiseVariance
    exact htestLaw publicBase
  have hnoTakeZero : sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
    exact lg21_optional_source_noTake_mass_zero_of_positiveReporter_allTake
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
      hsourceFactor E.takeDecision E.reportDecision htake hreport
      htakePublic hreportPublic hzeroReporterStable
      (by simpa [reportEvent] using hpositiveReporterAllTake) 0
  have htakeBad : {omega | ¬ E.takeDecision (skill omega) (base omega) = true} =
      {omega | E.takeDecision (skill omega) (base omega) = false} := by
    ext omega
    cases htakeValue : E.takeDecision (skill omega) (base omega) <;>
      simp [htakeValue]
  have hallTake : ∀ᵐ omega ∂sourceLaw,
      E.takeDecision (skill omega) (base omega) = true := by
    rw [ae_iff, htakeBad]
    exact hnoTakeZero
  let scoreNoReport : Set Omega :=
    {omega | E.reportDecision (base omega) (score omega) = false}
  have hnoReportImpossible : ¬ 0 < sourceLaw scoreNoReport := by
    simpa [scoreNoReport] using
      (lg21_optional_no_positive_currentNoReport_of_recalibratedEntry_stable
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
        hsourceFactor E.takeDecision E.reportDecision hallTake hpartialReporterStable)
  have hnoReportZero : sourceLaw scoreNoReport = 0 :=
    le_antisymm (not_lt.mp hnoReportImpossible) (zero_le _)
  have hreportBad : {omega | ¬ E.reportDecision (base omega) (score omega) = true} =
      scoreNoReport := by
    ext omega
    cases hreportValue : E.reportDecision (base omega) (score omega) <;>
      simp [scoreNoReport, hreportValue]
  have hreportAE : ∀ᵐ omega ∂sourceLaw,
      E.reportDecision (base omega) (score omega) = true := by
    rw [ae_iff, hreportBad]
    exact hnoReportZero
  filter_upwards [hallTake, hreportAE] with omega htakeValue hreportValue
  exact ⟨htakeValue, hreportValue⟩

/-- Measurability of the literal latent-skill coordinate of the continuous
source population. -/
theorem lg21ContinuousPopulationSkill_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature] :
    Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
  change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
  exact measurable_fst.comp measurable_snd

/-- Measurability of the literal realized test score of the continuous source
population. -/
theorem lg21ContinuousPopulationFeature_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21ContinuousPopulationFeature testFeature) := by
  change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
    student.2.1 + student.2.2 testFeature
  exact lg21ContinuousPopulationSkill_measurable.add
    ((measurable_pi_apply testFeature).comp (measurable_snd.comp measurable_snd))

/--
Literal observed-access source equilibrium data for the optional protocol.

The fields retain the two source action times and spell out the only PBO
identities used by the closeout.  In particular, `estimationConsistent` from
the legacy sequential data is not used: attained reporter fibres carry their
own selected-law PBO, and a positive literal sequential no-report population
carries both conditional means needed for its deviation comparison.
-/
structure LG21ObservedAccessOptionalLiteralSourceEquilibrium
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) where
  data : LG21OptionalSequentialEquilibriumData ℝ
    (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  definition1 : lg21OptionalSequentialEquilibrium data
  takeDecision_measurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    data.takeDecision pair.2 pair.1)
  reportDecision_measurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    data.reportDecision pair.1 pair.2)
  local_entry_stable :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
        ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
          lg21ContinuousPopulationSkill_measurable))
      data.takeDecision data.reportDecision
  /-- Stability against a positive-mass report entry from a partial reporter
  profile.  The candidate carries its own report and no-report PBOs; this
  field does not assign the predecessor's reported payoff on no-report
  histories. -/
  recalibrated_report_entry_stable :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
        ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
          lg21ContinuousPopulationSkill_measurable))
      data.takeDecision data.reportDecision
  /-- Definition 1's known-decision-function PBO semantic on each attained
  positive conditional reporter fibre.  This is deliberately scoped by
  positive fibre mass: it supplies no value or belief for a zero-mass action
  fibre.  The source PBO is pointwise in the known public decision functions,
  so this is a source-semantic obligation rather than a derived selection-free
  posterior formula. -/
  attained_positive_reporter_fibre_pbo : ∀
      (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
      (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ)
      (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ->
      0 < baseVariance ->
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationBase testFeature student,
            (lg21ContinuousPopulationFeature testFeature student,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) ->
      ∀ publicBase,
        selectionMass
          (gaussianSignalJointKernel baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ))
          (lg21OptionalSequentialFullPublicReportSet
            data.takeDecision data.reportDecision)
          publicBase ≠ 0 ->
        ∃ selected,
          LG21OptionalPositiveReporterFibrePBO data publicBase
            (baseMean publicBase) baseVariance
            (M.noiseVariance testFeature : ℝ) selected
  test_law_gaussian : ∀ publicBase latentSkill,
    data.testLaw latentSkill publicBase =
      gaussianReal latentSkill (M.noiseVariance testFeature)
  /-- The actual reporter branch is conditioned under the normalized
  sequential `take = report = true` action law.  It is not a raw-population
  PBO assertion before the behavior theorem has established that this branch
  has full mass. -/
  actual_report_integrable : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision) ->
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision))
  actual_report_pbo : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision) ->
    (fun student => data.reportedPayoff
      (lg21ContinuousPopulationBase testFeature student)
      (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            data.takeDecision data.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (fun student =>
              (lg21ContinuousPopulationBase testFeature student,
                lg21ContinuousPopulationFeature testFeature student))
              inferInstance]
  /-- The following two fields are both on the *actual* sequential
  `take = false ∨ report = false` action event. -/
  actual_noReport_integrable : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision) ->
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision))
  actual_noReport_pbo : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision) ->
    (fun student => data.noReportPayoff
      (lg21ContinuousPopulationBase testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceNoReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            data.takeDecision data.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          data.takeDecision data.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (lg21ContinuousPopulationBase testFeature)
              inferInstance]

/-- Continuous observed-access source closeout.  The Gaussian factorization
is obtained from the literal full-profile population in the proof; the
equilibrium carrier contributes only source action, PBO, and best-response
facts. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.data.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.data.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true := by
  let sourceLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  letI : IsProbabilityMeasure sourceLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable score := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have htake : Measurable (fun student =>
      E.data.takeDecision (skill student) (base student)) := by
    exact E.takeDecision_measurable.comp (hbase.prodMk hskill)
  have hreport : Measurable (fun student =>
      E.data.reportDecision (base student) (score student)) := by
    exact E.reportDecision_measurable.comp (hbase.prodMk hscore)
  have htakePublic : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
      E.data.takeDecision profile.2.2 profile.1) := by
    exact E.takeDecision_measurable.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hreportPublic : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
      E.data.reportDecision profile.1 profile.2.1) := by
    exact E.reportDecision_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hpositiveReporterFibre : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ))
        (lg21OptionalSequentialFullPublicReportSet
          E.data.takeDecision E.data.reportDecision)
        publicBase ≠ 0 ->
      ∃ selected,
        LG21OptionalPositiveReporterFibrePBO E.data publicBase
          (baseMean publicBase) baseVariance
          (M.noiseVariance testFeature : ℝ) selected := by
    exact E.attained_positive_reporter_fibre_pbo
      baseLaw baseMean baseVariance hbaseMean
      hbaseLaw hbaseVariance hsourceFactor
  have htestLaw : ∀ publicBase latentSkill,
      E.data.testLaw latentSkill publicBase =
        gaussianReal latentSkill (M.noiseVariance testFeature : ℝ).toNNReal := by
    intro publicBase latentSkill
    simpa using E.test_law_gaussian publicBase latentSkill
  simpa [sourceLaw, base, score, skill] using
    (lg21_optional_source_all_take_and_report_ae_of_recalibrated_entries
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
      hbaseVariance htestNoiseVariance hsourceFactor E.data E.definition1
      htake hreport htakePublic hreportPublic E.local_entry_stable
      E.recalibrated_report_entry_stable hpositiveReporterFibre htestLaw)

end

end LG21TestOptionalPolicies

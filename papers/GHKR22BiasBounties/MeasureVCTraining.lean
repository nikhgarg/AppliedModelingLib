import GHKR22BiasBounties.MeasureTernaryCSC
import GHKR22BiasBounties.VCTraining

/-!
# VC control for certificate training on arbitrary populations

Lemma 15 is a genuinely distributional statement.  This file lifts the
finite-PMF wrapper in `VCTraining` to any probability measure on `X × Bool`.
The combinatorial list-update VC bound is reused verbatim.  For infinite
classes we state explicitly the standard permissible-class condition: the
five suprema/events used by the VC symmetrization proof must be measurable.
-/

namespace GHKR22BiasBounties

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open AppliedModelingLib Probability
open AppliedModelingLib.Statistics

/-- Population zero-one error is exactly the measure-theoretic model loss. -/
theorem binaryPopulationError_eq_measureModelLoss
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (classifier : Model X Bool) :
    binaryPopulationError law classifier =
      measureModelLoss law binaryZeroOneLoss classifier := by
  unfold binaryPopulationError measureModelLoss
  apply integral_congr_ae
  filter_upwards [] with datum
  exact binaryClassificationLoss_eq_datumLoss classifier datum

/-- On any measurable population, a certificate score is the total-loss
decrease produced by its list update. -/
theorem measureCertificateImprovementScore_eq_measureModelLoss_sub_listUpdate
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement)
    {group : Group X} (hgroup : MeasurableGroup group) :
    measureCertificateImprovementScore law binaryZeroOneLoss current group replacement =
      measureModelLoss law binaryZeroOneLoss current -
        measureModelLoss law binaryZeroOneLoss
          (listUpdate current group replacement) := by
  rw [measureCertificateImprovementScore_eq_numerator_sub law
      measurableBoundedLoss_binaryZeroOneLoss hcurrent hreplacement hgroup,
    ← measureModelLoss_sub_listUpdate_eq_numerator_sub law
      measurableBoundedLoss_binaryZeroOneLoss hcurrent hreplacement hgroup]

/-- The source score-deviation event for a fixed current model and arbitrary
population law. -/
def MeasureCertificateVCDeviationEvent
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (tolerance : ℝ) {n : ℕ} (sample : Fin n → X × Bool) : Prop :=
  ∃ g ∈ G, ∃ h ∈ H,
    tolerance <
      |empiricalSubmissionScore binaryZeroOneLoss sample
          { current := current, group := g, replacement := h } -
        measureCertificateImprovementScore law binaryZeroOneLoss current g h|

/-- Probability of Lemma 15's deviation event under an iid sample. -/
noncomputable def MeasureCertificateVCDeviationFailure
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (tolerance : ℝ) (n : ℕ) : ℝ :=
  (finiteIIDSampleLaw law n).real
    {sample | MeasureCertificateVCDeviationEvent law current G H tolerance sample}

/-- The five event-measurability witnesses used in the reusable VC theorem.
This is the usual permissible-class regularity condition for a possibly
uncountable concept class, packaged so the source theorem remains readable. -/
def VCSourceEventsMeasurable
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (concepts : Set (BinaryClassifier X))
    (d count : ℕ) (delta : ℝ) : Prop :=
  MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)) ∧
    MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)) ∧
    MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)) ∧
    MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)) ∧
    MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4))

/-- A score deviation beyond the sum of the two VC radii forces either the
current classifier or the corresponding list update to violate its own
population-error bound. -/
theorem measureCertificateVCDeviationEvent_subset_errorEvents
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (updateRadius currentRadius : ℝ) (n : ℕ) :
    {sample : Fin n → X × Bool |
      MeasureCertificateVCDeviationEvent law current G H
        (updateRadius + currentRadius) sample} ⊆
      {sample | ∃ updated, updated ∈ ListUpdateClass current G H ∧
        updateRadius <
          |finiteBinaryEmpiricalError sample updated -
            binaryPopulationError law updated|} ∪
      {sample | ∃ classifier,
        classifier ∈ ({current} : Set (BinaryClassifier X)) ∧
        currentRadius <
          |finiteBinaryEmpiricalError sample classifier -
            binaryPopulationError law classifier|} := by
  intro sample hdeviation
  rcases hdeviation with ⟨g, hg, h, hh, hscore⟩
  let updated := listUpdate current g h
  let currentGap := finiteBinaryEmpiricalError sample current -
    binaryPopulationError law current
  let updateGap := finiteBinaryEmpiricalError sample updated -
    binaryPopulationError law updated
  have hscoreEq :
      empiricalSubmissionScore binaryZeroOneLoss sample
          { current := current, group := g, replacement := h } -
        measureCertificateImprovementScore law binaryZeroOneLoss current g h =
      currentGap - updateGap := by
    rw [empiricalSubmissionScore_eq_empiricalError_sub_listUpdate,
      measureCertificateImprovementScore_eq_measureModelLoss_sub_listUpdate
        law hcurrent (hHmeasurable h hh) (hGmeasurable g hg),
      ← binaryPopulationError_eq_measureModelLoss law current,
      ← binaryPopulationError_eq_measureModelLoss law (listUpdate current g h)]
    dsimp [currentGap, updateGap, updated]
    ring
  rw [hscoreEq] at hscore
  by_cases hupdate : updateRadius < |updateGap|
  · left
    exact ⟨updated, ⟨g, hg, h, hh, rfl⟩, hupdate⟩
  · right
    refine ⟨current, Set.mem_singleton current, ?_⟩
    have hupdateLe : |updateGap| ≤ updateRadius := le_of_not_gt hupdate
    have htriangle : |currentGap - updateGap| ≤
        |currentGap| + |updateGap| := abs_sub _ _
    change currentRadius < |currentGap|
    by_contra hcurrentGap
    have hcurrentLe : |currentGap| ≤ currentRadius := le_of_not_gt hcurrentGap
    linarith

/-- Lemma 15 on an arbitrary population measure, with the checked
product-trace VC dimension and explicit source confidence radius. -/
theorem measureLemma15_vc_uniform_convergence
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (dG dH : ℕ) (hvcG : VCDimensionAtMost G dG)
    (hvcH : VCDimensionAtMost H dH)
    (n : ℕ) (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (delta : ℝ) (hdelta : 0 < delta)
    (hupdateEvents : VCSourceEventsMeasurable law
      (ListUpdateClass current G H) (listUpdateVCDimensionBound dG dH) n (delta / 2))
    (hcurrentEvents : VCSourceEventsMeasurable law
      ({current} : Set (BinaryClassifier X)) 1 n (delta / 2)) :
    MeasureCertificateVCDeviationFailure law current G H
        (certificateVCConfidenceRadius dG dH n delta) n ≤ delta := by
  let updateDimension := listUpdateVCDimensionBound dG dH
  let updateRadius := finiteIIDVCSourceConfidenceRadius
    updateDimension n (delta / 2)
  let currentRadius := finiteIIDVCSourceConfidenceRadius 1 n (delta / 2)
  let updateBad : Set (Fin n → X × Bool) := {sample | ∃ updated,
    updated ∈ ListUpdateClass current G H ∧
      updateRadius <
        |finiteBinaryEmpiricalError sample updated -
          binaryPopulationError law updated|}
  let currentBad : Set (Fin n → X × Bool) := {sample | ∃ classifier,
    classifier ∈ ({current} : Set (BinaryClassifier X)) ∧
      currentRadius <
        |finiteBinaryEmpiricalError sample classifier -
          binaryPopulationError law classifier|}
  have hupdateDimensionPos : 0 < updateDimension := by
    dsimp [updateDimension, listUpdateVCDimensionBound]
    exact Nat.ceil_pos.mpr (sourceListUpdateVCBound_pos dG dH)
  have honeDimension : 1 ≤ n + n := by omega
  have hdeltaHalf : 0 < delta / 2 := half_pos hdelta
  have hupdateClassMeasurable : ∀ classifier,
      classifier ∈ ListUpdateClass current G H → Measurable classifier := by
    intro classifier hclassifier
    rcases hclassifier with ⟨g, hg, h, hh, rfl⟩
    exact measurableModel_listUpdate hcurrent (hHmeasurable h hh) (hGmeasurable g hg)
  rcases hupdateEvents with
    ⟨hupdateUnder, hupdateOver, hupdateTwo, hupdateSwap, hupdateProduct⟩
  rcases hcurrentEvents with
    ⟨hcurrentUnder, hcurrentOver, hcurrentTwo, hcurrentSwap, hcurrentProduct⟩
  have hupdateTail :
      (finiteIIDSampleLaw law n).real updateBad ≤ delta / 2 := by
    dsimp [updateBad, updateRadius, updateDimension]
    exact finiteIID_vc_generalization_theorem7 law
      (vcDimensionAtMost_listUpdateClass current G H dG dH hvcG hvcH)
      hcount hupdateDimensionPos hdimension hupdateClassMeasurable
      (delta / 2) hdeltaHalf hupdateUnder hupdateOver hupdateTwo
      hupdateSwap hupdateProduct
  have hcurrentTail :
      (finiteIIDSampleLaw law n).real currentBad ≤ delta / 2 := by
    dsimp [currentBad, currentRadius]
    exact finiteIID_vc_generalization_theorem7 law
      (vcDimensionAtMost_singleton current) hcount (by omega) honeDimension
      (by
        intro classifier hclassifier
        have heq : classifier = current := Set.mem_singleton_iff.mp hclassifier
        subst classifier
        exact hcurrent)
      (delta / 2) hdeltaHalf hcurrentUnder hcurrentOver hcurrentTwo
      hcurrentSwap hcurrentProduct
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law n) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hsubset :
      {sample : Fin n → X × Bool |
        MeasureCertificateVCDeviationEvent law current G H
          (updateRadius + currentRadius) sample} ⊆ updateBad ∪ currentBad := by
    simpa [updateBad, currentBad] using
      measureCertificateVCDeviationEvent_subset_errorEvents law hcurrent G H
        hGmeasurable hHmeasurable updateRadius currentRadius n
  unfold MeasureCertificateVCDeviationFailure
  change (finiteIIDSampleLaw law n).real
      {sample : Fin n → X × Bool |
        MeasureCertificateVCDeviationEvent law current G H
          (updateRadius + currentRadius) sample} ≤ delta
  calc
    (finiteIIDSampleLaw law n).real
        {sample : Fin n → X × Bool |
          MeasureCertificateVCDeviationEvent law current G H
            (updateRadius + currentRadius) sample} ≤
        (finiteIIDSampleLaw law n).real (updateBad ∪ currentBad) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ (finiteIIDSampleLaw law n).real updateBad +
        (finiteIIDSampleLaw law n).real currentBad := measureReal_union_le _ _
    _ ≤ delta / 2 + delta / 2 := add_le_add hupdateTail hcurrentTail
    _ = delta := by ring

end

end GHKR22BiasBounties

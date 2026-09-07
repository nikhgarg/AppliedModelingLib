import GHKR22BiasBounties.MeasureAdaptiveChecker
import GHKR22BiasBounties.TernaryCSC

/-!
# Ternary cost-sensitive classification on arbitrary populations

This file lifts Definitions 17--19 and Theorem 20 from the executable
finite-PMF specialization to an arbitrary probability measure.  The source's
ternary reduction is distribution-free: once the binary loss and the ternary
predictor are measurable, its central equality follows by integrating the
same pointwise identity proved in `TernaryCSC`.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The source's finite ternary alphabet carries its discrete sigma algebra. -/
local instance ternaryLabelMeasurableSpace : MeasurableSpace TernaryLabel := ⊤

/-- Zero-one loss on the discrete Boolean label space is measurable. -/
theorem measurableBoundedLoss_binaryZeroOneLoss :
    MeasurableBoundedLoss binaryZeroOneLoss := by
  exact measurable_of_finite _

/-- A measurable ternary predictor induces a measurable non-deferral group. -/
theorem measurableGroup_derivedGroup
    {X : Type*} [MeasurableSpace X]
    {p : TernaryPredictor X} (hp : Measurable p) :
    MeasurableGroup (derivedGroup p) := by
  let nondefer : TernaryLabel → Bool := fun label => label != .defer
  have hnondefer : Measurable nondefer := measurable_of_finite _
  simpa [derivedGroup, nondefer, Function.comp_def] using hnondefer.comp hp

/-- A measurable ternary predictor induces a measurable binary model. -/
theorem measurableModel_derivedModel
    {X : Type*} [MeasurableSpace X]
    {p : TernaryPredictor X} (hp : Measurable p) :
    MeasurableModel (derivedModel p) := by
  have hdecode : Measurable ternaryBinaryPrediction := measurable_of_finite _
  simpa [derivedModel, ternaryBinaryPrediction, Function.comp_def] using
    hdecode.comp hp

/-- Definition 18 for an arbitrary population law. -/
def measureExpectedTernaryCost
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (p : TernaryPredictor X) : ℝ :=
  ∫ datum, inducedCost current datum (p datum.1) ∂law

/-- Definition 18's optimizer predicate on an arbitrary population law. -/
def MeasureCostSensitiveMinimizer
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X) : Prop :=
  pStar ∈ K ∧ ∀ p ∈ K,
    measureExpectedTernaryCost law current pStar ≤
      measureExpectedTernaryCost law current p

/-- Measurability of the induced ternary cost under the source primitives. -/
theorem measurable_inducedCost_comp
    {X : Type*} [MeasurableSpace X]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    {p : TernaryPredictor X} (hp : Measurable p) :
    Measurable (fun datum : X × Bool => inducedCost current datum (p datum.1)) := by
  let submission : Submission X Bool :=
    { current := current, group := derivedGroup p,
      replacement := derivedModel p }
  have hsubmission : MeasureSubmissionMeasurable submission :=
    ⟨hcurrent, measurableGroup_derivedGroup hp, measurableModel_derivedModel hp⟩
  have hscore := measurable_submissionScore
    measurableBoundedLoss_binaryZeroOneLoss hsubmission
  have heq :
      (fun datum : X × Bool => inducedCost current datum (p datum.1)) =
        fun datum => -submissionScore binaryZeroOneLoss submission datum := by
    funext datum
    exact inducedCost_eq_neg_submissionScore current p datum
  rw [heq]
  exact hscore.neg

/-- The induced ternary cost is integrable under every probability law. -/
theorem integrable_inducedCost_comp
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    {p : TernaryPredictor X} (hp : Measurable p) :
    Integrable (fun datum : X × Bool => inducedCost current datum (p datum.1)) law := by
  let submission : Submission X Bool :=
    { current := current, group := derivedGroup p,
      replacement := derivedModel p }
  have hsubmission : MeasureSubmissionMeasurable submission :=
    ⟨hcurrent, measurableGroup_derivedGroup hp, measurableModel_derivedModel hp⟩
  have hscore := integrable_submissionScore law
    measurableBoundedLoss_binaryZeroOneLoss hsubmission
  have heq :
      (fun datum : X × Bool => inducedCost current datum (p datum.1)) =
        fun datum => -submissionScore binaryZeroOneLoss submission datum := by
    funext datum
    exact inducedCost_eq_neg_submissionScore current p datum
  rw [heq]
  exact hscore.neg

/-- Expected induced cost is the negative mass-weighted certificate score for
an arbitrary measurable population. -/
theorem measureExpectedTernaryCost_eq_neg_measureCertificateImprovementScore
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (p : TernaryPredictor X) (hp : Measurable p) :
    measureExpectedTernaryCost law current p =
      -measureCertificateImprovementScore law binaryZeroOneLoss current
        (derivedGroup p) (derivedModel p) := by
  let submission : Submission X Bool :=
    { current := current, group := derivedGroup p,
      replacement := derivedModel p }
  have hsubmission : MeasureSubmissionMeasurable submission :=
    ⟨hcurrent, measurableGroup_derivedGroup hp, measurableModel_derivedModel hp⟩
  calc
    measureExpectedTernaryCost law current p =
        ∫ datum, -submissionScore binaryZeroOneLoss submission datum ∂law := by
      apply integral_congr_ae
      filter_upwards [] with datum
      exact inducedCost_eq_neg_submissionScore current p datum
    _ = -∫ datum, submissionScore binaryZeroOneLoss submission datum ∂law := by
      rw [integral_neg]
    _ = -measureCertificateImprovementScore law binaryZeroOneLoss current
          (derivedGroup p) (derivedModel p) := by
      rw [integral_submissionScore_eq_measureCertificateImprovementScore law
        measurableBoundedLoss_binaryZeroOneLoss submission hsubmission]

/-- The derived pair of a ternary predictor maximizes the arbitrary-law
certificate objective. -/
def MeasureDerivedCertificateMaximizer
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X) : Prop :=
  pStar ∈ K ∧ ∀ p ∈ K,
    measureCertificateImprovementScore law binaryZeroOneLoss current
        (derivedGroup p) (derivedModel p) ≤
      measureCertificateImprovementScore law binaryZeroOneLoss current
        (derivedGroup pStar) (derivedModel pStar)

/-- Theorem 20 on the paper's full distributional domain. -/
theorem measureTheorem20_costSensitive_minimizer_is_certificate_maximizer
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X)
    (hKmeasurable : ∀ p ∈ K, Measurable p)
    (hmin : MeasureCostSensitiveMinimizer law current K pStar) :
    MeasureDerivedCertificateMaximizer law current K pStar := by
  refine ⟨hmin.1, ?_⟩
  intro p hp
  have hcost := hmin.2 p hp
  rw [measureExpectedTernaryCost_eq_neg_measureCertificateImprovementScore
      law hcurrent pStar (hKmeasurable pStar hmin.1),
    measureExpectedTernaryCost_eq_neg_measureCertificateImprovementScore
      law hcurrent p (hKmeasurable p hp)] at hcost
  linarith

end

end GHKR22BiasBounties

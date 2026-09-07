import GHKR22BiasBounties.Core
import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.UniformHoeffding
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp

/-!
# Measure-theoretic population semantics for bias bounties

The source paper quantifies over arbitrary population distributions, not only
finite-support laws.  This file supplies that semantic layer directly with a
probability measure on labelled examples.  Predictors, groups, and the loss are
required to be measurable; these are the standard well-definedness conditions
implicit whenever the paper writes a real-valued expectation.

The finite-PMF development remains useful as an executable specialization and
for the finite-support repair of the paper's pointwise Bayes characterization.
The update and certificate calculus below has no finite-carrier assumption.
-/

namespace GHKR22BiasBounties

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- The paper's loss is measurable as a function of prediction and truth. -/
def MeasurableBoundedLoss {Y : Type*} [MeasurableSpace Y]
    (loss : BoundedLoss Y) : Prop :=
  Measurable fun pair : Y × Y => loss.value pair.1 pair.2

/-- A model has a measurable prediction map. -/
def MeasurableModel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (model : Model X Y) : Prop :=
  Measurable model

/-- A group has a measurable Boolean membership map. -/
def MeasurableGroup {X : Type*} [MeasurableSpace X]
    (group : Group X) : Prop :=
  Measurable group

/-- Measurability of the pointwise loss under measurable primitives. -/
theorem measurable_datumLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model) :
    Measurable (datumLoss loss model) := by
  exact hloss.comp (Measurable.prod
    (f := fun datum : X × Y => (model datum.1, datum.2))
    (hmodel.comp measurable_fst) measurable_snd)

/-- Measurability of the real group-membership indicator. -/
theorem measurable_groupIndicator_comp_fst
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {group : Group X} (hgroup : MeasurableGroup group) :
    Measurable (fun datum : X × Y => groupIndicator group datum.1) := by
  let encode : Bool → ℝ := fun member => if member then 1 else 0
  have hencode : Measurable encode := measurable_of_finite encode
  simpa [encode, Function.comp_def, groupIndicator] using
    hencode.comp (hgroup.comp measurable_fst)

/-- Measurability of the mass-weighted pointwise loss. -/
theorem measurable_groupWeightedDatumLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model)
    {group : Group X} (hgroup : MeasurableGroup group) :
    Measurable (fun datum : X × Y =>
      groupIndicator group datum.1 * datumLoss loss model datum) :=
  (measurable_groupIndicator_comp_fst hgroup).mul
    (measurable_datumLoss hloss hmodel)

/-- A bounded measurable pointwise loss is integrable under a probability law. -/
theorem integrable_datumLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model) :
    Integrable (datumLoss loss model) law := by
  refine Integrable.of_bound (measurable_datumLoss hloss hmodel).aestronglyMeasurable 1 ?_
  filter_upwards [] with datum
  unfold datumLoss
  rw [Real.norm_eq_abs, abs_of_nonneg (loss.nonneg _ _)]
  exact loss.le_one _ _

/-- A measurable group indicator is integrable under a probability law. -/
theorem integrable_groupIndicator_comp_fst
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {group : Group X} (hgroup : MeasurableGroup group) :
    Integrable (fun datum : X × Y => groupIndicator group datum.1) law := by
  refine Integrable.of_bound
    (measurable_groupIndicator_comp_fst hgroup).aestronglyMeasurable 1 ?_
  filter_upwards [] with datum
  cases h : group datum.1 <;> simp [groupIndicator, h]

/-- A mass-weighted bounded measurable loss is integrable. -/
theorem integrable_groupWeightedDatumLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model)
    {group : Group X} (hgroup : MeasurableGroup group) :
    Integrable (fun datum : X × Y =>
      groupIndicator group datum.1 * datumLoss loss model datum) law := by
  refine Integrable.of_bound
    (measurable_groupWeightedDatumLoss hloss hmodel hgroup).aestronglyMeasurable 1 ?_
  filter_upwards [] with datum
  cases h : group datum.1
  · simp [groupIndicator, h]
  · simp only [groupIndicator,
      AppliedModelingLib.Learning.Prediction.hardGroupIndicator, h,
      Bool.false_eq_true, ↓reduceIte, one_mul]
    unfold datumLoss
    rw [Real.norm_eq_abs, abs_of_nonneg (loss.nonneg _ _)]
    exact loss.le_one _ _

/-! ## Arbitrary-distribution versions of Definitions 1, 2, 5, and 7 -/

/-- Definition 2 for an arbitrary probability measure. -/
def measureModelLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (model : Model X Y) : ℝ :=
  ∫ datum, datumLoss loss model datum ∂law

/-- Definition 1 for an arbitrary probability measure. -/
def measureGroupMass
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (group : Group X) : ℝ :=
  ∫ datum, groupIndicator group datum.1 ∂law

/-- The arbitrary-distribution mass-weighted group-loss numerator. -/
def measureGroupLossNumerator
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (model : Model X Y) (group : Group X) : ℝ :=
  ∫ datum, groupIndicator group datum.1 * datumLoss loss model datum ∂law

/-- Conditional group loss, totalized to zero on a null group. -/
def measureGroupLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (model : Model X Y) (group : Group X) : ℝ :=
  measureGroupLossNumerator law loss model group / measureGroupMass law group

/-- The source's mass-weighted certificate objective. -/
def measureCertificateImprovementScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (current : Model X Y) (group : Group X) (replacement : Model X Y) : ℝ :=
  measureGroupMass law group *
    (measureGroupLoss law loss current group -
      measureGroupLoss law loss replacement group)

/-- Definition 5 on an arbitrary probability measure. -/
def MeasureApproxBayesOptimal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (certificates : Set (Group X × Model X Y))
    (epsilon : ℝ) (current : Model X Y) : Prop :=
  ∀ pair ∈ certificates,
    measureCertificateImprovementScore law loss current pair.1 pair.2 ≤ epsilon

/-- Definition 7 on an arbitrary probability measure. -/
def MeasureCertificateOfSuboptimality
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (current : Model X Y) (group : Group X) (replacement : Model X Y)
    (mu Delta : ℝ) : Prop :=
  0 < mu ∧ 0 < Delta ∧ mu ≤ measureGroupMass law group ∧
    measureGroupLoss law loss replacement group + Delta ≤
      measureGroupLoss law loss current group

/-- Group mass is nonnegative on every measurable population. -/
theorem measureGroupMass_nonneg
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {group : Group X} (hgroup : MeasurableGroup group) :
    0 ≤ measureGroupMass law group := by
  apply integral_nonneg_of_ae
  filter_upwards [] with datum
  cases h : group datum.1 <;> simp [groupIndicator, h]

/-- Population loss is nonnegative. -/
theorem measureModelLoss_nonneg
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model) :
    0 ≤ measureModelLoss law loss model := by
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun datum => loss.nonneg _ _

/-- Population loss is at most one. -/
theorem measureModelLoss_le_one
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model) :
    measureModelLoss law loss model ≤ 1 := by
  have hle := integral_mono (integrable_datumLoss law hloss hmodel)
    (integrable_const (1 : ℝ))
    (fun datum => loss.le_one _ _)
  simpa [measureModelLoss] using hle

/-- A group-loss numerator is nonnegative. -/
theorem measureGroupLossNumerator_nonneg
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model)
    {group : Group X} (hgroup : MeasurableGroup group) :
    0 ≤ measureGroupLossNumerator law loss model group := by
  apply integral_nonneg_of_ae
  filter_upwards [] with datum
  exact mul_nonneg (by cases h : group datum.1 <;> simp [groupIndicator, h])
    (loss.nonneg _ _)

/-- A `[0,1]` group-loss numerator is at most group mass. -/
theorem measureGroupLossNumerator_le_groupMass
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model)
    {group : Group X} (hgroup : MeasurableGroup group) :
    measureGroupLossNumerator law loss model group ≤ measureGroupMass law group := by
  apply integral_mono
  · exact integrable_groupWeightedDatumLoss law hloss hmodel hgroup
  · exact integrable_groupIndicator_comp_fst law hgroup
  · intro datum
    cases h : group datum.1
    · simp [groupIndicator, h]
    · simpa [groupIndicator, h, datumLoss] using loss.le_one (model datum.1) datum.2

/-- A null group has zero weighted loss numerator. -/
theorem measureGroupLossNumerator_eq_zero_of_mass_eq_zero
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {model : Model X Y} (hmodel : MeasurableModel model)
    {group : Group X} (hgroup : MeasurableGroup group)
    (hmass : measureGroupMass law group = 0) :
    measureGroupLossNumerator law loss model group = 0 := by
  apply le_antisymm
  · simpa [hmass] using
      measureGroupLossNumerator_le_groupMass law hloss hmodel hgroup
  · exact measureGroupLossNumerator_nonneg law hloss hmodel hgroup

/-- Clearing the conditional-loss denominator on a positive-mass group. -/
theorem measureGroupMass_mul_groupLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (model : Model X Y) (group : Group X)
    (hmass : measureGroupMass law group ≠ 0) :
    measureGroupMass law group * measureGroupLoss law loss model group =
      measureGroupLossNumerator law loss model group := by
  unfold measureGroupLoss
  field_simp

/-- The weighted score is always the difference of weighted numerators. -/
theorem measureCertificateImprovementScore_eq_numerator_sub
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {current replacement : Model X Y}
    (hcurrent : MeasurableModel current) (hreplacement : MeasurableModel replacement)
    {group : Group X} (hgroup : MeasurableGroup group) :
    measureCertificateImprovementScore law loss current group replacement =
      measureGroupLossNumerator law loss current group -
        measureGroupLossNumerator law loss replacement group := by
  by_cases hmass : measureGroupMass law group = 0
  · rw [measureGroupLossNumerator_eq_zero_of_mass_eq_zero law hloss hcurrent hgroup hmass,
      measureGroupLossNumerator_eq_zero_of_mass_eq_zero law hloss hreplacement hgroup hmass]
    simp [measureCertificateImprovementScore, hmass]
  · unfold measureCertificateImprovementScore
    rw [mul_sub, measureGroupMass_mul_groupLoss law loss current group hmass,
      measureGroupMass_mul_groupLoss law loss replacement group hmass]

/-- The mass-weighted primitive is exactly the paper's divided formula on a
positive-mass group. -/
theorem measureApproxBayesOptimal_pair_iff_source
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (epsilon : ℝ) (current replacement : Model X Y) (group : Group X)
    (hmass : 0 < measureGroupMass law group) :
    measureCertificateImprovementScore law loss current group replacement ≤ epsilon ↔
      measureGroupLoss law loss current group ≤
        measureGroupLoss law loss replacement group +
          epsilon / measureGroupMass law group := by
  unfold measureCertificateImprovementScore
  constructor <;> intro hineq
  · have hmul :
        (measureGroupLoss law loss current group -
          measureGroupLoss law loss replacement group) * measureGroupMass law group ≤
            epsilon := by nlinarith
    have hgap := (le_div_iff₀ hmass).2 hmul
    linarith
  · have hgap :
        measureGroupLoss law loss current group -
            measureGroupLoss law loss replacement group ≤
          epsilon / measureGroupMass law group := by linarith
    have hmul := (le_div_iff₀ hmass).1 hgap
    nlinarith

/-- A positive source certificate lower-bounds the weighted score. -/
theorem measureCertificate_mul_le_improvementScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {law : Measure (X × Y)} {loss : BoundedLoss Y}
    {current replacement : Model X Y} {group : Group X} {mu Delta : ℝ}
    (hcert : MeasureCertificateOfSuboptimality law loss current group replacement mu Delta) :
    mu * Delta ≤
      measureCertificateImprovementScore law loss current group replacement := by
  rcases hcert with ⟨hmu, hDelta, hmass, hgap⟩
  have hgap' : Delta ≤ measureGroupLoss law loss current group -
      measureGroupLoss law loss replacement group := by linarith
  unfold measureCertificateImprovementScore
  exact mul_le_mul hmass hgap' hDelta.le (hmass.trans' hmu.le)

/-- A positive score gives the canonical positive source certificate. -/
theorem measureCanonical_certificate_of_positive_score
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} {current replacement : Model X Y} {group : Group X}
    (hgroup : MeasurableGroup group)
    (hscore : 0 < measureCertificateImprovementScore law loss current group replacement) :
    MeasureCertificateOfSuboptimality law loss current group replacement
      (measureGroupMass law group)
      (measureGroupLoss law loss current group -
        measureGroupLoss law loss replacement group) := by
  have hmass_nonneg := measureGroupMass_nonneg law hgroup
  have hmul : 0 < measureGroupMass law group *
      (measureGroupLoss law loss current group -
        measureGroupLoss law loss replacement group) := by
    simpa [measureCertificateImprovementScore] using hscore
  have hmass_pos : 0 < measureGroupMass law group := by
    by_contra hnot
    have hzero : measureGroupMass law group = 0 :=
      le_antisymm (le_of_not_gt hnot) hmass_nonneg
    simp [hzero] at hmul
  have hgap_pos : 0 < measureGroupLoss law loss current group -
      measureGroupLoss law loss replacement group := by
    rcases mul_pos_iff.mp hmul with hpositive | hnegative
    · exact hpositive.2
    · exact False.elim ((not_lt_of_ge hmass_nonneg) hnegative.1)
  refine ⟨hmass_pos, hgap_pos, le_rfl, ?_⟩
  linarith

/-- Measure-theoretic Theorem 8. -/
theorem theorem8_measure_certificate_iff_not_approxBayesOptimal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    (loss : BoundedLoss Y)
    (certificates : Set (Group X × Model X Y))
    (certificatesMeasurable : ∀ pair ∈ certificates, MeasurableGroup pair.1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (current : Model X Y) :
    (∃ group replacement mu Delta,
        (group, replacement) ∈ certificates ∧
        MeasureCertificateOfSuboptimality law loss current group replacement mu Delta ∧
        epsilon < mu * Delta) ↔
      ¬ MeasureApproxBayesOptimal law loss certificates epsilon current := by
  constructor
  · rintro ⟨group, replacement, mu, Delta, hmem, hcert, hlarge⟩ happ
    have hbound := happ (group, replacement) hmem
    have hmul := measureCertificate_mul_le_improvementScore hcert
    linarith
  · intro hnot
    unfold MeasureApproxBayesOptimal at hnot
    push_neg at hnot
    rcases hnot with ⟨pair, hmem, hscore⟩
    have hpositive : 0 < measureCertificateImprovementScore law loss current
        pair.1 pair.2 := lt_of_le_of_lt hepsilon hscore
    refine ⟨pair.1, pair.2, measureGroupMass law pair.1,
      measureGroupLoss law loss current pair.1 -
      measureGroupLoss law loss pair.2 pair.1,
      hmem, measureCanonical_certificate_of_positive_score law
        (certificatesMeasurable pair hmem) hpositive, ?_⟩
    simpa [measureCertificateImprovementScore] using hscore

/-! ## Arbitrary-distribution Algorithm 1 and Theorems 9--10 -/

/-- ListUpdate preserves measurability. -/
theorem measurableModel_listUpdate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {current replacement : Model X Y} (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement)
    {group : Group X} (hgroup : MeasurableGroup group) :
    MeasurableModel (listUpdate current group replacement) := by
  have hset : MeasurableSet {x : X | group x = true} :=
    (measurableSet_singleton true).preimage hgroup
  simpa [MeasurableModel, listUpdate] using
    Measurable.ite hset hreplacement hcurrent

/-- The updated model has exactly the replacement's weighted group loss. -/
theorem measureListUpdate_groupLossNumerator_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (current : Model X Y) (group : Group X) (replacement : Model X Y) :
    measureGroupLossNumerator law loss (listUpdate current group replacement) group =
      measureGroupLossNumerator law loss replacement group := by
  unfold measureGroupLossNumerator
  apply integral_congr_ae
  filter_upwards [] with datum
  cases h : group datum.1 <;>
    simp [groupIndicator, listUpdate, datumLoss, h]

/-- The updated model exactly matches the replacement's conditional group loss. -/
theorem measureListUpdate_groupLoss_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (current : Model X Y) (group : Group X) (replacement : Model X Y) :
    measureGroupLoss law loss (listUpdate current group replacement) group =
      measureGroupLoss law loss replacement group := by
  simp [measureGroupLoss, measureListUpdate_groupLossNumerator_eq]

/-- Exact total-loss change under ListUpdate for an arbitrary probability law. -/
theorem measureModelLoss_sub_listUpdate_eq_numerator_sub
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {current replacement : Model X Y}
    (hcurrent : MeasurableModel current) (hreplacement : MeasurableModel replacement)
    {group : Group X} (hgroup : MeasurableGroup group) :
    measureModelLoss law loss current -
        measureModelLoss law loss (listUpdate current group replacement) =
      measureGroupLossNumerator law loss current group -
        measureGroupLossNumerator law loss replacement group := by
  have hupdate := measurableModel_listUpdate hcurrent hreplacement hgroup
  unfold measureModelLoss measureGroupLossNumerator
  rw [← integral_sub (integrable_datumLoss law hloss hcurrent)
      (integrable_datumLoss law hloss hupdate),
    ← integral_sub (integrable_groupWeightedDatumLoss law hloss hcurrent hgroup)
      (integrable_groupWeightedDatumLoss law hloss hreplacement hgroup)]
  apply integral_congr_ae
  filter_upwards [] with datum
  cases h : group datum.1 <;>
    simp [datumLoss, groupIndicator, listUpdate, h]

/-- Measure-theoretic Theorem 9. -/
theorem theorem9_measure_listUpdate_progress
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {law : Measure (X × Y)} [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {current replacement : Model X Y}
    (hcurrent : MeasurableModel current) (hreplacement : MeasurableModel replacement)
    {group : Group X} (hgroup : MeasurableGroup group) {mu Delta : ℝ}
    (hcert : MeasureCertificateOfSuboptimality law loss current group replacement mu Delta) :
    measureGroupLoss law loss (listUpdate current group replacement) group =
        measureGroupLoss law loss replacement group ∧
      measureModelLoss law loss (listUpdate current group replacement) ≤
        measureModelLoss law loss current - mu * Delta := by
  refine ⟨measureListUpdate_groupLoss_eq law loss current group replacement, ?_⟩
  have hscore := measureCertificate_mul_le_improvementScore hcert
  rw [measureCertificateImprovementScore_eq_numerator_sub law hloss
    hcurrent hreplacement hgroup] at hscore
  rw [← measureModelLoss_sub_listUpdate_eq_numerator_sub law hloss
    hcurrent hreplacement hgroup] at hscore
  linarith

/-- Every model occurring in a source update sequence is measurable. -/
def MeasureValidUpdateSequence
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ) :
    Model X Y → List (Update X Y) → Prop
  | current, [] => MeasurableModel current
  | current, update :: rest =>
      MeasurableModel current ∧ MeasurableGroup update.group ∧
        MeasurableModel update.replacement ∧
        MeasureCertificateOfSuboptimality law loss current update.group
          update.replacement update.mu update.Delta ∧
        epsilon ≤ update.mu * update.Delta ∧
        MeasureValidUpdateSequence law loss epsilon
          (listUpdate current update.group update.replacement) rest

/-- Repeated arbitrary-distribution updates lower loss by at least
`length * epsilon`. -/
theorem measureRunUpdates_loss_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (initial : Model X Y) (updates : List (Update X Y))
    (hvalid : MeasureValidUpdateSequence law loss epsilon initial updates) :
    measureModelLoss law loss (runUpdates initial updates) ≤
      measureModelLoss law loss initial - (updates.length : ℝ) * epsilon := by
  induction updates generalizing initial with
  | nil => simp [runUpdates]
  | cons update rest ih =>
      rcases hvalid with ⟨hcurrent, hgroup, hreplacement, hcert, hlarge, hrest⟩
      have hstep := (theorem9_measure_listUpdate_progress (law := law) hloss hcurrent
        hreplacement hgroup hcert).2
      have htail := ih (listUpdate initial update.group update.replacement) hrest
      simp only [runUpdates, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        measureModelLoss law loss
            (runUpdates (listUpdate initial update.group update.replacement) rest) ≤
            measureModelLoss law loss
                (listUpdate initial update.group update.replacement) -
              (rest.length : ℝ) * epsilon := htail
        _ ≤ (measureModelLoss law loss initial - update.mu * update.Delta) -
              (rest.length : ℝ) * epsilon := sub_le_sub_right hstep _
        _ ≤ measureModelLoss law loss initial -
              ((rest.length : ℝ) + 1) * epsilon := by nlinarith

/-- Measure-theoretic Theorem 10. -/
theorem theorem10_measure_update_count
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (initial : Model X Y) (updates : List (Update X Y))
    (hvalid : MeasureValidUpdateSequence law loss epsilon initial updates) :
    (updates.length : ℝ) ≤ measureModelLoss law loss initial / epsilon ∧
      measureModelLoss law loss initial / epsilon ≤ 1 / epsilon := by
  have hfinalMeasurable : MeasurableModel (runUpdates initial updates) := by
    induction updates generalizing initial with
    | nil => simpa [runUpdates] using hvalid
    | cons update rest ih =>
        rcases hvalid with ⟨hcurrent, hgroup, hreplacement, _, _, hrest⟩
        simpa [runUpdates] using ih (listUpdate initial update.group update.replacement) hrest
  have hprogress := measureRunUpdates_loss_le law hloss epsilon initial updates hvalid
  have hnonneg := measureModelLoss_nonneg law hloss hfinalMeasurable
  have hinitialMeasurable : MeasurableModel initial := by
    cases updates with
    | nil => simpa [MeasureValidUpdateSequence] using hvalid
    | cons update rest => exact hvalid.1
  have hinitialOne := measureModelLoss_le_one law hloss hinitialMeasurable
  constructor
  · apply (le_div_iff₀ hepsilon).2
    linarith
  · exact (div_le_div_iff_of_pos_right hepsilon).2 hinitialOne

end

end GHKR22BiasBounties

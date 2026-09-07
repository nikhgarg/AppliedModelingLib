import GHKR22BiasBounties.MeasureTraining

/-!
# Alternating certificate optimization on arbitrary populations

This file lifts Lemmas 21--22 and the corrected Algorithm 6/Theorem 23 to an
arbitrary measurable population.  The source's finite-sample ERM reductions
are expectation identities, so their only new premises are measurability of
the current model and candidate classes.  As in `Alternating`, the algorithm
tests both coordinate gaps before stopping; this repairs the printed update
order and yields the advertised two-sided local guarantee.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory ProbabilityTheory

/-- Binary certificate objective on an arbitrary population law. -/
def MeasureBinaryCertificateObjective
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (g : Group X) (h : Model X Bool) : ℝ :=
  measureCertificateImprovementScore law binaryZeroOneLoss current g h

/-- Fixed-group ERM over a binary model class under an arbitrary law. -/
def MeasureGroupRestrictedERM
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (g : Group X)
    (H : Set (Model X Bool)) (hStar : Model X Bool) : Prop :=
  hStar ∈ H ∧ ∀ h ∈ H,
    measureGroupLossNumerator law binaryZeroOneLoss hStar g ≤
      measureGroupLossNumerator law binaryZeroOneLoss h g

/-- Lemma 21 on an arbitrary measurable population. -/
theorem measureLemma21_groupERM_maximizes_fixed_group
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    {g : Group X} (hgMeasurable : MeasurableGroup g)
    (H : Set (Model X Bool))
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (hStar : Model X Bool)
    (herm : MeasureGroupRestrictedERM law g H hStar) :
    hStar ∈ H ∧ ∀ h ∈ H,
      MeasureBinaryCertificateObjective law current g h ≤
        MeasureBinaryCertificateObjective law current g hStar := by
  refine ⟨herm.1, ?_⟩
  intro h hh
  rw [MeasureBinaryCertificateObjective,
    measureCertificateImprovementScore_eq_numerator_sub law
      measurableBoundedLoss_binaryZeroOneLoss hcurrent (hHmeasurable h hh)
      hgMeasurable,
    MeasureBinaryCertificateObjective,
    measureCertificateImprovementScore_eq_numerator_sub law
      measurableBoundedLoss_binaryZeroOneLoss hcurrent
      (hHmeasurable hStar herm.1) hgMeasurable]
  linarith [herm.2 h hh]

/-- Pointwise disagreement loss used in Lemma 22. -/
def measureDisagreementLossIntegrand
    {X : Type*} (current replacement : Model X Bool)
    (g : Group X) (datum : X × Bool) : ℝ :=
  if current datum.1 = replacement datum.1 then 0
  else binaryZeroOneLoss.value (g datum.1)
    (disagreementLabel replacement datum)

/-- Pointwise mass where the replacement is correct and current is wrong. -/
def measureReplacementAdvantageIntegrand
    {X : Type*} (current replacement : Model X Bool)
    (datum : X × Bool) : ℝ :=
  if current datum.1 ≠ replacement datum.1 ∧
      replacement datum.1 = datum.2 then 1 else 0

/-- Unnormalized disagreement-sample risk under an arbitrary law. -/
def measureDisagreementGroupLoss
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current replacement : Model X Bool)
    (g : Group X) : ℝ :=
  ∫ datum, measureDisagreementLossIntegrand current replacement g datum ∂law

/-- Population mass on disagreements where the replacement is correct. -/
def measureReplacementAdvantageMass
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current replacement : Model X Bool) : ℝ :=
  ∫ datum, measureReplacementAdvantageIntegrand current replacement datum ∂law

/-- The disagreement-loss integrand is measurable. -/
theorem measurable_measureDisagreementLossIntegrand
    {X : Type*} [MeasurableSpace X]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement)
    {g : Group X} (hg : MeasurableGroup g) :
    Measurable (measureDisagreementLossIntegrand current replacement g) := by
  let table : (Bool × Bool) × (Bool × Bool) → ℝ := fun labels =>
    if labels.1.1 = labels.1.2 then 0
    else binaryZeroOneLoss.value labels.2.1 (labels.1.2 = labels.2.2)
  have htable : Measurable table := measurable_of_finite _
  have hlabels : Measurable (fun datum : X × Bool =>
      ((current datum.1, replacement datum.1), (g datum.1, datum.2))) :=
    ((hcurrent.comp measurable_fst).prodMk
      (hreplacement.comp measurable_fst)).prodMk
      ((hg.comp measurable_fst).prodMk measurable_snd)
  simpa [measureDisagreementLossIntegrand, disagreementLabel, table] using
    htable.comp hlabels

/-- The replacement-advantage integrand is measurable. -/
theorem measurable_measureReplacementAdvantageIntegrand
    {X : Type*} [MeasurableSpace X]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement) :
    Measurable (measureReplacementAdvantageIntegrand current replacement) := by
  let table : (Bool × Bool) × Bool → ℝ := fun labels =>
    if labels.1.1 ≠ labels.1.2 ∧ labels.1.2 = labels.2 then 1 else 0
  have htable : Measurable table := measurable_of_finite _
  have hlabels : Measurable (fun datum : X × Bool =>
      ((current datum.1, replacement datum.1), datum.2)) :=
    ((hcurrent.comp measurable_fst).prodMk
      (hreplacement.comp measurable_fst)).prodMk measurable_snd
  simpa [measureReplacementAdvantageIntegrand, table] using htable.comp hlabels

/-- The disagreement-loss integrand is bounded and integrable. -/
theorem integrable_measureDisagreementLossIntegrand
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement)
    {g : Group X} (hg : MeasurableGroup g) :
    Integrable (measureDisagreementLossIntegrand current replacement g) law := by
  refine Integrable.of_bound
    (measurable_measureDisagreementLossIntegrand hcurrent hreplacement hg).aestronglyMeasurable
    1 ?_
  filter_upwards [] with datum
  cases hcurrentValue : current datum.1 <;>
    cases hreplacementValue : replacement datum.1 <;>
    cases hgValue : g datum.1 <;> cases htruth : datum.2 <;>
    simp [measureDisagreementLossIntegrand, disagreementLabel,
      binaryZeroOneLoss, hcurrentValue, hreplacementValue, hgValue, htruth]

/-- The replacement-advantage integrand is bounded and integrable. -/
theorem integrable_measureReplacementAdvantageIntegrand
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement) :
    Integrable (measureReplacementAdvantageIntegrand current replacement) law := by
  refine Integrable.of_bound
    (measurable_measureReplacementAdvantageIntegrand hcurrent hreplacement).aestronglyMeasurable
    1 ?_
  filter_upwards [] with datum
  cases hcurrentValue : current datum.1 <;>
    cases hreplacementValue : replacement datum.1 <;> cases htruth : datum.2 <;>
    simp [measureReplacementAdvantageIntegrand, hcurrentValue,
      hreplacementValue, htruth]

/-- Exact arbitrary-law objective decomposition used in Lemma 22. -/
theorem measureBinaryCertificateObjective_eq_advantage_sub_disagreementLoss
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement)
    {g : Group X} (hg : MeasurableGroup g) :
    MeasureBinaryCertificateObjective law current g replacement =
      measureReplacementAdvantageMass law current replacement -
        measureDisagreementGroupLoss law current replacement g := by
  let submission : Submission X Bool :=
    { current := current, group := g, replacement := replacement }
  have hsubmission : MeasureSubmissionMeasurable submission :=
    ⟨hcurrent, hg, hreplacement⟩
  calc
    MeasureBinaryCertificateObjective law current g replacement =
        ∫ datum, submissionScore binaryZeroOneLoss submission datum ∂law := by
      symm
      exact integral_submissionScore_eq_measureCertificateImprovementScore law
        measurableBoundedLoss_binaryZeroOneLoss submission hsubmission
    _ = ∫ datum,
          (measureReplacementAdvantageIntegrand current replacement datum -
            measureDisagreementLossIntegrand current replacement g datum) ∂law := by
      apply integral_congr_ae
      filter_upwards [] with datum
      simpa [submission, submissionScore, datumLoss,
        measureReplacementAdvantageIntegrand,
        measureDisagreementLossIntegrand] using
        disagreement_pointwise_identity current replacement g datum
    _ = measureReplacementAdvantageMass law current replacement -
          measureDisagreementGroupLoss law current replacement g := by
      rw [integral_sub
        (integrable_measureReplacementAdvantageIntegrand law hcurrent hreplacement)
        (integrable_measureDisagreementLossIntegrand law hcurrent hreplacement hg)]
      rfl

/-- ERM over the corrected disagreement sample under an arbitrary law. -/
def MeasureDisagreementERM
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current replacement : Model X Bool)
    (G : Set (Group X)) (gStar : Group X) : Prop :=
  gStar ∈ G ∧ ∀ g ∈ G,
    measureDisagreementGroupLoss law current replacement gStar ≤
      measureDisagreementGroupLoss law current replacement g

/-- Lemma 22 on an arbitrary measurable population. -/
theorem measureLemma22_disagreementERM_maximizes_fixed_model
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current replacement : Model X Bool}
    (hcurrent : MeasurableModel current)
    (hreplacement : MeasurableModel replacement)
    (G : Set (Group X))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (gStar : Group X)
    (herm : MeasureDisagreementERM law current replacement G gStar) :
    gStar ∈ G ∧ ∀ g ∈ G,
      MeasureBinaryCertificateObjective law current g replacement ≤
        MeasureBinaryCertificateObjective law current gStar replacement := by
  refine ⟨herm.1, ?_⟩
  intro g hg
  rw [measureBinaryCertificateObjective_eq_advantage_sub_disagreementLoss
      law hcurrent hreplacement (hGmeasurable g hg),
    measureBinaryCertificateObjective_eq_advantage_sub_disagreementLoss
      law hcurrent hreplacement (hGmeasurable gStar herm.1)]
  linarith [herm.2 g hg]

/-! ## Corrected arbitrary-law Algorithm 6 -/

/-- Exact coordinate best-response oracles for the measure objective. -/
structure MeasureCoordinateBestResponses
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool)) where
  bestGroup : Model X Bool → Group X
  bestModel : Group X → Model X Bool
  bestGroup_mem : ∀ h, bestGroup h ∈ G
  bestModel_mem : ∀ g, bestModel g ∈ H
  bestGroup_max : ∀ h g, g ∈ G →
    MeasureBinaryCertificateObjective law current g h ≤
      MeasureBinaryCertificateObjective law current (bestGroup h) h
  bestModel_max : ∀ g h, h ∈ H →
    MeasureBinaryCertificateObjective law current g h ≤
      MeasureBinaryCertificateObjective law current g (bestModel g)

/-- Two-sided epsilon-coordinatewise local optimality for the measure
objective. -/
def MeasureEpsilonCoordinatewiseLocal
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (epsilon : ℝ) (pair : CertificatePair X) : Prop :=
  PairAdmissible G H pair ∧
    (∀ h ∈ H,
      MeasureBinaryCertificateObjective law current pair.group h ≤
        MeasureBinaryCertificateObjective law current pair.group
          pair.replacement + epsilon) ∧
    (∀ g ∈ G,
      MeasureBinaryCertificateObjective law current g pair.replacement ≤
        MeasureBinaryCertificateObjective law current pair.group
          pair.replacement + epsilon)

/-- One corrected coordinate-ascent step for the arbitrary-law objective. -/
def measureCoordinateAscentStep
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (pair : CertificatePair X) : Option (CertificatePair X) :=
  let modelResponse : CertificatePair X :=
    { group := pair.group, replacement := oracle.bestModel pair.group }
  if MeasureBinaryCertificateObjective law current pair.group pair.replacement + epsilon <
      MeasureBinaryCertificateObjective law current modelResponse.group
        modelResponse.replacement then
    some modelResponse
  else
    let groupResponse : CertificatePair X :=
      { group := oracle.bestGroup pair.replacement,
        replacement := pair.replacement }
    if MeasureBinaryCertificateObjective law current pair.group pair.replacement + epsilon <
        MeasureBinaryCertificateObjective law current groupResponse.group
          groupResponse.replacement then
      some groupResponse
    else
      none

/-- A halted corrected step is epsilon-coordinatewise local. -/
theorem measureEpsilonCoordinatewiseLocal_of_step_eq_none
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (pair : CertificatePair X) (hpair : PairAdmissible G H pair)
    (hhalt : measureCoordinateAscentStep law current epsilon oracle pair = none) :
    MeasureEpsilonCoordinatewiseLocal law current G H epsilon pair := by
  unfold measureCoordinateAscentStep at hhalt
  dsimp only at hhalt
  split at hhalt
  · contradiction
  next hmodel =>
    split at hhalt
    · contradiction
    next hgroup =>
      refine ⟨hpair, ?_, ?_⟩
      · intro h hh
        exact le_trans (oracle.bestModel_max pair.group h hh)
          (le_of_not_gt hmodel)
      · intro g hg
        exact le_trans (oracle.bestGroup_max pair.replacement g hg)
          (le_of_not_gt hgroup)

/-- A successful corrected step remains in the two candidate classes. -/
theorem measurePairAdmissible_of_step_eq_some
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (pair next : CertificatePair X) (hpair : PairAdmissible G H pair)
    (hstep : measureCoordinateAscentStep law current epsilon oracle pair = some next) :
    PairAdmissible G H next := by
  unfold measureCoordinateAscentStep at hstep
  dsimp only at hstep
  split at hstep
  · simp only [Option.some.injEq] at hstep
    subst next
    exact ⟨hpair.1, oracle.bestModel_mem pair.group⟩
  next _ =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst next
      exact ⟨oracle.bestGroup_mem pair.replacement, hpair.2⟩
    · contradiction

/-- Every successful corrected step improves the measure objective by more
than epsilon. -/
theorem measureCoordinateAscentStep_improves
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (pair next : CertificatePair X)
    (hstep : measureCoordinateAscentStep law current epsilon oracle pair = some next) :
    MeasureBinaryCertificateObjective law current pair.group pair.replacement + epsilon <
      MeasureBinaryCertificateObjective law current next.group next.replacement := by
  unfold measureCoordinateAscentStep at hstep
  dsimp only at hstep
  split at hstep
  next hmodel =>
    simp only [Option.some.injEq] at hstep
    subst next
    exact hmodel
  next _ =>
    split at hstep
    next hgroup =>
      simp only [Option.some.injEq] at hstep
      subst next
      exact hgroup
    next _ => contradiction

/-- Fuelled corrected Algorithm 6 for an arbitrary population law. -/
def measureCoordinateAscentLoop
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H) :
    ℕ → CertificatePair X → Option (CertificatePair X)
  | 0, pair =>
      match measureCoordinateAscentStep law current epsilon oracle pair with
      | none => some pair
      | some _ => none
  | fuel + 1, pair =>
      match measureCoordinateAscentStep law current epsilon oracle pair with
      | none => some pair
      | some next =>
          measureCoordinateAscentLoop law current epsilon oracle fuel next

/-- Every successful Algorithm 6 result is epsilon-coordinatewise local. -/
theorem measureTheorem23_coordinateAscentLoop_local
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (fuel : ℕ) (initial output : CertificatePair X)
    (hinitial : PairAdmissible G H initial)
    (houtput : measureCoordinateAscentLoop law current epsilon oracle fuel initial =
      some output) :
    MeasureEpsilonCoordinatewiseLocal law current G H epsilon output := by
  induction fuel generalizing initial with
  | zero =>
      unfold measureCoordinateAscentLoop at houtput
      cases hstep : measureCoordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact measureEpsilonCoordinatewiseLocal_of_step_eq_none
            law current epsilon oracle initial hinitial hstep
      | some next => simp [hstep] at houtput
  | succ fuel ih =>
      unfold measureCoordinateAscentLoop at houtput
      cases hstep : measureCoordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact measureEpsilonCoordinatewiseLocal_of_step_eq_none
            law current epsilon oracle initial hinitial hstep
      | some next =>
          simp only [hstep] at houtput
          exact ih next
            (measurePairAdmissible_of_step_eq_some law current epsilon oracle
              initial next hinitial hstep)
            houtput

/-- A successful arbitrary-law coordinate-ascent run never lowers its
objective when `epsilon` is nonnegative. -/
theorem measureCoordinateAscentLoop_objective_mono
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (fuel : ℕ) (initial output : CertificatePair X)
    (houtput : measureCoordinateAscentLoop law current epsilon oracle fuel initial =
      some output) :
    MeasureBinaryCertificateObjective law current initial.group
        initial.replacement ≤
      MeasureBinaryCertificateObjective law current output.group
        output.replacement := by
  induction fuel generalizing initial with
  | zero =>
      unfold measureCoordinateAscentLoop at houtput
      cases hstep : measureCoordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact le_rfl
      | some next => simp [hstep] at houtput
  | succ fuel ih =>
      unfold measureCoordinateAscentLoop at houtput
      cases hstep : measureCoordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact le_rfl
      | some next =>
          simp only [hstep] at houtput
          have hfirst := measureCoordinateAscentStep_improves
            law current epsilon oracle initial next hstep
          have htail := ih next houtput
          exact le_trans (by linarith) htail

/-- Fuel exhaustion exposes `fuel + 1` strict improvements and preserves
admissibility of the terminal pair. -/
theorem measureCoordinateAscentLoop_none_objective_budget
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : MeasureCoordinateBestResponses law current G H)
    (fuel : ℕ) (initial : CertificatePair X)
    (hinitial : PairAdmissible G H initial)
    (hexhausted : measureCoordinateAscentLoop law current epsilon oracle fuel initial =
      none) :
    ∃ final : CertificatePair X,
      PairAdmissible G H final ∧
        MeasureBinaryCertificateObjective law current initial.group
            initial.replacement + ((fuel : ℝ) + 1) * epsilon <
          MeasureBinaryCertificateObjective law current final.group
            final.replacement := by
  induction fuel generalizing initial with
  | zero =>
      unfold measureCoordinateAscentLoop at hexhausted
      cases hstep : measureCoordinateAscentStep law current epsilon oracle initial with
      | none => simp [hstep] at hexhausted
      | some next =>
          refine ⟨next,
            measurePairAdmissible_of_step_eq_some law current epsilon oracle
              initial next hinitial hstep, ?_⟩
          have himproves := measureCoordinateAscentStep_improves
            law current epsilon oracle initial next hstep
          simpa using himproves
  | succ fuel ih =>
      unfold measureCoordinateAscentLoop at hexhausted
      cases hstep : measureCoordinateAscentStep law current epsilon oracle initial with
      | none => simp [hstep] at hexhausted
      | some next =>
          simp only [hstep] at hexhausted
          have hnext := measurePairAdmissible_of_step_eq_some
            law current epsilon oracle initial next hinitial hstep
          obtain ⟨final, hfinal, htail⟩ := ih next hnext hexhausted
          have hfirst := measureCoordinateAscentStep_improves
            law current epsilon oracle initial next hstep
          refine ⟨final, hfinal, ?_⟩
          push_cast
          nlinarith

/-- Every measurable binary certificate objective lies in `[-1,1]`. -/
theorem measureBinaryCertificateObjective_mem_Icc
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (pair : CertificatePair X)
    (hgroup : MeasurableGroup pair.group)
    (hreplacement : MeasurableModel pair.replacement) :
    MeasureBinaryCertificateObjective law current pair.group pair.replacement ∈
      Set.Icc (-1 : ℝ) 1 := by
  let submission : Submission X Bool :=
    { current := current, group := pair.group,
      replacement := pair.replacement }
  have hsubmission : MeasureSubmissionMeasurable submission :=
    ⟨hcurrent, hgroup, hreplacement⟩
  have hscoreIntegrable := integrable_submissionScore law
    measurableBoundedLoss_binaryZeroOneLoss hsubmission
  have hscoreEq :
      MeasureBinaryCertificateObjective law current pair.group pair.replacement =
        ∫ datum, submissionScore binaryZeroOneLoss submission datum ∂law := by
    symm
    exact integral_submissionScore_eq_measureCertificateImprovementScore law
      measurableBoundedLoss_binaryZeroOneLoss submission hsubmission
  rw [hscoreEq]
  constructor
  · have hlower := integral_mono (integrable_const (-1 : ℝ))
        hscoreIntegrable (fun datum =>
          (submissionScore_mem_Icc binaryZeroOneLoss submission datum).1)
    simpa using hlower
  · have hupper := integral_mono hscoreIntegrable (integrable_const (1 : ℝ))
        (fun datum =>
          (submissionScore_mem_Icc binaryZeroOneLoss submission datum).2)
    simpa using hupper

/-- The corrected arbitrary-law Algorithm 6 terminates once its fuel covers
the full objective range. -/
theorem measureCoordinateAscentLoop_terminates_of_budget
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (epsilon : ℝ) (_hepsilon : 0 < epsilon)
    (oracle : MeasureCoordinateBestResponses law current G H)
    (fuel : ℕ) (hbudget : 2 ≤ ((fuel : ℝ) + 1) * epsilon)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial) :
    ∃ output,
      measureCoordinateAscentLoop law current epsilon oracle fuel initial =
        some output := by
  cases hresult : measureCoordinateAscentLoop law current epsilon oracle fuel initial with
  | some output => exact ⟨output, rfl⟩
  | none =>
      obtain ⟨final, hfinal, himproves⟩ :=
        measureCoordinateAscentLoop_none_objective_budget law current epsilon
          oracle fuel initial hinitial hresult
      have hinitialBound := measureBinaryCertificateObjective_mem_Icc law
        hcurrent initial (hGmeasurable initial.group hinitial.1)
          (hHmeasurable initial.replacement hinitial.2)
      have hfinalBound := measureBinaryCertificateObjective_mem_Icc law
        hcurrent final (hGmeasurable final.group hfinal.1)
          (hHmeasurable final.replacement hfinal.2)
      exfalso
      nlinarith [hinitialBound.1, hfinalBound.2]

/-- Total corrected Theorem 23 on an arbitrary measurable population. -/
theorem measureTheorem23_coordinateAscentLoop_total
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (oracle : MeasureCoordinateBestResponses law current G H)
    (fuel : ℕ) (hbudget : 2 ≤ ((fuel : ℝ) + 1) * epsilon)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial) :
    ∃ output,
      measureCoordinateAscentLoop law current epsilon oracle fuel initial =
          some output ∧
        MeasureEpsilonCoordinatewiseLocal law current G H epsilon output := by
  obtain ⟨output, houtput⟩ := measureCoordinateAscentLoop_terminates_of_budget
    law hcurrent G H hGmeasurable hHmeasurable epsilon hepsilon oracle
      fuel hbudget initial hinitial
  exact ⟨output, houtput,
    measureTheorem23_coordinateAscentLoop_local law current epsilon oracle
      fuel initial output hinitial houtput⟩

/-- If Algorithm 6 starts from a positive measurable certificate objective,
the repaired arbitrary-law loop returns a positive certificate together with
the advertised two-sided local guarantee. -/
theorem measureTheorem23_coordinateAscentLoop_positive_certificate
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (oracle : MeasureCoordinateBestResponses law current G H)
    (fuel : ℕ) (hbudget : 2 ≤ ((fuel : ℝ) + 1) * epsilon)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial)
    (hpositive : 0 < MeasureBinaryCertificateObjective law current
      initial.group initial.replacement) :
    ∃ output,
      measureCoordinateAscentLoop law current epsilon oracle fuel initial =
          some output ∧
        MeasureEpsilonCoordinatewiseLocal law current G H epsilon output ∧
        MeasureCertificateOfSuboptimality law binaryZeroOneLoss current
          output.group output.replacement (measureGroupMass law output.group)
          (measureGroupLoss law binaryZeroOneLoss current output.group -
            measureGroupLoss law binaryZeroOneLoss output.replacement
              output.group) := by
  obtain ⟨output, houtput, hlocal⟩ :=
    measureTheorem23_coordinateAscentLoop_total law hcurrent G H
      hGmeasurable hHmeasurable epsilon hepsilon oracle fuel hbudget initial
      hinitial
  have hmono := measureCoordinateAscentLoop_objective_mono law current epsilon
    hepsilon.le oracle fuel initial output houtput
  have houtputPositive :
      0 < MeasureBinaryCertificateObjective law current output.group
        output.replacement := lt_of_lt_of_le hpositive hmono
  exact ⟨output, houtput, hlocal,
    measureCanonical_certificate_of_positive_score law
      (hGmeasurable output.group hlocal.1.1) houtputPositive⟩

/-- A source-shaped sequence of epsilon-improving measure-objective updates. -/
def MeasureImprovingCoordinateSequence
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool) (epsilon : ℝ) :
    CertificatePair X → List (CertificatePair X) → Prop
  | _, [] => True
  | pair, next :: rest =>
      MeasureBinaryCertificateObjective law current pair.group pair.replacement + epsilon ≤
          MeasureBinaryCertificateObjective law current next.group next.replacement ∧
        MeasureImprovingCoordinateSequence law current epsilon next rest

/-- Repeated coordinate improvements accumulate linearly. -/
theorem measureImprovingCoordinateSequence_objective_gain
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (current : Model X Bool) (epsilon : ℝ)
    (initial : CertificatePair X) (updates : List (CertificatePair X))
    (hsequence : MeasureImprovingCoordinateSequence law current epsilon
      initial updates) :
    MeasureBinaryCertificateObjective law current initial.group initial.replacement +
        (updates.length : ℝ) * epsilon ≤
      MeasureBinaryCertificateObjective law current
        (updates.getLastD initial).group
        (updates.getLastD initial).replacement := by
  induction updates generalizing initial with
  | nil => simp
  | cons next rest ih =>
      rcases hsequence with ⟨hstep, hrest⟩
      have htail := ih next hrest
      cases rest with
      | nil =>
          simp at htail ⊢
          linarith
      | cons later tail =>
          rw [List.getLastD_cons] at htail
          have htail' :
              MeasureBinaryCertificateObjective law current next.group next.replacement +
                  ((tail.length : ℝ) + 1) * epsilon ≤
                MeasureBinaryCertificateObjective law current
                  (tail.getLastD later).group (tail.getLastD later).replacement := by
            simpa [List.length_cons] using htail
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
            List.getLastD_cons]
          nlinarith

/-- Theorem 23 runtime on arbitrary populations: an epsilon-improving
trajectory cannot contain more than `2 / epsilon` updates. -/
theorem measureTheorem23_coordinate_update_bound
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (initial : CertificatePair X) (updates : List (CertificatePair X))
    (hsequence : MeasureImprovingCoordinateSequence law current epsilon
      initial updates)
    (hinitialGroup : MeasurableGroup initial.group)
    (hinitialModel : MeasurableModel initial.replacement)
    (hfinalGroup : MeasurableGroup (updates.getLastD initial).group)
    (hfinalModel : MeasurableModel (updates.getLastD initial).replacement) :
    (updates.length : ℝ) ≤ 2 / epsilon := by
  have hgain := measureImprovingCoordinateSequence_objective_gain law current
    epsilon initial updates hsequence
  have hinitialBound := measureBinaryCertificateObjective_mem_Icc law hcurrent
    initial hinitialGroup hinitialModel
  have hfinalBound := measureBinaryCertificateObjective_mem_Icc law hcurrent
    (updates.getLastD initial) hfinalGroup hfinalModel
  apply (le_div_iff₀ hepsilon).2
  nlinarith [hinitialBound.1, hfinalBound.2]

/-- A positive arbitrary-law local objective is a genuine source
certificate.  Positivity is separate from coordinatewise local optimality,
as required by the formal counterexample to the printed Theorem 23. -/
theorem measureLocal_pair_certificate_of_positive_objective
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (current : Model X Bool) (pair : CertificatePair X)
    (hgroup : MeasurableGroup pair.group)
    (hpositive : 0 < MeasureBinaryCertificateObjective law current
      pair.group pair.replacement) :
    MeasureCertificateOfSuboptimality law binaryZeroOneLoss current pair.group
      pair.replacement (measureGroupMass law pair.group)
      (measureGroupLoss law binaryZeroOneLoss current pair.group -
        measureGroupLoss law binaryZeroOneLoss pair.replacement pair.group) := by
  exact measureCanonical_certificate_of_positive_score law hgroup hpositive

/-- Canonical rounded fuel for the corrected Algorithm 6.  Since the loop
with fuel `F` can inspect at most `F + 1` pairs, subtracting one makes the
literal number of coordinate-response rounds exactly `ceil (2 / epsilon)`.
Each round evaluates the model response and, only if needed, the group
response, so this is also an upper bound on the number of calls to either
best-response oracle. -/
noncomputable def measureCoordinateAscentFuel (epsilon : ℝ) : ℕ :=
  Nat.ceil (2 / epsilon) - 1

/-- The canonical fuel permits exactly `ceil (2 / epsilon)` loop rounds. -/
theorem measureCoordinateAscentFuel_rounds
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    measureCoordinateAscentFuel epsilon + 1 = Nat.ceil (2 / epsilon) := by
  have hratio : 0 < 2 / epsilon := div_pos (by norm_num) hepsilon
  have hceil : 0 < Nat.ceil (2 / epsilon) := Nat.ceil_pos.mpr hratio
  unfold measureCoordinateAscentFuel
  omega

/-- The rounded fuel covers the full objective range. -/
theorem measureCoordinateAscentFuel_budget
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    2 ≤ ((measureCoordinateAscentFuel epsilon : ℝ) + 1) * epsilon := by
  have hrounds := measureCoordinateAscentFuel_rounds epsilon hepsilon
  have hle : 2 / epsilon ≤ ((measureCoordinateAscentFuel epsilon : ℝ) + 1) := by
    have hceil : 2 / epsilon ≤ (Nat.ceil (2 / epsilon) : ℝ) := Nat.le_ceil _
    rw [← hrounds] at hceil
    exact_mod_cast hceil
  have hmul := mul_le_mul_of_nonneg_right hle hepsilon.le
  have hnormalize : (2 / epsilon) * epsilon = 2 := by
    field_simp
  nlinarith

/-- Source-rounded arbitrary-law Theorem 23. -/
theorem measureTheorem23_coordinateAscent_sourceRounded
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (oracle : MeasureCoordinateBestResponses law current G H)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial) :
    ∃ output,
      measureCoordinateAscentLoop law current epsilon oracle
          (measureCoordinateAscentFuel epsilon) initial = some output ∧
        MeasureEpsilonCoordinatewiseLocal law current G H epsilon output := by
  exact measureTheorem23_coordinateAscentLoop_total law hcurrent G H
    hGmeasurable hHmeasurable epsilon hepsilon oracle
    (measureCoordinateAscentFuel epsilon)
    (measureCoordinateAscentFuel_budget epsilon hepsilon) initial hinitial

/-- Source-rounded arbitrary-law Theorem 23 with the paper's positive
certificate conclusion recovered from positive initialization. -/
theorem measureTheorem23_coordinateAscent_sourceRounded_positive_certificate
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    {current : Model X Bool} (hcurrent : MeasurableModel current)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (oracle : MeasureCoordinateBestResponses law current G H)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial)
    (hpositive : 0 < MeasureBinaryCertificateObjective law current
      initial.group initial.replacement) :
    ∃ output,
      measureCoordinateAscentLoop law current epsilon oracle
          (measureCoordinateAscentFuel epsilon) initial = some output ∧
        MeasureEpsilonCoordinatewiseLocal law current G H epsilon output ∧
        MeasureCertificateOfSuboptimality law binaryZeroOneLoss current
          output.group output.replacement (measureGroupMass law output.group)
          (measureGroupLoss law binaryZeroOneLoss current output.group -
            measureGroupLoss law binaryZeroOneLoss output.replacement
              output.group) := by
  exact measureTheorem23_coordinateAscentLoop_positive_certificate law hcurrent
    G H hGmeasurable hHmeasurable epsilon hepsilon oracle
    (measureCoordinateAscentFuel epsilon)
    (measureCoordinateAscentFuel_budget epsilon hepsilon) initial hinitial
    hpositive

end

end GHKR22BiasBounties

import PG24NoisyMatchingMarkets.Theorem2TwoScalePrimitiveBridge

/-!
# PG24 Theorem 2 iid block event

The local small-firm proof needs the probability that a student can afford a
small-block college while affording no large-block college.  This file derives
that factorization directly from the iid noise product law for disjoint
blocks, before any matching or capacity argument is used.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

private def theorem2CutoffCrossingSet
    {n : ℕ} (active : Finset (Fin n)) (value : ℝ)
    (cutoff : Fin n -> ℝ) : Set (Fin n -> ℝ) :=
  {noise | cutoffCrossedOn active (noisyScore value noise) cutoff}

private theorem theorem2CutoffCrossingSet_measurable
    {n : ℕ} (active : Finset (Fin n)) (value : ℝ)
    (cutoff : Fin n -> ℝ) :
    MeasurableSet (theorem2CutoffCrossingSet active value cutoff) := by
  classical
  let collegeEvent : Fin n -> Set (Fin n -> ℝ) :=
    fun c => {noise | cutoff c < value + noise c}
  have hset :
      theorem2CutoffCrossingSet active value cutoff =
        ⋃ c ∈ active, collegeEvent c := by
    ext noise
    simp [theorem2CutoffCrossingSet, collegeEvent, cutoffCrossedOn, noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore : Measurable (fun noise : Fin n -> ℝ => value + noise c) := by
    fun_prop
  change MeasurableSet {noise : Fin n -> ℝ | cutoff c < value + noise c}
  exact measurableSet_Ioi.preimage hscore

/--
The primitive iid noise event used in the small-firm argument: some small
cutoff is crossed and no large cutoff is crossed.
-/
def theorem2SmallOnlyAffordanceEvent
    {n : ℕ} (small large : Finset (Fin n)) (value : ℝ)
    (cutoff : Fin n -> ℝ) : (Fin n -> ℝ) -> Prop :=
  fun noise =>
    cutoffCrossedOn small (noisyScore value noise) cutoff ∧
      ¬ cutoffCrossedOn large (noisyScore value noise) cutoff

/--
For disjoint iid blocks, the small-only event has probability
`pSmall * (1 - pLarge)`.  This is the product-law calculation used implicitly
in `proof-amplifying.tex:220-250`.
-/
theorem theorem2_iid_smallOnlyAffordance_probability
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    (value : ℝ) (cutoff : Fin n -> ℝ) :
    (Measure.pi (fun _ : Fin n => noiseLaw)).real
        {noise : Fin n -> ℝ |
          theorem2SmallOnlyAffordanceEvent small large value cutoff noise} =
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) small value cutoff *
        (1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large value cutoff) := by
  classical
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let smallSet : Set (Fin n -> ℝ) :=
    theorem2CutoffCrossingSet small value cutoff
  let largeSet : Set (Fin n -> ℝ) :=
    theorem2CutoffCrossingSet large value cutoff
  let unionSet : Set (Fin n -> ℝ) :=
    theorem2CutoffCrossingSet (small ∪ large) value cutoff
  let smallOnlySet : Set (Fin n -> ℝ) :=
    {noise | theorem2SmallOnlyAffordanceEvent small large value cutoff noise}
  have hsmall_meas : MeasurableSet smallSet :=
    theorem2CutoffCrossingSet_measurable small value cutoff
  have hlarge_meas : MeasurableSet largeSet :=
    theorem2CutoffCrossingSet_measurable large value cutoff
  have hunion_meas : MeasurableSet unionSet :=
    theorem2CutoffCrossingSet_measurable (small ∪ large) value cutoff
  have hunion : unionSet = smallSet ∪ largeSet := by
    ext noise
    simp only [unionSet, smallSet, largeSet, theorem2CutoffCrossingSet]
    exact cutoffCrossedOn_union_iff
  have hsmallOnly : smallOnlySet = largeSetᶜ \ unionSetᶜ := by
    ext noise
    simp only [smallOnlySet, theorem2SmallOnlyAffordanceEvent, largeSet,
      unionSet, theorem2CutoffCrossingSet,
      Set.mem_diff, Set.mem_compl_iff]
    change
      (cutoffCrossedOn small (noisyScore value noise) cutoff ∧
        ¬ cutoffCrossedOn large (noisyScore value noise) cutoff) ↔
      (¬ cutoffCrossedOn large (noisyScore value noise) cutoff ∧
        ¬ ¬ cutoffCrossedOn (small ∪ large) (noisyScore value noise) cutoff)
    rw [cutoffCrossedOn_union_iff]
    tauto
  have hsubset : unionSetᶜ ⊆ largeSetᶜ := by
    intro noise hno_union hlarge
    apply hno_union
    rw [hunion]
    exact Or.inr hlarge
  have hdiff :
      productLaw.real (largeSetᶜ \ unionSetᶜ) =
        productLaw.real largeSetᶜ - productLaw.real unionSetᶜ :=
    measureReal_diff hsubset hunion_meas.compl
  have hlarge_compl :
      productLaw.real largeSetᶜ =
        1 - cutoffAffordanceProbability productLaw large value cutoff := by
    rw [probReal_compl_eq_one_sub (μ := productLaw) hlarge_meas]
    rfl
  have hunion_compl :
      productLaw.real unionSetᶜ =
        1 - cutoffAffordanceProbability productLaw (small ∪ large) value cutoff := by
    rw [probReal_compl_eq_one_sub (μ := productLaw) hunion_meas]
    rfl
  have hsmall_formula :
      cutoffAffordanceProbability productLaw small value cutoff =
        1 - ∏ c ∈ small,
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value)) := by
    exact cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw small value cutoff
  have hlarge_formula :
      cutoffAffordanceProbability productLaw large value cutoff =
        1 - ∏ c ∈ large,
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value)) := by
    exact cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw large value cutoff
  have hunion_formula :
      cutoffAffordanceProbability productLaw (small ∪ large) value cutoff =
        1 - ∏ c ∈ (small ∪ large),
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value)) := by
    exact cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw (small ∪ large) value cutoff
  have hprod :
      (∏ c ∈ (small ∪ large),
        (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value))) =
        (∏ c ∈ small,
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value))) *
        (∏ c ∈ large,
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value))) := by
    exact Finset.prod_union hdisjoint
  have hprob :
      productLaw.real smallOnlySet =
        cutoffAffordanceProbability productLaw small value cutoff *
          (1 - cutoffAffordanceProbability productLaw large value cutoff) := by
    rw [hsmallOnly, hdiff, hlarge_compl, hunion_compl]
    rw [hsmall_formula, hlarge_formula, hunion_formula, hprod]
    ring
  simpa [productLaw, smallOnlySet] using hprob

/-- The same small-only event on the source model's joint value/noise space. -/
def theorem2SmallOnlyAffordanceProductEvent
    {n : ℕ} (small large : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    ℝ × (Fin n -> ℝ) -> Prop :=
  fun outcome =>
    theorem2SmallOnlyAffordanceEvent small large outcome.1 cutoff outcome.2

private theorem theorem2ProductCrossingEvent_measurable
    {n : ℕ} (active : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {outcome : ℝ × (Fin n -> ℝ) |
        cutoffCrossedOn active (noisyScore outcome.1 outcome.2) cutoff} := by
  classical
  let collegeEvent : Fin n -> Set (ℝ × (Fin n -> ℝ)) :=
    fun c => {outcome | cutoff c < outcome.1 + outcome.2 c}
  have hset :
      {outcome : ℝ × (Fin n -> ℝ) |
        cutoffCrossedOn active (noisyScore outcome.1 outcome.2) cutoff} =
        ⋃ c ∈ active, collegeEvent c := by
    ext outcome
    simp [collegeEvent, cutoffCrossedOn, noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore :
      Measurable (fun outcome : ℝ × (Fin n -> ℝ) => outcome.1 + outcome.2 c) := by
    fun_prop
  change MeasurableSet
    {outcome : ℝ × (Fin n -> ℝ) | cutoff c < outcome.1 + outcome.2 c}
  exact measurableSet_Ioi.preimage hscore

/-- The joint small-only product event is measurable without any matching premise. -/
theorem theorem2SmallOnlyAffordanceProductEvent_measurable
    {n : ℕ} (small large : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {outcome : ℝ × (Fin n -> ℝ) |
        theorem2SmallOnlyAffordanceProductEvent small large cutoff outcome} := by
  change MeasurableSet
    ({outcome : ℝ × (Fin n -> ℝ) |
      cutoffCrossedOn small (noisyScore outcome.1 outcome.2) cutoff} ∩
      {outcome : ℝ × (Fin n -> ℝ) |
        cutoffCrossedOn large (noisyScore outcome.1 outcome.2) cutoff}ᶜ)
  exact (theorem2ProductCrossingEvent_measurable small cutoff).inter
    (theorem2ProductCrossingEvent_measurable large cutoff).compl

/-- Every value section of the joint small-only event is measurable. -/
theorem theorem2SmallOnlyAffordanceProductEvent_section_measurable
    {n : ℕ} (small large : Finset (Fin n)) (value : ℝ)
    (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {noise : Fin n -> ℝ |
        theorem2SmallOnlyAffordanceProductEvent small large cutoff (value, noise)} := by
  change MeasurableSet
    ({noise : Fin n -> ℝ |
      cutoffCrossedOn small (noisyScore value noise) cutoff} ∩
      {noise : Fin n -> ℝ |
        cutoffCrossedOn large (noisyScore value noise) cutoff}ᶜ)
  exact (theorem2CutoffCrossingSet_measurable small value cutoff).inter
    (theorem2CutoffCrossingSet_measurable large value cutoff).compl

/--
Source demand semantics imply the primitive small-only event is a chosen-small
event.  The hypotheses are local model rules: matching occurs exactly when a
college is affordable, and any chosen college is affordable.  They contain no
tail or convergence conclusion.
-/
theorem theorem2_chosenInSmall_of_smallOnly_affordance
    {n : ℕ} (small large : Finset (Fin n))
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    (cutoff : Fin n -> ℝ)
    (choice : ℝ × (Fin n -> ℝ) -> Option (Fin n))
    (hmatched_iff_affordable : ∀ outcome : ℝ × (Fin n -> ℝ),
      choice outcome ≠ none ↔
        cutoffCrossedOn (Finset.univ : Finset (Fin n))
          (noisyScore outcome.1 outcome.2) cutoff)
    (hchosen_affordable : ∀ (outcome : ℝ × (Fin n -> ℝ)) (college : Fin n),
      choice outcome = some college → cutoff college < outcome.1 + outcome.2 college) :
    ∀ outcome : ℝ × (Fin n -> ℝ),
      theorem2SmallOnlyAffordanceProductEvent small large cutoff outcome →
        chosenInActive choice small outcome := by
  intro outcome hsmallOnly
  rcases hsmallOnly with ⟨hsmall, hnot_large⟩
  have hwhole_cross :
      cutoffCrossedOn (Finset.univ : Finset (Fin n))
        (noisyScore outcome.1 outcome.2) cutoff := by
    rcases hsmall with ⟨college, hcollege_small, hcross⟩
    exact ⟨college, by simp, hcross⟩
  have hmatched : choice outcome ≠ none :=
    (hmatched_iff_affordable outcome).mpr hwhole_cross
  cases hchoice : choice outcome with
  | none => exact False.elim (hmatched hchoice)
  | some college =>
      refine ⟨college, ?_, hchoice⟩
      have hcollege_cross : cutoff college < outcome.1 + outcome.2 college :=
        hchosen_affordable outcome college hchoice
      have hcollege_union : college ∈ small ∪ large := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hcollege_union with hcollege_small | hcollege_large
      · exact hcollege_small
      · exfalso
        apply hnot_large
        exact ⟨college, hcollege_large, by
          simpa [noisyScore] using hcollege_cross⟩

/--
The off-diagonal residual factor gives a pointwise lower bound on the iid
small-only event once the large-block affordability probability is bounded.
-/
theorem theorem2_twoScale_smallOnly_probability_lower_bound
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    {totalSupply delta endpoint sigma value : ℝ} (cutoff : Fin n -> ℝ)
    (hresidual :
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large value cutoff) :
    theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) small value cutoff ≤
      (Measure.pi (fun _ : Fin n => noiseLaw)).real
        {noise : Fin n -> ℝ |
          theorem2SmallOnlyAffordanceEvent small large value cutoff noise} := by
  have hsmall_nonneg :
      0 ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) small value cutoff :=
    cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin n => noiseLaw)) small value cutoff
  have hmul := mul_le_mul_of_nonneg_left hresidual hsmall_nonneg
  rw [theorem2_iid_smallOnlyAffordance_probability
    noiseLaw small large hdisjoint value cutoff]
  simpa [mul_comm] using hmul

/--
The value-indexed iid small-only probability kernel is integrable under every
probability value law.  This is derived from the bounded affordability
probabilities rather than postulated as part of an endpoint package.
-/
theorem theorem2_iid_smallOnly_probability_integrable
    {n : ℕ} (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    (cutoff : Fin n -> ℝ) :
    Integrable
      (fun value : ℝ =>
        (Measure.pi (fun _ : Fin n => noiseLaw)).real
          {noise : Fin n -> ℝ |
            theorem2SmallOnlyAffordanceEvent small large value cutoff noise})
      valueLaw := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pSmall : ℝ -> ℝ :=
    fun value => cutoffAffordanceProbability productLaw small value cutoff
  let pLarge : ℝ -> ℝ :=
    fun value => cutoffAffordanceProbability productLaw large value cutoff
  have hpSmall_integrable : Integrable pSmall valueLaw := by
    simpa [pSmall, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw small cutoff)
  have hpSmall_meas : Measurable pSmall := by
    exact
      (AppliedModelingLib.Matching.cutoffCrossingProbability_monotone_value
        productLaw small cutoff).measurable
  have hpLarge_meas : Measurable pLarge := by
    exact
      (AppliedModelingLib.Matching.cutoffCrossingProbability_monotone_value
        productLaw large cutoff).measurable
  have hproduct_meas : AEStronglyMeasurable
      (fun value : ℝ => pSmall value * (1 - pLarge value)) valueLaw := by
    exact (hpSmall_meas.mul (measurable_const.sub hpLarge_meas)).aestronglyMeasurable
  have hproduct_bound : ∀ᶠ value : ℝ in ae valueLaw,
      ‖pSmall value * (1 - pLarge value)‖ ≤ pSmall value := by
    filter_upwards with value
    have hlarge_nonneg : 0 ≤ pLarge value := by
      exact cutoffAffordanceProbability_nonneg productLaw large value cutoff
    have hlarge_le_one : pLarge value ≤ 1 := by
      exact cutoffAffordanceProbability_le_one productLaw large value cutoff
    have hfactor_nonneg : 0 ≤ 1 - pLarge value := by linarith
    have hfactor_le_one : 1 - pLarge value ≤ 1 := by linarith
    have hfactor_abs : |1 - pLarge value| ≤ 1 := by
      simpa [abs_of_nonneg hfactor_nonneg] using hfactor_le_one
    have hsmall_nonneg : 0 ≤ pSmall value := by
      exact cutoffAffordanceProbability_nonneg productLaw small value cutoff
    calc
      ‖pSmall value * (1 - pLarge value)‖ =
          |pSmall value| * |1 - pLarge value| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |pSmall value| * 1 :=
        mul_le_mul_of_nonneg_left hfactor_abs (abs_nonneg _)
      _ = |pSmall value| := by ring
      _ = pSmall value := abs_of_nonneg hsmall_nonneg
  have hproduct_integrable : Integrable
      (fun value : ℝ => pSmall value * (1 - pLarge value)) valueLaw :=
    Integrable.mono' hpSmall_integrable hproduct_meas hproduct_bound
  have hkernel_eq :
      (fun value : ℝ =>
        productLaw.real {noise : Fin n -> ℝ |
          theorem2SmallOnlyAffordanceEvent small large value cutoff noise}) =
        (fun value : ℝ => pSmall value * (1 - pLarge value)) := by
    funext value
    simpa [productLaw, pSmall, pLarge] using
      (theorem2_iid_smallOnlyAffordance_probability
        noiseLaw small large hdisjoint value cutoff)
  rw [show
    (fun value : ℝ =>
      (Measure.pi (fun _ : Fin n => noiseLaw)).real
        {noise : Fin n -> ℝ |
          theorem2SmallOnlyAffordanceEvent small large value cutoff noise}) =
      (fun value : ℝ =>
        productLaw.real {noise : Fin n -> ℝ |
          theorem2SmallOnlyAffordanceEvent small large value cutoff noise}) by
      rfl]
  rw [hkernel_eq]
  exact hproduct_integrable

/--
The iid small-only event supplies the repaired off-diagonal integral-to-event
bridge directly from its pointwise residual bound and Fubini.
-/
theorem theorem2_twoScale_integral_le_smallOnly_eventMass_of_iid
    {n : ℕ} (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    {totalSupply delta endpoint sigma : ℝ} (cutoff : Fin n -> ℝ)
    (hresidual : ∀ value : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large value cutoff) :
    (∫ value : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) small value cutoff
      ∂valueLaw) ≤
      eventMass
        (valueLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2SmallOnlyAffordanceProductEvent small large cutoff) := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  have hpSmall_integrable : Integrable
      (fun value : ℝ => cutoffAffordanceProbability productLaw small value cutoff)
      valueLaw := by
    simpa [cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw small cutoff)
  have hintegrable : Integrable
      (fun value : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          cutoffAffordanceProbability productLaw small value cutoff) valueLaw := by
    simpa using hpSmall_integrable.const_mul
      (theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
  have hkernel_integrable : Integrable
      (fun value : ℝ => productLaw.real {noise : Fin n -> ℝ |
        theorem2SmallOnlyAffordanceEvent small large value cutoff noise}) valueLaw := by
    simpa [productLaw] using
      (theorem2_iid_smallOnly_probability_integrable
        valueLaw noiseLaw small large hdisjoint cutoff)
  have hpointwise : ∀ value : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          cutoffAffordanceProbability productLaw small value cutoff ≤
        productLaw.real {noise : Fin n -> ℝ |
          theorem2SmallOnlyAffordanceEvent small large value cutoff noise} := by
    intro value
    simpa [productLaw] using
      (theorem2_twoScale_smallOnly_probability_lower_bound
        noiseLaw small large hdisjoint cutoff (hresidual value))
  simpa [productLaw] using
    (theorem2_twoScale_integral_le_eventMass_of_pointwise_section_bound
      valueLaw productLaw
      (theorem2SmallOnlyAffordanceProductEvent small large cutoff)
      (theorem2SmallOnlyAffordanceProductEvent_measurable small large cutoff)
      (fun value =>
        theorem2SmallOnlyAffordanceProductEvent_section_measurable
          small large value cutoff)
      hkernel_integrable hintegrable hpointwise)

end

end PG24NoisyMatchingMarkets

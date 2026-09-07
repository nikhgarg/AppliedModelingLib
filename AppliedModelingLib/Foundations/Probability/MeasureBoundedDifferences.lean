import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.BoundedDifferences

/-!
# Finite iid measure-product decompositions

This module records the measure-preserving `Fin.snoc` decomposition of the
canonical finite iid product law.  It is the analytic product-space input to
the arbitrary-law bounded-differences and Rademacher-concentration arguments;
unlike `BoundedDifferences`, it does not assume finite outcome support.
-/

namespace AppliedModelingLib
namespace Probability
namespace MeasureBoundedDifferences

open MeasureTheory ProbabilityTheory

/-- A probability measure cannot live on an empty carrier. -/
theorem nonempty_of_isProbabilityMeasure
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] : Nonempty Outcome := by
  classical
  by_contra hnonempty
  haveI : IsEmpty Outcome := not_nonempty_iff.mp hnonempty
  have hmass : law Set.univ = 1 := measure_univ
  have huniv : (Set.univ : Set Outcome) = ∅ := by
    ext outcome
    exact isEmptyElim outcome
  rw [huniv, measure_empty] at hmass
  norm_num at hmass

/-- A nonempty family of reals with pairwise oscillation at most `bound` fits
inside some interval of width `bound`.  The lower endpoint need not be
attained; it is the infimum of the family. -/
theorem exists_mem_Icc_of_pairwise_abs_sub_le
    {Index : Type*} [Nonempty Index] (score : Index → ℝ) (bound : ℝ)
    (hoscillation : ∀ first second, |score first - score second| ≤ bound) :
    ∃ lower, ∀ index, score index ∈ Set.Icc lower (lower + bound) := by
  classical
  let index₀ : Index := Classical.choice (inferInstance : Nonempty Index)
  have hnonempty : (Set.range score).Nonempty := ⟨score index₀, ⟨index₀, rfl⟩⟩
  have hbelow : BddBelow (Set.range score) := by
    refine ⟨score index₀ - bound, ?_⟩
    rintro result ⟨index, rfl⟩
    have h := hoscillation index₀ index
    linarith [le_of_abs_le h]
  refine ⟨sInf (Set.range score), ?_⟩
  intro index
  constructor
  · exact csInf_le hbelow ⟨index, rfl⟩
  · have hlower : score index - bound ≤ sInf (Set.range score) := by
      apply le_csInf hnonempty
      rintro result ⟨other, rfl⟩
      have h := hoscillation index other
      linarith [le_of_abs_le h]
    linarith

/-- Hoeffding's exponential-moment bound using only a pairwise oscillation
bound, rather than a preselected interval. -/
theorem integral_exp_mul_sub_integral_le_of_pairwise_abs_sub_le
    {Outcome : Type*} [MeasurableSpace Outcome] [Nonempty Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (score : Outcome → ℝ) (hmeasurable : Measurable score)
    (bound tilt : ℝ)
    (hoscillation : ∀ first second, |score first - score second| ≤ bound) :
    (∫ outcome, Real.exp (tilt * (score outcome - law[score])) ∂law) ≤
      Real.exp (bound ^ 2 * tilt ^ 2 / 8) := by
  let outcome₀ : Outcome := Classical.choice (inferInstance : Nonempty Outcome)
  have hboundNonneg : 0 ≤ bound := by
    have h := hoscillation outcome₀ outcome₀
    simpa using h
  obtain ⟨lower, hinterval⟩ :=
    exists_mem_Icc_of_pairwise_abs_sub_le score bound hoscillation
  have hsubgaussian := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (X := score) (a := lower) (b := lower + bound) (μ := law)
    hmeasurable.aemeasurable
    (Filter.Eventually.of_forall hinterval)
  have hmgf := hsubgaussian.mgf_le tilt
  change (∫ outcome, Real.exp (tilt * (score outcome - law[score])) ∂law) ≤ _
  calc
    (∫ outcome, Real.exp (tilt * (score outcome - law[score])) ∂law) ≤
        Real.exp ((bound / 2) ^ 2 * tilt ^ 2 / 2) := by
          simpa [ProbabilityTheory.mgf, Real.norm_eq_abs, abs_of_nonneg hboundNonneg] using hmgf
    _ = Real.exp (bound ^ 2 * tilt ^ 2 / 8) := by
      congr 1
      ring

/-- Probability alone supplies the nonempty-carrier fact needed by the
pairwise-oscillation Hoeffding bound. -/
theorem integral_exp_mul_sub_integral_le_of_pairwise_abs_sub_le_probability
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (score : Outcome → ℝ) (hmeasurable : Measurable score)
    (bound tilt : ℝ)
    (hoscillation : ∀ first second, |score first - score second| ≤ bound) :
    (∫ outcome, Real.exp (tilt * (score outcome - law[score])) ∂law) ≤
      Real.exp (bound ^ 2 * tilt ^ 2 / 8) := by
  letI : Nonempty Outcome := nonempty_of_isProbabilityMeasure law
  exact integral_exp_mul_sub_integral_le_of_pairwise_abs_sub_le law score
    hmeasurable bound tilt hoscillation

/-- The measurable equivalence which appends the displayed draw to a finite
sample. -/
noncomputable def finiteIIDSnocMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome] (sampleCount : ℕ) :
    (Fin sampleCount → Outcome) × Outcome ≃ᵐ
      (Fin (sampleCount + 1) → Outcome) :=
  let split := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin sampleCount) => Outcome)).symm
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (sampleCount + 1) => Outcome)
    (optionFinEquivFinSucc sampleCount)
  split.trans reindex

/-- The `finiteIIDSnocMeasEquiv` map is literally `Fin.snoc`. -/
theorem finiteIIDSnocMeasEquiv_apply
    {Outcome : Type*} [MeasurableSpace Outcome] (sampleCount : ℕ)
    (sample : Fin sampleCount → Outcome) (outcome : Outcome) :
    finiteIIDSnocMeasEquiv sampleCount (sample, outcome) =
      Fin.snoc sample outcome := by
  funext index
  refine Fin.lastCases ?_ (fun oldIndex => ?_) index
  · simp [finiteIIDSnocMeasEquiv, optionFinEquivFinSucc,
      MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.prodCongr,
      MeasurableEquiv.piUnique, Equiv.piCongrLeft,
      Equiv.sumPiEquivProdPi, Equiv.piUnique]
  · simp [finiteIIDSnocMeasEquiv, optionFinEquivFinSucc,
      MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.prodCongr,
      MeasurableEquiv.piUnique, Equiv.piCongrLeft,
      Equiv.sumPiEquivProdPi, Equiv.piUnique]

/-- Appending an independent draw maps the old-product times marginal law to
the canonical `(n+1)`-draw iid product law. -/
theorem map_finiteIIDSnocMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] (sampleCount : ℕ) :
    Measure.map (finiteIIDSnocMeasEquiv (Outcome := Outcome) sampleCount)
      ((finiteIIDSampleLaw law sampleCount).prod law) =
      finiteIIDSampleLaw law (sampleCount + 1) := by
  let split := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin sampleCount) => Outcome)).symm
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (sampleCount + 1) => Outcome)
    (optionFinEquivFinSucc sampleCount)
  let optionLaw : Option (Fin sampleCount) → Measure Outcome := fun _ => law
  letI : ∀ index : Option (Fin sampleCount), SigmaFinite (optionLaw index) :=
    fun _ => inferInstance
  have hsplit : Measure.map split ((finiteIIDSampleLaw law sampleCount).prod law) =
      Measure.pi optionLaw := by
    simpa [split, optionLaw, finiteIIDSampleLaw] using
      (Measure.pi_map_piOptionEquivProd optionLaw)
  have hreindex : Measure.map reindex (Measure.pi optionLaw) =
      finiteIIDSampleLaw law (sampleCount + 1) := by
    simpa [reindex, optionLaw, finiteIIDSampleLaw] using
      (Measure.pi_map_piCongrLeft (optionFinEquivFinSucc sampleCount)
        (fun _ : Fin (sampleCount + 1) => law))
  change Measure.map (reindex ∘ split) ((finiteIIDSampleLaw law sampleCount).prod law) = _
  calc
    Measure.map (reindex ∘ split) ((finiteIIDSampleLaw law sampleCount).prod law) =
        Measure.map reindex (Measure.map split
          ((finiteIIDSampleLaw law sampleCount).prod law)) := by
          symm
          exact Measure.map_map reindex.measurable split.measurable
    _ = Measure.map reindex (Measure.pi optionLaw) := by rw [hsplit]
    _ = finiteIIDSampleLaw law (sampleCount + 1) := hreindex

/-- Integrals under the `(n+1)`-draw iid law may be evaluated by drawing an
`n`-sample and one fresh outcome, with the sample represented by `Fin.snoc`. -/
theorem integral_finiteIIDSnoc
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] (sampleCount : ℕ)
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hintegrable : Integrable value (finiteIIDSampleLaw law (sampleCount + 1))) :
    (∫ sample, value sample ∂finiteIIDSampleLaw law (sampleCount + 1)) =
      ∫ pair, value (Fin.snoc pair.1 pair.2) ∂
        (finiteIIDSampleLaw law sampleCount).prod law := by
  have hintegrableMap : Integrable value
      (Measure.map (finiteIIDSnocMeasEquiv sampleCount)
        ((finiteIIDSampleLaw law sampleCount).prod law)) := by
    rw [map_finiteIIDSnocMeasEquiv law sampleCount]
    exact hintegrable
  rw [← map_finiteIIDSnocMeasEquiv law sampleCount]
  rw [integral_map (finiteIIDSnocMeasEquiv sampleCount).measurable.aemeasurable
    hintegrableMap.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with pair
  rw [finiteIIDSnocMeasEquiv_apply]

/-- Conditional mean over a fresh final iid draw. -/
noncomputable def finiteIIDSnocConditionalMean
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (sample : Fin sampleCount → Outcome) : ℝ :=
  ∫ outcome, value (Fin.snoc sample outcome) ∂law

/-- Averaging a statistic by first conditioning on its final iid coordinate
recovers its ordinary iid expectation. -/
theorem integral_finiteIIDSnocConditionalMean_eq_integral
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] (sampleCount : ℕ)
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hintegrable : Integrable value (finiteIIDSampleLaw law (sampleCount + 1))) :
    (∫ sample, finiteIIDSnocConditionalMean law value sample ∂
      finiteIIDSampleLaw law sampleCount) =
      ∫ sample, value sample ∂finiteIIDSampleLaw law (sampleCount + 1) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law sampleCount) := by
    unfold finiteIIDSampleLaw
    infer_instance
  let snocMap := finiteIIDSnocMeasEquiv (Outcome := Outcome) sampleCount
  have hpreserving : MeasurePreserving snocMap
      ((finiteIIDSampleLaw law sampleCount).prod law)
      (finiteIIDSampleLaw law (sampleCount + 1)) :=
    ⟨snocMap.measurable, map_finiteIIDSnocMeasEquiv law sampleCount⟩
  have hproduct : Integrable (value ∘ snocMap)
      ((finiteIIDSampleLaw law sampleCount).prod law) :=
    hpreserving.integrable_comp_of_integrable hintegrable
  have hsnoc : Integrable (fun pair : (Fin sampleCount → Outcome) × Outcome =>
      value (Fin.snoc pair.1 pair.2))
      ((finiteIIDSampleLaw law sampleCount).prod law) := by
    convert hproduct using 1
    funext pair
    change value (Fin.snoc pair.1 pair.2) = value (snocMap pair)
    rw [finiteIIDSnocMeasEquiv_apply]
  calc
    (∫ sample, finiteIIDSnocConditionalMean law value sample ∂
        finiteIIDSampleLaw law sampleCount) =
        ∫ pair, value (Fin.snoc pair.1 pair.2) ∂
          (finiteIIDSampleLaw law sampleCount).prod law := by
          unfold finiteIIDSnocConditionalMean
          exact integral_integral hsnoc
    _ = ∫ sample, value sample ∂finiteIIDSampleLaw law (sampleCount + 1) :=
      (integral_finiteIIDSnoc law sampleCount value hintegrable).symm

/-- A measurable statistic has a measurable fresh-draw conditional mean. -/
theorem measurable_finiteIIDSnocConditionalMean
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hmeasurable : Measurable value) :
    Measurable (finiteIIDSnocConditionalMean law value) := by
  have hpair : Measurable (fun pair : (Fin sampleCount → Outcome) × Outcome =>
      value (Fin.snoc pair.1 pair.2)) := by
    have heq : (fun pair : (Fin sampleCount → Outcome) × Outcome =>
        value (Fin.snoc pair.1 pair.2)) =
        value ∘ finiteIIDSnocMeasEquiv sampleCount := by
      funext pair
      change value (Fin.snoc pair.1 pair.2) =
        value (finiteIIDSnocMeasEquiv sampleCount pair)
      rw [finiteIIDSnocMeasEquiv_apply]
    rw [heq]
    exact hmeasurable.comp (finiteIIDSnocMeasEquiv sampleCount).measurable
  exact hpair.stronglyMeasurable.integral_prod_right'.measurable

/-- Conditional expectation over a fresh iid draw preserves a pointwise
bounded interval. -/
theorem finiteIIDSnocConditionalMean_mem_Icc
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hmeasurable : Measurable value) {lower upper : ℝ}
    (hbounded : ∀ sample, value sample ∈ Set.Icc lower upper)
    (sample : Fin sampleCount → Outcome) :
    finiteIIDSnocConditionalMean law value sample ∈ Set.Icc lower upper := by
  have hsectionMeasurable : Measurable (fun outcome => value (Fin.snoc sample outcome)) := by
    have hpair : Measurable (fun pair : (Fin sampleCount → Outcome) × Outcome =>
        value (Fin.snoc pair.1 pair.2)) := by
      have heq : (fun pair : (Fin sampleCount → Outcome) × Outcome =>
          value (Fin.snoc pair.1 pair.2)) =
          value ∘ finiteIIDSnocMeasEquiv sampleCount := by
        funext pair
        change value (Fin.snoc pair.1 pair.2) =
          value (finiteIIDSnocMeasEquiv sampleCount pair)
        rw [finiteIIDSnocMeasEquiv_apply]
      rw [heq]
      exact hmeasurable.comp (finiteIIDSnocMeasEquiv sampleCount).measurable
    exact hpair.comp (measurable_const.prodMk measurable_id)
  have hintegrable : Integrable (fun outcome => value (Fin.snoc sample outcome)) law :=
    Integrable.of_mem_Icc lower upper hsectionMeasurable.aemeasurable
      (Filter.Eventually.of_forall fun outcome => hbounded (Fin.snoc sample outcome))
  unfold finiteIIDSnocConditionalMean
  constructor
  · have hnonnegative : 0 ≤ ∫ outcome,
        value (Fin.snoc sample outcome) - lower ∂law :=
      integral_nonneg fun outcome =>
        sub_nonneg.mpr (hbounded (Fin.snoc sample outcome)).1
    rw [integral_sub hintegrable (integrable_const lower), integral_const] at hnonnegative
    simpa using hnonnegative
  · calc
      ∫ outcome, value (Fin.snoc sample outcome) ∂law ≤
          ∫ _outcome : Outcome, upper ∂law := by
            apply integral_mono hintegrable (integrable_const upper)
            intro outcome
            exact (hbounded (Fin.snoc sample outcome)).2
      _ = upper := by simp

/-- Integrating two uniformly bounded measurable fresh-draw sections cannot
increase a pointwise absolute-difference bound. -/
theorem abs_finiteIIDSnocConditionalMean_sub_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hmeasurable : Measurable value) {lower upper bound : ℝ}
    (hbounded : ∀ sample, value sample ∈ Set.Icc lower upper)
    (first second : Fin sampleCount → Outcome)
    (hpoint : ∀ outcome,
      |value (Fin.snoc first outcome) - value (Fin.snoc second outcome)| ≤ bound) :
    |finiteIIDSnocConditionalMean law value first -
        finiteIIDSnocConditionalMean law value second| ≤ bound := by
  have hfirstMeasurable : Measurable (fun outcome => value (Fin.snoc first outcome)) := by
    have hpair : Measurable (fun pair : (Fin sampleCount → Outcome) × Outcome =>
        value (Fin.snoc pair.1 pair.2)) := by
      have heq : (fun pair : (Fin sampleCount → Outcome) × Outcome =>
          value (Fin.snoc pair.1 pair.2)) =
          value ∘ finiteIIDSnocMeasEquiv sampleCount := by
        funext pair
        change value (Fin.snoc pair.1 pair.2) =
          value (finiteIIDSnocMeasEquiv sampleCount pair)
        rw [finiteIIDSnocMeasEquiv_apply]
      rw [heq]
      exact hmeasurable.comp (finiteIIDSnocMeasEquiv sampleCount).measurable
    exact hpair.comp (measurable_const.prodMk measurable_id)
  have hsecondMeasurable : Measurable (fun outcome => value (Fin.snoc second outcome)) := by
    have hpair : Measurable (fun pair : (Fin sampleCount → Outcome) × Outcome =>
        value (Fin.snoc pair.1 pair.2)) := by
      have heq : (fun pair : (Fin sampleCount → Outcome) × Outcome =>
          value (Fin.snoc pair.1 pair.2)) =
          value ∘ finiteIIDSnocMeasEquiv sampleCount := by
        funext pair
        change value (Fin.snoc pair.1 pair.2) =
          value (finiteIIDSnocMeasEquiv sampleCount pair)
        rw [finiteIIDSnocMeasEquiv_apply]
      rw [heq]
      exact hmeasurable.comp (finiteIIDSnocMeasEquiv sampleCount).measurable
    exact hpair.comp (measurable_const.prodMk measurable_id)
  have hfirstIntegrable : Integrable (fun outcome => value (Fin.snoc first outcome)) law :=
    Integrable.of_mem_Icc lower upper hfirstMeasurable.aemeasurable
      (Filter.Eventually.of_forall fun outcome => hbounded (Fin.snoc first outcome))
  have hsecondIntegrable : Integrable (fun outcome => value (Fin.snoc second outcome)) law :=
    Integrable.of_mem_Icc lower upper hsecondMeasurable.aemeasurable
      (Filter.Eventually.of_forall fun outcome => hbounded (Fin.snoc second outcome))
  unfold finiteIIDSnocConditionalMean
  calc
    |(∫ outcome, value (Fin.snoc first outcome) ∂law) -
        ∫ outcome, value (Fin.snoc second outcome) ∂law| =
        |∫ outcome, value (Fin.snoc first outcome) -
          value (Fin.snoc second outcome) ∂law| := by
            rw [integral_sub hfirstIntegrable hsecondIntegrable]
    _ ≤ ∫ outcome, |value (Fin.snoc first outcome) -
          value (Fin.snoc second outcome)| ∂law := abs_integral_le_integral_abs
    _ ≤ ∫ _outcome : Outcome, bound ∂law := by
          apply integral_mono
          · exact (hfirstIntegrable.sub hsecondIntegrable).norm
          · exact integrable_const bound
          · intro outcome
            exact hpoint outcome
    _ = bound := by simp

/-- Integrating out the final draw preserves every bounded-difference
constant on the preceding coordinates. -/
theorem abs_finiteIIDSnocConditionalMean_sub_update_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hmeasurable : Measurable value) {lower upper : ℝ}
    (hboundedRange : ∀ sample, value sample ∈ Set.Icc lower upper)
    (bound : Fin (sampleCount + 1) → ℝ)
    (hboundedDifference : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤ bound index)
    (sample : Fin sampleCount → Outcome) (index : Fin sampleCount)
    (replacement : Outcome) :
    |finiteIIDSnocConditionalMean law value sample -
        finiteIIDSnocConditionalMean law value
          (Function.update sample index replacement)| ≤ bound index.castSucc := by
  apply abs_finiteIIDSnocConditionalMean_sub_le law value hmeasurable hboundedRange
    sample (Function.update sample index replacement)
  intro outcome
  have hpoint := hboundedDifference index.castSucc (Fin.snoc sample outcome) replacement
  rw [← BoundedDifferences.snoc_update_castSucc] at hpoint
  exact hpoint

/-- Conditional Hoeffding step for the final iid coordinate.  This is the
one-coordinate MGF input for finite-product bounded-difference tensorization. -/
theorem integral_exp_mul_sub_finiteIIDSnocConditionalMean_le
    {Outcome : Type*} [MeasurableSpace Outcome] [Nonempty Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hmeasurable : Measurable value)
    (bound : Fin (sampleCount + 1) → ℝ)
    (hboundedDifference : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤ bound index)
    (sample : Fin sampleCount → Outcome) (tilt : ℝ) :
    (∫ outcome, Real.exp (tilt *
      (value (Fin.snoc sample outcome) -
        finiteIIDSnocConditionalMean law value sample)) ∂law) ≤
      Real.exp (bound (Fin.last sampleCount) ^ 2 * tilt ^ 2 / 8) := by
  let sectionScore : Outcome → ℝ := fun outcome => value (Fin.snoc sample outcome)
  have hsectionMeasurable : Measurable sectionScore := by
    have hpair : Measurable (fun pair : (Fin sampleCount → Outcome) × Outcome =>
        value (Fin.snoc pair.1 pair.2)) := by
      have heq : (fun pair : (Fin sampleCount → Outcome) × Outcome =>
          value (Fin.snoc pair.1 pair.2)) =
          value ∘ finiteIIDSnocMeasEquiv sampleCount := by
        funext pair
        change value (Fin.snoc pair.1 pair.2) =
          value (finiteIIDSnocMeasEquiv sampleCount pair)
        rw [finiteIIDSnocMeasEquiv_apply]
      rw [heq]
      exact hmeasurable.comp (finiteIIDSnocMeasEquiv sampleCount).measurable
    exact hpair.comp (measurable_const.prodMk measurable_id)
  have hoscillation : ∀ first second,
      |sectionScore first - sectionScore second| ≤ bound (Fin.last sampleCount) := by
    intro first second
    have hpoint := hboundedDifference (Fin.last sampleCount)
      (Fin.snoc sample first) second
    have hupdate : Function.update (Fin.snoc sample first : Fin (sampleCount + 1) → Outcome)
        (Fin.last sampleCount) second = Fin.snoc sample second := by
      funext index
      refine Fin.lastCases ?_ (fun oldIndex => ?_) index <;> simp
    simpa [sectionScore, hupdate] using hpoint
  simpa [sectionScore, finiteIIDSnocConditionalMean] using
    (integral_exp_mul_sub_integral_le_of_pairwise_abs_sub_le law sectionScore
      hsectionMeasurable (bound (Fin.last sampleCount)) tilt hoscillation)

/-- Probability supplies the nonempty-carrier fact required by the conditional
Hoeffding step, so it is not an additional bounded-differences assumption. -/
theorem integral_exp_mul_sub_finiteIIDSnocConditionalMean_le_probability
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] {sampleCount : ℕ}
    (value : (Fin (sampleCount + 1) → Outcome) → ℝ)
    (hmeasurable : Measurable value)
    (bound : Fin (sampleCount + 1) → ℝ)
    (hboundedDifference : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤ bound index)
    (sample : Fin sampleCount → Outcome) (tilt : ℝ) :
    (∫ outcome, Real.exp (tilt *
      (value (Fin.snoc sample outcome) -
        finiteIIDSnocConditionalMean law value sample)) ∂law) ≤
      Real.exp (bound (Fin.last sampleCount) ^ 2 * tilt ^ 2 / 8) := by
  letI : Nonempty Outcome := nonempty_of_isProbabilityMeasure law
  exact integral_exp_mul_sub_finiteIIDSnocConditionalMean_le law value hmeasurable
    bound hboundedDifference sample tilt

/-- A bounded measurable score has an integrable centered exponential moment.
This elementary helper supplies the Fubini side condition in the finite-product
bounded-differences induction below. -/
theorem integrable_exp_mul_sub_integral_of_mem_Icc
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (score : Outcome → ℝ) (hmeasurable : Measurable score)
    {lower upper : ℝ}
    (hbounded : ∀ outcome, score outcome ∈ Set.Icc lower upper)
    (tilt : ℝ) :
    Integrable (fun outcome => Real.exp (tilt * (score outcome - law[score])) ) law := by
  exact (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    hmeasurable.aemeasurable (Filter.Eventually.of_forall hbounded)).integrable_exp_mul tilt

/--
Finite-product bounded differences under an arbitrary iid probability law.

For a measurable statistic whose range is pointwise bounded, changing its
`i`th coordinate by at most `bound i` gives the usual McDiarmid exponential
moment estimate.  The range premise supplies integrability only; the variance
proxy itself is exactly `∑ᵢ bound i² / 4`.
-/
theorem finiteIID_integral_exp_mul_sub_integral_le_of_boundedDifferences
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ)
    (value : (Fin sampleCount → Outcome) → ℝ)
    (hmeasurable : Measurable value) {lower upper : ℝ}
    (hboundedRange : ∀ sample, value sample ∈ Set.Icc lower upper)
    (bound : Fin sampleCount → ℝ)
    (hboundedDifference : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤ bound index)
    (tilt : ℝ) :
    (∫ sample, Real.exp (tilt *
      (value sample - ∫ sample, value sample ∂finiteIIDSampleLaw law sampleCount)) ∂
        finiteIIDSampleLaw law sampleCount) ≤
      Real.exp ((∑ index : Fin sampleCount, bound index ^ 2 / 4) * tilt ^ 2 / 2) := by
  classical
  induction sampleCount with
  | zero =>
      letI : IsProbabilityMeasure (finiteIIDSampleLaw law 0) := by
        dsimp [finiteIIDSampleLaw]
        infer_instance
      let emptySample : Fin 0 → Outcome := fun index => Fin.elim0 index
      have hconstant : ∀ sample : Fin 0 → Outcome, value sample = value emptySample := by
        intro sample
        congr
        funext index
        exact Fin.elim0 index
      have hmean :
          (∫ sample, value sample ∂finiteIIDSampleLaw law 0) = value emptySample := by
        calc
          (∫ sample, value sample ∂finiteIIDSampleLaw law 0) =
              ∫ _sample : Fin 0 → Outcome, value emptySample ∂finiteIIDSampleLaw law 0 := by
                apply integral_congr_ae
                filter_upwards with sample
                exact hconstant sample
          _ = value emptySample := by simp [probReal_univ]
      rw [hmean]
      have hcentered : ∀ sample : Fin 0 → Outcome,
          Real.exp (tilt * (value sample - value emptySample)) = 1 := by
        intro sample
        rw [hconstant sample]
        simp
      have hmeasure :
          (∫ sample, Real.exp (tilt * (value sample - value emptySample)) ∂
            finiteIIDSampleLaw law 0) = 1 := by
        calc
          (∫ sample, Real.exp (tilt * (value sample - value emptySample)) ∂
              finiteIIDSampleLaw law 0) =
              ∫ _sample : Fin 0 → Outcome, (1 : ℝ) ∂finiteIIDSampleLaw law 0 := by
                apply integral_congr_ae
                filter_upwards with sample
                rw [hcentered sample]
          _ = 1 := by simp [probReal_univ]
      rw [hmeasure]
      simp
  | succ previous inductionHypothesis =>
      letI : IsProbabilityMeasure (finiteIIDSampleLaw law previous) := by
        dsimp [finiteIIDSampleLaw]
        infer_instance
      letI : IsProbabilityMeasure (finiteIIDSampleLaw law (previous + 1)) := by
        dsimp [finiteIIDSampleLaw]
        infer_instance
      let oldBound : Fin previous → ℝ := fun index => bound index.castSucc
      let conditionalMean : (Fin previous → Outcome) → ℝ :=
        finiteIIDSnocConditionalMean law value
      have hconditionalMeasurable : Measurable conditionalMean :=
        measurable_finiteIIDSnocConditionalMean law value hmeasurable
      have hconditionalRange : ∀ sample, conditionalMean sample ∈ Set.Icc lower upper := by
        intro sample
        exact finiteIIDSnocConditionalMean_mem_Icc law value hmeasurable hboundedRange sample
      have hconditionalDifference : ∀ index sample replacement,
          |conditionalMean sample -
              conditionalMean (Function.update sample index replacement)| ≤ oldBound index := by
        intro index sample replacement
        exact abs_finiteIIDSnocConditionalMean_sub_update_le law value hmeasurable
          hboundedRange bound hboundedDifference sample index replacement
      have hprevious := inductionHypothesis conditionalMean hconditionalMeasurable
        hconditionalRange oldBound hconditionalDifference
      have hvalueIntegrable : Integrable value
          (finiteIIDSampleLaw law (previous + 1)) :=
        Integrable.of_mem_Icc lower upper hmeasurable.aemeasurable
          (Filter.Eventually.of_forall hboundedRange)
      have hglobalExpIntegrable : Integrable (fun sample => Real.exp (tilt *
          (value sample - ∫ sample, value sample ∂finiteIIDSampleLaw law (previous + 1))) )
          (finiteIIDSampleLaw law (previous + 1)) :=
        integrable_exp_mul_sub_integral_of_mem_Icc
          (finiteIIDSampleLaw law (previous + 1))
          (fun sample => value sample) hmeasurable hboundedRange tilt
      have hconditionalExpIntegrable : Integrable (fun sample => Real.exp (tilt *
          (conditionalMean sample -
            ∫ sample, conditionalMean sample ∂finiteIIDSampleLaw law previous)))
          (finiteIIDSampleLaw law previous) :=
        integrable_exp_mul_sub_integral_of_mem_Icc
          (finiteIIDSampleLaw law previous)
          conditionalMean hconditionalMeasurable hconditionalRange tilt
      let totalMean : ℝ :=
        ∫ sample, value sample ∂finiteIIDSampleLaw law (previous + 1)
      let residual : (Fin previous → Outcome) × Outcome → ℝ := fun pair =>
        Real.exp (tilt * (value (Fin.snoc pair.1 pair.2) - totalMean))
      let lastFactor : ℝ :=
        Real.exp (bound (Fin.last previous) ^ 2 * tilt ^ 2 / 8)
      have hconditionalMeanIntegral :
          (∫ sample, conditionalMean sample ∂finiteIIDSampleLaw law previous) = totalMean := by
        dsimp [conditionalMean, totalMean]
        exact integral_finiteIIDSnocConditionalMean_eq_integral law previous value
          hvalueIntegrable
      have hpreviousTotal :
          (∫ sample, Real.exp (tilt * (conditionalMean sample - totalMean)) ∂
            finiteIIDSampleLaw law previous) ≤
            Real.exp ((∑ index : Fin previous, oldBound index ^ 2 / 4) * tilt ^ 2 / 2) := by
        rw [← hconditionalMeanIntegral]
        exact hprevious
      have hconditionalExpIntegrableTotal : Integrable (fun sample => Real.exp (tilt *
          (conditionalMean sample - totalMean))) (finiteIIDSampleLaw law previous) := by
        rw [← hconditionalMeanIntegral]
        exact hconditionalExpIntegrable
      have hpreserving : MeasurePreserving
          (finiteIIDSnocMeasEquiv (Outcome := Outcome) previous)
          ((finiteIIDSampleLaw law previous).prod law)
          (finiteIIDSampleLaw law (previous + 1)) :=
        ⟨(finiteIIDSnocMeasEquiv (Outcome := Outcome) previous).measurable,
          map_finiteIIDSnocMeasEquiv law previous⟩
      have hresidualIntegrable : Integrable residual
          ((finiteIIDSampleLaw law previous).prod law) := by
        have hcomposed := hpreserving.integrable_comp_of_integrable hglobalExpIntegrable
        convert hcomposed using 1
        funext pair
        dsimp [residual]
        change Real.exp (tilt * (value (Fin.snoc pair.1 pair.2) - totalMean)) =
          Real.exp (tilt * (value
            (finiteIIDSnocMeasEquiv (Outcome := Outcome) previous pair) - totalMean))
        rw [finiteIIDSnocMeasEquiv_apply]
      have houterIntegrable : Integrable (fun sample =>
          ∫ outcome, residual (sample, outcome) ∂law)
          (finiteIIDSampleLaw law previous) :=
        hresidualIntegrable.integral_prod_left
      have hinnerFactor (sample : Fin previous → Outcome) :
          (∫ outcome, residual (sample, outcome) ∂law) =
            Real.exp (tilt * (conditionalMean sample - totalMean)) *
              ∫ outcome, Real.exp (tilt *
                (value (Fin.snoc sample outcome) - conditionalMean sample)) ∂law := by
        rw [show (fun outcome => residual (sample, outcome)) =
            fun outcome => Real.exp (tilt * (conditionalMean sample - totalMean)) *
              Real.exp (tilt *
                (value (Fin.snoc sample outcome) - conditionalMean sample)) by
              funext outcome
              dsimp [residual]
              rw [← Real.exp_add]
              congr 1
              ring]
        rw [integral_const_mul]
      have hinnerLe (sample : Fin previous → Outcome) :
          (∫ outcome, residual (sample, outcome) ∂law) ≤
            lastFactor * Real.exp (tilt * (conditionalMean sample - totalMean)) := by
        rw [hinnerFactor]
        calc
          Real.exp (tilt * (conditionalMean sample - totalMean)) *
              (∫ outcome, Real.exp (tilt *
                (value (Fin.snoc sample outcome) - conditionalMean sample)) ∂law) ≤
              Real.exp (tilt * (conditionalMean sample - totalMean)) * lastFactor := by
                apply mul_le_mul_of_nonneg_left
                · dsimp [lastFactor]
                  exact integral_exp_mul_sub_finiteIIDSnocConditionalMean_le_probability
                    law value hmeasurable bound hboundedDifference sample tilt
                · exact (Real.exp_pos _).le
          _ = lastFactor * Real.exp (tilt * (conditionalMean sample - totalMean)) := by
            ring
      have hupperIntegrable : Integrable (fun sample => lastFactor *
          Real.exp (tilt * (conditionalMean sample - totalMean)))
          (finiteIIDSampleLaw law previous) :=
        hconditionalExpIntegrableTotal.const_mul lastFactor
      have houterLe :
          (∫ sample, ∫ outcome, residual (sample, outcome) ∂law ∂
            finiteIIDSampleLaw law previous) ≤
            ∫ sample, lastFactor * Real.exp (tilt *
              (conditionalMean sample - totalMean)) ∂finiteIIDSampleLaw law previous := by
        apply integral_mono houterIntegrable hupperIntegrable
        intro sample
        exact hinnerLe sample
      have hsnocIntegral :
          (∫ sample, Real.exp (tilt * (value sample - totalMean)) ∂
            finiteIIDSampleLaw law (previous + 1)) =
            ∫ pair, residual pair ∂(finiteIIDSampleLaw law previous).prod law := by
        simpa [residual] using integral_finiteIIDSnoc law previous
          (fun sample => Real.exp (tilt * (value sample - totalMean))) hglobalExpIntegrable
      change (∫ sample, Real.exp (tilt * (value sample - totalMean)) ∂
        finiteIIDSampleLaw law (previous + 1)) ≤ _
      rw [hsnocIntegral, integral_prod residual hresidualIntegrable]
      calc
        (∫ sample, ∫ outcome, residual (sample, outcome) ∂law ∂
            finiteIIDSampleLaw law previous) ≤
            ∫ sample, lastFactor * Real.exp (tilt *
              (conditionalMean sample - totalMean)) ∂finiteIIDSampleLaw law previous := houterLe
        _ = lastFactor * (∫ sample, Real.exp (tilt *
              (conditionalMean sample - totalMean)) ∂finiteIIDSampleLaw law previous) := by
              rw [integral_const_mul]
        _ ≤ lastFactor * Real.exp ((∑ index : Fin previous,
              oldBound index ^ 2 / 4) * tilt ^ 2 / 2) := by
              apply mul_le_mul_of_nonneg_left hpreviousTotal
              exact (Real.exp_pos _).le
        _ = Real.exp ((∑ index : Fin (previous + 1), bound index ^ 2 / 4) *
              tilt ^ 2 / 2) := by
              rw [← Real.exp_add]
              congr 1
              dsimp [lastFactor, oldBound]
              rw [Fin.sum_univ_castSucc]
              ring

/-- The preceding finite-product estimate packaged in Mathlib's standard
sub-Gaussian interface. -/
theorem finiteIID_hasSubgaussianMGF_sub_integral_of_boundedDifferences
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ)
    (value : (Fin sampleCount → Outcome) → ℝ)
    (hmeasurable : Measurable value) {lower upper : ℝ}
    (hboundedRange : ∀ sample, value sample ∈ Set.Icc lower upper)
    (bound : Fin sampleCount → ℝ)
    (hboundedDifference : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤ bound index) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun sample => value sample -
        ∫ sample, value sample ∂finiteIIDSampleLaw law sampleCount)
      ⟨∑ index : Fin sampleCount, bound index ^ 2 / 4, by positivity⟩
      (finiteIIDSampleLaw law sampleCount) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law sampleCount) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  constructor
  · intro tilt
    exact integrable_exp_mul_sub_integral_of_mem_Icc
      (finiteIIDSampleLaw law sampleCount) value hmeasurable hboundedRange tilt
  · intro tilt
    change (∫ sample, Real.exp (tilt *
      (value sample - ∫ sample, value sample ∂finiteIIDSampleLaw law sampleCount)) ∂
        finiteIIDSampleLaw law sampleCount) ≤
      Real.exp ((∑ index : Fin sampleCount, bound index ^ 2 / 4) * tilt ^ 2 / 2)
    exact finiteIID_integral_exp_mul_sub_integral_le_of_boundedDifferences
      law sampleCount value hmeasurable hboundedRange bound hboundedDifference tilt

/-- McDiarmid's upper-tail conclusion for a bounded statistic on an arbitrary
finite iid product.  The zero-sensitivity case is intentionally retained: the
standard sub-Gaussian expression then supplies the valid, if non-sharp, bound. -/
theorem measureReal_finiteIID_sub_integral_ge_le_of_boundedDifferences
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ)
    (value : (Fin sampleCount → Outcome) → ℝ)
    (hmeasurable : Measurable value) {lower upper : ℝ}
    (hboundedRange : ∀ sample, value sample ∈ Set.Icc lower upper)
    (bound : Fin sampleCount → ℝ)
    (hboundedDifference : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤ bound index)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤ value sample -
        ∫ sample, value sample ∂finiteIIDSampleLaw law sampleCount} ≤
      Real.exp (-epsilon ^ 2 /
        (2 * (∑ index : Fin sampleCount, bound index ^ 2 / 4))) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law sampleCount) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  simpa using
    (finiteIID_hasSubgaussianMGF_sub_integral_of_boundedDifferences
      law sampleCount value hmeasurable hboundedRange bound hboundedDifference).measure_ge_le
        hepsilon

end MeasureBoundedDifferences
end Probability
end AppliedModelingLib

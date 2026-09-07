import PG24NoisyMatchingMarkets.Theorem1SourceModelIntegration
import PG24NoisyMatchingMarkets.Theorem1CutoffPartition
import PG24NoisyMatchingMarkets.Theorem1LargeGapGeometry
import Mathlib.Tactic

/-!
# PG24 Theorem 1 analytic tail bridge

This module proves the measure-theoretic and finite-iid event steps used in
the attenuation appendix.  It keeps all cutoff geometry, interval regularity,
and integer grouping data explicit.  In particular, low values are `Iic vS`
and high values are `Ioi vS`; no threshold atom is discarded.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open MeasureTheory
open AppliedModelingLib.Matching

universe u

/-- A pointwise bound on a measurable value region integrates to its mass times the bound. -/
theorem theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
    (valueLaw : Measure ℝ) [IsFiniteMeasure valueLaw]
    (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    {region : Set ℝ} (hregion : MeasurableSet region) {bound : ℝ}
    (hbound : ∀ v ∈ region, p v ≤ bound) :
    (∫ v in region, p v ∂valueLaw) ≤ valueLaw.real region * bound := by
  calc
    (∫ v in region, p v ∂valueLaw) ≤
        ∫ _v in region, bound ∂valueLaw :=
      setIntegral_mono_on hp.integrableOn
        (integrableOn_const (measure_ne_top valueLaw _)) hregion hbound
    _ = valueLaw.real region * bound := by
      rw [setIntegral_const]
      simp [smul_eq_mul]

/-- A probability-valued integrand is bounded on a region by that region's value mass. -/
theorem theorem1_setIntegral_le_measureReal_of_le_one
    (valueLaw : Measure ℝ) [IsFiniteMeasure valueLaw]
    (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    {region : Set ℝ} (hregion : MeasurableSet region)
    (hone : ∀ v ∈ region, p v ≤ 1) :
    (∫ v in region, p v ∂valueLaw) ≤ valueLaw.real region := by
  simpa using theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
    valueLaw p hp hregion hone

/--
Exact three-way decomposition of the closed low tail.  The pivot atoms are
allocated to the adjacent closed/half-open pieces, so this needs no `NoAtoms`
assumption.
-/
theorem theorem1_setIntegral_Iic_eq_low_middle_high
    (valueLaw : Measure ℝ) (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    {lowPivot highPivot vS : ℝ}
    (hlow_high : lowPivot ≤ highPivot)
    (hhigh_vS : highPivot ≤ vS) :
    (∫ v in Set.Iic vS, p v ∂valueLaw) =
      (∫ v in Set.Iio lowPivot, p v ∂valueLaw) +
        (∫ v in Set.Icc lowPivot highPivot, p v ∂valueLaw) +
          ∫ v in Set.Ioc highPivot vS, p v ∂valueLaw := by
  have hlow_middle_disjoint : Disjoint (Set.Iio lowPivot)
      (Set.Icc lowPivot highPivot) :=
    (Set.Iio_disjoint_Ici le_rfl).mono le_rfl Set.Icc_subset_Ici_self
  have hlow_middle_union : Set.Iio lowPivot ∪ Set.Icc lowPivot highPivot =
      Set.Iic highPivot :=
    Set.Iio_union_Icc_eq_Iic hlow_high
  have hprefix_high_disjoint : Disjoint (Set.Iic highPivot)
      (Set.Ioc highPivot vS) :=
    Set.Iic_disjoint_Ioc le_rfl
  calc
    (∫ v in Set.Iic vS, p v ∂valueLaw) =
        ∫ v in Set.Iic highPivot ∪ Set.Ioc highPivot vS, p v ∂valueLaw := by
      rw [Set.Iic_union_Ioc_eq_Iic hhigh_vS]
    _ = (∫ v in Set.Iic highPivot, p v ∂valueLaw) +
          ∫ v in Set.Ioc highPivot vS, p v ∂valueLaw :=
      setIntegral_union hprefix_high_disjoint measurableSet_Ioc
        hp.integrableOn hp.integrableOn
    _ = ((∫ v in Set.Iio lowPivot, p v ∂valueLaw) +
          ∫ v in Set.Icc lowPivot highPivot, p v ∂valueLaw) +
          ∫ v in Set.Ioc highPivot vS, p v ∂valueLaw := by
      congr 1
      calc
        (∫ v in Set.Iic highPivot, p v ∂valueLaw) =
            ∫ v in Set.Iio lowPivot ∪ Set.Icc lowPivot highPivot, p v ∂valueLaw := by
          rw [hlow_middle_union]
        _ = (∫ v in Set.Iio lowPivot, p v ∂valueLaw) +
            ∫ v in Set.Icc lowPivot highPivot, p v ∂valueLaw :=
          setIntegral_union hlow_middle_disjoint measurableSet_Icc
            hp.integrableOn hp.integrableOn
    _ = (∫ v in Set.Iio lowPivot, p v ∂valueLaw) +
          (∫ v in Set.Icc lowPivot highPivot, p v ∂valueLaw) +
          ∫ v in Set.Ioc highPivot vS, p v ∂valueLaw := by
      ring

/--
The source's capacity budget, derived directly from a high-side pointwise
match lower bound.  The source normalization is intentionally strict at the
threshold: `valueLaw (Ioi vS) = totalSupply`.
-/
theorem theorem1_high_interval_mass_budget
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    {totalSupply error highPivot vS : ℝ}
    (hp_nonneg : ∀ v, 0 ≤ p v)
    (htotal : (∫ v, p v ∂valueLaw) ≤ totalSupply)
    (hhigh_match : ∀ v ∈ Set.Ioi highPivot, 1 - error ≤ p v)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hpivot_le_vS : highPivot ≤ vS) :
    (1 - error) *
        (totalSupply + valueLaw.real (Set.Ioc highPivot vS)) ≤ totalSupply := by
  have hhigh_lower :
      (1 - error) * valueLaw.real (Set.Ioi highPivot) ≤
        ∫ v in Set.Ioi highPivot, p v ∂valueLaw := by
    simpa using (setIntegral_ge_of_const_le_real
      (μ := valueLaw) (f := p) measurableSet_Ioi
      (measure_ne_top valueLaw _) hhigh_match hp.integrableOn)
  have hhigh_le_total :
      (∫ v in Set.Ioi highPivot, p v ∂valueLaw) ≤
        ∫ v, p v ∂valueLaw :=
    setIntegral_le_integral hp (ae_of_all valueLaw hp_nonneg)
  have hbudget_raw :
      (1 - error) * valueLaw.real (Set.Ioi highPivot) ≤ totalSupply :=
    hhigh_lower.trans (hhigh_le_total.trans htotal)
  have htail_split :
      valueLaw.real (Set.Ioi highPivot) =
        valueLaw.real (Set.Ioc highPivot vS) + valueLaw.real (Set.Ioi vS) := by
    calc
      valueLaw.real (Set.Ioi highPivot) =
          valueLaw.real (Set.Ioc highPivot vS ∪ Set.Ioi vS) := by
        rw [Set.Ioc_union_Ioi_eq_Ioi hpivot_le_vS]
      _ = valueLaw.real (Set.Ioc highPivot vS) +
          valueLaw.real (Set.Ioi vS) :=
        measureReal_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
  rw [htail_split, htail_normalization] at hbudget_raw
  linarith

/--
The analytic low-tail bound used in both attenuation branches.  It is derived
from pointwise cutoff-affordance estimates, a concrete middle-window mass
bound, and the capacity budget; it does not take a tail estimate as a premise.
-/
theorem theorem1_low_affordance_integral_le_of_analytic_primitives
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    {totalSupply lowError highError middleMass lowPivot highPivot vS : ℝ}
    (hp_nonneg : ∀ v, 0 ≤ p v)
    (hp_le_one : ∀ v, p v ≤ 1)
    (hlow_error_nonneg : 0 ≤ lowError)
    (hhigh_error_nonneg : 0 ≤ highError)
    (hhigh_error_le_half : highError ≤ 1 / 2)
    (hlow_high : lowPivot ≤ highPivot)
    (hhigh_vS : highPivot ≤ vS)
    (hlow_match : ∀ v ∈ Set.Iio lowPivot, p v ≤ lowError)
    (hhigh_match : ∀ v ∈ Set.Ioi highPivot, 1 - highError ≤ p v)
    (htotal : (∫ v, p v ∂valueLaw) ≤ totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hmiddle : valueLaw.real (Set.Icc lowPivot highPivot) ≤ middleMass) :
    (∫ v : ℝ, (Set.Iic vS).indicator p v ∂valueLaw) ≤
      lowError + middleMass + 2 * totalSupply * highError := by
  have hlow_integral :
      (∫ v in Set.Iio lowPivot, p v ∂valueLaw) ≤ lowError := by
    calc
      (∫ v in Set.Iio lowPivot, p v ∂valueLaw) ≤
          valueLaw.real (Set.Iio lowPivot) * lowError :=
        theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
          valueLaw p hp measurableSet_Iio hlow_match
      _ ≤ lowError := by
        have hmeasure_le_one : valueLaw.real (Set.Iio lowPivot) ≤ 1 :=
          measureReal_le_one (μ := valueLaw)
        nlinarith
  have hmiddle_integral :
      (∫ v in Set.Icc lowPivot highPivot, p v ∂valueLaw) ≤ middleMass := by
    calc
      (∫ v in Set.Icc lowPivot highPivot, p v ∂valueLaw) ≤
          valueLaw.real (Set.Icc lowPivot highPivot) :=
        theorem1_setIntegral_le_measureReal_of_le_one
          valueLaw p hp measurableSet_Icc (fun v _ => hp_le_one v)
      _ ≤ middleMass := hmiddle
  have hbudget := theorem1_high_interval_mass_budget
    valueLaw p hp hp_nonneg htotal hhigh_match htail_normalization hhigh_vS
  have hhigh_mass :
      valueLaw.real (Set.Ioc highPivot vS) ≤
        2 * totalSupply * highError :=
    theorem1Tail_interval_mass_le_two_mul_supply_mul_error
      (by
        have hintegral_nonneg : 0 ≤ ∫ v, p v ∂valueLaw :=
          integral_nonneg hp_nonneg
        exact le_trans hintegral_nonneg htotal) hhigh_error_nonneg
      hhigh_error_le_half hbudget
  have hhigh_integral :
      (∫ v in Set.Ioc highPivot vS, p v ∂valueLaw) ≤
        2 * totalSupply * highError := by
    calc
      (∫ v in Set.Ioc highPivot vS, p v ∂valueLaw) ≤
          valueLaw.real (Set.Ioc highPivot vS) :=
        theorem1_setIntegral_le_measureReal_of_le_one
          valueLaw p hp measurableSet_Ioc (fun v _ => hp_le_one v)
      _ ≤ 2 * totalSupply * highError := hhigh_mass
  rw [integral_indicator measurableSet_Iic,
    theorem1_setIntegral_Iic_eq_low_middle_high valueLaw p hp
      hlow_high hhigh_vS]
  linarith

/--
Union bound for an explicitly finite family of cutoff blocks.  This is the
event-level grouping step in source Case 1, proved from the cutoff-crossing
event rather than supplied as a probability estimate.
-/
theorem theorem1_cutoff_affordance_biUnion_le_sum
    {n : ℕ} (noiseLaw : Measure (Fin n → ℝ))
    (groups : Finset (Finset (Fin n)))
    (v : ℝ) (cutoff : Fin n → ℝ) :
    cutoffAffordanceProbability noiseLaw (groups.biUnion id) v cutoff ≤
      ∑ group ∈ groups,
        cutoffAffordanceProbability noiseLaw group v cutoff := by
  classical
  let event : Finset (Fin n) → (Fin n → ℝ) → Prop :=
    fun active noise => cutoffCrossedOn active (noisyScore v noise) cutoff
  have hevent :
      (fun noise : Fin n → ℝ => event (groups.biUnion id) noise) =
        (fun noise : Fin n → ℝ => ∃ group ∈ groups, event group noise) := by
    funext noise
    apply propext
    constructor
    · rintro ⟨c, hc, hcross⟩
      rcases Finset.mem_biUnion.mp hc with ⟨group, hgroup, hcgroup⟩
      exact ⟨group, hgroup, c, hcgroup, hcross⟩
    · rintro ⟨group, hgroup, c, hcgroup, hcross⟩
      exact ⟨c, Finset.mem_biUnion.mpr ⟨group, hgroup, hcgroup⟩, hcross⟩
  change AppliedModelingLib.measureProb noiseLaw
      (fun noise : Fin n → ℝ => event (groups.biUnion id) noise) ≤ _
  rw [hevent]
  simpa [event, cutoffAffordanceProbability,
    AppliedModelingLib.Matching.cutoffCrossingProbability] using
    (AppliedModelingLib.measureProb_biUnion_finset_le noiseLaw groups
      (fun group noise => event group noise))

/--
For iid noise, a cutoff block with a common lower cutoff is bounded by the
deviation probability of an iid maximum of exactly the block's integer size.
This is the formal event inclusion behind source equation (163); no real-power
rounding convention is chosen here.
-/
theorem theorem1_iid_cutoff_affordance_le_top_deviation_of_card_lower_cutoff
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {v pivot center deviation : ℝ}
    (hcard : active.card = m)
    (hlower : ∀ c ∈ active, pivot ≤ cutoff c)
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => pivot) :=
      AppliedModelingLib.Matching.cutoffCrossingProbability_le_constantCutoff_of_le
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hlower
    _ = cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
            (Finset.univ : Finset (Fin m)) v (fun _ => pivot) := by
      change AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => pivot) =
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
            (Finset.univ : Finset (Fin m)) v (fun _ => pivot)
      rw [AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass_pow_card,
        AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow]
      simp [hcard]
    _ ≤ AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation :=
      AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) hseparation

/--
For iid noise, a dense cutoff block with a common upper cutoff has failure
probability bounded by the deviation probability of an iid maximum of exactly
the block's integer size.  This is the event-level core of source equation
(143), with the `dense.card = m` rounding obligation explicit.
-/
theorem theorem1_one_sub_iid_cutoff_affordance_le_top_deviation_of_card_upper_cutoff
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {v ceiling center deviation : ℝ}
    (hcard : active.card = m)
    (hupper : ∀ c ∈ active, cutoff c ≤ ceiling)
    (hdeviation_pos : 0 < deviation)
    (hseparation : ceiling - v < center - deviation) :
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  have hconstant_le :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => ceiling) ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff :=
    AppliedModelingLib.Matching.constantCutoffProbability_le_of_cutoff_le
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hupper
  have hconstant_eq :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => ceiling) =
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
            (Finset.univ : Finset (Fin m)) v (fun _ => ceiling) := by
    change AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => ceiling) =
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw))
          (Finset.univ : Finset (Fin m)) v (fun _ => ceiling)
    rw [AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass_pow_card,
      AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow]
    simp [hcard]
  have hconstant_deviation :
      1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
            (Finset.univ : Finset (Fin m)) v (fun _ => ceiling) ≤
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation :=
    AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
      (Measure.pi (fun _ : Fin m => noiseAtomLaw)) hdeviation_pos hseparation
  rw [← hconstant_eq] at hconstant_deviation
  linarith

/--
Lift the dense-block high-match estimate to every upper cutoff block containing
it.  The subset relation is the source geometry; the probability implication
is checked by monotonicity of the actual cutoff-crossing event.
-/
theorem theorem1_one_sub_iid_cutoff_affordance_le_deviation_of_dense_subset
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    {dense upper : Finset (Fin n)} (cutoff : Fin n → ℝ)
    {v ceiling center deviation : ℝ}
    (hdense_subset : dense ⊆ upper)
    (hcard : dense.card = m)
    (hupper : ∀ c ∈ dense, cutoff c ≤ ceiling)
    (hdeviation_pos : 0 < deviation)
    (hseparation : ceiling - v < center - deviation) :
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  have hdense_le_upper :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) dense v cutoff ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff :=
    cutoffAffordanceProbability_mono_active
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hdense_subset
  have hdense_error :=
    theorem1_one_sub_iid_cutoff_affordance_le_top_deviation_of_card_upper_cutoff
      noiseAtomLaw dense cutoff hcard hupper hdeviation_pos hseparation
  linarith

/--
Apply the iid block estimate to an explicit finite partition of an upper
cutoff block.  The group count and group size are separate integer premises,
which prevents the source's real-valued `C^phi2` notation from being used as
an unproved finite partition.
-/
theorem theorem1_iid_cutoff_affordance_le_group_count_mul_deviation
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (groups : Finset (Finset (Fin n))) (cutoff : Fin n → ℝ)
    {v pivot center deviation : ℝ}
    (hcard : ∀ group ∈ groups, group.card = m)
    (hlower : ∀ group ∈ groups, ∀ c ∈ group, pivot ≤ cutoff c)
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) (groups.biUnion id) v cutoff ≤
      (groups.card : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  have hsum := theorem1_cutoff_affordance_biUnion_le_sum
    (Measure.pi (fun _ : Fin n => noiseAtomLaw)) groups v cutoff
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) (groups.biUnion id) v cutoff ≤
        ∑ group ∈ groups,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseAtomLaw)) group v cutoff := hsum
    _ ≤ groups.card •
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
      exact Finset.sum_le_card_nsmul groups
        (fun group => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) group v cutoff)
        _ (fun group hgroup =>
          theorem1_iid_cutoff_affordance_le_top_deviation_of_card_lower_cutoff
            noiseAtomLaw group cutoff (hcard group hgroup)
            (hlower group hgroup) hseparation)
    _ = (groups.card : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
      simp [nsmul_eq_mul]

/--
The Case 1 low-side probability estimate for the repaired upper cutoff block.
Each group is required to be a subset of that block, so its common lower
cutoff is proved from `theorem1CutoffAtOrAboveBlock` rather than assumed.
-/
theorem theorem1_iid_atOrAbove_affordance_le_group_count_mul_deviation
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ) (pivot : ℝ)
    (groups : Finset (Finset (Fin n))) {v center deviation : ℝ}
    (hcover : theorem1CutoffAtOrAboveBlock active cutoff pivot ⊆ groups.biUnion id)
    (hgroups_subset : ∀ group ∈ groups,
      group ⊆ theorem1CutoffAtOrAboveBlock active cutoff pivot)
    (hcard : ∀ group ∈ groups, group.card = m)
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff ≤
      (groups.card : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) (groups.biUnion id) v cutoff :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hcover
    _ ≤ (groups.card : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation :=
      theorem1_iid_cutoff_affordance_le_group_count_mul_deviation
        noiseAtomLaw groups cutoff hcard
        (fun group hgroup c hc => (Finset.mem_filter.mp
          (hgroups_subset group hgroup hc)).2)
        hseparation

/--
The Case 1 high-side cutoff event bound from the concrete dense window.  The
window is contained in the repaired at-or-above block even when a cutoff is
exactly the pivot.
-/
theorem theorem1_one_sub_iid_atOrAbove_affordance_le_dense_window_deviation
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {pivot width v center deviation : ℝ}
    (hcard : (theorem1CutoffWindowBlock active cutoff pivot width).card = m)
    (hdeviation_pos : 0 < deviation)
    (hseparation : pivot + width - v < center - deviation) :
    1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  apply theorem1_one_sub_iid_cutoff_affordance_le_deviation_of_dense_subset
    noiseAtomLaw (cutoff := cutoff)
    (theorem1CutoffWindowBlock_subset_atOrAboveBlock active cutoff pivot width)
    hcard
  · intro c hc
    exact (Finset.mem_filter.mp hc).2.2
  · exact hdeviation_pos
  · exact hseparation

/--
Concrete dense-branch analytic bridge.  This composes the repaired cutoff
partition, exact iid cutoff events, capacity mass budget, and a supplied
value-window mass estimate.  Its only remaining inputs are source primitives:
an integer grouping of the upper block, the dense-window cardinality, the
two pointwise geometric separations, the actual clearing mass identity, and
the Holder-derived middle-window mass bound.
-/
theorem theorem1_iid_dense_group_low_affordance_integral_le
    {n m : ℕ} [NeZero m]
    (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (pivot width : ℝ) (groups : Finset (Finset (Fin n)))
    {center radius lowPivot highPivot vS totalSupply middleMass : ℝ}
    (hcover : theorem1CutoffAtOrAboveBlock active cutoff pivot ⊆ groups.biUnion id)
    (hgroups_subset : ∀ group ∈ groups,
      group ⊆ theorem1CutoffAtOrAboveBlock active cutoff pivot)
    (hgroup_card : ∀ group ∈ groups, group.card = m)
    (hdense_card : (theorem1CutoffWindowBlock active cutoff pivot width).card = m)
    (hradius_pos : 0 < radius)
    (hradius_le_half :
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center radius ≤ 1 / 2)
    (hlow_separation : ∀ v ∈ Set.Iio lowPivot,
      center + radius ≤ pivot - v)
    (hhigh_separation : ∀ v ∈ Set.Ioi highPivot,
      pivot + width - v < center - radius)
    (hfull_capacity :
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw))
          (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) = totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hlow_high : lowPivot ≤ highPivot)
    (hhigh_vS : highPivot ≤ vS)
    (hmiddle : valueLaw.real (Set.Icc lowPivot highPivot) ≤ middleMass) :
    (∫ v : ℝ,
      (Set.Iic vS).indicator
        (fun v => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff) v
      ∂valueLaw) ≤
      (groups.card : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center radius +
        middleMass + 2 * totalSupply *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center radius := by
  let upper : Finset (Fin n) := theorem1CutoffAtOrAboveBlock active cutoff pivot
  let p : ℝ → ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff
  let fullP : ℝ → ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseAtomLaw))
      (Finset.univ : Finset (Fin n)) v cutoff
  let error : ℝ := AppliedModelingLib.Matching.topOrderDeviationProbability
    (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center radius
  have hp : Integrable p valueLaw := by
    simpa [p, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) valueLaw upper cutoff)
  have hfullP : Integrable fullP valueLaw := by
    simpa [fullP, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) valueLaw
        (Finset.univ : Finset (Fin n)) cutoff)
  have hp_nonneg : ∀ v, 0 ≤ p v := by
    intro v
    exact cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff
  have hp_le_one : ∀ v, p v ≤ 1 := by
    intro v
    exact cutoffAffordanceProbability_le_one
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) upper v cutoff
  have herror_nonneg : 0 ≤ error := by
    change 0 ≤ (Measure.pi (fun _ : Fin m => noiseAtomLaw)).real
      {noise : Fin m → ℝ |
        radius < |AppliedModelingLib.Probability.upperOrderStatistic noise
          (AppliedModelingLib.Probability.topSampleRank (n := m)) - center|}
    exact measureReal_nonneg
  have hupper_le_full : ∀ v, p v ≤ fullP v := by
    intro v
    exact cutoffAffordanceProbability_mono_active
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) (Finset.subset_univ upper)
  have htotal : (∫ v, p v ∂valueLaw) ≤ totalSupply := by
    calc
      (∫ v, p v ∂valueLaw) ≤ ∫ v, fullP v ∂valueLaw :=
        integral_mono hp hfullP hupper_le_full
      _ = totalSupply := by
        simpa [fullP] using hfull_capacity
  have hlow : ∀ v ∈ Set.Iio lowPivot,
      p v ≤ (groups.card : ℝ) * error := by
    intro v hv
    simpa [p, upper, error] using
      (theorem1_iid_atOrAbove_affordance_le_group_count_mul_deviation
        noiseAtomLaw active cutoff pivot groups hcover hgroups_subset hgroup_card
        (hlow_separation v hv))
  have hhigh : ∀ v ∈ Set.Ioi highPivot, 1 - error ≤ p v := by
    intro v hv
    have hfailure :=
      theorem1_one_sub_iid_atOrAbove_affordance_le_dense_window_deviation
        noiseAtomLaw active cutoff hdense_card hradius_pos
        (hhigh_separation v hv)
    dsimp [p, upper, error]
    linarith
  have hclosed := theorem1_low_affordance_integral_le_of_analytic_primitives
    valueLaw p hp hp_nonneg hp_le_one
    (mul_nonneg (by exact_mod_cast groups.card.zero_le) herror_nonneg)
    herror_nonneg (by simpa [error] using hradius_le_half)
    hlow_high hhigh_vS hlow hhigh htotal htail_normalization hmiddle
  simpa [p, upper, error] using hclosed

/--
The strict source low side follows from the stronger closed-tail analytic
bound.  The boundary atom at `vS` remains part of the checked closed estimate;
this theorem merely restricts that estimate to the literal source region
`v < vS`.
-/
theorem theorem1_strict_low_affordance_integral_le_of_closed_low_bound
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    (hp_nonneg : ∀ v, 0 ≤ p v) {vS bound : ℝ}
    (hclosed : (∫ v, (Set.Iic vS).indicator p v ∂valueLaw) ≤ bound) :
    (∫ v, (Set.Iio vS).indicator p v ∂valueLaw) ≤ bound := by
  have hsubset : Set.Iio vS ⊆ Set.Iic vS := Set.Iio_subset_Iic_self
  have hrestrict :
      (∫ v in Set.Iio vS, p v ∂valueLaw) ≤
        ∫ v in Set.Iic vS, p v ∂valueLaw :=
    setIntegral_mono_set hp.integrableOn
      (ae_of_all (valueLaw.restrict (Set.Iic vS)) hp_nonneg) hsubset.eventuallyLE
  rw [integral_indicator measurableSet_Iio]
  exact hrestrict.trans (by
    simpa [integral_indicator measurableSet_Iic] using hclosed)

end

end PG24NoisyMatchingMarkets

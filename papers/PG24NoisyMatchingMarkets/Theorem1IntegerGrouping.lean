import PG24NoisyMatchingMarkets.Theorem1AnalyticTailBridge
import Mathlib.Tactic

/-!
# PG24 Theorem 1 integer grouping

This module gives the finite, integer-valued grouping construction needed for
the upper cutoff block.  It deliberately uses quotient blocks of an arbitrary
finite set and a visible final remainder block; it never interprets a real
rate parameter as a finite cardinality.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open MeasureTheory
open AppliedModelingLib.Matching

universe u

/-- Rank an element of a finite block by a fixed finite equivalence. -/
noncomputable def theorem1BlockRank {α : Type u} [DecidableEq α]
    (block : Finset α) (x : α) : ℕ :=
  if hx : x ∈ block then (block.equivFin ⟨x, hx⟩).val else 0

/-- The `i`th integer quotient block, with a possible short final block. -/
noncomputable def theorem1IntegerGroup {α : Type u} [DecidableEq α]
    (block : Finset α) (m i : ℕ) : Finset α :=
  block.filter fun x => theorem1BlockRank block x / m = i

/-- A safe upper bound on the number of quotient blocks, including a remainder slot. -/
def theorem1IntegerGroupCount {α : Type u} [DecidableEq α]
    (block : Finset α) (m : ℕ) : ℕ :=
  block.card / m + 1

/-- The finite family of quotient blocks, retaining the final remainder block. -/
noncomputable def theorem1IntegerGroups {α : Type u} [DecidableEq α]
    (block : Finset α) (m : ℕ) : Finset (Finset α) :=
  (Finset.range (theorem1IntegerGroupCount block m)).image
    (theorem1IntegerGroup block m)

theorem theorem1BlockRank_eq_of_mem {α : Type u} [DecidableEq α]
    (block : Finset α) {x : α} (hx : x ∈ block) :
    theorem1BlockRank block x = (block.equivFin ⟨x, hx⟩).val := by
  simp [theorem1BlockRank, hx]

theorem theorem1BlockRank_lt_card {α : Type u} [DecidableEq α]
    (block : Finset α) {x : α} (hx : x ∈ block) :
    theorem1BlockRank block x < block.card := by
  rw [theorem1BlockRank_eq_of_mem block hx]
  exact (block.equivFin ⟨x, hx⟩).isLt

theorem theorem1BlockRank_injective_on {α : Type u} [DecidableEq α]
    (block : Finset α) : Set.InjOn (theorem1BlockRank block) (↑block : Set α) := by
  intro x hx y hy hxy
  rw [theorem1BlockRank_eq_of_mem block hx,
    theorem1BlockRank_eq_of_mem block hy] at hxy
  have hsubtype : (⟨x, hx⟩ : block) = ⟨y, hy⟩ :=
    block.equivFin.injective (Fin.ext hxy)
  exact congrArg Subtype.val hsubtype

theorem theorem1IntegerGroup_subset_block {α : Type u} [DecidableEq α]
    (block : Finset α) (m i : ℕ) :
    theorem1IntegerGroup block m i ⊆ block := by
  exact Finset.filter_subset _ _

theorem theorem1IntegerGroup_mem_iff {α : Type u} [DecidableEq α]
    (block : Finset α) (m i : ℕ) (x : α) :
    x ∈ theorem1IntegerGroup block m i ↔
      x ∈ block ∧ theorem1BlockRank block x / m = i := by
  simp [theorem1IntegerGroup]

theorem theorem1IntegerGroup_cover {α : Type u} [DecidableEq α]
    (block : Finset α) {m : ℕ} :
    block ⊆ (Finset.range (theorem1IntegerGroupCount block m)).biUnion
      (theorem1IntegerGroup block m) := by
  intro x hx
  let i := theorem1BlockRank block x / m
  have hrank_le : theorem1BlockRank block x ≤ block.card :=
    Nat.le_of_lt (theorem1BlockRank_lt_card block hx)
  have hi_le : i ≤ block.card / m := by
    exact Nat.div_le_div_right hrank_le
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr ?_, ?_⟩
  · exact Nat.lt_succ_of_le hi_le
  · exact Finset.mem_filter.mpr ⟨hx, rfl⟩

/-- Every quotient block has at most the requested integer size. -/
theorem theorem1IntegerGroup_card_le {α : Type u} [DecidableEq α]
    (block : Finset α) {m i : ℕ} (hm : 0 < m) :
    (theorem1IntegerGroup block m i).card ≤ m := by
  classical
  let group : Finset α := theorem1IntegerGroup block m i
  let residue : group → Fin m := fun x =>
    ⟨theorem1BlockRank block x.1 % m, Nat.mod_lt _ hm⟩
  have hresidue_injective : Function.Injective residue := by
    intro x y hxy
    apply Subtype.ext
    have hxmem : x.1 ∈ theorem1IntegerGroup block m i := by
      exact x.2
    have hymem : y.1 ∈ theorem1IntegerGroup block m i := by
      exact y.2
    have hxblock : x.1 ∈ block := (Finset.mem_filter.mp hxmem).1
    have hyblock : y.1 ∈ block := (Finset.mem_filter.mp hymem).1
    have hxquot : theorem1BlockRank block x.1 / m = i :=
      (Finset.mem_filter.mp hxmem).2
    have hyquot : theorem1BlockRank block y.1 / m = i :=
      (Finset.mem_filter.mp hymem).2
    have hmod : theorem1BlockRank block x.1 % m =
        theorem1BlockRank block y.1 % m := by
      simpa [residue] using congrArg Fin.val hxy
    have hrank : theorem1BlockRank block x.1 = theorem1BlockRank block y.1 := by
      calc
        theorem1BlockRank block x.1 =
            theorem1BlockRank block x.1 / m * m + theorem1BlockRank block x.1 % m :=
          (Nat.div_add_mod' _ _).symm
        _ = theorem1BlockRank block y.1 / m * m + theorem1BlockRank block y.1 % m := by
          rw [hxquot, hyquot, hmod]
        _ = theorem1BlockRank block y.1 := Nat.div_add_mod' _ _
    exact theorem1BlockRank_injective_on block hxblock hyblock hrank
  simpa [group] using Fintype.card_le_of_injective residue hresidue_injective

/-- The quotient groups cover the original block exactly. -/
theorem theorem1IntegerGroups_biUnion_eq_block {α : Type u} [DecidableEq α]
    (block : Finset α) (m : ℕ) :
    (theorem1IntegerGroups block m).biUnion id = block := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨group, hgroup, hxgroup⟩
    rcases Finset.mem_image.mp hgroup with ⟨i, hi, rfl⟩
    exact theorem1IntegerGroup_subset_block block m i hxgroup
  · intro x hx
    rcases Finset.mem_biUnion.mp (theorem1IntegerGroup_cover block hx) with
      ⟨i, hi, hxgroup⟩
    exact Finset.mem_biUnion.mpr ⟨theorem1IntegerGroup block m i,
      Finset.mem_image.mpr ⟨i, hi, rfl⟩, hxgroup⟩

/-- The explicit number of quotient/remainder blocks is at most `block.card / m + 1`. -/
theorem theorem1IntegerGroups_card_le_count {α : Type u} [DecidableEq α]
    (block : Finset α) (m : ℕ) :
    (theorem1IntegerGroups block m).card ≤ theorem1IntegerGroupCount block m := by
  calc
    (theorem1IntegerGroups block m).card ≤
        (Finset.range (theorem1IntegerGroupCount block m)).card :=
      Finset.card_image_le
    _ = theorem1IntegerGroupCount block m := Finset.card_range _

/-- A capacity bound transfers directly to the visible integer group count. -/
theorem theorem1IntegerGroupCount_le_capacity_div_add_one {α : Type u} [DecidableEq α]
    (block : Finset α) (m capacity : ℕ) (hcapacity : block.card ≤ capacity) :
    theorem1IntegerGroupCount block m ≤ capacity / m + 1 := by
  dsimp [theorem1IntegerGroupCount]
  exact Nat.succ_le_succ (Nat.div_le_div_right hcapacity)

/-- For a block of `Fin n`, the source union factor is bounded by `n / m + 1`. -/
theorem theorem1IntegerGroupCount_le_index_div_add_one
    {n m : ℕ} (block : Finset (Fin n)) :
    theorem1IntegerGroupCount block m ≤ n / m + 1 := by
  apply theorem1IntegerGroupCount_le_capacity_div_add_one block m n
  simpa using Finset.card_le_card (Finset.subset_univ block)

/-- Every member of the explicit quotient/remainder family has cardinality at most `m`. -/
theorem theorem1IntegerGroups_card_le {α : Type u} [DecidableEq α]
    (block : Finset α) {m : ℕ} [NeZero m]
    {group : Finset α} (hgroup : group ∈ theorem1IntegerGroups block m) :
    group.card ≤ m := by
  rcases Finset.mem_image.mp hgroup with ⟨i, hi, rfl⟩
  exact theorem1IntegerGroup_card_le block (NeZero.pos m)

/-- Every quotient/remainder group remains inside the block it partitions. -/
theorem theorem1IntegerGroups_member_subset_block {α : Type u} [DecidableEq α]
    (block : Finset α) (m : ℕ) {group : Finset α}
    (hgroup : group ∈ theorem1IntegerGroups block m) :
    group ⊆ block := by
  rcases Finset.mem_image.mp hgroup with ⟨i, hi, rfl⟩
  exact theorem1IntegerGroup_subset_block block m i

/--
An iid cutoff block of at most `m` coordinates is bounded by the deviation
probability for an iid block of exactly `m` coordinates.  This is the step
that accounts for the final short integer remainder without pretending that
its cardinality equals a real-valued rate.
-/
theorem theorem1_iid_cutoff_affordance_le_top_deviation_of_card_le_lower_cutoff
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {v pivot center deviation : ℝ}
    (hcard : active.card ≤ m)
    (hlower : ∀ c ∈ active, pivot ≤ cutoff c)
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  let base : ℝ := AppliedModelingLib.Probability.lowerCDFMass noiseAtomLaw (pivot - v)
  have hbase_nonneg : 0 ≤ base := by
    exact AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseAtomLaw _
  have hbase_le_one : base ≤ 1 := by
    exact AppliedModelingLib.Probability.lowerCDFMass_le_one noiseAtomLaw _
  have hpow : base ^ m ≤ base ^ active.card :=
    pow_right_anti₀ hbase_nonneg hbase_le_one hcard
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v cutoff ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) active v (fun _ => pivot) :=
      AppliedModelingLib.Matching.cutoffCrossingProbability_le_constantCutoff_of_le
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) hlower
    _ = 1 - base ^ active.card := by
      simpa [base] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass_pow_card
          (μ := noiseAtomLaw) active v pivot)
    _ ≤ 1 - base ^ m := by
      exact sub_le_sub_left hpow 1
    _ = cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
            (Finset.univ : Finset (Fin m)) v (fun _ => pivot) := by
      symm
      change AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw))
          (Finset.univ : Finset (Fin m)) v (fun _ => pivot) = _
      simpa [base] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow
          (μ := noiseAtomLaw) (n := m) v pivot)
    _ ≤ AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation :=
      AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
        (Measure.pi (fun _ : Fin m => noiseAtomLaw)) hseparation

/-- Nonnegativity of the actual iid maximum-deviation event probability. -/
theorem theorem1_iid_topOrderDeviationProbability_nonneg
    {m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw] (center deviation : ℝ) :
    0 ≤ AppliedModelingLib.Matching.topOrderDeviationProbability
      (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  change 0 ≤ (Measure.pi (fun _ : Fin m => noiseAtomLaw)).real
    {noise : Fin m → ℝ |
      deviation < |AppliedModelingLib.Probability.upperOrderStatistic noise
        (AppliedModelingLib.Probability.topSampleRank (n := m)) - center|}
  exact measureReal_nonneg

/--
The source union estimate for an arbitrary finite cutoff block, with the
integer quotient/remainder construction substituted for the informal grouping
step.  The final bound retains the concrete count `block.card / m + 1`.
-/
theorem theorem1_iid_cutoff_affordance_le_integer_group_count_mul_deviation
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw]
    (block : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {v pivot center deviation : ℝ}
    (hlower : ∀ c ∈ block, pivot ≤ cutoff c)
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) block v cutoff ≤
      (theorem1IntegerGroupCount block m : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  let groups := theorem1IntegerGroups block m
  let error : ℝ := AppliedModelingLib.Matching.topOrderDeviationProbability
    (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation
  have herror_nonneg : 0 ≤ error := by
    exact theorem1_iid_topOrderDeviationProbability_nonneg
      noiseAtomLaw center deviation
  have hblock : groups.biUnion id = block := by
    simpa [groups] using theorem1IntegerGroups_biUnion_eq_block block m
  have hgroups_count : groups.card ≤ theorem1IntegerGroupCount block m := by
    simpa [groups] using theorem1IntegerGroups_card_le_count block m
  have hgroup_card : ∀ group ∈ groups, group.card ≤ m := by
    intro group hgroup
    apply theorem1IntegerGroups_card_le block
    simpa [groups] using hgroup
  have hgroup_subset : ∀ group ∈ groups, group ⊆ block := by
    intro group hgroup
    apply theorem1IntegerGroups_member_subset_block block m
    simpa [groups] using hgroup
  have hgroup_bound : ∀ group ∈ groups,
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) group v cutoff ≤ error := by
    intro group hgroup
    dsimp [error]
    exact theorem1_iid_cutoff_affordance_le_top_deviation_of_card_le_lower_cutoff
      noiseAtomLaw group cutoff (hgroup_card group hgroup)
      (fun c hc => hlower c (hgroup_subset group hgroup hc)) hseparation
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) block v cutoff =
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) (groups.biUnion id) v cutoff := by
      rw [hblock]
    _ ≤ ∑ group ∈ groups,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) group v cutoff :=
      theorem1_cutoff_affordance_biUnion_le_sum
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) groups v cutoff
    _ ≤ groups.card • error := by
      exact Finset.sum_le_card_nsmul groups
        (fun group => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseAtomLaw)) group v cutoff)
        _ hgroup_bound
    _ = (groups.card : ℝ) * error := by
      simp [nsmul_eq_mul]
    _ ≤ (theorem1IntegerGroupCount block m : ℝ) * error := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgroups_count) herror_nonneg
    _ = (theorem1IntegerGroupCount block m : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
      rfl

/--
The same union estimate expressed with the ambient number of colleges.  This
is the exact integer replacement for the source's informal `C / m` factor.
-/
theorem theorem1_iid_cutoff_affordance_le_index_div_add_one_mul_deviation
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw]
    (block : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {v pivot center deviation : ℝ}
    (hlower : ∀ c ∈ block, pivot ≤ cutoff c)
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) block v cutoff ≤
      ((n / m + 1 : ℕ) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  have hgroup := theorem1_iid_cutoff_affordance_le_integer_group_count_mul_deviation
    (m := m) noiseAtomLaw block cutoff hlower hseparation
  have hcount : theorem1IntegerGroupCount block m ≤ n / m + 1 :=
    theorem1IntegerGroupCount_le_index_div_add_one block
  have herror_nonneg := theorem1_iid_topOrderDeviationProbability_nonneg
    (m := m) noiseAtomLaw center deviation
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw)) block v cutoff ≤
        (theorem1IntegerGroupCount block m : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := hgroup
    _ ≤ ((n / m + 1 : ℕ) : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) herror_nonneg

/--
Apply the explicit integer grouping to the repaired upper cutoff block.  The
lower cutoff condition is derived from membership in that block, rather than
accepted as a theorem-sized probability premise.
-/
theorem theorem1_iid_atOrAbove_affordance_le_integer_group_count_mul_deviation
    {n m : ℕ} [NeZero m] (noiseAtomLaw : Measure ℝ)
    [IsProbabilityMeasure noiseAtomLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ) (pivot : ℝ)
    {v center deviation : ℝ}
    (hseparation : center + deviation ≤ pivot - v) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseAtomLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff ≤
      (theorem1IntegerGroupCount
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) m : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin m => noiseAtomLaw)) center deviation := by
  apply theorem1_iid_cutoff_affordance_le_integer_group_count_mul_deviation
    noiseAtomLaw (theorem1CutoffAtOrAboveBlock active cutoff pivot) cutoff
  · intro c hc
    exact (Finset.mem_filter.mp hc).2
  · exact hseparation

/--
The dense-branch analytic estimate with the finite quotient/remainder
construction substituted for the source's informal `m`-sized grouping.  The
only probabilistic rate left visible here is the actual iid maximum-deviation
probability; no tail-rate estimate is postulated.
-/
theorem theorem1_iid_dense_integer_group_low_affordance_integral_le
    {n m : ℕ} [NeZero m]
    (noiseAtomLaw : Measure ℝ) [IsProbabilityMeasure noiseAtomLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (pivot width : ℝ)
    {center radius lowPivot highPivot vS totalSupply middleMass : ℝ}
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
      (theorem1IntegerGroupCount
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) m : ℝ) *
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
      p v ≤ (theorem1IntegerGroupCount upper m : ℝ) * error := by
    intro v hv
    simpa [p, upper, error] using
      (theorem1_iid_atOrAbove_affordance_le_integer_group_count_mul_deviation
        noiseAtomLaw active cutoff pivot (hlow_separation v hv))
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
    (mul_nonneg (by exact_mod_cast (theorem1IntegerGroupCount upper m).zero_le)
      herror_nonneg)
    herror_nonneg (by simpa [error] using hradius_le_half)
    hlow_high hhigh_vS hlow hhigh htotal htail_normalization hmiddle
  simpa [p, upper, error] using hclosed

end

end PG24NoisyMatchingMarkets

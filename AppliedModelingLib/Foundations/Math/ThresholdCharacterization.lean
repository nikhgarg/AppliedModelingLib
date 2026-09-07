import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Threshold Characterizations

Reusable one-dimensional cutoff lemmas for papers that turn monotone scalar
comparisons into threshold statements.

## Main declarations

- `exists_threshold_of_continuous_strictMonoOn_Icc_crossing`
- `LowerCutoffStrategy`, `monotone_of_lowerCutoffStrategy`
- `lowerCutoffStrategy_cutoff_eq`
- `exists_indifference_and_profitable_above_of_continuous_strictMonoOn_Icc_crossing`
- `exists_indifference_lower_cutoff_of_continuous_strictMono_crossing`
- `exists_indexed_indifference_lower_cutoffs_of_continuous_strictMono_crossing`
- `exists_chosen_below_of_lowerCutoff_lt`
- `exists_chosen_of_lowerCutoff`
- `exists_not_chosen_below_of_lowerCutoff`
- `bool_lowerCutoff_if_true_iff`
- `bool_lowerCutoff_true_of_le`
- `bool_lowerCutoff_false_of_lt`
- `CapacityThreshold`
- `exists_threshold_of_continuous_strictMonoOn_Icc`
- `exists_threshold_of_continuous_strictMonoOn_Icc_crossing_interval`
- `exists_threshold_of_continuous_strictMonoOn_Icc_interval`
- `exists_threshold_le_of_continuous_strictMonoOn_Icc_interval`
- `exists_threshold_le_of_continuous_strictMonoOn_Icc`
- `exists_threshold_of_continuous_strictAntiOn_Icc_crossing`
- `exists_threshold_of_continuous_strictAntiOn_Icc_crossing_interval`
- `exists_threshold_gt_of_continuous_strictAntiOn_Icc`
- `exists_threshold_le_of_continuous_strictAntiOn_Icc`
- `continuousOn_rightInverse_of_strictMono`
- `existsUnique_eq_of_continuous_strictMono_tendsto_atBot_atTop`
- `existsUnique_zero_and_nonneg_iff_of_continuous_strictMono_crossing`
- `existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop`
- `existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop`
-/

namespace AppliedModelingLib

noncomputable section

open Set

/--
Capacity-realizing upper-threshold condition for a scalar mass curve.

The value `threshold` realizes `capacity`, and the set of cutoffs whose mass is
at most capacity is exactly the upper ray above `threshold`.
-/
def CapacityThreshold (mass : ℝ → ℝ) (capacity threshold : ℝ) : Prop :=
  mass threshold = capacity ∧
    ∀ z : ℝ, mass z ≤ capacity ↔ threshold ≤ z

/-- A one-dimensional decision rule is a lower-cutoff rule. -/
def LowerCutoffStrategy (choose : ℝ → Prop) : Prop :=
  ∃ cutoff : ℝ, ∀ value : ℝ, choose value ↔ cutoff ≤ value

/-- Every lower-cutoff rule is monotone in the source direction. -/
theorem monotone_of_lowerCutoffStrategy
    {choose : ℝ → Prop} (hcutoff : LowerCutoffStrategy choose) :
    ∀ {low high : ℝ}, low ≤ high → choose low → choose high := by
  rcases hcutoff with ⟨cutoff, hchoose⟩
  intro low high hle hlow
  exact (hchoose high).2 ((hchoose low).1 hlow |>.trans hle)

/-- The finite cutoff representing a real lower-cutoff rule is unique. -/
theorem lowerCutoffStrategy_cutoff_eq
    {choose : ℝ → Prop} {left right : ℝ}
    (hleft : ∀ value : ℝ, choose value ↔ left ≤ value)
    (hright : ∀ value : ℝ, choose value ↔ right ≤ value) :
    left = right := by
  exact le_antisymm
    ((hleft right).1 ((hright right).2 le_rfl))
    ((hright left).1 ((hleft left).2 le_rfl))

/-- If a lower-cutoff rule has cutoff below a target, it chooses some value below that target. -/
theorem exists_chosen_below_of_lowerCutoff_lt
    {choose : ℝ → Prop} {cutoff target : ℝ}
    (hcutoff : ∀ value : ℝ, choose value ↔ cutoff ≤ value)
    (hcutoff_lt_target : cutoff < target) :
    ∃ value : ℝ, choose value ∧ value < target := by
  let value : ℝ := (cutoff + target) / 2
  have hcutoff_le_value : cutoff ≤ value := by
    dsimp [value]
    linarith
  have hvalue_lt_target : value < target := by
    dsimp [value]
    linarith
  exact ⟨value, (hcutoff value).2 hcutoff_le_value, hvalue_lt_target⟩

/-- Every finite lower-cutoff rule chooses at least one value, namely its cutoff. -/
theorem exists_chosen_of_lowerCutoff
    {choose : ℝ → Prop} {cutoff : ℝ}
    (hcutoff : ∀ value : ℝ, choose value ↔ cutoff ≤ value) :
    ∃ value : ℝ, choose value :=
  ⟨cutoff, (hcutoff cutoff).2 le_rfl⟩

/-- Every finite lower-cutoff rule rejects some value below its cutoff. -/
theorem exists_not_chosen_below_of_lowerCutoff
    {choose : ℝ → Prop} {cutoff : ℝ}
    (hcutoff : ∀ value : ℝ, choose value ↔ cutoff ≤ value) :
    ∃ value : ℝ, ¬ choose value := by
  refine ⟨cutoff - 1, ?_⟩
  intro hchoose
  have hle : cutoff ≤ cutoff - 1 := (hcutoff (cutoff - 1)).1 hchoose
  linarith

/-- The literal Boolean lower-cutoff decision is true exactly above the cutoff. -/
theorem bool_lowerCutoff_if_true_iff {cutoff value : ℝ} :
    (if cutoff ≤ value then true else false) = true ↔ cutoff ≤ value := by
  by_cases h : cutoff ≤ value
  · simp [h]
  · simp [h]

/-- A Boolean lower-cutoff rule chooses every value weakly above the cutoff. -/
theorem bool_lowerCutoff_true_of_le
    {choose : ℝ → Bool} {cutoff value : ℝ}
    (hcutoff : ∀ value : ℝ, choose value = true ↔ cutoff ≤ value)
    (hle : cutoff ≤ value) :
    choose value = true :=
  (hcutoff value).2 hle

/-- A Boolean lower-cutoff rule rejects every value strictly below the cutoff. -/
theorem bool_lowerCutoff_false_of_lt
    {choose : ℝ → Bool} {cutoff value : ℝ}
    (hcutoff : ∀ value : ℝ, choose value = true ↔ cutoff ≤ value)
    (hlt : value < cutoff) :
    choose value = false := by
  cases hchoose : choose value
  · rfl
  · have hle : cutoff ≤ value := (hcutoff value).1 (by simpa [hchoose])
    linarith

/--
If a continuous candidate outside option crosses a continuous strictly
increasing chosen-option payoff on an interval, then there is an interior
indifference point.  At that point, choosing weakly beats the outside option
exactly on the lower-threshold upper ray.
-/
theorem exists_indifference_lower_cutoff_of_continuous_strictMono_crossing
    {choosePayoff outsideAtCutoff : ℝ → ℝ} {low high : ℝ}
    (hcontChoose : ContinuousOn choosePayoff (Icc low high))
    (hcontOutside : ContinuousOn outsideAtCutoff (Icc low high))
    (hmonoChoose : StrictMono choosePayoff)
    (hlow_high : low < high)
    (hleft : choosePayoff low < outsideAtCutoff low)
    (hright : outsideAtCutoff high < choosePayoff high) :
    ∃ cutoff : ℝ,
      cutoff ∈ Ioo low high ∧
        outsideAtCutoff cutoff = choosePayoff cutoff ∧
          (∀ value : ℝ,
            outsideAtCutoff cutoff ≤ choosePayoff value ↔ cutoff ≤ value) ∧
            (∀ value : ℝ,
              choosePayoff value < outsideAtCutoff cutoff ↔ value < cutoff) := by
  let gap : ℝ → ℝ :=
    fun cutoff => choosePayoff cutoff - outsideAtCutoff cutoff
  have hgap_cont : ContinuousOn gap (Icc low high) :=
    hcontChoose.sub hcontOutside
  have hzero_mem : (0 : ℝ) ∈ Icc (gap low) (gap high) := by
    constructor <;> dsimp [gap] <;> linarith
  rcases intermediate_value_Icc hlow_high.le hgap_cont hzero_mem with
    ⟨cutoff, hcutoff_mem, hgap_zero⟩
  have hlow_lt_cutoff : low < cutoff := by
    have hne : cutoff ≠ low := by
      intro h
      subst cutoff
      dsimp [gap] at hgap_zero
      linarith
    exact lt_of_le_of_ne hcutoff_mem.1 (Ne.symm hne)
  have hcutoff_lt_high : cutoff < high := by
    have hne : cutoff ≠ high := by
      intro h
      subst cutoff
      dsimp [gap] at hgap_zero
      linarith
    exact lt_of_le_of_ne hcutoff_mem.2 hne
  have hindiff :
      outsideAtCutoff cutoff = choosePayoff cutoff := by
    dsimp [gap] at hgap_zero
    linarith
  refine ⟨cutoff, ⟨hlow_lt_cutoff, hcutoff_lt_high⟩,
    hindiff, ?_, ?_⟩
  · intro value
    constructor
    · intro hbest
      by_contra hnot
      have hvalue_lt : value < cutoff := lt_of_not_ge hnot
      have hstrict : choosePayoff value < choosePayoff cutoff :=
        hmonoChoose hvalue_lt
      rw [← hindiff] at hstrict
      linarith
    · intro hcutoff_le_value
      rcases lt_or_eq_of_le hcutoff_le_value with hlt | rfl
      · have hstrict : choosePayoff cutoff < choosePayoff value :=
          hmonoChoose hlt
        rw [hindiff]
        exact le_of_lt hstrict
      · rw [hindiff]
  · intro value
    constructor
    · intro hstrict
      by_contra hnot
      have hcutoff_le_value : cutoff ≤ value := le_of_not_gt hnot
      have hbest :
          outsideAtCutoff cutoff ≤ choosePayoff value := by
        rcases lt_or_eq_of_le hcutoff_le_value with hlt | rfl
        · have hmono : choosePayoff cutoff < choosePayoff value :=
            hmonoChoose hlt
          rw [hindiff]
          exact le_of_lt hmono
        · rw [hindiff]
      linarith
    · intro hvalue_lt
      have hmono : choosePayoff value < choosePayoff cutoff :=
        hmonoChoose hvalue_lt
      rw [← hindiff] at hmono
      exact hmono

/--
Indexed version of
`exists_indifference_lower_cutoff_of_continuous_strictMono_crossing`: for each
profile, a continuous crossing against a strictly increasing chosen payoff
produces an interior cutoff and a lower-cutoff choice rule.  A nonempty index
set also gives a concrete value below one cutoff where choosing is not weakly
optimal.
-/
theorem exists_indexed_indifference_lower_cutoffs_of_continuous_strictMono_crossing
    {ι : Type*} [Nonempty ι]
    (choosePayoff outsideAtCutoff : ι → ℝ → ℝ)
    (low high : ι → ℝ)
    (hcontChoose :
      ∀ i, ContinuousOn (choosePayoff i) (Icc (low i) (high i)))
    (hcontOutside :
      ∀ i, ContinuousOn (outsideAtCutoff i) (Icc (low i) (high i)))
    (hmonoChoose : ∀ i, StrictMono (choosePayoff i))
    (hlow_high : ∀ i, low i < high i)
    (hleft : ∀ i, choosePayoff i (low i) < outsideAtCutoff i (low i))
    (hright : ∀ i, outsideAtCutoff i (high i) < choosePayoff i (high i)) :
    ∃ cutoff : ι → ℝ,
      (∀ i, cutoff i ∈ Ioo (low i) (high i)) ∧
        (∀ i, outsideAtCutoff i (cutoff i) = choosePayoff i (cutoff i)) ∧
          (∀ i value,
            outsideAtCutoff i (cutoff i) ≤ choosePayoff i value ↔
              cutoff i ≤ value) ∧
            (∃ i value,
              ¬ outsideAtCutoff i (cutoff i) ≤ choosePayoff i value) ∧
              (∀ i, ∃ c : ℝ, ∀ value : ℝ,
                outsideAtCutoff i (cutoff i) ≤ choosePayoff i value ↔
                  c ≤ value) := by
  have hcutoff_exists :
      ∀ i, ∃ cutoff : ℝ,
        cutoff ∈ Ioo (low i) (high i) ∧
          outsideAtCutoff i cutoff = choosePayoff i cutoff ∧
            (∀ value : ℝ,
              outsideAtCutoff i cutoff ≤ choosePayoff i value ↔
                cutoff ≤ value) ∧
              (∀ value : ℝ,
                choosePayoff i value < outsideAtCutoff i cutoff ↔
                  value < cutoff) := by
    intro i
    exact
      exists_indifference_lower_cutoff_of_continuous_strictMono_crossing
        (hcontChoose i) (hcontOutside i) (hmonoChoose i)
        (hlow_high i) (hleft i) (hright i)
  choose cutoff hmem hindiff hthreshold _hbelow using hcutoff_exists
  refine ⟨cutoff, hmem, hindiff, hthreshold, ?_, ?_⟩
  · let i : ι := Classical.choice inferInstance
    refine ⟨i, low i, ?_⟩
    rw [hthreshold i (low i)]
    exact not_le.mpr (hmem i).1
  · intro i
    exact ⟨cutoff i, hthreshold i⟩

/--
If a continuous strictly increasing scalar function crosses a level between a
low point and a cutoff, then there is an interior indifference point, all
points from that indifference point to the cutoff weakly clear the level, and
some interior point strictly clears it.
-/
theorem exists_indifference_and_profitable_above_of_continuous_strictMonoOn_Icc_crossing
    {f : ℝ → ℝ} {low cutoff level : ℝ}
    (hcont : ContinuousOn f (Icc low cutoff))
    (hmono : StrictMonoOn f (Icc low cutoff))
    (hlow_cutoff : low < cutoff)
    (hlow : f low < level)
    (hcutoff : level < f cutoff) :
    ∃ indifferent : ℝ,
      indifferent ∈ Ioo low cutoff ∧
        f indifferent = level ∧
          (∀ x ∈ Icc indifferent cutoff, level ≤ f x) ∧
            ∃ profitable : ℝ,
              profitable ∈ Ioo indifferent cutoff ∧ level < f profitable := by
  have hlevel_mem : level ∈ Icc (f low) (f cutoff) :=
    ⟨hlow.le, hcutoff.le⟩
  rcases intermediate_value_Icc hlow_cutoff.le hcont hlevel_mem with
    ⟨indifferent, hindiff_mem, hindiff_eq⟩
  have hlow_lt_indiff : low < indifferent := by
    have hne : indifferent ≠ low := by
      intro hEq
      subst indifferent
      linarith
    exact lt_of_le_of_ne hindiff_mem.1 (Ne.symm hne)
  have hindiff_lt_cutoff : indifferent < cutoff := by
    have hne : indifferent ≠ cutoff := by
      intro hEq
      subst indifferent
      linarith
    exact lt_of_le_of_ne hindiff_mem.2 hne
  have hweak : ∀ x ∈ Icc indifferent cutoff, level ≤ f x := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hindiff_lt_x | rfl
    · have hstrict : f indifferent < f x :=
        hmono hindiff_mem ⟨hindiff_mem.1.trans hx.1, hx.2⟩ hindiff_lt_x
      exact (by simpa [hindiff_eq] using hstrict.le)
    · exact le_of_eq hindiff_eq.symm
  let profitable : ℝ := (indifferent + cutoff) / 2
  have hprofitable_low : indifferent < profitable := by
    dsimp [profitable]
    linarith
  have hprofitable_high : profitable < cutoff := by
    dsimp [profitable]
    linarith
  have hprofitable_mem_big : profitable ∈ Icc low cutoff :=
    ⟨le_of_lt (hlow_lt_indiff.trans hprofitable_low),
      le_of_lt hprofitable_high⟩
  have hprofitable_strict : f indifferent < f profitable :=
    hmono hindiff_mem hprofitable_mem_big hprofitable_low
  refine ⟨indifferent, ⟨hlow_lt_indiff, hindiff_lt_cutoff⟩,
    hindiff_eq, hweak, profitable,
    ⟨hprofitable_low, hprofitable_high⟩, ?_⟩
  simpa [hindiff_eq] using hprofitable_strict

/--
Continuity of a scalar merit term after a cutoff transformation.

This small wrapper is useful in threshold proofs where cost first determines a
cutoff and merit is then evaluated at that cutoff.
-/
theorem continuousOn_comp_of_mapsTo
    {f g : ℝ → ℝ} {s t : Set ℝ}
    (hf : ContinuousOn f t) (hg : ContinuousOn g s)
    (hmap : MapsTo g s t) :
    ContinuousOn (fun x => f (g x)) s :=
  hf.comp hg hmap

/--
If a cutoff is strictly increasing in cost and merit is strictly decreasing in
the cutoff, then merit is strictly decreasing in cost.
-/
theorem strictAntiOn_comp_strictMonoOn
    {f g : ℝ → ℝ} {s t : Set ℝ}
    (hf : StrictAntiOn f t) (hg : StrictMonoOn g s)
    (hmap : MapsTo g s t) :
    StrictAntiOn (fun x => f (g x)) s := by
  intro x hx y hy hxy
  exact hf (hmap hx) (hmap hy) (hg hx hy hxy)

/--
A right inverse of a strictly increasing scalar function is continuous on its
domain.

This is useful for implicit cutoff proofs.  If `base (root y) = y` for every
`y` in a cost domain, then strict monotonicity of `base` forces nearby costs to
have nearby roots; no separate continuity assumption on `root` is needed.
-/
theorem continuousOn_rightInverse_of_strictMono
    {base root : ℝ → ℝ} {s : Set ℝ}
    (hbase_mono : StrictMono base)
    (hroot : ∀ y ∈ s, base (root y) = y) :
    ContinuousOn root s := by
  intro y hy
  rw [ContinuousWithinAt]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    have hbase_lower_lt_y : base lower < y := by
      simpa [hroot y hy] using hbase_mono hlower
    have hevent :
        ∀ᶠ z in nhdsWithin y s, base lower < z :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbase_lower_lt_y)
    filter_upwards [hevent, self_mem_nhdsWithin] with z hz hs
    by_contra hnot
    have hle : root z ≤ lower := le_of_not_gt hnot
    have hbase_le : base (root z) ≤ base lower :=
      hbase_mono.monotone hle
    have hroot_z : base (root z) = z := hroot z hs
    linarith
  · intro upper hupper
    have hy_lt_base_upper : y < base upper := by
      simpa [hroot y hy] using hbase_mono hupper
    have hevent :
        ∀ᶠ z in nhdsWithin y s, z < base upper :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hy_lt_base_upper)
    filter_upwards [hevent, self_mem_nhdsWithin] with z hz hs
    by_contra hnot
    have hle : upper ≤ root z := le_of_not_gt hnot
    have hbase_le : base upper ≤ base (root z) :=
      hbase_mono.monotone hle
    have hroot_z : base (root z) = z := hroot z hs
    linarith

/--
An implicitly defined root of a jointly continuous scalar function varies
continuously when the function is strictly decreasing in its root coordinate.
Unlike `continuousOn_rightInverse_of_strictMono`, the strictly monotone slice
is allowed to vary with the parameter.

The proof uses Mathlib's standard order-topology neighborhood API, including
`ContinuousAt.preimage_mem_nhds`, from the Apache-2.0-licensed
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
repository at pinned commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external proof or code is copied or ported.
-/
theorem continuousOn_implicitRoot_of_continuous_strictAnti
    {cost : ℝ → ℝ → ℝ} {root : ℝ → ℝ} {domain : Set ℝ} {level : ℝ}
    (hcost : Continuous fun pair : ℝ × ℝ => cost pair.1 pair.2)
    (hanti : ∀ target, StrictAnti (fun initial => cost initial target))
    (hroot : ∀ target ∈ domain, cost (root target) target = level) :
    ContinuousOn root domain := by
  have hslice : ∀ initial, Continuous (fun target => cost initial target) := by
    intro initial
    exact hcost.comp (continuous_const.prodMk continuous_id)
  intro target htarget
  rw [ContinuousWithinAt]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    have hlevel_lt : level < cost lower target := by
      rw [← hroot target htarget]
      exact hanti target hlower
    have hnear : ∀ᶠ nearby in nhdsWithin target domain, level < cost lower nearby := by
      apply mem_nhdsWithin_of_mem_nhds
      exact (hslice lower).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hlevel_lt)
    filter_upwards [hnear, self_mem_nhdsWithin] with nearby hnear hnearDomain
    by_contra hnot
    have hroot_le : root nearby ≤ lower := le_of_not_gt hnot
    rcases lt_or_eq_of_le hroot_le with hlt | heq
    · have hcost_lt : cost lower nearby < cost (root nearby) nearby :=
        hanti nearby hlt
      rw [hroot nearby hnearDomain] at hcost_lt
      exact (not_lt_of_ge hcost_lt.le) hnear
    · rw [← heq, hroot nearby hnearDomain] at hnear
      exact (lt_irrefl level) hnear
  · intro upper hupper
    have hcost_lt : cost upper target < level := by
      rw [← hroot target htarget]
      exact hanti target hupper
    have hnear : ∀ᶠ nearby in nhdsWithin target domain, cost upper nearby < level := by
      apply mem_nhdsWithin_of_mem_nhds
      exact (hslice upper).continuousAt.preimage_mem_nhds (Iio_mem_nhds hcost_lt)
    filter_upwards [hnear, self_mem_nhdsWithin] with nearby hnear hnearDomain
    by_contra hnot
    have hupper_le : upper ≤ root nearby := le_of_not_gt hnot
    rcases lt_or_eq_of_le hupper_le with hlt | heq
    · have hcost_lt : cost (root nearby) nearby < cost upper nearby :=
        hanti nearby hlt
      rw [hroot nearby hnearDomain] at hcost_lt
      exact (not_lt_of_ge hnear.le) hcost_lt
    · rw [heq, hroot nearby hnearDomain] at hnear
      exact (lt_irrefl level) hnear

/--
An implicitly defined cost level is continuous when the cost is jointly
continuous and strictly decreases in its initial coordinate below the target.
This is the natural one-sided form for an upward-manipulation cost: values at
or above the target need not satisfy any artificial monotonicity condition.

The proof uses Mathlib's order-topology neighborhood API from the Apache-2.0
licensed [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
repository at pinned commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external proof or code is copied or ported.
-/
theorem continuousOn_implicitRoot_of_continuous_strictAntiBelow
    {cost : ℝ → ℝ → ℝ} {root : ℝ → ℝ} {domain : Set ℝ} {level : ℝ}
    (hcost : Continuous fun pair : ℝ × ℝ => cost pair.1 pair.2)
    (hanti : ∀ target {lowerInitial higherInitial : ℝ},
      lowerInitial < higherInitial → higherInitial < target →
        cost higherInitial target < cost lowerInitial target)
    (hroot : ∀ target ∈ domain,
      root target < target ∧ cost (root target) target = level) :
    ContinuousOn root domain := by
  have hslice : ∀ initial, Continuous (fun target => cost initial target) := by
    intro initial
    exact hcost.comp (continuous_const.prodMk continuous_id)
  intro target htarget
  rw [ContinuousWithinAt]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    have hlevel_lt : level < cost lower target := by
      rw [← (hroot target htarget).2]
      exact hanti target hlower (hroot target htarget).1
    have hnear : ∀ᶠ nearby in nhdsWithin target domain, level < cost lower nearby := by
      apply mem_nhdsWithin_of_mem_nhds
      exact (hslice lower).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hlevel_lt)
    have hbelow : ∀ᶠ nearby in nhdsWithin target domain, lower < nearby := by
      apply mem_nhdsWithin_of_mem_nhds
      exact Ioi_mem_nhds (hlower.trans (hroot target htarget).1)
    filter_upwards [hnear, hbelow, self_mem_nhdsWithin] with nearby hnear hbelow hnearDomain
    by_contra hnot
    have hroot_le : root nearby ≤ lower := le_of_not_gt hnot
    rcases lt_or_eq_of_le hroot_le with hlt | heq
    · have hcost_lt : cost lower nearby < cost (root nearby) nearby :=
        hanti nearby hlt hbelow
      rw [(hroot nearby hnearDomain).2] at hcost_lt
      exact (not_lt_of_ge hcost_lt.le) hnear
    · rw [← heq, (hroot nearby hnearDomain).2] at hnear
      exact (lt_irrefl level) hnear
  · intro upper hupper
    let barrier := (root target + min upper target) / 2
    have hroot_lt_min : root target < min upper target :=
      lt_min hupper (hroot target htarget).1
    have hroot_lt_barrier : root target < barrier := by
      dsimp [barrier]
      linarith
    have hbarrier_lt_min : barrier < min upper target := by
      dsimp [barrier]
      linarith
    have hbarrier_lt_target : barrier < target :=
      hbarrier_lt_min.trans_le (min_le_right _ _)
    have hbarrier_lt_upper : barrier < upper :=
      hbarrier_lt_min.trans_le (min_le_left _ _)
    have hcost_lt : cost barrier target < level := by
      rw [← (hroot target htarget).2]
      exact hanti target hroot_lt_barrier hbarrier_lt_target
    have hnear : ∀ᶠ nearby in nhdsWithin target domain, cost barrier nearby < level := by
      apply mem_nhdsWithin_of_mem_nhds
      exact (hslice barrier).continuousAt.preimage_mem_nhds (Iio_mem_nhds hcost_lt)
    have hroot_lt_barrier : ∀ᶠ nearby in nhdsWithin target domain,
        root nearby < barrier := by
      filter_upwards [hnear, self_mem_nhdsWithin] with nearby hnear hnearDomain
      by_contra hnot
      have hbarrier_le : barrier ≤ root nearby := le_of_not_gt hnot
      rcases lt_or_eq_of_le hbarrier_le with hlt | heq
      · have hcost_lt : cost (root nearby) nearby < cost barrier nearby :=
          hanti nearby hlt (hroot nearby hnearDomain).1
        rw [(hroot nearby hnearDomain).2] at hcost_lt
        exact (not_lt_of_ge hnear.le) hcost_lt
      · rw [heq, (hroot nearby hnearDomain).2] at hnear
        exact (lt_irrefl level) hnear
    filter_upwards [hroot_lt_barrier] with nearby hroot_lt_barrier
    exact hroot_lt_barrier.trans hbarrier_lt_upper

/--
Interval version of `continuousOn_rightInverse_of_strictMono`.  The inverse
only needs to take values in the interior of the bracket on which the base map
is strictly increasing.
-/
theorem continuousOn_rightInverse_of_strictMonoOn_Icc
    {base root : ℝ → ℝ} {s : Set ℝ} {left right : ℝ}
    (hbase_mono : StrictMonoOn base (Icc left right))
    (hroot_mem : ∀ y ∈ s, root y ∈ Ioo left right)
    (hroot : ∀ y ∈ s, base (root y) = y) :
    ContinuousOn root s := by
  intro y hy
  have hyroot_mem_Ioo : root y ∈ Ioo left right := hroot_mem y hy
  have hyroot_mem_Icc : root y ∈ Icc left right :=
    ⟨hyroot_mem_Ioo.1.le, hyroot_mem_Ioo.2.le⟩
  rw [ContinuousWithinAt]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    by_cases hlower_left : lower < left
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hlower_left.trans (hroot_mem z hz).1
    · have hleft_lower : left ≤ lower := le_of_not_gt hlower_left
      have hlower_right : lower < right := hlower.trans hyroot_mem_Ioo.2
      have hlower_mem : lower ∈ Icc left right :=
        ⟨hleft_lower, hlower_right.le⟩
      have hbase_lower_lt_y : base lower < y := by
        simpa [hroot y hy] using
          hbase_mono hlower_mem hyroot_mem_Icc hlower
      have hevent :
          ∀ᶠ z in nhdsWithin y s, base lower < z :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbase_lower_lt_y)
      filter_upwards [hevent, self_mem_nhdsWithin] with z hz hs
      by_contra hnot
      have hle : root z ≤ lower := le_of_not_gt hnot
      have hzroot_mem_Ioo : root z ∈ Ioo left right := hroot_mem z hs
      have hzroot_mem_Icc : root z ∈ Icc left right :=
        ⟨hzroot_mem_Ioo.1.le, hzroot_mem_Ioo.2.le⟩
      have hbase_le : base (root z) ≤ base lower := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact le_of_lt (hbase_mono hzroot_mem_Icc hlower_mem hlt)
        · rw [heq]
      have hroot_z : base (root z) = z := hroot z hs
      linarith
  · intro upper hupper
    by_cases hright_upper : right < upper
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hroot_mem z hz).2.trans hright_upper
    · have hupper_right : upper ≤ right := le_of_not_gt hright_upper
      have hleft_upper : left < upper := hyroot_mem_Ioo.1.trans hupper
      have hupper_mem : upper ∈ Icc left right :=
        ⟨hleft_upper.le, hupper_right⟩
      have hy_lt_base_upper : y < base upper := by
        simpa [hroot y hy] using
          hbase_mono hyroot_mem_Icc hupper_mem hupper
      have hevent :
          ∀ᶠ z in nhdsWithin y s, z < base upper :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hy_lt_base_upper)
      filter_upwards [hevent, self_mem_nhdsWithin] with z hz hs
      by_contra hnot
      have hle : upper ≤ root z := le_of_not_gt hnot
      have hzroot_mem_Ioo : root z ∈ Ioo left right := hroot_mem z hs
      have hzroot_mem_Icc : root z ∈ Icc left right :=
        ⟨hzroot_mem_Ioo.1.le, hzroot_mem_Ioo.2.le⟩
      have hbase_le : base upper ≤ base (root z) := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact le_of_lt (hbase_mono hupper_mem hzroot_mem_Icc hlt)
        · rw [← heq]
      have hroot_z : base (root z) = z := hroot z hs
      linarith

/--
Strictly decreasing analogue of
`continuousOn_rightInverse_of_strictMonoOn_Icc`.
-/
theorem continuousOn_rightInverse_of_strictAntiOn_Icc
    {base root : ℝ → ℝ} {s : Set ℝ} {left right : ℝ}
    (hbase_anti : StrictAntiOn base (Icc left right))
    (hroot_mem : ∀ y ∈ s, root y ∈ Ioo left right)
    (hroot : ∀ y ∈ s, base (root y) = y) :
    ContinuousOn root s := by
  intro y hy
  have hyroot_mem_Ioo : root y ∈ Ioo left right := hroot_mem y hy
  have hyroot_mem_Icc : root y ∈ Icc left right :=
    ⟨hyroot_mem_Ioo.1.le, hyroot_mem_Ioo.2.le⟩
  rw [ContinuousWithinAt]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    by_cases hlower_left : lower < left
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hlower_left.trans (hroot_mem z hz).1
    · have hleft_lower : left ≤ lower := le_of_not_gt hlower_left
      have hlower_right : lower < right := hlower.trans hyroot_mem_Ioo.2
      have hlower_mem : lower ∈ Icc left right :=
        ⟨hleft_lower, hlower_right.le⟩
      have hy_lt_base_lower : y < base lower := by
        simpa [hroot y hy] using
          hbase_anti hlower_mem hyroot_mem_Icc hlower
      have hevent :
          ∀ᶠ z in nhdsWithin y s, z < base lower :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hy_lt_base_lower)
      filter_upwards [hevent, self_mem_nhdsWithin] with z hz hs
      by_contra hnot
      have hle : root z ≤ lower := le_of_not_gt hnot
      have hzroot_mem_Ioo : root z ∈ Ioo left right := hroot_mem z hs
      have hzroot_mem_Icc : root z ∈ Icc left right :=
        ⟨hzroot_mem_Ioo.1.le, hzroot_mem_Ioo.2.le⟩
      have hbase_le : base lower ≤ base (root z) := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact le_of_lt (hbase_anti hzroot_mem_Icc hlower_mem hlt)
        · rw [heq]
      have hroot_z : base (root z) = z := hroot z hs
      linarith
  · intro upper hupper
    by_cases hright_upper : right < upper
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hroot_mem z hz).2.trans hright_upper
    · have hupper_right : upper ≤ right := le_of_not_gt hright_upper
      have hleft_upper : left < upper := hyroot_mem_Ioo.1.trans hupper
      have hupper_mem : upper ∈ Icc left right :=
        ⟨hleft_upper.le, hupper_right⟩
      have hbase_upper_lt_y : base upper < y := by
        simpa [hroot y hy] using
          hbase_anti hyroot_mem_Icc hupper_mem hupper
      have hevent :
          ∀ᶠ z in nhdsWithin y s, base upper < z :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbase_upper_lt_y)
      filter_upwards [hevent, self_mem_nhdsWithin] with z hz hs
      by_contra hnot
      have hle : upper ≤ root z := le_of_not_gt hnot
      have hzroot_mem_Ioo : root z ∈ Ioo left right := hroot_mem z hs
      have hzroot_mem_Icc : root z ∈ Icc left right :=
        ⟨hzroot_mem_Ioo.1.le, hzroot_mem_Ioo.2.le⟩
      have hbase_le : base (root z) ≤ base upper := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact le_of_lt (hbase_anti hupper_mem hzroot_mem_Icc hlt)
        · rw [← heq]
      have hroot_z : base (root z) = z := hroot z hs
      linarith

/--
Unbounded intermediate-value cutoff for a continuous scalar function with
opposite end limits.  If `f` tends to `high` at `-∞`, tends to `low` at `+∞`,
and `level` lies strictly between them, then some real cutoff attains `level`.
-/
theorem exists_eq_of_continuous_tendsto_atBot_atTop
    {f : ℝ → ℝ} {level low high : ℝ}
    (hf_cont : Continuous f)
    (hatBot : Filter.Tendsto f Filter.atBot (nhds high))
    (hatTop : Filter.Tendsto f Filter.atTop (nhds low))
    (hlevel : level ∈ Ioo low high) :
    ∃ cutoff : ℝ, f cutoff = level := by
  have htop :
      ∀ᶠ cutoff in Filter.atTop, f cutoff < level :=
    hatTop.eventually (eventually_lt_nhds hlevel.1)
  have hbot :
      ∀ᶠ cutoff in Filter.atBot, level < f cutoff :=
    hatBot.eventually (eventually_gt_nhds hlevel.2)
  rcases htop.exists with ⟨cutoffTop, hcutoffTop⟩
  rcases hbot.exists with ⟨cutoffBot, hcutoffBot⟩
  rcases mem_range_of_exists_le_of_exists_ge hf_cont
      ⟨cutoffTop, le_of_lt hcutoffTop⟩
      ⟨cutoffBot, le_of_lt hcutoffBot⟩ with
    ⟨cutoff, hcutoff⟩
  exact ⟨cutoff, hcutoff⟩

/--
Unbounded uniqueness cutoff for a continuous strictly decreasing scalar
function with opposite end limits.
-/
theorem existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop
    {f : ℝ → ℝ} {level low high : ℝ}
    (hf_cont : Continuous f)
    (hf_anti : StrictAnti f)
    (hatBot : Filter.Tendsto f Filter.atBot (nhds high))
    (hatTop : Filter.Tendsto f Filter.atTop (nhds low))
    (hlevel : level ∈ Ioo low high) :
    ∃! cutoff : ℝ, f cutoff = level := by
  rcases exists_eq_of_continuous_tendsto_atBot_atTop
      hf_cont hatBot hatTop hlevel with
    ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  intro cutoff' hcutoff'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := hf_anti hlt
    rw [hcutoff, hcutoff'] at hstrict
    exact (lt_irrefl level) hstrict
  · have hstrict := hf_anti hgt
    rw [hcutoff', hcutoff] at hstrict
    exact (lt_irrefl level) hstrict

/--
Unbounded uniqueness cutoff for a continuous strictly decreasing scalar
function, bundled with the upper-threshold region characterization.

This is the reusable form of capacity-cutoff arguments: once `f cutoff = level`,
strict antitonicity makes `{z | f z ≤ level}` exactly the upper ray starting at
that cutoff.
-/
theorem existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop
    {f : ℝ → ℝ} {level low high : ℝ}
    (hf_cont : Continuous f)
    (hf_anti : StrictAnti f)
    (hatBot : Filter.Tendsto f Filter.atBot (nhds high))
    (hatTop : Filter.Tendsto f Filter.atTop (nhds low))
    (hlevel : level ∈ Ioo low high) :
    ∃! cutoff : ℝ,
      f cutoff = level ∧
        ∀ z : ℝ, f z ≤ level ↔ cutoff ≤ z := by
  rcases
    existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop
      hf_cont hf_anti hatBot hatTop hlevel with
    ⟨cutoff, hcutoff, hunique⟩
  refine ⟨cutoff, ⟨hcutoff, ?_⟩, ?_⟩
  · intro z
    constructor
    · intro hz
      by_contra hnot
      have hzlt : z < cutoff := lt_of_not_ge hnot
      have hstrict := hf_anti hzlt
      rw [hcutoff] at hstrict
      linarith
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | rfl
      · have hstrict := hf_anti hlt
        rw [hcutoff] at hstrict
        exact le_of_lt hstrict
      · exact le_of_eq hcutoff
  · intro cutoff' hprops
    exact hunique cutoff' hprops.1

/--
Unbounded uniqueness cutoff for a continuous strictly increasing scalar
function with opposite end limits.
-/
theorem existsUnique_eq_of_continuous_strictMono_tendsto_atBot_atTop
    {f : ℝ → ℝ} {level low high : ℝ}
    (hf_cont : Continuous f)
    (hf_mono : StrictMono f)
    (hatBot : Filter.Tendsto f Filter.atBot (nhds low))
    (hatTop : Filter.Tendsto f Filter.atTop (nhds high))
    (hlevel : level ∈ Ioo low high) :
    ∃! cutoff : ℝ, f cutoff = level := by
  have hneg_cont : Continuous (fun x : ℝ => -f x) := hf_cont.neg
  have hneg_anti : StrictAnti (fun x : ℝ => -f x) := by
    intro x y hxy
    exact neg_lt_neg (hf_mono hxy)
  have hneg_atBot :
      Filter.Tendsto (fun x : ℝ => -f x) Filter.atBot (nhds (-low)) :=
    hatBot.neg
  have hneg_atTop :
      Filter.Tendsto (fun x : ℝ => -f x) Filter.atTop (nhds (-high)) :=
    hatTop.neg
  have hlevel_neg : -level ∈ Ioo (-high) (-low) := by
    constructor <;> linarith [hlevel.1, hlevel.2]
  rcases
    existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop
      hneg_cont hneg_anti hneg_atBot hneg_atTop hlevel_neg with
    ⟨cutoff, hcutoff, hunique⟩
  refine ⟨cutoff, ?_, ?_⟩
  · linarith
  · intro cutoff' hcutoff'
    exact hunique cutoff' (by linarith)

/--
Continuous strictly increasing crossing theorem for payoff cutoffs.  If a
payoff is negative somewhere and positive somewhere, then it has a unique zero
and its nonnegative set is exactly an upper threshold region.
-/
theorem existsUnique_zero_and_nonneg_iff_of_continuous_strictMono_crossing
    {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_mono : StrictMono f)
    (hneg : ∃ x : ℝ, f x < 0) (hpos : ∃ y : ℝ, 0 < f y) :
    ∃! cutoff : ℝ,
      f cutoff = 0 ∧ ∀ z : ℝ, 0 ≤ f z ↔ cutoff ≤ z := by
  rcases hneg with ⟨x, hx⟩
  rcases hpos with ⟨y, hy⟩
  have hxy : x < y := by
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    have hfy_le_fx : f y ≤ f x := hf_mono.monotone hyx
    linarith
  have hzero_mem : (0 : ℝ) ∈ Icc (f x) (f y) :=
    ⟨le_of_lt hx, le_of_lt hy⟩
  rcases intermediate_value_Icc hxy.le hf_cont.continuousOn hzero_mem with
    ⟨cutoff, _hcutoff_mem, hcutoff⟩
  refine ⟨cutoff, ⟨hcutoff, ?_⟩, ?_⟩
  · intro z
    constructor
    · intro hz_nonneg
      by_contra hnot
      have hz_lt : z < cutoff := lt_of_not_ge hnot
      have hstrict : f z < f cutoff := hf_mono hz_lt
      linarith
    · intro hcutoff_le
      rcases lt_or_eq_of_le hcutoff_le with hlt | rfl
      · have hstrict : f cutoff < f z := hf_mono hlt
        linarith
      · linarith
  · intro cutoff' hprops
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict : f cutoff' < f cutoff := hf_mono hlt
      rw [hprops.1, hcutoff] at hstrict
      exact (lt_irrefl (0 : ℝ)) hstrict
    · have hstrict : f cutoff < f cutoff' := hf_mono hgt
      rw [hcutoff, hprops.1] at hstrict
      exact (lt_irrefl (0 : ℝ)) hstrict

/--
If a scalar function is continuous and strictly increasing on `[0, 1]`, and a
level lies strictly between the endpoint values, then there is an interior
threshold where the function equals the level.  On `[0, 1]`, strict comparison
to the level is equivalent to being below or above that threshold.
-/
theorem exists_threshold_of_continuous_strictMonoOn_Icc_crossing
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1))
    (hleft : f 0 < level) (hright : level < f 1) :
    ∃ threshold : ℝ, threshold ∈ Ioo 0 1 ∧ f threshold = level ∧
      (∀ x ∈ Icc 0 1, f x < level ↔ x < threshold) ∧
      (∀ x ∈ Icc 0 1, level < f x ↔ threshold < x) ∧
      (∀ x ∈ Icc 0 1, f x ≤ level ↔ x ≤ threshold) ∧
      (∀ x ∈ Icc 0 1, level ≤ f x ↔ threshold ≤ x) := by
  have hzero_mem : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hlevel_mem : level ∈ Icc (f 0) (f 1) := ⟨hleft.le, hright.le⟩
  rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf_cont hlevel_mem with
    ⟨threshold, hthreshold_mem, hthreshold_eq⟩
  have hthreshold_pos : 0 < threshold := by
    have hne : threshold ≠ 0 := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.1 (Ne.symm hne)
  have hthreshold_lt_one : threshold < 1 := by
    have hne : threshold ≠ 1 := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.2 hne
  refine ⟨threshold, ⟨hthreshold_pos, hthreshold_lt_one⟩, hthreshold_eq, ?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have htx : threshold ≤ x := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have htx_strict : threshold < x := lt_of_le_of_ne htx (Ne.symm hx_ne)
        have hfx_gt : f threshold < f x :=
          hf_mono hthreshold_mem hx htx_strict
        linarith
      subst x
      linarith
    · intro hxlt
      have hfx : f x < f threshold :=
        hf_mono hx hthreshold_mem hxlt
      linarith
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have hxt : x ≤ threshold := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have hxt_strict : x < threshold := lt_of_le_of_ne hxt hx_ne
        have hfx_lt : f x < f threshold :=
          hf_mono hx hthreshold_mem hxt_strict
        linarith
      subst x
      linarith
    · intro htx
      have hfx : f threshold < f x :=
        hf_mono hthreshold_mem hx htx
      linarith
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have htx : threshold < x := lt_of_not_ge hnot
      have hfx : f threshold < f x :=
        hf_mono hthreshold_mem hx htx
      linarith
    · intro hxt
      by_cases hx_eq : x = threshold
      · subst x
        linarith
      · have hxt_strict : x < threshold := lt_of_le_of_ne hxt hx_eq
        have hfx : f x < f threshold :=
          hf_mono hx hthreshold_mem hxt_strict
        linarith
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have hxt : x < threshold := lt_of_not_ge hnot
      have hfx : f x < f threshold :=
        hf_mono hx hthreshold_mem hxt
      linarith
    · intro htx
      by_cases hx_eq : x = threshold
      · subst x
        linarith
      · have htx_strict : threshold < x := lt_of_le_of_ne htx (Ne.symm hx_eq)
        have hfx : f threshold < f x :=
          hf_mono hthreshold_mem hx htx_strict
        linarith

/--
If a scalar function is continuous and strictly increasing on `[0, 1]`, then
for any level there is a real threshold whose lower set on `[0, 1]` is exactly
`{x | f x < level}`.  The threshold may lie outside `[0, 1]` when the level is
outside the endpoint range.
-/
theorem exists_threshold_of_continuous_strictMonoOn_Icc
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc 0 1, f x < level ↔ x < threshold := by
  have hzero_mem : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  by_cases hleft : f 0 < level
  · by_cases hright : level < f 1
    · rcases exists_threshold_of_continuous_strictMonoOn_Icc_crossing
        hf_cont hf_mono hleft hright with
        ⟨threshold, _hthreshold, _hroot, hlt, _hgt, _hle, _hge⟩
      exact ⟨threshold, hlt⟩
    · have hf1_le : f 1 ≤ level := le_of_not_gt hright
      by_cases hf1_lt : f 1 < level
      · refine ⟨2, ?_⟩
        intro x hx
        constructor
        · intro _hfx
          linarith [hx.2]
        · intro _hx
          by_cases hx_one : x = 1
          · simpa [hx_one] using hf1_lt
          · have hx_lt_one : x < 1 := lt_of_le_of_ne hx.2 hx_one
            have hfx_lt_one : f x < f 1 :=
              hf_mono hx hone_mem hx_lt_one
            exact lt_trans hfx_lt_one hf1_lt
      · have hf1_eq : f 1 = level :=
          le_antisymm hf1_le (le_of_not_gt hf1_lt)
        refine ⟨1, ?_⟩
        intro x hx
        constructor
        · intro hfx
          by_contra hnot
          have hle : 1 ≤ x := le_of_not_gt hnot
          have hx_eq : x = 1 := le_antisymm hx.2 hle
          subst x
          linarith
        · intro hx_lt_one
          have hfx_lt_one : f x < f 1 :=
            hf_mono hx hone_mem hx_lt_one
          simpa [hf1_eq] using hfx_lt_one
  · have hlevel_le_f0 : level ≤ f 0 := le_of_not_gt hleft
    refine ⟨0, ?_⟩
    intro x hx
    constructor
    · intro hfx
      by_cases hx_zero : x = 0
      · subst x
        linarith
      · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
        have hf0_lt_fx : f 0 < f x :=
          hf_mono hzero_mem hx hx_pos
        linarith
    · intro hx_lt_zero
      linarith [hx.1]

/--
If a scalar function is continuous and strictly increasing on `[0, 1]`, then
for any level there is a real threshold whose weak lower set on `[0, 1]` is
exactly `{x | f x ≤ level}`.  The threshold may lie outside `[0, 1]` when the
level is outside the endpoint range.
-/
theorem exists_threshold_le_of_continuous_strictMonoOn_Icc
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc 0 1, f x ≤ level ↔ x ≤ threshold := by
  have hzero_mem : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  by_cases hlevel_lt_f0 : level < f 0
  · refine ⟨-1, ?_⟩
    intro x hx
    constructor
    · intro hfx
      by_cases hx_zero : x = 0
      · subst x
        linarith
      · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
        have hf0_lt_fx : f 0 < f x :=
          hf_mono hzero_mem hx hx_pos
        linarith
    · intro hx_le
      linarith [hx.1, hx_le]
  · have hf0_le_level : f 0 ≤ level := le_of_not_gt hlevel_lt_f0
    by_cases hf1_le_level : f 1 ≤ level
    · refine ⟨1, ?_⟩
      intro x hx
      constructor
      · intro _hfx
        exact hx.2
      · intro _hx
        by_cases hx_one : x = 1
        · simpa [hx_one] using hf1_le_level
        · have hx_lt_one : x < 1 := lt_of_le_of_ne hx.2 hx_one
          have hfx_lt_one : f x < f 1 :=
            hf_mono hx hone_mem hx_lt_one
          exact (lt_of_lt_of_le hfx_lt_one hf1_le_level).le
    · have hlevel_lt_f1 : level < f 1 := lt_of_not_ge hf1_le_level
      by_cases hf0_lt_level : f 0 < level
      · rcases exists_threshold_of_continuous_strictMonoOn_Icc_crossing
          hf_cont hf_mono hf0_lt_level hlevel_lt_f1 with
          ⟨threshold, _hthreshold, _hroot, _hlt, _hgt, hle, _hge⟩
        exact ⟨threshold, hle⟩
      · have hf0_eq : f 0 = level :=
          le_antisymm hf0_le_level (le_of_not_gt hf0_lt_level)
        refine ⟨0, ?_⟩
        intro x hx
        constructor
        · intro hfx
          by_contra hnot
          have hx_pos : 0 < x := lt_of_not_ge hnot
          have hf0_lt_fx : f 0 < f x :=
            hf_mono hzero_mem hx hx_pos
          linarith
        · intro hx_le_zero
          have hx_eq : x = 0 := le_antisymm hx_le_zero hx.1
          subst x
          linarith

/--
Interval version of
`exists_threshold_of_continuous_strictMonoOn_Icc_crossing`.

If a scalar function is continuous and strictly increasing on `[left, right]`,
with the level strictly between its endpoint values, then the threshold lies in
the interval interior and comparisons to the level are exactly comparisons to
that threshold.
-/
theorem exists_threshold_of_continuous_strictMonoOn_Icc_crossing_interval
    {f : ℝ → ℝ} {level left right : ℝ}
    (hleft_right : left < right)
    (hf_cont : ContinuousOn f (Icc left right))
    (hf_mono : StrictMonoOn f (Icc left right))
    (hleft : f left < level) (hright : level < f right) :
    ∃ threshold : ℝ, threshold ∈ Ioo left right ∧ f threshold = level ∧
      (∀ x ∈ Icc left right, f x < level ↔ x < threshold) ∧
      (∀ x ∈ Icc left right, level < f x ↔ threshold < x) ∧
      (∀ x ∈ Icc left right, f x ≤ level ↔ x ≤ threshold) ∧
      (∀ x ∈ Icc left right, level ≤ f x ↔ threshold ≤ x) := by
  have hlevel_mem : level ∈ Icc (f left) (f right) :=
    ⟨hleft.le, hright.le⟩
  rcases intermediate_value_Icc hleft_right.le hf_cont hlevel_mem with
    ⟨threshold, hthreshold_mem, hthreshold_eq⟩
  have hthreshold_gt_left : left < threshold := by
    have hne : threshold ≠ left := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.1 (Ne.symm hne)
  have hthreshold_lt_right : threshold < right := by
    have hne : threshold ≠ right := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.2 hne
  have hlt_level :
      ∀ x ∈ Icc left right, f x < level ↔ x < threshold := by
    intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have htx : threshold ≤ x := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have htx_strict : threshold < x := lt_of_le_of_ne htx (Ne.symm hx_ne)
        have hfx_gt : f threshold < f x :=
          hf_mono hthreshold_mem hx htx_strict
        linarith
      subst x
      linarith
    · intro hx_threshold
      have hfx : f x < f threshold :=
        hf_mono hx hthreshold_mem hx_threshold
      linarith
  have hlevel_lt :
      ∀ x ∈ Icc left right, level < f x ↔ threshold < x := by
    intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have hxt : x ≤ threshold := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have hxt_strict : x < threshold := lt_of_le_of_ne hxt hx_ne
        have hfx_lt : f x < f threshold :=
          hf_mono hx hthreshold_mem hxt_strict
        linarith
      subst x
      linarith
    · intro hthreshold_x
      have hfx : f threshold < f x :=
        hf_mono hthreshold_mem hx hthreshold_x
      linarith
  have hle_level :
      ∀ x ∈ Icc left right, f x ≤ level ↔ x ≤ threshold := by
    intro x hx
    constructor
    · intro hfx_level
      by_contra hnot
      have hthreshold_x : threshold < x := lt_of_not_ge hnot
      have hlevel_x : level < f x := (hlevel_lt x hx).mpr hthreshold_x
      linarith
    · intro hx_threshold
      rcases lt_or_eq_of_le hx_threshold with hlt | rfl
      · have hfx_level : f x < level := (hlt_level x hx).mpr hlt
        exact le_of_lt hfx_level
      · linarith
  have hlevel_le :
      ∀ x ∈ Icc left right, level ≤ f x ↔ threshold ≤ x := by
    intro x hx
    constructor
    · intro hlevel_x
      by_contra hnot
      have hx_threshold : x < threshold := lt_of_not_ge hnot
      have hfx_level : f x < level := (hlt_level x hx).mpr hx_threshold
      linarith
    · intro hthreshold_x
      rcases lt_or_eq_of_le hthreshold_x with hlt | hEq
      · have hlevel_x : level < f x := (hlevel_lt x hx).mpr hlt
        exact le_of_lt hlevel_x
      · subst x
        linarith
  exact
    ⟨threshold, ⟨hthreshold_gt_left, hthreshold_lt_right⟩,
      hthreshold_eq, hlt_level, hlevel_lt, hle_level, hlevel_le⟩

/--
If a scalar function is continuous and strictly increasing on `[left, right]`,
then for any level there is a real threshold whose lower set on that interval
is exactly `{x | f x < level}`.
-/
theorem exists_threshold_of_continuous_strictMonoOn_Icc_interval
    {f : ℝ → ℝ} {level left right : ℝ}
    (hleft_right : left < right)
    (hf_cont : ContinuousOn f (Icc left right))
    (hf_mono : StrictMonoOn f (Icc left right)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc left right, f x < level ↔ x < threshold := by
  have hleft_mem : left ∈ Icc left right :=
    ⟨le_rfl, hleft_right.le⟩
  have hright_mem : right ∈ Icc left right :=
    ⟨hleft_right.le, le_rfl⟩
  by_cases hleft_level : f left < level
  · by_cases hright_level : level < f right
    · rcases exists_threshold_of_continuous_strictMonoOn_Icc_crossing_interval
        hleft_right hf_cont hf_mono hleft_level hright_level with
        ⟨threshold, _hthreshold, _hroot, hlt, _hgt, _hle, _hge⟩
      exact ⟨threshold, hlt⟩
    · have hright_le : f right ≤ level := le_of_not_gt hright_level
      by_cases hright_lt : f right < level
      · refine ⟨right + 1, ?_⟩
        intro x hx
        constructor
        · intro _hfx
          linarith [hx.2]
        · intro _hx
          by_cases hx_right : x = right
          · simpa [hx_right] using hright_lt
          · have hx_lt_right : x < right := lt_of_le_of_ne hx.2 hx_right
            have hfx_lt_right : f x < f right :=
              hf_mono hx hright_mem hx_lt_right
            exact lt_trans hfx_lt_right hright_lt
      · have hright_eq : f right = level :=
          le_antisymm hright_le (le_of_not_gt hright_lt)
        refine ⟨right, ?_⟩
        intro x hx
        constructor
        · intro hfx
          by_contra hnot
          have hle : right ≤ x := le_of_not_gt hnot
          have hx_eq : x = right := le_antisymm hx.2 hle
          subst x
          linarith
        · intro hx_lt_right
          have hfx_lt_right : f x < f right :=
            hf_mono hx hright_mem hx_lt_right
          simpa [hright_eq] using hfx_lt_right
  · have hlevel_le_left : level ≤ f left := le_of_not_gt hleft_level
    refine ⟨left, ?_⟩
    intro x hx
    constructor
    · intro hfx
      by_cases hx_left : x = left
      · subst x
        linarith
      · have hx_gt_left : left < x := lt_of_le_of_ne hx.1 (Ne.symm hx_left)
        have hleft_lt_fx : f left < f x :=
          hf_mono hleft_mem hx hx_gt_left
        linarith
    · intro hx_lt_left
      linarith [hx.1]

/--
If a scalar function is continuous and strictly increasing on `[left, right]`,
then for any level there is a real threshold whose weak lower set on that
interval is exactly `{x | f x ≤ level}`.
-/
theorem exists_threshold_le_of_continuous_strictMonoOn_Icc_interval
    {f : ℝ → ℝ} {level left right : ℝ}
    (hleft_right : left < right)
    (hf_cont : ContinuousOn f (Icc left right))
    (hf_mono : StrictMonoOn f (Icc left right)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc left right, f x ≤ level ↔ x ≤ threshold := by
  have hleft_mem : left ∈ Icc left right :=
    ⟨le_rfl, hleft_right.le⟩
  have hright_mem : right ∈ Icc left right :=
    ⟨hleft_right.le, le_rfl⟩
  by_cases hlevel_lt_left : level < f left
  · refine ⟨left - 1, ?_⟩
    intro x hx
    constructor
    · intro hfx
      by_cases hx_left : x = left
      · subst x
        linarith
      · have hx_gt_left : left < x := lt_of_le_of_ne hx.1 (Ne.symm hx_left)
        have hleft_lt_fx : f left < f x :=
          hf_mono hleft_mem hx hx_gt_left
        linarith
    · intro hx_le
      linarith [hx.1, hx_le]
  · have hleft_le_level : f left ≤ level := le_of_not_gt hlevel_lt_left
    by_cases hright_le_level : f right ≤ level
    · refine ⟨right, ?_⟩
      intro x hx
      constructor
      · intro _hfx
        exact hx.2
      · intro _hx
        by_cases hx_right : x = right
        · simpa [hx_right] using hright_le_level
        · have hx_lt_right : x < right := lt_of_le_of_ne hx.2 hx_right
          have hfx_lt_right : f x < f right :=
            hf_mono hx hright_mem hx_lt_right
          exact (lt_of_lt_of_le hfx_lt_right hright_le_level).le
    · have hlevel_lt_right : level < f right := lt_of_not_ge hright_le_level
      by_cases hleft_lt_level : f left < level
      · rcases exists_threshold_of_continuous_strictMonoOn_Icc_crossing_interval
          hleft_right hf_cont hf_mono hleft_lt_level hlevel_lt_right with
          ⟨threshold, _hthreshold, _hroot, _hlt, _hgt, hle, _hge⟩
        exact ⟨threshold, hle⟩
      · have hleft_eq : f left = level :=
          le_antisymm hleft_le_level (le_of_not_gt hleft_lt_level)
        refine ⟨left, ?_⟩
        intro x hx
        constructor
        · intro hfx
          by_contra hnot
          have hx_gt_left : left < x := lt_of_not_ge hnot
          have hleft_lt_fx : f left < f x :=
            hf_mono hleft_mem hx hx_gt_left
          linarith
        · intro hx_le_left
          have hx_eq : x = left := le_antisymm hx_le_left hx.1
          subst x
          linarith

/--
If a scalar function is continuous and strictly decreasing on `[0, 1]`, and a
level lies strictly between the endpoint values, then there is an interior
threshold where the function equals `level`.  On `[0, 1]`, comparison to the
level is equivalent to being on the corresponding side of the threshold.
-/
theorem exists_threshold_of_continuous_strictAntiOn_Icc_crossing
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_anti : StrictAntiOn f (Icc 0 1))
    (hleft : level < f 0) (hright : f 1 < level) :
    ∃ threshold : ℝ, threshold ∈ Ioo 0 1 ∧ f threshold = level ∧
      (∀ x ∈ Icc 0 1, level < f x ↔ x < threshold) ∧
      (∀ x ∈ Icc 0 1, f x < level ↔ threshold < x) ∧
      (∀ x ∈ Icc 0 1, level ≤ f x ↔ x ≤ threshold) ∧
      (∀ x ∈ Icc 0 1, f x ≤ level ↔ threshold ≤ x) := by
  have hneg_cont : ContinuousOn (fun x : ℝ => -f x) (Icc 0 1) :=
    hf_cont.neg
  have hneg_mono : StrictMonoOn (fun x : ℝ => -f x) (Icc 0 1) := by
    intro x hx y hy hxy
    exact neg_lt_neg (hf_anti hx hy hxy)
  have hneg_left : -f 0 < -level := by linarith
  have hneg_right : -level < -f 1 := by linarith
  rcases
    exists_threshold_of_continuous_strictMonoOn_Icc_crossing
      (f := fun x : ℝ => -f x) (level := -level)
      hneg_cont hneg_mono hneg_left hneg_right with
    ⟨threshold, hthreshold_mem, hthreshold_eq,
      hneg_lt, hneg_gt, hneg_le, hneg_ge⟩
  refine ⟨threshold, hthreshold_mem, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · intro x hx
    constructor
    · intro hlevel
      exact (hneg_lt x hx).mp (by linarith)
    · intro hx_threshold
      have hneg := (hneg_lt x hx).mpr hx_threshold
      linarith
  · intro x hx
    constructor
    · intro hfx
      exact (hneg_gt x hx).mp (by linarith)
    · intro hthreshold_x
      have hneg := (hneg_gt x hx).mpr hthreshold_x
      linarith
  · intro x hx
    constructor
    · intro hlevel
      exact (hneg_le x hx).mp (by linarith)
    · intro hx_threshold
      have hneg := (hneg_le x hx).mpr hx_threshold
      linarith
  · intro x hx
    constructor
    · intro hfx
      exact (hneg_ge x hx).mp (by linarith)
    · intro hthreshold_x
      have hneg := (hneg_ge x hx).mpr hthreshold_x
      linarith

/--
Interval version of
`exists_threshold_of_continuous_strictAntiOn_Icc_crossing`.

If a scalar function is continuous and strictly decreasing on `[left, right]`,
with the level strictly between its endpoint values, then the threshold lies in
the interval interior and comparisons to the level are exactly comparisons to
that threshold.
-/
theorem exists_threshold_of_continuous_strictAntiOn_Icc_crossing_interval
    {f : ℝ → ℝ} {level left right : ℝ}
    (hleft_right : left < right)
    (hf_cont : ContinuousOn f (Icc left right))
    (hf_anti : StrictAntiOn f (Icc left right))
    (hleft : level < f left) (hright : f right < level) :
    ∃ threshold : ℝ, threshold ∈ Ioo left right ∧ f threshold = level ∧
      (∀ x ∈ Icc left right, level < f x ↔ x < threshold) ∧
      (∀ x ∈ Icc left right, f x < level ↔ threshold < x) ∧
      (∀ x ∈ Icc left right, level ≤ f x ↔ x ≤ threshold) ∧
      (∀ x ∈ Icc left right, f x ≤ level ↔ threshold ≤ x) := by
  have hlevel_mem : level ∈ Icc (f right) (f left) :=
    ⟨hright.le, hleft.le⟩
  rcases intermediate_value_Icc' hleft_right.le hf_cont hlevel_mem with
    ⟨threshold, hthreshold_mem, hthreshold_eq⟩
  have hthreshold_gt_left : left < threshold := by
    have hne : threshold ≠ left := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.1 (Ne.symm hne)
  have hthreshold_lt_right : threshold < right := by
    have hne : threshold ≠ right := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.2 hne
  have hlevel_lt :
      ∀ x ∈ Icc left right, level < f x ↔ x < threshold := by
    intro x hx
    constructor
    · intro hlevel_x
      by_contra hnot
      have htx : threshold ≤ x := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have htx_strict : threshold < x := lt_of_le_of_ne htx (Ne.symm hx_ne)
        have hfx_lt : f x < f threshold :=
          hf_anti hthreshold_mem hx htx_strict
        linarith
      subst x
      linarith
    · intro hx_threshold
      have hfx : f threshold < f x :=
        hf_anti hx hthreshold_mem hx_threshold
      linarith
  have hlt_level :
      ∀ x ∈ Icc left right, f x < level ↔ threshold < x := by
    intro x hx
    constructor
    · intro hfx_level
      by_contra hnot
      have hxt : x ≤ threshold := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have hxt_strict : x < threshold := lt_of_le_of_ne hxt hx_ne
        have hthreshold_lt_fx : f threshold < f x :=
          hf_anti hx hthreshold_mem hxt_strict
        linarith
      subst x
      linarith
    · intro hthreshold_x
      have hfx : f x < f threshold :=
        hf_anti hthreshold_mem hx hthreshold_x
      linarith
  have hlevel_le :
      ∀ x ∈ Icc left right, level ≤ f x ↔ x ≤ threshold := by
    intro x hx
    constructor
    · intro hlevel_x
      by_contra hnot
      have hthreshold_x : threshold < x := lt_of_not_ge hnot
      have hfx_lt : f x < level := (hlt_level x hx).mpr hthreshold_x
      linarith
    · intro hx_threshold
      rcases lt_or_eq_of_le hx_threshold with hlt | rfl
      · have hlevel_x : level < f x := (hlevel_lt x hx).mpr hlt
        exact le_of_lt hlevel_x
      · linarith
  have hle_level :
      ∀ x ∈ Icc left right, f x ≤ level ↔ threshold ≤ x := by
    intro x hx
    constructor
    · intro hfx_level
      by_contra hnot
      have hx_threshold : x < threshold := lt_of_not_ge hnot
      have hlevel_x : level < f x := (hlevel_lt x hx).mpr hx_threshold
      linarith
    · intro hthreshold_x
      rcases lt_or_eq_of_le hthreshold_x with hlt | hEq
      · have hfx_level : f x < level := (hlt_level x hx).mpr hlt
        exact le_of_lt hfx_level
      · subst x
        linarith
  exact
    ⟨threshold, ⟨hthreshold_gt_left, hthreshold_lt_right⟩,
      hthreshold_eq, hlevel_lt, hlt_level, hlevel_le, hle_level⟩

/--
If a scalar function is continuous and strictly decreasing on `[0, 1]`, then
for any level there is a real threshold whose strict upper set on `[0, 1]` is
exactly `{x | level < f x}`.
-/
theorem exists_threshold_gt_of_continuous_strictAntiOn_Icc
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_anti : StrictAntiOn f (Icc 0 1)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc 0 1, level < f x ↔ x < threshold := by
  have hneg_cont : ContinuousOn (fun x : ℝ => -f x) (Icc 0 1) :=
    hf_cont.neg
  have hneg_mono : StrictMonoOn (fun x : ℝ => -f x) (Icc 0 1) := by
    intro x hx y hy hxy
    exact neg_lt_neg (hf_anti hx hy hxy)
  rcases
    exists_threshold_of_continuous_strictMonoOn_Icc
      (f := fun x : ℝ => -f x) (level := -level)
      hneg_cont hneg_mono with
    ⟨threshold, hthreshold⟩
  refine ⟨threshold, ?_⟩
  intro x hx
  constructor
  · intro hlevel
    exact hthreshold x hx |>.mp (by linarith)
  · intro hx_threshold
    have hneg := hthreshold x hx |>.mpr hx_threshold
    linarith

/--
If a scalar function is continuous and strictly decreasing on `[0, 1]`, then
for any level there is a real threshold whose weak lower set on `[0, 1]` is
exactly `{x | f x ≤ level}`.
-/
theorem exists_threshold_le_of_continuous_strictAntiOn_Icc
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_anti : StrictAntiOn f (Icc 0 1)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc 0 1, f x ≤ level ↔ threshold ≤ x := by
  rcases
    exists_threshold_gt_of_continuous_strictAntiOn_Icc
      (f := f) (level := level) hf_cont hf_anti with
    ⟨threshold, hthreshold⟩
  refine ⟨threshold, ?_⟩
  intro x hx
  constructor
  · intro hfx
    by_contra hnot
    have hx_lt_threshold : x < threshold := lt_of_not_ge hnot
    have hlevel_lt : level < f x :=
      (hthreshold x hx).mpr hx_lt_threshold
    linarith
  · intro htx
    by_contra hnot
    have hlevel_lt : level < f x := lt_of_not_ge hnot
    have hx_lt_threshold : x < threshold :=
      (hthreshold x hx).mp hlevel_lt
    linarith

end

end AppliedModelingLib

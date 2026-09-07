import Mathlib.Data.Set.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Uniform argmax stability on a compact set

This module records the elementary deterministic part of finite M-estimator
consistency.  If a continuous population objective has a unique maximum on a
compact feasible set, then any uniformly close empirical objective cannot
maximize on a compact bad set that excludes that population maximum.
-/

namespace AppliedModelingLib
namespace Optimization

/-- A continuous strictly positive real function has one strictly positive
lower bound on a nonempty compact set.  This is the elementary margin bridge
used to turn pointwise population argmax separation into a uniform empirical
margin. -/
theorem exists_pos_le_on_isCompact_of_continuous_pos
    {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hcompact : IsCompact s) (hne : s.Nonempty) (hcontinuous : Continuous f)
    (hpositive : ∀ x, x ∈ s → 0 < f x) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ x, x ∈ s → margin ≤ f x := by
  obtain ⟨minimizer, hminimizer_mem, hminimizer⟩ :=
    hcompact.exists_isMinOn hne hcontinuous.continuousOn
  have hminimizer_pos : 0 < f minimizer := hpositive minimizer hminimizer_mem
  refine ⟨f minimizer / 2, by linarith, ?_⟩
  intro x hx
  have hmin : f minimizer ≤ f x := hminimizer hx
  nlinarith

/--
For a continuous objective with a unique compact-domain maximum, there is a
positive uniform-error tolerance under which every empirical domain maximizer
avoids any compact bad subset excluding that maximum.
-/
theorem exists_pos_uniformArgmaxTolerance_not_mem_of_compact
    {X : Type*} [TopologicalSpace X]
    {domain bad : Set X} {base : X} {objective : X → ℝ}
    (hbadCompact : IsCompact bad) (hbadSubset : bad ⊆ domain)
    (hobjectiveContinuous : ContinuousOn objective domain)
    (hbase : base ∈ domain ∧ IsMaxOn objective domain base)
    (hbaseUnique : ∀ other, other ∈ domain →
      objective other = objective base → other = base)
    (hbaseNotBad : base ∉ bad) :
    ∃ tolerance : ℝ, 0 < tolerance ∧
      ∀ (empirical : X → ℝ) (candidate : X),
        (∀ point, point ∈ domain →
          |empirical point - objective point| ≤ tolerance) →
        candidate ∈ domain → IsMaxOn empirical domain candidate → candidate ∉ bad := by
  by_cases hbadEmpty : bad = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro empirical candidate _ _ _ hcandidateBad
    simp [hbadEmpty] at hcandidateBad
  obtain ⟨badMax, hbadMaxMem, hbadMax⟩ :=
    hbadCompact.exists_isMaxOn (Set.nonempty_iff_ne_empty.mpr hbadEmpty)
      (hobjectiveContinuous.mono hbadSubset)
  have hbadLe : objective badMax ≤ objective base :=
    hbase.2 (hbadSubset hbadMaxMem)
  have hbadLt : objective badMax < objective base := by
    refine lt_of_le_of_ne hbadLe ?_
    intro hvalue
    have hpoint : badMax = base := hbaseUnique badMax (hbadSubset hbadMaxMem) hvalue
    exact hbaseNotBad (hpoint ▸ hbadMaxMem)
  let gap : ℝ := objective base - objective badMax
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith
  refine ⟨gap / 3, by linarith, ?_⟩
  intro empirical candidate huniform hcandidateMem hcandidateMax hcandidateBad
  have hbaseApprox := huniform base hbase.1
  have hcandidateApprox := huniform candidate hcandidateMem
  have hcandidateObjective : objective candidate ≤ objective badMax :=
    hbadMax hcandidateBad
  have hbaseEmpiricalLower : objective base - gap / 3 ≤ empirical base := by
    have hbound : -(gap / 3) ≤ empirical base - objective base := by
      exact neg_le_of_abs_le hbaseApprox
    linarith
  have hcandidateEmpiricalUpper : empirical candidate ≤ objective candidate + gap / 3 := by
    have hbound : empirical candidate - objective candidate ≤ gap / 3 := by
      exact le_of_abs_le hcandidateApprox
    linarith
  have hmax : empirical base ≤ empirical candidate := hcandidateMax hbase.1
  have hcontradiction : objective base - gap / 3 ≤ objective badMax + gap / 3 := by
    linarith
  dsimp [gap] at hcontradiction
  linarith

/--
The same compact stability conclusion needs no unique population maximizer
when the compact bad set is already known to have a strict population-objective
gap below a selected maximizer.  This is the form used when a source theorem
orders every population maximizer but does not identify its coordinates.
-/
theorem exists_pos_uniformArgmaxTolerance_not_mem_of_compact_of_strictSeparation
    {X : Type*} [TopologicalSpace X]
    {domain bad : Set X} {base : X} {objective : X → ℝ}
    (hbadCompact : IsCompact bad) (hbadSubset : bad ⊆ domain)
    (hobjectiveContinuous : ContinuousOn objective domain)
    (hbase : base ∈ domain ∧ IsMaxOn objective domain base)
    (hbadStrict : ∀ point, point ∈ bad → objective point < objective base) :
    ∃ tolerance : ℝ, 0 < tolerance ∧
      ∀ (empirical : X → ℝ) (candidate : X),
        (∀ point, point ∈ domain →
          |empirical point - objective point| ≤ tolerance) →
        candidate ∈ domain → IsMaxOn empirical domain candidate → candidate ∉ bad := by
  by_cases hbadEmpty : bad = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro empirical candidate _ _ _ hcandidateBad
    simp [hbadEmpty] at hcandidateBad
  obtain ⟨badMax, hbadMaxMem, hbadMax⟩ :=
    hbadCompact.exists_isMaxOn (Set.nonempty_iff_ne_empty.mpr hbadEmpty)
      (hobjectiveContinuous.mono hbadSubset)
  let gap : ℝ := objective base - objective badMax
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith [hbadStrict badMax hbadMaxMem]
  refine ⟨gap / 3, by linarith, ?_⟩
  intro empirical candidate huniform hcandidateMem hcandidateMax hcandidateBad
  have hbaseApprox := huniform base hbase.1
  have hcandidateApprox := huniform candidate hcandidateMem
  have hcandidateObjective : objective candidate ≤ objective badMax :=
    hbadMax hcandidateBad
  have hbaseEmpiricalLower : objective base - gap / 3 ≤ empirical base := by
    have hbound : -(gap / 3) ≤ empirical base - objective base := by
      exact neg_le_of_abs_le hbaseApprox
    linarith
  have hcandidateEmpiricalUpper : empirical candidate ≤ objective candidate + gap / 3 := by
    have hbound : empirical candidate - objective candidate ≤ gap / 3 := by
      exact le_of_abs_le hcandidateApprox
    linarith
  have hmax : empirical base ≤ empirical candidate := hcandidateMax hbase.1
  have hcontradiction : objective base - gap / 3 ≤ objective badMax + gap / 3 := by
    linarith
  dsimp [gap] at hcontradiction
  linarith

end Optimization
end AppliedModelingLib

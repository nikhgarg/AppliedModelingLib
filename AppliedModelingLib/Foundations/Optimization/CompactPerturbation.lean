import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

namespace AppliedModelingLib
namespace Optimization

/-!
# Compact Stability under a Scaled Perturbation

A finite paper argument often compares maximizers of `n * objective + perturbation`
to the unique maximizer of `objective` on a common compact feasible set.  This
module records the elementary compact-gap argument: a sufficiently large
positive integer scale keeps every selected maximizer outside a compact bad
set which excludes the base maximizer.  It deliberately does not assume a
parametric maximum theorem or any continuity of an argmax correspondence.
-/

/--
On a compact feasible set, a continuous perturbation cannot move every
maximizer of `n * objective + perturbation` into a compact bad set that
excludes the unique base-objective maximizer.  For some positive natural scale
`n`, any supplied scaled maximizer lies outside that bad set.

The result is source-neutral.  Its hypotheses make the two actual ingredients
explicit: compact attainment for the base/perturbation objectives and a common
compact domain for the scaled maximizers.  Thus it applies directly to exact
integer-count perturbations without replacing them by a nonintegral
continuation argument.
-/
theorem exists_pos_nat_isMaxOn_scaled_add_not_mem_of_compact
    {X : Type*} [TopologicalSpace X]
    {domain bad : Set X} {base : X}
    {objective perturbation : X → ℝ} {certificate : ℕ → X → Prop}
    (hdomainCompact : IsCompact domain)
    (hbadCompact : IsCompact bad) (hbadSubset : bad ⊆ domain)
    (hobjectiveContinuous : ContinuousOn objective domain)
    (hperturbationContinuous : ContinuousOn perturbation domain)
    (hbase : base ∈ domain ∧ IsMaxOn objective domain base)
    (hbaseUnique : ∀ other, other ∈ domain →
      objective other = objective base → other = base)
    (hbaseNotBad : base ∉ bad)
    (hscaledMax : ∀ n : ℕ, 0 < n →
      ∃ candidate, candidate ∈ domain ∧
        IsMaxOn (fun x => (n : ℝ) * objective x + perturbation x) domain candidate ∧
          certificate n candidate) :
    ∃ n : ℕ, 0 < n ∧ ∃ candidate, candidate ∈ domain ∧
      IsMaxOn (fun x => (n : ℝ) * objective x + perturbation x) domain candidate ∧
        certificate n candidate ∧ candidate ∉ bad := by
  by_cases hbadEmpty : bad = ∅
  · obtain ⟨candidate, hcandidateMem, hcandidateMax, hcertificate⟩ :=
      hscaledMax 1 (Nat.zero_lt_succ 0)
    refine ⟨1, Nat.zero_lt_succ 0, candidate, hcandidateMem, hcandidateMax, hcertificate, ?_⟩
    simp [hbadEmpty]
  have hbadNonempty : bad.Nonempty := Set.nonempty_iff_ne_empty.mpr hbadEmpty
  obtain ⟨badMax, hbadMaxMem, hbadMax⟩ := hbadCompact.exists_isMaxOn hbadNonempty
    (hobjectiveContinuous.mono hbadSubset)
  obtain ⟨perturbationMax, hperturbationMaxMem, hperturbationMax⟩ :=
    hdomainCompact.exists_isMaxOn ⟨base, hbase.1⟩ hperturbationContinuous
  have hbaseMaxBad : objective badMax ≤ objective base :=
    hbase.2 (hbadSubset hbadMaxMem)
  have hbadStrict : objective badMax < objective base := by
    refine lt_of_le_of_ne hbaseMaxBad ?_
    intro hvalue
    have hpoint : badMax = base := hbaseUnique badMax (hbadSubset hbadMaxMem) hvalue
    exact hbaseNotBad (hpoint ▸ hbadMaxMem)
  let gap : ℝ := objective base - objective badMax
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith
  obtain ⟨index, hindex⟩ := exists_nat_gt
    ((perturbation perturbationMax - perturbation base) / gap)
  let n : ℕ := index + 1
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  have hnLarge :
      (perturbation perturbationMax - perturbation base) / gap < (n : ℝ) := by
    calc
      _ < (index : ℝ) := hindex
      _ ≤ (n : ℝ) := by
        dsimp [n]
        exact_mod_cast Nat.le_succ index
  obtain ⟨candidate, hcandidateMem, hcandidateMax, hcertificate⟩ := hscaledMax n hnPos
  refine ⟨n, hnPos, candidate, hcandidateMem, hcandidateMax, hcertificate, ?_⟩
  intro hcandidateBad
  have hobjectiveCandidate : objective candidate ≤ objective badMax :=
    hbadMax hcandidateBad
  have hperturbationCandidate : perturbation candidate ≤ perturbation perturbationMax :=
    hperturbationMax hcandidateMem
  have hscaledCompare := hcandidateMax hbase.1
  change (n : ℝ) * objective base + perturbation base ≤
    (n : ℝ) * objective candidate + perturbation candidate at hscaledCompare
  have hnNonneg : 0 ≤ (n : ℝ) := by positivity
  have hscaledGap : (n : ℝ) * gap ≤ perturbation candidate - perturbation base := by
    dsimp [gap]
    nlinarith
  have hscaledUpper : (n : ℝ) * gap ≤
      perturbation perturbationMax - perturbation base := by
    linarith
  have hscaledStrict : perturbation perturbationMax - perturbation base <
      (n : ℝ) * gap :=
    (div_lt_iff₀ hgapPos).mp hnLarge
  linarith

end Optimization
end AppliedModelingLib

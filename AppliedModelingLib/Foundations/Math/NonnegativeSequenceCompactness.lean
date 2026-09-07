import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Compactness criterion for nonnegative real sequences

This file records a sequential compactness argument useful when a
nonnegative parameter sequence cannot approach either endpoint of the
extended nonnegative half-line and all of its finite positive cluster points
are identified.
-/

namespace AppliedModelingLib
namespace Sequence

open Filter Topology

/-- A nonnegative sequence which approaches neither zero nor positive infinity
has a strictly positive finite subsequential limit. -/
theorem exists_positive_subsequence_tendsto_of_nonneg
    {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hnot_zero : ∀ subsequence : ℕ → ℕ, Tendsto subsequence atTop atTop →
      ¬ Tendsto (u ∘ subsequence) atTop (𝓝 0))
    (hnot_top : ¬ Tendsto u atTop atTop) :
    ∃ (cluster : ℝ) (subsequence : ℕ → ℕ), 0 < cluster ∧ StrictMono subsequence ∧
      Tendsto (u ∘ subsequence) atTop (𝓝 cluster) := by
  rw [tendsto_atTop_atTop] at hnot_top
  push Not at hnot_top
  obtain ⟨bound, hbound⟩ := hnot_top
  have hfrequently_le : ∃ᶠ n in atTop, u n ≤ bound := by
    rw [frequently_atTop]
    intro start
    obtain ⟨n, hn_start, hn_bound⟩ := hbound start
    exact ⟨n, hn_start, hn_bound.le⟩
  have hfrequently_bounded : ∃ᶠ n in atTop, u n ∈ Set.Icc 0 bound :=
    hfrequently_le.mono fun n hn => ⟨hu n, hn⟩
  obtain ⟨cluster, hcluster_mem, subsequence, hsubsequence, hsubsequence_limit⟩ :=
    tendsto_subseq_of_frequently_bounded (Metric.isBounded_Icc (0 : ℝ) bound)
      hfrequently_bounded
  have hcluster_nonneg : 0 ≤ cluster := by
    rw [closure_Icc] at hcluster_mem
    exact hcluster_mem.1
  have hcluster_pos : 0 < cluster := by
    refine lt_of_le_of_ne hcluster_nonneg ?_
    intro hcluster_zero
    subst cluster
    exact (hnot_zero subsequence hsubsequence.tendsto_atTop) hsubsequence_limit
  exact ⟨cluster, subsequence, hcluster_pos, hsubsequence, hsubsequence_limit⟩

/-- A nonnegative real sequence converges to `limit` if every cofinal
subsequence avoids both endpoint limits and every finite positive cluster
point is `limit`. -/
theorem tendsto_of_nonneg_of_cofinal_subsequence_limits
    {u : ℕ → ℝ} {limit : ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hnot_zero : ∀ index : ℕ → ℕ, Tendsto index atTop atTop →
      ¬ Tendsto (u ∘ index) atTop (𝓝 0))
    (hnot_top : ∀ index : ℕ → ℕ, Tendsto index atTop atTop →
      ¬ Tendsto (u ∘ index) atTop atTop)
    (hcluster : ∀ (cluster : ℝ) (index : ℕ → ℕ),
      Tendsto index atTop atTop → Tendsto (u ∘ index) atTop (𝓝 cluster) →
        0 < cluster → cluster = limit) :
    Tendsto u atTop (𝓝 limit) := by
  apply tendsto_of_subseq_tendsto
  intro index hindex
  let v : ℕ → ℝ := u ∘ index
  have hnot_top_v : ¬ Tendsto v atTop atTop := by
    simpa [v] using hnot_top index hindex
  rw [tendsto_atTop_atTop] at hnot_top_v
  push Not at hnot_top_v
  obtain ⟨bound, hbound⟩ := hnot_top_v
  have hfrequently_le : ∃ᶠ n in atTop, v n ≤ bound := by
    rw [frequently_atTop]
    intro start
    obtain ⟨n, hn_start, hn_bound⟩ := hbound start
    exact ⟨n, hn_start, hn_bound.le⟩
  have hfrequently_bounded : ∃ᶠ n in atTop, v n ∈ Set.Icc 0 bound :=
    hfrequently_le.mono fun n hn => ⟨hu (index n), hn⟩
  obtain ⟨cluster, hcluster_mem, subsequence, hsubsequence, hsubsequence_limit⟩ :=
    tendsto_subseq_of_frequently_bounded (Metric.isBounded_Icc (0 : ℝ) bound)
      hfrequently_bounded
  have hcluster_nonneg : 0 ≤ cluster := by
    rw [closure_Icc] at hcluster_mem
    exact hcluster_mem.1
  have hcofinal : Tendsto (index ∘ subsequence) atTop atTop :=
    hindex.comp hsubsequence.tendsto_atTop
  have hsubsequence_limit' :
      Tendsto (u ∘ (index ∘ subsequence)) atTop (𝓝 cluster) := by
    simpa [v, Function.comp_def] using hsubsequence_limit
  have hcluster_pos : 0 < cluster := by
    refine lt_of_le_of_ne hcluster_nonneg ?_
    intro hcluster_zero
    subst cluster
    exact (hnot_zero (index ∘ subsequence) hcofinal) hsubsequence_limit'
  have hcluster_eq : cluster = limit :=
    hcluster cluster (index ∘ subsequence) hcofinal hsubsequence_limit' hcluster_pos
  refine ⟨subsequence, ?_⟩
  simpa [Function.comp_def, hcluster_eq] using hsubsequence_limit'

end Sequence
end AppliedModelingLib

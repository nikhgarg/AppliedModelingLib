import AppliedModelingLib.Foundations.Probability.CDFContinuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# The nonatomic probability integral transform

Applying a real probability measure's continuous CDF to a draw from that
measure gives the uniform law on the unit interval. Flat CDF intervals are
allowed; no density or strictly increasing CDF is assumed.
-/

namespace AppliedModelingLib.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- A continuous CDF has sublevel mass equal to its level below one. The last
point of a nonempty sublevel set handles flat CDF intervals exactly. -/
theorem measure_cdf_sublevel_of_noAtoms
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    μ {x | cdf μ x ≤ t} = ENNReal.ofReal t := by
  let S := {x | cdf μ x ≤ t}
  have hcont := continuous_cdf_of_noAtoms μ
  have hclosed : IsClosed S := isClosed_le hcont continuous_const
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ht1)).exists
  have hbounded : BddAbove S := ⟨b, fun x hx => by
    by_contra hn
    have hmono := monotone_cdf μ (le_of_not_ge hn)
    exact (not_le_of_gt hb) (hmono.trans hx)⟩
  by_cases hne : S.Nonempty
  · let q := sSup S
    have hq : q ∈ S := hclosed.csSup_mem hne hbounded
    have hset : S = Iic q := by
      ext x
      exact ⟨fun hx => le_csSup hbounded hx,
        fun hx => (monotone_cdf μ hx).trans hq⟩
    have hqb : q ≤ b := by
      by_contra hn
      exact (not_le_of_gt hb) ((monotone_cdf μ (le_of_not_ge hn)).trans hq)
    have hlevel : cdf μ q = t := by
      obtain ⟨z, hz, heq⟩ := intermediate_value_Icc hqb hcont.continuousOn
        (show t ∈ Icc (cdf μ q) (cdf μ b) from ⟨hq, hb.le⟩)
      have hzS : z ∈ S := heq.le
      have hzq : z ≤ q := le_csSup hbounded hzS
      exact le_antisymm hq (heq ▸ monotone_cdf μ hzq)
    change μ S = ENNReal.ofReal t
    rw [hset, ← ofReal_cdf μ q, hlevel]
  · have ht : t = 0 := by
      by_contra hn
      have htpos := lt_of_le_of_ne ht0 (Ne.symm hn)
      obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds htpos)).exists
      exact hne ⟨a, ha.le⟩
    have hS : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    change μ S = ENNReal.ofReal t
    rw [hS, ht]
    simp

/-- The CDF pushes any nonatomic real probability measure to uniform
probability on `[0,1]`, without a density or strict-CDF-monotonicity premise. -/
theorem map_cdf_eq_uniform_of_noAtoms
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Measure.map (cdf μ) μ = volume.restrict (Icc (0 : ℝ) 1) := by
  have hm : Measurable (cdf μ) := (monotone_cdf μ).measurable
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  by_cases ht0 : t < 0
  · have hpre : (cdf μ) ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (ht0.trans_le (cdf_nonneg μ x))
    have hinter : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro hx hx0 _
      linarith
    simp only [hpre, hinter, measure_empty]
  · have hnonneg := le_of_not_gt ht0
    by_cases ht1 : t < 1
    · have hinter : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans ht1.le⟩⟩
      rw [hinter, Real.volume_Icc, sub_zero]
      exact measure_cdf_sublevel_of_noAtoms μ hnonneg ht1
    · have htop := le_of_not_gt ht1
      have hpre : (cdf μ) ⁻¹' Iic t = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cdf_le_one μ x).trans htop
      have hinter : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 1 :=
        inter_eq_right.mpr (fun _ hx => hx.2.trans htop)
      rw [hpre, hinter, measure_univ, Real.volume_Icc]
      norm_num

end AppliedModelingLib.Probability

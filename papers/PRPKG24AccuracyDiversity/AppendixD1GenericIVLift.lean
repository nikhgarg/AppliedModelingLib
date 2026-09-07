import PRPKG24AccuracyDiversity.AppendixD1GenericIV

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericIVLift

open AppliedModelingLib
open AppendixD1GenericPower
open AppendixD1GenericIV

/-- The corrected power objective is continuous on the whole finite profile space. -/
theorem continuous_sourcePowerObjective
    {m : ℕ} (p : Fin m → ℝ) {sigma : ℝ} (hsigma_nonneg : 0 ≤ sigma) :
    Continuous (sourcePowerObjective p sigma) := by
  unfold sourcePowerObjective
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul
    ((Real.continuous_rpow_const hsigma_nonneg).comp (continuous_apply i))

/--
Corrected generic Lemma D.1(iv), lifted directly to the literal fixed-total
integer optimizers.  The proof uses the raw tail comparison in both
directions and the strict compact simplex gap of the explicit power
objective; it does not take a limiting-objective or optimizer-convergence
certificate as an input.
-/
theorem corrected_lemmaD1_iv_optimizer_shares_of_power_tail
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile (targetShare p sigma) := by
  classical
  have hweight_sum_pos : 0 < ∑ i : Fin m, p i :=
    Finset.sum_pos (fun i _ => hp_pos i) Finset.univ_nonempty
  have hweight_sum_ne : (∑ i : Fin m, p i) ≠ 0 := ne_of_gt hweight_sum_pos
  have htarget_simplex : targetShare p sigma ∈ stdSimplex ℝ (Fin m) := by
    constructor
    · intro i
      exact (targetShare_pos p hsigma_lt_one hp_pos i).le
    · exact sum_targetShare_eq_one p hsigma_lt_one hp_pos
  have hobjective_cont :
      ContinuousOn (sourcePowerObjective p sigma) (stdSimplex ℝ (Fin m)) :=
    (continuous_sourcePowerObjective p hsigma_pos.le).continuousOn
  have hobjective_strict :
      ∀ x : Fin m → ℝ, x ∈ stdSimplex ℝ (Fin m) ->
        x ≠ targetShare p sigma ->
          sourcePowerObjective p sigma x <
            sourcePowerObjective p sigma (targetShare p sigma) := by
    intro x hx hx_ne
    exact sourcePowerObjective_lt_target_of_simplex_ne
      p hsigma_pos hsigma_lt_one hp_pos x hx.1 hx.2 hx_ne
  have hbenchmark_counts_atTop : ∀ i,
      Tendsto (fun N : ℕ => (powerBenchmarkAllocation p sigma N).count i)
        atTop atTop := by
    intro i
    exact tendsto_powerBenchmarkAllocation_count_atTop
      p hsigma_pos hsigma_lt_one hp_pos i
  have hbenchmark_share : ∀ i,
      Tendsto
        (fun N : ℕ => ((powerBenchmarkAllocation p sigma N).count i : ℝ) /
          (N : ℝ))
        atTop (nhds (targetShare p sigma i)) := by
    intro i
    exact tendsto_powerBenchmarkAllocation_count_div_targetShare
      p hsigma_pos hsigma_lt_one hp_pos i
  have hbenchmark_value_limit :=
    tendsto_normalized_rawPowerTailObjective_of_power_tail
      p (powerBenchmarkAllocation p sigma) (targetShare p sigma)
      hB_pos hsigma_pos htail hbenchmark_counts_atTop hbenchmark_share
  have hactual_simplex : ∀ᶠ N : ℕ in atTop,
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ∈
        stdSimplex ℝ (Fin m) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    constructor
    · intro i
      exact AppliedModelingLib.Allocation.share_nonneg (seq.allocation N) i
    · exact AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
        (a := seq.allocation N) (by
          rw [(seq.optimal N).1]
          exact Nat.ne_of_gt hN)
  intro t
  change Tendsto
    (fun N : ℕ => AppliedModelingLib.Allocation.share (seq.allocation N) t)
    atTop (nhds (targetShare p sigma t))
  rw [Metric.tendsto_nhds]
  intro ε hε_pos
  let εhalf : ℝ := ε / 2
  have hεhalf_pos : 0 < εhalf := by
    dsimp [εhalf]
    linarith
  obtain ⟨eta, heta_pos, hseparate⟩ :=
    AppliedModelingLib.Allocation.exists_gap_on_stdSimplex_of_strict_unique_max
      (sourcePowerObjective p sigma) (targetShare p sigma)
      htarget_simplex hobjective_cont hobjective_strict εhalf hεhalf_pos
  let delta : ℝ := eta / 3
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    linarith
  let tailDelta : ℝ := delta / ∑ i : Fin m, p i
  have htailDelta_pos : 0 < tailDelta := by
    dsimp [tailDelta]
    exact div_pos hdelta_pos hweight_sum_pos
  have htail_error : tailDelta * (∑ i : Fin m, p i) = delta := by
    dsimp [tailDelta]
    field_simp
  have hbenchmark_lower : ∀ᶠ N : ℕ in atTop,
      sourcePowerObjective p sigma (targetShare p sigma) - delta ≤
        rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) /
          (B * (N : ℝ) ^ sigma) := by
    filter_upwards [hbenchmark_value_limit.eventually
        (Ioi_mem_nhds (by linarith :
          sourcePowerObjective p sigma (targetShare p sigma) - delta <
            sourcePowerObjective p sigma (targetShare p sigma)))] with N hN
    exact hN.le
  have hselected_upper :=
    eventually_normalized_rawPowerTailObjective_le_sourcePowerObjective_add
      p seq hp_pos hB_pos hsigma_pos hsigma_lt_one hconc htail htailDelta_pos
  filter_upwards [eventually_gt_atTop 0, hactual_simplex, hbenchmark_lower,
      hselected_upper] with N hN hsimplex hbenchmark_lowerN hselected_upperN
  by_contra hnot
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden_pos : 0 < B * (N : ℝ) ^ sigma :=
    mul_pos hB_pos (Real.rpow_pos_of_pos hN_real_pos sigma)
  have hbenchmark_le_selected :
      rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) /
          (B * (N : ℝ) ^ sigma) ≤
        rawPowerTailObjective p h (seq.allocation N) /
          (B * (N : ℝ) ^ sigma) := by
    have hopt := (seq.optimal N).2 (powerBenchmarkAllocation p sigma N)
      (powerBenchmarkAllocation_total p sigma N)
    have hraw :
        rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) ≤
          rawPowerTailObjective p h (seq.allocation N) := by
      simpa [rawPowerTailObjective, AppliedModelingLib.Allocation.objective] using hopt
    exact (div_le_div_iff_of_pos_right hden_pos).2 hraw
  have hfar_abs : εhalf <
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - targetShare p sigma t| := by
    have hnot_dist : ¬ dist
        (AppliedModelingLib.Allocation.share (seq.allocation N) t)
        (targetShare p sigma t) < ε := by
      simpa using hnot
    have hdist : ε ≤ dist
        (AppliedModelingLib.Allocation.share (seq.allocation N) t)
        (targetShare p sigma t) := le_of_not_gt hnot_dist
    rw [Real.dist_eq] at hdist
    calc
      εhalf = ε / 2 := rfl
      _ < ε := by linarith
      _ ≤ |AppliedModelingLib.Allocation.share (seq.allocation N) t - targetShare p sigma t| := hdist
  have hgapN := hseparate
    (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i)
    hsimplex ⟨t, hfar_abs⟩
  have hchain :
      sourcePowerObjective p sigma (targetShare p sigma) - delta ≤
        sourcePowerObjective p sigma (targetShare p sigma) - eta +
          tailDelta * ∑ i : Fin m, p i := by
    exact le_trans hbenchmark_lowerN
      (le_trans hbenchmark_le_selected
        (le_trans hselected_upperN (add_le_add hgapN le_rfl)))
  rw [htail_error] at hchain
  have heta_le : eta ≤ 2 * delta := by
    linarith
  have htwo_delta_lt_eta : 2 * delta < eta := by
    dsimp [delta]
    linarith
  exact (not_lt_of_ge heta_le) htwo_delta_lt_eta

end AppendixD1GenericIVLift
end PRPKG24AccuracyDiversity

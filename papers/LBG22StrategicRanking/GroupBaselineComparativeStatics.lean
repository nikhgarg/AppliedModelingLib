import LBG22StrategicRanking.GroupBaselineExamples

/-!
# Fixed-capacity welfare gaps under baseline qualification

Varying the policy cutoff changes the admitted reward while capacity and
the two-group population remain fixed. Around cutoff `3/8`, capacity `5/32`
admits an interval of high latent ranks at baseline effort in both groups.
Their actual welfare gap is locally constant, with derivative zero.
-/

namespace LBG22StrategicRanking.BaselineGroupExample

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def boundaryEffort (rho c : ℝ) : ℝ := Real.sqrt (rho / (1 - c))

noncomputable def fixedCapacityEffort (rho c : ℝ) : Bool × ℝ → ℝ :=
  effort (4 * c / 3) (boundaryEffort rho c)

noncomputable def fixedCapacityScore (rho c : ℝ) : Bool × ℝ → ℝ :=
  score (4 * c / 3) (boundaryEffort rho c)

/-- Actual welfare gap under the policy with the same exogenous capacity
`rho` at every cutoff. The effort and score family does not choose its own
population, technology, skill distribution, or tie key. -/
noncomputable def fixedCapacityGap (rho : ℝ) (tie : Bool × ℝ → ℝ) (t c : ℝ) : ℝ :=
  sourceActualGroupWelfareGap (fun e => e ^ 2) (fixedCapacityEffort rho c) (fixedCapacityScore rho c) tie
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t

theorem cutoff_parameter_id (c : ℝ) : 3 * (4 * c / 3) / 4 = c := by ring

theorem fixedCapacity_parameters {rho c : ℝ} (hrho : 0 < rho)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hc3 : c ≤ 3 / 4) :
    4 * c / 3 ∈ Ioc (0 : ℝ) 1 ∧ boundaryEffort rho c ∈ Ioc (0 : ℝ) 1 ∧
      capacity (4 * c / 3) (boundaryEffort rho c) = rho := by
  have hden : 0 < 1 - c := by linarith [hc.2]
  have hq : 0 < rho / (1 - c) := div_pos hrho hden
  have hq1 : rho / (1 - c) ≤ 1 := (div_le_one hden).mpr (by linarith [hc.2])
  refine ⟨⟨by linarith [hc.1], by linarith⟩,
    ⟨Real.sqrt_pos.mpr hq, Real.sqrt_le_one.mpr hq1⟩, ?_⟩
  unfold capacity boundaryEffort
  rw [cutoff_parameter_id, Real.sq_sqrt hq.le, div_mul_cancel₀ _ hden.ne']

/-- An actual equilibrium family at fixed capacity, on the cutoffs whose
effective-skill threshold lies in the overlapping part of the supports. -/
theorem fixedCapacity_equilibrium {rho c : ℝ} (hrho : 0 < rho)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hc3 : c ≤ 3 / 4)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) (fun e => 1 + e)
        effectiveSkill (fixedCapacityScore rho c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) x (fixedCapacityEffort rho c x) := by
  have hp := fixedCapacity_parameters hrho hc hc3
  have heq := (source_equilibrium hp.1 hp.2.1 htie hinj).2.2
  simpa only [hp.2.2, cutoff_parameter_id, fixedCapacityScore, fixedCapacityEffort] using heq

theorem fixedCapacityGap_eq {rho c t : ℝ} (hrho : 0 < rho)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hc3 : c ≤ 3 / 4) (tie : Bool × ℝ → ℝ) :
    fixedCapacityGap rho tie t c = welfareGap (4 * c / 3) (boundaryEffort rho c) tie t := by
  have hp := fixedCapacity_parameters hrho hc hc3
  simp only [fixedCapacityGap, welfareGap, hp.2.2, cutoff_parameter_id, fixedCapacityScore, fixedCapacityEffort]

/-- High latent ranks in both groups qualify at baseline throughout a
nondegenerate neighborhood of the policy cutoff, with capacity held fixed. -/
theorem fixedCapacityGap_zero_near {c t : ℝ}
    (hc : c ∈ Icc (1 / 3 : ℝ) (2 / 5)) (ht : t ∈ Ioc (7 / 8 : ℝ) 1) (tie : Bool × ℝ → ℝ) :
    fixedCapacityGap (5 / 32) tie t c = 0 := by
  have hcf : c ∈ Ioc (0 : ℝ) (1 - 5 / 32) := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hc3 : c ≤ 3 / 4 := by linarith [hc.2]
  have hp := fixedCapacity_parameters (by norm_num : (0 : ℝ) < 5 / 32) hcf hc3
  have hden : 0 < 1 - c := by linarith [hc.2]
  have hd : boundaryEffort (5 / 32) c ≤ 3 / 5 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, (div_le_iff₀ hden).mpr ?_⟩
    nlinarith [hc.2]
  have ha : 4 * c / 3 ≤ 8 / 15 := by linarith [hc.2]
  have hprod := mul_le_mul (show 1 + boundaryEffort (5 / 32) c ≤ 8 / 5 by linarith) ha hp.1.1.le
    (by norm_num : (0 : ℝ) ≤ 8 / 5)
  have hT : (1 + boundaryEffort (5 / 32) c) * (4 * c / 3) < 7 / 8 := by linarith
  rw [fixedCapacityGap_eq (by norm_num) hcf hc3 tie]
  exact welfareGap_zero_above_threshold hp.1 hp.2.1.1 tie ⟨hT.trans ht.1, ht.2⟩

/-- The actual fixed-capacity welfare-gap derivative is zero throughout
a positive-length interval of latent ranks, at an interior policy cutoff. -/
theorem fixedCapacityGap_hasDerivAt_zero {t : ℝ} (ht : t ∈ Ioc (7 / 8 : ℝ) 1)
    (tie : Bool × ℝ → ℝ) : HasDerivAt (fixedCapacityGap (5 / 32) tie t) 0 (3 / 8) := by
  have heq : fixedCapacityGap (5 / 32) tie t =ᶠ[𝓝 (3 / 8)] fun _ => 0 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (1 / 3 : ℝ) < 3 / 8)
      (by norm_num : (3 / 8 : ℝ) < 2 / 5)] with c hc
    exact fixedCapacityGap_zero_near hc ht tie
  exact (hasDerivAt_const (3 / 8) (0 : ℝ)).congr_of_eventuallyEq heq

/-- A fixed-population, fixed-capacity counterexample to the strictly
positive derivative in Proposition 4.3. It supplies actual equilibria on
an open neighborhood and a zero derivative at every rank in `(7/8,1]`.
These ranks are strictly inside the source's common-admission region. -/
theorem source_derivative_counterexample {tie : Bool × ℝ → ℝ}
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    (3 / 8 : ℝ) ≤ sourceEnvironmentCDF (fun t => t) 2 1 1 ∧
      (∀ c ∈ Icc (1 / 3 : ℝ) (2 / 5),
        c ∈ Ioc (0 : ℝ) (1 - 5 / 32) ∧
        ∀ᵐ x ∂sourceTwoGroupMeasure,
          SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) (fun e => 1 + e)
            effectiveSkill (fixedCapacityScore (5 / 32) c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (sourceTwoLevelReward (5 / 32) c) x (fixedCapacityEffort (5 / 32) c x)) ∧
      (∀ t ∈ Ioc (7 / 8 : ℝ) 1,
        sourceGroupThreshold (fun t => t) 2 1 false (3 / 8) < t ∧
        HasDerivAt (fixedCapacityGap (5 / 32) tie t) 0 (3 / 8)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mixtureCDF_at (by norm_num)]
    norm_num
  · intro c hc
    have hcf : c ∈ Ioc (0 : ℝ) (1 - 5 / 32) := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    exact ⟨hcf, fixedCapacity_equilibrium (by norm_num) hcf (by linarith [hc.2]) htie hinj⟩
  · intro t ht
    refine ⟨?_, fixedCapacityGap_hasDerivAt_zero ht tie⟩
    have h := groupThreshold_eq (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num) false
    norm_num at h
    rw [h]
    linarith [ht.1]

end LBG22StrategicRanking.BaselineGroupExample

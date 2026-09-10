import LBG22StrategicRanking.GroupBoundaryPrimitiveRepairs

/-!
# Quantitative welfare-gap comparisons

Convex score costs provide both a positive lower bound on the welfare-gap
increment and a finite upper bound on boundary cost increments. Together
these control policy differences without differentiating a mixture inverse.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

private theorem convex_slope_le_of_endpoints {C : ℝ → ℝ} {upper a b c d : ℝ}
    (hconv : ConvexOn ℝ (Iic upper) C) (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hbd : b ≤ d) (hd : d ≤ upper) :
    slope C a b ≤ slope C c d := by
  have had : a < d := hac.trans_lt hcd
  have hs1 := hconv.slope_mono (hab.le.trans (hbd.trans hd))
    (show b ∈ Iic upper \ {a} from ⟨hbd.trans hd, by simpa using hab.ne'⟩)
    (show d ∈ Iic upper \ {a} from ⟨hd, by simpa using had.ne'⟩) hbd
  have hs2 := hconv.slope_mono hd
    (show a ∈ Iic upper \ {d} from ⟨had.le.trans hd, by simpa using had.ne⟩)
    (show c ∈ Iic upper \ {d} from ⟨hcd.le.trans hd, by simpa using hcd.ne⟩) hac
  exact hs1.trans (by simpa only [slope_comm] using hs2)

/-- Score-cost increments contract by at least the inverse skill ratio,
including when one interval crosses the zero-cost production floor. -/
theorem sourceCostAtScore_gap_ratio_le
    {cost production : ℝ → ℝ} {E T U lowSkill highSkill : ℝ}
    (hE : 0 ≤ E) (hp : MonotoneOn cost (Icc 0 E)) (hpconv : ConvexOn ℝ (Icc 0 E) cost)
    (hg : ContinuousOn production (Icc 0 E)) (hgm : StrictMonoOn production (Icc 0 E))
    (hgconc : ConcaveOn ℝ (Icc 0 E) production)
    (hT : 0 ≤ T) (hTU : T ≤ U) (hlo : 0 < lowSkill) (hskill : lowSkill ≤ highSkill)
    (hcap : U / lowSkill ≤ production E) :
    highSkill * (sourceCostAtScore cost production E (U / highSkill) -
        sourceCostAtScore cost production E (T / highSkill)) ≤
      lowSkill * (sourceCostAtScore cost production E (U / lowSkill) -
        sourceCostAtScore cost production E (T / lowSkill)) := by
  rcases eq_or_lt_of_le hTU with rfl | hTU
  · simp
  let C := sourceCostAtScore cost production E
  have hhi : 0 < highSkill := hlo.trans_le hskill
  have hU : 0 ≤ U := hT.trans hTU.le
  have h := convex_slope_le_of_endpoints (sourceCostAtScore_convexOn hE hp hpconv hg hgm hgconc)
    ((div_lt_div_iff_of_pos_right hhi).mpr hTU) ((div_lt_div_iff_of_pos_right hlo).mpr hTU)
    ((div_le_div_iff₀ hhi hlo).mpr (mul_le_mul_of_nonneg_left hskill hT))
    ((div_le_div_iff₀ hhi hlo).mpr (mul_le_mul_of_nonneg_left hskill hU)) hcap
  have hslope (s : ℝ) :
      slope C (T / s) (U / s) = s * (C (U / s) - C (T / s)) / (U - T) := by
    rw [slope_def_field]
    field_simp
  rw [hslope highSkill, hslope lowSkill] at h
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr hTU)).mp h

/-- A positive effort cost at the lower score gives a positive linear
lower bound on the increase in the between-skill cost gap. No derivatives
or positive baseline-production exclusion are needed. -/
theorem sourceCostAtScore_welfareGap_increment_lower
    {cost production : ℝ → ℝ} {E T U lowSkill highSkill : ℝ}
    (hE : 0 ≤ E) (hp : MonotoneOn cost (Icc 0 E)) (hpconv : ConvexOn ℝ (Icc 0 E) cost)
    (hpzero : cost 0 = 0)
    (hg : ContinuousOn production (Icc 0 E)) (hgm : StrictMonoOn production (Icc 0 E))
    (hgconc : ConcaveOn ℝ (Icc 0 E) production) (hg0 : 0 ≤ production 0)
    (hT : 0 < T) (hTU : T ≤ U) (hlo : 0 < lowSkill) (hskill : lowSkill ≤ highSkill)
    (hcap : U / lowSkill ≤ production E) :
    (1 - lowSkill / highSkill) * sourceCostAtScore cost production E (T / lowSkill) / T * (U - T) ≤
      (sourceCostAtScore cost production E (U / lowSkill) - sourceCostAtScore cost production E (U / highSkill)) -
        (sourceCostAtScore cost production E (T / lowSkill) - sourceCostAtScore cost production E (T / highSkill)) := by
  rcases eq_or_lt_of_le hTU with rfl | hTU
  · simp
  let C := sourceCostAtScore cost production E
  have hhi : 0 < highSkill := hlo.trans_le hskill
  have hC := sourceCostAtScore_convexOn hE hp hpconv hg hgm hgconc
  have hCzero : C 0 = 0 := sourceCostAtScore_zero hE hpzero hgm hg0
  have hgE0 : 0 ≤ production E := hg0.trans (hgm.monotoneOn ⟨le_rfl, hE⟩ ⟨hE, le_rfl⟩ hE)
  have hx : 0 < T / lowSkill := div_pos hT hlo
  have hxy : T / lowSkill < U / lowSkill := (div_lt_div_iff_of_pos_right hlo).mpr hTU
  have hCB := hC.slope_mono_adjacent (show (0 : ℝ) ∈ Iic (production E) from hgE0) hcap hx hxy
  change (C (T / lowSkill) - C 0) / (T / lowSkill - 0) ≤
    (C (U / lowSkill) - C (T / lowSkill)) / (U / lowSkill - T / lowSkill) at hCB
  rw [hCzero, sub_zero, sub_zero] at hCB
  have hCB' := (le_div_iff₀ (sub_pos.mpr hxy)).mp hCB
  have hnorm : C (T / lowSkill) / (T / lowSkill) * (U / lowSkill - T / lowSkill) =
      C (T / lowSkill) / T * (U - T) := by field_simp
  rw [hnorm] at hCB'
  have hratio := sourceCostAtScore_gap_ratio_le hE hp hpconv hg hgm hgconc hT.le hTU.le hlo hskill hcap
  have hCA : C (U / highSkill) - C (T / highSkill) ≤
      lowSkill / highSkill * (C (U / lowSkill) - C (T / lowSkill)) := by
    calc
      _ ≤ (lowSkill * (C (U / lowSkill) - C (T / lowSkill))) / highSkill :=
        (le_div_iff₀ hhi).mpr (by nlinarith [hratio])
      _ = _ := by ring
  have hfactor : 0 ≤ 1 - lowSkill / highSkill := sub_nonneg.mpr ((div_le_one hhi).mpr hskill)
  have h := mul_le_mul_of_nonneg_left hCB' hfactor
  change (1 - lowSkill / highSkill) * C (T / lowSkill) / T * (U - T) ≤
    (C (U / lowSkill) - C (U / highSkill)) - (C (T / lowSkill) - C (T / highSkill))
  calc
    _ = (1 - lowSkill / highSkill) * (C (T / lowSkill) / T * (U - T)) := by ring
    _ ≤ (1 - lowSkill / highSkill) * (C (U / lowSkill) - C (T / lowSkill)) := h
    _ ≤ _ := by nlinarith only [hCA]

/-- A source-primitive upper bound on score-cost slopes up to the unit-cost
effort cap, obtained from the next unit of effort rather than a derivative. -/
noncomputable def sourceScoreCostSlopeBound (cost production : ℝ → ℝ) (E : ℝ) : ℝ :=
  (cost (E + 1) - cost E) / (production (E + 1) - production E)

theorem sourceScoreCostSlopeBound_pos
    {cost production : ℝ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (hp : StrictMonoOn cost (Ici 0)) (hg : StrictMonoOn production (Ici 0)) :
    0 < sourceScoreCostSlopeBound cost production E := by
  have hF : 0 ≤ E + 1 := by linarith
  exact div_pos (sub_pos.mpr (hp hE hF (by linarith))) (sub_pos.mpr (hg hE hF (by linarith)))

/-- Convexity supplies a finite Lipschitz bound for score costs throughout
the equilibrium-feasible range. The larger inverse interval is only a proof
device and does not cap the source action space. -/
theorem sourceCostAtScore_increment_le
    {cost production : ℝ → ℝ} {E x y : ℝ} (hE : 0 ≤ E)
    (hp : MonotoneOn cost (Ici 0)) (hpconv : ConvexOn ℝ (Ici 0) cost)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hxy : x ≤ y) (hy : y ≤ production E) :
    sourceCostAtScore cost production E y - sourceCostAtScore cost production E x ≤
      sourceScoreCostSlopeBound cost production E * (y - x) := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · simp
  let F := E + 1
  have hF : 0 ≤ F := by dsimp [F]; linarith
  have hEF : E < F := by dsimp [F]; linarith
  have hgEF : production E < production F := hgm hE hF hEF
  let C := sourceCostAtScore cost production F
  have hconv := sourceCostAtScore_convexOn hF (hp.mono Icc_subset_Ici_self)
    (hpconv.subset Icc_subset_Ici_self (convex_Icc _ _)) (hg.mono Icc_subset_Ici_self)
    (hgm.mono Icc_subset_Ici_self) (hgconc.subset Icc_subset_Ici_self (convex_Icc _ _))
  have hs := convex_slope_le_of_endpoints hconv hxy hgEF (hxy.le.trans hy) (hy.trans hgEF.le) le_rfl
  have hcost (e : ℝ) (he : e ∈ Icc (0 : ℝ) F) : C (production e) = cost e := by
    change cost (sourceEffortAtScore production F (production e)) = cost e
    rw [sourceEffortAtScore_at_production (hgm.mono Icc_subset_Ici_self) he]
  change slope C x y ≤ slope C (production E) (production F) at hs
  rw [slope_def_field, slope_def_field, hcost E ⟨hE, hEF.le⟩, hcost F ⟨hF, le_rfl⟩] at hs
  have h := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
  have hcap (z : ℝ) (hz : z ≤ production E) : sourceCostAtScore cost production E z = C z :=
    congrArg cost (sourceEffortAtScore_eq_of_caps hE hF (hg.mono Icc_subset_Ici_self)
      (hg.mono Icc_subset_Ici_self) hgm hz (hz.trans hgEF.le))
  rw [hcap y hy, hcap x (hxy.le.trans hy)]
  exact h

/-- Boundary indifference yields a quantitative threshold increase as
the reward rises and the marginal admitted skill weakly increases. -/
theorem sourceBoundaryThreshold_increment_lower
    {cost production : ℝ → ℝ} {E T U s t q r : ℝ}
    (hE : 0 ≤ E) (hp : StrictMonoOn cost (Ici 0)) (hpconv : ConvexOn ℝ (Ici 0) cost)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hs : 0 < s) (hst : s ≤ t) (hqr : q ≤ r)
    (hbaseT : production 0 * s ≤ T) (hbaseU : production 0 * t ≤ U)
    (hcapT : T ≤ production E * s) (hcapU : U ≤ production E * t)
    (hcostT : sourceCostAtScore cost production E (T / s) = q)
    (hcostU : sourceCostAtScore cost production E (U / t) = r) :
    s / sourceScoreCostSlopeBound cost production E * (r - q) ≤ U - T := by
  have ht : 0 < t := hs.trans_le hst
  have hx : T / s ∈ Icc (production 0) (production E) :=
    ⟨(le_div_iff₀ hs).mpr hbaseT, (div_le_iff₀ hs).mpr hcapT⟩
  have hy : U / t ∈ Icc (production 0) (production E) :=
    ⟨(le_div_iff₀ ht).mpr hbaseU, (div_le_iff₀ ht).mpr hcapU⟩
  have hCM := sourceCostAtScore_strictMonoOn_feasible hE (hp.mono Icc_subset_Ici_self)
    (hg.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self)
  have hxy : T / s ≤ U / t := by
    by_contra hn
    have h := hCM hy hx (lt_of_not_ge hn)
    rw [hcostT, hcostU] at h
    exact (not_lt_of_ge hqr) h
  have h := sourceCostAtScore_increment_le hE hp.monotoneOn hpconv hg hgm hgconc hxy hy.2
  rw [hcostT, hcostU] at h
  have hL := sourceScoreCostSlopeBound_pos hE hp hgm
  have hU : 0 ≤ U := (mul_nonneg hg0 ht.le).trans hbaseU
  have hratio : U / t ≤ U / s := (div_le_div_iff₀ ht hs).mpr (mul_le_mul_of_nonneg_left hst hU)
  have h' := h.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hratio _) hL.le)
  have h'' := mul_le_mul_of_nonneg_left h' hs.le
  have hnorm : s * (sourceScoreCostSlopeBound cost production E * (U / s - T / s)) =
      sourceScoreCostSlopeBound cost production E * (U - T) := by field_simp
  rw [hnorm] at h''
  have hdiv : s * (r - q) / sourceScoreCostSlopeBound cost production E ≤ U - T :=
    (div_le_iff₀ hL).mpr (by nlinarith only [h''])
  simpa only [div_mul_eq_mul_div] using hdiv

/-- The unique nonnegative effort whose source cost equals one. -/
noncomputable def sourceUnitCostEffort (cost : ℝ → ℝ) : ℝ :=
  Function.invFunOn cost (Ici 0) 1

theorem sourceUnitCostEffort_eq {cost : ℝ → ℝ} {E : ℝ}
    (hp : StrictMonoOn cost (Ici 0)) (hE : 0 ≤ E) (hpE : cost E = 1) :
    sourceUnitCostEffort cost = E := by
  unfold sourceUnitCostEffort
  rw [← hpE]
  exact hp.injOn.leftInvOn_invFunOn hE

theorem sourceUnitCostEffort_spec {cost : ℝ → ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0) :
    0 < sourceUnitCostEffort cost ∧ cost (sourceUnitCostEffort cost) = 1 := by
  obtain ⟨E, hE, hpE, hpm⟩ := exists_unitCost_effort_of_sourcePrimitives hpcont hpconv hpnonneg hpzero
  rw [sourceUnitCostEffort_eq hpm hE.le hpE]
  exact ⟨hE, hpE⟩

/-- A positive growth coefficient determined by cost, production, capacity,
and the environment ratio, independently of the admission policy. -/
noncomputable def sourceGroupGapGrowthRate
    (cost production : ℝ → ℝ) (psiA psiB rho : ℝ) : ℝ :=
  (1 - psiB / psiA) * rho /
    (production (sourceUnitCostEffort cost) * sourceScoreCostSlopeBound cost production (sourceUnitCostEffort cost))

theorem sourceGroupGapGrowthRate_pos {cost production : ℝ → ℝ} {psiA psiB rho : ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgm : StrictMonoOn production (Ici 0)) (hg0 : 0 ≤ production 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) (hrho : 0 < rho) :
    0 < sourceGroupGapGrowthRate cost production psiA psiB rho := by
  have hE := (sourceUnitCostEffort_spec hpcont hpconv hpnonneg hpzero).1
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hgE : 0 < production (sourceUnitCostEffort cost) := hg0.trans_lt (hgm (by simp) hE.le hE)
  have hL := sourceScoreCostSlopeBound_pos hE.le hpm hgm
  have hf : 0 < 1 - psiB / psiA := sub_pos.mpr ((div_lt_one (hB.trans hBA)).mpr hBA)
  exact div_pos (mul_pos hf hrho) (mul_pos hgE hL)

/-- At a fixed policy, one coefficient controls the actual welfare-gap
increase against every more selective feasible policy and every equilibrium
of that policy. The coefficient is positive at each applicant whose
disadvantaged effort has positive cost at the fixed policy. All population
and policy primitives, including capacity and tie order, remain fixed. -/
theorem sourceActualGroupWelfareGap_quantitative_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effortC scoreC tie : Bool × ℝ → ℝ}
    {psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscoreC : Measurable scoreC) (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbestC : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) scoreC tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effortC x)) :
    ∃ K : ℝ → ℝ,
      K = (fun t => sourceGroupGapGrowthRate cost production psiA psiB rho * cost (effortC (false, t))) ∧
      (∀ t, 0 ≤ cost (effortC (false, t)) → 0 ≤ K t) ∧
      (∀ t, 0 < cost (effortC (false, t)) → 0 < K t) ∧
      ∀ d ∈ Ioc (0 : ℝ) (1 - rho), c ≤ d →
        ∀ effortD scoreD : Bool × ℝ → ℝ, Measurable scoreD →
          (∀ᵐ x ∂sourceTwoGroupMeasure,
            SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
              (sourceEnvironmentSkill skill psiA psiB) scoreD tie
              (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) x (effortD x)) →
          ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false d < t →
            K t * (d - c) ≤
              sourceActualGroupWelfareGap cost effortD scoreD tie (fun i : Fin 2 => sourceTwoLevelCutoff d i)
                  (sourceTwoLevelReward rho d) t -
                sourceActualGroupWelfareGap cost effortC scoreC tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
                  (sourceTwoLevelReward rho c) t := by
  let K := fun t => sourceGroupGapGrowthRate cost production psiA psiB rho * cost (effortC (false, t))
  have hrate := sourceGroupGapGrowthRate_pos hpcont hpconv hpnonneg hpzero hgm hg0 hB hBA hrho
  refine ⟨K, rfl, fun t ht => mul_nonneg hrate.le ht, fun t ht => mul_pos hrate ht, ?_⟩
  by_cases hcB : c < sourceDisadvantagedRank skill psiA psiB 1
  swap
  · intro d _ hcd _ _ _ _
    have htheta := sourceDisadvantagedThreshold_eq_one hfcont hf (hB.trans hBA) hB ((le_of_not_gt hcB).trans hcd)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro hhigh
    change sourceDisadvantagedThreshold skill psiA psiB d < t at hhigh
    rw [htheta] at hhigh
    exact False.elim ((not_lt_of_ge ht.2) hhigh)
  obtain ⟨E, T, hE, hpE, hbaseT, hcapT, hcostT, hprofileC⟩ :=
    sourceDisadvantagedEquilibrium_boundary_of_sourcePrimitives hrho hc hcB
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreC htie hinj hbestC
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  let tc := sourceDisadvantagedThreshold skill psiA psiB c
  have htc : tc ∈ Icc (0 : ℝ) 1 := sourceDisadvantagedThreshold_mem
  have hc1 : c < 1 := by linarith [hc.2]
  have htc0 : 0 < tc := hc.1.trans
    (sourceDisadvantagedThreshold_gt_cutoff hfcont hf hf0 hB hBA ⟨hc.1, hc1⟩)
  have hskillc : 0 < psiB * skill tc := mul_pos hB (hf0.trans_lt (hf (by norm_num) htc htc0))
  have hTnonneg : 0 ≤ T := (mul_nonneg hg0 hskillc.le).trans hbaseT
  have hTpos : 0 < T := by
    apply lt_of_le_of_ne hTnonneg
    intro hz
    rw [← hz, zero_div, sourceCostAtScore_zero hE.le hpzero (hgm.mono Icc_subset_Ici_self) hg0] at hcostT
    exact (div_pos hrho (sub_pos.mpr hc1)).ne' hcostT.symm
  let L := sourceScoreCostSlopeBound cost production E
  have hL : 0 < L := sourceScoreCostSlopeBound_pos hE.le hpm hgm
  have hfactor : 0 < 1 - psiB / psiA := sub_pos.mpr ((div_lt_one (hB.trans hBA)).mpr hBA)
  have hcanonical := sourceUnitCostEffort_eq hpm hE.le hpE
  have hgEpos : 0 < production E := hg0.trans_lt (hgm (by simp) hE.le hE)
  intro d hd hcd effortD scoreD hscoreD hbestD
  by_cases hdB : d < sourceDisadvantagedRank skill psiA psiB 1
  swap
  · have htheta := sourceDisadvantagedThreshold_eq_one hfcont hf (hB.trans hBA) hB (le_of_not_gt hdB)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro hhigh
    change sourceDisadvantagedThreshold skill psiA psiB d < t at hhigh
    rw [htheta] at hhigh
    exact False.elim ((not_lt_of_ge ht.2) hhigh)
  obtain ⟨F, U, hF, hpF, hbaseU, hcapU, hcostU, hprofileD⟩ :=
    sourceDisadvantagedEquilibrium_boundary_of_sourcePrimitives hrho hd hdB
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreD htie hinj hbestD
  have hFE : F = E := hpm.injOn hF.le hE.le (hpF.trans hpE.symm)
  subst F
  let td := sourceDisadvantagedThreshold skill psiA psiB d
  have htd : td ∈ Icc (0 : ℝ) 1 := sourceDisadvantagedThreshold_mem
  have hd1 : d < 1 := by linarith [hd.2]
  have htheta : tc ≤ td := (monotone_cdf _) hcd
  have hskillcd : psiB * skill tc ≤ psiB * skill td :=
    mul_le_mul_of_nonneg_left (hf.monotoneOn htc htd htheta) hB.le
  have hreward : rho / (1 - c) ≤ rho / (1 - d) :=
    (div_le_div_iff₀ (sub_pos.mpr hc1) (sub_pos.mpr hd1)).mpr (by nlinarith)
  have hTU := sourceBoundaryThreshold_mono hE.le (hpm.mono Icc_subset_Ici_self)
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self) hg0 hskillc hskillcd hreward
    hbaseT hbaseU hcapT hcapU hcostT hcostU
  have hquant := sourceBoundaryThreshold_increment_lower hE.le hpm hpconv.convexOn hgcont hgm hgconc hg0
    hskillc hskillcd hreward hbaseT hbaseU hcapT hcapU hcostT hcostU
  have hqdiff : rho * (d - c) ≤ rho / (1 - d) - rho / (1 - c) := by
    have heq : rho / (1 - d) - rho / (1 - c) = rho * (d - c) / ((1 - c) * (1 - d)) := by
      field_simp [(sub_pos.mpr hc1).ne', (sub_pos.mpr hd1).ne']
      ring
    rw [heq]
    have hden : (1 - c) * (1 - d) ≤ 1 := calc
      _ ≤ 1 * (1 - d) := mul_le_mul_of_nonneg_right (by linarith [hc.1]) (sub_pos.mpr hd1).le
      _ ≤ 1 := by linarith [hd.1]
    apply (le_div_iff₀ (mul_pos (sub_pos.mpr hc1) (sub_pos.mpr hd1))).mpr
    nlinarith [mul_nonneg hrho.le (sub_nonneg.mpr hcd)]
  have hthreshold : (psiB * skill tc) / L * rho * (d - c) ≤ U - T := by
    have h := (mul_le_mul_of_nonneg_left hqdiff (div_pos hskillc hL).le).trans hquant
    simpa only [mul_assoc] using h
  have hadmitC := sourceActualGroupAdmission_of_sourcePrimitives hrho hc (by norm_num)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreC htie hinj hbestC
  have hadmitD := sourceActualGroupAdmission_of_sourcePrimitives hrho hd (by norm_num)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreD htie hinj hbestD
  filter_upwards [hprofileC true, hprofileC false, hprofileD true, hprofileD false,
    hadmitC true, hadmitC false, hadmitD true, hadmitD false,
    sourceTwoGroupMeasure_ae_branch hbestC false, ae_restrict_mem measurableSet_Ioc]
    with t hpCA hpCB hpDA hpDB haCA haCB haDA haDB hbC ht
  intro hhighD
  have hhighC : sourceGroupThreshold skill psiA psiB false c < t := htheta.trans_lt hhighD
  have hhighCA := (sourceGroupThreshold_order (c := c) hfcont hf hf0 hB hBA).trans_lt hhighC
  have hhighDA := (sourceGroupThreshold_order (c := d) hfcont hf hf0 hB hBA).trans_lt hhighD
  have heCA := (hpCA hhighCA).2
  have heCB := (hpCB hhighC).2
  have heDA := (hpDA hhighDA).2
  have heDB := (hpDB hhighD).2
  simp only [Bool.false_eq_true, ↓reduceIte] at heCA heCB heDA heDB
  have hWC : sourceActualGroupWelfareGap cost effortC scoreC tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t =
      sourceCostAtScore cost production E (T / (psiB * skill t)) -
        sourceCostAtScore cost production E (T / (psiA * skill t)) := by
    dsimp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare]
    rw [haCA, haCB, if_pos hhighCA, if_pos hhighC, ← heCA, ← heCB]
    dsimp only [sourceCostAtScore]
    ring
  have hWD : sourceActualGroupWelfareGap cost effortD scoreD tie
      (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t =
      sourceCostAtScore cost production E (U / (psiB * skill t)) -
        sourceCostAtScore cost production E (U / (psiA * skill t)) := by
    dsimp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare]
    rw [haDA, haDB, if_pos hhighDA, if_pos hhighD, ← heDA, ← heDB]
    dsimp only [sourceCostAtScore]
    ring
  have hft : 0 < skill t := hf0.trans_lt (hf (by norm_num) ⟨ht.1.le, ht.2⟩ ht.1)
  have hst : 0 < psiB * skill t := mul_pos hB hft
  have hskill : psiB * skill t < psiA * skill t := mul_lt_mul_of_pos_right hBA hft
  have hgE0 : 0 ≤ production E := hg0.trans (hgm.monotoneOn (by simp) hE.le hE.le)
  have hcap : U / (psiB * skill t) ≤ production E := (div_le_iff₀ hst).mpr (hcapU.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hf.monotoneOn htd ⟨ht.1.le, ht.2⟩ hhighD.le) hB.le) hgE0))
  have hgap := sourceCostAtScore_welfareGap_increment_lower hE.le (hpm.monotoneOn.mono Icc_subset_Ici_self)
    (hpconv.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _)) hpzero
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self)
    (hgconc.subset Icc_subset_Ici_self (convex_Icc _ _)) hg0 hTpos hTU hst hskill.le hcap
  have hratio : (psiB * skill t) / (psiA * skill t) = psiB / psiA := by field_simp
  have hcostCB : sourceCostAtScore cost production E (T / (psiB * skill t)) = cost (effortC (false, t)) :=
    congrArg cost heCB
  rw [hratio, hcostCB] at hgap
  have hcoef : 0 ≤ (1 - psiB / psiA) * cost (effortC (false, t)) / T :=
    div_nonneg (mul_nonneg hfactor.le (hpnonneg _ hbC.1)) hTpos.le
  have hconstant : K t ≤ (1 - psiB / psiA) * cost (effortC (false, t)) / T * (psiB * skill tc) / L * rho := by
    have hratioT : 1 / production E ≤ (psiB * skill tc) / T :=
      (div_le_div_iff₀ hgEpos hTpos).mpr (by nlinarith only [hcapT])
    have hM : 0 ≤ (1 - psiB / psiA) * cost (effortC (false, t)) / L * rho :=
      mul_nonneg (div_nonneg (mul_nonneg hfactor.le (hpnonneg _ hbC.1)) hL.le) hrho.le
    calc
      K t = ((1 - psiB / psiA) * cost (effortC (false, t)) / L * rho) * (1 / production E) := by
        dsimp only [K, sourceGroupGapGrowthRate]
        rw [hcanonical]
        dsimp only [L]
        ring
      _ ≤ ((1 - psiB / psiA) * cost (effortC (false, t)) / L * rho) * ((psiB * skill tc) / T) :=
        mul_le_mul_of_nonneg_left hratioT hM
      _ = _ := by ring
  rw [hWC, hWD, hcostCB]
  calc
    K t * (d - c) ≤
        ((1 - psiB / psiA) * cost (effortC (false, t)) / T * (psiB * skill tc) / L * rho) * (d - c) :=
      mul_le_mul_of_nonneg_right hconstant (sub_nonneg.mpr hcd)
    _ = ((1 - psiB / psiA) * cost (effortC (false, t)) / T) *
        ((psiB * skill tc) / L * rho * (d - c)) := by ring
    _ ≤ ((1 - psiB / psiA) * cost (effortC (false, t)) / T) * (U - T) :=
      mul_le_mul_of_nonneg_left hthreshold hcoef
    _ ≤ _ := hgap

/-- In an actual equilibrium family, a commonly admitted applicant has a
nonnegative welfare-gap derivative wherever that derivative exists, and the
derivative is positive when disadvantaged effort is positive. Only a countable sequence of higher
policies is used, so policy-specific null exception sets need not coincide.
No differentiability of cost, production, or the mixture quantile is assumed. -/
theorem sourceActualGroupWelfareGap_deriv_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score : ℝ → Bool × ℝ → ℝ} {tie : Bool × ℝ → ℝ}
    {psiA psiB rho c b : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hb : b ≤ 1 - rho) (hcb : c < b)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : ∀ d ∈ Icc c b, Measurable (score d))
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ d ∈ Icc c b, ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) (score d) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) x (effort d x)) :
    ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t →
      ∀ v : ℝ,
        HasDerivAt (fun d => sourceActualGroupWelfareGap cost (effort d) (score d) tie
          (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t) v c →
          0 ≤ v ∧ (0 < effort c (false, t) → 0 < v) := by
  have hcI : c ∈ Icc c b := ⟨le_rfl, hcb.le⟩
  obtain ⟨K, _, hKnonneg, hKpos, hK⟩ := sourceActualGroupWelfareGap_quantitative_of_sourcePrimitives hrho hc
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA
    (hscore c hcI) htie hinj (hbest c hcI)
  let d := fun n : ℕ => c + (b - c) / ((n : ℝ) + 2)
  have hd (n : ℕ) : d n ∈ Ioc c b := by
    have hn : 0 < (n : ℝ) + 2 := by positivity
    have hpos := div_pos (sub_pos.mpr hcb) hn
    have hle : (b - c) / ((n : ℝ) + 2) ≤ b - c := (div_le_iff₀ hn).mpr (by
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hdlim : Tendsto d atTop (𝓝 c) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (b - c)).comp (tendsto_add_atTop_nat 2)).const_add c
    simpa only [d, Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, add_zero] using h
  have hdne : Tendsto d atTop (𝓝[≠] c) := tendsto_nhdsWithin_iff.mpr
    ⟨hdlim, Eventually.of_forall (fun n => by simpa only [mem_compl_iff, mem_singleton_iff] using (hd n).1.ne')⟩
  have hcomparisons : ∀ᵐ t ∂unitRankMeasure, ∀ n : ℕ,
      sourceGroupThreshold skill psiA psiB false (d n) < t →
        K t * (d n - c) ≤
          sourceActualGroupWelfareGap cost (effort (d n)) (score (d n)) tie
              (fun i : Fin 2 => sourceTwoLevelCutoff (d n) i) (sourceTwoLevelReward rho (d n)) t -
            sourceActualGroupWelfareGap cost (effort c) (score c) tie
              (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t := by
    rw [ae_all_iff]
    intro n
    exact hK (d n) ⟨hc.1.trans (hd n).1, (hd n).2.trans hb⟩ (hd n).1.le
      (effort (d n)) (score (d n)) (hscore _ ⟨(hd n).1.le, (hd n).2⟩)
      (hbest _ ⟨(hd n).1.le, (hd n).2⟩)
  filter_upwards [hcomparisons, ae_restrict_mem measurableSet_Ioc,
    sourceTwoGroupMeasure_ae_branch (hbest c hcI) false] with t ht htmem htbest
  intro hhigh v hv
  have hrank : c < sourceEnvironmentRank skill psiA psiB (false, t) :=
    (sourceGroupThreshold_lt_iff hfcont hf (hB.trans hBA) hB false htmem).mp hhigh
  have hnear : ∀ᶠ n in atTop, d n < sourceEnvironmentRank skill psiA psiB (false, t) :=
    hdlim.eventually (Iio_mem_nhds hrank)
  let W := fun z => sourceActualGroupWelfareGap cost (effort z) (score z) tie
    (fun i : Fin 2 => sourceTwoLevelCutoff z i) (sourceTwoLevelReward rho z) t
  have hslope : ∀ᶠ n in atTop, K t ≤ slope W c (d n) := by
    filter_upwards [hnear] with n hn
    rw [slope_def_field]
    exact (le_div_iff₀ (sub_pos.mpr (hd n).1)).mpr
      (ht n ((sourceGroupThreshold_lt_iff hfcont hf (hB.trans hBA) hB false htmem).mpr hn))
  have hbound : K t ≤ v := ge_of_tendsto (hv.tendsto_slope.comp hdne) hslope
  refine ⟨(hKnonneg t (hpnonneg _ htbest.1)).trans hbound, ?_⟩
  intro he
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hcost : 0 < cost (effort c (false, t)) := by
    simpa only [hpzero] using hpm (by simp) he.le he
  exact (hKpos t hcost).trans_le hbound

end LBG22StrategicRanking

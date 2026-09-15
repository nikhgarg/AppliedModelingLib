import LBG22StrategicRanking.GroupEndpointPrimitiveRepairs
import Mathlib.Analysis.Calculus.Monotone

/-!+# Canonical group profiles from actual best responses

Boundary indifference identifies the common admitted score threshold with
the source's inverse-cost formula. The resulting clipped welfare-gap
function is a representative of every actual equilibrium in the region
where both groups are admitted. No equilibrium formula is assumed.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory

/-- Inverting the boundary cost equation identifies the threshold itself,
including when zero effort has positive production. -/
theorem sourceBoundaryThreshold_eq_scoreScale
    {cost production : ℝ → ℝ} {E rho c s T : ℝ}
    (hE : 0 ≤ E) (hp : StrictMonoOn cost (Icc 0 E))
    (hg : ContinuousOn production (Icc 0 E)) (hgm : MonotoneOn production (Icc 0 E))
    (hs : 0 < s) (hbase : production 0 * s ≤ T) (hcap : T ≤ production E * s)
    (hcost : sourceCostAtScore cost production E (T / s) = rho / (1 - c)) :
    T = sourceScoreScale cost production E rho c * s := by
  have he := sourceEffortAtScore_spec hE hg hgm ((div_le_iff₀ hs).mpr hcap)
  have hbase' : production 0 ≤ T / s := (le_div_iff₀ hs).mpr hbase
  unfold sourceScoreScale
  rw [← hcost]
  change T = production (effortIntervalInverse cost E (cost (sourceEffortAtScore production E (T / s)))) * s
  have hinverse : effortIntervalInverse cost E (cost (sourceEffortAtScore production E (T / s))) =
      sourceEffortAtScore production E (T / s) := hp.injOn.leftInvOn_invFunOn he.1
  rw [hinverse, he.2, max_eq_left hbase', div_mul_cancel₀ _ hs.ne']

/-- The admitted score threshold determined by the disadvantaged boundary.
Its source interpretation applies below the top of that group's rank
support; it does not select an arbitrary inverse across a mixture gap. -/
noncomputable def sourceCanonicalGroupScoreThreshold
    (cost production skill : ℝ → ℝ) (psiA psiB rho c : ℝ) : ℝ :=
  sourceScoreScale cost production (sourceUnitCostEffort cost) rho c *
    (psiB * skill (sourceDisadvantagedThreshold skill psiA psiB c))

/-- The baseline-clipped cost difference in the common-admission region.
The shared admission reward cancels, leaving the disadvantaged effort cost
minus the advantaged effort cost. -/
noncomputable def sourceCanonicalGroupWelfareGap
    (cost production skill : ℝ → ℝ) (psiA psiB rho t c : ℝ) : ℝ :=
  sourceCostAtScore cost production (sourceUnitCostEffort cost)
      (sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho c / (psiB * skill t)) -
    sourceCostAtScore cost production (sourceUnitCostEffort cost)
      (sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho c / (psiA * skill t))

/-- Every actual two-group equilibrium has the source's canonical admitted
effort and score profiles almost everywhere below the disadvantaged top
rank. The cap and threshold are derived from source primitives. -/
theorem sourceActualGroupProfile_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hcB : c < sourceDisadvantagedRank skill psiA psiB 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x)) :
    ∀ group : Bool, ∀ᵐ t ∂unitRankMeasure,
      sourceGroupThreshold skill psiA psiB group c < t →
        score (group, t) = max (sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho c)
          (production 0 * ((if group then psiA else psiB) * skill t)) ∧
        sourceEffortAtScore production (sourceUnitCostEffort cost)
          (sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho c /
            ((if group then psiA else psiB) * skill t)) = effort (group, t) := by
  obtain ⟨E, T, hE, hpE, hbase, hcap, hcost, hprofile⟩ :=
    sourceDisadvantagedEquilibrium_boundary_of_sourcePrimitives hrho hc hcB
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscore htie hinj hbest
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hcanonical := sourceUnitCostEffort_eq hpm hE.le hpE
  have hc1 : c < 1 := by linarith [hc.2]
  have htheta := sourceDisadvantagedThreshold_mem (skill := skill) (psiA := psiA) (psiB := psiB) (c := c)
  have htheta0 : 0 < sourceDisadvantagedThreshold skill psiA psiB c := hc.1.trans
    (sourceDisadvantagedThreshold_gt_cutoff hfcont hf hf0 hB hBA ⟨hc.1, hc1⟩)
  have hs : 0 < psiB * skill (sourceDisadvantagedThreshold skill psiA psiB c) :=
    mul_pos hB (hf0.trans_lt (hf (by norm_num) htheta htheta0))
  have hT := sourceBoundaryThreshold_eq_scoreScale hE.le (hpm.mono Icc_subset_Ici_self)
    (hgcont.mono Icc_subset_Ici_self) (hgm.monotoneOn.mono Icc_subset_Ici_self) hs hbase hcap hcost
  simpa only [sourceCanonicalGroupScoreThreshold, hcanonical, hT] using hprofile

/-- The explicit cost-difference formula equals actual population welfare
at almost every commonly admitted latent rank, for every feasible policy
and every actual equilibrium. If the disadvantaged group is exhausted,
the common-admission region is null and no inverse across a support gap is
needed. -/
theorem sourceActualGroupWelfareGap_eq_canonical_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x)) :
    ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t →
      sourceActualGroupWelfareGap cost effort score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) t =
          sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t c := by
  by_cases hcB : c < sourceDisadvantagedRank skill psiA psiB 1
  swap
  · have htheta := sourceDisadvantagedThreshold_eq_one hfcont hf (hB.trans hBA) hB (le_of_not_gt hcB)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro hhigh
    change sourceDisadvantagedThreshold skill psiA psiB c < t at hhigh
    rw [htheta] at hhigh
    exact False.elim ((not_lt_of_ge ht.2) hhigh)
  have hprofile := sourceActualGroupProfile_of_sourcePrimitives hrho hc hcB
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscore htie hinj hbest
  have hadmit := sourceActualGroupAdmission_of_sourcePrimitives hrho hc (by norm_num)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscore htie hinj hbest
  filter_upwards [hprofile true, hprofile false, hadmit true, hadmit false] with t hA hBprofile hAr hBr
  intro hhigh
  have hhighA := (sourceGroupThreshold_order (c := c) hfcont hf hf0 hB hBA).trans_lt hhigh
  have heA := (hA hhighA).2
  have heB := (hBprofile hhigh).2
  simp only [Bool.false_eq_true, ↓reduceIte] at heA heB
  dsimp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare]
  rw [hAr, hBr, if_pos hhighA, if_pos hhigh, ← heA, ← heB]
  dsimp only [sourceCanonicalGroupWelfareGap, sourceCostAtScore]
  ring

/-- The canonical threshold is nonnegative, bounded by the derived unit-cost
production at its boundary skill, and nondecreasing in the policy cutoff. -/
theorem sourceCanonicalGroupScoreThreshold_properties
    {cost production skill : ℝ → ℝ} {psiA psiB rho : ℝ}
    (hrho : 0 < rho)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgm : StrictMonoOn production (Ici 0)) (hg0 : 0 ≤ production 0)
    (hf : MonotoneOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) :
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      0 ≤ sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho c ∧
      sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho c ≤
        production (sourceUnitCostEffort cost) *
          (psiB * skill (sourceDisadvantagedThreshold skill psiA psiB c))) ∧
    MonotoneOn (sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho)
      (Ioc (0 : ℝ) (1 - rho)) := by
  have hE := sourceUnitCostEffort_spec hpcont hpconv hpnonneg hpzero
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hscale := sourceScoreScale_mem_and_strictMono hrho hE.1.le
    (hpcont.mono Icc_subset_Ici_self) (hpm.mono Icc_subset_Ici_self) hpzero hE.2
    (hgm.mono Icc_subset_Ici_self)
  have hs (c : ℝ) : 0 ≤ psiB * skill (sourceDisadvantagedThreshold skill psiA psiB c) :=
    mul_nonneg hB.le (hf0.trans (hf (by norm_num) sourceDisadvantagedThreshold_mem
      sourceDisadvantagedThreshold_mem.1))
  constructor
  · intro c hc
    exact ⟨mul_nonneg (hg0.trans (hscale.1 c hc).1.le) (hs c),
      mul_le_mul_of_nonneg_right (hscale.1 c hc).2 (hs c)⟩
  · intro c hc d hd hcd
    exact mul_le_mul (hscale.2.monotoneOn hc hd hcd)
      (mul_le_mul_of_nonneg_left (hf sourceDisadvantagedThreshold_mem sourceDisadvantagedThreshold_mem
        ((monotone_cdf _) hcd)) hB.le) (hs c) (hg0.trans (hscale.1 d hd).1.le)

/-- For a fixed latent rank, the source welfare-gap representative is
nondecreasing throughout the feasible open common-admission interval.
This is pointwise in both the applicant rank and the policy cutoff. -/
theorem sourceCanonicalGroupWelfareGap_monotoneOn
    {cost production skill : ℝ → ℝ} {psiA psiB rho t : ℝ}
    (hrho : 0 < rho) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA) :
    MonotoneOn (sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t)
      (Ioo (0 : ℝ) (min (1 - rho) (sourceDisadvantagedRank skill psiA psiB t))) := by
  have hE := sourceUnitCostEffort_spec hpcont hpconv hpnonneg hpzero
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hprops := sourceCanonicalGroupScoreThreshold_properties (psiA := psiA) hrho
    hpcont hpconv hpnonneg hpzero hgm hg0 hf.monotoneOn hf0 hB
  have hft : 0 < skill t := hf0.trans_lt (hf (by norm_num) ⟨ht.1.le, ht.2⟩ ht.1)
  have hsp : 0 < psiB * skill t := mul_pos hB hft
  have hgE : 0 ≤ production (sourceUnitCostEffort cost) :=
    hg0.trans (hgm.monotoneOn (by simp) hE.1.le hE.1.le)
  intro c hc d hd hcd
  have hcF : c ∈ Ioc (0 : ℝ) (1 - rho) := ⟨hc.1, hc.2.le.trans (min_le_left _ _)⟩
  have hdF : d ∈ Ioc (0 : ℝ) (1 - rho) := ⟨hd.1, hd.2.le.trans (min_le_left _ _)⟩
  have hhigh : sourceDisadvantagedThreshold skill psiA psiB d < t :=
    (sourceGroupThreshold_lt_iff hfcont hf (hB.trans hBA) hB false ht).mpr
      (hd.2.trans_le (min_le_right _ _))
  have hcap : sourceCanonicalGroupScoreThreshold cost production skill psiA psiB rho d /
      (psiB * skill t) ≤ production (sourceUnitCostEffort cost) := by
    apply (div_le_iff₀ hsp).mpr
    exact (hprops.1 d hdF).2.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hf.monotoneOn sourceDisadvantagedThreshold_mem
        ⟨ht.1.le, ht.2⟩ hhigh.le) hB.le) hgE)
  have hgap := sourceCostAtScore_gap_antitone_skill hE.1.le (hpm.monotoneOn.mono Icc_subset_Ici_self)
    (hpconv.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self)
    (hgconc.subset Icc_subset_Ici_self (convex_Icc _ _)) (hprops.1 c hcF).1
    (hprops.2 hcF hdF hcd) hsp (mul_le_mul_of_nonneg_right hBA.le hft.le) hcap
  dsimp only [sourceCanonicalGroupWelfareGap]
  linarith only [hgap]

/-- Without assuming smooth cost, production, skill, or mixture inverses,
the actual-equilibrium welfare-gap representative is differentiable with a
nonnegative derivative at Lebesgue-almost every feasible commonly admitting policy cutoff. The null
set here is in policy space, for each fixed applicant rank. -/
theorem sourceCanonicalGroupWelfareGap_ae_differentiableAt
    {cost production skill : ℝ → ℝ} {psiA psiB rho t : ℝ}
    (hrho : 0 < rho) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA) :
    ∀ᵐ c ∂volume.restrict (Ioo (0 : ℝ) (min (1 - rho) (sourceDisadvantagedRank skill psiA psiB t))),
      DifferentiableAt ℝ (sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t) c ∧
      0 ≤ deriv (sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t) c := by
  have hmono := sourceCanonicalGroupWelfareGap_monotoneOn hrho ht hpcont hpconv hpnonneg hpzero
    hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA
  filter_upwards [hmono.ae_differentiableWithinAt measurableSet_Ioo,
    ae_restrict_mem measurableSet_Ioo] with c hc hmem
  have hnhds := isOpen_Ioo.mem_nhds hmem
  exact ⟨hc.differentiableAt hnhds, by
    rw [← derivWithin_of_mem_nhds hnhds]
    exact hmono.derivWithin_nonneg⟩

end LBG22StrategicRanking

import LBG22StrategicRanking.FiniteUniquenessPrimitiveRepairs

/-!
# Environment-scaled ranks in the actual two-group population

Each group has mass one half and the same uniform latent rank. Scaling its
skill quantile by its environment parameter gives the mixture skill law.
Its CDF, including its constant tails and any gaps between group supports,
defines the environment-scaled rank used in equilibrium reward preservation.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The source population: equal-sized groups, each with uniform latent rank.
The Boolean label `true` denotes group A and `false` denotes group B. -/
noncomputable def sourceTwoGroupMeasure : Measure (Bool × ℝ) :=
  (1 / 2 : ℝ≥0∞) • Measure.map (fun t : ℝ => (true, t)) unitRankMeasure +
    (1 / 2 : ℝ≥0∞) • Measure.map (fun t : ℝ => (false, t)) unitRankMeasure

instance sourceTwoGroupMeasure_isProbabilityMeasure : IsProbabilityMeasure sourceTwoGroupMeasure := by
  have hA : Measurable (fun t : ℝ => (true, t)) := measurable_const.prodMk measurable_id
  have hB : Measurable (fun t : ℝ => (false, t)) := measurable_const.prodMk measurable_id
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hA.aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hB.aemeasurable
  constructor
  simp only [sourceTwoGroupMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  simpa only [one_div] using ENNReal.inv_two_add_inv_two

/-- Pushing the actual group population through an observable gives the
equal-weight mixture of that observable's two conditional laws. -/
theorem sourceTwoGroupMeasure_map {β : Type*} [MeasurableSpace β]
    {observable : Bool × ℝ → β} (hm : Measurable observable) :
    Measure.map observable sourceTwoGroupMeasure =
      (1 / 2 : ℝ≥0∞) • Measure.map (fun t : ℝ => observable (true, t)) unitRankMeasure +
        (1 / 2 : ℝ≥0∞) • Measure.map (fun t : ℝ => observable (false, t)) unitRankMeasure := by
  have hA : Measurable (fun t : ℝ => (true, t)) := measurable_const.prodMk measurable_id
  have hB : Measurable (fun t : ℝ => (false, t)) := measurable_const.prodMk measurable_id
  rw [sourceTwoGroupMeasure, Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.map_map hm hA, Measure.map_map hm hB]
  rfl

theorem sourceTwoGroupMeasure_ae_latent_mem :
    ∀ᵐ x ∂sourceTwoGroupMeasure, x.2 ∈ Ioc (0 : ℝ) 1 := by
  rw [sourceTwoGroupMeasure, ae_add_measure_iff,
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0),
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)]
  have hbranch (b : Bool) : ∀ᵐ x ∂Measure.map (fun t : ℝ => (b, t)) unitRankMeasure,
      x.2 ∈ Ioc (0 : ℝ) 1 := by
    have hm : Measurable (fun t : ℝ => (b, t)) := measurable_const.prodMk measurable_id
    exact (ae_map_iff hm.aemeasurable
      (measurable_snd measurableSet_Ioc)).mpr (ae_restrict_mem measurableSet_Ioc)
  exact ⟨hbranch true, hbranch false⟩

/-- A measurable injection on the actual two-group support has no atoms.
Injectivity of an arbitrary extension outside the population is not needed. -/
theorem noAtoms_map_sourceTwoGroup_of_injOn
    {observable : Bool × ℝ → ℝ} (hm : Measurable observable)
    (hinj : InjOn observable {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    NoAtoms (Measure.map observable sourceTwoGroupMeasure) := by
  have hbranch (b : Bool) : NoAtoms (Measure.map (fun t : ℝ => observable (b, t)) unitRankMeasure) := by
    apply noAtoms_map_tie_of_injOn_unitRank (hm.comp (measurable_const.prodMk measurable_id))
    intro x hx y hy hxy
    exact congrArg Prod.snd (hinj hx hy hxy)
  constructor
  intro r
  rw [sourceTwoGroupMeasure_map hm]
  haveI := hbranch true
  haveI := hbranch false
  simp

/-- Effective skill is latent skill times the group's environment factor.
Endpoint clipping only extends the quantile outside the population support. -/
noncomputable def sourceEnvironmentSkill (skill : ℝ → ℝ) (psiA psiB : ℝ) (x : Bool × ℝ) : ℝ :=
  (if x.1 then psiA else psiB) * sourceClampedSkill skill x.2

theorem sourceEnvironmentSkill_measurable {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hf : ContinuousOn skill (Icc (0 : ℝ) 1)) : Measurable (sourceEnvironmentSkill skill psiA psiB) := by
  exact ((measurable_of_finite (fun b : Bool => if b then psiA else psiB)).comp measurable_fst).mul
    ((continuous_sourceClampedSkill hf).measurable.comp measurable_snd)

/-- The latent skill CDF, rather than an unrestricted algebraic inverse. -/
noncomputable def sourceSkillCDF (skill : ℝ → ℝ) : ℝ → ℝ :=
  cdf (Measure.map (sourceClampedSkill skill) unitRankMeasure)

/-- The CDF of effective skill under the actual two-group population. -/
noncomputable def sourceEnvironmentCDF (skill : ℝ → ℝ) (psiA psiB : ℝ) : ℝ → ℝ :=
  cdf (Measure.map (sourceEnvironmentSkill skill psiA psiB) sourceTwoGroupMeasure)

/-- Environment-scaled pre-effort rank is the mixture CDF at effective skill. -/
noncomputable def sourceEnvironmentRank (skill : ℝ → ℝ) (psiA psiB : ℝ) (x : Bool × ℝ) : ℝ :=
  sourceEnvironmentCDF skill psiA psiB (sourceEnvironmentSkill skill psiA psiB x)

theorem sourceScaledSkillCDF_eq {skill : ℝ → ℝ} {psi : ℝ}
    (hf : ContinuousOn skill (Icc (0 : ℝ) 1)) (hpsi : 0 < psi) (z : ℝ) :
    cdf (Measure.map (fun t => psi * sourceClampedSkill skill t) unitRankMeasure) z =
      sourceSkillCDF skill (z / psi) := by
  have hm := (continuous_sourceClampedSkill hf).measurable
  have hms : Measurable (fun t => psi * sourceClampedSkill skill t) := measurable_const.mul hm
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hm.aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hms.aemeasurable
  have hpre : (fun t => psi * sourceClampedSkill skill t) ⁻¹' Iic z =
      sourceClampedSkill skill ⁻¹' Iic (z / psi) := by
    ext t
    simp only [mem_preimage, mem_Iic, le_div_iff₀ hpsi]
    rw [mul_comm]
  unfold sourceSkillCDF
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply hms measurableSet_Iic, Measure.map_apply hm measurableSet_Iic, hpre]

/-- The source mixture-CDF formula is derived from the equal-sized group
population. It remains valid outside either group's support. -/
theorem sourceEnvironmentCDF_eq_mixture {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hf : ContinuousOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) (z : ℝ) :
    sourceEnvironmentCDF skill psiA psiB z =
      (1 / 2 : ℝ) * sourceSkillCDF skill (z / psiA) +
        (1 / 2 : ℝ) * sourceSkillCDF skill (z / psiB) := by
  have hm := (continuous_sourceClampedSkill hf).measurable
  have hmA : Measurable (fun t => psiA * sourceClampedSkill skill t) := measurable_const.mul hm
  have hmB : Measurable (fun t => psiB * sourceClampedSkill skill t) := measurable_const.mul hm
  have hmE := sourceEnvironmentSkill_measurable (psiA := psiA) (psiB := psiB) hf
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hmA.aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hmB.aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := sourceTwoGroupMeasure) hmE.aemeasurable
  have hmap := sourceTwoGroupMeasure_map hmE
  simp only [sourceEnvironmentSkill, Bool.false_eq_true, ↓reduceIte] at hmap
  have hfinA : ((1 / 2 : ℝ≥0∞) *
      (Measure.map (fun t => psiA * sourceClampedSkill skill t) unitRankMeasure) (Iic z)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)
  have hfinB : ((1 / 2 : ℝ≥0∞) *
      (Measure.map (fun t => psiB * sourceClampedSkill skill t) unitRankMeasure) (Iic z)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)
  unfold sourceEnvironmentCDF
  rw [cdf_eq_real, measureReal_def, hmap, Measure.add_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add hfinA hfinB]
  simp only [ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [← measureReal_def, ← measureReal_def, ← cdf_eq_real, ← cdf_eq_real,
    sourceScaledSkillCDF_eq hf hA, sourceScaledSkillCDF_eq hf hB]

/-- Effective skills are nonatomic even when the two group supports are
disjoint. The source's strictly increasing latent quantile supplies this. -/
theorem noAtoms_map_sourceEnvironmentSkill {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    NoAtoms (Measure.map (sourceEnvironmentSkill skill psiA psiB) sourceTwoGroupMeasure) := by
  have hm := (continuous_sourceClampedSkill hfcont).measurable
  have hbranch (psi : ℝ) (hpsi : 0 < psi) :
      NoAtoms (Measure.map (fun t => psi * sourceClampedSkill skill t) unitRankMeasure) := by
    apply noAtoms_map_tie_of_injOn_unitRank (measurable_const.mul hm)
    intro x hx y hy heq
    dsimp only at heq
    rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩, sourceClampedSkill_eq ⟨hy.1.le, hy.2⟩] at heq
    exact hf.injOn ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ (mul_left_cancel₀ hpsi.ne' heq)
  haveI := hbranch psiA hA
  haveI := hbranch psiB hB
  constructor
  intro z
  rw [sourceTwoGroupMeasure_map (sourceEnvironmentSkill_measurable hfcont)]
  simp only [sourceEnvironmentSkill, Bool.false_eq_true, ↓reduceIte]
  simp

/-- Environment-scaled rank is uniform for the actual mixture population.
No strict-CDF, density, inverse-quantile continuity, or support overlap is
assumed. -/
theorem sourceEnvironmentRank_map_eq_uniform {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    Measure.map (sourceEnvironmentRank skill psiA psiB) sourceTwoGroupMeasure = unitRankMeasure := by
  have hm := sourceEnvironmentSkill_measurable (psiA := psiA) (psiB := psiB) hfcont
  haveI := Measure.isProbabilityMeasure_map (μ := sourceTwoGroupMeasure) hm.aemeasurable
  haveI := noAtoms_map_sourceEnvironmentSkill hfcont hf hA hB
  have h := AppliedModelingLib.Probability.map_cdf_eq_uniform_of_noAtoms
    (Measure.map (sourceEnvironmentSkill skill psiA psiB) sourceTwoGroupMeasure)
  rw [Measure.map_map (monotone_cdf _).measurable hm] at h
  exact h.trans restrict_Ioc_eq_restrict_Icc.symm

/-- Best response under the actual population score and tie-contour rank.
All nonnegative effort deviations are compared with the applicant's current
score and reward, keeping the population distribution fixed. -/
def SourcePopulationFiniteBestResponseAt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (cost production : ℝ → ℝ) (skill score tie : α → ℝ)
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (x : α) (effort : ℝ) : Prop :=
  0 ≤ effort ∧ score x = production effort * skill x ∧
    ∀ d : ℝ, 0 ≤ d →
      reward (finiteLowerRankBand cutoff
        (counterfactualTieBrokenRank μ score tie x (production d * skill x))).val - cost d ≤
      reward (finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)).val - cost effort

/-- Equilibrium preserves reward bands when pre-effort rank is the actual
CDF of nonatomic positive skills. Both rank distributions and the incentive
single-crossing comparison are derived. No inverse skill quantile or
continuity across gaps in its support is required. -/
theorem sourcePopulationFiniteEquilibrium_rank_preservation
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production : ℝ → ℝ} {skill effort score tie : α → ℝ} {baseline : ℝ}
    [NoAtoms (Measure.map skill μ)] [NoAtoms (Measure.map tie μ)]
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hskill : Measurable skill) (hpositive : ∀ᵐ x ∂μ, 0 < skill x)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hscore : Measurable score) (htie : Measurable tie)
    (hbest : ∀ᵐ x ∂μ,
      SourcePopulationFiniteBestResponseAt μ cost production skill score tie cutoff reward x (effort x)) :
    (fun x => finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => finiteLowerRankBand cutoff (cdf (Measure.map skill μ) (skill x))) := by
  let preRank := fun x => cdf (Measure.map skill μ) (skill x)
  let postRank := tieBrokenRank μ score tie
  let level := fun r => (finiteLowerRankBand cutoff r).val
  let R := fun r => reward (level r)
  let good := fun x => 0 < skill x ∧
    SourcePopulationFiniteBestResponseAt μ cost production skill score tie cutoff reward x (effort x)
  have hgood : ∀ᵐ x ∂μ, good x := by
    filter_upwards [hpositive, hbest] with x hx hb
    exact ⟨hx, hb⟩
  have hlevel_mono : Monotone level := fun _ _ hab => finiteLowerRankBand_monotone cutoff hab
  have hlevel_meas : Measurable level := hlevel_mono.measurable
  have hpre_meas : Measurable preRank := (monotone_cdf _).measurable.comp hskill
  have hpost_meas : Measurable postRank := measurable_tieBrokenRank hscore htie
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hskill.aemeasurable
  have hpre : Measure.map preRank μ = volume.restrict (Icc (0 : ℝ) 1) := by
    have h := AppliedModelingLib.Probability.map_cdf_eq_uniform_of_noAtoms (Measure.map skill μ)
    rw [Measure.map_map (monotone_cdf _).measurable hskill] at h
    exact h
  have hpost : Measure.map postRank μ = volume.restrict (Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_noAtoms_tie μ hscore htie
  have hlevels : (fun x => level (postRank x)) =ᵐ[μ] (fun x => level (preRank x)) := by
    refine bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_off_null_and_equal_rank_tail_measures
      (n + 1) preRank postRank level (ae_iff.mp hgood)
      (fun x => (finiteLowerRankBand cutoff (preRank x)).isLt)
      (fun x => (finiteLowerRankBand cutoff (postRank x)).isLt) ?_
      hpre_meas hpost_meas hlevel_meas ?_
    · intro x y hx hy hpre_order hpost_order
      have hxg : good x := not_not.mp hx
      have hyg : good y := not_not.mp hy
      have hsyx : skill y < skill x := by
        by_contra hn
        have h := hlevel_mono ((monotone_cdf (Measure.map skill μ)) (le_of_not_gt hn))
        exact (not_le_of_gt hpre_order) h
      have hrew := sourceBestResponses_reward_mono_skill_of_sourcePrimitives μ score tie y x
        hbaseline hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0
        (monotone_finiteLowerRankReward cutoff hr.monotoneOn) hyg.1 hsyx
        hyg.2.1 hxg.2.1 hyg.2.2.1 hxg.2.2.1 hyg.2.2.2 hxg.2.2.2
      have hstrict := hr
        ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff (postRank x)).isLt⟩
        ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff (postRank y)).isLt⟩ hpost_order
      exact (not_lt_of_ge hrew) hstrict
    · intro l _
      have hs : MeasurableSet {r | l ≤ level r} := hlevel_meas measurableSet_Ici
      have h := congrArg (fun ν : Measure ℝ => ν {r | l ≤ level r}) (hpre.trans hpost.symm)
      dsimp only at h
      rw [Measure.map_apply hpre_meas hs, Measure.map_apply hpost_meas hs] at h
      exact h
  filter_upwards [hlevels] with x hx
  exact Fin.ext hx

theorem sourceEnvironmentSkill_eq_on_support {skill : ℝ → ℝ} {psiA psiB : ℝ} {x : Bool × ℝ}
    (hx : x.2 ∈ Icc (0 : ℝ) 1) :
    sourceEnvironmentSkill skill psiA psiB x = (if x.1 then psiA else psiB) * skill x.2 := by
  unfold sourceEnvironmentSkill
  rw [sourceClampedSkill_eq hx]

theorem sourceEnvironmentSkill_positive_ae {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hA : 0 < psiA) (hB : 0 < psiB) :
    ∀ᵐ x ∂sourceTwoGroupMeasure, 0 < sourceEnvironmentSkill skill psiA psiB x := by
  filter_upwards [sourceTwoGroupMeasure_ae_latent_mem] with x hx
  rw [sourceEnvironmentSkill_eq_on_support ⟨hx.1.le, hx.2⟩]
  have hfpos : 0 < skill x.2 := hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1)
  exact mul_pos (by split <;> assumption) hfpos

/-- Proposition 4.1 for the actual two-group population and arbitrary
measurable-score almost-everywhere equilibria. The mixture-CDF formula,
uniform pre- and post-effort ranks, and reward-band preservation follow
from the source primitives and actual best-response inequalities.

The groups may have disjoint effective-skill supports. Neither an assumed
CDF identity nor a globally continuous inverse mixture quantile is used. -/
theorem sourceEnvironmentEquilibrium_reward_preservation_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {baseline psiA psiB : ℝ} {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hA : 0 < psiA) (hB : 0 < psiB)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hscore : Measurable score) (htie : Measurable tie)
    (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie cutoff reward x (effort x)) :
    (∀ z, sourceEnvironmentCDF skill psiA psiB z =
      (1 / 2 : ℝ) * sourceSkillCDF skill (z / psiA) +
        (1 / 2 : ℝ) * sourceSkillCDF skill (z / psiB)) ∧
    Measure.map (sourceEnvironmentRank skill psiA psiB) sourceTwoGroupMeasure = unitRankMeasure ∧
    Measure.map (tieBrokenRank sourceTwoGroupMeasure score tie) sourceTwoGroupMeasure = unitRankMeasure ∧
    (∀ᵐ x ∂sourceTwoGroupMeasure,
      reward (finiteLowerRankBand cutoff (tieBrokenRank sourceTwoGroupMeasure score tie x)).val =
        reward (finiteLowerRankBand cutoff (sourceEnvironmentRank skill psiA psiB x)).val) := by
  haveI := noAtoms_map_sourceEnvironmentSkill hfcont hf hA hB
  haveI := noAtoms_map_sourceTwoGroup_of_injOn htie hinj
  refine ⟨sourceEnvironmentCDF_eq_mixture hfcont hA hB,
    sourceEnvironmentRank_map_eq_uniform hfcont hf hA hB, ?_, ?_⟩
  · exact (tieBrokenRank_map_eq_uniform_of_noAtoms_tie sourceTwoGroupMeasure hscore htie).trans
      restrict_Ioc_eq_restrict_Icc.symm
  · have h := sourcePopulationFiniteEquilibrium_rank_preservation sourceTwoGroupMeasure cutoff
      hbaseline hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0
      (sourceEnvironmentSkill_measurable hfcont) (sourceEnvironmentSkill_positive_ae hf hf0 hA hB)
      hr hscore htie hbest
    filter_upwards [h] with x hx
    change reward (finiteLowerRankBand cutoff (tieBrokenRank sourceTwoGroupMeasure score tie x)).val =
      reward (finiteLowerRankBand cutoff (cdf (Measure.map (sourceEnvironmentSkill skill psiA psiB)
        sourceTwoGroupMeasure) (sourceEnvironmentSkill skill psiA psiB x))).val
    rw [hx]

/-- On the quantile's actual support, its CDF is its inverse, including
both endpoints. -/
theorem sourceSkillCDF_at_quantile {skill : ℝ → ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceSkillCDF skill (skill t) = t := by
  have hm := (continuous_sourceClampedSkill hfcont).measurable
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hm.aemeasurable
  have hset : (sourceClampedSkill skill ⁻¹' Iic (skill t)) ∩ Ioc (0 : ℝ) 1 = Ioc 0 t := by
    ext x
    constructor
    · rintro ⟨hx, hxmem⟩
      change sourceClampedSkill skill x ≤ skill t at hx
      rw [sourceClampedSkill_eq ⟨hxmem.1.le, hxmem.2⟩] at hx
      exact ⟨hxmem.1, (hf.le_iff_le ⟨hxmem.1.le, hxmem.2⟩ ht).mp hx⟩
    · intro hx
      have hxmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans ht.2⟩
      refine ⟨?_, hxmem⟩
      change sourceClampedSkill skill x ≤ skill t
      rw [sourceClampedSkill_eq ⟨hxmem.1.le, hxmem.2⟩]
      exact hf.monotoneOn ⟨hxmem.1.le, hxmem.2⟩ ht hx.2
  unfold sourceSkillCDF
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hm measurableSet_Iic,
    unitRankMeasure, Measure.restrict_apply (hm measurableSet_Iic), hset, Real.volume_Ioc,
    sub_zero, ENNReal.toReal_ofReal ht.1]

/-- The latent CDF is zero below its support, not an extrapolated inverse. -/
theorem sourceSkillCDF_eq_zero_of_le_bottom {skill : ℝ → ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) {z : ℝ} (hz : z ≤ skill 0) :
    sourceSkillCDF skill z = 0 := by
  apply le_antisymm
  · exact ((monotone_cdf _) hz).trans_eq (sourceSkillCDF_at_quantile hfcont hf (by norm_num))
  · exact cdf_nonneg _ _

/-- The latent CDF is one above its support, not an extrapolated inverse. -/
theorem sourceSkillCDF_eq_one_of_top_le {skill : ℝ → ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) {z : ℝ} (hz : skill 1 ≤ z) :
    sourceSkillCDF skill z = 1 := by
  apply le_antisymm (cdf_le_one _ _)
  have h := (monotone_cdf (Measure.map (sourceClampedSkill skill) unitRankMeasure)) hz
  change sourceSkillCDF skill (skill 1) ≤ sourceSkillCDF skill z at h
  simpa only [sourceSkillCDF_at_quantile hfcont hf (by norm_num : (1 : ℝ) ∈ Icc 0 1)] using h

/-- A score strictly below an interior positive rank's latent skill has
strictly smaller latent CDF. This is local to the actual quantile support. -/
theorem sourceSkillCDF_lt_rank_of_lt_quantile {skill : ℝ → ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) {t z : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) (hz : z < skill t) : sourceSkillCDF skill z < t := by
  by_cases hbottom : z ≤ skill 0
  · rw [sourceSkillCDF_eq_zero_of_le_bottom hfcont hf hbottom]
    exact ht.1
  obtain ⟨q, hq, hqz⟩ := intermediate_value_Icc ht.1.le
    (hfcont.mono (show Icc (0 : ℝ) t ⊆ Icc 0 1 from fun _ h => ⟨h.1, h.2.trans ht.2⟩))
    (show z ∈ Icc (skill 0) (skill t) from ⟨(lt_of_not_ge hbottom).le, hz.le⟩)
  have hqt : q < t := by
    by_contra hn
    have h := hf.monotoneOn ⟨ht.1.le, ht.2⟩ ⟨hq.1, hq.2.trans ht.2⟩ (le_of_not_gt hn)
    rw [hqz] at h
    exact (not_le_of_gt hz) h
  rw [← hqz, sourceSkillCDF_at_quantile hfcont hf ⟨hq.1, hq.2.trans ht.2⟩]
  exact hqt

/-- At equal positive latent rank, group A has strictly higher effective
rank. The proof uses the actual mixture CDF and remains valid for disjoint
group supports and clipped conditional CDF values. -/
theorem sourceEnvironmentRank_group_order {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    sourceEnvironmentRank skill psiA psiB (false, t) < t ∧
      t ≤ sourceEnvironmentRank skill psiA psiB (true, t) ∧
      sourceEnvironmentRank skill psiA psiB (false, t) <
        sourceEnvironmentRank skill psiA psiB (true, t) := by
  have hA := hB.trans hBA
  have hfpos : 0 < skill t := hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  have hlow : psiB * skill t / psiA < skill t := by
    apply (div_lt_iff₀ hA).mpr
    nlinarith
  have hhigh : skill t ≤ psiA * skill t / psiB := by
    apply (le_div_iff₀ hB).mpr
    nlinarith
  have hlowCDF := sourceSkillCDF_lt_rank_of_lt_quantile hfcont hf ht hlow
  have hhighCDF : t ≤ sourceSkillCDF skill (psiA * skill t / psiB) := by
    have h := (monotone_cdf (Measure.map (sourceClampedSkill skill) unitRankMeasure)) hhigh
    change sourceSkillCDF skill (skill t) ≤ sourceSkillCDF skill (psiA * skill t / psiB) at h
    simpa only [sourceSkillCDF_at_quantile hfcont hf ⟨ht.1.le, ht.2⟩] using h
  have hdiagA : psiA * skill t / psiA = skill t := by field_simp
  have hdiagB : psiB * skill t / psiB = skill t := by field_simp
  have hformulaA : sourceEnvironmentRank skill psiA psiB (true, t) =
      (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * sourceSkillCDF skill (psiA * skill t / psiB) := by
    unfold sourceEnvironmentRank
    rw [sourceEnvironmentSkill_eq_on_support ⟨ht.1.le, ht.2⟩,
      sourceEnvironmentCDF_eq_mixture hfcont hA hB]
    simp only [↓reduceIte, hdiagA, sourceSkillCDF_at_quantile hfcont hf ⟨ht.1.le, ht.2⟩]
  have hformulaB : sourceEnvironmentRank skill psiA psiB (false, t) =
      (1 / 2 : ℝ) * sourceSkillCDF skill (psiB * skill t / psiA) + (1 / 2 : ℝ) * t := by
    unfold sourceEnvironmentRank
    rw [sourceEnvironmentSkill_eq_on_support ⟨ht.1.le, ht.2⟩,
      sourceEnvironmentCDF_eq_mixture hfcont hA hB]
    simp only [Bool.false_eq_true, ↓reduceIte, hdiagB, sourceSkillCDF_at_quantile hfcont hf ⟨ht.1.le, ht.2⟩]
  rw [hformulaA, hformulaB]
  constructor
  · linarith
  constructor <;> linarith

/-- Rank-band preservation only needs convex, strictly increasing cost when
the cost minimum is at the lower action boundary. Strict cost convexity,
nonnegative cost levels, and a zero-cost normalization are unnecessary for
this conclusion. This version applies directly to the multidimensional
appendix's increasing cost of endogenous total effort. -/
theorem sourcePopulationFiniteEquilibrium_rank_preservation_of_convex_cost
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production : ℝ → ℝ} {skill effort score tie : α → ℝ}
    [NoAtoms (Measure.map skill μ)] [NoAtoms (Measure.map tie μ)]
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hpM : StrictMonoOn cost (Ici 0))
    (hpconv : ConvexOn ℝ (Ici 0) cost)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hskill : Measurable skill) (hpositive : ∀ᵐ x ∂μ, 0 < skill x)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hscore : Measurable score) (htie : Measurable tie)
    (hbest : ∀ᵐ x ∂μ,
      SourcePopulationFiniteBestResponseAt μ cost production skill score tie cutoff reward x (effort x)) :
    (fun x => finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => finiteLowerRankBand cutoff (cdf (Measure.map skill μ) (skill x))) := by
  let preRank := fun x => cdf (Measure.map skill μ) (skill x)
  let postRank := tieBrokenRank μ score tie
  let level := fun r => (finiteLowerRankBand cutoff r).val
  let R := fun r => reward (level r)
  let good := fun x => 0 < skill x ∧
    SourcePopulationFiniteBestResponseAt μ cost production skill score tie cutoff reward x (effort x)
  have hgood : ∀ᵐ x ∂μ, good x := by
    filter_upwards [hpositive, hbest] with x hx hb
    exact ⟨hx, hb⟩
  have hlevel_mono : Monotone level := fun _ _ hab => finiteLowerRankBand_monotone cutoff hab
  have hlevel_meas : Measurable level := hlevel_mono.measurable
  have hpre_meas : Measurable preRank := (monotone_cdf _).measurable.comp hskill
  have hpost_meas : Measurable postRank := measurable_tieBrokenRank hscore htie
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hskill.aemeasurable
  have hpre : Measure.map preRank μ = volume.restrict (Icc (0 : ℝ) 1) := by
    have h := AppliedModelingLib.Probability.map_cdf_eq_uniform_of_noAtoms (Measure.map skill μ)
    rw [Measure.map_map (monotone_cdf _).measurable hskill] at h
    exact h
  have hpost : Measure.map postRank μ = volume.restrict (Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_noAtoms_tie μ hscore htie
  have hlevels : (fun x => level (postRank x)) =ᵐ[μ] (fun x => level (preRank x)) := by
    refine bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_off_null_and_equal_rank_tail_measures
      (n + 1) preRank postRank level (ae_iff.mp hgood)
      (fun x => (finiteLowerRankBand cutoff (preRank x)).isLt)
      (fun x => (finiteLowerRankBand cutoff (postRank x)).isLt) ?_
      hpre_meas hpost_meas hlevel_meas ?_
    · intro x y hx hy hpre_order hpost_order
      have hxg : good x := not_not.mp hx
      have hyg : good y := not_not.mp hy
      have hsyx : skill y < skill x := by
        by_contra hn
        have h := hlevel_mono ((monotone_cdf (Measure.map skill μ)) (le_of_not_gt hn))
        exact (not_le_of_gt hpre_order) h
      have hrew := sourceBestResponses_reward_mono_skill μ score tie y x
        hpcont hpM hpconv hgcont hgm hgconc hg0
        (monotone_finiteLowerRankReward cutoff hr.monotoneOn) hyg.1 hsyx
        hyg.2.1 hxg.2.1 hyg.2.2.1 hxg.2.2.1 hyg.2.2.2 hxg.2.2.2
      have hstrict := hr
        ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff (postRank x)).isLt⟩
        ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff (postRank y)).isLt⟩ hpost_order
      exact (not_lt_of_ge hrew) hstrict
    · intro l _
      have hs : MeasurableSet {r | l ≤ level r} := hlevel_meas measurableSet_Ici
      have h := congrArg (fun ν : Measure ℝ => ν {r | l ≤ level r}) (hpre.trans hpost.symm)
      dsimp only at h
      rw [Measure.map_apply hpre_meas hs, Measure.map_apply hpost_meas hs] at h
      exact h
  filter_upwards [hlevels] with x hx
  exact Fin.ext hx

end LBG22StrategicRanking

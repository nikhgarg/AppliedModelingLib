import LBG22StrategicRanking.FiniteRankPrimitiveRepairs
import AppliedModelingLib.Foundations.Probability.ProbabilityIntegralTransform

/-!
# Uniformity of population ranks with nonatomic tie keys

The contour-measure construction has a nonatomic rank law when exact
score/tie keys have zero population mass. Its CDF at an applicant's rank
equals that rank, so the nonatomic probability integral transform identifies
the entire rank distribution as uniform.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory

theorem tieBrokenLowerContour_subset_of_mem
    {α : Type*} {score tie : α → ℝ} {x y : α}
    (hxy : x ∈ tieBrokenLowerContour score tie y) :
    tieBrokenLowerContour score tie x ⊆ tieBrokenLowerContour score tie y := by
  rcases hxy with hs | ⟨hs, ht⟩
  · exact tieBrokenLowerContour_subset_of_score_lt hs
  · exact tieBrokenLowerContour_subset_of_same_score_tie_le hs ht

theorem tieBrokenLowerContour_total
    {α : Type*} (score tie : α → ℝ) (x y : α) :
    x ∈ tieBrokenLowerContour score tie y ∨ y ∈ tieBrokenLowerContour score tie x := by
  rcases lt_trichotomy (score x) (score y) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (tie x) (tie y) with ht | ht
    · exact Or.inl (Or.inr ⟨h, ht⟩)
    · exact Or.inr (Or.inr ⟨h.symm, ht⟩)
  · exact Or.inr (Or.inl h)

theorem exactScoreTieKey_of_forward_and_reverse
    {α : Type*} {score tie : α → ℝ} {x y : α}
    (hf : y ∈ tieBrokenLowerContour score tie x)
    (hr : y ∈ tieBrokenLowerContour (fun z => -score z) (fun z => -tie z) x) :
    y ∈ exactScoreTieKey score tie x := by
  rcases hf with hf | ⟨hf, htf⟩ <;> rcases hr with hr | ⟨hr, htr⟩
  · linarith
  · linarith
  · linarith
  · exact ⟨hf, by linarith⟩

theorem measure_eq_zero_of_tieBrokenLowerContour_zero_ae
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (hzero : ∀ᵐ x ∂μ, μ (tieBrokenLowerContour score tie x) = 0) : μ = 0 := by
  by_contra hn
  haveI : NeZero μ := ⟨hn⟩
  obtain ⟨x, hpos, hz⟩ := ((tieBrokenLowerContour_pos_ae μ hscore htie).and hzero).exists
  rw [hz] at hpos
  exact (lt_irrefl _) hpos

/-- Equal-rank applicants cannot have positive population mass when exact
keys are null. A positive prefix of such a fiber would have zero reverse
contours almost everywhere, contradicting contour positivity by Fubini. -/
theorem measure_tieBrokenRank_fiber_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (hkey : ∀ x, μ (exactScoreTieKey score tie x) = 0) (r : ℝ) :
    μ {x | tieBrokenRank μ score tie x = r} = 0 := by
  let A := {x | tieBrokenRank μ score tie x = r}
  have hA : MeasurableSet A := measurableSet_eq_fun (measurable_tieBrokenRank hscore htie) measurable_const
  have hprefix (x : α) (hx : x ∈ A) : μ (A ∩ tieBrokenLowerContour score tie x) = 0 := by
    let B := A ∩ tieBrokenLowerContour score tie x
    have hB : MeasurableSet B := hA.inter (measurableSet_tieBrokenLowerContour hscore htie x)
    have hBzero : μ.restrict B = 0 := by
      apply measure_eq_zero_of_tieBrokenLowerContour_zero_ae _ hscore.neg htie.neg
      filter_upwards [ae_restrict_mem hB] with y hy
      have hsub := tieBrokenLowerContour_subset_of_mem hy.2
      have hmass : μ (tieBrokenLowerContour score tie x) = μ (tieBrokenLowerContour score tie y) := by
        apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
        exact hx.trans hy.1.symm
      have hdiff : μ (tieBrokenLowerContour score tie x \ tieBrokenLowerContour score tie y) = 0 := by
        rw [measure_diff hsub (measurableSet_tieBrokenLowerContour hscore htie y).nullMeasurableSet (measure_ne_top _ _),
          hmass, tsub_self]
      rw [Measure.restrict_apply (measurableSet_tieBrokenLowerContour hscore.neg htie.neg y)]
      apply measure_mono_null (t := (tieBrokenLowerContour score tie x \ tieBrokenLowerContour score tie y) ∪
        exactScoreTieKey score tie y)
      · intro z hz
        by_cases hzy : z ∈ tieBrokenLowerContour score tie y
        · exact Or.inr (exactScoreTieKey_of_forward_and_reverse hzy hz.1)
        · exact Or.inl ⟨hz.2.2, hzy⟩
      · exact measure_union_null hdiff (hkey y)
    simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
      congrArg (fun ν : Measure α => ν univ) hBzero
  have hAzero : μ.restrict A = 0 := by
    apply measure_eq_zero_of_tieBrokenLowerContour_zero_ae _ hscore htie
    filter_upwards [ae_restrict_mem hA] with x hx
    rw [Measure.restrict_apply (measurableSet_tieBrokenLowerContour hscore htie x), inter_comm]
    exact hprefix x hx
  simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
    congrArg (fun ν : Measure α => ν univ) hAzero

theorem noAtoms_map_tieBrokenRank_of_exact_key_null
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (hkey : ∀ x, μ (exactScoreTieKey score tie x) = 0) :
    NoAtoms (Measure.map (tieBrokenRank μ score tie) μ) := by
  constructor
  intro r
  rw [Measure.map_apply (measurable_tieBrokenRank hscore htie) (measurableSet_singleton r)]
  exact measure_tieBrokenRank_fiber_eq_zero μ hscore htie hkey r

/-- The CDF of the rank law fixes every realized rank. Any applicant below
the current rank is in its lower contour; the only possible mismatch is the
null equal-rank fiber. -/
theorem cdf_map_tieBrokenRank_at_rank
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (hkey : ∀ x, μ (exactScoreTieKey score tie x) = 0) (x : α) :
    cdf (Measure.map (tieBrokenRank μ score tie) μ) (tieBrokenRank μ score tie x) =
      tieBrokenRank μ score tie x := by
  have hm := measurable_tieBrokenRank hscore htie (μ := μ)
  haveI : IsProbabilityMeasure (Measure.map (tieBrokenRank μ score tie) μ) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have hne : ∀ᵐ y ∂μ, tieBrokenRank μ score tie y ≠ tieBrokenRank μ score tie x := by
    apply ae_iff.mpr
    simpa only [not_not] using
      measure_tieBrokenRank_fiber_eq_zero μ hscore htie hkey (tieBrokenRank μ score tie x)
  have hsets : (tieBrokenRank μ score tie) ⁻¹' Iic (tieBrokenRank μ score tie x)
      =ᵐ[μ] tieBrokenLowerContour score tie x := by
    filter_upwards [hne] with y hy
    apply propext
    change (tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x) ↔
      y ∈ tieBrokenLowerContour score tie x
    constructor
    · intro hle
      rcases tieBrokenLowerContour_total score tie y x with h | h
      · exact h
      · have hrev : tieBrokenRank μ score tie x ≤ tieBrokenRank μ score tie y := by
          rcases h with hs | ⟨hs, ht⟩
          · exact tieBrokenRank_le_of_score_lt hs
          · exact tieBrokenRank_le_of_same_score_tie_le hs ht
        exact (hy (le_antisymm hle hrev)).elim
    · intro h
      rcases h with hs | ⟨hs, ht⟩
      · exact tieBrokenRank_le_of_score_lt hs
      · exact tieBrokenRank_le_of_same_score_tie_le hs ht
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hm measurableSet_Iic, measure_congr hsets]
  rfl

/-- Measurable scores and tie keys with null exact joint fibers produce
uniform population ranks by the actual contour construction. Score atoms,
flat score intervals, and arbitrary dependence of the tie key are allowed. -/
theorem tieBrokenRank_map_eq_uniform_of_exact_key_null
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (hkey : ∀ x, μ (exactScoreTieKey score tie x) = 0) :
    Measure.map (tieBrokenRank μ score tie) μ = volume.restrict (Icc (0 : ℝ) 1) := by
  let rank := tieBrokenRank μ score tie
  let ν := Measure.map rank μ
  have hm : Measurable rank := measurable_tieBrokenRank hscore htie
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm.aemeasurable
  haveI : NoAtoms ν := noAtoms_map_tieBrokenRank_of_exact_key_null μ hscore htie hkey
  have hfixed : (fun x => cdf ν (rank x)) = rank := by
    funext x
    exact cdf_map_tieBrokenRank_at_rank μ hscore htie hkey x
  have hmap : Measure.map (cdf ν) ν = ν := by
    change Measure.map (cdf ν) (Measure.map rank μ) = Measure.map rank μ
    rw [Measure.map_map (monotone_cdf ν).measurable hm]
    change Measure.map (fun x => cdf ν (rank x)) μ = Measure.map rank μ
    rw [hfixed]
  exact hmap.symm.trans (AppliedModelingLib.Probability.map_cdf_eq_uniform_of_noAtoms ν)

/-- A nonatomic tie-key distribution suffices for the uniform-rank law.
The tie key need not be independent of score or of skill. -/
theorem tieBrokenRank_map_eq_uniform_of_noAtoms_tie
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie μ)] :
    Measure.map (tieBrokenRank μ score tie) μ = volume.restrict (Icc (0 : ℝ) 1) := by
  apply tieBrokenRank_map_eq_uniform_of_exact_key_null μ hscore htie
  intro x
  have hnull : μ (tie ⁻¹' {tie x}) = 0 := by
    rw [← Measure.map_apply htie (measurableSet_singleton _)]
    exact measure_singleton _
  exact measure_mono_null (fun _ h => h.2) hnull

/-- The source's injective measurable tie key on a nonatomic population
constructs uniform ranks, without any separate CDF or reachability premise. -/
theorem tieBrokenRank_map_eq_uniform_of_injective_tie
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NoAtoms μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (htie_inj : Function.Injective tie) :
    Measure.map (tieBrokenRank μ score tie) μ = volume.restrict (Icc (0 : ℝ) 1) :=
  tieBrokenRank_map_eq_uniform_of_exact_key_null μ hscore htie
    (measure_exactScoreTieKey_eq_zero_of_injective_tie htie_inj)

/-- Injectivity is needed only on the actual source population support,
not on an arbitrary extension of the tie key outside the unit interval. -/
theorem noAtoms_map_tie_of_injOn_unitRank
    {tie : ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    NoAtoms (Measure.map tie unitRankMeasure) := by
  constructor
  intro r
  rw [Measure.map_apply htie (measurableSet_singleton r), unitRankMeasure,
    Measure.restrict_apply (htie (measurableSet_singleton r))]
  have hsub : (tie ⁻¹' {r} ∩ Ioc (0 : ℝ) 1).Subsingleton := by
    intro x hx y hy
    exact hinj hx.2 hy.2 (hx.1.trans hy.1.symm)
  exact hsub.measure_zero volume

/-- Away from score atoms, the source counterfactual rank is exactly the
score CDF. The tie-prefix term has zero population mass there. -/
theorem counterfactualTieBrokenRank_eq_cdf_of_score_atom_null
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (x : α) (v : ℝ)
    (hnull : μ {y | score y = v} = 0) :
    counterfactualTieBrokenRank μ score tie x v = cdf (Measure.map score μ) v := by
  haveI : IsProbabilityMeasure (Measure.map score μ) := Measure.isProbabilityMeasure_map hscore.aemeasurable
  have hne : ∀ᵐ y ∂μ, score y ≠ v := by
    apply ae_iff.mpr
    simpa only [not_not] using hnull
  have hsets : {y | score y < v ∨ score y = v ∧ tie y ≤ tie x} =ᵐ[μ] score ⁻¹' Iic v := by
    filter_upwards [hne] with y hy
    apply propext
    change (score y < v ∨ score y = v ∧ tie y ≤ tie x) ↔ score y ≤ v
    simp only [hy, false_and, or_false]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hy⟩
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hscore measurableSet_Iic]
  exact congrArg ENNReal.toReal (measure_congr hsets)

/-- The finite-band source construction gives a measurable equilibrium
profile in the almost-everywhere sense, a uniform post-effort rank distribution,
and best response against all nonnegative efforts under the lower-reward cutoff convention. The
unit-cost cap, all cutoff skills, and rank uniformity are constructed from
the source primitives rather than supplied as equilibrium certificates. -/
theorem exists_sourceFiniteRankEquilibrium_of_sourcePrimitives
    {cost production skill tie : ℝ → ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hcost_cont : ContinuousOn cost (Ici 0))
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hcost_nonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hcost_zero : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hg_mono : StrictMonoOn production (Ici 0))
    (hg_zero : 0 ≤ production 0) (hg_conc : ConcaveOn ℝ (Ici 0) production)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0)
    (hc_top : cutoff (n + 1) = 1) (hf_cont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf_zero : 0 ≤ skill 0)
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1)
    (htie : Measurable tie) (htie_inj : InjOn tie (Ioc (0 : ℝ) 1)) :
    ∃ effortMax : ℝ, 0 < effortMax ∧ cost effortMax = 1 ∧
      let effort := sourceFiniteRankEffort cost production skill effortMax n cutoff reward
      let score := sourceFiniteRankScore cost production skill effortMax n cutoff reward
      let band := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      let rank := fun t d => counterfactualTieBrokenRank unitRankMeasure score tie t
        (production d * skill t)
      AEMeasurable effort unitRankMeasure ∧
      Measure.map (tieBrokenRank unitRankMeasure score tie) unitRankMeasure =
        volume.restrict (Icc (0 : ℝ) 1) ∧
      ∀ᵐ t ∂unitRankMeasure,
        effort t ∈ Icc (0 : ℝ) effortMax ∧ score t = production (effort t) * skill t ∧
        band (rank t (effort t)) = band t ∧
        ∀ d : ℝ, 0 ≤ d → reward (band (rank t d)).val - cost d ≤
          reward (band (rank t (effort t))).val - cost (effort t) := by
  obtain ⟨effortMax, hmax, hcap, hmeas, hbest⟩ :=
    exists_sourceFiniteRankEffort_bestResponseAE_of_sourcePrimitives
      hcost_cont hcost hcost_nonneg hcost_zero hg hg_mono hg_zero hg_conc
      hc hc_zero hc_top hf_cont hf hf_zero hreward hreward_zero hreward_top htie
  haveI := noAtoms_map_tie_of_injOn_unitRank htie htie_inj
  refine ⟨effortMax, hmax, hcap, hmeas, ?_, hbest⟩
  exact tieBrokenRank_map_eq_uniform_of_noAtoms_tie unitRankMeasure
    (measurable_sourceFiniteRankScore hf_cont) htie

/-- A source-admissible tie key that assigns the minimum tie value to the
interior applicant of skill rank `3/4`, by swapping two labels. -/
noncomputable def rankBoundaryInteriorTie : ℝ → ℝ := by
  classical
  exact fun t => Equiv.swap (3 / 4 : ℝ) 0 t

theorem rankBoundaryInteriorTie_measurable : Measurable rankBoundaryInteriorTie := by
  classical
  change Measurable (fun t => Equiv.swap (3 / 4 : ℝ) 0 t)
  simp_rw [Equiv.swap_apply_def]
  exact measurable_const.ite (measurableSet_singleton _) (measurable_const.ite
    (measurableSet_singleton _) measurable_id)

theorem rankBoundaryInteriorTie_injective : Function.Injective rankBoundaryInteriorTie := by
  classical
  exact (Equiv.swap (3 / 4 : ℝ) 0).injective

theorem rankBoundaryInteriorTie_mem_unit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rankBoundaryInteriorTie t ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold rankBoundaryInteriorTie
  rw [Equiv.swap_apply_def]
  split_ifs
  · norm_num
  · norm_num
  · exact ht

/-- An interior applicant first in the high score atom receives the exact
lower cutoff rank, despite injective measurable tie-breaking and a uniform
population rank law. This single-applicant event has zero population mass. -/
theorem rankBoundaryInteriorTie_current_rank :
    counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore rankBoundaryInteriorTie
      (3 / 4) (1 / 2) = 1 / 2 := by
  classical
  let C := {y | rankBoundaryScore y < (1 / 2 : ℝ) ∨
    rankBoundaryScore y = 1 / 2 ∧ rankBoundaryInteriorTie y ≤ rankBoundaryInteriorTie (3 / 4)}
  have htie0 : rankBoundaryInteriorTie (3 / 4) = 0 := by
    simp [rankBoundaryInteriorTie]
  have hlo : Iic (1 / 2 : ℝ) ⊆ C := by
    intro y hy
    change y ≤ 1 / 2 at hy
    left
    rw [rankBoundaryScore_eq, if_pos hy]
    norm_num
  have hhi : C ⊆ Iic (1 / 2 : ℝ) ∪ {3 / 4} := by
    intro y hy
    by_cases hylo : y ≤ 1 / 2
    · exact Or.inl hylo
    · by_cases hyeq : y = 3 / 4
      · exact Or.inr hyeq
      · have hy0 : y ≠ 0 := by linarith
        have htiey : rankBoundaryInteriorTie y = y := by
          simp [rankBoundaryInteriorTie, Equiv.swap_apply_def, hyeq, hy0]
        change rankBoundaryScore y < (1 / 2 : ℝ) ∨
          rankBoundaryScore y = 1 / 2 ∧ rankBoundaryInteriorTie y ≤ rankBoundaryInteriorTie (3 / 4) at hy
        rw [rankBoundaryScore_eq, if_neg hylo, htiey, htie0] at hy
        rcases hy with hy | ⟨_, hy⟩ <;> exfalso <;> linarith
  haveI : NoAtoms unitRankMeasure := inferInstanceAs (NoAtoms (volume.restrict (Ioc (0 : ℝ) 1)))
  have hm : unitRankMeasure C = unitRankMeasure (Iic (1 / 2 : ℝ)) := by
    apply le_antisymm _ (measure_mono hlo)
    calc
      unitRankMeasure C ≤ unitRankMeasure (Iic (1 / 2 : ℝ) ∪ {3 / 4}) := measure_mono hhi
      _ ≤ unitRankMeasure (Iic (1 / 2 : ℝ)) + unitRankMeasure {3 / 4} := measure_union_le _ _
      _ = unitRankMeasure (Iic (1 / 2 : ℝ)) := by rw [measure_singleton, add_zero]
  change (unitRankMeasure C).toReal = 1 / 2
  rw [hm, unitRankMeasure_Iic_half]

/-- The strict-percentile representation need not be a pointwise best
response for every admissible tie key: an exceptional interior applicant in
a score atom can profitably choose zero effort. This does not refute the
author-confirmed stated model, whose equilibrium requirement is almost
everywhere in applicants, not pointwise. -/
theorem rankBoundary_source_profile_pointwise_deviation_lowerBoundary :
    twoLevelAdmissionLowerBoundary rankBoundaryPolicy
      (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore rankBoundaryInteriorTie
        (3 / 4) (rankBoundaryScore (3 / 4))) - (rankBoundaryEffort (3 / 4)) ^ 2 <
    twoLevelAdmissionLowerBoundary rankBoundaryPolicy
      (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore rankBoundaryInteriorTie
        (3 / 4) 0) - (0 : ℝ) ^ 2 := by
  have hscore : rankBoundaryScore (3 / 4) = 1 / 2 := by norm_num [rankBoundaryScore_eq]
  have heffort : rankBoundaryEffort (3 / 4) = 2 / 3 := by norm_num [rankBoundaryEffort]
  have hzeroRank := counterfactualTieBrokenRank_le_cutoff
    (score := rankBoundaryScore) (tie := rankBoundaryInteriorTie) (v := 0)
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (fun y hy => by rw [rankBoundaryScore_eq, if_neg (not_le.mpr hy.1)]; norm_num) (3 / 4)
  rw [hscore, rankBoundaryInteriorTie_current_rank, heffort]
  have hnot : ¬rankBoundaryPolicy.c < counterfactualTieBrokenRank unitRankMeasure
      rankBoundaryScore rankBoundaryInteriorTie (3 / 4) 0 := not_lt_of_ge hzeroRank
  have hnotc : ¬rankBoundaryPolicy.c < (1 / 2 : ℝ) := by norm_num [rankBoundaryPolicy]
  rw [twoLevelAdmissionLowerBoundary, if_neg hnotc,
    twoLevelAdmissionLowerBoundary, if_neg hnot]
  norm_num

theorem rankBoundaryInteriorTie_reward (v : ℝ) :
    twoLevelAdmissionLowerBoundary rankBoundaryPolicy
      (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore rankBoundaryInteriorTie
        (3 / 4) v) = if v ≤ 1 / 2 then 0 else 1 := by
  by_cases hv : v ≤ 1 / 2
  · rw [if_pos hv]
    have hrank : counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore
        rankBoundaryInteriorTie (3 / 4) v ≤ 1 / 2 := by
      rcases lt_or_eq_of_le hv with hlt | rfl
      · apply counterfactualTieBrokenRank_le_cutoff (by norm_num : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1) _ (3 / 4)
        intro y hy
        rw [rankBoundaryScore_eq, if_neg (not_le.mpr hy.1)]
        exact hlt
      · exact rankBoundaryInteriorTie_current_rank.le
    exact if_neg (not_lt_of_ge hrank)
  · rw [if_neg hv]
    have hset : {y | rankBoundaryScore y < v ∨ rankBoundaryScore y = v ∧
        rankBoundaryInteriorTie y ≤ rankBoundaryInteriorTie (3 / 4)} = univ := by
      ext y
      simp only [mem_setOf_eq, mem_univ, iff_true]
      left
      rw [rankBoundaryScore_eq]
      split_ifs <;> linarith
    rw [counterfactualTieBrokenRank, hset, measure_univ, ENNReal.toReal_one]
    norm_num [twoLevelAdmissionLowerBoundary, rankBoundaryPolicy, twoLevelHighProb]

/-- No effort is optimal for the first interior tie-key applicant against
this population. Above the score atom one can reduce effort while retaining
the high reward; at or below it one receives zero and can profitably cross it.
The supremum high-reward payoff is therefore not attained. -/
theorem rankBoundaryInteriorTie_no_bestResponse (d : ℝ) (hd : 0 ≤ d) :
    ∃ d' : ℝ, 0 ≤ d' ∧
      twoLevelAdmissionLowerBoundary rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore rankBoundaryInteriorTie
          (3 / 4) (d * (3 / 4))) - d ^ 2 <
      twoLevelAdmissionLowerBoundary rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore rankBoundaryInteriorTie
          (3 / 4) (d' * (3 / 4))) - d' ^ 2 := by
  by_cases hlow : d ≤ 2 / 3
  · refine ⟨3 / 4, by norm_num, ?_⟩
    rw [rankBoundaryInteriorTie_reward, if_pos (by linarith : d * (3 / 4) ≤ 1 / 2),
      rankBoundaryInteriorTie_reward, if_neg (by norm_num : ¬(3 / 4 : ℝ) * (3 / 4) ≤ 1 / 2)]
    nlinarith [sq_nonneg d]
  · let d' := (d + 2 / 3) / 2
    have hd' : 0 ≤ d' := by dsimp [d']; linarith
    have hlt : d' < d := by dsimp [d']; linarith
    have hscore : ¬d' * (3 / 4) ≤ 1 / 2 := by dsimp [d']; linarith
    refine ⟨d', hd', ?_⟩
    rw [rankBoundaryInteriorTie_reward, if_neg (by linarith : ¬d * (3 / 4) ≤ 1 / 2),
      rankBoundaryInteriorTie_reward, if_neg hscore]
    have hsq := pow_lt_pow_left₀ hlt hd' (by norm_num : (2 : ℕ) ≠ 0)
    linarith

/-- Null changes to the score profile do not alter any counterfactual rank
against that population, with the applicant and tie key fixed. -/
theorem counterfactualTieBrokenRank_congr_score
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {score score' tie : α → ℝ}
    (hscore : score =ᵐ[μ] score') (x : α) (v : ℝ) :
    counterfactualTieBrokenRank μ score tie x v = counterfactualTieBrokenRank μ score' tie x v := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hscore] with y hy
  change (score y < v ∨ score y = v ∧ tie y ≤ tie x) =
    (score' y < v ∨ score' y = v ∧ tie y ≤ tie x)
  rw [hy]

/-- Changing the displayed score profile on a null set cannot restore
pointwise equilibrium for this source-admissible tie key. -/
theorem rankBoundaryInteriorTie_no_bestResponse_of_ae_score
    {score : ℝ → ℝ} (hscore : score =ᵐ[unitRankMeasure] rankBoundaryScore)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ d' : ℝ, 0 ≤ d' ∧
      twoLevelAdmissionLowerBoundary rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure score rankBoundaryInteriorTie
          (3 / 4) (d * (3 / 4))) - d ^ 2 <
      twoLevelAdmissionLowerBoundary rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure score rankBoundaryInteriorTie
          (3 / 4) (d' * (3 / 4))) - d' ^ 2 := by
  obtain ⟨d', hd', hprofit⟩ := rankBoundaryInteriorTie_no_bestResponse d hd
  refine ⟨d', hd', ?_⟩
  rw [counterfactualTieBrokenRank_congr_score hscore, counterfactualTieBrokenRank_congr_score hscore]
  exact hprofit

end LBG22StrategicRanking

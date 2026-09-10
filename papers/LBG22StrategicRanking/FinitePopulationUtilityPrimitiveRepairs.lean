import LBG22StrategicRanking.PopulationUtilityPrimitiveRepairs

/-!
# Finite-band population utility

The actual post-rank reward is averaged over the fixed applicant population.
When equilibrium preserves reward bands, finite-band population integrals
are computed with their actual interval masses, not unweighted band sums.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- The source school's private utility for a finite reward schedule. -/
noncomputable def sourceFiniteSchoolUtility {n : ℕ}
    (score tie : ℝ → ℝ) (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) : ℝ :=
  ∫ t, score t * reward (finiteLowerRankBand cutoff
    (tieBrokenRank unitRankMeasure score tie t)).val ∂unitRankMeasure

theorem finiteLowerRankBand_eq_iff_mem_Ioc {n : ℕ} {cutoff : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0)
    (hcn : cutoff (n + 1) = 1) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin (n + 1)) :
    finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t = i ↔
      t ∈ Ioc (cutoff i.val) (cutoff (i.val + 1)) := by
  constructor
  · intro hi
    have hlo := cutoff_finiteLowerRankBand_lt
      (cutoff := fun j : Fin (n + 1) => cutoff j) (rank := t)
      (by simpa only [Fin.val_zero, hc0] using ht.1)
    rw [hi] at hlo
    refine ⟨hlo, ?_⟩
    by_cases hin : i.val = n
    · simpa only [hin, hcn] using ht.2
    · by_contra hupper
      have hj : i.val + 1 < n + 1 := by have := i.isLt; omega
      have hle := le_finiteLowerRankBand_of_cutoff_lt
        (cutoff := fun j : Fin (n + 1) => cutoff j) (rank := t)
        (i := ⟨i.val + 1, hj⟩) (lt_of_not_ge hupper)
      rw [hi] at hle
      have hv : i.val + 1 ≤ i.val := hle
      omega
  · intro hti
    apply finiteLowerRankBand_eq_of_interval hti.1
    intro j hij
    have hij' : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hij
    exact hti.2.trans (hc.monotoneOn ⟨Nat.zero_le _, by have := i.isLt; omega⟩
      ⟨Nat.zero_le _, Nat.le_of_lt j.isLt⟩ hij')

/-- A function constant on finite rank bands is integrable, and its population
mean uses exactly the band widths. Endpoint tie conventions are respected. -/
theorem integral_finiteLowerRankBand
    {n : ℕ} {cutoff : ℕ → ℝ} (value : Fin (n + 1) → ℝ)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0)
    (hcn : cutoff (n + 1) = 1) :
    Integrable (fun t => value (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t)) unitRankMeasure ∧
    (∫ t, value (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t) ∂unitRankMeasure) =
      ∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) * value i := by
  classical
  let F := fun i : Fin (n + 1) => (Ioc (cutoff i.val) (cutoff (i.val + 1))).indicator (fun _ : ℝ => value i)
  have hi (i : Fin (n + 1)) : Integrable (F i) unitRankMeasure :=
    (integrable_const _).indicator measurableSet_Ioc
  have hsum : Integrable (fun t => ∑ i : Fin (n + 1), F i t) unitRankMeasure :=
    integrable_finset_sum _ (fun i _ => hi i)
  have heq : (fun t => value (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t)) =ᵐ[unitRankMeasure]
      (fun t => ∑ i : Fin (n + 1), F i t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    let j := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t
    have hj : t ∈ Ioc (cutoff j.val) (cutoff (j.val + 1)) :=
      (finiteLowerRankBand_eq_iff_mem_Ioc hc hc0 hcn ht j).mp rfl
    rw [Finset.sum_eq_single j]
    · exact (indicator_of_mem hj (fun _ : ℝ => value j)).symm
    · intro i _ hij
      apply indicator_of_notMem
      intro hti
      have he : j = i := (finiteLowerRankBand_eq_iff_mem_Ioc hc hc0 hcn ht i).mpr hti
      exact hij he.symm
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  refine ⟨hsum.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finset_sum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hc_lo : 0 ≤ cutoff i.val := by
    rw [← hc0]
    exact hc.monotoneOn ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, Nat.le_of_lt i.isLt⟩ (Nat.zero_le _)
  have hc_hi : cutoff (i.val + 1) ≤ 1 := by
    rw [← hcn]
    exact hc.monotoneOn ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩ ⟨Nat.zero_le _, le_rfl⟩
      (Nat.succ_le_of_lt i.isLt)
  have hwidth : 0 ≤ cutoff (i.val + 1) - cutoff i.val := sub_nonneg.mpr
    (hc.monotoneOn ⟨Nat.zero_le _, Nat.le_of_lt i.isLt⟩
      ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩ (Nat.le_succ _))
  dsimp only [F]
  rw [integral_indicator measurableSet_Ioc]
  change (∫ _, value i ∂(volume.restrict (Ioc (0 : ℝ) 1)).restrict
    (Ioc (cutoff i.val) (cutoff (i.val + 1)))) = _
  rw [Measure.restrict_restrict_of_subset (show Ioc (cutoff i.val) (cutoff (i.val + 1)) ⊆ Ioc (0 : ℝ) 1 from
    fun _ ht => ⟨hc_lo.trans_lt ht.1, ht.2.trans hc_hi⟩), integral_const]
  simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal hwidth, smul_eq_mul]

/-- Expected actual admission equals the population-weighted schedule once
reward bands are preserved. Integrability is a proved part of the bridge. -/
theorem sourceFiniteAdmission_integrable_and_mean
    {n : ℕ} {score tie : ℝ → ℝ} {cutoff reward : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0)
    (hcn : cutoff (n + 1) = 1)
    (hband : (fun t => finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank unitRankMeasure score tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)) :
    Integrable (fun t => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie t)).val) unitRankMeasure ∧
    (∫ t, reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie t)).val ∂unitRankMeasure) =
      ∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) * reward i.val := by
  have h := integral_finiteLowerRankBand (fun i : Fin (n + 1) => reward i.val) hc hc0 hcn
  have heq : (fun t => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie t)).val) =ᵐ[unitRankMeasure]
      (fun t => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t).val) := by
    filter_upwards [hband] with t ht
    rw [ht]
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans h.2⟩

/-- With zero baseline production, the constructed score is constant within
each rank band. Actual school utility therefore has a finite weighted sum,
and its integrability does not need to be assumed. -/
theorem sourceFiniteSchoolUtility_eq_sum_of_zero_baseline
    {cost production skill tie : ℝ → ℝ} {E : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0)
    (hcn : cutoff (n + 1) = 1) (hg0 : production 0 = 0)
    (hband : (fun t => finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank unitRankMeasure (sourceFiniteRankScore cost production skill E n cutoff reward) tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)) :
    Integrable (fun t => sourceFiniteRankScore cost production skill E n cutoff reward t *
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank unitRankMeasure (sourceFiniteRankScore cost production skill E n cutoff reward) tie t)).val)
      unitRankMeasure ∧
    sourceFiniteSchoolUtility (sourceFiniteRankScore cost production skill E n cutoff reward) tie
      (fun i : Fin (n + 1) => cutoff i) reward =
      ∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) *
        (max (sourceRecursiveBandScore cost production E (fun k => skill (cutoff k)) reward i.val) 0 * reward i.val) := by
  let T := sourceRecursiveBandScore cost production E (fun k => skill (cutoff k)) reward
  have h := integral_finiteLowerRankBand (fun i : Fin (n + 1) => max (T i.val) 0 * reward i.val) hc hc0 hcn
  have heq : (fun t => sourceFiniteRankScore cost production skill E n cutoff reward t *
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank unitRankMeasure (sourceFiniteRankScore cost production skill E n cutoff reward) tie t)).val) =ᵐ[unitRankMeasure]
      (fun t => max (T (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t).val) 0 *
        reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t).val) := by
    filter_upwards [hband] with t ht
    rw [ht]
    simp only [sourceFiniteRankScore, hg0, zero_mul, T]
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans h.2⟩

/-- At a fixed unit-cost effort cap, the recursive profile is measurable,
feasible, and an actual almost-everywhere equilibrium. -/
theorem sourceFiniteRankEffort_equilibrium_at_unitCost
    {cost production skill tie : ℝ → ℝ} {E : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hE : 0 ≤ E) (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0) (hpE : cost E = 1)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (htie : Measurable tie) :
    let effort := sourceFiniteRankEffort cost production skill E n cutoff reward
    let score := sourceFiniteRankScore cost production skill E n cutoff reward
    AEMeasurable effort unitRankMeasure ∧ Measurable score ∧
    ∀ᵐ t ∂unitRankMeasure, effort t ∈ Icc (0 : ℝ) E ∧
      SourceFiniteBestResponseAt cost production skill score tie (fun i : Fin (n + 1) => cutoff i) reward t (effort t) ∧
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) (tieBrokenRank unitRankMeasure score tie t) =
        finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t := by
  let effort := sourceFiniteRankEffort cost production skill E n cutoff reward
  let score := sourceFiniteRankScore cost production skill E n cutoff reward
  have hb := sourceFiniteRankEffort_bestResponseAE hE (hp.mono Icc_subset_Ici_self)
    (sourceCost_strictMonoOn_of_strictConvex hpC hpN hp0) hp0 hpE
    (hpC.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    (hg.mono Icc_subset_Ici_self) (hgM.mono Icc_subset_Ici_self) hg0
    (hgC.subset Icc_subset_Ici_self (convex_Icc _ _)) hc hc0 hcn hfcont hf hf0 hr hr0 hrn htie
  have hs : Measurable score := measurable_sourceFiniteRankScore hfcont
  have hm : AEMeasurable effort unitRankMeasure :=
    aemeasurable_effort_of_measurable_score hE (hg.mono Icc_subset_Ici_self)
      (hgM.mono Icc_subset_Ici_self) hfcont
      (fun t ht => hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)) hs
      (hb.mono (fun _ ht => ⟨ht.1, ht.2.1⟩))
  refine ⟨hm, hs, ?_⟩
  filter_upwards [hb] with t ht
  have hcur : counterfactualTieBrokenRank unitRankMeasure score tie t (production (effort t) * skill t) =
      tieBrokenRank unitRankMeasure score tie t := by
    rw [← ht.2.1]
    rfl
  refine ⟨ht.1, ⟨ht.1.1, ht.2.1, ?_⟩, ?_⟩
  · intro d hd
    have h := ht.2.2.2 d hd
    change reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t))).val - cost d ≤
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (counterfactualTieBrokenRank unitRankMeasure score tie t (production (effort t) * skill t))).val - cost (effort t) at h
    rwa [hcur] at h
  · have h := ht.2.2.1
    change finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (counterfactualTieBrokenRank unitRankMeasure score tie t (production (effort t) * skill t)) = _ at h
    rwa [hcur] at h

end LBG22StrategicRanking

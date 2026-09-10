import LBG22StrategicRanking.UniquenessPrimitiveRepairs

/-!
# Finite-band effort uniqueness

The thresholds extracted from arbitrary equilibrium bands satisfy the same
adjacent recursion as the constructed profile. The bottom band's zero-cost
effort initializes the recursion; finitely many cutoff applicants are null.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

theorem finiteLowerRankBand_eq_on_open_band {n k : ℕ} {cutoff : ℕ → ℝ} {t : ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hk : k ≤ n)
    (ht : t ∈ Ioo (cutoff k) (cutoff (k + 1))) :
    finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t = ⟨k, Nat.lt_succ_of_le hk⟩ := by
  apply finiteLowerRankBand_eq_of_interval ht.1
  intro j hj
  have hjk : k + 1 ≤ j.val := Nat.succ_le_of_lt hj
  exact ht.2.le.trans (hc.monotoneOn ⟨Nat.zero_le _, by omega⟩
    ⟨Nat.zero_le _, Nat.le_of_lt j.isLt⟩ hjk)

theorem finiteLowerRankBand_mem_open_band {n : ℕ} {cutoff : ℕ → ℝ} {t : ℝ}
    (hc_zero : cutoff 0 = 0) (hc_top : cutoff (n + 1) = 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hne : ∀ k : ℕ, t ≠ cutoff k) :
    let i := finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t
    t ∈ Ioo (cutoff i.val) (cutoff (i.val + 1)) := by
  let i := finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t
  have hlo : cutoff i.val < t := cutoff_finiteLowerRankBand_lt
    (cutoff := fun j : Fin (n + 1) => cutoff j) (rank := t)
    (by simpa only [Fin.val_zero, hc_zero] using ht.1)
  refine ⟨hlo, ?_⟩
  by_cases hilast : i.val = n
  · rw [hilast, hc_top]
    exact lt_of_le_of_ne ht.2 (by simpa only [hc_top] using hne (n + 1))
  · have hi : i.val + 1 < n + 1 := by have := i.isLt; omega
    by_contra hn
    have hcut : cutoff (i.val + 1) < t := lt_of_le_of_ne (le_of_not_gt hn) (hne _).symm
    have h := le_finiteLowerRankBand_of_cutoff_lt
      (cutoff := fun j : Fin (n + 1) => cutoff j) (rank := t) (i := ⟨i.val + 1, hi⟩) hcut
    change (⟨i.val + 1, hi⟩ : Fin (n + 1)) ≤ i at h
    have hv : i.val + 1 ≤ i.val := h
    omega

theorem sourceEffortAtScore_eq_zero_of_le_baseline
    {production : ℝ → ℝ} {E z : ℝ} (hE : 0 ≤ E)
    (hg : StrictMonoOn production (Icc 0 E)) (hz : z ≤ production 0) :
    sourceEffortAtScore production E z = 0 := by
  unfold sourceEffortAtScore
  rw [max_eq_right hz]
  exact hg.injOn.leftInvOn_invFunOn ⟨le_rfl, hE⟩

/-- On the full-measure set of feasible best responders with preserved
reward bands, the adjacent boundary recursion fixes every band effort. -/
theorem sourceFiniteEquilibrium_effort_eq_recursive_on_good_set
    {cost production skill effort score tie : ℝ → ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    {good : Set ℝ} {E : ℝ}
    (hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good) (hE : 0 ≤ E)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0)) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0) (hc_top : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hdata : ∀ t ∈ good, t ∈ Ioc (0 : ℝ) 1 ∧ effort t ∈ Icc (0 : ℝ) E ∧
      SourceFiniteBestResponseAt cost production skill score tie (fun i : Fin (n + 1) => cutoff i) reward t (effort t) ∧
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) (tieBrokenRank unitRankMeasure score tie t) =
        finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t) :
    ∀ k, k ≤ n → ∀ t ∈ Ioo (cutoff k) (cutoff (k + 1)) ∩ good,
      effort t = sourceEffortAtScore production E
        (sourceRecursiveBandScore cost production E (fun j => skill (cutoff j)) reward k / skill t) := by
  let band := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
  let R := fun r => reward (band r).val
  let T := fun k => sourceEquilibriumBandThreshold score good (cutoff k) (cutoff (k + 1))
  let S := sourceRecursiveBandScore cost production E (fun j => skill (cutoff j)) reward
  have hcmem (k : ℕ) (hk : k ≤ n + 1) : cutoff k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hc_zero] using hc.monotoneOn ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hk⟩ (Nat.zero_le k)
    · simpa only [hc_top] using hc.monotoneOn ⟨Nat.zero_le _, hk⟩ ⟨Nat.zero_le _, le_rfl⟩ hk
  have hstepc (k : ℕ) (hk : k ≤ n) : cutoff k < cutoff (k + 1) :=
    hc ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (Nat.lt_succ_self k)
  have hR : Monotone R := monotone_finiteLowerRankReward _ hr.monotoneOn
  have hrew (k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : x ∈ Ioo (cutoff k) (cutoff (k + 1)) ∩ good) :
      R (tieBrokenRank unitRankMeasure score tie x) = reward k := by
    change reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie x)).val = reward k
    rw [(hdata x hx.2).2.2.2, finiteLowerRankBand_eq_on_open_band hc hk hx.1]
  have hprops (k : ℕ) (hk : k ≤ n) :
      0 ≤ T k ∧ production 0 * skill (cutoff k) ≤ T k ∧ T k ≤ production E * skill (cutoff k) ∧
      ∀ x ∈ Ioo (cutoff k) (cutoff (k + 1)) ∩ good,
        score x = max (T k) (production 0 * skill x) ∧ sourceEffortAtScore production E (T k / skill x) = effort x :=
    sourceEquilibriumBandThreshold_properties unitRankMeasure id score tie skill effort hgood
      (hcmem k (by omega)).1 (hcmem (k + 1) (by omega)).2 (hstepc k hk) hE
      hpconv hpnonneg hpzero hg hgm hg0 hR hfcont hf hf0
      (fun x hx => (hdata x hx.2).2.1) (fun x hx => (hdata x hx.2).2.2.1.2.1)
      (hrew k hk) (fun x hx => (hdata x hx.2).2.2.1.2.2)
  have hstep (k : ℕ) (hk : k < n) : T (k + 1) =
      sourceBoundaryStepScore cost production E (T k) (skill (cutoff (k + 1))) (reward (k + 1) - reward k) :=
    sourceEquilibriumBandThreshold_adjacent_recursion score tie skill effort hgood
      (hcmem k (by omega)).1 (hcmem (k + 2) (by omega)).2 (hstepc k (by omega)) (hstepc (k + 1) (by omega))
      hE hpcont hpconv hpnonneg hpzero hg hgm hg0 hR hfcont hf hf0
      (fun x hx => (hdata x hx.2).2.1) (fun x hx => (hdata x hx.2).2.2.1.2.1)
      (hrew k (by omega)) (hrew (k + 1) (by omega)) (fun x hx => (hdata x hx.2).2.2.1.2.2)
  have hbottom (x : ℝ) (hx : x ∈ Ioo (cutoff 0) (cutoff 1) ∩ good) : effort x = 0 := by
    apply sourceBestResponse_bottomReward_effort_eq_baseline unitRankMeasure score tie x
      (cost := cost) (production := production) (reward := R) (skill := skill x)
      (baseline := 0) (by norm_num) hpconv hpnonneg hpzero ?_ (hdata x hx.2).2.1.1
      (hrew 0 (Nat.zero_le _) x hx) (hdata x hx.2).2.2.1.2.2
    intro r
    exact hr.monotoneOn ⟨le_rfl, Nat.zero_le _⟩
      ⟨Nat.zero_le _, Nat.le_of_lt_succ (band r).isLt⟩ (Nat.zero_le _)
  have hzeroProps := sourceEquilibriumBandThreshold_properties unitRankMeasure id score tie skill effort hgood
    (hcmem 0 (by omega)).1 (hcmem 1 (by omega)).2 (hstepc 0 (Nat.zero_le _))
    (E := 0) (by norm_num) hpconv hpnonneg hpzero hg hgm hg0 hR hfcont hf hf0
    (fun x hx => by rw [hbottom x hx]; exact ⟨le_rfl, le_rfl⟩)
    (fun x hx => (hdata x hx.2).2.2.1.2.1) (hrew 0 (Nat.zero_le _))
    (fun x hx => (hdata x hx.2).2.2.1.2.2)
  have hTzero : T 0 = production 0 * skill (cutoff 0) :=
    le_antisymm hzeroProps.2.2.1 (hprops 0 (Nat.zero_le _)).2.1
  have hgM : StrictMonoOn production (Icc 0 E) := hgm.mono Icc_subset_Ici_self
  have hcostzero (k : ℕ) (hk : k ≤ n + 1) (hkpos : 0 < k) :
      sourceCostAtScore cost production E (T 0 / skill (cutoff k)) = 0 := by
    have hck : 0 < cutoff k := by simpa only [hc_zero] using hc ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hk⟩ hkpos
    have hfk : 0 < skill (cutoff k) := hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ (hcmem k hk) hck)
    have hbound : T 0 ≤ production 0 * skill (cutoff k) := by
      rw [hTzero]
      exact mul_le_mul_of_nonneg_left
        (hf.monotoneOn (hcmem 0 (by omega)) (hcmem k hk)
          (hc.monotoneOn ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hk⟩ (Nat.zero_le k))) hg0
    rw [sourceCostAtScore, sourceEffortAtScore_eq_zero_of_le_baseline hE hgM ((div_le_iff₀ hfk).mpr hbound), hpzero]
  have hTeq : ∀ k, k ≤ n → k ≠ 0 → T k = S k := by
    intro k
    induction k with
    | zero => intro _ hn; exact (hn rfl).elim
    | succ k ih =>
      intro hk _
      rw [hstep k (by omega)]
      change sourceBoundaryStepScore cost production E (T k) (skill (cutoff (k + 1))) (reward (k + 1) - reward k) =
        sourceBoundaryStepScore cost production E (S k) (skill (cutoff (k + 1))) (reward (k + 1) - reward k)
      by_cases hk0 : k = 0
      · subst k
        have hC : sourceCostAtScore cost production E (T 0 / skill (cutoff 1)) =
            sourceCostAtScore cost production E (S 0 / skill (cutoff 1)) := by
          rw [hcostzero 1 (by omega) (by omega)]
          change 0 = sourceCostAtScore cost production E (0 / skill (cutoff 1))
          rw [zero_div, sourceCostAtScore, sourceEffortAtScore_zero hE hgM hg0, hpzero]
        unfold sourceBoundaryStepScore sourceBoundaryStepEffort
        rw [hC]
      · rw [ih (by omega) hk0]
  intro k hk t ht
  by_cases hk0 : k = 0
  · subst k
    rw [hbottom t ht]
    change 0 = sourceEffortAtScore production E (0 / skill t)
    rw [zero_div, sourceEffortAtScore_zero hE hgM hg0]
  · change effort t = sourceEffortAtScore production E (S k / skill t)
    rw [← hTeq k hk hk0]
    exact ((hprops k hk).2.2.2 t ht).2.symm

/-- Every almost-everywhere equilibrium agrees with the recursively
constructed source effort profile. Feasibility, rank preservation, threshold
shape, and the adjacent cutoff equations are all derived from primitives. -/
theorem sourceFiniteEquilibrium_effort_unique_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0) (hc_top : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill score tie (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) :
    ∃ E : ℝ, 0 < E ∧ cost E = 1 ∧
      effort =ᵐ[unitRankMeasure] sourceFiniteRankEffort cost production skill E n cutoff reward := by
  obtain ⟨E, hE, hpE, hdataAE⟩ := sourceFiniteEquilibrium_unitCost_bound_of_sourcePrimitives
    (fun i : Fin (n + 1) => cutoff i) hpcont hpconv hpnonneg hpzero hg hgm hgconc hg0
    hf hf0 hr hr0 hrn hscore htie hinj hbest
  let good := {t | t ∈ Ioc (0 : ℝ) 1 ∧ effort t ∈ Icc (0 : ℝ) E ∧
    SourceFiniteBestResponseAt cost production skill score tie (fun i : Fin (n + 1) => cutoff i) reward t (effort t) ∧
    finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) (tieBrokenRank unitRankMeasure score tie t) =
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t}
  have hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good := hdataAE
  have hlocal := sourceFiniteEquilibrium_effort_eq_recursive_on_good_set hgood hE.le
    hpcont hpconv hpnonneg hpzero hg hgm hg0 hc hc_zero hc_top hfcont hf hf0 hr (fun _ ht => ht)
  haveI : NoAtoms unitRankMeasure := inferInstanceAs (NoAtoms (volume.restrict (Ioc (0 : ℝ) 1)))
  have hne : ∀ᵐ t ∂unitRankMeasure, ∀ k : ℕ, t ≠ cutoff k := by
    rw [ae_all_iff]
    exact fun k => unitRankMeasure.ae_ne (cutoff k)
  refine ⟨E, hE, hpE, ?_⟩
  filter_upwards [hgood, hne] with t ht htne
  let i := finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t
  have hband : t ∈ Ioo (cutoff i.val) (cutoff (i.val + 1)) :=
    finiteLowerRankBand_mem_open_band hc_zero hc_top ht.1 htne
  have h := hlocal i.val (Nat.le_of_lt_succ i.isLt) t ⟨hband, ht⟩
  unfold sourceFiniteRankEffort
  rw [sourceClampedSkill_eq ⟨ht.1.1.le, ht.1.2⟩]
  exact h

/-- Effort uniqueness in the source's original units, with an arbitrary
nonnegative cost-minimizing baseline and all nonnegative deviations. -/
theorem sourceFiniteBaselineEquilibrium_effort_unique_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {baseline : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ} (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0) (hc_top : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill score tie (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) :
    ∃ E : ℝ, 0 < E ∧ cost (baseline + E) = 1 ∧
      effort =ᵐ[unitRankMeasure] sourceFiniteBaselineEffort cost production skill baseline E n cutoff reward := by
  let P := fun e => cost (baseline + e)
  let G := fun e => production (baseline + e)
  let shiftedEffort := fun t => effort t - baseline
  have hshift : MapsTo (fun e => baseline + e) (Ici (0 : ℝ)) (Ici 0) := fun _ he => add_nonneg hbaseline he
  have hpc : ContinuousOn P (Ici 0) := hpcont.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hpv : StrictConvexOn ℝ (Ici 0) P := (hpconv.translate_right baseline).subset hshift (convex_Ici _)
  have hpn (e : ℝ) (he : e ∈ Ici (0 : ℝ)) : 0 ≤ P e := hpnonneg _ (hshift he)
  have hpz : P 0 = 0 := by simpa only [P, add_zero] using hpzero
  have hgc : ContinuousOn G (Ici 0) := hg.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hgM : StrictMonoOn G (Ici 0) :=
    fun a ha b hb hab => hgm (hshift ha) (hshift hb) (by dsimp only; linarith)
  have hgC : ConcaveOn ℝ (Ici 0) G := (hgconc.translate_right baseline).subset hshift (convex_Ici _)
  have hgZ : 0 ≤ G 0 := by
    simpa only [G, add_zero] using hg0.trans (hgm.monotoneOn (by simp) hbaseline hbaseline)
  have hR := monotone_finiteLowerRankReward (fun i : Fin (n + 1) => cutoff i) hr.monotoneOn
  have hshiftbest : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt P G skill score tie (fun i : Fin (n + 1) => cutoff i) reward t (shiftedEffort t) := by
    filter_upwards [hbest, ae_restrict_mem measurableSet_Ioc] with t ht htmem
    have hskill : 0 ≤ skill t := hf0.trans
      (hf.monotoneOn ⟨le_rfl, by norm_num⟩ ⟨htmem.1.le, htmem.2⟩ htmem.1.le)
    have hbase := sourceBestResponse_effort_ge_baseline unitRankMeasure score tie t hbaseline hskill
      hgm.monotoneOn hR hpconv hpnonneg hpzero ht.1 ht.2.1 ht.2.2
    have heq : baseline + (effort t - baseline) = effort t := by ring
    refine ⟨sub_nonneg.mpr hbase, ?_, ?_⟩
    · simpa only [G, shiftedEffort, heq] using ht.2.1
    · intro d hd
      simpa only [G, P, shiftedEffort, heq] using ht.2.2 (baseline + d) (add_nonneg hbaseline hd)
  obtain ⟨E, hE, hpE, heq⟩ := sourceFiniteEquilibrium_effort_unique_of_sourcePrimitives
    hpc hpv hpn hpz hgc hgM hgC hgZ hc hc_zero hc_top hfcont hf hf0 hr hr0 hrn hscore htie hinj hshiftbest
  refine ⟨E, hE, hpE, ?_⟩
  filter_upwards [heq] with t ht
  change effort t = baseline + sourceFiniteRankEffort P G skill E n cutoff reward t
  rw [← ht]
  dsimp [shiftedEffort]
  ring

/-- Almost-everywhere existence and uniqueness of the source's finite-band
effort profile under the lower-reward cutoff convention. The cost minimum
may be nonzero, baseline production may be positive, and the tie order is
any measurable injection on the population support. -/
theorem exists_unique_sourceFiniteBaselineEquilibrium_of_sourcePrimitives
    {cost production skill tie : ℝ → ℝ} {baseline : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ} (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0) (hc_top : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    ∃ E : ℝ, 0 < E ∧ cost (baseline + E) = 1 ∧
      let effort := sourceFiniteBaselineEffort cost production skill baseline E n cutoff reward
      let score := sourceFiniteBaselineScore cost production skill baseline E n cutoff reward
      AEMeasurable effort unitRankMeasure ∧ Measurable score ∧
      Measure.map (tieBrokenRank unitRankMeasure score tie) unitRankMeasure = volume.restrict (Icc (0 : ℝ) 1) ∧
      (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
        (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) ∧
      ∀ otherEffort otherScore : ℝ → ℝ, Measurable otherScore →
        (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill otherScore tie
          (fun i : Fin (n + 1) => cutoff i) reward t (otherEffort t)) →
        otherEffort =ᵐ[unitRankMeasure] effort := by
  obtain ⟨E, hE, hpE, hm, hu, hb⟩ := exists_sourceFiniteBaselineEquilibrium_of_sourcePrimitives
    hbaseline hpcont hpconv hpnonneg hpzero hg hgm hg0 hgconc hc hc_zero hc_top hfcont hf hf0 hr hr0 hrn htie hinj
  let effort := sourceFiniteBaselineEffort cost production skill baseline E n cutoff reward
  let score := sourceFiniteBaselineScore cost production skill baseline E n cutoff reward
  have hs : Measurable score := measurable_sourceFiniteRankScore hfcont
  refine ⟨E, hE, hpE, hm, hs, hu, ?_, ?_⟩
  · filter_upwards [hb] with t ht
    have hcur : counterfactualTieBrokenRank unitRankMeasure score tie t (production (effort t) * skill t) =
        tieBrokenRank unitRankMeasure score tie t := by
      rw [← ht.2.1]
      rfl
    refine ⟨hbaseline.trans ht.1.1, ht.2.1, ?_⟩
    intro d hd
    have h := ht.2.2.2 d hd
    change reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t))).val - cost d ≤
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (counterfactualTieBrokenRank unitRankMeasure score tie t (production (effort t) * skill t))).val - cost (effort t) at h
    rwa [hcur] at h
  · intro otherEffort otherScore hotherScore hbest
    obtain ⟨F, hF, hpF, heq⟩ := sourceFiniteBaselineEquilibrium_effort_unique_of_sourcePrimitives
      hbaseline hpcont hpconv hpnonneg hpzero hg hgm hgconc hg0 hc hc_zero hc_top
      hfcont hf hf0 hr hr0 hrn hotherScore htie hinj hbest
    have hpm := sourceCost_strictMonoOn_above_baseline hbaseline hpconv hpnonneg hpzero
    have hcap := hpm.injOn (le_add_of_nonneg_right hF.le) (le_add_of_nonneg_right hE.le) (hpF.trans hpE.symm)
    have hFE : F = E := by linarith
    simpa only [hFE] using heq

end LBG22StrategicRanking

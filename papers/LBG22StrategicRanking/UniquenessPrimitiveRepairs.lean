import LBG22StrategicRanking.IncentivePrimitiveRepairs
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Equilibrium score thresholds from source primitives

Almost-everywhere best responders approach each interior reward cutoff from
both sides. Continuity therefore identifies boundary incentive inequalities
without requiring any null cutoff applicant to best respond.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory Filter
open scoped Topology

/-- A full-measure source population remains dense in every nondegenerate
rank interval, including at its two endpoints. -/
theorem sourceFullMeasure_closure_band {good : Set ℝ} {a b : ℝ}
    (hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    closure (Ioo a b ∩ good) = Icc a b := by
  have hdense : Dense {t : ℝ | t ∈ Ioc (0 : ℝ) 1 → t ∈ good} :=
    Measure.dense_of_ae (μ := volume) (ae_imp_of_ae_restrict hgood)
  have hset : Ioo a b ∩ {t : ℝ | t ∈ Ioc (0 : ℝ) 1 → t ∈ good} = Ioo a b ∩ good := by
    ext t
    constructor
    · rintro ⟨ht, hg⟩
      exact ⟨ht, hg ⟨ha.trans_lt ht.1, ht.2.le.trans hb⟩⟩
    · rintro ⟨ht, hg⟩
      exact ⟨ht, fun _ => hg⟩
  have hsub := hdense.open_subset_closure_inter (isOpen_Ioo (a := a) (b := b))
  rw [hset] at hsub
  apply le_antisymm
  · exact (closure_mono inter_subset_left).trans_eq (closure_Ioo hab.ne)
  · rw [← closure_Ioo hab.ne]
    exact closure_minimal hsub isClosed_closure

/-- Left-band and right-band good applicants jointly approach a cutoff.
The same null exception set may contain the cutoff itself. -/
theorem sourceFullMeasure_cutoff_pair_mem_closure {good : Set ℝ} {a c b : ℝ}
    (hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hac : a < c) (hcb : c < b) :
    (c, c) ∈ closure ((Ioo a c ∩ good) ×ˢ (Ioo c b ∩ good)) := by
  rw [closure_prod_eq, sourceFullMeasure_closure_band hgood ha (hcb.le.trans hb) hac,
    sourceFullMeasure_closure_band hgood (ha.trans hac.le) hb hcb]
  exact ⟨⟨hac.le, le_rfl⟩, ⟨le_rfl, hcb.le⟩⟩

/-- The clipped minimal-effort inverse is continuous on every feasible
production target, including the flat region below baseline production. -/
theorem sourceEffortAtScore_continuousOn
    {production : ℝ → ℝ} {effortMax : ℝ} (hmax : 0 ≤ effortMax)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hgm : StrictMonoOn production (Icc 0 effortMax)) :
    ContinuousOn (sourceEffortAtScore production effortMax) (Iic (production effortMax)) := by
  apply (effortIntervalInverse_continuousOn hmax hg hgm).comp
    (continuous_id.max continuous_const).continuousOn
  intro z hz
  exact ⟨le_max_right _ _, max_le hz
    (hgm.monotoneOn ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax)⟩

theorem sourceCostAtScore_continuousOn
    {cost production : ℝ → ℝ} {effortMax : ℝ} (hmax : 0 ≤ effortMax)
    (hp : ContinuousOn cost (Icc 0 effortMax))
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hgm : StrictMonoOn production (Icc 0 effortMax)) :
    ContinuousOn (sourceCostAtScore cost production effortMax) (Iic (production effortMax)) := by
  apply hp.comp (sourceEffortAtScore_continuousOn hmax hg hgm)
  intro z hz
  exact (sourceEffortAtScore_spec hmax hg hgm.monotoneOn hz).1

/-- Below the upper feasible endpoint, the baseline-clipped cost kernel
is continuous in an ordinary neighborhood of its target. -/
theorem sourceCostAtScore_continuousAt
    {cost production : ℝ → ℝ} {effortMax z : ℝ} (hmax : 0 ≤ effortMax)
    (hp : ContinuousOn cost (Icc 0 effortMax))
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hgm : StrictMonoOn production (Icc 0 effortMax)) (hz : z < production effortMax) :
    ContinuousAt (sourceCostAtScore cost production effortMax) z :=
  (sourceCostAtScore_continuousOn hmax hp hg hgm).continuousAt (Iic_mem_nhds hz)

/-- Best-response inequalities persist at a common accumulation point of
two applicant groups whose scores have continuous extensions. The target
effort is constructed from the technology; matching ties is not assumed
to attain the other group's reward. -/
theorem sourceBestResponse_group_boundary_inequality
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (applicant : ℝ → α) (score tie : α → ℝ) (skill effort : ℝ → ℝ)
    {cost production reward ownScore otherScore : ℝ → ℝ}
    {ownGroup otherGroup : Set ℝ} {c effortMax ownReward otherReward : ℝ}
    (hclosure : (c, c) ∈ closure (ownGroup ×ˢ otherGroup))
    (hmax : 0 ≤ effortMax) (hp : ContinuousOn cost (Ici 0))
    (hg : ContinuousOn production (Icc 0 effortMax)) (hgm : StrictMonoOn production (Ici 0))
    (hr : Monotone reward) (hf : ContinuousAt skill c) (hfpos : 0 < skill c)
    (hown : ContinuousAt ownScore c) (hother : ContinuousAt otherScore c)
    (howncap : ownScore c / skill c < production effortMax)
    (hothercap : otherScore c / skill c < production effortMax)
    (heffort : ∀ x ∈ ownGroup, effort x ∈ Icc (0 : ℝ) effortMax)
    (hactual : ∀ x ∈ ownGroup, score (applicant x) = production (effort x) * skill x)
    (hownscore : ∀ x ∈ ownGroup, score (applicant x) = ownScore x)
    (hotherscore : ∀ x ∈ otherGroup, score (applicant x) = otherScore x)
    (hownreward : ∀ x ∈ ownGroup, reward (tieBrokenRank μ score tie (applicant x)) = ownReward)
    (hotherreward : ∀ x ∈ otherGroup, reward (tieBrokenRank μ score tie (applicant x)) = otherReward)
    (hbest : ∀ x ∈ ownGroup, ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie (applicant x) (production d * skill x)) - cost d ≤
        reward (tieBrokenRank μ score tie (applicant x)) - cost (effort x)) :
    otherReward - sourceCostAtScore cost production effortMax (otherScore c / skill c) ≤
      ownReward - sourceCostAtScore cost production effortMax (ownScore c / skill c) := by
  let C := sourceCostAtScore cost production effortMax
  let F := fun p : ℝ × ℝ => otherReward - C (otherScore p.2 / skill p.1) -
    (ownReward - C (ownScore p.1 / skill p.1))
  have hgM : StrictMonoOn production (Icc 0 effortMax) := hgm.mono Icc_subset_Ici_self
  have hpc : ContinuousOn cost (Icc 0 effortMax) := hp.mono Icc_subset_Ici_self
  have hf1 : ContinuousAt (fun p : ℝ × ℝ => skill p.1) (c, c) := hf.comp continuous_fst.continuousAt
  have hQ : ContinuousAt (fun p : ℝ × ℝ => otherScore p.2 / skill p.1) (c, c) :=
    (hother.comp continuous_snd.continuousAt).div hf1 hfpos.ne'
  have hP : ContinuousAt (fun p : ℝ × ℝ => ownScore p.1 / skill p.1) (c, c) :=
    (hown.comp continuous_fst.continuousAt).div hf1 hfpos.ne'
  have hCQ : ContinuousAt (fun p : ℝ × ℝ => C (otherScore p.2 / skill p.1)) (c, c) :=
    (sourceCostAtScore_continuousAt hmax hpc hg hgM hothercap).comp_of_eq hQ rfl
  have hCP : ContinuousAt (fun p : ℝ × ℝ => C (ownScore p.1 / skill p.1)) (c, c) :=
    (sourceCostAtScore_continuousAt hmax hpc hg hgM howncap).comp_of_eq hP rfl
  have hF : ContinuousAt F (c, c) :=
    (continuousAt_const.sub hCQ).sub (continuousAt_const.sub hCP)
  have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (c, c),
      0 < skill p.1 ∧ otherScore p.2 / skill p.1 < production effortMax :=
    (hf1.eventually (Ioi_mem_nhds hfpos)).and (hQ.eventually (Iio_mem_nhds hothercap))
  have hfreq : ∃ᶠ p in 𝓝 (c, c), F p ≤ 0 := by
    apply ((mem_closure_iff_frequently.mp hclosure).and_eventually hnear).mono
    rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hskill, hcap⟩
    have hi := sourceEffortAtScore_spec hmax hg hgM.monotoneOn hcap.le
    have hreach : score (applicant y) ≤ production (sourceEffortAtScore production effortMax (otherScore y / skill x)) * skill x := by
      rw [hotherscore y hy, hi.2]
      exact (div_le_iff₀ hskill).mp (le_max_left _ _)
    have h := sourceBestResponse_imitation_inequality μ score tie (applicant x) (applicant y) hp hgm hr
      hskill hi.1.1 hreach (hbest x hx)
    rw [hownreward x hx, hotherreward y hy] at h
    have hC : C (ownScore x / skill x) = cost (effort x) := by
      rw [← hownscore x hx, hactual x hx, mul_div_cancel_right₀ _ hskill.ne']
      exact congrArg cost (sourceEffortAtScore_at_production hgM (heffort x hx))
    change otherReward - C (otherScore y / skill x) ≤ ownReward - cost (effort x) at h
    change otherReward - C (otherScore y / skill x) - (ownReward - C (ownScore x / skill x)) ≤ 0
    rw [hC]
    linarith
  have h := le_of_tendsto_of_frequently hF hfreq
  change otherReward - C (otherScore c / skill c) - (ownReward - C (ownScore c / skill c)) ≤ 0 at h
  linarith

/-- Enlarging the auxiliary inverse interval does not change feasible
minimal effort. Both inverses solve the same strictly monotone equation. -/
theorem sourceEffortAtScore_eq_of_caps
    {production : ℝ → ℝ} {E F z : ℝ} (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hgE : ContinuousOn production (Icc 0 E)) (hgF : ContinuousOn production (Icc 0 F))
    (hgm : StrictMonoOn production (Ici 0)) (hzE : z ≤ production E) (hzF : z ≤ production F) :
    sourceEffortAtScore production E z = sourceEffortAtScore production F z := by
  have hiE := sourceEffortAtScore_spec hE hgE (hgm.mono Icc_subset_Ici_self).monotoneOn hzE
  have hiF := sourceEffortAtScore_spec hF hgF (hgm.mono Icc_subset_Ici_self).monotoneOn hzF
  exact hgm.injOn hiE.1.1 hiF.1.1 (hiE.2.trans hiF.2.symm)

/-- The threshold score and its baseline-clipped score have identical
minimal effort cost for a positive skill. -/
theorem sourceCostAtScore_max_baseline {cost production : ℝ → ℝ} {E T f : ℝ} (hf : 0 < f) :
    sourceCostAtScore cost production E (max T (production 0 * f) / f) =
      sourceCostAtScore cost production E (T / f) := by
  rw [← max_div_div_right hf.le, mul_div_cancel_right₀ _ hf.ne']
  simp only [sourceCostAtScore, sourceEffortAtScore, max_self, max_assoc]

/-- Feasibility, the actual score identity, and best response against every
nonnegative effort, with the population score law and tie key held fixed. -/
def SourceFiniteBestResponseAt
    (cost production skill score tie : ℝ → ℝ) {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (t effort : ℝ) : Prop :=
  0 ≤ effort ∧ score t = production effort * skill t ∧
  ∀ d : ℝ, 0 ≤ d →
    reward (finiteLowerRankBand cutoff
      (counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t))).val - cost d ≤
    reward (finiteLowerRankBand cutoff (tieBrokenRank unitRankMeasure score tie t)).val - cost effort

/-- The source primitives construct a common finite effort interval for
an arbitrary equilibrium, together with its almost-everywhere preserved
reward bands. The cap is proved from the reward range, not imposed on actions. -/
theorem sourceFiniteEquilibrium_unitCost_bound_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie cutoff reward t (effort t)) :
    ∃ E : ℝ, 0 < E ∧ cost E = 1 ∧ ∀ᵐ t ∂unitRankMeasure,
      t ∈ Ioc (0 : ℝ) 1 ∧ effort t ∈ Icc (0 : ℝ) E ∧
      SourceFiniteBestResponseAt cost production skill score tie cutoff reward t (effort t) ∧
      finiteLowerRankBand cutoff (tieBrokenRank unitRankMeasure score tie t) = finiteLowerRankBand cutoff t := by
  obtain ⟨E, hE, hpE, hpm⟩ := exists_unitCost_effort_of_sourcePrimitives hpcont hpconv hpnonneg hpzero
  have hpres := sourceFiniteEquilibrium_rank_preservation_of_sourcePrimitives cutoff
    (baseline := 0) (by norm_num) hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0
    hf hf0 hr hscore htie hinj hbest
  let R := fun r => reward (finiteLowerRankBand cutoff r).val
  have hbottom (r : ℝ) : reward 0 ≤ R r := hr.monotoneOn
    ⟨le_rfl, Nat.zero_le _⟩
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff r).isLt⟩ (Nat.zero_le _)
  have htop (r : ℝ) : R r ≤ reward n := hr.monotoneOn
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff r).isLt⟩
    ⟨Nat.zero_le _, le_rfl⟩ (Nat.le_of_lt_succ (finiteLowerRankBand cutoff r).isLt)
  refine ⟨E, hE, hpE, ?_⟩
  filter_upwards [hbest, hpres, ae_restrict_mem measurableSet_Ioc] with t ht hband htmem
  have hcost := sourceBestResponse_cost_le_reward_range unitRankMeasure score tie t
    (baseline := 0) (by norm_num) hpzero hbottom
    (htop (tieBrokenRank unitRankMeasure score tie t)) ht.2.2
  have hupper : effort t ≤ E := by
    by_contra hn
    have h := hpm hE.le ht.1 (lt_of_not_ge hn)
    rw [hpE] at h
    linarith
  exact ⟨htmem, ⟨ht.1, hupper⟩, ht, hband⟩

/-- Adjacent reward bands are indifferent at their common cutoff. Scores
and incentives need hold only on the full-measure set of actual best
responders. A slightly larger inverse interval supplies ordinary continuity,
then inverse uniqueness returns the equation to the original effort cap. -/
theorem sourceBestResponses_adjacent_boundary_cost_gap
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (applicant : ℝ → α) (score tie : α → ℝ) (skill effort : ℝ → ℝ)
    {cost production reward lowScore highScore : ℝ → ℝ}
    {good : Set ℝ} {a c b E lowReward highReward : ℝ}
    (hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hac : a < c) (hcb : c < b)
    (hE : 0 ≤ E) (hp : ContinuousOn cost (Ici 0))
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hr : Monotone reward) (hf : ContinuousAt skill c) (hfpos : 0 < skill c)
    (hlo : ContinuousAt lowScore c) (hhi : ContinuousAt highScore c)
    (hlocap : lowScore c / skill c ≤ production E)
    (hhicap : highScore c / skill c ≤ production E)
    (heffort : ∀ x ∈ Ioo a b ∩ good, effort x ∈ Icc (0 : ℝ) E)
    (hactual : ∀ x ∈ Ioo a b ∩ good, score (applicant x) = production (effort x) * skill x)
    (hloscore : ∀ x ∈ Ioo a c ∩ good, score (applicant x) = lowScore x)
    (hhiscore : ∀ x ∈ Ioo c b ∩ good, score (applicant x) = highScore x)
    (hloreward : ∀ x ∈ Ioo a c ∩ good, reward (tieBrokenRank μ score tie (applicant x)) = lowReward)
    (hhireward : ∀ x ∈ Ioo c b ∩ good, reward (tieBrokenRank μ score tie (applicant x)) = highReward)
    (hbest : ∀ x ∈ Ioo a b ∩ good, ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie (applicant x) (production d * skill x)) - cost d ≤
        reward (tieBrokenRank μ score tie (applicant x)) - cost (effort x)) :
    sourceCostAtScore cost production E (highScore c / skill c) -
      sourceCostAtScore cost production E (lowScore c / skill c) = highReward - lowReward := by
  let F := E + 1
  have hEF : E < F := by dsimp [F]; linarith
  have hF : 0 ≤ F := hE.trans hEF.le
  have hgEF : production E < production F := hgm hE hF hEF
  have hgE : ContinuousOn production (Icc 0 E) := hg.mono Icc_subset_Ici_self
  have hgF : ContinuousOn production (Icc 0 F) := hg.mono Icc_subset_Ici_self
  have hA : Ioo a c ∩ good ⊆ Ioo a b ∩ good :=
    fun _ hx => ⟨⟨hx.1.1, hx.1.2.trans hcb⟩, hx.2⟩
  have hB : Ioo c b ∩ good ⊆ Ioo a b ∩ good :=
    fun _ hx => ⟨⟨hac.trans hx.1.1, hx.1.2⟩, hx.2⟩
  have heF (x : ℝ) (hx : x ∈ Ioo a b ∩ good) : effort x ∈ Icc (0 : ℝ) F :=
    ⟨(heffort x hx).1, (heffort x hx).2.trans hEF.le⟩
  have hclosure := sourceFullMeasure_cutoff_pair_mem_closure hgood ha hb hac hcb
  have hclosure' : (c, c) ∈ closure ((Ioo c b ∩ good) ×ˢ (Ioo a c ∩ good)) := by
    rw [closure_prod_eq] at hclosure ⊢
    exact ⟨hclosure.2, hclosure.1⟩
  have hLH := sourceBestResponse_group_boundary_inequality μ applicant score tie skill effort
    hclosure hF hp hgF hgm hr hf hfpos hlo hhi (hlocap.trans_lt hgEF) (hhicap.trans_lt hgEF)
    (fun x hx => heF x (hA hx)) (fun x hx => hactual x (hA hx)) hloscore hhiscore
    hloreward hhireward (fun x hx => hbest x (hA hx))
  have hHL := sourceBestResponse_group_boundary_inequality μ applicant score tie skill effort
    hclosure' hF hp hgF hgm hr hf hfpos hhi hlo (hhicap.trans_lt hgEF) (hlocap.trans_lt hgEF)
    (fun x hx => heF x (hB hx)) (fun x hx => hactual x (hB hx)) hhiscore hloscore
    hhireward hloreward (fun x hx => hbest x (hB hx))
  have hgap : sourceCostAtScore cost production F (highScore c / skill c) -
      sourceCostAtScore cost production F (lowScore c / skill c) = highReward - lowReward := by linarith
  have hcap (z : ℝ) (hz : z ≤ production E) :
      sourceCostAtScore cost production E z = sourceCostAtScore cost production F z :=
    congrArg cost (sourceEffortAtScore_eq_of_caps hE hF hgE hgF hgm hz (hz.trans hgEF.le))
  rwa [← hcap _ hhicap, ← hcap _ hlocap] at hgap

/-- The lowest score among the full-measure best responders in a band. -/
noncomputable def sourceEquilibriumBandThreshold (score : ℝ → ℝ) (good : Set ℝ) (a b : ℝ) : ℝ :=
  sInf (score '' (Ioo a b ∩ good))

/-- The threshold in an arbitrary common-reward equilibrium band lies in
the feasible range at its lower cutoff. It determines every good applicant's
score and effort through the actual baseline-clipped technology inverse. -/
theorem sourceEquilibriumBandThreshold_properties
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (applicant : ℝ → α) (score tie : α → ℝ) (skill effort : ℝ → ℝ)
    {cost production reward : ℝ → ℝ}
    {good : Set ℝ} {a b E groupReward : ℝ}
    (hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (hE : 0 ≤ E)
    (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hg0 : 0 ≤ production 0) (hr : Monotone reward)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (heffort : ∀ x ∈ Ioo a b ∩ good, effort x ∈ Icc (0 : ℝ) E)
    (hactual : ∀ x ∈ Ioo a b ∩ good, score (applicant x) = production (effort x) * skill x)
    (hequal : ∀ x ∈ Ioo a b ∩ good, reward (tieBrokenRank μ score tie (applicant x)) = groupReward)
    (hbest : ∀ x ∈ Ioo a b ∩ good, ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie (applicant x) (production d * skill x)) - cost d ≤
        reward (tieBrokenRank μ score tie (applicant x)) - cost (effort x)) :
    let T := sourceEquilibriumBandThreshold (score ∘ applicant) good a b
    0 ≤ T ∧ production 0 * skill a ≤ T ∧ T ≤ production E * skill a ∧
    ∀ x ∈ Ioo a b ∩ good,
      score (applicant x) = max T (production 0 * skill x) ∧
      sourceEffortAtScore production E (T / skill x) = effort x := by
  let A := Ioo a b ∩ good
  let T := sourceEquilibriumBandThreshold (score ∘ applicant) good a b
  have hcl : closure A = Icc a b := sourceFullMeasure_closure_band hgood ha hb hab
  have haA : a ∈ closure A := by rw [hcl]; exact ⟨le_rfl, hab.le⟩
  have hA : A.Nonempty := (show (closure A).Nonempty from ⟨a, haA⟩).of_closure
  have ha01 : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.le.trans hb⟩
  have hx01 (x : ℝ) (hx : x ∈ A) : x ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hx.1.1, hx.1.2.le.trans hb⟩
  have hfpos (x : ℝ) (hx : x ∈ A) : 0 < skill x := hf0.trans_lt
    (hf ⟨le_rfl, by norm_num⟩ ⟨(hx01 x hx).1.le, (hx01 x hx).2⟩ (hx01 x hx).1)
  have hscore0 (x : ℝ) (hx : x ∈ A) : 0 ≤ score (applicant x) := by
    rw [hactual x hx]
    exact mul_nonneg (hg0.trans (hgm.monotoneOn (by simp) (heffort x hx).1 (heffort x hx).1))
      (hfpos x hx).le
  have hbdd : BddBelow ((score ∘ applicant) '' A) := ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact hscore0 x hx⟩
  have hT0 : 0 ≤ T := le_csInf (hA.image (score ∘ applicant)) (by rintro _ ⟨x, hx, rfl⟩; exact hscore0 x hx)
  have hTle (x : ℝ) (hx : x ∈ A) : T ≤ score (applicant x) := csInf_le hbdd (mem_image_of_mem (score ∘ applicant) hx)
  have hTbase : production 0 * skill a ≤ T := by
    apply le_csInf (hA.image (score ∘ applicant))
    rintro _ ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [hactual x hx]
    exact (mul_le_mul_of_nonneg_left
      (hf.monotoneOn ha01 ⟨(hx01 x hx).1.le, (hx01 x hx).2⟩ hx.1.1.le) hg0).trans
      (mul_le_mul_of_nonneg_right
        (hgm.monotoneOn (by simp) (heffort x hx).1 (heffort x hx).1) (hfpos x hx).le)
  have hbound (x : ℝ) (hx : x ∈ A) : score (applicant x) ≤ production E * skill x := by
    rw [hactual x hx]
    exact mul_le_mul_of_nonneg_right (hgm.monotoneOn (heffort x hx).1 hE (heffort x hx).2) (hfpos x hx).le
  have hTcap : T ≤ production E * skill a := by
    have hcont : ContinuousAt (fun t => production E * sourceClampedSkill skill t) a :=
      (continuous_const.mul (continuous_sourceClampedSkill hfcont)).continuousAt
    have h := ge_of_tendsto_of_frequently hcont ((mem_closure_iff_frequently.mp haA).mono
      (fun x hx => by
        rw [sourceClampedSkill_eq ⟨(hx01 x hx).1.le, (hx01 x hx).2⟩]
        exact (hTle x hx).trans (hbound x hx)))
    simpa only [sourceClampedSkill_eq ha01] using h
  have hshape (x : ℝ) (hx : x ∈ A) : score (applicant x) = max T (production 0 * skill x) := by
    rcases eq_or_lt_of_le (heffort x hx).1 with he0 | he0
    · have hs : score (applicant x) = production 0 * skill x := by rw [hactual x hx, ← he0]
      rw [← hs, max_eq_right (hTle x hx)]
    · have hlow : score (applicant x) ≤ T := by
        apply le_csInf (hA.image (score ∘ applicant))
        rintro _ ⟨y, hy, rfl⟩
        exact sourceBestResponse_score_le_of_same_reward μ score tie (applicant x) (applicant y)
          (baseline := 0) (by norm_num)
          (sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero)
          hg hr he0 (hactual x hx) ((hequal y hy).trans (hequal x hx).symm) (hbest x hx)
      have hfloor : production 0 * skill x ≤ score (applicant x) := by
        rw [hactual x hx]
        exact mul_le_mul_of_nonneg_right (hgm.monotoneOn (by simp) he0.le he0.le) (hfpos x hx).le
      rw [le_antisymm (hTle x hx) hlow, max_eq_left hfloor]
  refine ⟨hT0, hTbase, hTcap, ?_⟩
  intro x hx
  refine ⟨hshape x hx, ?_⟩
  have hprod : production (effort x) = max (T / skill x) (production 0) := by
    have hs : score (applicant x) = max T (production 0 * skill x) := hshape x hx
    have hdiv : production (effort x) = max T (production 0 * skill x) / skill x := by
      rw [← hs, hactual x hx, mul_div_cancel_right₀ _ (hfpos x hx).ne']
    rwa [← max_div_div_right (hfpos x hx).le, mul_div_cancel_right₀ _ (hfpos x hx).ne'] at hdiv
  have hcap : T / skill x ≤ production E :=
    (div_le_iff₀ (hfpos x hx)).mpr ((hTle x hx).trans (hbound x hx))
  have hi := sourceEffortAtScore_spec hE (hg.mono Icc_subset_Ici_self)
    (hgm.mono Icc_subset_Ici_self).monotoneOn hcap
  exact hgm.injOn hi.1.1 (heffort x hx).1 (hi.2.trans hprod.symm)

/-- A feasible threshold satisfying the adjacent cost equation is exactly
the source's recursively constructed next score. -/
theorem sourceBoundaryStepScore_eq_of_cost_equation
    {cost production : ℝ → ℝ} {E previousScore nextScore cutoffSkill increment : ℝ}
    (hE : 0 ≤ E) (hp : StrictMonoOn cost (Icc 0 E))
    (hg : ContinuousOn production (Icc 0 E)) (hgm : StrictMonoOn production (Icc 0 E))
    (hf : 0 < cutoffSkill) (hfloor : production 0 * cutoffSkill ≤ nextScore)
    (hcap : nextScore / cutoffSkill ≤ production E)
    (heq : sourceCostAtScore cost production E (nextScore / cutoffSkill) =
      sourceCostAtScore cost production E (previousScore / cutoffSkill) + increment) :
    sourceBoundaryStepScore cost production E previousScore cutoffSkill increment = nextScore := by
  have hi := sourceEffortAtScore_spec hE hg hgm.monotoneOn hcap
  unfold sourceBoundaryStepScore sourceBoundaryStepEffort
  rw [← heq]
  change production (effortIntervalInverse cost E
    (cost (sourceEffortAtScore production E (nextScore / cutoffSkill)))) * cutoffSkill = nextScore
  have hpi : effortIntervalInverse cost E (cost (sourceEffortAtScore production E (nextScore / cutoffSkill))) =
      sourceEffortAtScore production E (nextScore / cutoffSkill) := hp.injOn.leftInvOn_invFunOn hi.1
  rw [hpi, hi.2,
    max_eq_left ((le_div_iff₀ hf).mpr hfloor), div_mul_cancel₀ _ hf.ne']

/-- The thresholds extracted from two adjacent equilibrium reward bands
obey the source's next-band recursion. All threshold values, inverse domains,
and boundary incentive equations are derived from the actual best responders. -/
theorem sourceEquilibriumBandThreshold_adjacent_recursion
    (score tie skill effort : ℝ → ℝ) {cost production reward : ℝ → ℝ}
    {good : Set ℝ} {a c b E lowReward highReward : ℝ}
    (hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hac : a < c) (hcb : c < b) (hE : 0 ≤ E)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hg0 : 0 ≤ production 0) (hr : Monotone reward)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (heffort : ∀ x ∈ Ioo a b ∩ good, effort x ∈ Icc (0 : ℝ) E)
    (hactual : ∀ x ∈ Ioo a b ∩ good, score x = production (effort x) * skill x)
    (hloreward : ∀ x ∈ Ioo a c ∩ good, reward (tieBrokenRank unitRankMeasure score tie x) = lowReward)
    (hhireward : ∀ x ∈ Ioo c b ∩ good, reward (tieBrokenRank unitRankMeasure score tie x) = highReward)
    (hbest : ∀ x ∈ Ioo a b ∩ good, ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank unitRankMeasure score tie x (production d * skill x)) - cost d ≤
        reward (tieBrokenRank unitRankMeasure score tie x) - cost (effort x)) :
    sourceEquilibriumBandThreshold score good c b =
      sourceBoundaryStepScore cost production E (sourceEquilibriumBandThreshold score good a c)
        (skill c) (highReward - lowReward) := by
  let L := sourceEquilibriumBandThreshold score good a c
  let H := sourceEquilibriumBandThreshold score good c b
  have hA : Ioo a c ∩ good ⊆ Ioo a b ∩ good :=
    fun _ hx => ⟨⟨hx.1.1, hx.1.2.trans hcb⟩, hx.2⟩
  have hB : Ioo c b ∩ good ⊆ Ioo a b ∩ good :=
    fun _ hx => ⟨⟨hac.trans hx.1.1, hx.1.2⟩, hx.2⟩
  have hL := sourceEquilibriumBandThreshold_properties unitRankMeasure id score tie skill effort
    hgood ha (hcb.le.trans hb) hac hE hpconv hpnonneg hpzero hg hgm hg0 hr hfcont hf hf0
    (fun x hx => heffort x (hA hx)) (fun x hx => hactual x (hA hx)) hloreward
    (fun x hx => hbest x (hA hx))
  have hH := sourceEquilibriumBandThreshold_properties unitRankMeasure id score tie skill effort
    hgood (ha.trans hac.le) hb hcb hE hpconv hpnonneg hpzero hg hgm hg0 hr hfcont hf hf0
    (fun x hx => heffort x (hB hx)) (fun x hx => hactual x (hB hx)) hhireward
    (fun x hx => hbest x (hB hx))
  have hc0 : 0 < c := ha.trans_lt hac
  have hc1 : c < 1 := hcb.trans_le hb
  have hfc : ContinuousAt skill c := hfcont.continuousAt (Icc_mem_nhds hc0 hc1)
  have hfcpos : 0 < skill c := hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨hc0.le, hc1.le⟩ hc0)
  have hg0E : production 0 ≤ production E := hgm.monotoneOn (by simp) hE hE
  have hLcap : L ≤ production E * skill c := hL.2.2.1.trans
    (mul_le_mul_of_nonneg_left
      (hf.monotoneOn ⟨ha, hac.le.trans hc1.le⟩ ⟨hc0.le, hc1.le⟩ hac.le) (hg0.trans hg0E))
  have hHcap : H ≤ production E * skill c := hH.2.2.1
  have hfloorcap : production 0 * skill c ≤ production E * skill c :=
    mul_le_mul_of_nonneg_right hg0E hfcpos.le
  have hLC : ContinuousAt (fun t => max L (production 0 * skill t)) c :=
    continuousAt_const.max (continuousAt_const.mul hfc)
  have hHC : ContinuousAt (fun t => max H (production 0 * skill t)) c :=
    continuousAt_const.max (continuousAt_const.mul hfc)
  have hgap := sourceBestResponses_adjacent_boundary_cost_gap unitRankMeasure id score tie skill effort
    hgood ha hb hac hcb hE hpcont hg hgm hr hfc hfcpos hLC hHC
    ((div_le_iff₀ hfcpos).mpr (max_le hLcap hfloorcap))
    ((div_le_iff₀ hfcpos).mpr (max_le hHcap hfloorcap))
    heffort hactual (fun x hx => (hL.2.2.2 x hx).1) (fun x hx => (hH.2.2.2 x hx).1)
    hloreward hhireward hbest
  change sourceCostAtScore cost production E (max H (production 0 * skill c) / skill c) -
    sourceCostAtScore cost production E (max L (production 0 * skill c) / skill c) = highReward - lowReward at hgap
  rw [sourceCostAtScore_max_baseline hfcpos, sourceCostAtScore_max_baseline hfcpos] at hgap
  have heq : sourceCostAtScore cost production E (H / skill c) =
      sourceCostAtScore cost production E (L / skill c) + (highReward - lowReward) := by linarith
  exact (sourceBoundaryStepScore_eq_of_cost_equation hE
    ((sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero).mono Icc_subset_Ici_self)
    (hg.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self)
    hfcpos hH.2.1 ((div_le_iff₀ hfcpos).mpr hHcap) heq).symm

end LBG22StrategicRanking

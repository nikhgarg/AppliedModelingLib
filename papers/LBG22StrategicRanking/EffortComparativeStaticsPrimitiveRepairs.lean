import LBG22StrategicRanking.FiniteUniquenessPrimitiveRepairs

/-!
# Effort comparative statics from the finite equilibrium recursion

A transfer of reward from a higher band to a lower band increases the lower
band's score threshold and decreases the intervening thresholds. Convexity
of effort cost and concavity of production control the change in the next
band's imitation cost, including clipping at positive baseline production.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- A band's score threshold depends only on the rewards up to that band. -/
theorem sourceRecursiveBandScore_congr_rewards
    (cost production : ℝ → ℝ) (effortMax : ℝ) (cutoffSkill reward newReward : ℕ → ℝ)
    (i : ℕ) (heq : ∀ l ≤ i, newReward l = reward l) :
    sourceRecursiveBandScore cost production effortMax cutoffSkill newReward i =
      sourceRecursiveBandScore cost production effortMax cutoffSkill reward i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [sourceRecursiveBandScore]
    rw [ih (fun l hl => heq l (by omega)), heq (i + 1) le_rfl, heq i (by omega)]

/-- Transferring reward from band `j` to band `k < j` leaves all earlier
thresholds unchanged, raises threshold `k` (strictly unless it is the bottom
band), and weakly lowers thresholds `k+1` through `j`. The first and last of
these decreasing thresholds fall strictly. Both reward schedules are valid;
no differentiability or zero-production-baseline assumption is needed. -/
theorem sourceRecursiveBandScore_reward_transfer
    {cost production : ℝ → ℝ} {effortMax : ℝ} {n k j : ℕ}
    {cutoffSkill reward newReward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hpcont : ContinuousOn cost (Icc 0 effortMax))
    (hp : StrictMonoOn cost (Icc 0 effortMax))
    (hp0 : cost 0 = 0) (hpmax : cost effortMax = 1)
    (hpconv : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hgm : StrictMonoOn production (Icc 0 effortMax)) (hg0 : 0 ≤ production 0)
    (hgconc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hskill : ∀ i ∈ Icc (1 : ℕ) n, 0 < cutoffSkill i)
    (hskill_mono : StrictMonoOn cutoffSkill (Icc (1 : ℕ) n))
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hr' : StrictMonoOn newReward (Icc (0 : ℕ) n)) (hr0' : 0 ≤ newReward 0) (hrn' : newReward n ≤ 1)
    (hkj : k < j) (hjn : j ≤ n)
    (hk : reward k < newReward k) (hj : newReward j < reward j)
    (heq : ∀ i ≤ n, i ≠ k → i ≠ j → newReward i = reward i) :
    let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
    let U := sourceRecursiveBandScore cost production effortMax cutoffSkill newReward
    (∀ i, i < k → U i = T i) ∧ T k ≤ U k ∧ (0 < k → T k < U k) ∧
      (∀ i, k < i → i ≤ j → U i ≤ T i) ∧ U (k + 1) < T (k + 1) ∧ U j < T j := by
  let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
  let U := sourceRecursiveBandScore cost production effortMax cutoffSkill newReward
  let C := sourceCostAtScore cost production effortMax
  have hT := sourceRecursiveBandScore_properties hmax hpcont hp hp0 hpmax
    hg hgm hg0 hskill hskill_mono.monotoneOn hr hr0 hrn
  have hU := sourceRecursiveBandScore_properties hmax hpcont hp hp0 hpmax
    hg hgm hg0 hskill hskill_mono.monotoneOn hr' hr0' hrn'
  have hCm := sourceCostAtScore_monotoneOn hmax hp.monotoneOn hg hgm
  have hCs := sourceCostAtScore_strictMonoOn_feasible hmax hp hg hgm
  have hTm (i : ℕ) (hi : i < n) : T (i + 1) / cutoffSkill (i + 1) ∈
      Icc (production 0) (production effortMax) := by
    have hs := hskill (i + 1) ⟨by omega, by omega⟩
    exact ⟨(le_div_iff₀ hs).mpr ((le_max_right _ _).trans (hT i hi).1.le),
      (div_le_iff₀ hs).mpr (hT i hi).2.1⟩
  have hUm (i : ℕ) (hi : i < n) : U (i + 1) / cutoffSkill (i + 1) ∈
      Icc (production 0) (production effortMax) := by
    have hs := hskill (i + 1) ⟨by omega, by omega⟩
    exact ⟨(le_div_iff₀ hs).mpr ((le_max_right _ _).trans (hU i hi).1.le),
      (div_le_iff₀ hs).mpr (hU i hi).2.1⟩
  have hTp (i : ℕ) (hi : i < n) : T i / cutoffSkill (i + 1) ≤ production effortMax := by
    exact (div_le_iff₀ (hskill (i + 1) ⟨by omega, by omega⟩)).mpr
      (((le_max_left _ _).trans (hT i hi).1.le).trans (hT i hi).2.1)
  have hUp (i : ℕ) (hi : i < n) : U i / cutoffSkill (i + 1) ≤ production effortMax := by
    exact (div_le_iff₀ (hskill (i + 1) ⟨by omega, by omega⟩)).mpr
      (((le_max_left _ _).trans (hU i hi).1.le).trans (hU i hi).2.1)
  have hstep_le (i : ℕ) (hi : i < n)
      (h : C (U i / cutoffSkill (i + 1)) + (newReward (i + 1) - newReward i) ≤
        C (T i / cutoffSkill (i + 1)) + (reward (i + 1) - reward i)) : U (i + 1) ≤ T (i + 1) := by
    rw [← (hU i hi).2.2.1, ← (hT i hi).2.2.1] at h
    exact (div_le_div_iff_of_pos_right (hskill (i + 1) ⟨by omega, by omega⟩)).mp
      ((hCs.le_iff_le (hUm i hi) (hTm i hi)).mp h)
  have hstep_lt (i : ℕ) (hi : i < n)
      (h : C (U i / cutoffSkill (i + 1)) + (newReward (i + 1) - newReward i) <
        C (T i / cutoffSkill (i + 1)) + (reward (i + 1) - reward i)) : U (i + 1) < T (i + 1) := by
    rw [← (hU i hi).2.2.1, ← (hT i hi).2.2.1] at h
    exact (div_lt_div_iff_of_pos_right (hskill (i + 1) ⟨by omega, by omega⟩)).mp
      ((hCs.lt_iff_lt (hUm i hi) (hTm i hi)).mp h)
  have hbefore (i : ℕ) (hi : i < k) : U i = T i := by
    exact sourceRecursiveBandScore_congr_rewards cost production effortMax cutoffSkill reward newReward i
      (fun l hl => heq l (by omega) (by omega) (by omega))
  have hcost_k (hk0 : 0 < k) : C (U k / cutoffSkill k) - C (T k / cutoffSkill k) =
      newReward k - reward k := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have ht := (hT l (by omega)).2.2.1
    have hu := (hU l (by omega)).2.2.1
    change C (T (l + 1) / cutoffSkill (l + 1)) =
      C (T l / cutoffSkill (l + 1)) + (reward (l + 1) - reward l) at ht
    change C (U (l + 1) / cutoffSkill (l + 1)) =
      C (U l / cutoffSkill (l + 1)) + (newReward (l + 1) - newReward l) at hu
    rw [hbefore l (by omega), heq l (by omega) (by omega) (by omega)] at hu
    linarith
  have hraise (hk0 : 0 < k) : T k < U k := by
    have hcost := hcost_k hk0
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact (div_lt_div_iff_of_pos_right (hskill (l + 1) ⟨by omega, by omega⟩)).mp
      ((hCs.lt_iff_lt (hTm l (by omega)) (hUm l (by omega))).mp (by linarith))
  have hraise_le : T k ≤ U k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact le_rfl
    · exact (hraise hk0).le
  have hreward_next : newReward (k + 1) ≤ reward (k + 1) := by
    by_cases h : k + 1 = j
    · simpa only [h] using hj.le
    · exact (heq (k + 1) (by omega) (by omega) h).le
  have hnext : U (k + 1) < T (k + 1) := by
    apply hstep_lt k (by omega)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hzero : U 0 = T 0 := rfl
      rw [hzero]
      linarith
    · have hc := hcost_k hk0
      have hnonneg : 0 ≤ T k := by
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        exact (mul_nonneg hg0 (hskill (l + 1) ⟨by omega, by omega⟩).le).trans
          ((le_max_right _ _).trans (hT l (by omega)).1.le)
      have hfeas : U k / cutoffSkill k ≤ production effortMax := by
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        exact (hUm l (by omega)).2
      have hgap := sourceCostAtScore_gap_strict_antitone_skill_of_cost_lt
        hmax hp.monotoneOn hpconv hg hgm hgconc hnonneg (hraise hk0)
        (hskill k ⟨hk0, by omega⟩)
        (hskill_mono ⟨hk0, by omega⟩ ⟨by omega, by omega⟩ (by omega : k < k + 1)) hfeas
        (show C (T k / cutoffSkill k) < C (U k / cutoffSkill k) by linarith)
      change C (U k / cutoffSkill (k + 1)) - C (T k / cutoffSkill (k + 1)) <
        C (U k / cutoffSkill k) - C (T k / cutoffSkill k) at hgap
      linarith
  have hmiddle : ∀ i, k < i → i ≤ j → U i ≤ T i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hki hij
      by_cases hfirst : i = k + 1
      · simpa only [hfirst] using hnext.le
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hprev := ih l (by omega) (by omega) (by omega)
      apply hstep_le l (by omega)
      have hcost := hCm (hUp l (by omega)) (hTp l (by omega))
        ((div_le_div_iff_of_pos_right (hskill (l + 1) ⟨by omega, by omega⟩)).mpr hprev)
      have hrl := heq l (by omega) (by omega) (by omega)
      have hrnext : newReward (l + 1) ≤ reward (l + 1) := by
        by_cases h : l + 1 = j
        · simpa only [h] using hj.le
        · exact (heq (l + 1) (by omega) (by omega) h).le
      change C (U l / cutoffSkill (l + 1)) ≤ C (T l / cutoffSkill (l + 1)) at hcost
      linarith
  have hlast : U j < T j := by
    by_cases hfirst : j = k + 1
    · simpa only [hfirst] using hnext
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    apply hstep_lt l (by omega)
    have hprev := hmiddle l (by omega) (by omega)
    have hcost := hCm (hUp l (by omega)) (hTp l (by omega))
      ((div_le_div_iff_of_pos_right (hskill (l + 1) ⟨by omega, by omega⟩)).mpr hprev)
    have hrl := heq l (by omega) (by omega) (by omega)
    change C (U l / cutoffSkill (l + 1)) ≤ C (T l / cutoffSkill (l + 1)) at hcost
    linarith
  exact ⟨hbefore, hraise_le, hraise, hmiddle, hnext, hlast⟩

/-- Effort comparative statics for the source's actual recursive profile.
The lower band rises strictly whenever its new effort is positive; the next
and donor bands fall strictly whenever their old effort is positive. This
includes entry into and exit from the zero-effort region. -/
theorem sourceFiniteRankEffort_reward_transfer
    {cost production skill : ℝ → ℝ} {effortMax : ℝ} {n k j : ℕ}
    {cutoff reward newReward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hpcont : ContinuousOn cost (Icc 0 effortMax))
    (hp : StrictMonoOn cost (Icc 0 effortMax))
    (hp0 : cost 0 = 0) (hpmax : cost effortMax = 1)
    (hpconv : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hgm : StrictMonoOn production (Icc 0 effortMax)) (hg0 : 0 ≤ production 0)
    (hgconc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hr' : StrictMonoOn newReward (Icc (0 : ℕ) n)) (hr0' : 0 ≤ newReward 0) (hrn' : newReward n ≤ 1)
    (hkj : k < j) (hjn : j ≤ n)
    (hk : reward k < newReward k) (hj : newReward j < reward j)
    (heq : ∀ i ≤ n, i ≠ k → i ≠ j → newReward i = reward i)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    let i := (finiteLowerRankBand (fun l : Fin (n + 1) => cutoff l) t).val
    let e := sourceFiniteRankEffort cost production skill effortMax n cutoff reward t
    let d := sourceFiniteRankEffort cost production skill effortMax n cutoff newReward t
    (i < k → d = e) ∧ (i = k → e ≤ d) ∧ (k < i → i ≤ j → d ≤ e) ∧
      (i = k → 0 < d → e < d) ∧ ((i = k + 1 ∨ i = j) → 0 < e → d < e) := by
  let i := (finiteLowerRankBand (fun l : Fin (n + 1) => cutoff l) t).val
  let T := sourceRecursiveBandScore cost production effortMax (fun l => skill (cutoff l)) reward
  let U := sourceRecursiveBandScore cost production effortMax (fun l => skill (cutoff l)) newReward
  let e := sourceEffortAtScore production effortMax (T i / skill t)
  let d := sourceEffortAtScore production effortMax (U i / skill t)
  change (i < k → sourceFiniteRankEffort cost production skill effortMax n cutoff newReward t =
      sourceFiniteRankEffort cost production skill effortMax n cutoff reward t) ∧ _
  dsimp only [sourceFiniteRankEffort]
  rw [sourceClampedSkill_eq ⟨ht.1.le, ht.2⟩]
  change (i < k → d = e) ∧ (i = k → e ≤ d) ∧ (k < i → i ≤ j → d ≤ e) ∧
    (i = k → 0 < d → e < d) ∧ ((i = k + 1 ∨ i = j) → 0 < e → d < e)
  have hcmem (l : ℕ) (hl : l ≤ n + 1) : cutoff l ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hc0] using hc.monotoneOn ⟨le_rfl, by omega⟩ ⟨Nat.zero_le _, hl⟩ (Nat.zero_le _)
    · simpa only [hcn] using hc.monotoneOn ⟨Nat.zero_le _, hl⟩ ⟨Nat.zero_le _, le_rfl⟩ hl
  have hsk := sourceFiniteCutoffSkills_properties hc hc0 hcn hf hf0
  have hsk_strict : StrictMonoOn (fun l => skill (cutoff l)) (Icc (1 : ℕ) n) := by
    intro a ha b hb hab
    exact hf (hcmem a (Nat.le_succ_of_le ha.2)) (hcmem b (Nat.le_succ_of_le hb.2))
      (hc ⟨Nat.zero_le _, Nat.le_succ_of_le ha.2⟩ ⟨Nat.zero_le _, Nat.le_succ_of_le hb.2⟩ hab)
  have htransfer := sourceRecursiveBandScore_reward_transfer hmax hpcont hp hp0 hpmax hpconv
    hg hgm hg0 hgconc hsk.1 hsk_strict hr hr0 hrn hr' hr0' hrn' hkj hjn hk hj heq
  have hb := sourceFiniteRankBand_skill_bounds hc hc0 hcn hf hf0 ht
  have hi : i ≤ n := Nat.le_of_lt_succ (finiteLowerRankBand (fun l : Fin (n + 1) => cutoff l) t).isLt
  have he := sourceRecursiveBandScore_assigned_effort hmax hpcont hp hp0 hpmax hg hgm hg0
    hsk.1 hsk.2 hr hr0 hrn hi hb.1 hb.2.1
  have hd := sourceRecursiveBandScore_assigned_effort hmax hpcont hp hp0 hpmax hg hgm hg0
    hsk.1 hsk.2 hr' hr0' hrn' hi hb.1 hb.2.1
  have heScore : production e * skill t = max (T i) (production 0 * skill t) := he.2.2
  have hdScore : production d * skill t = max (U i) (production 0 * skill t) := hd.2.2
  have hmono : T i ≤ U i → e ≤ d := by
    intro h
    apply (hgm.le_iff_le he.1 hd.1).mp
    apply (mul_le_mul_iff_left₀ hb.1).mp
    rw [heScore, hdScore]
    exact max_le_max_right _ h
  have hanti : U i ≤ T i → d ≤ e := by
    intro h
    apply (hgm.le_iff_le hd.1 he.1).mp
    apply (mul_le_mul_iff_left₀ hb.1).mp
    rw [hdScore, heScore]
    exact max_le_max_right _ h
  have hstrict_up (h : T i < U i) (hpositive : 0 < d) : e < d := by
    have hbase := mul_lt_mul_of_pos_right (hgm ⟨le_rfl, hmax⟩ hd.1 hpositive) hb.1
    rw [hdScore] at hbase
    have hfloor : production 0 * skill t < U i :=
      (lt_max_iff.mp hbase).resolve_right (lt_irrefl _)
    apply (hgm.lt_iff_lt he.1 hd.1).mp
    apply (mul_lt_mul_iff_left₀ hb.1).mp
    rw [heScore, hdScore, max_eq_left hfloor.le]
    exact max_lt h hfloor
  have hstrict_down (h : U i < T i) (hpositive : 0 < e) : d < e := by
    have hbase := mul_lt_mul_of_pos_right (hgm ⟨le_rfl, hmax⟩ he.1 hpositive) hb.1
    rw [heScore] at hbase
    have hfloor : production 0 * skill t < T i :=
      (lt_max_iff.mp hbase).resolve_right (lt_irrefl _)
    apply (hgm.lt_iff_lt hd.1 he.1).mp
    apply (mul_lt_mul_iff_left₀ hb.1).mp
    rw [hdScore, heScore, max_eq_left hfloor.le]
    exact max_lt h hfloor
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hik
    change sourceEffortAtScore production effortMax (U i / skill t) =
      sourceEffortAtScore production effortMax (T i / skill t)
    have hequal : U i = T i := htransfer.1 i hik
    rw [hequal]
  · intro hik
    exact hmono (by simpa only [hik] using htransfer.2.1)
  · intro hki hij
    exact hanti (htransfer.2.2.2.1 i hki hij)
  · intro hik hpositive
    by_cases hk0 : k = 0
    · have hd0 : d = 0 := by
        change sourceEffortAtScore production effortMax (U i / skill t) = 0
        rw [hik, hk0]
        change sourceEffortAtScore production effortMax (0 / skill t) = 0
        simpa only [zero_div] using sourceEffortAtScore_zero hmax hgm hg0
      exact False.elim (by linarith)
    · exact hstrict_up (by simpa only [hik] using htransfer.2.2.1 (by omega)) hpositive
  · intro hij hpositive
    apply hstrict_down _ hpositive
    rcases hij with hik | hij
    · simpa only [hik] using htransfer.2.2.2.2.1
    · simpa only [hij] using htransfer.2.2.2.2.2

/-- The effort comparative-statics corollary for any pair of actual
almost-everywhere equilibria. The population, primitives, cutoffs, and tie
order are fixed. Increasing reward `k` and decreasing reward `j > k` gives
all weak comparisons and the source's strict-above-baseline clauses.

The cost-minimizing effort and its production may both be positive. No
differentiability is required, and no conclusion is imposed on bands above
the donor band. The result applies, in particular, to capacity-preserving
transfers between valid finite admission policies. -/
theorem sourceActualFiniteEquilibrium_effort_reward_transfer_of_sourcePrimitives
    {cost production skill effort newEffort score newScore tie : ℝ → ℝ} {baseline : ℝ}
    {n k j : ℕ} {cutoff reward newReward : ℕ → ℝ} (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hg : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hr' : StrictMonoOn newReward (Icc (0 : ℕ) n)) (hr0' : 0 ≤ newReward 0) (hrn' : newReward n ≤ 1)
    (hkj : k < j) (hjn : j ≤ n)
    (hk : reward k < newReward k) (hj : newReward j < reward j)
    (heq : ∀ i ≤ n, i ≠ k → i ≠ j → newReward i = reward i)
    (hscore : Measurable score) (hnewScore : Measurable newScore)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill score tie
        (fun i : Fin (n + 1) => cutoff i) reward t (effort t))
    (hnewBest : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill newScore tie
        (fun i : Fin (n + 1) => cutoff i) newReward t (newEffort t)) :
    ∀ᵐ t ∂unitRankMeasure,
      let i := (finiteLowerRankBand (fun l : Fin (n + 1) => cutoff l) t).val
      (i < k → newEffort t = effort t) ∧ (i = k → effort t ≤ newEffort t) ∧
        (k < i → i ≤ j → newEffort t ≤ effort t) ∧
        (i = k → baseline < newEffort t → effort t < newEffort t) ∧
        ((i = k + 1 ∨ i = j) → baseline < effort t → newEffort t < effort t) := by
  obtain ⟨E, hE, hpE, heffort⟩ := sourceFiniteBaselineEquilibrium_effort_unique_of_sourcePrimitives
    hbaseline hpcont hpconv hpnonneg hpzero hg hgm hgconc hg0 hc hc0 hcn hfcont hf hf0
    hr hr0 hrn hscore htie hinj hbest
  obtain ⟨F, hF, hpF, hnewEffort⟩ := sourceFiniteBaselineEquilibrium_effort_unique_of_sourcePrimitives
    hbaseline hpcont hpconv hpnonneg hpzero hg hgm hgconc hg0 hc hc0 hcn hfcont hf hf0
    hr' hr0' hrn' hnewScore htie hinj hnewBest
  have hpm := sourceCost_strictMonoOn_above_baseline hbaseline hpconv hpnonneg hpzero
  have hcap := hpm.injOn (le_add_of_nonneg_right hF.le) (le_add_of_nonneg_right hE.le) (hpF.trans hpE.symm)
  have hFE : F = E := by linarith
  subst F
  let P := fun e => cost (baseline + e)
  let G := fun e => production (baseline + e)
  have hshift : MapsTo (fun e => baseline + e) (Icc (0 : ℝ) E) (Ici 0) :=
    fun _ he => add_nonneg hbaseline he.1
  have hpc : ContinuousOn P (Icc 0 E) := hpcont.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hpM : StrictMonoOn P (Icc 0 E) := fun a ha b hb hab =>
    hpm (le_add_of_nonneg_right ha.1) (le_add_of_nonneg_right hb.1) (by linarith)
  have hpC : ConvexOn ℝ (Icc 0 E) P :=
    (hpconv.convexOn.translate_right baseline).subset hshift (convex_Icc _ _)
  have hpZ : P 0 = 0 := by simpa only [P, add_zero] using hpzero
  have hgC : ContinuousOn G (Icc 0 E) := hg.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hgM : StrictMonoOn G (Icc 0 E) := fun a ha b hb hab =>
    hgm (hshift ha) (hshift hb) (by linarith)
  have hgV : ConcaveOn ℝ (Icc 0 E) G :=
    (hgconc.translate_right baseline).subset hshift (convex_Icc _ _)
  have hgZ : 0 ≤ G 0 := by
    simpa only [G, add_zero] using hg0.trans (hgm.monotoneOn (by simp) hbaseline hbaseline)
  filter_upwards [heffort, hnewEffort, ae_restrict_mem measurableSet_Ioc] with t he hd ht
  have h := sourceFiniteRankEffort_reward_transfer hE.le hpc hpM hpZ hpE hpC hgC hgM hgZ hgV
    hc hc0 hcn hf hf0 hr hr0 hrn hr' hr0' hrn' hkj hjn hk hj heq ht
  dsimp only
  rw [he, hd]
  simpa only [sourceFiniteBaselineEffort, add_right_inj, add_le_add_iff_left,
    add_lt_add_iff_left, lt_add_iff_pos_right, P, G] using h

end LBG22StrategicRanking

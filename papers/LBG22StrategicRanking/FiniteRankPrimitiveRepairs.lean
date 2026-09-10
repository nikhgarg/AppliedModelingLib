import LBG22StrategicRanking.FiniteEquilibriumPrimitiveRepairs

/-!
# Population ranks for finite reward bands

Rank cutoffs carry the lower reward. Within each reward band, the score and
tie key order the population; between bands, the constructed score thresholds
separate all applicants. These facts connect score-menu incentives to the
actual contour-measure rank, including counterfactual scores in gaps.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- The greatest reward level whose lower cutoff is strictly below the rank.
The bottom reward also covers ranks below the first cutoff. -/
noncomputable def finiteLowerRankBand {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    (rank : ℝ) : Fin (n + 1) := by
  classical
  exact Finset.univ.sup (fun i => if cutoff i < rank then i else 0)

theorem le_finiteLowerRankBand_of_cutoff_lt {n : ℕ}
    {cutoff : Fin (n + 1) → ℝ} {rank : ℝ} {i : Fin (n + 1)}
    (hi : cutoff i < rank) : i ≤ finiteLowerRankBand cutoff rank := by
  classical
  unfold finiteLowerRankBand
  simpa only [if_pos hi] using
    (Finset.le_sup (f := fun j => if cutoff j < rank then j else 0) (Finset.mem_univ i))

theorem finiteLowerRankBand_le_of_upper {n : ℕ}
    {cutoff : Fin (n + 1) → ℝ} {rank : ℝ} {i : Fin (n + 1)}
    (hi : ∀ j, i < j → rank ≤ cutoff j) : finiteLowerRankBand cutoff rank ≤ i := by
  classical
  apply Finset.sup_le_iff.mpr
  intro j _
  split_ifs with hj
  · exact le_of_not_gt (fun hij => (not_lt_of_ge (hi j hij)) hj)
  · exact Fin.zero_le _

theorem finiteLowerRankBand_eq_of_interval {n : ℕ}
    {cutoff : Fin (n + 1) → ℝ} {rank : ℝ} {i : Fin (n + 1)}
    (hlower : cutoff i < rank) (hupper : ∀ j, i < j → rank ≤ cutoff j) :
    finiteLowerRankBand cutoff rank = i :=
  le_antisymm (finiteLowerRankBand_le_of_upper hupper)
    (le_finiteLowerRankBand_of_cutoff_lt hlower)

theorem finiteLowerRankBand_monotone {n : ℕ} (cutoff : Fin (n + 1) → ℝ) :
    Monotone (finiteLowerRankBand cutoff) := by
  classical
  intro a b hab
  apply Finset.sup_le_iff.mpr
  intro i _
  split_ifs with hi
  · exact le_finiteLowerRankBand_of_cutoff_lt (hi.trans_le hab)
  · exact Fin.zero_le _

theorem measurable_finiteLowerRankBand {n : ℕ} (cutoff : Fin (n + 1) → ℝ) :
    Measurable (finiteLowerRankBand cutoff) :=
  (finiteLowerRankBand_monotone cutoff).measurable

theorem finiteLowerRankBand_lt_iff {n : ℕ} {cutoff : Fin (n + 1) → ℝ}
    (hc : Monotone cutoff) {rank : ℝ} {i : Fin (n + 1)} (hi : 0 < i) :
    finiteLowerRankBand cutoff rank < i ↔ rank ≤ cutoff i := by
  classical
  constructor
  · intro h
    exact le_of_not_gt (fun hr => (not_le_of_gt h) (le_finiteLowerRankBand_of_cutoff_lt hr))
  · intro h
    apply (Finset.sup_lt_iff hi).mpr
    intro j _
    split_ifs with hj
    · exact lt_of_not_ge (fun hij => (not_lt_of_ge (h.trans (hc hij))) hj)
    · exact hi

theorem cutoff_finiteLowerRankBand_lt {n : ℕ} {cutoff : Fin (n + 1) → ℝ}
    {rank : ℝ} (hfirst : cutoff 0 < rank) :
    cutoff (finiteLowerRankBand cutoff rank) < rank := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i : Fin (n + 1) => if cutoff i < rank then i else 0)
  change finiteLowerRankBand cutoff rank = _ at hi
  rw [hi]
  split_ifs with h
  · exact h
  · exact hfirst

theorem unitRankMeasure_Iic {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    (unitRankMeasure (Iic c)).toReal = c := by
  have hset : Iic c ∩ Ioc (0 : ℝ) 1 = Ioc 0 c := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hc.2⟩⟩
  rw [unitRankMeasure, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Ioc,
    sub_zero, ENNReal.toReal_ofReal hc.1]

/-- A score below every applicant above a cutoff has counterfactual rank at
most that cutoff, regardless of the tie key or whether the score is attained. -/
theorem counterfactualTieBrokenRank_le_cutoff
    {score tie : ℝ → ℝ} {c v : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (habove : ∀ y ∈ Ioc c 1, v < score y) (x : ℝ) :
    counterfactualTieBrokenRank unitRankMeasure score tie x v ≤ c := by
  have hsubset : {y | score y < v ∨ score y = v ∧ tie y ≤ tie x} ≤ᵐ[unitRankMeasure] Iic c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    intro h
    by_contra hn
    have hs := habove y ⟨lt_of_not_ge hn, hy.2⟩
    rcases h with h | ⟨h, _⟩ <;> linarith
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)).trans_eq
    (unitRankMeasure_Iic hc)

/-- A measurable total ordering has a positive lower contour almost
everywhere. If a positive-mass set had zero lower contours, Fubini would make
almost every pair in that set incomparable, contradicting totality. Neither
atomlessness nor a particular tie key is needed for this positivity fact. -/
theorem tieBrokenLowerContour_pos_ae
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie) :
    ∀ᵐ x ∂μ, 0 < μ (tieBrokenLowerContour score tie x) := by
  let A := {x | μ (tieBrokenLowerContour score tie x) = 0}
  have hm : Measurable (fun x => μ (tieBrokenLowerContour score tie x)) :=
    measurable_measure_prodMk_left (measurableSet_tieBrokenLowerContourProduct hscore htie)
  have hA : MeasurableSet A := measurableSet_eq_fun hm measurable_const
  have hzero : μ A = 0 := by
    let ν := μ.restrict A
    have hrows : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, y ∉ tieBrokenLowerContour score tie x := by
      filter_upwards [ae_restrict_mem hA] with x hx
      apply ae_restrict_of_ae
      exact ae_iff.mpr (by simpa only [not_not] using hx)
    have hcols : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, x ∉ tieBrokenLowerContour score tie y := by
      exact (Measure.ae_ae_comm
        (measurableSet_tieBrokenLowerContourProduct hscore htie).compl).mp hrows
    have hν : ν = 0 := by
      by_contra hn
      haveI : NeZero ν := ⟨hn⟩
      obtain ⟨x, hx, hx'⟩ := (hrows.and hcols).exists
      obtain ⟨y, hy, hy'⟩ := (hx.and hx').exists
      apply hy
      change score y < score x ∨ score y = score x ∧ tie y ≤ tie x
      by_cases hs : score y < score x
      · exact Or.inl hs
      · have hs' : score y = score x := by
          by_contra hne
          exact hy' (Or.inl (lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm hne)))
        right
        refine ⟨hs', ?_⟩
        by_contra ht
        exact hy' (Or.inr ⟨hs'.symm, (lt_of_not_ge ht).le⟩)
    simpa [ν] using
      congrArg (fun m : Measure α => m univ) hν
  apply ae_iff.mpr
  simpa only [not_lt, nonpos_iff_eq_zero] using hzero

/-- Strict score separation across a population cutoff makes almost every
rank above that cutoff strictly exceed it, even when scores have atoms. -/
theorem tieBrokenRank_gt_cutoff_ae
    {score tie : ℝ → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ y ∈ Ioc (0 : ℝ) c, ∀ x ∈ Ioc c 1, score y < score x) :
    ∀ᵐ x ∂unitRankMeasure, x ∈ Ioc c 1 →
      c < tieBrokenRank unitRankMeasure score tie x := by
  have hprefix := (ae_restrict_iff' measurableSet_Ioc).mp
    (tieBrokenLowerContour_pos_ae (unitRankMeasure.restrict (Ioc c 1)) hscore htie)
  filter_upwards [hprefix] with x hx hxmem
  let C := tieBrokenLowerContour score tie x
  have hC : MeasurableSet C := measurableSet_tieBrokenLowerContour hscore htie x
  have hleft : (unitRankMeasure (Ioc (0 : ℝ) c)).toReal = c := by
    rw [unitRankMeasure, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc (0 : ℝ) c ⊆ Ioc 0 1 from
        fun _ hy => ⟨hy.1, hy.2.trans hc.2⟩), Real.volume_Ioc,
      sub_zero, ENNReal.toReal_ofReal hc.1]
  have hdisjoint : Disjoint (Ioc (0 : ℝ) c) (C ∩ Ioc c 1) := by
    apply disjoint_left.mpr
    intro y hy hy'
    exact (not_lt_of_ge hy.2) hy'.2.1
  have hsubset : Ioc (0 : ℝ) c ∪ (C ∩ Ioc c 1) ⊆ C := by
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (hsep y hy x hxmem)
    · exact hy.1
  have hbound := ENNReal.toReal_mono (measure_ne_top unitRankMeasure C) (measure_mono hsubset)
  rw [measure_union hdisjoint (hC.inter measurableSet_Ioc),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hleft] at hbound
  have hp := hx hxmem
  rw [Measure.restrict_apply hC] at hp
  have hpositive : 0 < (unitRankMeasure (C ∩ Ioc c 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  change c < (unitRankMeasure C).toReal
  linarith

/-- For strictly score-separated reward bands, actual tie-broken ranks give
the assigned band almost everywhere. The result allows arbitrary measurable
tie keys, so reward realization does not require choosing ties by skill. -/
theorem finiteLowerRankBand_tieBrokenRank_ae_eq
    {n : ℕ} {cutoff : Fin (n + 1) → ℝ}
    (hc : StrictMono cutoff) (hc_zero : cutoff 0 = 0)
    (hc_one : ∀ i, cutoff i ≤ 1)
    {score tie : ℝ → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    (hsep : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      finiteLowerRankBand cutoff x < finiteLowerRankBand cutoff y → score x < score y) :
    (fun x => finiteLowerRankBand cutoff (tieBrokenRank unitRankMeasure score tie x))
      =ᵐ[unitRankMeasure] finiteLowerRankBand cutoff := by
  have hnonneg (i : Fin (n + 1)) : 0 ≤ cutoff i := by
    simpa only [hc_zero] using hc.monotone (Fin.zero_le i)
  have hpositive (i : Fin (n + 1)) : ∀ᵐ x ∂unitRankMeasure, x ∈ Ioc (cutoff i) 1 →
      cutoff i < tieBrokenRank unitRankMeasure score tie x := by
    apply tieBrokenRank_gt_cutoff_ae hscore htie ⟨hnonneg i, hc_one i⟩
    intro y hy x hx
    have hi : 0 < i := by
      by_contra hn
      have hieq : i = 0 := le_antisymm (le_of_not_gt hn) (Fin.zero_le i)
      rw [hieq, hc_zero] at hy
      exact (not_lt_of_ge hy.2) hy.1
    have hyband := (finiteLowerRankBand_lt_iff hc.monotone hi).mpr hy.2
    have hxband := le_finiteLowerRankBand_of_cutoff_lt hx.1
    exact hsep y ⟨hy.1, hy.2.trans (hc_one i)⟩
      x ⟨(hnonneg i).trans_lt hx.1, hx.2⟩ (hyband.trans_le hxband)
  filter_upwards [ae_all_iff.mpr hpositive, ae_restrict_mem measurableSet_Ioc] with x hx hxmem
  let i := finiteLowerRankBand cutoff x
  have hix : cutoff i < x := cutoff_finiteLowerRankBand_lt (by simpa only [hc_zero] using hxmem.1)
  apply finiteLowerRankBand_eq_of_interval (hx i ⟨hix, hxmem.2⟩)
  intro j hij
  apply counterfactualTieBrokenRank_le_cutoff ⟨hnonneg j, hc_one j⟩ _ x
  intro y hy
  have hjy := le_finiteLowerRankBand_of_cutoff_lt hy.1
  exact hsep x hxmem y ⟨(hnonneg j).trans_lt hy.1, hy.2⟩ (hij.trans_le hjy)

/-- Any counterfactual ranking reward is bounded by the score-threshold menu.
Strict cutoff inequalities are essential when the score lies in a gap. -/
theorem finiteLowerRankBand_counterfactual_le_scoreBand
    {n : ℕ} {cutoff target : Fin (n + 1) → ℝ}
    (hc : Monotone cutoff) (hc_zero : cutoff 0 = 0)
    (hc_one : ∀ i, cutoff i ≤ 1) (hT : Monotone target)
    {score tie : ℝ → ℝ}
    (hreach : ∀ y ∈ Ioc (0 : ℝ) 1, target (finiteLowerRankBand cutoff y) ≤ score y)
    (x v : ℝ) :
    finiteLowerRankBand cutoff (counterfactualTieBrokenRank unitRankMeasure score tie x v)
      ≤ finiteScoreBand target v := by
  apply finiteLowerRankBand_le_of_upper
  intro i hi
  have hi0 : 0 ≤ cutoff i := by simpa only [hc_zero] using hc (Fin.zero_le i)
  apply counterfactualTieBrokenRank_le_cutoff ⟨hi0, hc_one i⟩ _ x
  intro y hy
  have hv : v < target i := by
    by_contra hn
    exact (not_le_of_gt hi) (le_finiteScoreBand_of_target_le (le_of_not_gt hn))
  exact hv.trans_le ((hT (le_finiteLowerRankBand_of_cutoff_lt hy.1)).trans
    (hreach y ⟨hi0.trans_lt hy.1, hy.2⟩))

/-- Extending the skill quantile by endpoint clipping adds no assumption
outside its source domain, the unit rank interval. -/
noncomputable def sourceClampedSkill (skill : ℝ → ℝ) (t : ℝ) : ℝ :=
  skill (max 0 (min t 1))

theorem sourceClampedSkill_eq {skill : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceClampedSkill skill t = skill t := by
  simp only [sourceClampedSkill, min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_sourceClampedSkill {skill : ℝ → ℝ}
    (hf : ContinuousOn skill (Icc (0 : ℝ) 1)) : Continuous (sourceClampedSkill skill) := by
  apply hf.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
  intro t
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

/-- The source finite-band effort profile, with boundary scores constructed
recursively from cost, production, skills, and reward increments. -/
noncomputable def sourceFiniteRankEffort (cost production skill : ℝ → ℝ)
    (effortMax : ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ) (t : ℝ) : ℝ :=
  sourceEffortAtScore production effortMax
    (sourceRecursiveBandScore cost production effortMax (fun k => skill (cutoff k)) reward
      (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t) / sourceClampedSkill skill t)

/-- The finite-band score profile, retaining positive baseline production.
Endpoint-clipped skills are used only to define the function off the source
population's support. -/
noncomputable def sourceFiniteRankScore (cost production skill : ℝ → ℝ)
    (effortMax : ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ) (t : ℝ) : ℝ :=
  max (sourceRecursiveBandScore cost production effortMax (fun k => skill (cutoff k)) reward
    (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t))
    (production 0 * sourceClampedSkill skill t)

theorem measurable_sourceFiniteRankScore {cost production skill : ℝ → ℝ}
    {effortMax : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hf : ContinuousOn skill (Icc (0 : ℝ) 1)) :
    Measurable (sourceFiniteRankScore cost production skill effortMax n cutoff reward) := by
  exact ((measurable_of_finite
    (fun i : Fin (n + 1) => sourceRecursiveBandScore cost production effortMax
      (fun k => skill (cutoff k)) reward i)).comp
        (measurable_finiteLowerRankBand _)).max
    (measurable_const.mul (continuous_sourceClampedSkill hf).measurable)

/-- Rank band membership supplies the actual lower and upper skill bounds.
In particular no boundary-skill equalities are supplied separately. -/
theorem sourceFiniteRankBand_skill_bounds
    {skill : ℝ → ℝ} {n : ℕ} {cutoff : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0)
    (hc_top : cutoff (n + 1) = 1) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf_zero : 0 ≤ skill 0) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    let i := (finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t).val
    0 < skill t ∧ (0 < i → skill (cutoff i) ≤ skill t) ∧
      (i < n → skill t ≤ skill (cutoff (i + 1))) := by
  let i := finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t
  have hc_mem (k : ℕ) (hk : k ≤ n + 1) : cutoff k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hc_zero] using hc.monotoneOn ⟨le_rfl, by omega⟩ ⟨Nat.zero_le _, hk⟩ (Nat.zero_le k)
    · simpa only [hc_top] using hc.monotoneOn ⟨Nat.zero_le _, hk⟩ ⟨Nat.zero_le _, le_rfl⟩ hk
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hlow : cutoff i.val < t := cutoff_finiteLowerRankBand_lt
    (cutoff := fun j : Fin (n + 1) => cutoff j) (by simpa only [Fin.val_zero, hc_zero] using ht.1)
  refine ⟨hf_zero.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1), ?_, ?_⟩
  · intro _
    exact hf.monotoneOn (hc_mem i.val (by omega)) ⟨ht.1.le, ht.2⟩ hlow.le
  · intro hin
    have hhigh : t ≤ cutoff (i.val + 1) := by
      by_contra hn
      have hle := le_finiteLowerRankBand_of_cutoff_lt
        (cutoff := fun j : Fin (n + 1) => cutoff j)
        (i := ⟨i.val + 1, by omega⟩) (lt_of_not_ge hn)
      have : i.val + 1 ≤ i.val := hle
      omega
    exact hf.monotoneOn ⟨ht.1.le, ht.2⟩ (hc_mem (i.val + 1) (by omega)) hhigh

theorem sourceFiniteCutoffSkills_properties
    {skill : ℝ → ℝ} {n : ℕ} {cutoff : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0)
    (hc_top : cutoff (n + 1) = 1) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf_zero : 0 ≤ skill 0) :
    (∀ k ∈ Icc (1 : ℕ) n, 0 < skill (cutoff k)) ∧
      MonotoneOn (fun k => skill (cutoff k)) (Icc (1 : ℕ) n) := by
  have hc_mem (k : ℕ) (hk : k ≤ n + 1) : cutoff k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hc_zero] using hc.monotoneOn ⟨le_rfl, by omega⟩ ⟨Nat.zero_le _, hk⟩ (Nat.zero_le k)
    · simpa only [hc_top] using hc.monotoneOn ⟨Nat.zero_le _, hk⟩ ⟨Nat.zero_le _, le_rfl⟩ hk
  constructor
  · intro k hk
    have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk.1
    have hck : 0 < cutoff k := by
      simpa only [hc_zero] using hc ⟨le_rfl, by omega⟩
        ⟨Nat.zero_le _, Nat.le_succ_of_le hk.2⟩ hk0
    exact hf_zero.trans_lt (hf ⟨le_rfl, by norm_num⟩ (hc_mem k (Nat.le_succ_of_le hk.2)) hck)
  · intro a ha b hb hab
    exact hf.monotoneOn (hc_mem a (Nat.le_succ_of_le ha.2)) (hc_mem b (Nat.le_succ_of_le hb.2))
      (hc.monotoneOn ⟨Nat.zero_le _, Nat.le_succ_of_le ha.2⟩
        ⟨Nat.zero_le _, Nat.le_succ_of_le hb.2⟩ hab)

/-- The rank-indexed source profile has its displayed score, reaches its
assigned score-menu band, and is optimal against every nonnegative effort.
All boundary skills are instantiated from the source quantile and cutoffs. -/
theorem sourceFiniteRankEffort_score_and_incentives
    {cost production skill : ℝ → ℝ} {effortMax : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Ici 0))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0)
    (hc_top : cutoff (n + 1) = 1) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf_zero : 0 ≤ skill 0) (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    let T := fun i : Fin (n + 1) =>
      sourceRecursiveBandScore cost production effortMax (fun k => skill (cutoff k)) reward i
    let i := finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t
    let e := sourceFiniteRankEffort cost production skill effortMax n cutoff reward t
    let v := sourceFiniteRankScore cost production skill effortMax n cutoff reward t
    e ∈ Icc (0 : ℝ) effortMax ∧ v = production e * skill t ∧ finiteScoreBand T v = i ∧
      ∀ d : ℝ, 0 ≤ d → reward (finiteScoreBand T (production d * skill t)).val - cost d ≤
        reward i.val - cost e := by
  let i := finiteLowerRankBand (fun j : Fin (n + 1) => cutoff j) t
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hsk := sourceFiniteCutoffSkills_properties hc hc_zero hc_top hf hf_zero
  have hb := sourceFiniteRankBand_skill_bounds hc hc_zero hc_top hf hf_zero ht
  have hpmono : StrictMonoOn cost (Icc 0 effortMax) := hcost_mono.mono Icc_subset_Ici_self
  have he := sourceRecursiveBandScore_assigned_effort hmax hcost hpmono hcost_zero hcost_max
    hg hg_mono hg_zero hsk.1 hsk.2 hreward hreward_zero hreward_top hi hb.1 hb.2.1
  have hbest := sourceRecursiveBandScore_bestResponse_to_scoreClassifier
    hmax hcost hcost_mono hcost_zero hcost_max hcost_convex hg hg_mono hg_zero hg_conc
    hsk.1 hsk.2 hreward hreward_zero hreward_top hi hb.1 hb.2.1 hb.2.2
  dsimp only [sourceFiniteRankEffort, sourceFiniteRankScore]
  rw [sourceClampedSkill_eq ⟨ht.1.le, ht.2⟩]
  refine ⟨he.1, he.2.2.symm, ?_, ?_⟩
  · rw [← he.2.2]
    exact Fin.ext hbest.2.1
  · intro d hd
    simpa only [hbest.2.1] using hbest.2.2 d hd

/-- The constructed finite-band effort is an almost-everywhere best response
under the actual contour-measure rank and the lower-reward cutoff convention.
The population score, all boundary efforts, reward realization, and the bound
on every counterfactual reward are derived from cost, production, and skills.
No atomless-rank or rank-reachability conclusion is assumed. -/
theorem sourceFiniteRankEffort_bestResponseAE
    {cost production skill tie : ℝ → ℝ} {effortMax : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Ici 0))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0)
    (hc_top : cutoff (n + 1) = 1) (hf_cont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf_zero : 0 ≤ skill 0)
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1) (htie : Measurable tie) :
    let effort := sourceFiniteRankEffort cost production skill effortMax n cutoff reward
    let score := sourceFiniteRankScore cost production skill effortMax n cutoff reward
    let band := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
    let rank := fun t d => counterfactualTieBrokenRank unitRankMeasure score tie t
      (production d * skill t)
    ∀ᵐ t ∂unitRankMeasure,
      effort t ∈ Icc (0 : ℝ) effortMax ∧ score t = production (effort t) * skill t ∧
      band (rank t (effort t)) = band t ∧
      ∀ d : ℝ, 0 ≤ d → reward (band (rank t d)).val - cost d ≤
        reward (band (rank t (effort t))).val - cost (effort t) := by
  let effort := sourceFiniteRankEffort cost production skill effortMax n cutoff reward
  let score := sourceFiniteRankScore cost production skill effortMax n cutoff reward
  let cuts := fun i : Fin (n + 1) => cutoff i
  let band := finiteLowerRankBand cuts
  let targets := fun i : Fin (n + 1) =>
    sourceRecursiveBandScore cost production effortMax (fun k => skill (cutoff k)) reward i
  have hcuts : StrictMono cuts := by
    intro i j hij
    exact hc ⟨Nat.zero_le _, Nat.le_of_lt i.isLt⟩ ⟨Nat.zero_le _, Nat.le_of_lt j.isLt⟩ hij
  have hcuts0 : cuts 0 = 0 := hc_zero
  have hcuts1 (i : Fin (n + 1)) : cuts i ≤ 1 := by
    simpa only [hc_top] using hc.monotoneOn
      ⟨Nat.zero_le _, Nat.le_of_lt i.isLt⟩ ⟨Nat.zero_le _, le_rfl⟩ (Nat.le_of_lt i.isLt)
  have hprofile (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :=
    sourceFiniteRankEffort_score_and_incentives hmax hcost hcost_mono hcost_zero hcost_max
      hcost_convex hg hg_mono hg_zero hg_conc hc hc_zero hc_top hf hf_zero
      hreward hreward_zero hreward_top ht
  have hreach (t : ℝ) (_ht : t ∈ Ioc (0 : ℝ) 1) : targets (band t) ≤ score t :=
    le_max_left _ _
  have hsep : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      band x < band y → score x < score y := by
    intro x hx y hy hxy
    by_contra hn
    have hle : band y ≤ finiteScoreBand targets (score x) :=
      le_finiteScoreBand_of_target_le ((hreach y hy).trans (le_of_not_gt hn))
    have hclass : finiteScoreBand targets (score x) = band x := (hprofile x hx).2.2.1
    rw [hclass] at hle
    exact (not_le_of_gt hxy) hle
  have hown := finiteLowerRankBand_tieBrokenRank_ae_eq hcuts hcuts0 hcuts1
    (measurable_sourceFiniteRankScore hf_cont) htie hsep
  have hsk := sourceFiniteCutoffSkills_properties hc hc_zero hc_top hf hf_zero
  have hpmono : StrictMonoOn cost (Icc 0 effortMax) := hcost_mono.mono Icc_subset_Ici_self
  have hstep := sourceRecursiveBandScore_properties hmax hcost hpmono hcost_zero hcost_max
    hg hg_mono hg_zero hsk.1 hsk.2 hreward hreward_zero hreward_top
  have hstrict : StrictMonoOn
      (sourceRecursiveBandScore cost production effortMax (fun k => skill (cutoff k)) reward)
      (Iic n) := strictMonoOn_Iic_of_lt_succ
        (fun k hk => (le_max_left _ _).trans_lt (hstep k hk).1)
  have htargets : Monotone targets := by
    intro i j hij
    exact hstrict.monotoneOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
  have hcounter (t v : ℝ) := finiteLowerRankBand_counterfactual_le_scoreBand
    hcuts.monotone hcuts0 hcuts1 htargets (tie := tie) hreach t v
  filter_upwards [hown, ae_restrict_mem measurableSet_Ioc] with t ht htmem
  change band (tieBrokenRank unitRankMeasure score tie t) = band t at ht
  have hp := hprofile t htmem
  have hcurrent : counterfactualTieBrokenRank unitRankMeasure score tie t
      (production (effort t) * skill t) = tieBrokenRank unitRankMeasure score tie t := by
    rw [← hp.2.1]
    rfl
  refine ⟨hp.1, hp.2.1, ?_, ?_⟩
  · exact congrArg band hcurrent |>.trans ht
  · intro d hd
    change reward (band (counterfactualTieBrokenRank unitRankMeasure score tie t
      (production d * skill t))).val - cost d ≤ reward (band
        (counterfactualTieBrokenRank unitRankMeasure score tie t
          (production (effort t) * skill t))).val - cost (effort t)
    rw [hcurrent, ht]
    have hbd := hcounter t (production d * skill t)
    have hr := hreward.monotoneOn
      ⟨Nat.zero_le _, Nat.le_of_lt_succ (band (counterfactualTieBrokenRank
        unitRankMeasure score tie t (production d * skill t))).isLt⟩
      ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteScoreBand targets (production d * skill t)).isLt⟩
      (show (band (counterfactualTieBrokenRank unitRankMeasure score tie t
        (production d * skill t))).val ≤ (finiteScoreBand targets (production d * skill t)).val
        from hbd)
    exact (sub_le_sub_right hr (cost d)).trans (hp.2.2.2 d hd)

/-- A bounded effort is measurably recoverable from its score and positive
skill by the continuous inverse of strictly increasing production. -/
theorem aemeasurable_effort_of_measurable_score
    {production skill score effort : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hf_cont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < skill t) (hscore : Measurable score)
    (he : ∀ᵐ t ∂unitRankMeasure, effort t ∈ Icc (0 : ℝ) effortMax ∧
      score t = production (effort t) * skill t) :
    AEMeasurable effort unitRankMeasure := by
  let inv := fun z => effortIntervalInverse production effortMax
    (max (production 0) (min z (production effortMax)))
  have hinv : Continuous inv := by
    apply (effortIntervalInverse_continuousOn hmax hg hg_mono).comp_continuous
      (continuous_const.max (continuous_id.min continuous_const))
    intro z
    exact ⟨le_max_left _ _, max_le (hg_mono.monotoneOn ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax)
      (min_le_right _ _)⟩
  apply (hinv.measurable.comp (hscore.div (continuous_sourceClampedSkill hf_cont).measurable)).aemeasurable.congr
  filter_upwards [he, ae_restrict_mem measurableSet_Ioc] with t ht htmem
  change inv (score t / sourceClampedSkill skill t) = effort t
  rw [sourceClampedSkill_eq ⟨htmem.1.le, htmem.2⟩, ht.2,
    mul_div_cancel_right₀ _ (hf_pos t htmem).ne']
  change effortIntervalInverse production effortMax
    (max (production 0) (min (production (effort t)) (production effortMax))) = effort t
  rw [min_eq_left (hg_mono.monotoneOn ht.1 ⟨hmax, le_rfl⟩ ht.1.2),
    max_eq_right (hg_mono.monotoneOn ⟨le_rfl, hmax⟩ ht.1 ht.1.1)]
  exact hg_mono.injOn.leftInvOn_invFunOn ht.1

/-- The unit-cost effort cap and cost monotonicity are consequences of the
source cost primitives, not additional assumptions on the action space.
The constructed profile is a best response against every nonnegative effort
under the corrected finite-band rank policy. -/
theorem exists_sourceFiniteRankEffort_bestResponseAE_of_sourcePrimitives
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
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1) (htie : Measurable tie) :
    ∃ effortMax : ℝ, 0 < effortMax ∧ cost effortMax = 1 ∧
      let effort := sourceFiniteRankEffort cost production skill effortMax n cutoff reward
      let score := sourceFiniteRankScore cost production skill effortMax n cutoff reward
      let band := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      let rank := fun t d => counterfactualTieBrokenRank unitRankMeasure score tie t
        (production d * skill t)
      AEMeasurable effort unitRankMeasure ∧ ∀ᵐ t ∂unitRankMeasure,
        effort t ∈ Icc (0 : ℝ) effortMax ∧ score t = production (effort t) * skill t ∧
        band (rank t (effort t)) = band t ∧
        ∀ d : ℝ, 0 ≤ d → reward (band (rank t d)).val - cost d ≤
          reward (band (rank t (effort t))).val - cost (effort t) := by
  obtain ⟨effortMax, hmax, hcap, hpmono⟩ :=
    exists_unitCost_effort_of_sourcePrimitives hcost_cont hcost hcost_nonneg hcost_zero
  refine ⟨effortMax, hmax, hcap, ?_⟩
  have hbest := sourceFiniteRankEffort_bestResponseAE hmax.le (hcost_cont.mono Icc_subset_Ici_self)
    hpmono hcost_zero hcap (hcost.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    (hg.mono Icc_subset_Ici_self) (hg_mono.mono Icc_subset_Ici_self) hg_zero
    (hg_conc.subset Icc_subset_Ici_self (convex_Icc _ _)) hc hc_zero hc_top
    hf_cont hf hf_zero hreward hreward_zero hreward_top htie
  refine ⟨?_, hbest⟩
  apply aemeasurable_effort_of_measurable_score hmax.le (hg.mono Icc_subset_Ici_self)
    (hg_mono.mono Icc_subset_Ici_self) hf_cont _ (measurable_sourceFiniteRankScore hf_cont)
    (hbest.mono (fun _ h => ⟨h.1, h.2.1⟩))
  intro t ht
  exact hf_zero.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)

end LBG22StrategicRanking

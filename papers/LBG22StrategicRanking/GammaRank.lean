import LBG22StrategicRanking.MainTheorems
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.CDF

namespace LBG22StrategicRanking

open Set
open MeasureTheory

/-!
# Tie-broken rank construction

The source paper's `gamma` map ranks applicants by post-effort score and fills
atoms by an auxiliary tie-breaking order.  This file starts the source-model
object needed to remove the remaining `hpost_dist` parameter from the
rank-preservation bridge.
-/

/--
Lower contour for the source tie-broken ranking: applicants with lower score
come first; applicants with the same score are ordered by the auxiliary
tie-breaking coordinate.
-/
def tieBrokenLowerContour
    {α : Type*} (score tie : α → ℝ) (x : α) : Set α :=
  {y | score y < score x ∨ score y = score x ∧ tie y ≤ tie x}

/--
Strict lower score contour, before filling a score atom by the tie-breaking
coordinate.
-/
def scoreLowerContour
    {α : Type*} (score : α → ℝ) (x : α) : Set α :=
  {y | score y < score x}

/-- The score atom containing an applicant. -/
def scoreAtom
    {α : Type*} (score : α → ℝ) (x : α) : Set α :=
  {y | score y = score x}

/--
Tie prefix inside a score atom.  This is the piece used by the source gamma
construction to fill a discontinuity of the score CDF.
-/
def tiePrefixInScoreAtom
    {α : Type*} (score tie : α → ℝ) (x : α) : Set α :=
  {y | score y = score x ∧ tie y ≤ tie x}

/-- Strict version of the tie-broken lower contour. -/
def tieBrokenStrictLowerContour
    {α : Type*} (score tie : α → ℝ) (x : α) : Set α :=
  {y | score y < score x ∨ score y = score x ∧ tie y < tie x}

/-- Exact key fiber for the score/tie lexicographic key. -/
def exactScoreTieKey
    {α : Type*} (score tie : α → ℝ) (x : α) : Set α :=
  {y | score y = score x ∧ tie y = tie x}

theorem measurableSet_scoreLowerContour
    {α : Type*} [MeasurableSpace α] {score : α → ℝ}
    (hscore : Measurable score) (x : α) :
    MeasurableSet (scoreLowerContour score x) := by
  simpa [scoreLowerContour] using
    measurableSet_lt hscore measurable_const

theorem measurableSet_scoreAtom
    {α : Type*} [MeasurableSpace α] {score : α → ℝ}
    (hscore : Measurable score) (x : α) :
    MeasurableSet (scoreAtom score x) := by
  change MeasurableSet (score ⁻¹' ({score x} : Set ℝ))
  exact hscore (measurableSet_singleton (score x))

theorem measurableSet_tiePrefixInScoreAtom
    {α : Type*} [MeasurableSpace α] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α) :
    MeasurableSet (tiePrefixInScoreAtom score tie x) := by
  have htie_prefix : MeasurableSet {y | tie y ≤ tie x} := by
    change MeasurableSet (tie ⁻¹' Set.Iic (tie x))
    exact htie measurableSet_Iic
  change MeasurableSet ({y | score y = score x} ∩ {y | tie y ≤ tie x})
  exact (measurableSet_scoreAtom hscore x).inter htie_prefix

theorem measurableSet_tieBrokenStrictLowerContour
    {α : Type*} [MeasurableSpace α] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α) :
    MeasurableSet (tieBrokenStrictLowerContour score tie x) := by
  have htie_strict : MeasurableSet {y | tie y < tie x} := by
    change MeasurableSet (tie ⁻¹' Set.Iio (tie x))
    exact htie measurableSet_Iio
  change MeasurableSet ({y | score y < score x} ∪
    ({y | score y = score x} ∩ {y | tie y < tie x}))
  exact (measurableSet_scoreLowerContour hscore x).union
    ((measurableSet_scoreAtom hscore x).inter htie_strict)

theorem measurableSet_exactScoreTieKey
    {α : Type*} [MeasurableSpace α] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α) :
    MeasurableSet (exactScoreTieKey score tie x) := by
  have htie_atom : MeasurableSet {y | tie y = tie x} := by
    change MeasurableSet (tie ⁻¹' ({tie x} : Set ℝ))
    exact htie (measurableSet_singleton (tie x))
  change MeasurableSet ({y | score y = score x} ∩ {y | tie y = tie x})
  exact (measurableSet_scoreAtom hscore x).inter htie_atom

theorem measurableSet_tieBrokenLowerContour
    {α : Type*} [MeasurableSpace α] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α) :
    MeasurableSet (tieBrokenLowerContour score tie x) := by
  exact (measurableSet_scoreLowerContour hscore x).union
    (measurableSet_tiePrefixInScoreAtom hscore htie x)

theorem measurableSet_tieBrokenLowerContourProduct
    {α : Type*} [MeasurableSpace α] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) :
    MeasurableSet
      ({p : α × α |
        score p.2 < score p.1 ∨
          score p.2 = score p.1 ∧ tie p.2 ≤ tie p.1}) := by
  have hscore_fst : Measurable fun p : α × α => score p.1 :=
    hscore.comp measurable_fst
  have hscore_snd : Measurable fun p : α × α => score p.2 :=
    hscore.comp measurable_snd
  have htie_fst : Measurable fun p : α × α => tie p.1 :=
    htie.comp measurable_fst
  have htie_snd : Measurable fun p : α × α => tie p.2 :=
    htie.comp measurable_snd
  have hlt : MeasurableSet {p : α × α | score p.2 < score p.1} :=
    measurableSet_lt hscore_snd hscore_fst
  have heq : MeasurableSet {p : α × α | score p.2 = score p.1} :=
    measurableSet_eq_fun hscore_snd hscore_fst
  have hle : MeasurableSet {p : α × α | tie p.2 ≤ tie p.1} :=
    measurableSet_le htie_snd htie_fst
  simpa [Set.setOf_and, Set.setOf_or] using hlt.union (heq.inter hle)

/--
Source tie-broken rank value: the mass of the tie-broken lower contour.
The remaining hard theorem is that, under the source nonatomic tie-breaking
construction, this map pushes the applicant measure to the uniform rank
measure.
-/
noncomputable def tieBrokenRank
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (score tie : α → ℝ) (x : α) : ℝ :=
  (μ (tieBrokenLowerContour score tie x)).toReal

theorem measurable_tieBrokenRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) :
    Measurable (tieBrokenRank μ score tie) := by
  let contourProduct : Set (α × α) :=
    {p | score p.2 < score p.1 ∨
      score p.2 = score p.1 ∧ tie p.2 ≤ tie p.1}
  have hprod : MeasurableSet contourProduct := by
    simpa [contourProduct] using
      measurableSet_tieBrokenLowerContourProduct hscore htie
  have hsection :
      (fun x => μ (Prod.mk x ⁻¹' contourProduct)) =
        fun x => μ (tieBrokenLowerContour score tie x) := by
    funext x
    rfl
  have hmeas :
      Measurable (fun x => μ (Prod.mk x ⁻¹' contourProduct)) :=
    measurable_measure_prodMk_left hprod
  simpa [tieBrokenRank, hsection] using hmeas.ennreal_toReal

theorem tieBrokenRank_mem_Icc
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (score tie : α → ℝ) (x : α) :
    tieBrokenRank μ score tie x ∈ Set.Icc (0 : ℝ) 1 := by
  have hle_top : μ (tieBrokenLowerContour score tie x) ≤ μ Set.univ :=
    measure_mono (Set.subset_univ _)
  have hle_one :
      (μ (tieBrokenLowerContour score tie x)).toReal ≤ 1 := by
    rw [measure_univ] at hle_top
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hle_top).trans_eq
      ENNReal.toReal_one
  exact ⟨ENNReal.toReal_nonneg, by simpa [tieBrokenRank] using hle_one⟩

theorem tieBrokenRank_map_eq_uniform_of_cdf
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hmeas : Measurable (tieBrokenRank μ score tie))
    (hcdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t)) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine Measure.ext_of_Iic
    (Measure.map (tieBrokenRank μ score tie) μ)
    (volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun t => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic]
  exact hcdf t

theorem tieBrokenRank_cdf_target_of_map_eq_uniform
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score tie : α → ℝ}
    (hmeas : Measurable (tieBrokenRank μ score tie))
    (hmap :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1)) :
    ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) := by
  intro t
  change μ ((tieBrokenRank μ score tie) ⁻¹' Set.Iic t) =
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t)
  rw [← hmap, Measure.map_apply hmeas measurableSet_Iic]

theorem tieBrokenRank_map_eq_uniform_of_ae_eq_uniform_rank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score tie preRank : α → ℝ}
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hrank_eq :
      tieBrokenRank μ score tie =ᵐ[μ] preRank) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  exact (Measure.map_congr hrank_eq).trans hpre_dist

theorem tieBrokenRank_cdf_target_of_ae_eq_uniform_rank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {score tie preRank : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hrank_eq :
      tieBrokenRank μ score tie =ᵐ[μ] preRank) :
    ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) :=
  tieBrokenRank_cdf_target_of_map_eq_uniform
    (measurable_tieBrokenRank hscore_meas htie_meas)
    (tieBrokenRank_map_eq_uniform_of_ae_eq_uniform_rank hpre_dist hrank_eq)

theorem uniformRankTarget_Iic_of_mem_Icc {t : ℝ}
    (_h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) =
      ENNReal.ofReal t := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset :
      Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) t := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.1⟩
    · intro hx
      exact ⟨hx.2, ⟨hx.1, hx.2.trans h1⟩⟩
  rw [hset, Real.volume_Icc, sub_zero]

theorem uniformRankTarget_Iic_of_lt_zero {t : ℝ} (ht : t < 0) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) = 0 := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset :
      Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = (∅ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      exact (not_le_of_gt ht) (hx.2.1.trans hx.1)
    · intro hx
      exact False.elim hx
  rw [hset, measure_empty]

theorem uniformRankTarget_Iic_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) = 1 := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset :
      Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨hx.2.trans ht, hx⟩
  rw [hset, Real.volume_Icc]
  norm_num

theorem tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hrange : ∀ x, tieBrokenRank μ score tie x ∈ Set.Icc (0 : ℝ) 1)
    (hcdf_inside :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) := by
  intro t
  by_cases ht0 : t < 0
  · have hset :
        {x | tieBrokenRank μ score tie x ≤ t} = (∅ : Set α) := by
      ext x
      constructor
      · intro hx
        exact False.elim ((not_le_of_gt ht0) ((hrange x).1.trans hx))
      · intro hx
        exact False.elim hx
    rw [hset, measure_empty, uniformRankTarget_Iic_of_lt_zero ht0]
  · have h0 : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : t ≤ 1
    · rw [hcdf_inside t h0 ht1, uniformRankTarget_Iic_of_mem_Icc h0 ht1]
    · have h1 : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
      have hset :
          {x | tieBrokenRank μ score tie x ≤ t} = Set.univ := by
        ext x
        constructor
        · intro _hx
          exact Set.mem_univ x
        · intro _hx
          exact (hrange x).2.trans h1
      rw [hset, measure_univ, uniformRankTarget_Iic_of_one_le h1]

theorem scalar_cdf_of_self_cdf_on_surjective_unit_interval_rank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {rank : α → ℝ}
    (hsurj : ∀ t, 0 ≤ t → t ≤ 1 → ∃ x, rank x = t)
    (hself :
      ∀ x, μ {y | rank y ≤ rank x} = ENNReal.ofReal (rank x)) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | rank x ≤ t} = ENNReal.ofReal t := by
  intro t ht0 ht1
  rcases hsurj t ht0 ht1 with ⟨x, hx⟩
  simpa [hx] using hself x

/--
Dense-image version of the scalar CDF endpoint.  Exact surjectivity of the
rank map is stronger than the source construction needs: it is enough to
approximate every interior cutoff from below and above by realized rank
values.  The proof squeezes the real value of the sublevel measure between
`t - ε` and `t + ε`.
-/
theorem scalar_cdf_of_self_cdf_on_dense_unit_interval_rank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {rank : α → ℝ}
    (hrange : ∀ x, rank x ∈ Set.Icc (0 : ℝ) 1)
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ rank x ∧ rank x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ rank x ∧ rank x ≤ t + ε)
    (hself :
      ∀ x, μ {y | rank y ≤ rank x} = ENNReal.ofReal (rank x)) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | rank x ≤ t} = ENNReal.ofReal t := by
  intro t ht0 ht1
  let M : ENNReal := μ {x | rank x ≤ t}
  have hM_le_one : M ≤ 1 := by
    rw [← measure_univ (μ := μ)]
    exact measure_mono (Set.subset_univ _)
  have hM_ne_top : M ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hM_le_one
  have hM_lower : t ≤ M.toReal := by
    by_cases htzero : t = 0
    · simpa [htzero] using ENNReal.toReal_nonneg (a := M)
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
      rw [le_iff_forall_pos_lt_add]
      intro ε hε
      have hεhalf : 0 < ε / 2 := by linarith
      rcases hbelow t (ε / 2) htpos ht1 hεhalf with
        ⟨x, hx_lower, hx_upper⟩
      have hsub :
          μ {y | rank y ≤ rank x} ≤ M := by
        exact measure_mono (by
          intro y hy
          exact le_trans hy hx_upper)
      have hx_toReal : rank x ≤ M.toReal := by
        rw [hself x] at hsub
        exact (ENNReal.ofReal_le_iff_le_toReal hM_ne_top).mp hsub
      have ht_lt : t < rank x + ε := by linarith
      have hle : rank x + ε ≤ M.toReal + ε := by linarith
      exact lt_of_lt_of_le ht_lt hle
  have hM_upper : M.toReal ≤ t := by
    by_cases htone : t = 1
    · have hM_real_le_one : M.toReal ≤ 1 := by
        simpa [ENNReal.toReal_one] using
          ENNReal.toReal_mono ENNReal.one_ne_top hM_le_one
      simpa [htone] using hM_real_le_one
    · have htlt : t < 1 := lt_of_le_of_ne ht1 htone
      rw [le_iff_forall_pos_lt_add]
      intro ε hε
      have hεhalf : 0 < ε / 2 := by linarith
      rcases habove t (ε / 2) ht0 htlt hεhalf with
        ⟨x, hx_lower, hx_upper⟩
      have hsub :
          M ≤ μ {y | rank y ≤ rank x} := by
        exact measure_mono (by
          intro y hy
          exact le_trans hy hx_lower)
      have hx_nonneg : 0 ≤ rank x := (hrange x).1
      have hM_toReal_le : M.toReal ≤ rank x := by
        rw [hself x] at hsub
        exact ENNReal.toReal_le_of_le_ofReal hx_nonneg hsub
      have hx_lt : rank x < t + ε := by linarith
      exact lt_of_le_of_lt hM_toReal_le hx_lt
  have hM_real_eq : M.toReal = t := le_antisymm hM_upper hM_lower
  change M = ENNReal.ofReal t
  rw [← ENNReal.ofReal_toReal hM_ne_top, hM_real_eq]

/--
Interval-density version of the approximation hypotheses used by the dense
PIT endpoint.  The source atom-filling argument naturally says that every
open rank interval contains realized ranks; this lemma turns that into the
one-sided approximations needed for the scalar CDF squeeze.
-/
theorem dense_unit_interval_rank_yields_one_sided_approximations
    {α : Type*} {rank : α → ℝ}
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < rank x ∧ rank x < b) :
    (∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
      ∃ x, t - ε ≤ rank x ∧ rank x ≤ t) ∧
    (∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
      ∃ x, t ≤ rank x ∧ rank x ≤ t + ε) := by
  constructor
  · intro t ε htpos htle hε
    let a : ℝ := max 0 (t - ε)
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact le_max_left 0 (t - ε)
    have hat : a < t := by
      dsimp [a]
      rw [max_lt_iff]
      exact ⟨htpos, by linarith⟩
    rcases hdense a t ha0 hat htle with ⟨x, hax, hxt⟩
    refine ⟨x, ?_, le_of_lt hxt⟩
    have hbase : t - ε ≤ a := by
      dsimp [a]
      exact le_max_right 0 (t - ε)
    exact le_trans hbase (le_of_lt hax)
  · intro t ε ht0 htlt hε
    let b : ℝ := min 1 (t + ε)
    have htb : t < b := by
      dsimp [b]
      rw [lt_min_iff]
      exact ⟨htlt, by linarith⟩
    have hb1 : b ≤ 1 := by
      dsimp [b]
      exact min_le_left 1 (t + ε)
    rcases hdense t b ht0 htb hb1 with ⟨x, htx, hxb⟩
    refine ⟨x, le_of_lt htx, ?_⟩
    have hb : b ≤ t + ε := by
      dsimp [b]
      exact min_le_right 1 (t + ε)
    exact le_trans (le_of_lt hxb) hb

/--
Dense-open-interval version of the scalar CDF endpoint.  This is equivalent
to the source statement that atom filling makes the realized rank image dense
in each gap interval.
-/
theorem scalar_cdf_of_self_cdf_on_interval_dense_unit_interval_rank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {rank : α → ℝ}
    (hrange : ∀ x, rank x ∈ Set.Icc (0 : ℝ) 1)
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < rank x ∧ rank x < b)
    (hself :
      ∀ x, μ {y | rank y ≤ rank x} = ENNReal.ofReal (rank x)) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | rank x ≤ t} = ENNReal.ofReal t := by
  rcases dense_unit_interval_rank_yields_one_sided_approximations
      (rank := rank) hdense with ⟨hbelow, habove⟩
  exact scalar_cdf_of_self_cdf_on_dense_unit_interval_rank
    hrange hbelow habove hself

theorem tieBrokenRank_scalar_cdf_of_self_cdf_on_surjective_unit_interval
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score tie : α → ℝ}
    (hsurj :
      ∀ t, 0 ≤ t → t ≤ 1 →
        ∃ x, tieBrokenRank μ score tie x = t)
    (hself :
      ∀ x, μ {y | tieBrokenRank μ score tie y ≤
        tieBrokenRank μ score tie x} =
          ENNReal.ofReal (tieBrokenRank μ score tie x)) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  scalar_cdf_of_self_cdf_on_surjective_unit_interval_rank hsurj hself

/--
Dense-image version for the source tie-broken rank.  This is the preferred
gamma/PIT endpoint for the paper construction: atom filling only has to
produce realized ranks arbitrarily close to each interior cutoff.
-/
theorem tieBrokenRank_scalar_cdf_of_self_cdf_on_dense_unit_interval
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t + ε)
    (hself :
      ∀ x, μ {y | tieBrokenRank μ score tie y ≤
        tieBrokenRank μ score tie x} =
          ENNReal.ofReal (tieBrokenRank μ score tie x)) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  scalar_cdf_of_self_cdf_on_dense_unit_interval_rank
    (fun x => tieBrokenRank_mem_Icc score tie x) hbelow habove hself

/--
Open-interval-density version for the source tie-broken rank.  Downstream
paper statements can now ask for the natural dense-image fact directly.
-/
theorem tieBrokenRank_scalar_cdf_of_self_cdf_on_interval_dense_unit_interval
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hself :
      ∀ x, μ {y | tieBrokenRank μ score tie y ≤
        tieBrokenRank μ score tie x} =
          ENNReal.ofReal (tieBrokenRank μ score tie x)) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  scalar_cdf_of_self_cdf_on_interval_dense_unit_interval_rank
    (fun x => tieBrokenRank_mem_Icc score tie x) hdense hself

theorem tieBrokenRank_self_cdf_of_sublevel_eq_lowerContour
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    ∀ x, μ {y | tieBrokenRank μ score tie y ≤
        tieBrokenRank μ score tie x} =
          ENNReal.ofReal (tieBrokenRank μ score tie x) := by
  intro x
  rw [hsublevel x, tieBrokenRank]
  exact (ENNReal.ofReal_toReal (measure_ne_top μ
    (tieBrokenLowerContour score tie x))).symm

theorem tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_surjective
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hsurj :
      ∀ t, 0 ≤ t → t ≤ 1 →
        ∃ x, tieBrokenRank μ score tie x = t)
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_self_cdf_on_surjective_unit_interval
    hsurj
    (tieBrokenRank_self_cdf_of_sublevel_eq_lowerContour hsublevel)

theorem tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t + ε)
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_self_cdf_on_dense_unit_interval
    hbelow habove
    (tieBrokenRank_self_cdf_of_sublevel_eq_lowerContour hsublevel)

theorem tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_self_cdf_on_interval_dense_unit_interval
    hdense
    (tieBrokenRank_self_cdf_of_sublevel_eq_lowerContour hsublevel)

theorem tieBrokenRank_map_eq_uniform_of_sublevel_eq_lowerContour_and_surjective
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hsurj :
      ∀ t, 0 ≤ t → t ≤ 1 →
        ∃ x, tieBrokenRank μ score tie x = t)
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine tieBrokenRank_map_eq_uniform_of_cdf
    (measurable_tieBrokenRank hscore_meas htie_meas) ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x)
    (tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_surjective
      hsurj hsublevel)

theorem tieBrokenRank_map_eq_uniform_of_sublevel_eq_lowerContour_and_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t + ε)
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine tieBrokenRank_map_eq_uniform_of_cdf
    (measurable_tieBrokenRank hscore_meas htie_meas) ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x)
    (tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_dense
      hbelow habove hsublevel)

theorem tieBrokenRank_map_eq_uniform_of_sublevel_eq_lowerContour_and_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hsublevel :
      ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
        tieBrokenLowerContour score tie x) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine tieBrokenRank_map_eq_uniform_of_cdf
    (measurable_tieBrokenRank hscore_meas htie_meas) ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x)
    (tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_interval_dense
      hdense hsublevel)

theorem tieBrokenRank_eq_preRank_of_lowerContour_eq_preRank_Iic
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    ∀ x, tieBrokenRank μ score tie x = preRank x := by
  intro x
  have hmeasure :
      μ (tieBrokenLowerContour score tie x) =
        ENNReal.ofReal (preRank x) := by
    rw [hcontour x]
    have hmap :
        μ {y | preRank y ≤ preRank x} =
          Measure.map preRank μ (Set.Iic (preRank x)) := by
      change μ (preRank ⁻¹' Set.Iic (preRank x)) =
        Measure.map preRank μ (Set.Iic (preRank x))
      exact (Measure.map_apply hpreRank_meas measurableSet_Iic).symm
    rw [hmap, hpre_dist]
    exact uniformRankTarget_Iic_of_mem_Icc (hpre_range x).1 (hpre_range x).2
  rw [tieBrokenRank, hmeasure]
  exact ENNReal.toReal_ofReal (hpre_range x).1

/-- A source-uniform pre-rank has no positive-mass point fibers. -/
theorem measure_preRank_fiber_eq_zero_of_uniform
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (x : α) :
    μ {y | preRank y = preRank x} = 0 := by
  have hmap :
      μ {y | preRank y = preRank x} =
        Measure.map preRank μ ({preRank x} : Set ℝ) := by
    change μ (preRank ⁻¹' ({preRank x} : Set ℝ)) =
      Measure.map preRank μ ({preRank x} : Set ℝ)
    exact (Measure.map_apply hpreRank_meas
      (measurableSet_singleton (preRank x))).symm
  rw [hmap, hpre_dist]
  rw [Measure.restrict_apply (measurableSet_singleton (preRank x))]
  exact measure_mono_null Set.inter_subset_left
    (by simp : (volume : Measure ℝ) ({preRank x} : Set ℝ) = 0)

/--
If strict score order agrees with strict pre-rank order, then arbitrary
tie-breaking can only change the lower contour on the zero-mass pre-rank fiber.
Thus the lower-contour mass is the same as the source pre-rank lower tail.
-/
theorem measure_tieBrokenLowerContour_eq_preRank_Iic_of_strict_score_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hscore_order :
      ∀ x y, score y < score x ↔ preRank y < preRank x) :
    ∀ x, μ (tieBrokenLowerContour score tie x) =
      μ {y | preRank y ≤ preRank x} := by
  intro x
  let A := tieBrokenLowerContour score tie x
  let B := {y | preRank y ≤ preRank x}
  have hA_meas : MeasurableSet A :=
    measurableSet_tieBrokenLowerContour hscore_meas htie_meas x
  have hB_meas : MeasurableSet B := by
    change MeasurableSet (preRank ⁻¹' Set.Iic (preRank x))
    exact hpreRank_meas measurableSet_Iic
  have hsubset : A ⊆ B := by
    intro y hy
    rcases hy with hscore_lt | hsame
    · exact le_of_lt ((hscore_order x y).1 hscore_lt)
    · by_contra hnot
      have hpre_gt : preRank x < preRank y := lt_of_not_ge hnot
      have hscore_gt : score x < score y := (hscore_order y x).2 hpre_gt
      exact (ne_of_lt hscore_gt) hsame.1.symm
  have hdiff_subset :
      B \ A ⊆ {y | preRank y = preRank x} := by
    intro y hy
    have hyB : preRank y ≤ preRank x := hy.1
    have hyA_not : y ∉ A := hy.2
    rcases lt_or_eq_of_le hyB with hlt | heq
    · have hscore_lt : score y < score x := (hscore_order x y).2 hlt
      exact False.elim (hyA_not (Or.inl hscore_lt))
    · exact heq
  have hdiff_zero : μ (B \ A) = 0 :=
    measure_mono_null hdiff_subset
      (measure_preRank_fiber_eq_zero_of_uniform hpreRank_meas hpre_dist x)
  have hB_union : B = A ∪ (B \ A) := by
    ext y
    constructor
    · intro hyB
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · exact Or.inr ⟨hyB, hyA⟩
    · intro hy
      rcases hy with hyA | hyDiff
      · exact hsubset hyA
      · exact hyDiff.1
  have hdisjoint : Disjoint A (B \ A) := by
    rw [Set.disjoint_left]
    intro y hyA hyDiff
    exact hyDiff.2 hyA
  have hdiff_meas : MeasurableSet (B \ A) := hB_meas.diff hA_meas
  have hmeasure :
      μ B = μ A + μ (B \ A) := by
    calc
      μ B = μ (A ∪ (B \ A)) := congrArg μ hB_union
      _ = μ A + μ (B \ A) := measure_union hdisjoint hdiff_meas
  rw [hdiff_zero, add_zero] at hmeasure
  exact hmeasure.symm

/--
Strict source score order is enough to identify the tie-broken rank with the
source pre-rank. Arbitrary tie-breaking only affects the null pre-rank fiber.
-/
theorem tieBrokenRank_eq_preRank_of_strict_score_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_order :
      ∀ x y, score y < score x ↔ preRank y < preRank x) :
    ∀ x, tieBrokenRank μ score tie x = preRank x := by
  intro x
  have hmeasure :
      μ (tieBrokenLowerContour score tie x) =
        ENNReal.ofReal (preRank x) := by
    rw [measure_tieBrokenLowerContour_eq_preRank_Iic_of_strict_score_order
      hpreRank_meas hscore_meas htie_meas hpre_dist hscore_order]
    have hmap :
        μ {y | preRank y ≤ preRank x} =
          Measure.map preRank μ (Set.Iic (preRank x)) := by
      change μ (preRank ⁻¹' Set.Iic (preRank x)) =
        Measure.map preRank μ (Set.Iic (preRank x))
      exact (Measure.map_apply hpreRank_meas measurableSet_Iic).symm
    rw [hmap, hpre_dist]
    exact uniformRankTarget_Iic_of_mem_Icc (hpre_range x).1 (hpre_range x).2
  rw [tieBrokenRank, hmeasure]
  exact ENNReal.toReal_ofReal (hpre_range x).1

/--
Scalar CDF version of the strict-score-order special case. This avoids a
general atom-filling PIT theorem when the source score has no positive-mass
flat regions except null pre-rank fibers.
-/
theorem tieBrokenRank_scalar_cdf_of_strict_score_order_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_order :
      ∀ x y, score y < score x ↔ preRank y < preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t := by
  have hrank_eq :
      ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_strict_score_order
      hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range hscore_order
  intro t ht0 ht1
  have hset :
      {x | tieBrokenRank μ score tie x ≤ t} =
        {x | preRank x ≤ t} := by
    ext x
    simp [hrank_eq x]
  rw [hset]
  have hmap :
      μ {x | preRank x ≤ t} =
        Measure.map preRank μ (Set.Iic t) := by
    change μ (preRank ⁻¹' Set.Iic t) =
      Measure.map preRank μ (Set.Iic t)
    exact (Measure.map_apply hpreRank_meas measurableSet_Iic).symm
  rw [hmap, hpre_dist]
  exact uniformRankTarget_Iic_of_mem_Icc ht0 ht1

theorem tieBrokenRank_scalar_cdf_of_lowerContour_eq_preRank_Iic
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t := by
  have hrank_eq :
      ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_lowerContour_eq_preRank_Iic
      hpreRank_meas hpre_dist hpre_range hcontour
  intro t ht0 ht1
  have hset :
      {x | tieBrokenRank μ score tie x ≤ t} =
        {x | preRank x ≤ t} := by
    ext x
    simp [hrank_eq x]
  rw [hset]
  have hmap :
      μ {x | preRank x ≤ t} =
        Measure.map preRank μ (Set.Iic t) := by
    change μ (preRank ⁻¹' Set.Iic t) =
      Measure.map preRank μ (Set.Iic t)
    exact (Measure.map_apply hpreRank_meas measurableSet_Iic).symm
  rw [hmap, hpre_dist]
  exact uniformRankTarget_Iic_of_mem_Icc ht0 ht1

theorem tieBrokenRank_map_eq_uniform_of_lowerContour_eq_preRank_Iic
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine tieBrokenRank_map_eq_uniform_of_cdf
    (measurable_tieBrokenRank hscore_meas htie_meas) ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x)
    (tieBrokenRank_scalar_cdf_of_lowerContour_eq_preRank_Iic
      hpreRank_meas hpre_dist hpre_range hcontour)

theorem tieBrokenLowerContour_eq_preRank_Iic_of_lex_order
    {α : Type*} {preRank score tie : α → ℝ}
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    ∀ x, tieBrokenLowerContour score tie x =
      {y | preRank y ≤ preRank x} := by
  intro x
  ext y
  exact hlex x y

theorem tieBrokenRank_map_eq_uniform_of_lex_order_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) :=
  tieBrokenRank_map_eq_uniform_of_lowerContour_eq_preRank_Iic
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    (tieBrokenLowerContour_eq_preRank_Iic_of_lex_order hlex)

theorem tieBrokenLex_order_iff_preRank_of_score_tie_order
    {α : Type*} {preRank score tie : α → ℝ}
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_mono :
      ∀ x y, preRank y ≤ preRank x → tie y ≤ tie x)
    (htie_reflect_same_score :
      ∀ x y, score y = score x → tie y ≤ tie x → preRank y ≤ preRank x) :
    ∀ x y,
      (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
        preRank y ≤ preRank x := by
  intro x y
  constructor
  · intro hlex
    rcases hlex with hscore_lt | hsame
    · exact hscore_reflect x y hscore_lt
    · exact htie_reflect_same_score x y hsame.1 hsame.2
  · intro hpre
    have hscore_le : score y ≤ score x := hscore_mono x y hpre
    rcases lt_or_eq_of_le hscore_le with hscore_lt | hscore_eq
    · exact Or.inl hscore_lt
    · exact Or.inr ⟨hscore_eq, htie_mono x y hpre⟩

theorem tieBrokenRank_map_eq_uniform_of_score_tie_order_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_mono :
      ∀ x y, preRank y ≤ preRank x → tie y ≤ tie x)
    (htie_reflect_same_score :
      ∀ x y, score y = score x → tie y ≤ tie x → preRank y ≤ preRank x) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) :=
  tieBrokenRank_map_eq_uniform_of_lex_order_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    (tieBrokenLex_order_iff_preRank_of_score_tie_order
      hscore_mono hscore_reflect htie_mono htie_reflect_same_score)

theorem tieBrokenRank_map_eq_uniform_of_score_order_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_eq : ∀ x, tie x = preRank x) :
    Measure.map (tieBrokenRank μ score tie) μ =
      volume.restrict (Set.Icc (0 : ℝ) 1) :=
  tieBrokenRank_map_eq_uniform_of_score_tie_order_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono hscore_reflect
    (fun x y hpre => by simpa [htie_eq x, htie_eq y] using hpre)
    (fun x y _hscore htie_le => by simpa [htie_eq x, htie_eq y] using htie_le)

/--
Pointwise version of the source pre-rank tie-key endpoint.  Once the
score/tie lexicographic lower contour is the initial segment of the uniform
source pre-rank, the source tie-broken rank equals the source pre-rank
pointwise.  This lets downstream source-tie bridges derive post-rank level
bounds instead of assuming them separately.
-/
theorem tieBrokenRank_eq_preRank_of_score_order_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ x, tieBrokenRank μ score tie x = preRank x :=
  tieBrokenRank_eq_preRank_of_lowerContour_eq_preRank_Iic
    hpreRank_meas hpre_dist hpre_range
    (tieBrokenLowerContour_eq_preRank_Iic_of_lex_order
      (tieBrokenLex_order_iff_preRank_of_score_tie_order
        hscore_mono hscore_reflect
        (fun x y hpre => by simpa [htie_eq x, htie_eq y] using hpre)
        (fun x y _hscore htie_le => by
          simpa [htie_eq x, htie_eq y] using htie_le)))

/--
Monotone-score specialization of
`tieBrokenRank_eq_preRank_of_score_order_and_tie_eq_preRank`.  Strict
score-order reflection is derived from monotonicity, matching the source route
where scores are weakly ordered by the original rank and ties are broken by
the original rank label.
-/
theorem tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ x, tieBrokenRank μ score tie x = preRank x :=
  tieBrokenRank_eq_preRank_of_score_order_and_tie_eq_preRank
    hpreRank_meas hpre_dist hpre_range hscore_mono
    (fun x y hscore_lt => by
      by_contra hnot
      have hpre : preRank x < preRank y := lt_of_not_ge hnot
      have hscore_le : score x ≤ score y := hscore_mono y x (le_of_lt hpre)
      exact not_lt_of_ge hscore_le hscore_lt)
    htie_eq

theorem tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t := by
  have hmap :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_score_order_and_tie_eq_preRank
      hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
      hscore_mono hscore_reflect htie_eq
  have hcdf :=
    tieBrokenRank_cdf_target_of_map_eq_uniform
      (measurable_tieBrokenRank hscore_meas htie_meas) hmap
  intro t ht0 ht1
  rw [hcdf t]
  exact uniformRankTarget_Iic_of_mem_Icc ht0 ht1

/--
If score is monotone in the source pre-rank order, then strict score
improvement reflects the same pre-rank order.  This removes a redundant
premise from source-ordered gamma wrappers.
-/
theorem score_reflect_of_preRank_score_mono
    {α : Type*} {preRank score : α → ℝ}
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x) :
    ∀ x y, score y < score x → preRank y ≤ preRank x := by
  intro x y hscore_lt
  by_contra hnot
  have hpre : preRank x < preRank y := lt_of_not_ge hnot
  have hscore_le : score x ≤ score y := hscore_mono y x (le_of_lt hpre)
  exact not_lt_of_ge hscore_le hscore_lt

/--
Source-ordered gamma endpoint with the public tie key equal to the source
pre-rank and only monotonicity of score in pre-rank.  The strict-reflection
premise is derived in Lean.
-/
theorem tieBrokenRank_scalar_cdf_of_score_mono_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono (score_reflect_of_preRank_score_mono hscore_mono) htie_eq

theorem rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_cdf
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_cdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t)) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpostRank_meas : Measurable (tieBrokenRank μ score tie) :=
    measurable_tieBrokenRank hscore_meas htie_meas
  have hpost_dist :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_cdf hpostRank_meas hgamma_cdf
  have hrank_dist :
      Measure.map preRank μ =
        Measure.map (tieBrokenRank μ score tie) μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} =
          Measure.map
            (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail := by
      change μ ((fun x => rankLevel (tieBrokenRank μ score tie x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail
      exact (Measure.map_apply (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibrium_deviation_rank_facts_and_equal_rank_tail_measures
      K preRank (tieBrokenRank μ score tie) rankOfEffort rankLevel rankSkill
      skill score effort levelReward hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hbest hpost_actual hequal_score_level
      hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

/--
Tie-broken-rank rank-preservation bridge using source reward reachability
rather than exact equal-score deviation ranks.  This is the same CDF route as
`rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_cdf`, but the
source-specific deviation premise says that reaching another applicant's score
is enough to reach that applicant's reward.
-/
theorem rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_cdf_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_cdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t)) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpostRank_meas : Measurable (tieBrokenRank μ score tie) :=
    measurable_tieBrokenRank hscore_meas htie_meas
  have hpost_dist :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_cdf hpostRank_meas hgamma_cdf
  have hrank_dist :
      Measure.map preRank μ =
        Measure.map (tieBrokenRank μ score tie) μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} =
          Measure.map
            (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail := by
      change μ ((fun x => rankLevel (tieBrokenRank μ score tie x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail
      exact (Measure.map_apply (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibrium_deviation_reward_facts_and_equal_rank_tail_measures
      K preRank (tieBrokenRank μ score tie) rankOfEffort rankLevel rankSkill
      skill score effort levelReward hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hbest hpost_actual hdeviation_reaches_reward
      hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

theorem rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x) hgamma_scalar_cdf

/--
Scalar-CDF form of the source reward-reachability rank-preservation bridge.
Use this when the gamma/PIT work supplies the scalar uniform CDF target rather
than the full uniform-measure CDF statement.
-/
theorem rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_cdf_reward_reach
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual hdeviation_reaches_reward hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x) hgamma_scalar_cdf

/--
Scalar-CDF gamma bridge in rank-reach form.  The source-specific deviation
premise is stated directly as a rank comparison; monotonicity of the rank
levels and rewards derives the reward-reachability needed by the payoff
argument.
-/
theorem rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf_rank_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hrankLevel_mono : Monotone rankLevel)
    (hlevelReward_mono : Monotone levelReward)
    (hrank_reaches :
      ∀ x y d, score y ≤ g d * skill x →
        tieBrokenRank μ score tie y ≤ rankOfEffort x d)
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf_reward_reach
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual
    (deviation_reward_reach_of_rank_reach
      hrankLevel_mono hlevelReward_mono hrank_reaches)
    hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
    hgamma_scalar_cdf

theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_cdf
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_cdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t)) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpostRank_meas : Measurable (tieBrokenRank μ score tie) :=
    measurable_tieBrokenRank hscore_meas htie_meas
  have hpost_dist :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_cdf hpostRank_meas hgamma_cdf
  have hrank_dist :
      Measure.map preRank μ =
        Measure.map (tieBrokenRank μ score tie) μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} =
          Measure.map
            (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail := by
      change μ ((fun x => rankLevel (tieBrokenRank μ score tie x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail
      exact (Measure.map_apply (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_and_equal_rank_tail_measures
      K preRank (tieBrokenRank μ score tie) rankOfEffort rankLevel rankSkill
      skill score effort levelReward hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hbestAE hpost_actual hequal_score_level
      hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
    (fun x => tieBrokenRank_mem_Icc score tie x) hgamma_scalar_cdf

/--
Almost-everywhere-post-rank version of the scalar-CDF bridge.  The source
equilibrium only requires the realized post-rank relation almost everywhere,
so this theorem avoids strengthening that model condition to pointwise equality.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpostRank_meas : Measurable (tieBrokenRank μ score tie) :=
    measurable_tieBrokenRank hscore_meas htie_meas
  have hgamma_cdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) :=
    tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
      (fun x => tieBrokenRank_mem_Icc score tie x) hgamma_scalar_cdf
  have hpost_dist :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_cdf hpostRank_meas hgamma_cdf
  have hrank_dist :
      Measure.map preRank μ =
        Measure.map (tieBrokenRank μ score tie) μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} =
          Measure.map
            (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail := by
      change μ ((fun x => rankLevel (tieBrokenRank μ score tie x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_ae_post_actual_and_equal_rank_tail_measures
      K preRank (tieBrokenRank μ score tie) rankOfEffort rankLevel rankSkill
      skill score effort levelReward hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hbestAE hpost_actual_ae
      hequal_score_level hpreRank_meas hpostRank_meas hrankLevel_meas
      htail_measure

/--
Almost-everywhere-post-rank scalar-CDF bridge using reward reachability rather
than exact equal-score deviation rank facts.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpostRank_meas : Measurable (tieBrokenRank μ score tie) :=
    measurable_tieBrokenRank hscore_meas htie_meas
  have hgamma_cdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) :=
    tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
      (fun x => tieBrokenRank_mem_Icc score tie x) hgamma_scalar_cdf
  have hpost_dist :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_cdf hpostRank_meas hgamma_cdf
  have hrank_dist :
      Measure.map preRank μ =
        Measure.map (tieBrokenRank μ score tie) μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} =
          Measure.map
            (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail := by
      change μ ((fun x => rankLevel (tieBrokenRank μ score tie x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_reward_facts_ae_post_actual_and_equal_rank_tail_measures
      K preRank (tieBrokenRank μ score tie) rankOfEffort rankLevel rankSkill
      skill score effort levelReward hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hbestAE hpost_actual_ae
      hdeviation_reaches_reward hpreRank_meas hpostRank_meas
      hrankLevel_meas htail_measure

/--
Scalar-CDF bridge where reward reachability may use the target applicant's
off-null realized post-rank equality.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_local_post_actual_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hdeviation_reaches_reward :
      ∀ x y d,
        rankLevel (rankOfEffort y (effort y)) =
          rankLevel (tieBrokenRank μ score tie y) →
        score y ≤ g d * skill x →
          levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
            levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpostRank_meas : Measurable (tieBrokenRank μ score tie) :=
    measurable_tieBrokenRank hscore_meas htie_meas
  have hgamma_cdf :
      ∀ t, μ {x | tieBrokenRank μ score tie x ≤ t} =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) :=
    tieBrokenRank_cdf_target_of_unit_interval_scalar_cdf
      (fun x => tieBrokenRank_mem_Icc score tie x) hgamma_scalar_cdf
  have hpost_dist :
      Measure.map (tieBrokenRank μ score tie) μ =
        volume.restrict (Set.Icc (0 : ℝ) 1) :=
    tieBrokenRank_map_eq_uniform_of_cdf hpostRank_meas hgamma_cdf
  have hrank_dist :
      Measure.map preRank μ =
        Measure.map (tieBrokenRank μ score tie) μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (tieBrokenRank μ score tie x)} =
          Measure.map
            (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail := by
      change μ ((fun x => rankLevel (tieBrokenRank μ score tie x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (tieBrokenRank μ score tie x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_reward_facts_local_post_actual_and_equal_rank_tail_measures
      K preRank (tieBrokenRank μ score tie) rankOfEffort rankLevel rankSkill
      skill score effort levelReward hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hbestAE hpost_actual_ae
      hdeviation_reaches_reward hpreRank_meas hpostRank_meas
      hrankLevel_meas htail_measure

theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_strict_score_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_order :
      ∀ x y, score y < score x ↔ preRank y < preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist
    (tieBrokenRank_scalar_cdf_of_strict_score_order_preRank
      hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range hscore_order)

/--
Almost-everywhere-post-rank version of the strict-score source-order bridge.
The source equilibrium only identifies realized ranks almost everywhere.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_strict_score_order_ae_post_actual
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_order :
      ∀ x y, score y < score x ↔ preRank y < preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist
    (tieBrokenRank_scalar_cdf_of_strict_score_order_preRank
      hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range hscore_order)

theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono hscore_reflect htie_eq

/--
Almost-everywhere-post-rank version of the score-order source-tie bridge.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_order_tie_eq_preRank_ae_post_actual
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono hscore_reflect htie_eq

/--
Monotone-score version of the source pre-rank tie-key bridge.  It derives
strict score-order reflection from score monotonicity instead of requiring it
as a separate premise.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_order_tie_eq_preRank
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono
    (score_reflect_of_preRank_score_mono hscore_mono) htie_eq

/--
Almost-everywhere-post-rank version of the monotone-score source-tie bridge.
This matches source equilibrium statements where realized post-rank equality is
allowed to fail on a null boundary/tie set.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono (score_reflect_of_preRank_score_mono hscore_mono) htie_eq

/--
Almost-everywhere-post-rank monotone-score source-tie bridge using reward
reachability rather than exact equal-score deviation rank facts.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual_reward_reach
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hdeviation_reaches_reward hpreRank_meas
      hscore_meas htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono (score_reflect_of_preRank_score_mono hscore_mono) htie_eq

/--
Monotone-score source-tie bridge where reward reachability may use the target
applicant's off-null realized post-rank equality.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_local_post_actual_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hdeviation_reaches_reward :
      ∀ x y d,
        rankLevel (rankOfEffort y (effort y)) =
          rankLevel (tieBrokenRank μ score tie y) →
        score y ≤ g d * skill x →
          levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
            levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_local_post_actual_reward_reach
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hdeviation_reaches_reward hpreRank_meas
      hscore_meas htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono (score_reflect_of_preRank_score_mono hscore_mono) htie_eq

/--
Source-tie score-monotone bridge without a separate post-rank boundedness
premise.  Since the tie-broken rank equals the source pre-rank in this route,
the post-bound follows mechanically from the pre-bound.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Almost-everywhere post-rank variant of
`rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_no_post_bound`.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Multidimensional fixed-budget linear-score bridge for source Proposition
`prop:linearg`.  After the source reduction has identified a combined
pre-effort index and a rank variable ordered by that index, and after
fixed-budget best-coordinate effort makes the realized weighted score equal to
a nonnegative scalar multiple of the index, the one-dimensional
rank-preservation theorem applies.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_multidim_linear_fixed_budget
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie scalarEffort : α → ℝ) (levelReward : ℕ → ℝ)
    (combinedIndex : α → ℝ) (best : α → ι)
    (weight effortBySkill : α → ι → ℝ) {h total : ℝ}
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ scalarEffort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward
        scalarEffort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (scalarEffort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hindex_order :
      ∀ x y, preRank y ≤ preRank x → combinedIndex y ≤ combinedIndex x)
    (hscale_nonneg : 0 ≤ h * total)
    (hbest :
      ∀ x, weight x (best x) = combinedIndex x)
    (heffortBySkill :
      ∀ x i, effortBySkill x i = if i = best x then total else 0)
    (hweightedScore :
      ∀ x, score x = h * ∑ i, effortBySkill x i * weight x i)
    (hscore_eq :
      ∀ x, score x = g (scalarEffort x) * skill x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_combined :
      ∀ x, score x = h * total * combinedIndex x :=
    multidim_linear_fixed_budget_best_coordinate_score_eq
      h total best weight effortBySkill combinedIndex score
      hbest heffortBySkill hweightedScore
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    intro x y hpre
    exact
      multidim_linear_fixed_budget_score_mono_of_combined_index
        hscale_nonneg hscore_combined x y (hindex_order x y hpre)
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie scalarEffort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Almost-everywhere-post-rank version of the multidimensional fixed-budget
linear-score bridge.  This is the source-shaped statement for Proposition
`prop:linearg`, since the source equilibrium records realized post ranks only
almost everywhere.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_multidim_linear_fixed_budget_ae_post_actual
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie scalarEffort : α → ℝ) (levelReward : ℕ → ℝ)
    (combinedIndex : α → ℝ) (best : α → ι)
    (weight effortBySkill : α → ι → ℝ) {h total : ℝ}
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ scalarEffort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward
        scalarEffort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (scalarEffort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hindex_order :
      ∀ x y, preRank y ≤ preRank x → combinedIndex y ≤ combinedIndex x)
    (hscale_nonneg : 0 ≤ h * total)
    (hbest :
      ∀ x, weight x (best x) = combinedIndex x)
    (heffortBySkill :
      ∀ x i, effortBySkill x i = if i = best x then total else 0)
    (hweightedScore :
      ∀ x, score x = h * ∑ i, effortBySkill x i * weight x i)
    (hscore_eq :
      ∀ x, score x = g (scalarEffort x) * skill x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_combined :
      ∀ x, score x = h * total * combinedIndex x :=
    multidim_linear_fixed_budget_best_coordinate_score_eq
      h total best weight effortBySkill combinedIndex score
      hbest heffortBySkill hweightedScore
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    intro x y hpre
    exact
      multidim_linear_fixed_budget_score_mono_of_combined_index
        hscale_nonneg hscore_combined x y (hindex_order x y hpre)
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie scalarEffort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Source-contour version of the almost-everywhere rank-preservation bridge.
Instead of assuming the scalar CDF of the source `gamma` map directly, it is
enough to identify the source tie-broken lower contour with the initial
segment of a uniform pre-rank. This is the structural probability-integral
transform endpoint used by the source construction.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_lowerContour_eq_preRank_Iic
    hpreRank_meas hpre_dist hpre_range hcontour

/--
Almost-everywhere-post-rank version of the source-contour bridge.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours_ae_post_actual
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_lowerContour_eq_preRank_Iic
    hpreRank_meas hpre_dist hpre_range hcontour

/--
Source-contour rank-preservation bridge without a separate post-rank bound.
Once the tie-broken lower contour is the source pre-rank initial segment, Lean
derives `tieBrokenRank = preRank`, so the post-rank level bound follows from
the pre-rank level bound.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_lowerContour_eq_preRank_Iic
        hpreRank_meas hpre_dist hpre_range hcontour
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hcontour

/--
Almost-everywhere-post-rank version of
`rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours_no_post_bound`.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours_ae_post_actual_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hcontour :
      ∀ x, tieBrokenLowerContour score tie x =
        {y | preRank y ≤ preRank x}) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_lowerContour_eq_preRank_Iic
        hpreRank_meas hpre_dist hpre_range hcontour
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hcontour

/--
Order-based source-contour version.  If the source pre-rank orders applicants
exactly as the score/tie lexicographic key, the lower-contour condition needed
for the preceding theorem follows directly.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hpre_range
    (tieBrokenLowerContour_eq_preRank_Iic_of_lex_order hlex)

/--
Almost-everywhere-post-rank version of the lexicographic source-contour bridge.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_preRank_ae_post_actual
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_preRank_contours_ae_post_actual
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hpre_range
    (tieBrokenLowerContour_eq_preRank_Iic_of_lex_order hlex)

theorem tieBrokenRank_eq_score_lower_add_tie_prefix
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α) :
    tieBrokenRank μ score tie x =
      (μ (scoreLowerContour score x)).toReal
        + (μ (tiePrefixInScoreAtom score tie x)).toReal := by
  have hdisjoint :
      Disjoint (scoreLowerContour score x) (tiePrefixInScoreAtom score tie x) := by
    rw [Set.disjoint_left]
    intro y hlt heq
    exact (ne_of_lt hlt) heq.1
  have hmeas_lower := measurableSet_scoreLowerContour hscore x
  have hmeas_prefix := measurableSet_tiePrefixInScoreAtom hscore htie x
  have hmeasure :
      μ (tieBrokenLowerContour score tie x) =
        μ (scoreLowerContour score x) + μ (tiePrefixInScoreAtom score tie x) := by
    rw [tieBrokenLowerContour, scoreLowerContour, tiePrefixInScoreAtom]
    exact measure_union hdisjoint hmeas_prefix
  rw [tieBrokenRank, hmeasure]
  exact ENNReal.toReal_add
    (measure_ne_top μ (scoreLowerContour score x))
    (measure_ne_top μ (tiePrefixInScoreAtom score tie x))

/--
The tie-broken rank of a point always lies between the strict lower-score mass
and the strict lower-score mass plus the entire score atom.  This is the
mechanical part of the source tie-breaking argument; only the statement that
score atoms do not cross reward-level boundaries is model-specific.
-/
theorem tieBrokenRank_mem_score_atom_interval
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α) :
    (μ (scoreLowerContour score x)).toReal ≤ tieBrokenRank μ score tie x ∧
      tieBrokenRank μ score tie x ≤
        (μ (scoreLowerContour score x)).toReal +
          (μ (scoreAtom score x)).toReal := by
  rw [tieBrokenRank_eq_score_lower_add_tie_prefix hscore htie x]
  constructor
  · exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  · have hprefix_le_atom :
        (μ (tiePrefixInScoreAtom score tie x)).toReal ≤
          (μ (scoreAtom score x)).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top μ (scoreAtom score x))
        (measure_mono (by
          intro y hy
          rcases hy with ⟨hscore_eq, _htie_le⟩
          exact hscore_eq))
    exact add_le_add_right hprefix_le_atom _

/--
Reward-level version of the tie-breaking interval lemma.  If every rank value
between the strict lower-score mass and the lower-score-plus-atom mass maps to
the source reward level of `x`, then arbitrary tie-breaking inside that score
atom preserves `x`'s reward level.
-/
theorem rankLevel_tieBrokenRank_eq_of_score_atom_interval_level
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {preRank score tie : α → ℝ} {rankLevel : ℝ → ℕ}
    (hscore : Measurable score) (htie : Measurable tie)
    (hatom_level :
      ∀ x r,
        (μ (scoreLowerContour score x)).toReal ≤ r →
        r ≤ (μ (scoreLowerContour score x)).toReal +
          (μ (scoreAtom score x)).toReal →
        rankLevel r = rankLevel (preRank x)) :
    ∀ x, rankLevel (tieBrokenRank μ score tie x) =
      rankLevel (preRank x) := by
  intro x
  rcases tieBrokenRank_mem_score_atom_interval (μ := μ) hscore htie x with
    ⟨hlower, hupper⟩
  exact hatom_level x (tieBrokenRank μ score tie x) hlower hupper

/--
Almost-everywhere reward preservation from source score-atom containment.
This avoids asking for a full scalar PIT theorem when the source tie-breaking
lemma has already established that no positive score atom straddles two
reward bands.
-/
theorem rankLevel_tieBrokenRank_ae_eq_of_score_atom_interval_level
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {preRank score tie : α → ℝ} {rankLevel : ℝ → ℕ}
    (hscore : Measurable score) (htie : Measurable tie)
    (hatom_level :
      ∀ x r,
        (μ (scoreLowerContour score x)).toReal ≤ r →
        r ≤ (μ (scoreLowerContour score x)).toReal +
          (μ (scoreAtom score x)).toReal →
        rankLevel r = rankLevel (preRank x)) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  Filter.Eventually.of_forall
    (rankLevel_tieBrokenRank_eq_of_score_atom_interval_level
      hscore htie hatom_level)

/--
Band-bound version of the score-atom containment criterion.  It is often
easier to audit a source proof by showing that the whole score atom lies
between two rank cutoffs for the applicant's current reward band, and that
`rankLevel` is constant on that band interval.
-/
theorem rankLevel_tieBrokenRank_ae_eq_of_score_atom_band_bounds
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {preRank score tie : α → ℝ} {rankLevel : ℝ → ℕ}
    (hscore : Measurable score) (htie : Measurable tie)
    (bandOf : α → ι) (bandLower bandUpper : ι → ℝ)
    (hatom_lower :
      ∀ x, bandLower (bandOf x) ≤
        (μ (scoreLowerContour score x)).toReal)
    (hatom_upper :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal +
          (μ (scoreAtom score x)).toReal ≤ bandUpper (bandOf x))
    (hrank_band :
      ∀ x r,
        bandLower (bandOf x) ≤ r →
        r ≤ bandUpper (bandOf x) →
        rankLevel r = rankLevel (preRank x)) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rankLevel_tieBrokenRank_ae_eq_of_score_atom_interval_level
    hscore htie (by
      intro x r hlower hupper
      exact hrank_band x r
        (le_trans (hatom_lower x) hlower)
        (le_trans hupper (hatom_upper x)))

/--
Pointwise source gamma formula.  If the atom-filling construction gives
`preRank x` as lower-score mass plus within-atom prefix mass, then the
tie-broken lower-contour rank is exactly the source pre-rank.  This is a local
formula target for the source gamma construction, stronger and more auditable
than a raw scalar-CDF premise.
-/
theorem tieBrokenRank_eq_preRank_of_lower_add_prefix_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie)
    (hgamma :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal
          + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x) :
    ∀ x, tieBrokenRank μ score tie x = preRank x := by
  intro x
  rw [tieBrokenRank_eq_score_lower_add_tie_prefix hscore htie x]
  exact hgamma x

/--
Scalar CDF endpoint from the pointwise source gamma formula.  Once the
tie-broken rank is identified with the uniform source pre-rank, the scalar CDF
target follows without a separate probability-integral-transform certificate.
-/
theorem tieBrokenRank_scalar_cdf_of_lower_add_prefix_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore : Measurable score) (htie : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal
          + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t := by
  have hrank_eq :
      ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_lower_add_prefix_eq hscore htie hgamma
  intro t ht0 ht1
  have hset :
      {x | tieBrokenRank μ score tie x ≤ t} =
        {x | preRank x ≤ t} := by
    ext x
    simp [hrank_eq x]
  rw [hset]
  have hmap :
      μ {x | preRank x ≤ t} =
        Measure.map preRank μ (Set.Iic t) := by
    change μ (preRank ⁻¹' Set.Iic t) =
      Measure.map preRank μ (Set.Iic t)
    exact (Measure.map_apply hpreRank_meas measurableSet_Iic).symm
  rw [hmap, hpre_dist]
  exact uniformRankTarget_Iic_of_mem_Icc ht0 ht1

/--
Closed source-tie special case for the local gamma formula.  If post-effort
scores are monotone in the uniform source pre-rank and the public tie key is
the source pre-rank, then the lower-score mass plus within-atom prefix mass is
exactly the source pre-rank.
-/
theorem lower_add_prefix_eq_preRank_of_score_mono_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore : Measurable score)
    (htie : Measurable tie)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ x,
      (μ (scoreLowerContour score x)).toReal
        + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x := by
  intro x
  have hrank_eq :
      tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq x
  rw [← hrank_eq]
  exact (tieBrokenRank_eq_score_lower_add_tie_prefix (μ := μ) hscore htie x).symm

theorem tieBrokenLowerContour_eq_strict_union_exact
    {α : Type*} {score tie : α → ℝ} (x : α) :
    tieBrokenLowerContour score tie x =
      tieBrokenStrictLowerContour score tie x ∪ exactScoreTieKey score tie x := by
  ext y
  constructor
  · intro hy
    rcases hy with hy_score | hy_tie
    · exact Or.inl (Or.inl hy_score)
    · rcases lt_or_eq_of_le hy_tie.2 with htie_lt | htie_eq
      · exact Or.inl (Or.inr ⟨hy_tie.1, htie_lt⟩)
      · exact Or.inr ⟨hy_tie.1, htie_eq⟩
  · intro hy
    rcases hy with hy_strict | hy_exact
    · rcases hy_strict with hy_score | hy_tie
      · exact Or.inl hy_score
      · exact Or.inr ⟨hy_tie.1, le_of_lt hy_tie.2⟩
    · exact Or.inr ⟨hy_exact.1, le_of_eq hy_exact.2⟩

theorem measure_tieBrokenLowerContour_eq_strict_of_exact_key_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α)
    (hnull : μ (exactScoreTieKey score tie x) = 0) :
    μ (tieBrokenLowerContour score tie x) =
      μ (tieBrokenStrictLowerContour score tie x) := by
  have hdisjoint :
      Disjoint (tieBrokenStrictLowerContour score tie x)
        (exactScoreTieKey score tie x) := by
    rw [Set.disjoint_left]
    intro y hy_strict hy_exact
    rcases hy_strict with hy_score | hy_tie
    · exact (ne_of_lt hy_score) hy_exact.1
    · exact (ne_of_lt hy_tie.2) hy_exact.2
  rw [tieBrokenLowerContour_eq_strict_union_exact x]
  rw [measure_union hdisjoint (measurableSet_exactScoreTieKey hscore htie x),
    hnull, add_zero]

theorem tieBrokenLowerContour_ae_eq_strict_of_exact_key_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (x : α)
    (hnull : μ (exactScoreTieKey score tie x) = 0) :
    tieBrokenLowerContour score tie x =ᵐ[μ]
      tieBrokenStrictLowerContour score tie x := by
  have hsubset :
      tieBrokenStrictLowerContour score tie x ⊆
        tieBrokenLowerContour score tie x := by
    intro y hy
    rcases hy with hy_score | hy_tie
    · exact Or.inl hy_score
    · exact Or.inr ⟨hy_tie.1, le_of_lt hy_tie.2⟩
  have hmeasure :
      μ (tieBrokenLowerContour score tie x) ≤
        μ (tieBrokenStrictLowerContour score tie x) := by
    rw [measure_tieBrokenLowerContour_eq_strict_of_exact_key_null
      hscore htie x hnull]
  have hae :
      tieBrokenStrictLowerContour score tie x =ᵐ[μ]
        tieBrokenLowerContour score tie x :=
    ae_eq_of_subset_of_measure_ge hsubset hmeasure
      (measurableSet_tieBrokenStrictLowerContour hscore htie x).nullMeasurableSet
      (by finiteness)
  exact hae.symm

/--
If the tie-breaking key is injective on a nonatomic applicant space, then an
exact score/tie key has zero mass.  This is the source-model collision-free
tie-breaker step used to convert weak atom prefixes to strict prefixes.
-/
theorem measure_exactScoreTieKey_eq_zero_of_injective_tie
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    {score tie : α → ℝ}
    (htie_inj : Function.Injective tie) (x : α) :
    μ (exactScoreTieKey score tie x) = 0 := by
  refine measure_mono_null ?_ (measure_singleton x)
  intro y hy
  exact htie_inj hy.2

/--
An injective measurable tie key pushes a nonatomic applicant measure to a
nonatomic real measure.  This is the distributional form of the source
collision-free tie-breaking coordinate.
-/
theorem noAtoms_map_tie_of_injective
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    {tie : α → ℝ}
    (htie_meas : Measurable tie)
    (htie_inj : Function.Injective tie) :
    NoAtoms (Measure.map tie μ) := by
  refine ⟨fun z => ?_⟩
  rw [Measure.map_apply htie_meas (measurableSet_singleton z)]
  have hsub : ({x | tie x = z} : Set α).Subsingleton := by
    intro x hx y hy
    exact htie_inj (hx.trans hy.symm)
  simpa using hsub.measure_zero μ

/--
The same nonatomic tie-key conclusion holds after restricting to any score
atom.  This is the local atom-filling ingredient used by the source gamma
construction.
-/
theorem noAtoms_map_tie_restrict_scoreAtom_of_injective
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    {score tie : α → ℝ}
    (hscore : Measurable score)
    (htie_meas : Measurable tie)
    (htie_inj : Function.Injective tie) (x : α) :
    NoAtoms (Measure.map tie (μ.restrict (scoreAtom score x))) :=
  noAtoms_map_tie_of_injective
    (μ := μ.restrict (scoreAtom score x)) htie_meas htie_inj

/--
Collision-free source tie-breaking on a nonatomic applicant space makes the
weak and strict tie-broken lower contours agree almost everywhere.
-/
theorem tieBrokenLowerContour_ae_eq_strict_of_injective_tie
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [NoAtoms μ]
    {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie)
    (htie_inj : Function.Injective tie) (x : α) :
    tieBrokenLowerContour score tie x =ᵐ[μ]
      tieBrokenStrictLowerContour score tie x :=
  tieBrokenLowerContour_ae_eq_strict_of_exact_key_null
    hscore htie x
    (measure_exactScoreTieKey_eq_zero_of_injective_tie htie_inj x)

theorem tieBrokenLowerContour_subset_of_score_lt
    {α : Type*} {score tie : α → ℝ} {x z : α}
    (hscore : score x < score z) :
    tieBrokenLowerContour score tie x ⊆ tieBrokenLowerContour score tie z := by
  intro y hy
  rcases hy with hy_score | hy_tie
  · exact Or.inl (lt_trans hy_score hscore)
  · exact Or.inl (by rw [hy_tie.1]; exact hscore)

theorem tieBrokenLowerContour_subset_of_same_score_tie_le
    {α : Type*} {score tie : α → ℝ} {x z : α}
    (hscore : score x = score z) (htie : tie x ≤ tie z) :
    tieBrokenLowerContour score tie x ⊆ tieBrokenLowerContour score tie z := by
  intro y hy
  rcases hy with hy_score | hy_tie
  · exact Or.inl (by rwa [← hscore])
  · exact Or.inr ⟨hy_tie.1.trans hscore, le_trans hy_tie.2 htie⟩

theorem tieBrokenRank_le_of_score_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ} {x z : α}
    (hscore : score x < score z) :
    tieBrokenRank μ score tie x ≤ tieBrokenRank μ score tie z := by
  unfold tieBrokenRank
  exact ENNReal.toReal_mono (measure_ne_top μ (tieBrokenLowerContour score tie z))
    (measure_mono (tieBrokenLowerContour_subset_of_score_lt hscore))

theorem tieBrokenRank_le_of_same_score_tie_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ} {x z : α}
    (hscore : score x = score z) (htie : tie x ≤ tie z) :
    tieBrokenRank μ score tie x ≤ tieBrokenRank μ score tie z := by
  unfold tieBrokenRank
  exact ENNReal.toReal_mono (measure_ne_top μ (tieBrokenLowerContour score tie z))
    (measure_mono
      (tieBrokenLowerContour_subset_of_same_score_tie_le hscore htie))

/--
Strict monotonicity of the atom-filled rank in the source score/tie order
implies the positive lower-contour gap used by the PIT endpoint below.  This
packages the no-gap premise in terms of the semantic rank construction rather
than a raw measure difference.
-/
theorem tieBrokenRank_lex_gap_of_strict_rank_mono
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hstrict :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          tieBrokenRank μ score tie x < tieBrokenRank μ score tie z) :
    ∀ {x z},
      (score x < score z ∨ score x = score z ∧ tie x < tie z) →
        μ (tieBrokenLowerContour score tie z ∩
          (tieBrokenLowerContour score tie x)ᶜ) ≠ 0 := by
  intro x z hlex hzero
  let P := tieBrokenLowerContour score tie x
  let Q := tieBrokenLowerContour score tie z
  have hsubset : P ⊆ Q := by
    rcases hlex with hscore_lt | hsame
    · exact tieBrokenLowerContour_subset_of_score_lt hscore_lt
    · exact tieBrokenLowerContour_subset_of_same_score_tie_le
        hsame.1 (le_of_lt hsame.2)
  have hP_meas : MeasurableSet P := by
    exact measurableSet_tieBrokenLowerContour hscore_meas htie_meas x
  have hdiff_zero_real : μ.real (Q \ P) = 0 := by
    have hzero' : μ (Q \ P) = 0 := by
      simpa [P, Q, Set.diff_eq] using hzero
    simp [Measure.real, hzero']
  have hdiff_eq :
      μ.real (Q \ P) = μ.real Q - μ.real P := by
    exact measureReal_diff (μ := μ) (s₁ := Q) (s₂ := P) hsubset hP_meas
  have hreal_le : μ.real Q ≤ μ.real P := by
    rw [hdiff_eq] at hdiff_zero_real
    linarith
  have hrank_lt := hstrict hlex
  unfold tieBrokenRank at hrank_lt
  exact (not_lt_of_ge hreal_le) hrank_lt

/--
If every strict increase in the score/tie lexicographic order adds positive
measure to the tie-broken lower contour, then sublevel sets of the
lower-contour rank are exactly the lower contours.  This is the no-gap half of
the atom-filled probability-integral-transform argument.
-/
theorem tieBrokenRank_sublevel_eq_lowerContour_of_lex_gap
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    ∀ x, {y | tieBrokenRank μ score tie y ≤ tieBrokenRank μ score tie x} =
      tieBrokenLowerContour score tie x := by
  intro x
  ext y
  constructor
  · intro hyrank
    by_contra hnot
    have hstrict :
        score x < score y ∨ score x = score y ∧ tie x < tie y := by
      rcases lt_trichotomy (score y) (score x) with hlt | heq | hgt
      · exact False.elim (hnot (Or.inl hlt))
      · have htie : tie x < tie y := by
          exact lt_of_not_ge (fun hle => hnot (Or.inr ⟨heq, hle⟩))
        exact Or.inr ⟨heq.symm, htie⟩
      · exact Or.inl hgt
    have hsubset :
        tieBrokenLowerContour score tie x ⊆
          tieBrokenLowerContour score tie y := by
      rcases hstrict with hscore_lt | hsame
      · exact tieBrokenLowerContour_subset_of_score_lt hscore_lt
      · exact tieBrokenLowerContour_subset_of_same_score_tie_le
          hsame.1 (le_of_lt hsame.2)
    have hmeasure_lt :
        μ (tieBrokenLowerContour score tie x) <
          μ (tieBrokenLowerContour score tie y) := by
      refine AppliedModelingLib.measure_lt_of_imp_of_diff_ne_zero μ
        (fun a => a ∈ tieBrokenLowerContour score tie x)
        (fun a => a ∈ tieBrokenLowerContour score tie y)
        (measurableSet_tieBrokenLowerContour hscore_meas htie_meas x)
        (measurableSet_tieBrokenLowerContour hscore_meas htie_meas y)
        (fun a ha => hsubset ha) ?_
      simpa using hgap hstrict
    have hrank_lt :
        tieBrokenRank μ score tie x < tieBrokenRank μ score tie y := by
      unfold tieBrokenRank
      exact (ENNReal.toReal_lt_toReal
        (measure_ne_top μ (tieBrokenLowerContour score tie x))
        (measure_ne_top μ (tieBrokenLowerContour score tie y))).2 hmeasure_lt
    exact not_lt_of_ge hyrank hrank_lt
  · intro hycontour
    rcases hycontour with hscore_lt | hsame
    · exact tieBrokenRank_le_of_score_lt hscore_lt
    · exact tieBrokenRank_le_of_same_score_tie_le hsame.1 hsame.2

/--
No-gap plus surjectivity version of the scalar CDF endpoint for the source
tie-broken rank.  The remaining source-specific work is to prove these two
structural properties from the atom-filling construction of `gamma`.
-/
theorem tieBrokenRank_scalar_cdf_of_lex_gap_and_surjective
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hsurj :
      ∀ t, 0 ≤ t → t ≤ 1 →
        ∃ x, tieBrokenRank μ score tie x = t)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_surjective
    hsurj
    (tieBrokenRank_sublevel_eq_lowerContour_of_lex_gap
      hscore_meas htie_meas hgap)

/--
No-gap plus dense-image version of the scalar CDF endpoint for the source
tie-broken rank.  This weakens exact surjectivity to the approximation
property naturally supplied by dense atom filling.
-/
theorem tieBrokenRank_scalar_cdf_of_lex_gap_and_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t + ε)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_dense
    hbelow habove
    (tieBrokenRank_sublevel_eq_lowerContour_of_lex_gap
      hscore_meas htie_meas hgap)

/--
No-gap plus open-interval-density version of the scalar CDF endpoint for the
source tie-broken rank.  This is the closest formal shape to the supplement's
claim that atom filling makes the image dense in every gap interval.
-/
theorem tieBrokenRank_scalar_cdf_of_lex_gap_and_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_sublevel_eq_lowerContour_and_interval_dense
    hdense
    (tieBrokenRank_sublevel_eq_lowerContour_of_lex_gap
      hscore_meas htie_meas hgap)

/--
Open-interval-density PIT endpoint stated directly with strict monotonicity of
the atom-filled rank in the source score/tie order.  This is a cleaner
paper-facing formulation of the no-gap side of the gamma construction.
-/
theorem tieBrokenRank_scalar_cdf_of_strict_rank_mono_and_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hstrict :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          tieBrokenRank μ score tie x < tieBrokenRank μ score tie z) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_lex_gap_and_interval_dense
    hscore_meas htie_meas hdense
    (tieBrokenRank_lex_gap_of_strict_rank_mono
      hscore_meas htie_meas hstrict)

/--
Rank-preservation bridge from the two structural PIT facts for the source
gamma construction: strict score/tie increases add positive lower-contour mass,
and the tie-broken rank map reaches every point in `[0,1]`.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_gap_surjective
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hsurj :
      ∀ t, 0 ≤ t → t ≤ 1 →
        ∃ x, tieBrokenRank μ score tie x = t)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_lex_gap_and_surjective
    hscore_meas htie_meas hsurj hgap

/--
Rank-preservation bridge from no-gap plus dense-image PIT facts for the source
gamma construction.  This is the paper-facing structural endpoint for dense
atom filling: exact surjectivity is not required.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_gap_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t + ε)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_lex_gap_and_dense
    hscore_meas htie_meas hbelow habove hgap

/--
Rank-preservation bridge from no-gap plus open-interval-density PIT facts for
the source gamma construction.  This is the most source-shaped dense endpoint:
atom filling must make every open rank interval contain realized ranks.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_gap_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist ?_
  exact tieBrokenRank_scalar_cdf_of_lex_gap_and_interval_dense
    hscore_meas htie_meas hdense hgap

end LBG22StrategicRanking

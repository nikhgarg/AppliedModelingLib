import LBG22StrategicRanking.BaselineEquilibriumPrimitiveRepairs

/-!
# Incentive comparisons under actual population ranking

A deviating applicant can approach another applicant's score from above.
One-sided continuity of effort cost then gives the weak imitation inequality,
even when matching the score exactly would lose the tie. These comparisons
derive equal rewards at equal equilibrium scores and score ordering across
distinct reward levels.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Strictly exceeding another applicant's score reaches at least their
actual rank, independently of the deviator's tie key. -/
theorem tieBrokenRank_le_counterfactual_of_score_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {v : ℝ} (hy : score y < v) :
    tieBrokenRank μ score tie y ≤ counterfactualTieBrokenRank μ score tie x v := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro z hz
  left
  rcases hz with hz | ⟨hz, _⟩
  · exact hz.trans hy
  · exact hz ▸ hy

/-- Best response and source cost continuity imply the cost-of-imitation
inequality. Exact matching need not reach the other applicant's reward:
strictly higher scores are used, and their effort costs approach the target
cost from the feasible side. -/
theorem sourceBestResponse_imitation_inequality
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {skill ownEffort targetEffort : ℝ}
    (hcost : ContinuousOn cost (Ici 0)) (hg : StrictMonoOn production (Ici 0))
    (hr : Monotone reward) (hskill : 0 < skill) (htarget : 0 ≤ targetEffort)
    (hscore : score y ≤ production targetEffort * skill)
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost ownEffort) :
    reward (tieBrokenRank μ score tie y) - cost targetEffort ≤
      reward (tieBrokenRank μ score tie x) - cost ownEffort := by
  let U := reward (tieBrokenRank μ score tie x) - cost ownEffort
  let V := reward (tieBrokenRank μ score tie y)
  by_contra hn
  have hgap : 0 < V - cost targetEffort - U := by dsimp [V, U]; linarith
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousWithinAt_iff.mp (hcost targetEffort htarget))
    (V - cost targetEffort - U) hgap
  let d := targetEffort + δ / 2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have htd : targetEffort < d := by dsimp [d]; linarith
  have hdist : dist d targetEffort < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr htd)]
    dsimp [d]
    linarith
  have hcostnear := hnear hd hdist
  have hcostupper : cost d - cost targetEffort < V - cost targetEffort - U := by
    rw [Real.dist_eq] at hcostnear
    exact (le_abs_self _).trans_lt hcostnear
  have hs : score y < production d * skill :=
    hscore.trans_lt (mul_lt_mul_of_pos_right (hg htarget hd htd) hskill)
  have hrank := tieBrokenRank_le_counterfactual_of_score_lt μ score tie x y hs
  have hrew := hr hrank
  have hpayoff := hbest d hd
  change V ≤ reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) at hrew
  change reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤ U at hpayoff
  linarith

/-- At a best response, an applicant receives at least every reward earned
at the same score. Otherwise an arbitrarily small effort increase is profitable. -/
theorem sourceBestResponse_reward_ge_of_score_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {skill effort : ℝ} (hcost : ContinuousOn cost (Ici 0))
    (hg : StrictMonoOn production (Ici 0)) (hr : Monotone reward)
    (hskill : 0 < skill) (heffort : 0 ≤ effort)
    (hactual : score x = production effort * skill) (hscore : score y = score x)
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort) :
    reward (tieBrokenRank μ score tie y) ≤ reward (tieBrokenRank μ score tie x) := by
  have h := sourceBestResponse_imitation_inequality μ score tie x y
    hcost hg hr hskill heffort ((hscore.trans hactual).le) hbest
  linarith

/-- Equal scores receive equal rewards whenever both applicants best
respond. This is derived for the actual tie-ranking rule, not assumed as a
counterfactual reward-reachability condition. -/
theorem sourceBestResponses_equal_score_equal_reward
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {skillX skillY effortX effortY : ℝ} (hcost : ContinuousOn cost (Ici 0))
    (hg : StrictMonoOn production (Ici 0)) (hr : Monotone reward)
    (hskillX : 0 < skillX) (hskillY : 0 < skillY) (heffortX : 0 ≤ effortX) (heffortY : 0 ≤ effortY)
    (hactualX : score x = production effortX * skillX) (hactualY : score y = production effortY * skillY)
    (hscore : score x = score y)
    (hbestX : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skillX)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effortX)
    (hbestY : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie y (production d * skillY)) - cost d ≤
        reward (tieBrokenRank μ score tie y) - cost effortY) :
    reward (tieBrokenRank μ score tie x) = reward (tieBrokenRank μ score tie y) := by
  exact le_antisymm
    (sourceBestResponse_reward_ge_of_score_eq μ score tie y x hcost hg hr hskillY heffortY hactualY hscore hbestY)
    (sourceBestResponse_reward_ge_of_score_eq μ score tie x y hcost hg hr hskillX heffortX hactualX hscore.symm hbestX)

/-- A lower reward at a best response must come from a strictly lower score.
The equal-score case is ruled out by the one-sided imitation argument. -/
theorem sourceBestResponse_score_lt_of_reward_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {skill effort : ℝ} (hcost : ContinuousOn cost (Ici 0))
    (hg : StrictMonoOn production (Ici 0)) (hr : Monotone reward)
    (hskill : 0 < skill) (heffort : 0 ≤ effort)
    (hactual : score x = production effort * skill)
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort)
    (hreward : reward (tieBrokenRank μ score tie x) < reward (tieBrokenRank μ score tie y)) :
    score x < score y := by
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
  · exact (not_le_of_gt hreward) (hr (tieBrokenRank_le_of_score_lt hlt))
  · exact (not_le_of_gt hreward)
      (sourceBestResponse_reward_ge_of_score_eq μ score tie x y hcost hg hr hskill heffort hactual heq hbest)

private theorem convex_gap_lt_on_Iic {C : ℝ → ℝ} {upper a b c d : ℝ}
    (hconv : ConvexOn ℝ (Iic upper) C) (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hbd : b ≤ d) (hlen : b - a < d - c)
    (hd : d ≤ upper) (hcost : C c < C d) : C b - C a < C d - C c := by
  have had : a < d := hac.trans_lt hcd
  have hs1 := hconv.slope_mono (hab.le.trans (hbd.trans hd))
    (show b ∈ Iic upper \ {a} from ⟨hbd.trans hd, by simpa using hab.ne'⟩)
    (show d ∈ Iic upper \ {a} from ⟨hd, by simpa using had.ne'⟩) hbd
  have hs2 := hconv.slope_mono hd
    (show a ∈ Iic upper \ {d} from ⟨had.le.trans hd, by simpa using had.ne⟩)
    (show c ∈ Iic upper \ {d} from ⟨hcd.le.trans hd, by simpa using hcd.ne⟩) hac
  have hslope : slope C a b ≤ slope C c d :=
    hs1.trans (by simpa only [slope_comm] using hs2)
  have hspos : 0 < slope C c d := by
    rw [slope_def_field]
    exact div_pos (sub_pos.mpr hcost) (sub_pos.mpr hcd)
  have hprod := (mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hab.le)).trans_lt
    (mul_lt_mul_of_pos_right hlen hspos)
  have hleft : (b - a) * slope C a b = C b - C a := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hright : (d - c) * slope C c d = C d - C c := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hcd.ne']
  simpa only [hleft, hright] using hprod

theorem sourceCostAtScore_strictMonoOn_feasible
    {cost production : ℝ → ℝ} {effortMax : ℝ} (hmax : 0 ≤ effortMax)
    (hp : StrictMonoOn cost (Icc 0 effortMax)) (hg : ContinuousOn production (Icc 0 effortMax))
    (hgm : StrictMonoOn production (Icc 0 effortMax)) :
    StrictMonoOn (sourceCostAtScore cost production effortMax)
      (Icc (production 0) (production effortMax)) := by
  intro a ha b hb hab
  have h := hp (effortIntervalInverse_spec hmax hg ha).1 (effortIntervalInverse_spec hmax hg hb).1
    (effortIntervalInverse_strictMonoOn hmax hg hgm ha hb hab)
  simpa only [sourceCostAtScore, sourceEffortAtScore, max_eq_left ha.1, max_eq_left hb.1] using h

/-- Greater skill strictly reduces a positive incremental score cost.
Either or both targets may lie below the higher-skill applicant's baseline;
only the lower-skill applicant's cost increment must be positive. -/
theorem sourceCostAtScore_gap_strict_antitone_skill_of_cost_lt
    {cost production : ℝ → ℝ} {effortMax lowerScore upperScore lowSkill highSkill : ℝ}
    (hmax : 0 ≤ effortMax) (hp : MonotoneOn cost (Icc 0 effortMax))
    (hpconv : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax)) (hgm : StrictMonoOn production (Icc 0 effortMax))
    (hgconc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hlo : 0 ≤ lowerScore) (hscore : lowerScore < upperScore)
    (hskill : 0 < lowSkill) (hskill_order : lowSkill < highSkill)
    (hfeasible : upperScore / lowSkill ≤ production effortMax)
    (hcost : sourceCostAtScore cost production effortMax (lowerScore / lowSkill) <
      sourceCostAtScore cost production effortMax (upperScore / lowSkill)) :
    sourceCostAtScore cost production effortMax (upperScore / highSkill) -
        sourceCostAtScore cost production effortMax (lowerScore / highSkill) <
      sourceCostAtScore cost production effortMax (upperScore / lowSkill) -
        sourceCostAtScore cost production effortMax (lowerScore / lowSkill) := by
  have hhigh : 0 < highSkill := hskill.trans hskill_order
  have hupp : 0 ≤ upperScore := hlo.trans hscore.le
  have hlow_order : lowerScore / highSkill ≤ lowerScore / lowSkill :=
    (div_le_div_iff₀ hhigh hskill).mpr (mul_le_mul_of_nonneg_left hskill_order.le hlo)
  have hupp_order : upperScore / highSkill ≤ upperScore / lowSkill :=
    (div_le_div_iff₀ hhigh hskill).mpr (mul_le_mul_of_nonneg_left hskill_order.le hupp)
  have hlen : upperScore / highSkill - lowerScore / highSkill <
      upperScore / lowSkill - lowerScore / lowSkill := by
    have h := (div_lt_div_iff₀ hhigh hskill).mpr
      (mul_lt_mul_of_pos_left hskill_order (sub_pos.mpr hscore))
    simpa only [sub_div] using h
  exact convex_gap_lt_on_Iic (sourceCostAtScore_convexOn hmax hp hpconv hg hgm hgconc)
    ((div_lt_div_iff_of_pos_right hhigh).mpr hscore)
    ((div_lt_div_iff_of_pos_right hskill).mpr hscore)
    hlow_order hupp_order hlen hfeasible hcost

/-- Above the high-skill applicant's baseline score, greater skill strictly
reduces the cost increment between two distinct attainable scores. Positive
baseline production is retained and all inverse inputs are feasible. -/
theorem sourceCostAtScore_gap_strict_antitone_skill
    {cost production : ℝ → ℝ} {effortMax lowerScore upperScore lowSkill highSkill : ℝ}
    (hmax : 0 ≤ effortMax) (hp : StrictMonoOn cost (Icc 0 effortMax))
    (hpconv : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax)) (hgm : StrictMonoOn production (Icc 0 effortMax))
    (hg0 : 0 ≤ production 0) (hgconc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hskill : 0 < lowSkill) (hskill_order : lowSkill < highSkill)
    (hbaseline : production 0 * highSkill ≤ lowerScore) (hscore : lowerScore < upperScore)
    (hfeasible : upperScore / lowSkill ≤ production effortMax) :
    sourceCostAtScore cost production effortMax (upperScore / highSkill) -
        sourceCostAtScore cost production effortMax (lowerScore / highSkill) <
      sourceCostAtScore cost production effortMax (upperScore / lowSkill) -
        sourceCostAtScore cost production effortMax (lowerScore / lowSkill) := by
  have hhigh : 0 < highSkill := hskill.trans hskill_order
  have hlo : 0 ≤ lowerScore := (mul_nonneg hg0 hhigh.le).trans hbaseline
  have hupp : 0 ≤ upperScore := hlo.trans hscore.le
  have hlow_order : lowerScore / highSkill ≤ lowerScore / lowSkill :=
    (div_le_div_iff₀ hhigh hskill).mpr (mul_le_mul_of_nonneg_left hskill_order.le hlo)
  have hupp_order : upperScore / highSkill ≤ upperScore / lowSkill :=
    (div_le_div_iff₀ hhigh hskill).mpr (mul_le_mul_of_nonneg_left hskill_order.le hupp)
  have hlen : upperScore / highSkill - lowerScore / highSkill <
      upperScore / lowSkill - lowerScore / lowSkill := by
    have h := (div_lt_div_iff₀ hhigh hskill).mpr
      (mul_lt_mul_of_pos_left hskill_order (sub_pos.mpr hscore))
    simpa only [sub_div] using h
  have hab := (div_lt_div_iff_of_pos_right hhigh).mpr hscore
  have hcd := (div_lt_div_iff_of_pos_right hskill).mpr hscore
  have hlower : production 0 ≤ lowerScore / lowSkill :=
    ((le_div_iff₀ hhigh).mpr hbaseline).trans hlow_order
  have hCcost := sourceCostAtScore_strictMonoOn_feasible hmax hp hg hgm
    ⟨hlower, hcd.le.trans hfeasible⟩ ⟨hlower.trans hcd.le, hfeasible⟩ hcd
  exact convex_gap_lt_on_Iic (sourceCostAtScore_convexOn hmax hp.monotoneOn hpconv hg hgm hgconc)
    hab hcd hlow_order hupp_order hlen hfeasible hCcost

/-- Two best responders cannot reverse the skill order in their rewards.
The imitation efforts are constructed on a compact interval containing both
actual efforts, and strict cost single crossing contradicts a reward inversion. -/
theorem sourceBestResponses_reward_mono_skill
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {skillX skillY effortX effortY : ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hpm : StrictMonoOn cost (Ici 0))
    (hpconv : ConvexOn ℝ (Ici 0) cost)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hr : Monotone reward) (hskillX : 0 < skillX) (hskill : skillX < skillY)
    (heffortX : 0 ≤ effortX) (heffortY : 0 ≤ effortY)
    (hactualX : score x = production effortX * skillX)
    (hactualY : score y = production effortY * skillY)
    (hbestX : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skillX)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effortX)
    (hbestY : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie y (production d * skillY)) - cost d ≤
        reward (tieBrokenRank μ score tie y) - cost effortY) :
    reward (tieBrokenRank μ score tie x) ≤ reward (tieBrokenRank μ score tie y) := by
  by_contra hn
  have hinv := lt_of_not_ge hn
  have hskillY := hskillX.trans hskill
  have hscore := sourceBestResponse_score_lt_of_reward_lt μ score tie y x
    hpcont hgm hr hskillY heffortY hactualY hbestY hinv
  let E := max effortX effortY
  have hE : 0 ≤ E := heffortX.trans (le_max_left _ _)
  have hX : effortX ∈ Icc (0 : ℝ) E := ⟨heffortX, le_max_left _ _⟩
  have hY : effortY ∈ Icc (0 : ℝ) E := ⟨heffortY, le_max_right _ _⟩
  have hsub : Icc (0 : ℝ) E ⊆ Ici 0 := fun _ he => he.1
  have hgC := hgcont.mono hsub
  have hgM := hgm.mono hsub
  have hbase : production 0 * skillY ≤ score y := by
    rw [hactualY]
    exact mul_le_mul_of_nonneg_right
      (hgm.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp) heffortY heffortY) hskillY.le
  have hsY : 0 ≤ score y := (mul_nonneg hg0 hskillY.le).trans hbase
  have hsX : 0 ≤ score x := hsY.trans hscore.le
  have hXX : score x / skillX = production effortX := by
    rw [hactualX, mul_div_cancel_right₀ _ hskillX.ne']
  have hYY : score y / skillY = production effortY := by
    rw [hactualY, mul_div_cancel_right₀ _ hskillY.ne']
  have hXXmax : score x / skillX ≤ production E := by
    rw [hXX]
    exact hgM.monotoneOn hX ⟨hE, le_rfl⟩ hX.2
  have hYXmax : score y / skillX ≤ production E :=
    (div_le_div_of_nonneg_right hscore.le hskillX.le).trans hXXmax
  have hXYmax : score x / skillY ≤ production E :=
    (div_le_div_of_nonneg_left hsX hskillX hskill.le).trans hXXmax
  have hYYbase : production 0 ≤ score y / skillY := (le_div_iff₀ hskillY).mpr hbase
  have hYXbase : production 0 ≤ score y / skillX := hYYbase.trans
    (div_le_div_of_nonneg_left hsY hskillX hskill.le)
  have hXYbase : production 0 ≤ score x / skillY := hYYbase.trans
    (div_le_div_of_nonneg_right hscore.le hskillY.le)
  have hiX := sourceEffortAtScore_spec hE hgC hgM.monotoneOn hYXmax
  have hiY := sourceEffortAtScore_spec hE hgC hgM.monotoneOn hXYmax
  have hiXscore : score y = production (sourceEffortAtScore production E (score y / skillX)) * skillX := by
    rw [hiX.2, max_eq_left hYXbase, div_mul_cancel₀ _ hskillX.ne']
  have hiYscore : score x = production (sourceEffortAtScore production E (score x / skillY)) * skillY := by
    rw [hiY.2, max_eq_left hXYbase, div_mul_cancel₀ _ hskillY.ne']
  have hix := sourceBestResponse_imitation_inequality μ score tie x y
    hpcont hgm hr hskillX hiX.1.1 hiXscore.le hbestX
  have hiy := sourceBestResponse_imitation_inequality μ score tie y x
    hpcont hgm hr hskillY hiY.1.1 hiYscore.le hbestY
  have hgap := sourceCostAtScore_gap_strict_antitone_skill hE (hpm.mono hsub)
    (hpconv.subset hsub (convex_Icc _ _)) hgC hgM hg0
    (hgconc.subset hsub (convex_Icc _ _)) hskillX hskill hbase hscore hXXmax
  have hcX : sourceCostAtScore cost production E (score x / skillX) = cost effortX := by
    rw [sourceCostAtScore, hXX, sourceEffortAtScore_at_production hgM hX]
  have hcY : sourceCostAtScore cost production E (score y / skillY) = cost effortY := by
    rw [sourceCostAtScore, hYY, sourceEffortAtScore_at_production hgM hY]
  rw [hcX, hcY] at hgap
  change cost (sourceEffortAtScore production E (score x / skillY)) - cost effortY <
    cost effortX - cost (sourceEffortAtScore production E (score y / skillX)) at hgap
  linarith

/-- Every feasible best response lies weakly above the source's
cost-minimizing baseline; no restriction of the action space is imposed. -/
theorem sourceBestResponse_effort_ge_baseline
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x : α) {cost production reward : ℝ → ℝ}
    {baseline skill effort : ℝ} (hbaseline : 0 ≤ baseline) (hskill : 0 ≤ skill)
    (hg : MonotoneOn production (Ici 0)) (hr : Monotone reward)
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hzero : cost baseline = 0)
    (heffort : 0 ≤ effort) (hactual : score x = production effort * skill)
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort) : baseline ≤ effort := by
  by_contra hn
  have hdom := sourceEffortBelowBaseline_strictly_dominated μ score tie x
    hbaseline hskill hg hr hcost hnonneg hzero heffort (lt_of_not_ge hn)
  rw [← hactual, counterfactualTieBrokenRank_at_current_score] at hdom
  exact (not_lt_of_ge (hbest baseline hbaseline)) hdom

/-- The source cost and production primitives imply reward order for any
two best responders, including a nonzero cost-minimizing effort baseline. -/
theorem sourceBestResponses_reward_mono_skill_of_sourcePrimitives
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {baseline skillX skillY effortX effortY : ℝ} (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hr : Monotone reward) (hskillX : 0 < skillX) (hskill : skillX < skillY)
    (heffortX : 0 ≤ effortX) (heffortY : 0 ≤ effortY)
    (hactualX : score x = production effortX * skillX)
    (hactualY : score y = production effortY * skillY)
    (hbestX : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skillX)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effortX)
    (hbestY : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie y (production d * skillY)) - cost d ≤
        reward (tieBrokenRank μ score tie y) - cost effortY) :
    reward (tieBrokenRank μ score tie x) ≤ reward (tieBrokenRank μ score tie y) := by
  have hbX := sourceBestResponse_effort_ge_baseline μ score tie x hbaseline hskillX.le
    hgm.monotoneOn hr hpconv hpnonneg hpzero heffortX hactualX hbestX
  have hbY := sourceBestResponse_effort_ge_baseline μ score tie y hbaseline (hskillX.trans hskill).le
    hgm.monotoneOn hr hpconv hpnonneg hpzero heffortY hactualY hbestY
  let P := fun e => cost (baseline + e)
  let G := fun e => production (baseline + e)
  have hshift : MapsTo (fun e => baseline + e) (Ici (0 : ℝ)) (Ici 0) :=
    fun _ he => add_nonneg hbaseline he
  have hpc : ContinuousOn P (Ici 0) := hpcont.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hpv : StrictConvexOn ℝ (Ici 0) P :=
    (hpconv.translate_right baseline).subset hshift (convex_Ici _)
  have hpn (e : ℝ) (he : e ∈ Ici (0 : ℝ)) : 0 ≤ P e := hpnonneg _ (hshift he)
  have hpz : P 0 = 0 := by simpa only [P, add_zero] using hpzero
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpv hpn hpz
  have hgc : ContinuousOn G (Ici 0) := hgcont.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hgM : StrictMonoOn G (Ici 0) :=
    fun a ha b hb hab => hgm (hshift ha) (hshift hb) (by dsimp only; linarith)
  have hgC : ConcaveOn ℝ (Ici 0) G :=
    (hgconc.translate_right baseline).subset hshift (convex_Ici _)
  have hgZ : 0 ≤ G 0 := by
    simpa only [G, add_zero] using
      hg0.trans (hgm.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp) hbaseline hbaseline)
  have heX : baseline + (effortX - baseline) = effortX := by ring
  have heY : baseline + (effortY - baseline) = effortY := by ring
  apply sourceBestResponses_reward_mono_skill μ score tie x y
    hpc hpm hpv.convexOn hgc hgM hgC hgZ hr hskillX hskill
    (sub_nonneg.mpr hbX) (sub_nonneg.mpr hbY)
  · simpa only [G, heX] using hactualX
  · simpa only [G, heY] using hactualY
  · intro d hd
    simpa only [G, P, heX] using hbestX (baseline + d) (add_nonneg hbaseline hd)
  · intro d hd
    simpa only [G, P, heY] using hbestY (baseline + d) (add_nonneg hbaseline hd)

/-- Every almost-everywhere equilibrium preserves finite reward bands under
the source cost, production, skill-order, and measurable injective tie
primitives. Uniform post-effort ranks and the pairwise incentive comparison
are derived, not supplied as equilibrium certificates. -/
theorem sourceFiniteEquilibrium_rank_preservation_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {baseline : ℝ}
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure,
      0 ≤ effort t ∧ score t = production (effort t) * skill t ∧
      ∀ d : ℝ, 0 ≤ d →
        reward (finiteLowerRankBand cutoff
          (counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t))).val - cost d ≤
        reward (finiteLowerRankBand cutoff (tieBrokenRank unitRankMeasure score tie t)).val - cost (effort t)) :
    (fun t => finiteLowerRankBand cutoff (tieBrokenRank unitRankMeasure score tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand cutoff := by
  let rank := tieBrokenRank unitRankMeasure score tie
  let level := fun r => (finiteLowerRankBand cutoff r).val
  let R := fun r => reward (level r)
  let good := fun t => t ∈ Ioc (0 : ℝ) 1 ∧ 0 ≤ effort t ∧
    score t = production (effort t) * skill t ∧
    ∀ d : ℝ, 0 ≤ d →
      R (counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t)) - cost d ≤
        R (rank t) - cost (effort t)
  have hgood : ∀ᵐ t ∂unitRankMeasure, good t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hbest] with t ht hb
    exact ⟨ht, hb⟩
  have hexception : unitRankMeasure {t | ¬ good t} = 0 := ae_iff.mp hgood
  have hlevel_mono : Monotone level := fun _ _ hab => finiteLowerRankBand_monotone cutoff hab
  have hlevel_meas : Measurable level := hlevel_mono.measurable
  have hrank_meas : Measurable rank := measurable_tieBrokenRank hscore htie
  haveI : NoAtoms (Measure.map tie unitRankMeasure) := noAtoms_map_tie_of_injOn_unitRank htie hinj
  have hdist : Measure.map rank unitRankMeasure = unitRankMeasure := by
    calc
      Measure.map rank unitRankMeasure = volume.restrict (Icc (0 : ℝ) 1) :=
        tieBrokenRank_map_eq_uniform_of_noAtoms_tie unitRankMeasure hscore htie
      _ = unitRankMeasure := restrict_Ioc_eq_restrict_Icc.symm
  have hlevels : (fun t => level (rank t)) =ᵐ[unitRankMeasure] level := by
    refine bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_off_null_and_equal_rank_tail_measures
      (n + 1) id rank level hexception
      (fun t => (finiteLowerRankBand cutoff t).isLt)
      (fun t => (finiteLowerRankBand cutoff (rank t)).isLt) ?_
      measurable_id hrank_meas hlevel_meas ?_
    · intro x y hx hy hpre hpost
      have hxg : good x := not_not.mp hx
      have hyg : good y := not_not.mp hy
      have hyx : y < x := lt_of_not_ge (fun h => (not_le_of_gt hpre) (hlevel_mono h))
      have hskill : skill y < skill x := hf ⟨hyg.1.1.le, hyg.1.2⟩ ⟨hxg.1.1.le, hxg.1.2⟩ hyx
      have hskillY : 0 < skill y := hf0.trans_lt
        (hf ⟨le_rfl, by norm_num⟩ ⟨hyg.1.1.le, hyg.1.2⟩ hyg.1.1)
      have hrew := sourceBestResponses_reward_mono_skill_of_sourcePrimitives unitRankMeasure score tie y x
        hbaseline hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0
        (monotone_finiteLowerRankReward cutoff hr.monotoneOn) hskillY hskill
        hyg.2.1 hxg.2.1 hyg.2.2.1 hxg.2.2.1 hyg.2.2.2 hxg.2.2.2
      have hstrict := hr
        ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff (rank x)).isLt⟩
        ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff (rank y)).isLt⟩ hpost
      exact (not_lt_of_ge hrew) hstrict
    · intro k _hk
      have hset : MeasurableSet {r | k ≤ level r} := hlevel_meas measurableSet_Ici
      have h := congrArg (fun ν : Measure ℝ => ν {r | k ≤ level r}) hdist
      change (Measure.map rank unitRankMeasure) {r | k ≤ level r} = unitRankMeasure {r | k ≤ level r} at h
      rw [Measure.map_apply hrank_meas hset] at h
      exact h.symm
  filter_upwards [hlevels] with t ht
  exact Fin.ext ht

/-- A best responder who earns the minimum available reward must choose
the unique cost-minimizing effort. This gives the bottom-band base case
for effort uniqueness after reward-band preservation. -/
theorem sourceBestResponse_bottomReward_effort_eq_baseline
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x : α) {cost production reward : ℝ → ℝ}
    {baseline skill effort bottomReward : ℝ} (hbaseline : 0 ≤ baseline)
    (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hbottom : ∀ r, bottomReward ≤ reward r) (heffort : 0 ≤ effort)
    (hown : reward (tieBrokenRank μ score tie x) = bottomReward)
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort) : effort = baseline := by
  by_contra hn
  have hpos := sourceCost_pos_away_from_baseline hbaseline heffort hpconv hpnonneg hpzero hn
  have h := hbest baseline hbaseline
  rw [hpzero, hown] at h
  have hb := hbottom (counterfactualTieBrokenRank μ score tie x (production baseline * skill))
  linarith

/-- The range of rewards bounds equilibrium effort cost because the
cost-minimizing action always guarantees at least the minimum reward. -/
theorem sourceBestResponse_cost_le_reward_range
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x : α) {cost production reward : ℝ → ℝ}
    {baseline skill effort bottomReward topReward : ℝ}
    (hbaseline : 0 ≤ baseline) (hpzero : cost baseline = 0)
    (hbottom : ∀ r, bottomReward ≤ reward r)
    (htop : reward (tieBrokenRank μ score tie x) ≤ topReward)
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort) : cost effort ≤ topReward - bottomReward := by
  have h := hbest baseline hbaseline
  rw [hpzero] at h
  have hb := hbottom (counterfactualTieBrokenRank μ score tie x (production baseline * skill))
  linarith

/-- An applicant exerting more than the cost minimum cannot have a higher
score than another applicant receiving the same reward. A small reduction
in effort still strictly exceeds that score and reduces cost. -/
theorem sourceBestResponse_score_le_of_same_reward
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {baseline skill effort : ℝ} (hbaseline : 0 ≤ baseline)
    (hp : StrictMonoOn cost (Ici baseline)) (hg : ContinuousOn production (Ici 0))
    (hr : Monotone reward) (heffort : baseline < effort)
    (hactual : score x = production effort * skill)
    (hequal : reward (tieBrokenRank μ score tie y) = reward (tieBrokenRank μ score tie x))
    (hbest : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort) : score x ≤ score y := by
  by_contra hn
  have hgap : 0 < score x - score y := sub_pos.mpr (lt_of_not_ge hn)
  have hc : ContinuousWithinAt (fun d => production d * skill) (Ici 0) effort :=
    (hg effort (hbaseline.trans heffort.le)).mul_const skill
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousWithinAt_iff.mp hc) (score x - score y) hgap
  let η := min δ (effort - baseline)
  have hη : 0 < η := lt_min hδ (sub_pos.mpr heffort)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηe : η ≤ effort - baseline := min_le_right _ _
  let d := effort - η / 2
  have hbd : baseline < d := by dsimp [d]; linarith
  have hd : d < effort := by dsimp [d]; linarith
  have hd0 : 0 ≤ d := hbaseline.trans hbd.le
  have hdist : dist d effort < δ := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hd)]
    dsimp [d]
    linarith
  have hnear' := hnear hd0 hdist
  rw [Real.dist_eq, ← hactual] at hnear'
  have hscore : score y < production d * skill := by
    have hl := (abs_lt.mp hnear').1
    linarith
  have hrew := hr (tieBrokenRank_le_counterfactual_of_score_lt μ score tie x y hscore)
  rw [hequal] at hrew
  have hbest' := hbest d hd0
  have hcost := hp hbd.le heffort.le hd
  linarith

/-- Scores in a common-reward group have the source threshold shape:
the group's infimum score or the applicant's baseline score, whichever is
larger. This is a consequence of best response, not a supplied profile form. -/
theorem sourceBestResponses_equalReward_score_shape
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie skill effort : α → ℝ) {cost production reward : ℝ → ℝ}
    {baseline groupReward : ℝ} {group : Set α} (hbaseline : 0 ≤ baseline)
    (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hg0 : 0 ≤ production 0) (hr : Monotone reward)
    (hskill : ∀ x ∈ group, 0 ≤ skill x) (heffort : ∀ x ∈ group, 0 ≤ effort x)
    (hactual : ∀ x ∈ group, score x = production (effort x) * skill x)
    (hequal : ∀ x ∈ group, reward (tieBrokenRank μ score tie x) = groupReward)
    (hbest : ∀ x ∈ group, ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie x (production d * skill x)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost (effort x)) :
    ∀ x ∈ group, score x = max (sInf (score '' group)) (production baseline * skill x) := by
  have hpm := sourceCost_strictMonoOn_above_baseline hbaseline hpconv hpnonneg hpzero
  have hbdd : BddBelow (score '' group) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hactual x hx]
    exact mul_nonneg (hg0.trans (hgm.monotoneOn (by simp) (heffort x hx) (heffort x hx))) (hskill x hx)
  intro x hx
  have hmem : score x ∈ score '' group := mem_image_of_mem score hx
  have hmin := csInf_le hbdd hmem
  have hbase := sourceBestResponse_effort_ge_baseline μ score tie x hbaseline (hskill x hx)
    hgm.monotoneOn hr hpconv hpnonneg hpzero (heffort x hx) (hactual x hx) (hbest x hx)
  rcases eq_or_lt_of_le hbase with heq | hlt
  · have hs : score x = production baseline * skill x := by rw [hactual x hx, ← heq]
    rw [← hs, max_eq_right hmin]
  · have hlow : score x ≤ sInf (score '' group) := by
      apply le_csInf ⟨score x, hmem⟩
      rintro _ ⟨y, hy, rfl⟩
      exact sourceBestResponse_score_le_of_same_reward μ score tie x y hbaseline hpm hgcont hr hlt
        (hactual x hx) ((hequal y hy).trans (hequal x hx).symm) (hbest x hx)
    have hfloor : production baseline * skill x ≤ score x := by
      rw [hactual x hx]
      exact mul_le_mul_of_nonneg_right
        (hgm.monotoneOn hbaseline (heffort x hx) hbase) (hskill x hx)
    rw [le_antisymm hmin hlow, max_eq_left hfloor]

end LBG22StrategicRanking

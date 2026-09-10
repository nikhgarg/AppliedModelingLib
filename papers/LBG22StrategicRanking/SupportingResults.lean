import LBG22StrategicRanking.SecondPriceFinite
import LBG22StrategicRanking.GammaRank
import LBG22StrategicRanking.WeightedPrivateUtility

/-!
# Supporting results for strategic ranking

Algebraic implications, finite-band incentive comparisons, and conditional
rank and welfare results. Each theorem states its own mathematical premises;
in particular, supplied rank identities and fixed-total effort constraints
are hypotheses of the corresponding conditional results.
-/

namespace LBG22StrategicRanking

open Filter MeasureTheory

/--
Definition: source equilibrium at the pointwise rank layer.  The selected
effort profile is a best response to the rank map, and the realized
post-effort rank is the rank induced by those efforts.
-/
abbrev definition_equilibrium
    {α : Type*} (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  SourceRankEquilibrium cost rankOfEffort postRank rankLevel levelReward
    effort

/--
Definition: source equilibrium at the rank layer.  The selected effort profile
is an almost-everywhere best response to the rank map, and the realized
post-effort rank agrees almost everywhere with the rank induced by those
efforts.
-/
abbrev definition_equilibriumAE
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  SourceRankEquilibriumAE μ cost rankOfEffort postRank rankLevel
    levelReward effort

/--
Definition: source equilibrium with the paper's rank-construction distribution
clause exposed. The post-effort rank induced by `gamma` is required to have the
same uniform `[0,1]` distribution as the pre-effort rank.
-/
abbrev definition_equilibriumAE_with_uniform_post_rank
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  SourceRankEquilibriumAE μ cost rankOfEffort postRank rankLevel
    levelReward effort ∧
    MeasureTheory.Measure.map postRank μ =
      MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/--
Definition: two-level policy.  For capacity `rho` and cutoff `c`, applicants
with post-effort rank at least `c` are admitted with probability
`rho / (1 - c)`, and other applicants are rejected.
-/
noncomputable abbrev definition_two_level_admission :=
  twoLevelAdmission

/--
Definition check: the source's two-level high-rank probability
`ell_1 = rho / (1 - c)` lies strictly above `rho` and at most `1` under the
source cutoff domain `c in (0, 1 - rho]`.
-/
theorem definition_two_level_high_probability_unit_interval (P : TwoLevelPolicy) :
    0 < twoLevelHighProb P ∧ P.rho < twoLevelHighProb P ∧
      twoLevelHighProb P ≤ 1 :=
  twoLevel_highProb_mem_unit_interval P

/--
Definition check: holding capacity fixed, the high-rank admission probability
`ell_1 = rho/(1-c)` weakly increases as the two-level cutoff `c` increases.
-/
theorem definition_two_level_high_probability_mono_in_cutoff
    {rho cLow cHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh) :
    rho / (1 - cLow) ≤ rho / (1 - cHigh) :=
  twoLevel_highProb_mono_of_cutoff_mono hrho hc_mono hdenLow hdenHigh

/--
Definition endpoint: at the non-randomized two-level cutoff `c = 1 - rho`,
the high-rank admission probability is `1`.
-/
theorem definition_two_level_high_probability_at_nonrandomized_cutoff
    {rho : ℝ} (hrho : rho ≠ 0) :
    rho / (1 - (1 - rho)) = 1 :=
  twoLevel_highProb_at_nonrandomized_cutoff hrho

/-- Definition check: the two-level high-region probability clears capacity. -/
theorem definition_two_level_capacity_clearing (P : TwoLevelPolicy) :
    twoLevelHighProb P * (1 - P.c) = P.rho :=
  twoLevel_highProb_mul_tail_eq_capacity P

/--
Definition: applicant welfare equals capacity minus average effort cost after
using the fixed-capacity constraint on the admission policy.
-/
abbrev definition_applicant_welfare :=
  applicantWelfare

/--
Proposition: for a finite `K`-level policy, if total admission reward clears
capacity and each level's average effort cost is nonnegative, applicant welfare
is at most capacity.
-/
theorem proposition_applicant_welfare_finite_level_capacity_bound
    {ι : Type*} [Fintype ι]
    {admissionReward averageEffortCost : ι → ℝ} {rho : ℝ}
    (hcapacity : (∑ i, admissionReward i) = rho)
    (hcost : ∀ i, 0 ≤ averageEffortCost i) :
    finiteApplicantWelfare admissionReward averageEffortCost ≤ rho ∧
      finiteApplicantWelfare admissionReward averageEffortCost ≤
        applicantWelfare rho 0 ∧
      (finiteApplicantWelfare admissionReward averageEffortCost = rho ↔
        ∀ i, averageEffortCost i = 0) :=
  ⟨finiteApplicantWelfare_le_capacity_of_nonnegative_costs hcapacity hcost,
    finiteApplicantWelfare_le_pureRandomization_of_nonnegative_costs
      hcapacity hcost,
    finiteApplicantWelfare_eq_capacity_iff_all_costs_zero hcapacity hcost⟩

/--
Proposition: applicant welfare is bounded above by the capacity whenever effort
costs are nonnegative, and pure randomization attains capacity when effort cost
is zero.
-/
theorem proposition_applicant_welfare_capacity_bound
    {rho averageEffortCost : ℝ} (hcost : 0 ≤ averageEffortCost) :
    applicantWelfare rho averageEffortCost ≤ rho :=
  applicantWelfare_le_capacity_of_nonnegative_cost hcost

/--
Proposition: in the reduced applicant-welfare identity, the capacity upper
bound is attained exactly when the average effort-cost term is zero.
-/
theorem proposition_applicant_welfare_capacity_equality_iff_zero_cost
    {rho averageEffortCost : ℝ} (hcost : 0 ≤ averageEffortCost) :
    applicantWelfare rho averageEffortCost = rho ↔ averageEffortCost = 0 :=
  applicantWelfare_eq_capacity_iff_zero_cost hcost

/--
Proposition: after the source welfare identity is reduced to
`rho - average effort cost`, the zero-cost pure-randomization policy weakly
maximizes applicant welfare.
-/
theorem proposition_applicant_welfare_pure_randomization_maximizes
    {rho averageEffortCost : ℝ} (hcost : 0 ≤ averageEffortCost) :
    applicantWelfare rho averageEffortCost ≤ applicantWelfare rho 0 :=
  applicantWelfare_le_pureRandomization_of_nonnegative_cost hcost

/--
Proposition: within the two-level policy class, if the equilibrium effort-cost
term weakly increases with the cutoff, applicant welfare weakly decreases with
the cutoff.
-/
theorem proposition_applicant_welfare_nonincreasing_from_cost_monotonicity
    {rho costLow costHigh : ℝ} (hcost : costLow ≤ costHigh) :
    applicantWelfare rho costHigh ≤ applicantWelfare rho costLow :=
  applicantWelfare_nonincreasing_when_cost_increases hcost

/--
Proposition `prop:student-welfare`, bundled source-facing endpoint.  For a
finite `K`-level policy with nonnegative equilibrium effort costs, pure
randomization weakly maximizes applicant welfare; within the two-level class,
the welfare expression is nonincreasing whenever the equilibrium effort-cost
term is nondecreasing in the cutoff.

Source status: source-facing endpoint with the two-level monotonicity condition
kept explicit.
-/
theorem proposition_applicant_welfare
    {ι : Type*} [Fintype ι]
    {admissionReward averageEffortCost : ι → ℝ}
    {rho costLow costHigh : ℝ}
    (hcapacity : (∑ i, admissionReward i) = rho)
    (hcost : ∀ i, 0 ≤ averageEffortCost i)
    (htwoLevelCost : costLow ≤ costHigh) :
    finiteApplicantWelfare admissionReward averageEffortCost ≤
        applicantWelfare rho 0 ∧
      applicantWelfare rho costHigh ≤ applicantWelfare rho costLow := by
  exact
    ⟨finiteApplicantWelfare_le_pureRandomization_of_nonnegative_costs
        hcapacity hcost,
      applicantWelfare_nonincreasing_when_cost_increases htwoLevelCost⟩

/--
Source caveat for Proposition `prop:student-welfare`: the printed
two-level monotonicity subclaim is false under the paper's broad source
assumptions.  In the source-family
`f(theta)=1/sqrt(1-theta^2/4)`, `g(e)=e`, `cost(e)=e^2`, and `rho=3/10`,
the displayed two-level effort-cost expression is lower at cutoff `1/5` than
at cutoff `1/10`; therefore applicant welfare is higher at the larger cutoff.

Source status: documented source caveat; Lean checks a source-family
counterexample to the printed monotonicity subclaim.
-/
theorem proposition_applicant_welfare_two_level_monotonicity_counterexample :
    (0 : ℝ) < 1 / 10 ∧
      (1 / 10 : ℝ) ≤ 1 / 5 ∧
      (1 / 5 : ℝ) ≤ 1 - 3 / 10 ∧
      applicantWelfare (3 / 10)
          (twoLevelApplicantCostCounterexample (3 / 10) (1 / 10)) <
        applicantWelfare (3 / 10)
          (twoLevelApplicantCostCounterexample (3 / 10) (1 / 5)) :=
  applicantWelfare_twoLevel_monotonicity_claim_counterexample

/--
Proposition: if two-level private utility is nondecreasing in the cutoff, then
the non-randomized cutoff `1 - rho` maximizes private utility on the feasible
two-level interval.
-/
theorem proposition_private_utility_maximized_at_nonrandomized_from_monotonicity
    {rho : ℝ} {u : ℝ → ℝ}
    (hrho_le_one : rho ≤ 1)
    (hmono : ∀ c d, 0 ≤ c → c ≤ d → d ≤ 1 - rho → u c ≤ u d) :
    MaximizesOnInterval u (1 - rho) 0 (1 - rho) :=
  privateUtility_maximized_at_nonrandomized_of_nondecreasing hrho_le_one hmono

/--
Proposition: in the source's two-level private-utility expression
`g(cost^{-1}(rho/(1-c))) * f(c)`, monotone `cost^{-1}`, monotone `g`, and
monotone `f` imply that non-randomized admissions maximize private utility on
the feasible two-level interval.
-/
theorem proposition_private_utility_maximized_at_nonrandomized_from_product_factors
    {rho : ℝ} {costInv g f : ℝ → ℝ}
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hcostInv_mono : Monotone costInv)
    (hg_mono : Monotone g)
    (hf_mono : Monotone f)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    MaximizesOnInterval
      (twoLevelPrivateUtilitySource rho costInv g f) (1 - rho) 0 (1 - rho) :=
  twoLevelPrivateUtilitySource_maximized_at_nonrandomized
    hrho_pos hrho_le_one hcostInv_mono hg_mono hf_mono hg_nonneg
    hf_nonneg

/--
Appendix lemma: the two displayed best-response inequalities in the
rank-preservation proof imply the corresponding effort-cost gap ordering.
-/
theorem lemma_order_p_cost_gap_order
    {rewardLow rewardHigh costLow costLowToHigh costHigh costHighToLow : ℝ}
    (hlow_best :
      rewardLow - costLow ≥ rewardHigh - costLowToHigh)
    (hhigh_best :
      rewardHigh - costHigh ≥ rewardLow - costHighToLow) :
    costHigh - costHighToLow ≤ costLowToHigh - costLow :=
  reward_imitation_inequalities_imply_cost_gap_order hlow_best hhigh_best

/--
Appendix lemma `order_g`: from the source score equations, the lower-skill
applicant must traverse a strictly longer effort interval to generate the same
score improvement. Concavity of `g` converts the larger `g`-increment into the
effort-distance ordering used in the rank-preservation contradiction.
-/
theorem lemma_order_g_concave_transfer
    {g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e eToHigh eHighToLow eHigh : ℝ}
    (hconc : ConcaveOn ℝ Set.univ g)
    (hmono : Monotone g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : g e = scoreLow / skillHigh)
    (htoHigh_score : g eToHigh = scoreHigh / skillHigh)
    (hhighToLow_score : g eHighToLow = scoreLow / skillLow)
    (hhigh_score : g eHigh = scoreHigh / skillLow)
    (he_toHigh : e < eToHigh)
    (hhighToLow_high : eHighToLow < eHigh)
    (he_highToLow : e ≤ eHighToLow)
    (htoHigh_high : eToHigh ≤ eHigh) :
    eToHigh - e < eHigh - eHighToLow :=
  order_g_from_source_score_equalities
    hconc hmono hskillLow_pos hskill_order hscore_order he_score
    htoHigh_score hhighToLow_score hhigh_score he_toHigh
    hhighToLow_high he_highToLow htoHigh_high

/--
Appendix rank-preservation algebra: the source score equalities, the two
best-response inequalities, concave increasing effort transfer, and convex
increasing effort cost rule out a pairwise reward-order inversion.
-/
theorem lemma_rank_preservation_no_inversion_algebra_contradiction
    {cost g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e0 e eToHigh eHighToLow eHigh rewardLow rewardHigh : ℝ}
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_mono : Monotone g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : g e = scoreLow / skillHigh)
    (htoHigh_score : g eToHigh = scoreHigh / skillHigh)
    (hhighToLow_score : g eHighToLow = scoreLow / skillLow)
    (hhigh_score : g eHigh = scoreHigh / skillLow)
    (he0 : e0 ≤ e)
    (he_toHigh : e < eToHigh)
    (hhighToLow_high : eHighToLow < eHigh)
    (he_highToLow : e ≤ eHighToLow)
    (htoHigh_high : eToHigh ≤ eHigh)
    (hlow_best :
      rewardLow - cost e ≥ rewardHigh - cost eToHigh)
    (hhigh_best :
      rewardHigh - cost eHigh ≥ rewardLow - cost eHighToLow) :
    False :=
  rank_preservation_no_inversion_source_score_contradiction
    hcost_conv hcost_strict hg_conc hg_mono hskillLow_pos hskill_order
    hscore_order he_score htoHigh_score hhighToLow_score hhigh_score
    he0 he_toHigh hhighToLow_high he_highToLow htoHigh_high
    hlow_best hhigh_best

/--
Appendix lemma `tienotmatter`, analytic core: if one tied applicant would get
a strictly higher rank reward after an arbitrarily small effort increase, then
continuity of effort cost contradicts best response.
-/
theorem lemma_tie_breaking_higher_reward_contradicts_best_response
    {cost : ℝ → ℝ} {effort stayReward devReward : ℝ}
    (hcost_cont : ContinuousAt cost effort)
    (hreward : stayReward < devReward)
    (hbest :
      ∀ eps, 0 < eps →
        devReward - cost (effort + eps) ≤ stayReward - cost effort) :
    False :=
  no_best_response_when_arbitrarily_small_increase_gets_higher_reward
    hcost_cont hreward hbest

/--
Appendix lemma `tienotmatter`, source-shaped version: when applicant `y` has
the same realized multiplicative score as applicant `x` but a strictly higher
rank reward, and every positive score bump by `x` reaches at least `y`'s reward
level, `x` cannot be best responding.  This derives the strict bump from
`score = g(effort) * skill`, positive skill, and strict monotonicity of `g`.
-/
theorem lemma_tie_breaking_same_score_higher_reward_contradicts_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hcost_cont : ContinuousAt cost (effort x))
    (hg_strict : StrictMono g)
    (hskill_pos : 0 < skill x)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hdeviation_reaches_y_reward :
      ∀ d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hreward :
      levelReward (rankLevel (rankOfEffort x (effort x))) <
        levelReward (rankLevel (rankOfEffort y (effort y)))) :
    False :=
  tied_score_higher_reward_contradicts_source_best_response
    hcost_cont hg_strict hskill_pos hscore_eq hsame_score
    hdeviation_reaches_y_reward hbest_x hreward

/--
Appendix lemma `tienotmatter`, monotone-level version: the preceding source
tie-breaking contradiction also follows when the effort bump reaches at least
`y`'s reward level through a rank-level comparison and a monotone reward
function.
-/
theorem lemma_tie_breaking_same_score_higher_reward_contradicts_source_best_response_of_level_mono
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hcost_cont : ContinuousAt cost (effort x))
    (hg_strict : StrictMono g)
    (hskill_pos : 0 < skill x)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hlevelReward_mono : Monotone levelReward)
    (hdeviation_reaches_y_level :
      ∀ d, score y < g d * skill x →
        rankLevel (rankOfEffort y (effort y)) ≤
          rankLevel (rankOfEffort x d))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hreward :
      levelReward (rankLevel (rankOfEffort x (effort x))) <
        levelReward (rankLevel (rankOfEffort y (effort y)))) :
    False :=
  tied_score_higher_reward_contradicts_source_best_response_of_level_mono
    hcost_cont hg_strict hskill_pos hscore_eq hsame_score
    hlevelReward_mono hdeviation_reaches_y_level hbest_x hreward

/--
Appendix lemma `tienotmatter`, equality form: if two tied applicants can each
reach the other's reward level after an arbitrarily small score increase and
both are best responding, then they receive the same reward.  This is the
source-facing statement used with the score-atom interval endpoint below.
-/
theorem lemma_tie_breaking_same_score_rewards_equal_of_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hcost_cont_x : ContinuousAt cost (effort x))
    (hcost_cont_y : ContinuousAt cost (effort y))
    (hg_strict : StrictMono g)
    (hskill_pos_x : 0 < skill x)
    (hskill_pos_y : 0 < skill y)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hdeviation_x_reaches_y_reward :
      ∀ d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hdeviation_y_reaches_x_reward :
      ∀ d, score x < g d * skill y →
        levelReward (rankLevel (rankOfEffort x (effort x))) ≤
          levelReward (rankLevel (rankOfEffort y d)))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y)) :
    levelReward (rankLevel (rankOfEffort x (effort x))) =
      levelReward (rankLevel (rankOfEffort y (effort y))) :=
  tied_score_rewards_eq_of_source_best_response
    hcost_cont_x hcost_cont_y hg_strict hskill_pos_x hskill_pos_y
    hscore_eq hsame_score hdeviation_x_reaches_y_reward
    hdeviation_y_reaches_x_reward hbest_x hbest_y

/--
Appendix lemma `tienotmatter`, rank-level form.  When the paper's reward
levels are distinct, the equality-of-rewards conclusion for tied actual scores
implies equality of the realized post-rank levels themselves.  This is the
source-facing route for eliminating actual equal-score level certificates.
-/
theorem lemma_tie_breaking_same_score_rank_levels_equal_of_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hlevelReward_inj : Function.Injective levelReward)
    (hpost_actual_x :
      rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hpost_actual_y :
      rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y))
    (hcost_cont_x : ContinuousAt cost (effort x))
    (hcost_cont_y : ContinuousAt cost (effort y))
    (hg_strict : StrictMono g)
    (hskill_pos_x : 0 < skill x)
    (hskill_pos_y : 0 < skill y)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hdeviation_x_reaches_y_reward :
      ∀ d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hdeviation_y_reaches_x_reward :
      ∀ d, score x < g d * skill y →
        levelReward (rankLevel (rankOfEffort x (effort x))) ≤
          levelReward (rankLevel (rankOfEffort y d)))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y)) :
    rankLevel (postRank x) = rankLevel (postRank y) :=
  tied_score_actual_rank_levels_eq_of_source_best_response
    hlevelReward_inj hpost_actual_x hpost_actual_y hcost_cont_x hcost_cont_y
    hg_strict hskill_pos_x hskill_pos_y hscore_eq hsame_score
    hdeviation_x_reaches_y_reward hdeviation_y_reaches_x_reward
    hbest_x hbest_y

/--
Appendix lemma `tienotmatter`, pointwise source-tie bridge.  If the source
best-response condition holds and small score bumps reach the other tied
applicant's reward level, then all realized equal-score ties have equal
post-rank levels.  This exposes the reusable paper-facing conclusion instead
of leaving actual equal-score level equality as a certificate.
-/
theorem lemma_actual_equal_score_rank_levels_of_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    (hlevelReward_inj : Function.Injective levelReward)
    (hpost_actual :
      ∀ z, rankLevel (rankOfEffort z (effort z)) =
        rankLevel (postRank z))
    (hcost_cont : ∀ z, ContinuousAt cost (effort z))
    (hg_strict : StrictMono g)
    (hskill_pos : ∀ z, 0 < skill z)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hdeviation_reaches_reward :
      ∀ x y d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort) :
    ∀ x y, score x = score y → rankLevel (postRank x) = rankLevel (postRank y) :=
  actual_equal_score_rank_levels_of_source_best_response
    hlevelReward_inj hpost_actual hcost_cont hg_strict hskill_pos hscore_eq
    hdeviation_reaches_reward hbest

/--
Appendix lemma `deviationsmeasure0`, distribution core: changing the
post-effort score function only on a measure-zero set leaves the induced score
distribution unchanged.
-/
theorem lemma_measure_zero_deviations_preserve_score_distribution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {score deviatedScore : α → β}
    (hscore : score =ᵐ[μ] deviatedScore) :
    MeasureTheory.Measure.map score μ =
      MeasureTheory.Measure.map deviatedScore μ :=
  measure_zero_deviations_preserve_score_distribution hscore

/--
Continuum rank-preservation lift: for bounded ordered reward levels, if the
no-inversion conclusion of the rank-preservation contradiction holds and
upper-tail measures are unchanged at every reward threshold, then pre- and
post-effort reward levels agree almost everywhere.
-/
theorem lemma_bounded_reward_levels_preserved_ae_from_no_inversion_and_equal_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ x, preLevel x < K)
    (hpost_bound : ∀ x, postLevel x < K)
    (hNoInv :
      ∀ x y, preLevel y < preLevel x → postLevel y ≤ postLevel x)
    (hmeasure :
      ∀ t, t < K →
        μ {x | t ≤ preLevel x} = μ {x | t ≤ postLevel x})
    (hpre_meas :
      ∀ t, t < K → MeasureTheory.NullMeasurableSet {x | t ≤ preLevel x} μ)
    (hpost_meas :
      ∀ t, t < K → MeasureTheory.NullMeasurableSet {x | t ≤ postLevel x} μ)
    (hpre_finite :
      ∀ t, t < K → (μ {x | t ≤ preLevel x}) ≠ ⊤)
    (hpost_finite :
      ∀ t, t < K → (μ {x | t ≤ postLevel x}) ≠ ⊤) :
    postLevel =ᵐ[μ] preLevel :=
  bounded_reward_levels_ae_eq_of_no_inversion_and_equal_tail_measures
    K preLevel postLevel hpre_bound hpost_bound hNoInv hmeasure
    hpre_meas hpost_meas hpre_finite hpost_finite

/--
Continuum rank-preservation lift in distribution form: for bounded ordered
reward levels on a finite measure space, pairwise no-inversion plus equality
of the pre- and post-effort reward-level distributions force pre- and
post-effort reward levels to agree almost everywhere.
-/
theorem lemma_bounded_reward_levels_preserved_ae_from_no_inversion_and_equal_level_distribution
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ x, preLevel x < K)
    (hpost_bound : ∀ x, postLevel x < K)
    (hNoInv :
      ∀ x y, preLevel y < preLevel x → postLevel y ≤ postLevel x)
    (hpre_meas : Measurable preLevel)
    (hpost_meas : Measurable postLevel)
    (hdist :
      MeasureTheory.Measure.map preLevel μ =
        MeasureTheory.Measure.map postLevel μ) :
    postLevel =ᵐ[μ] preLevel :=
  bounded_reward_levels_ae_eq_of_no_inversion_and_equal_level_distribution
    K preLevel postLevel hpre_bound hpost_bound hNoInv hpre_meas hpost_meas
    hdist

/--
Continuum rank-preservation lift in rank-distribution form: if the
post-effort ranking has the same rank distribution as the pre-effort ranking,
and reward levels are a measurable function of rank, then pairwise
no-inversion forces pre- and post-effort reward levels to agree almost
everywhere.
-/
theorem lemma_bounded_reward_levels_preserved_ae_from_no_inversion_and_equal_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hNoInv :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hrank_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.Measure.map postRank μ) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  bounded_rank_levels_ae_eq_of_no_inversion_and_equal_rank_distribution
    K preRank postRank rankLevel hpre_bound hpost_bound hNoInv
    hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist

/--
Continuum rank-preservation bridge in source-equilibrium form: source
best-response optimality gives the no-profitable-deviation inequalities, the
source skill must be a strictly increasing function of pre-effort rank,
pre-effort reward-level order must refine pre-effort rank order, score-induced
post-effort reward levels must be monotone in score, equal post-effort scores
must receive the same reward level, and the pre/post rank-level upper tails
must have the same mass at every reward cutpoint. Under those source-facing
primitives, reward levels are preserved almost everywhere.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_deviation_rank_facts
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_deviation_rank_facts_and_equal_rank_tail_measures
    K preRank postRank rankOfEffort rankLevel rankSkill skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos hskill_eq hrankSkill_strict
    hpre_level_rank_order hscore_level_mono hscore_eq hbest hpost_actual
    hequal_score_level
    hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

/--
Continuum rank-preservation bridge using source reward reachability instead
of exact equal-score deviation rank equality.  This matches the appendix route
where a deviating applicant only needs to reach at least the other applicant's
rank reward; the remaining assumptions are source primitives plus equality of
pre/post rank-tail masses.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_deviation_reward_facts
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (postRank y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_deviation_reward_facts_and_equal_rank_tail_measures
    K preRank postRank rankOfEffort rankLevel rankSkill skill score effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual hdeviation_reaches_reward hpreRank_meas
    hpostRank_meas hrankLevel_meas htail_measure

/--
Continuum rank-preservation bridge using source rank reachability.  This is
the most literal source-facing form of the deviation step: reaching another
applicant's score reaches at least that applicant's post-rank, and monotone
rank/reward levels convert that into the payoff inequalities.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_deviation_rank_reach
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hrankLevel_mono : Monotone rankLevel)
    (hlevelReward_mono : Monotone levelReward)
    (hrank_reaches :
      ∀ x y d, score y ≤ g d * skill x →
        postRank y ≤ rankOfEffort x d)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_deviation_rank_reach_and_equal_rank_tail_measures
    K preRank postRank rankOfEffort rankLevel rankSkill skill score effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual hrankLevel_mono hlevelReward_mono hrank_reaches
    hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

/--
Almost-everywhere source-equilibrium rank-preservation bridge.  This is the
source-faithful continuous version of the preceding theorem: the best-response
condition may fail on a null cutoff/tie exception set, while all finite reward
levels are still preserved almost everywhere once the source rank-tail
measures agree.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_equal_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_and_equal_rank_tail_measures
    K preRank postRank rankOfEffort rankLevel rankSkill skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos hskill_eq hrankSkill_strict
    hpre_level_rank_order hscore_level_mono hscore_eq hbestAE hpost_actual
    hequal_score_level
    hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

/--
Almost-everywhere source-equilibrium rank-preservation bridge, with the source
rank-construction requirement exposed as a common reference distribution: the
pre-effort rank and constructed post-effort rank both push the applicant
measure to the same rank distribution. For the paper's gamma construction this
is the clause that post-effort ranks are uniform on `[0,1]`.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_common_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    {reference : MeasureTheory.Measure ℝ}
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist : MeasureTheory.Measure.map preRank μ = reference)
    (hpost_dist : MeasureTheory.Measure.map postRank μ = reference) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_and_common_distribution
    K preRank postRank rankOfEffort rankLevel rankSkill skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos hskill_eq hrankSkill_strict
    hpre_level_rank_order hscore_level_mono hscore_eq hbestAE hpost_actual
    hequal_score_level hpreRank_meas hpostRank_meas hrankLevel_meas hpre_dist
    hpost_dist

/--
Almost-everywhere source-equilibrium rank-preservation bridge with the paper's
uniform post-rank construction built into the model boundary. This is the
paper-facing version of the common-distribution theorem: the only distributional
premise left outside equilibrium is that the pre-effort rank is uniform on
`[0,1]`, while the constructed post-effort rank uniformity is part of
`definition_equilibriumAE_with_uniform_post_rank`.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_uniform_rank_model
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (heq :
      definition_equilibriumAE_with_uniform_post_rank μ cost rankOfEffort
        postRank rankLevel levelReward effort)
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  rcases heq with ⟨hsourceEq, hpost_dist⟩
  have hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
    sourceRankEquilibriumAE_bestResponse hsourceEq
  have hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x) := by
    filter_upwards [sourceRankEquilibriumAE_postRank hsourceEq] with x hx
    exact congrArg rankLevel hx
  have hlevel_dist :
      MeasureTheory.Measure.map (fun x => rankLevel (preRank x)) μ =
        MeasureTheory.Measure.map (fun x => rankLevel (postRank x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas
      (by rw [hpre_dist, hpost_dist])
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          MeasureTheory.Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        MeasureTheory.Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (MeasureTheory.Measure.map_apply
        (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (postRank x)} =
          MeasureTheory.Measure.map (fun x => rankLevel (postRank x)) μ tail := by
      change μ ((fun x => rankLevel (postRank x)) ⁻¹' tail) =
        MeasureTheory.Measure.map (fun x => rankLevel (postRank x)) μ tail
      exact (MeasureTheory.Measure.map_apply
        (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_ae_post_actual_and_equal_rank_tail_measures
      K preRank postRank rankOfEffort rankLevel rankSkill skill score effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae
      hequal_score_level hpreRank_meas hpostRank_meas hrankLevel_meas
      htail_measure

/--
Almost-everywhere source-equilibrium rank preservation with the paper's
uniform post-rank construction and the source deviation-reachability step.  This
is the preferred general-rank bridge: the rank distribution clause is part of
the source definition of the constructed post-effort rank, while the deviation
step asks only that reaching another applicant's score reaches at least that
applicant's rank reward.  No scalar gamma-CDF or equal-score rank-level
certificate is exposed.

Source status: source-model rank-preservation endpoint.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_uniform_rank_model_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
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
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (heq :
      definition_equilibriumAE_with_uniform_post_rank μ cost rankOfEffort
        postRank rankLevel levelReward effort)
    (hdeviation_reaches_reward :
      ∀ x y d,
        rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y) →
        score y ≤ g d * skill x →
          levelReward (rankLevel (postRank y)) ≤
            levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  rcases heq with ⟨hsourceEq, hpost_dist⟩
  have hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
    sourceRankEquilibriumAE_bestResponse hsourceEq
  have hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x) := by
    filter_upwards [sourceRankEquilibriumAE_postRank hsourceEq] with x hx
    exact congrArg rankLevel hx
  have hlevel_dist :
      MeasureTheory.Measure.map (fun x => rankLevel (preRank x)) μ =
        MeasureTheory.Measure.map (fun x => rankLevel (postRank x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas
      (by rw [hpre_dist, hpost_dist])
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          MeasureTheory.Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        MeasureTheory.Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (MeasureTheory.Measure.map_apply
        (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (postRank x)} =
          MeasureTheory.Measure.map (fun x => rankLevel (postRank x)) μ tail := by
      change μ ((fun x => rankLevel (postRank x)) ⁻¹' tail) =
        MeasureTheory.Measure.map (fun x => rankLevel (postRank x)) μ tail
      exact (MeasureTheory.Measure.map_apply
        (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_reward_facts_local_post_actual_and_equal_rank_tail_measures
      K preRank postRank rankOfEffort rankLevel rankSkill skill score effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hdeviation_reaches_reward hpreRank_meas
      hpostRank_meas hrankLevel_meas htail_measure

/--
Continuum rank-preservation bridge with the source gamma construction reduced
to its scalar probability-integral-transform target: it is enough to prove
that the tie-broken lower-contour rank has CDF `t` on every `t in [0,1]`.
The outside-threshold cases and the restricted-uniform target are derived in
Lean from the range of the rank map.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_gamma_scalar_cdf
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hgamma_scalar_cdf

/--
Continuum gamma bridge using reward reachability instead of exact equal-score
deviation-rank equality.  The remaining gamma/PIT target is the same scalar
CDF statement, but the source-specific deviation obligation is the weaker
appendix condition that reaching another applicant's score reaches at least
that applicant's rank reward.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_gamma_scalar_cdf_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
    hbest hpost_actual hdeviation_reaches_reward hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hgamma_scalar_cdf

/--
Continuum gamma bridge in rank-reach form.  The source-specific deviation
obligation is a direct rank comparison: a deviation score that reaches another
applicant's score reaches at least that applicant's tie-broken post-rank.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_gamma_scalar_cdf_rank_reach
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf_rank_reach
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual hrankLevel_mono hlevelReward_mono hrank_reaches
    hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
    hgamma_scalar_cdf

/--
Almost-everywhere version of the continuum gamma bridge.  The remaining
distributional boundary is unchanged: prove the source atom-filled gamma
construction has scalar CDF `t` on `[0,1]`.  The equilibrium best-response
condition itself is only required almost everywhere, matching the source's
measure-zero tie/deviation convention.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_gamma_scalar_cdf
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma_scalar_cdf :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_scalar_cdf_ae_post_actual
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hgamma_scalar_cdf

/--
Almost-everywhere continuum rank-preservation bridge with the source gamma
construction reduced to the two visible structural facts in the supplement:
the atom-filled tie-broken rank is strictly increasing in the score/tie order,
and every open rank interval contains a realized tie-broken rank.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_gamma_strict_rank_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hstrict :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          tieBrokenRank μ score tie x < tieBrokenRank μ score tie z) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  lemma_rank_preservation_ae_from_source_equilibriumAE_gamma_scalar_cdf
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist
    (tieBrokenRank_scalar_cdf_of_strict_rank_mono_and_interval_dense
      hscore_meas htie_meas hdense hstrict)

/--
Almost-everywhere continuum rank-preservation bridge with the source gamma
construction reduced to a structural contour condition: a uniform pre-rank
orders applicants exactly as the score/tie lexicographic key.  This derives
the scalar CDF of the tie-broken rank in Lean rather than assuming it as a
separate probability formula.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_gamma_lex_preRank
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_preRank
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hpre_range hlex

/--
Lexicographic source-contour rank-preservation bridge without a separate
post-rank bound.  The lexicographic contour condition implies
`tieBrokenRank = preRank`, so post-rank boundedness is derived internally.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_gamma_lex_preRank_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (rankLevel : ℝ → ℕ)
    (preRank score tie : α → ℝ)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  let hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_lowerContour_eq_preRank_Iic
      hpreRank_meas hpre_dist hpre_range
      (tieBrokenLowerContour_eq_preRank_Iic_of_lex_order hlex)
  Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Almost-everywhere continuum rank-preservation bridge with the source tie key
chosen as the baseline rank label.  If the equilibrium score is monotone in
that source rank, the scalar uniform post-rank CDF follows in Lean, so no
separate gamma/PIT certificate is needed for this source-ordered route.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_score_mono_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
    K preRank rankOfEffort rankLevel rankSkill skill score tie effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Almost-everywhere continuum rank-preservation bridge with the source tie key
chosen as the baseline rank label, without a separate post-rank bound.  In
this source-ordered route Lean proves that the tie-broken post-rank equals the
uniform pre-rank, so the post-rank level bound follows from the pre-rank bound.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_score_mono_source_tie_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (rankLevel : ℝ → ℕ)
    (preRank score tie : α → ℝ)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  let hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Bundled-equilibrium version of the source-tie rank-preservation bridge.  This
uses the paper-facing equilibrium definition rather than exposing best-response
and realized-post-rank hypotheses as separate proof certificates.
-/
theorem lemma_rank_preservation_ae_from_source_equilibrium_score_mono_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
    (hEq :
      SourceRankEquilibrium cost rankOfEffort (tieBrokenRank μ score tie)
        rankLevel levelReward effort)
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse
      (sourceRankEquilibrium_bestResponse hEq)
  have hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x) := by
    intro x
    rw [sourceRankEquilibrium_postRank hEq x]
  exact
    lemma_rank_preservation_ae_from_source_equilibriumAE_score_mono_source_tie
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE (Filter.Eventually.of_forall hpost_actual) hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Bundled almost-everywhere equilibrium version of the source-tie
rank-preservation bridge.  This is the preferred source-facing route when the
paper invokes an equilibrium only up to null boundary/tie sets.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_bundled_score_mono_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
    (hEq :
      SourceRankEquilibriumAE μ cost rankOfEffort (tieBrokenRank μ score tie)
        rankLevel levelReward effort)
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
    sourceRankEquilibriumAE_bestResponse hEq
  have hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x) := by
    filter_upwards [sourceRankEquilibriumAE_postRank hEq] with x hx
    exact congrArg rankLevel hx
  exact
    lemma_rank_preservation_ae_from_source_equilibriumAE_score_mono_source_tie
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Bundled almost-everywhere equilibrium version of the source-tie
rank-preservation bridge without a separate post-rank bound.  The post-bound
is derived from source pre-rank boundedness because the source tie key makes
the tie-broken rank equal to the pre-rank.
-/
theorem lemma_rank_preservation_ae_from_source_equilibriumAE_bundled_score_mono_source_tie_no_post_bound
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
    (hEq :
      SourceRankEquilibriumAE μ cost rankOfEffort (tieBrokenRank μ score tie)
        rankLevel levelReward effort)
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
    sourceRankEquilibriumAE_bestResponse hEq
  have hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x) := by
    filter_upwards [sourceRankEquilibriumAE_postRank hEq] with x hx
    exact congrArg rankLevel hx
  exact
    lemma_rank_preservation_ae_from_source_equilibriumAE_score_mono_source_tie_no_post_bound
      rankLevel preRank score tie hpreRank_meas hpre_dist hpre_range
      hscore_mono htie_eq

/--
Gamma construction step: if the source tie-filled score order has no positive
mass gaps and its tie-broken lower-contour rank reaches every point in
`[0,1]`, then the tie-broken rank has the scalar uniform CDF required by the
rank-preservation bridge. This replaces a raw CDF certificate with structural
properties of the atom-filling construction.
-/
theorem lemma_gamma_scalar_cdf_from_no_gap_and_surjective_tie_breaking
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
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
  tieBrokenRank_scalar_cdf_of_lex_gap_and_surjective
    hscore_meas htie_meas hsurj hgap

/--
Gamma construction step, dense-image version: no positive mass gaps in the
source tie-filled score order plus arbitrarily close realized tie-broken ranks
from below and above imply the scalar uniform CDF.  This is the source-shaped
PIT target for dense atom filling; exact surjectivity is not required.
-/
theorem lemma_gamma_scalar_cdf_from_no_gap_and_dense_tie_breaking
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
  tieBrokenRank_scalar_cdf_of_lex_gap_and_dense
    hscore_meas htie_meas hbelow habove hgap

/--
Gamma construction step, open-interval-density version: no positive mass gaps
in the source tie-filled score order plus realized tie-broken ranks in every
open interval of `[0,1]` imply the scalar uniform CDF.  This is the closest
paper-facing PIT target to the supplement's dense atom-filling statement.
-/
theorem lemma_gamma_scalar_cdf_from_no_gap_and_interval_dense_tie_breaking
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
  tieBrokenRank_scalar_cdf_of_lex_gap_and_interval_dense
    hscore_meas htie_meas hdense hgap

/--
Gamma construction step, strict-rank version: interval-dense realized
tie-broken ranks plus strict monotonicity of the atom-filled rank in the
source score/tie order imply the scalar uniform CDF.
-/
theorem lemma_gamma_scalar_cdf_from_strict_rank_and_interval_dense_tie_breaking
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
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
  tieBrokenRank_scalar_cdf_of_strict_rank_mono_and_interval_dense
    hscore_meas htie_meas hdense hstrict

/--
Gamma construction step, strict-score-order version: if source pre-rank is
uniform and strict post-effort score order is exactly strict pre-rank order,
then arbitrary tie-breaking only affects null pre-rank fibers, so the
tie-broken post-rank has the scalar uniform CDF.
-/
theorem lemma_gamma_scalar_cdf_from_strict_score_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_order :
      ∀ x y, score y < score x ↔ preRank y < preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_strict_score_order_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range hscore_order

/--
Gamma construction step, source-ordered version: if source pre-rank is uniform,
post-effort scores are ordered by that pre-rank, strict score improvements
reflect pre-rank order, and the public tie-breaking key is the source pre-rank
label, then the atom-filled tie-broken post-rank has the scalar uniform CDF.
-/
theorem lemma_gamma_scalar_cdf_from_score_order_and_source_tie_key
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (hscore_reflect :
      ∀ x y, score y < score x → preRank y ≤ preRank x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_score_order_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono hscore_reflect htie_eq

/--
Gamma construction step, monotone source-ordered version: if source pre-rank is
uniform, post-effort scores are monotone in that pre-rank, and the public
tie-breaking key is the source pre-rank label, then the atom-filled
tie-broken post-rank has the scalar uniform CDF. Strict score-order reflection
is derived from monotonicity.
-/
theorem lemma_gamma_scalar_cdf_from_score_mono_and_source_tie_key
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_score_mono_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono htie_eq

/--
Gamma construction step, pointwise source-tie version: under the same
monotone source-score and `tie = preRank` convention, the atom-filled
tie-broken rank is exactly the source pre-rank. This is the strongest
source-tie PIT form used to derive downstream post-rank boundedness rather
than assuming it separately.
-/
theorem lemma_gamma_rank_eq_preRank_from_score_mono_and_source_tie_key
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ x, tieBrokenRank μ score tie x = preRank x :=
  tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
    hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Gamma construction step, source lower-contour formula: if the atom-filling
construction identifies the source pre-rank with lower score mass plus the
within-atom tie-prefix mass, then the tie-broken post-rank is exactly the
source pre-rank.  This exposes the local formula the source construction must
prove instead of hiding it inside a scalar CDF premise.
-/
theorem lemma_gamma_rank_eq_preRank_from_lower_add_prefix_formula
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hgamma :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal
          + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x) :
    ∀ x, tieBrokenRank μ score tie x = preRank x :=
  tieBrokenRank_eq_preRank_of_lower_add_prefix_eq
    hscore_meas htie_meas hgamma

/--
Gamma construction step, scalar CDF from the source lower-contour formula:
once lower score mass plus within-atom tie-prefix mass equals the uniform source
pre-rank pointwise, the scalar uniform CDF follows mechanically.
-/
theorem lemma_gamma_scalar_cdf_from_lower_add_prefix_formula
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hgamma :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal
          + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
  tieBrokenRank_scalar_cdf_of_lower_add_prefix_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hgamma

/--
Gamma construction step, closed monotone source-tie case: if post-effort scores
are monotone in the uniform source pre-rank and the tie key is the source
pre-rank, then the local lower-score plus within-atom-prefix formula follows
in Lean.
-/
theorem lemma_gamma_lower_add_prefix_formula_from_score_mono_and_source_tie_key
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {preRank score tie : α → ℝ}
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    ∀ x,
      (μ (scoreLowerContour score x)).toReal
        + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x :=
  lower_add_prefix_eq_preRank_of_score_mono_and_tie_eq_preRank
    hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
    hscore_mono htie_eq

/--
Rank-preservation consequence of the source lower-contour gamma formula.  This
is the direct paper-facing endpoint: once the source atom-filling construction
proves the local lower-mass plus within-atom-prefix identity, reward levels are
preserved without any additional scalar distribution certificate.
-/
theorem lemma_rank_preservation_ae_from_lower_add_prefix_formula
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (rankLevel : ℝ → ℕ)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hgamma :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal
          + (μ (tiePrefixInScoreAtom score tie x)).toReal = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hrank_eq :
      ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_lower_add_prefix_eq
      hscore_meas htie_meas hgamma
  filter_upwards with x
  rw [hrank_eq x]

/--
Rank-preservation consequence of source score-atom containment.  Since the
tie-broken rank always lies between strict lower-score mass and
lower-score-plus-atom mass, arbitrary tie-breaking preserves reward levels as
soon as each score atom is contained in one source reward band.  This is the
paper-facing form of the `tienotmatter` route that avoids requiring the full
scalar PIT theorem.
-/
theorem lemma_rank_preservation_ae_from_score_atom_interval_level
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (rankLevel : ℝ → ℕ)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hatom_level :
      ∀ x r,
        (μ (scoreLowerContour score x)).toReal ≤ r →
        r ≤ (μ (scoreLowerContour score x)).toReal +
          (μ (scoreAtom score x)).toReal →
        rankLevel r = rankLevel (preRank x)) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rankLevel_tieBrokenRank_ae_eq_of_score_atom_interval_level
    hscore_meas htie_meas hatom_level

/--
Rank-preservation consequence of source score-atom band bounds.  This is a
more auditable version of the atom-containment endpoint: the source proof may
give lower and upper rank cutoffs for the applicant's band, prove that the
whole score atom lies inside those cutoffs, and prove that `rankLevel` is
constant on that interval.
-/
theorem lemma_rank_preservation_ae_from_score_atom_band_bounds
    {α ι : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {preRank score tie : α → ℝ}
    (rankLevel : ℝ → ℕ)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
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
  rankLevel_tieBrokenRank_ae_eq_of_score_atom_band_bounds
    hscore_meas htie_meas bandOf bandLower bandUpper
    hatom_lower hatom_upper hrank_band

/--
Finite rank-preservation lift: for a finite population, if pre-effort reward
order implies score order, post-effort rewards are monotone in score order, and
upper-tail counts are unchanged at every reward threshold, then every
applicant's pre- and post-effort reward levels agree.
-/
theorem lemma_finite_reward_levels_preserved_from_score_order_and_equal_tail_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (preLevel postLevel : α → ℕ) (score : α → ℝ)
    (hpre_to_score :
      ∀ x y, preLevel y < preLevel x → score y ≤ score x)
    (hpost_score_mono :
      ∀ x y, score y ≤ score x → postLevel y ≤ postLevel x)
    (hcount :
      ∀ t,
        (Finset.univ.filter (fun i => t ≤ preLevel i)).card =
          (Finset.univ.filter (fun i => t ≤ postLevel i)).card) :
    ∀ i, postLevel i = preLevel i :=
  finite_reward_levels_preserved_of_score_order_and_equal_tail_counts
    preLevel postLevel score hpre_to_score hpost_score_mono hcount

/--
Finite rank-preservation lift, per-level form: for a finite population, if
the no-inversion conclusion of the rank-preservation contradiction holds and
every exact reward level has the same pre- and post-effort count, then every
applicant's pre- and post-effort reward levels agree.
-/
theorem lemma_finite_reward_levels_preserved_from_no_inversion_and_exact_level_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ i, preLevel i < K)
    (hpost_bound : ∀ i, postLevel i < K)
    (hNoInv :
      ∀ i j, preLevel j < preLevel i → postLevel j ≤ postLevel i)
    (hlevel_count :
      ∀ t, t < K →
        (Finset.univ.filter (fun i => preLevel i = t)).card =
          (Finset.univ.filter (fun i => postLevel i = t)).card) :
    ∀ i, postLevel i = preLevel i :=
  finite_reward_levels_preserved_of_no_inversion_and_exact_level_counts
    K preLevel postLevel hpre_bound hpost_bound hNoInv hlevel_count

/--
Proposition: the source's three-level counterexample inequality is sufficient
for a three-level admission policy to strictly beat deterministic two-level
admissions in private utility.
-/
theorem proposition_three_level_private_utility_counterexample_algebra
    {rho fDet x fc1 fc2 c1 c2 : ℝ}
    (hineq :
      deterministicPrivateUtility rho fDet
        < x * fc1 * (c2 - c1) * x + ((1 - x) * fc2 + x * fc1) * (1 - c2)) :
    deterministicPrivateUtility rho fDet < threeLevelPrivateUtility x fc1 fc2 c1 c2 :=
  threeLevel_privateUtility_gt_deterministic_of_source_inequality hineq

/--
Proposition witness: there are concrete algebraic parameter values for which
the source's three-level private-utility expression strictly exceeds the
deterministic two-level expression.
-/
theorem proposition_three_level_private_utility_counterexample_witness :
    ∃ rho x fc1 fc2 c1 c2 fDet : ℝ,
      0 < rho ∧ rho < 1 ∧ 0 < x ∧ x < 1 ∧ c1 < c2 ∧ c2 < 1 ∧
      x * (c2 - c1) + (1 - c2) = rho ∧
      deterministicPrivateUtility rho fDet < threeLevelPrivateUtility x fc1 fc2 c1 c2 :=
  exists_threeLevel_privateUtility_counterexample_algebra

/--
Proposition witness, source-shaped version: the three-level counterexample is
realized by a continuous strictly increasing long-tail quantile function, and
the deterministic benchmark uses the source cutoff `1 - rho`.

Source status: source-shaped witness for the three-level counterexample.
-/
theorem proposition_three_level_private_utility_counterexample_continuous_quantile :
    ∃ Q : ℝ → ℝ, ∃ rho x c1 c2 : ℝ,
      Continuous Q ∧ StrictMonoOn Q (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < Q t) ∧
      0 < rho ∧ rho < 1 ∧ 0 < x ∧ x < 1 ∧
      0 ≤ c1 ∧ c1 < 1 - rho ∧ 1 - rho < c2 ∧ c2 < 1 ∧
      x * (c2 - c1) + (1 - c2) = rho ∧
      deterministicPrivateUtility rho (Q (1 - rho))
        < threeLevelPrivateUtility x (Q c1) (Q c2) c1 c2 :=
  exists_threeLevel_privateUtility_counterexample_continuous_quantile

/--
Definition: the pointwise welfare gap is the advantaged-group welfare minus the
disadvantaged-group welfare at the same latent rank.
-/
abbrev definition_welfare_gap :=
  welfareGap

/--
Proposition: if the disadvantaged group has weakly lower welfare at the same
latent rank, the pointwise welfare gap is nonnegative; if the inequality is
strict, the welfare gap is positive.
-/
theorem proposition_pointwise_welfare_gap_sign
    {welfareA welfareB : ℝ} :
    welfareB ≤ welfareA → 0 ≤ welfareGap welfareA welfareB
    ∧ (welfareB < welfareA → 0 < welfareGap welfareA welfareB) := by
  intro hle
  exact ⟨welfareGap_nonnegative_of_le hle, fun hlt => welfareGap_positive_of_lt hlt⟩

/--
Proposition: when the two groups have equal welfare at a latent rank, as in the
pure-randomization comparison, the pointwise welfare gap is zero.
-/
theorem proposition_pointwise_welfare_gap_zero_of_equal_welfare
    {welfareA welfareB : ℝ} (h : welfareA = welfareB) :
    welfareGap welfareA welfareB = 0 :=
  welfareGap_eq_zero_of_equal_welfare h

/--
Proposition `prop:environment-diff` welfare-sign layer: the low region has
zero welfare gap, the middle region has nonnegative gap when the advantaged
applicant's welfare is nonnegative, and the high region has nonnegative
gap when the advantaged group has weakly lower effort cost at the same
admission reward, with a strict gap under strict cost inequality.
-/
theorem proposition_environment_welfare_gap_region_signs
    {admitHigh midWelfareA costA costB : ℝ} :
    welfareGap (individualWelfare 0 0) (individualWelfare 0 0) = 0
    ∧ (0 ≤ midWelfareA → 0 ≤ welfareGap midWelfareA (individualWelfare 0 0))
    ∧ (costA ≤ costB →
        0 ≤ welfareGap
          (individualWelfare admitHigh costA)
          (individualWelfare admitHigh costB))
    ∧ (costA < costB →
        0 < welfareGap
          (individualWelfare admitHigh costA)
          (individualWelfare admitHigh costB)) :=
  environment_region_welfare_gap_signs

/--
Proposition `prop:deriv-welfare-gap` source-factor endpoint: in the high
region, the displayed welfare-derivative expression for group `A` is larger
than the corresponding expression for group `B` when the source numerator terms
are positive, the disadvantaged environment has lower `psi`, `g^{-1}` is
increasing, and the relevant derivative factors are monotone and positive.

Source status: source-factor derivative-comparison endpoint.
-/
theorem proposition_welfare_gap_derivative_positive_from_factor_orders
    {common scoreNumerator derivNumerator fTheta psiA psiB : ℝ}
    {gInv costDeriv invDeriv : ℝ → ℝ}
    (hscoreNum : 0 < scoreNumerator)
    (hderivNum : 0 < derivNumerator)
    (hfTheta : 0 < fTheta)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hgInv_mono : StrictMono gInv)
    (hcostDeriv_mono : Monotone costDeriv)
    (hcostDeriv_nonneg : ∀ x, 0 ≤ costDeriv x)
    (hcostDeriv_pos : ∀ x, 0 < costDeriv x)
    (hinvDeriv_mono : Monotone invDeriv)
    (hinvDeriv_nonneg : ∀ x, 0 ≤ invDeriv x)
    (hinvDeriv_pos : ∀ x, 0 < invDeriv x) :
    0 <
      (common
          - costDeriv (gInv (scoreNumerator / (fTheta * psiA)))
            * invDeriv (scoreNumerator / (fTheta * psiA))
            * (derivNumerator / (fTheta * psiA)))
        - (common
          - costDeriv (gInv (scoreNumerator / (fTheta * psiB)))
            * invDeriv (scoreNumerator / (fTheta * psiB))
            * (derivNumerator / (fTheta * psiB))) :=
  welfareGap_derivative_positive_from_source_factor_primitives
    hscoreNum hderivNum hfTheta hpsiB_pos hpsi_order hgInv_mono
    hcostDeriv_mono hcostDeriv_nonneg hcostDeriv_pos hinvDeriv_mono
    hinvDeriv_nonneg hinvDeriv_pos

/--
Proposition: under a strictly increasing environment-scaled rank CDF, a more
favorable environment gives a strictly higher environment-scaled pre-effort
rank for the same latent skill whenever the latent skill value is positive.
-/
theorem proposition_environment_scaled_rank_advantaged_higher
    {fMixInv f : ℝ → ℝ} {thetaTrue psiA psiB : ℝ}
    (hmono : StrictMono fMixInv)
    (hskill : 0 < f thetaTrue)
    (hadv : psiB < psiA) :
    environmentScaledRank fMixInv f thetaTrue psiB
      < environmentScaledRank fMixInv f thetaTrue psiA :=
  environmentScaledRank_advantaged_gt_disadvantaged hmono hskill hadv

/--
Proposition `prop:equi-env` reward-preservation endpoint: once the base
rank-preservation theorem has been applied to the environment-scaled pre-rank
`f_mix^{-1}(f(theta_true) * psi)`, the paper's displayed conclusion
`lambda(theta_post) = lambda(theta_pre)` follows for any rank-level policy
represented by `levelReward ∘ rankLevel`.
-/
theorem proposition_environment_equilibrium_reward_preservation_from_rank_levels
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (fMixInv f : ℝ → ℝ) (thetaTrue psi postRank : α → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ)
    (hrank_preserved :
      (fun x => rankLevel (postRank x)) =ᵐ[μ]
        (fun x =>
          rankLevel (environmentScaledRank fMixInv f (thetaTrue x) (psi x)))) :
    (fun x => levelReward (rankLevel (postRank x))) =ᵐ[μ]
      (fun x =>
        levelReward
          (rankLevel (environmentScaledRank fMixInv f (thetaTrue x) (psi x)))) := by
  filter_upwards [hrank_preserved] with x hx
  exact congrArg levelReward hx

/--
Proposition `prop:equi-env`, source-tie rank-preservation endpoint.  When the
environment-scaled pre-rank is the paper's uniform source rank and equilibrium
scores are monotone in that rank, choosing the public tie key to be that rank
makes the tie-broken post-rank equal to the environment-scaled pre-rank.  The
displayed conclusion for any step policy `lambda = levelReward ∘ rankLevel`
then follows without a separate post-rank distribution certificate.

Source status: source-tie endpoint for Proposition `prop:equi-env`.
-/
theorem proposition_environment_equilibrium_reward_preservation_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (fMixInv f : ℝ → ℝ) (thetaTrue psi score tie : α → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ)
    (hpreRank_meas :
      Measurable
        (fun x => environmentScaledRank fMixInv f (thetaTrue x) (psi x)))
    (hpre_dist :
      MeasureTheory.Measure.map
          (fun x => environmentScaledRank fMixInv f (thetaTrue x) (psi x)) μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range :
      ∀ x,
        environmentScaledRank fMixInv f (thetaTrue x) (psi x) ∈
          Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y,
        environmentScaledRank fMixInv f (thetaTrue y) (psi y) ≤
          environmentScaledRank fMixInv f (thetaTrue x) (psi x) →
        score y ≤ score x)
    (htie_eq :
      ∀ x, tie x = environmentScaledRank fMixInv f (thetaTrue x) (psi x)) :
    (fun x => levelReward (rankLevel (tieBrokenRank μ score tie x))) =ᵐ[μ]
      (fun x =>
        levelReward
          (rankLevel (environmentScaledRank fMixInv f (thetaTrue x) (psi x)))) := by
  have hrank_preserved :
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x =>
          rankLevel (environmentScaledRank fMixInv f (thetaTrue x) (psi x))) :=
    lemma_rank_preservation_ae_from_source_equilibriumAE_score_mono_source_tie_no_post_bound
      rankLevel
      (fun x => environmentScaledRank fMixInv f (thetaTrue x) (psi x))
      score tie hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  exact
    proposition_environment_equilibrium_reward_preservation_from_rank_levels
      fMixInv f thetaTrue psi (tieBrokenRank μ score tie) rankLevel
      levelReward hrank_preserved

/--
Proposition `prop:equi-env` threshold bridge: clearing the
environment-scaled rank cutoff `c` is equivalent to the true rank clearing the
group threshold `theta_G(c) = f^{-1}(f_mix(c) / psi_G)`, under the displayed
inverse and monotonicity primitives.
-/
theorem proposition_environment_scaled_rank_cutoff_iff_true_rank_threshold
    {fMixInv fInv fMix f : ℝ → ℝ} {thetaTrue psi c : ℝ}
    (hfMixInv_mono : StrictMono fMixInv)
    (hf_mono : StrictMono f)
    (hpsi_pos : 0 < psi)
    (hmix : fMixInv (fMix c) = c)
    (hfInv : f (fInv (fMix c / psi)) = fMix c / psi) :
    c ≤ environmentScaledRank fMixInv f thetaTrue psi ↔
      groupThreshold fInv fMix c psi ≤ thetaTrue :=
  environmentScaledRank_ge_cutoff_iff_groupThreshold_le_trueRank
    hfMixInv_mono hf_mono hpsi_pos hmix hfInv

/--
Proposition: for the group-specific true-rank threshold
`theta_G(c) = f^{-1}(f_mix(c) / psi_G)`, the advantaged group has the lower
threshold when `psi_A > psi_B`.
-/
theorem proposition_environment_threshold_advantaged_lower
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hadv : psiB < psiA) :
    groupThreshold fInv fMix c psiA
      < groupThreshold fInv fMix c psiB :=
  groupThreshold_advantaged_lt_disadvantaged hmono hfmix_pos hpsiB_pos hadv

/--
Proposition: if the source mixture-inverse identity places the cutoff at the
average of the two group thresholds, then the cutoff lies between the
advantaged and disadvantaged thresholds.
-/
theorem proposition_environment_cutoff_between_group_thresholds
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hthreshold_order :
      groupThreshold fInv fMix c psiA ≤ groupThreshold fInv fMix c psiB)
    (hmixInv :
      twoGroupMixtureInverse fInv psiA psiB (fMix c) = c) :
    groupThreshold fInv fMix c psiA ≤ c ∧
      c ≤ groupThreshold fInv fMix c psiB :=
  groupThreshold_cutoff_between_of_mix_inverse_order hthreshold_order
    (groupThreshold_mix_identity_of_twoGroupMixtureInverse hmixInv)

/--
Proposition: the two group thresholds partition true ranks into the source's
low, middle, and high admission regions under a two-level policy.
-/
theorem proposition_environment_two_level_admission_regions
    {rho c thetaTrue thetaA thetaB : ℝ} :
    (thetaTrue < thetaA → thetaTrue < thetaB →
      twoLevelGroupAdmission rho c thetaTrue thetaA = 0 ∧
        twoLevelGroupAdmission rho c thetaTrue thetaB = 0)
    ∧ (thetaA ≤ thetaTrue → thetaTrue < thetaB →
      twoLevelGroupAdmission rho c thetaTrue thetaA = rho / (1 - c) ∧
        twoLevelGroupAdmission rho c thetaTrue thetaB = 0)
    ∧ (thetaA ≤ thetaB → thetaB ≤ thetaTrue →
      twoLevelGroupAdmission rho c thetaTrue thetaA = rho / (1 - c) ∧
        twoLevelGroupAdmission rho c thetaTrue thetaB = rho / (1 - c)) := by
  exact ⟨twoLevel_groupAdmission_low_region,
    twoLevel_groupAdmission_middle_region,
    twoLevel_groupAdmission_high_region⟩

/--
Definition: disadvantaged-group access under the two-level policy is
`rho / (1 - c) * (1 - thetaB)`, where `thetaB` is the disadvantaged group's
latent-rank threshold.
-/
noncomputable abbrev definition_two_level_access :=
  twoLevelDisadvantagedAccess

/--
Proposition: pure randomization gives strictly higher disadvantaged-group
access than a two-level policy under the source mixture-inverse formula:
the advantaged threshold is strictly below the disadvantaged threshold, so the
cutoff lies strictly below the disadvantaged threshold.
-/
theorem proposition_access_pure_randomization_dominates_two_level
    {rho c psiA psiB : ℝ} {fInv fMix : ℝ → ℝ}
    (hrho : 0 < rho)
    (hc : c < 1)
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixInv :
      twoGroupMixtureInverse fInv psiA psiB (fMix c) = c) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
      < pureRandomizationAccess rho :=
  pureRandomization_access_gt_twoLevel_of_source_mix_inverse
    hrho hc hmono hfmix_pos hpsiB_pos hpsi_order hmixInv

/--
Proposition `prop:access`, source-definition version of the pure-randomization
comparison: the paper defines `f_mix^{-1}` as the two-group mixture inverse,
and the cutoff identity supplies the ordinary inverse equation at `f_mix(c)`.
-/
theorem proposition_access_pure_randomization_dominates_two_level_from_source_mix_definition
    {rho c psiA psiB : ℝ} {fInv fMix fMixInv : ℝ → ℝ}
    (hrho : 0 < rho)
    (hc : c < 1)
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMixInv_def :
      ∀ x, fMixInv x = twoGroupMixtureInverse fInv psiA psiB x)
    (hmix : fMixInv (fMix c) = c) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
      < pureRandomizationAccess rho :=
  pureRandomization_access_gt_twoLevel_of_source_mix_inverse_definition
    hrho hc hmono hfmix_pos hpsiB_pos hpsi_order hfMixInv_def hmix

/--
Proposition: if the threshold movement dominates the cutoff movement, the
two-level disadvantaged-group access expression is nonincreasing as the cutoff
increases.
-/
theorem proposition_access_nonincreasing_from_threshold_slope
    {rho cLow cHigh thetaLow thetaHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hslope : (1 - thetaHigh) / (1 - cHigh) ≤ (1 - thetaLow) / (1 - cLow)) :
    twoLevelDisadvantagedAccess rho cHigh thetaHigh
      ≤ twoLevelDisadvantagedAccess rho cLow thetaLow :=
  twoLevel_access_nonincreasing_of_threshold_slope_bound hrho hdenLow hdenHigh hslope

/--
Proposition specialization: in the linear environment calculation, if the
advantaged environment factor is strictly larger than the disadvantaged one,
two-level disadvantaged-group access is nonincreasing in the cutoff.
-/
theorem proposition_access_nonincreasing_linear_environment
    {rho psiA psiB cLow cHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hpsiB : 0 < psiB)
    (hadv : psiB < psiA)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh) :
    twoLevelDisadvantagedAccess rho cHigh
        (linearEnvironmentDisadvantagedThresholdSlope psiA psiB * cHigh)
      ≤ twoLevelDisadvantagedAccess rho cLow
        (linearEnvironmentDisadvantagedThresholdSlope psiA psiB * cLow) :=
  twoLevel_access_nonincreasing_linear_environment
    hrho hpsiB hadv hc_mono hdenLow hdenHigh

/--
Proposition: under the source two-group mixture-inverse formula, monotone
nonnegative `f_mix`, and increasing convex `f^{-1}`, disadvantaged-group
access for two-level policies is nonincreasing in the cutoff.
-/
theorem proposition_access_nonincreasing_from_source_shape_primitives
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixLow :
      twoGroupMixtureInverse fInv psiA psiB (fMix cLow) = cLow)
    (hmixHigh :
      twoGroupMixtureInverse fInv psiA psiB (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) :=
  twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse_no_deriv
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order
    hmixLow hmixHigh hfMix_nonneg hfMix_mono hfInv_convex hfInv_mono

/--
Proposition `prop:access`, source-definition version of the monotonicity row.
The global displayed definition of `f_mix^{-1}` provides the two pointwise
mixture-inverse equations used by the algebraic access proof.
-/
theorem proposition_access_nonincreasing_from_source_mix_definition_and_shape_primitives
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix fMixInv : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMixInv_def :
      ∀ x, fMixInv x = twoGroupMixtureInverse fInv psiA psiB x)
    (hmixLow : fMixInv (fMix cLow) = cLow)
    (hmixHigh : fMixInv (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) :=
  twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse_definition_no_deriv
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hfMixInv_def
    hmixLow hmixHigh hfMix_nonneg hfMix_mono hfInv_convex hfInv_mono

/--
Proposition specialization: in the same linear environment calculation, pure
randomization gives strictly higher disadvantaged-group access than a
positive-cutoff two-level policy.
-/
theorem proposition_access_pure_randomization_dominates_linear_environment
    {rho psiA psiB c : ℝ}
    (hrho : 0 < rho)
    (hpsiB : 0 < psiB)
    (hadv : psiB < psiA)
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1) :
    twoLevelDisadvantagedAccess rho c
        (linearEnvironmentDisadvantagedThresholdSlope psiA psiB * c)
      < pureRandomizationAccess rho :=
  pureRandomization_access_gt_twoLevel_linear_environment
    hrho hpsiB hadv hc_pos hc_lt_one

/--
Proposition `prop:access`, bundled source-facing endpoint.  The source
mixture-inverse definition implies pure randomization gives strictly higher
disadvantaged-group access than any positive-cutoff two-level policy, and
under the source monotone/convex shape primitives, two-level disadvantaged
access is nonincreasing as the cutoff increases.

Source status: source-facing access endpoint with corrected source proof
directions recorded in the validation report.
-/
theorem proposition_access
    {rho c cLow cHigh psiA psiB : ℝ}
    {fInv fMix fMixInv : ℝ → ℝ}
    (hrho_pos : 0 < rho)
    (hc_lt_one : c < 1)
    (hfInv_strict : StrictMono fInv)
    (hfmix_c_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMixInv_def :
      ∀ x, fMixInv x = twoGroupMixtureInverse fInv psiA psiB x)
    (hmix_c : fMixInv (fMix c) = c)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hmixLow : fMixInv (fMix cLow) = cLow)
    (hmixHigh : fMixInv (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
        < pureRandomizationAccess rho ∧
      twoLevelDisadvantagedAccess rho cHigh
          (groupThreshold fInv fMix cHigh psiB)
        ≤ twoLevelDisadvantagedAccess rho cLow
          (groupThreshold fInv fMix cLow psiB) := by
  exact
    ⟨proposition_access_pure_randomization_dominates_two_level_from_source_mix_definition
        hrho_pos hc_lt_one hfInv_strict hfmix_c_pos hpsiB_pos hpsi_order
        hfMixInv_def hmix_c,
      proposition_access_nonincreasing_from_source_mix_definition_and_shape_primitives
        (le_of_lt hrho_pos) hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order
        hfMixInv_def hmixLow hmixHigh hfMix_nonneg hfMix_mono
        hfInv_convex hfInv_mono⟩

/--
Proposition: there is a source-family two-level societal-utility setting with
an interior randomized cutoff maximizer. For the valid witness
`f(c)=c`, `g(e)=e`, and `cost(e)=e^2`, the nonnegative societal utility
`sqrt(rho) * c * sqrt(1-c)` has an interior maximizer, and the high admission
probability `ell_1 = rho/(1-c)` lies strictly between `rho` and `1`.

Source status: corrected source-family witness for the SocUtil caveat.
-/
theorem proposition_societal_utility_interior_two_level_example :
    ∃ rho c : ℝ,
      0 < rho ∧ rho < 1 ∧ 0 < c ∧ c < 1 - rho ∧
      (rho < rho / (1 - c) ∧ rho / (1 - c) < 1) ∧
      MaximizesOnInterval (linearEffortSquaredCostSocietalUtility rho)
        c 0 (1 - rho) :=
  exists_twoLevel_societalUtility_interior_maximizer

/--
Proposition `prop:linearg` proof step: with linear effort transfer
`g(e) = h e`, `h >= 0`, and a fixed total effort budget over finitely many
coordinates, some best coordinate maximizes the weighted skill coefficient;
the scaled weighted score is bounded by `h` times total effort times this
coefficient, and allocating all effort to that coordinate attains the bound.
-/
theorem proposition_multidimensional_linear_effort_best_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h total : ℝ) (weight : ι → ℝ) (hh_nonneg : 0 ≤ h) :
    ∃ best : ι, ∃ maxWeight : ℝ,
      weight best = maxWeight ∧
      (∀ i, weight i ≤ maxWeight) ∧
      (∀ effort : ι → ℝ,
          (∀ i, 0 ≤ effort i) →
          (∑ i, effort i = total) →
          h * (∑ i, effort i * weight i) ≤ h * total * maxWeight)
      ∧ h * (∑ i, (if i = best then total else 0) * weight i)
          = h * total * maxWeight :=
  multidim_linear_scaled_effort_best_coordinate_exists h total weight hh_nonneg

/--
Proposition `prop:linearg` fixed-total payoff step: with linear effort
transfer and a monotone reward in weighted score, putting all effort into a
skill with maximal weighted coefficient maximizes applicant payoff among all
allocations with the same total effort cost.
-/
theorem proposition_multidimensional_linear_effort_best_coordinate_maximizes_payoff
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h total : ℝ) (weight : ι → ℝ) (reward : ℝ → ℝ) (costOfTotal : ℝ)
    (hh_nonneg : 0 ≤ h) (hreward_mono : Monotone reward) :
    ∃ best : ι, ∃ maxWeight : ℝ,
      weight best = maxWeight ∧
      (∀ i, weight i ≤ maxWeight) ∧
      (∀ effort : ι → ℝ,
          (∀ i, 0 ≤ effort i) →
          (∑ i, effort i = total) →
          reward (h * (∑ i, effort i * weight i)) - costOfTotal
            ≤ reward (h * total * maxWeight) - costOfTotal)
      ∧ reward (h * (∑ i, (if i = best then total else 0) * weight i)) - costOfTotal
          = reward (h * total * maxWeight) - costOfTotal :=
  multidim_linear_effort_single_best_maximizes_fixed_total_payoff
    h total weight reward costOfTotal hh_nonneg hreward_mono

/--
Proposition `prop:linearg` pointwise fixed-budget payoff step: if a chosen
coordinate has maximal weighted skill coefficient for an applicant, then any
allocation with the same total effort gives weakly lower payoff than putting
the full budget on that chosen coordinate.
-/
theorem proposition_multidimensional_linear_effort_chosen_best_coordinate_maximizes_payoff
    {α ι : Type*} [Fintype ι]
    (h total : ℝ) (weight : α → ι → ℝ) (best : α → ι)
    (reward : ℝ → ℝ) (costOfTotal : ℝ)
    (hh_nonneg : 0 ≤ h) (hreward_mono : Monotone reward)
    (hbest_max : ∀ x i, weight x i ≤ weight x (best x)) :
    ∀ x (effort : ι → ℝ),
      (∀ i, 0 ≤ effort i) →
      (∑ i, effort i = total) →
      reward (h * (∑ i, effort i * weight x i)) - costOfTotal
        ≤ reward (h * total * weight x (best x)) - costOfTotal := by
  intro x effort heffort hsum
  have hle :
      ∑ i, effort i * weight x i ≤ total * weight x (best x) :=
    multidim_linear_effort_score_le_total_mul_max
      effort (weight x) heffort hsum (hbest_max x)
  have hscaled :
      h * (∑ i, effort i * weight x i) ≤
        h * (total * weight x (best x)) :=
    mul_le_mul_of_nonneg_left hle hh_nonneg
  have hreward := hreward_mono hscaled
  have htarget :
      h * (total * weight x (best x)) =
        h * total * weight x (best x) := by
    ring
  calc
    reward (h * (∑ i, effort i * weight x i)) - costOfTotal
        ≤ reward (h * (total * weight x (best x))) - costOfTotal :=
      sub_le_sub_right hreward costOfTotal
    _ = reward (h * total * weight x (best x)) - costOfTotal := by
      rw [htarget]

/--
Proposition `prop:linearg` rank-order endpoint: after the fixed-budget
reduction selects a best coordinate and the resulting linear score is
`h * total * combinedIndex`, a nonnegative scale and source-ordered combined
index imply source-rank preservation under the source tie key `tie = preRank`.
-/
theorem proposition_multidimensional_linear_fixed_budget_score_order_rank_preservation
    {α ι : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι]
    (rankLevel : ℝ → ℕ) (preRank score tie combinedIndex : α → ℝ)
    (best : α → ι) (weight effortBySkill : α → ι → ℝ) {h total : ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  exact Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Proposition `prop:linearg`, source-facing fixed-budget endpoint.  For each
applicant, a chosen coordinate with maximal weighted skill coefficient
maximizes fixed-total payoff.  If the induced combined index is source ordered
and the public tie key is the source pre-rank, the resulting weighted-score
ranking preserves source rank levels.
-/
theorem proposition_multidimensional_linear_fixed_budget_payoff_and_rank_preservation
    {α ι : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι]
    (rankLevel : ℝ → ℕ) (preRank score tie combinedIndex : α → ℝ)
    (best : α → ι) (weight effortBySkill : α → ι → ℝ)
    (reward : ℝ → ℝ) (costOfTotal : ℝ) {h total : ℝ}
    (hh_nonneg : 0 ≤ h)
    (hreward_mono : Monotone reward)
    (hbest_max : ∀ x i, weight x i ≤ weight x (best x))
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
    (htie_eq : ∀ x, tie x = preRank x) :
    (∀ x (effort : ι → ℝ),
      (∀ i, 0 ≤ effort i) →
      (∑ i, effort i = total) →
      reward (h * (∑ i, effort i * weight x i)) - costOfTotal
        ≤ reward (h * total * combinedIndex x) - costOfTotal)
      ∧
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  constructor
  · intro x effort heffort hsum
    have hpayoff :=
      proposition_multidimensional_linear_effort_chosen_best_coordinate_maximizes_payoff
        h total weight best reward costOfTotal hh_nonneg hreward_mono
        hbest_max x effort heffort hsum
    simpa [hbest x] using hpayoff
  · exact
      proposition_multidimensional_linear_fixed_budget_score_order_rank_preservation
        rankLevel preRank score tie combinedIndex best weight effortBySkill
        hpreRank_meas hpre_dist hpre_range hindex_order hscale_nonneg hbest
        heffortBySkill hweightedScore htie_eq

/--
Proposition `prop:linearg` rank-preservation bridge: after the source
fixed-budget reduction has selected a best coordinate for each applicant, the
linear weighted score is a nonnegative scalar multiple of the combined
pre-effort index. If the displayed combined index is represented by a
source-rank variable and the one-dimensional source-equilibrium primitives
hold, then post-effort reward levels agree with those combined-index reward
levels almost everywhere.
-/
theorem proposition_multidimensional_linear_fixed_budget_rank_preservation
    {α ι : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι]
    (rankLevel : ℝ → ℕ) (preRank score tie : α → ℝ)
    (combinedIndex : α → ℝ) (best : α → ι)
    (weight effortBySkill : α → ι → ℝ) {h total : ℝ}
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    proposition_multidimensional_linear_fixed_budget_score_order_rank_preservation
      rankLevel preRank score tie combinedIndex best weight effortBySkill
      hpreRank_meas hpre_dist hpre_range hindex_order hscale_nonneg
      hbest heffortBySkill hweightedScore htie_eq

/--
Proposition: if the measurable-skill utility derivative is positive and the
unmeasurable-skill derivative is negative at a cutoff, there is a weight
`beta in (0,1)` making the weighted first-order condition zero.
-/
theorem proposition_weighted_private_utility_balancing_derivative
    {dMeasurable dUnmeasurable : ℝ}
    (hM : 0 < dMeasurable)
    (hU : dUnmeasurable < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      weightedUtilityDerivative beta dMeasurable dUnmeasurable = 0 :=
  exists_beta_weightedUtilityDerivative_eq_zero hM hU

/--
Proposition first-order condition in calculus form: if the measurable and
unmeasurable utility components have derivatives of opposite sign at the
cutoff, some `beta in (0,1)` makes the weighted private utility stationary at
that cutoff.
-/
theorem proposition_weighted_private_utility_has_stationary_cutoff
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {c dMeasurable dUnmeasurable : ℝ}
    (hMderiv : HasDerivAt measurableUtility dMeasurable c)
    (hUderiv : HasDerivAt unmeasurableUtility dUnmeasurable c)
    (hM : 0 < dMeasurable)
    (hU : dUnmeasurable < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      HasDerivAt (weightedPrivateUtility beta measurableUtility unmeasurableUtility) 0 c :=
  exists_beta_weightedPrivateUtility_hasDerivAt_zero hMderiv hUderiv hM hU

/--
Proposition B.2's Pareto conclusion without a supported-frontier assumption:
if measurable utility strictly rises and unmeasurable utility strictly falls
across the feasible two-level interval, then every cutoff is Pareto efficient.
This is the global economic tradeoff implied by the intended strict
monotonicity argument without the extra shape needed for linear scalarization.
-/
theorem proposition_weighted_private_utility_every_cutoff_pareto_efficient
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi : ℝ}
    (hmeasurable_strictMono :
      StrictMonoOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_strictAnti :
      StrictAntiOn unmeasurableUtility (Set.Icc lo hi))
    (hc : c ∈ Set.Icc lo hi) :
    AppliedModelingLib.IsTwoUtilityParetoEfficientOn
      (Set.Icc lo hi) measurableUtility unmeasurableUtility c :=
  every_cutoff_isTwoUtilityParetoEfficient_of_strict_tradeoff
    hmeasurable_strictMono hunmeasurable_strictAnti hc

/--
Proposition B.2's weaker headline recovery: if the balancing scalarization
weight is lower at the low-cutoff endpoint than at the high-cutoff endpoint,
some positive weight has an interior global maximizer.  Thus some genuinely
randomized two-level policy is optimal without requiring every prescribed
cutoff to lie on a supported concave frontier.
-/
theorem proposition_weighted_private_utility_some_randomization_optimal_of_endpoint_crossing
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo hi dMLo dULo dMHi dUHi : ℝ}
    (hlohi : lo < hi)
    (hMcont : ContinuousOn measurableUtility (Set.Icc lo hi))
    (hUcont : ContinuousOn unmeasurableUtility (Set.Icc lo hi))
    (hMderiv_lo : HasDerivAt measurableUtility dMLo lo)
    (hUderiv_lo : HasDerivAt unmeasurableUtility dULo lo)
    (hMderiv_hi : HasDerivAt measurableUtility dMHi hi)
    (hUderiv_hi : HasDerivAt unmeasurableUtility dUHi hi)
    (hdMLo_pos : 0 < dMLo)
    (hdULo_neg : dULo < 0)
    (hdMHi_pos : 0 < dMHi)
    (hdUHi_neg : dUHi < 0)
    (hcrossing :
      weightedUtilityBalancingWeight dMLo dULo <
        weightedUtilityBalancingWeight dMHi dUHi) :
    ∃ beta maximizer : ℝ,
      0 < beta ∧ beta < 1 ∧ maximizer ∈ Set.Ioo lo hi ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        maximizer lo hi :=
  exists_weightedPrivateUtility_interior_maximizer_of_endpoint_crossing
    hlohi hMcont hUcont hMderiv_lo hUderiv_lo hMderiv_hi hUderiv_hi
    hdMLo_pos hdULo_neg hdMHi_pos hdUHi_neg hcrossing

/--
Proposition maximum step: after choosing a weight, if the weighted private
utility has nonnegative derivative to the left of the cutoff and nonpositive
derivative to the right, then that cutoff maximizes weighted private utility
over the two-level interval.
-/
theorem proposition_weighted_private_utility_maximized_from_derivative_signs
    {measurableUtility unmeasurableUtility W' : ℝ → ℝ}
    {beta lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hcont_left :
      ContinuousOn
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (Set.Icc lo c))
    (hcont_right :
      ContinuousOn
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (Set.Icc c hi))
    (hderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (W' x) (Set.Ioo lo c) x)
    (hderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (W' x) (Set.Ioo c hi) x)
    (hleft_nonneg : ∀ x ∈ Set.Ioo lo c, 0 ≤ W' x)
    (hright_nonpos : ∀ x ∈ Set.Ioo c hi, W' x ≤ 0) :
    MaximizesOnInterval
      (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
      c lo hi :=
  weightedPrivateUtility_maximizesOnInterval_of_derivative_signs
    hlo hhi hcont_left hcont_right hderiv_left hderiv_right
    hleft_nonneg hright_nonpos

/--
Proposition source-shaped maximum step: if the measurable and unmeasurable
utility components have opposite derivatives at the target cutoff and their
derivative profiles are ordered around that cutoff, then some
`beta in (0,1)` makes the target cutoff maximize weighted private utility over
the two-level interval.
-/
theorem proposition_weighted_private_utility_maximized_from_component_derivative_order
    {measurableUtility unmeasurableUtility dMeasurable dUnmeasurable : ℝ → ℝ}
    {lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hMcont_left : ContinuousOn measurableUtility (Set.Icc lo c))
    (hMcont_right : ContinuousOn measurableUtility (Set.Icc c hi))
    (hUcont_left : ContinuousOn unmeasurableUtility (Set.Icc lo c))
    (hUcont_right : ContinuousOn unmeasurableUtility (Set.Icc c hi))
    (hMderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo lo c) x)
    (hMderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo c hi) x)
    (hUderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo lo c) x)
    (hUderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo c hi) x)
    (hM_target : 0 < dMeasurable c)
    (hU_target : dUnmeasurable c < 0)
    (hleftM :
      ∀ x ∈ Set.Ioo lo c, dMeasurable c ≤ dMeasurable x)
    (hleftU :
      ∀ x ∈ Set.Ioo lo c, dUnmeasurable c ≤ dUnmeasurable x)
    (hrightM :
      ∀ x ∈ Set.Ioo c hi, dMeasurable x ≤ dMeasurable c)
    (hrightU :
      ∀ x ∈ Set.Ioo c hi, dUnmeasurable x ≤ dUnmeasurable c) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_component_derivative_order
    hlo hhi hMcont_left hMcont_right hUcont_left hUcont_right
    hMderiv_left hMderiv_right hUderiv_left hUderiv_right
    hM_target hU_target hleftM hleftU hrightM hrightU

/--
Proposition B.2's exact target-specific repair: a prescribed cutoff is globally
optimal for some positive scalarization weight whenever its attainable utility
pair has one negative-slope supporting line.  This is weaker than global
frontier concavity and is the minimal geometric condition for that target.
-/
theorem proposition_weighted_private_utility_maximized_from_frontier_support
    {measurableUtility unmeasurableUtility frontier : ℝ → ℝ}
    {lo c hi supportSlope : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_factor :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x = frontier (measurableUtility x))
    (hsupport :
      ∀ output ∈
          Set.Icc (measurableUtility lo) (measurableUtility hi),
        frontier output ≤
          frontier (measurableUtility c) +
            supportSlope * (output - measurableUtility c))
    (hslope_neg : supportSlope < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_frontier_support
    hlo hhi hmeasurable_mono hunmeasurable_factor hsupport hslope_neg

/--
Proposition B.2 primitive-style repair: reparameterize a two-level policy by
its admitted measurable utility.  If measurable utility is nondecreasing in
the cutoff and admitted unmeasurable utility is a concave, locally decreasing
function of measurable utility, then every target cutoff is globally supported
by some weight `beta in (0,1)`.

This frontier condition is invariant to increasing changes of the cutoff
parameter and has the direct economic meaning of increasing marginal
unmeasurable-skill loss per additional unit of measurable skill.
-/
theorem proposition_weighted_private_utility_maximized_from_concave_frontier
    {measurableUtility unmeasurableUtility frontier : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_factor :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x = frontier (measurableUtility x))
    (hfrontier_concave :
      ConcaveOn ℝ
        (Set.Icc (measurableUtility lo) (measurableUtility hi)) frontier)
    (hfrontier_deriv :
      HasDerivAt frontier frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_concave_frontier
    hlo hhi hmeasurable_mono hunmeasurable_factor hfrontier_concave
    hfrontier_deriv hfrontier_decreasing

/--
Proposition B.2's weakest type-level crowd-out repair: for almost every
normalized admitted type, assume directly that residual-task output is
nonincreasing and concave in the measurable-output target.  Averaging preserves
that shape, so a negative frontier derivative supplies a positive supporting
weight.  Unlike convex effort response, this premise permits production
curvature to compensate for mild response concavity.
-/
theorem proposition_weighted_private_utility_maximized_from_residual_shape
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (hresidual_concave :
      ∀ᵐ agent ∂μ,
        ConcaveOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (fun target => production (budget - effortResponse agent target)))
    (hresidual_antitone :
      ∀ᵐ agent ∂μ,
        AntitoneOn
          (fun target => production (budget - effortResponse agent target))
          (Set.Icc (measurableUtility lo) (measurableUtility hi)))
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent target)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_residual_shape
    μ typeWeight production budget effortResponse hlo hhi hmeasurable_mono
    hunmeasurable_eq hweight_nonneg hresidual_concave hresidual_antitone
    hintegrable hfrontier_deriv hfrontier_decreasing

/--
Proposition B.2 behavioral-primitive repair: represent admitted applicants by
types (for example normalized admitted-class quantiles).  If measurable-task
effort is nondecreasing and convex in the admitted measurable-output target,
and residual-task production is increasing and concave, then aggregate
unmeasurable utility is a nonincreasing concave frontier.  A strictly negative
frontier derivative at the target yields a positive weight that globally
supports the requested cutoff.
-/
theorem proposition_weighted_private_utility_maximized_from_convex_effort_response
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (heffort_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effortResponse agent))
    (heffort_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn (effortResponse agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)))
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent target)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effort_response
    μ typeWeight production budget effortResponse hlo hhi hmeasurable_mono
    hunmeasurable_eq hproduction_concave hproduction_mono hweight_nonneg
    heffort_convex heffort_mono hintegrable hfrontier_deriv
    hfrontier_decreasing

/--
Proposition B.2 technology-primitive repair.  For each normalized admitted
type, let `effectiveInput` be the measurable score required to attain a target
measurable output.  If this requirement is nondecreasing and convex, and the
paper's production technology is strictly increasing and concave with the
specified right inverse on the relevant ranges, the induced effort response
is nondecreasing and convex.  The compiled crowd-out/frontier argument then
makes every target cutoff globally optimal for some positive weight.

This theorem closes the source-primitives seam identified in the working memo:
one may verify the shape of the explicit ratio
`m / f_M(C(m) + (1-C(m))s)` rather than assume convex effort response as a
reduced-form behavioral primitive.
-/
theorem proposition_weighted_private_utility_maximized_from_convex_effective_input
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production productionInv : ℝ → ℝ)
    (budget : ℝ)
    (effectiveInput : Agent → ℝ → ℝ)
    (effortDomain inputDomain : Set ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget
            (fun agent target => productionInv (effectiveInput agent target))
            (measurableUtility x))
    (heffortDomain_convex : Convex ℝ effortDomain)
    (hinputDomain_convex : Convex ℝ inputDomain)
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hproduction_strictMono : StrictMonoOn production effortDomain)
    (hinverse_maps : Set.MapsTo productionInv inputDomain effortDomain)
    (hinverse : Set.RightInvOn productionInv production inputDomain)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (heffective_maps :
      ∀ᵐ agent ∂μ,
        Set.MapsTo (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) inputDomain)
    (heffective_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effectiveInput agent))
    (heffective_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)))
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production
                (budget - productionInv (effectiveInput agent target))) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget
          (fun agent target => productionInv (effectiveInput agent target)))
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effectiveInput
    μ typeWeight production productionInv budget effectiveInput
    effortDomain inputDomain hlo hhi hmeasurable_mono hunmeasurable_eq
    heffortDomain_convex hinputDomain_convex hproduction_concave
    hproduction_mono hproduction_strictMono hinverse_maps hinverse
    hweight_nonneg heffective_maps heffective_convex heffective_mono
    hintegrable hfrontier_deriv hfrontier_decreasing

/--
Proposition source-shaped maximum step, marginal-tradeoff version: if the
measurable component has positive marginal gain, the unmeasurable component has
negative marginal gain, and the marginal loss/gain ratio is weakly increasing
through the target cutoff, then the source first-order weight makes that cutoff
maximize weighted private utility over the two-level interval.
-/
theorem proposition_weighted_private_utility_maximized_from_marginal_tradeoff_order
    {measurableUtility unmeasurableUtility dMeasurable dUnmeasurable : ℝ → ℝ}
    {lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hMcont_left : ContinuousOn measurableUtility (Set.Icc lo c))
    (hMcont_right : ContinuousOn measurableUtility (Set.Icc c hi))
    (hUcont_left : ContinuousOn unmeasurableUtility (Set.Icc lo c))
    (hUcont_right : ContinuousOn unmeasurableUtility (Set.Icc c hi))
    (hMderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo lo c) x)
    (hMderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo c hi) x)
    (hUderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo lo c) x)
    (hUderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo c hi) x)
    (hM_target : 0 < dMeasurable c)
    (hU_target : dUnmeasurable c < 0)
    (hleft_trade :
      ∀ x ∈ Set.Ioo lo c,
        (-dUnmeasurable x) * dMeasurable c ≤
          (-dUnmeasurable c) * dMeasurable x)
    (hright_trade :
      ∀ x ∈ Set.Ioo c hi,
        (-dUnmeasurable c) * dMeasurable x ≤
          (-dUnmeasurable x) * dMeasurable c) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi :=
  exists_beta_weightedPrivateUtility_maximizesOnInterval_of_marginal_tradeoff_order
    hlo hhi hMcont_left hMcont_right hUcont_left hUcont_right
    hMderiv_left hMderiv_right hUderiv_left hUderiv_right
    hM_target hU_target hleft_trade hright_trade

/--
Proposition B.2 clarification: the printed primitive assumptions do not imply
the stated maximum conclusion.  The explicit source-family instance in
`WeightedPrivateUtility.lean` has increasing/concave score technology,
increasing/strictly convex cost, continuous strictly increasing skill
quantiles, feasible fixed-budget efforts, and correctly normalized admitted
utility.  Nevertheless, at the admissible cutoff `c=7/16`, no
`beta in (0,1)` makes weighted private utility globally maximal.

The preceding marginal-tradeoff theorem is therefore an actual additional
shape assumption, not merely a Lean proof convenience.
-/
theorem proposition_weighted_private_utility_printed_claim_counterexample :
    B2SourcePrimitiveRegularity
      b2CounterexampleRho b2CounterexampleBudget
      b2CounterexampleScoreTechnology b2CounterexampleCost
      b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill ∧
    0 < b2CounterexampleTargetCutoff ∧
    b2CounterexampleTargetCutoff < 1 - b2CounterexampleRho ∧
    ∀ beta : ℝ, 0 < beta → beta < 1 →
      ¬ MaximizesOnInterval
        (weightedPrivateUtility beta
          b2CounterexampleMeasurableUtility
          b2CounterexampleUnmeasurableUtility)
        b2CounterexampleTargetCutoff 0 (1 - b2CounterexampleRho) :=
  proposition_B2_printed_conclusion_false_for_source_family

/--
Definition: second-price effort formula from the source theorem.  This is the
formula target used by the local two-level and finite reward-band
paper-facing endpoints below.
-/
noncomputable abbrev definition_second_price_effort_formula :=
  secondPriceEffort

/--
Theorem formula check: the second-price effort expression gives the source
within-band post-effort score
`max { g(tilde e_{k-1}) f(c_k), g(e0) f(theta) }` when `gInv` is a right
inverse for `g`.
-/
theorem theorem_second_price_effort_score_formula
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g) :
    g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta =
      max (g tildePrev * f c) (g e0 * f theta) :=
  secondPriceEffort_score_eq_max_of_rightInverse hg_mono hf_theta_pos hInv

/--
Theorem `lem:effort` within-band effort monotonicity: under the displayed
second-price formula, effort weakly decreases with type inside a reward band
when `f` and `gInv` are increasing and the boundary target is nonnegative.
-/
theorem theorem_second_price_effort_antitone_within_band
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hboundary_nonneg : 0 ≤ g tildePrev * f c)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hgInv_mono : Monotone gInv) :
    ∀ {theta₁ theta₂ : ℝ}, theta₁ ≤ theta₂ →
      secondPriceEffort e0 gInv g f tildePrev c theta₂
        ≤ secondPriceEffort e0 gInv g f tildePrev c theta₁ :=
  secondPriceEffort_antitone_within_band
    hboundary_nonneg hf_pos hf_mono hgInv_mono

/--
Theorem `lem:effort` within-band score monotonicity: the post-effort score
generated by the displayed second-price effort formula weakly increases with
type inside a reward band.
-/
theorem theorem_second_price_score_mono_within_band
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g) :
    ∀ {theta₁ theta₂ : ℝ}, theta₁ ≤ theta₂ →
      g (secondPriceEffort e0 gInv g f tildePrev c theta₁) * f theta₁
        ≤ g (secondPriceEffort e0 gInv g f tildePrev c theta₂) * f theta₂ :=
  secondPriceEffort_score_mono_within_band_of_rightInverse
    hg_mono hf_pos hf_mono hbaseline_nonneg hInv

/--
Theorem `lem:effort` source-rank score monotonicity: if the score map is the
second-price formula evaluated at source rank, then source-rank order implies
post-effort score order.
-/
theorem theorem_second_price_score_mono_of_source_rank_formula
    {α : Type*} {preRank score : α → ℝ}
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g)
    (hscore_formula :
      ∀ x,
        score x =
          g (secondPriceEffort e0 gInv g f tildePrev c (preRank x))
            * f (preRank x)) :
    ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
  secondPriceEffort_score_mono_of_source_rank_formula
    hg_mono hf_pos hf_mono hbaseline_nonneg hInv hscore_formula

/--
Theorem `lem:effort` best-response ingredient: any feasible alternative effort
that reaches the adjacent boundary score has weakly higher cost than the
source second-price effort formula.
-/
theorem theorem_second_price_effort_min_cost_to_reach_boundary
    {e0 tildePrev c theta d : ℝ} {cost gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hd_feasible : e0 ≤ d)
    (hreach : g tildePrev * f c ≤ g d * f theta) :
    cost (secondPriceEffort e0 gInv g f tildePrev c theta) ≤ cost d :=
  secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
    hg_strict hf_theta_pos hInv hcost_mono hd_feasible hreach

/--
Theorem `lem:effort` two-level low-band best-response core: a low-band
applicant cannot profit from any deviation when high-reaching deviations must
cross the source boundary score and the boundary cost equals the high-low
reward gap.
-/
theorem theorem_second_price_two_level_low_band_best_response
    {lowReward highReward e0 tilde c theta : ℝ}
    {cost g f : ℝ → ℝ} {reachesHigh : ℝ → Prop}
    [DecidablePred reachesHigh]
    (hg_strict : StrictMono g)
    (hfc_pos : 0 < f c)
    (hf_theta_le_cutoff : f theta ≤ f c)
    (hg_deviation_nonneg : ∀ d, reachesHigh d → 0 ≤ g d)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hreaches_boundary :
      ∀ d, reachesHigh d → e0 ≤ d → g tilde * f c ≤ g d * f theta)
    (hdeviation_feasible : ∀ d, reachesHigh d → e0 ≤ d) :
    ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
      ≤ lowReward - cost e0 :=
  secondPrice_twoLevel_low_band_best_response_of_score_boundary
    hg_strict hfc_pos hf_theta_le_cutoff hg_deviation_nonneg hcost_mono
    hbase_min htilde_feasible htilde_cost hreaches_boundary
    hdeviation_feasible

/--
Theorem `lem:effort` two-level high-band best-response core: a high-band
applicant using the displayed second-price effort cannot profit by dropping
to the low band or by choosing any other effort that still reaches the
high-band boundary score.
-/
theorem theorem_second_price_two_level_high_band_best_response
    {lowReward highReward e0 tilde c theta : ℝ}
    {cost gInv g f : ℝ → ℝ} {reachesHigh : ℝ → Prop}
    [DecidablePred reachesHigh]
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hboundary_reaches_at_theta :
      g tilde * f c ≤ g tilde * f theta)
    (hreaches_boundary :
      ∀ d, reachesHigh d → e0 ≤ d → g tilde * f c ≤ g d * f theta)
    (hdeviation_feasible : ∀ d, reachesHigh d → e0 ≤ d) :
    ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
      ≤ highReward -
        cost (secondPriceEffort e0 gInv g f tilde c theta) :=
  secondPrice_twoLevel_high_band_best_response_of_score_boundary
    hg_strict hf_theta_pos hInv hcost_mono hbase_min htilde_feasible
    htilde_cost hboundary_reaches_at_theta hreaches_boundary
    hdeviation_feasible

/--
Theorem `lem:effort` two-level source best-response theorem: if the rank layer
is exactly low/high, low-band applicants choose the minimum-cost effort, and
high-band applicants choose the displayed second-price effort, then the whole
two-level profile satisfies the source rank best-response predicate.
-/
theorem theorem_second_price_two_level_source_rank_best_response
    {α : Type*}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hg_deviation_nonneg :
      ∀ x d, reachesHigh x d → 0 ≤ g d)
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d) :
    SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort :=
  secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
    hg_strict hInv hcost_mono hbase_min htilde_feasible htilde_cost
    hlevel_zero hlevel_one hactual_reaches hlevel heffort_low heffort_high
    hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
    hg_deviation_nonneg hreaches_boundary hdeviation_feasible

/--
Theorem `lem:effort` two-level source best-response theorem for the displayed
effort function itself: low-band applicants use the baseline effort and
high-band applicants use the second-price boundary formula by definition, so
the wrapper does not expose separate low/high effort equalities.
-/
theorem theorem_second_price_two_level_source_rank_best_response_of_effort_function
    {α : Type*}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x,
        reachesHigh x
          (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x) ↔
            actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hg_deviation_nonneg :
      ∀ x d, reachesHigh x d → 0 ≤ g d)
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d) :
    SourceRankBestResponse cost rankOfEffort rankLevel levelReward
      (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta) :=
  secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries_function
    hg_strict hInv hcost_mono hbase_min htilde_feasible htilde_cost
    hlevel_zero hlevel_one hactual_reaches hlevel hf_cutoff_pos
    hf_low_le_cutoff hf_high_pos hboundary_reaches_high hg_deviation_nonneg
    hreaches_boundary hdeviation_feasible

/--
Theorem `lem:effort` two-level uniqueness direction: in the two-level source
threshold model, any source rank best response is forced pointwise to use the
displayed second-price effort formula.  This is the converse of the
construction theorem above and is the source-facing uniqueness ingredient for
the displayed profile.
-/
theorem theorem_second_price_two_level_effort_formula_unique_of_source_best_response
    {α : Type*}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hbase_low : ∀ x, ¬ actualHigh x → ¬ reachesHigh x e0)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hsp_high :
      ∀ x, actualHigh x →
        reachesHigh x (secondPriceEffort e0 gInv g f tilde c (theta x)))
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x :=
  secondPrice_twoLevel_effort_eq_source_formula_of_best_response
    hg_strict hInv hcost_mono hcost_strict hbase_min hlevel_zero hlevel_one
    hactual_reaches hlevel heffort_feasible hbase_low hf_high_pos
    hreaches_boundary hsp_high hbest

/--
Theorem `lem:effort` two-level uniqueness up to measure zero: an
almost-everywhere source rank best response in the two-level threshold model
agrees almost everywhere with the displayed second-price effort formula.
-/
theorem theorem_second_price_two_level_effort_formula_unique_ae_of_source_best_response
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hbase_low : ∀ x, ¬ actualHigh x → ¬ reachesHigh x e0)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hsp_high :
      ∀ x, actualHigh x →
        reachesHigh x (secondPriceEffort e0 gInv g f tilde c (theta x)))
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward
        effort) :
    ∀ᵐ x ∂μ,
      effort x =
        twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x :=
  secondPrice_twoLevel_effort_eq_source_formula_ae_of_best_responseAE
    hg_strict hInv hcost_mono hcost_strict hbase_min hlevel_zero hlevel_one
    hactual_reaches hlevel heffort_feasible hbase_low hf_high_pos
    hreaches_boundary hsp_high hbestAE

/--
Theorem `lem:effort`, two-level rank-preservation bridge: the concrete
two-level second-price best-response construction, together with the
source-shaped gamma endpoint that every open rank interval is realized and
that lexicographic score/tie improvements create positive lower-contour mass,
preserves pre-effort rank levels almost everywhere.
-/
theorem theorem_second_price_two_level_rank_preservationAE_of_gamma_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
      (fun x => rankLevel (preRank x)) :=
  secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_gamma_interval_dense
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward hInv hbase_min htilde_feasible htilde_cost hlevel_zero
    hlevel_one hactual_reaches hlevel heffort_low heffort_high
    hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
    hreaches_boundary hdeviation_feasible hpre_bound hpost_bound hcost_conv
    hcost_strict hg_conc hg_cont hg_strict hg_nonneg hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hpost_actual hequal_score_level
    hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist hdense hgap

/--
Theorem `lem:effort`, two-level rank-preservation bridge using reward
reachability rather than a global equal-score certificate.  The extra
source-shaped premise says that a deviation whose score reaches an actually
high applicant's score reaches the high band.
-/
theorem theorem_second_price_two_level_rank_preservationAE_of_gamma_interval_dense_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
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
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
      (fun x => rankLevel (preRank x)) :=
  secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_gamma_interval_dense_reward_reach
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward hInv hbase_min htilde_feasible htilde_cost hlevel_zero
    hlevel_one hlow_le_high hactual_reaches hlevel heffort_low heffort_high
    hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
    hreaches_boundary hdeviation_feasible hscore_reaches_high hpre_bound
    hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict hg_nonneg
    hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
    hscore_level_mono hscore_eq hpost_actual hpreRank_meas hscore_meas
    htie_meas hrankLevel_meas hpre_dist hdense hgap

/--
Theorem `lem:effort`, two-level rank-preservation bridge for the displayed
effort function itself, using the open-interval-density gamma endpoint.  This
keeps the genuine source gamma density/no-gap obligations visible while
removing redundant low/high effort equalities.
-/
theorem theorem_second_price_two_level_rank_preservationAE_of_gamma_interval_dense_effort_function
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x,
        reachesHigh x
          (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x) ↔
            actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
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
    (hscore_eq :
      ∀ x,
        score x =
          g (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x)
            * skill x)
    (hpost_actual :
      ∀ x,
        rankLevel
          (rankOfEffort x
            (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x)) =
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
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
  refine
    secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_gamma_interval_dense
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta
      (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta)
      levelReward hInv hbase_min htilde_feasible htilde_cost hlevel_zero
      hlevel_one hactual_reaches hlevel ?_ ?_
      hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
      hreaches_boundary hdeviation_feasible hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hpost_actual hequal_score_level
      hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist hdense hgap
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]

/--
Theorem `lem:effort`, two-level source-formula rank-preservation endpoint:
the source's low/high second-price score formulas, monotonicity of the source
type, upper-set high band, and source tie key `tie = preRank` imply a.e.
preservation of pre-effort rank levels.  This theorem isolates the rank-order
consequence from the separate best-response proof.
-/
theorem theorem_second_price_two_level_rank_preservationAE_of_piecewise_source_formula_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {gInv g f : ℝ → ℝ} {e0 tilde c : ℝ}
    (rankLevel : ℝ → ℕ) (preRank score tie theta : α → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  secondPrice_twoLevel_rankPreservationAE_of_piecewise_source_formula_and_tie_eq_preRank
    rankLevel preRank score tie theta hpreRank_meas hpre_dist hpre_range
    hg_mono hf_pos hf_mono hbaseline_nonneg hInv htheta_mono
    hactualHigh_upper hscore_low hscore_high htie_eq

/--
Theorem `lem:effort`, two-level source-equilibrium plus direct source-tie
rank preservation.  This bundles the two-level second-price best-response
proof with the direct rank-preservation consequence of the displayed
low/high score formulas and source tie key.  It avoids the older transport
surface: no post-rank bound, scalar gamma-CDF, dense-image, post-actual,
score-level, or equal-score level premise is needed for this source-tie
two-level route.
-/
theorem theorem_second_price_two_level_equilibrium_and_rank_preservationAE_of_piecewise_source_formula_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  constructor
  · exact sourceRankBestResponseAE_of_sourceRankBestResponse
      (theorem_second_price_two_level_source_rank_best_response
        hg_strict hInv hcost_mono hbase_min htilde_feasible htilde_cost
        hlevel_zero hlevel_one hactual_reaches hlevel heffort_low
        heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
        hboundary_reaches_high (fun _ d _ => hg_nonneg d)
        hreaches_boundary hdeviation_feasible)
  · exact
      theorem_second_price_two_level_rank_preservationAE_of_piecewise_source_formula_and_source_tie
        rankLevel preRank score tie theta hpreRank_meas hpre_dist
        hpre_range hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
        htheta_mono hactualHigh_upper hscore_low hscore_high htie_eq

/--
Theorem `lem:effort`, two-level displayed-effort-function source endpoint.
This is the same direct source-tie equilibrium/rank-preservation theorem, but
the effort profile is the source's displayed piecewise second-price function,
so the low/high effort equalities are derived by simplification.
-/
theorem theorem_second_price_two_level_equilibrium_and_rank_preservationAE_of_source_effort_function_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x,
        reachesHigh x
          (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x) ↔
            actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward
        (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta) ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  refine
    theorem_second_price_two_level_equilibrium_and_rank_preservationAE_of_piecewise_source_formula_and_source_tie
      preRank rankOfEffort rankLevel score tie theta
      (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta)
      levelReward hg_strict hInv hcost_mono hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel ?_ ?_
      hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
      hg_nonneg hreaches_boundary hdeviation_feasible hpreRank_meas
      hpre_dist hpre_range hf_pos hf_mono htheta_mono hactualHigh_upper
      hscore_low hscore_high htie_eq
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]

/--
Theorem `lem:effort`, two-level source-formula rank-preservation bridge: the
concrete two-level second-price best-response construction, the source's
piecewise low/high score formulas, monotonicity of the source type, and the
source tie key `tie = preRank` imply a.e. preservation of pre-effort rank
levels.  The multiplicative score equation is derived from the piecewise
source formulas rather than assumed separately.
-/
theorem theorem_second_price_two_level_rank_preservationAE_of_source_rank_formula
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
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
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_piecewise_score_mono_of_type_mono
      hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
      htheta_mono hactualHigh_upper hscore_low hscore_high
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
        hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
  secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_piecewise_source_formula_reward_reach
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward hInv hbase_min htilde_feasible htilde_cost hlevel_zero
    hlevel_one hlow_le_high hactual_reaches hlevel heffort_low heffort_high
    hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
    hreaches_boundary hdeviation_feasible hscore_reaches_high
    hpre_bound hpost_bound hcost_conv
    hcost_strict hg_conc hg_cont hg_strict hg_nonneg hskill_pos hskill_eq
    hskill_source hrankSkill_strict hpre_level_rank_order hscore_level_mono
    hpost_actual_ae hpreRank_meas hscore_meas htie_meas hrankLevel_meas
    hpre_dist hpre_range hf_pos hf_mono htheta_mono hactualHigh_upper
    hscore_low hscore_high htie_eq

/--
Theorem `lem:effort`, two-level source-formula rank-preservation bridge for
the displayed effort function itself.  This is the same source-shaped endpoint
as the previous theorem, but the low-band baseline effort and high-band
second-price effort formula are built into the profile rather than exposed as
separate theorem premises.
-/
theorem theorem_second_price_two_level_rank_preservationAE_of_source_effort_function
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    {cost gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x,
        reachesHigh x
          (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x) ↔
            actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel
          (rankOfEffort x
            (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_piecewise_score_mono_of_type_mono
      hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
      htheta_mono hactualHigh_upper hscore_low hscore_high
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
        hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
    intro x
    simpa [hrank_eq x] using hpre_bound x
  refine
    secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_piecewise_source_formula_reward_reach
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta
      (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta)
      levelReward hInv hbase_min htilde_feasible htilde_cost hlevel_zero
      hlevel_one hlow_le_high hactual_reaches hlevel ?_ ?_
      hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
      hreaches_boundary hdeviation_feasible hscore_reaches_high hpre_bound
      hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
      hg_nonneg hskill_pos hskill_eq hskill_source hrankSkill_strict
      hpre_level_rank_order hscore_level_mono hpost_actual_ae hpreRank_meas
      hscore_meas htie_meas hrankLevel_meas hpre_dist hpre_range hf_pos
      hf_mono htheta_mono hactualHigh_upper hscore_low hscore_high htie_eq
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]

/--
Theorem `lem:effort` finite separation step: if every previous-band score is
bounded above by the prior boundary score and the source cost equation has a
positive adjacent reward gap, then the second-price score in the next band is
strictly above every previous-band score.
-/
theorem theorem_second_price_finite_previous_band_score_separation
    {ι : Type*} {previousBands : Finset ι}
    {previousScore : ι → ℝ}
    {e0 prevAtCutoff tildePrev rewardGap c theta prevSup : ℝ}
    {cost gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hfc_pos : 0 < f c)
    (hInv : Function.RightInverse gInv g)
    (hprevious_le_sup :
      ∀ i ∈ previousBands, previousScore i ≤ prevSup)
    (hprevSup_le : prevSup ≤ g prevAtCutoff * f c)
    (hprev_le_tilde : prevAtCutoff ≤ tildePrev)
    (hcost :
      cost tildePrev = cost prevAtCutoff + rewardGap)
    (hgap : 0 < rewardGap) :
    ∀ i ∈ previousBands,
      previousScore i
        < g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta :=
  secondPrice_score_gt_finite_previousBand_scores_of_cost_gap
    hg_mono hg_strict hf_theta_pos hfc_pos
    (hInv (g tildePrev * f c / f theta)) hprevious_le_sup
    hprevSup_le hprev_le_tilde hcost hgap

/--
Theorem `lem:effort` finite upward no-jump step: adjacent second-price cost
equations along a finite reward chain telescope, so no lower-index band can
profitably jump to any higher-index band.
-/
theorem theorem_second_price_finite_upward_no_profit_between
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
          cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
              - reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)) :
    ∀ {i j : Fin (n + 1)}, i ≤ j →
      reward j - cost j ≤ reward i - cost i := by
  intro i j hij
  exact secondPrice_fin_chain_no_profit_of_adjacent_cost_equations
    reward cost hcost hij

/--
Theorem `lem:effort` finite downward no-jump step: adjacent downward
second-price cost equations along a finite reward chain telescope, so no
higher-index band can profitably jump to any lower-index band.
-/
theorem theorem_second_price_finite_downward_no_profit_between
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩ =
          cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            + (reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
              - reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)) :
    ∀ {i j : Fin (n + 1)}, i ≤ j →
      reward i - cost i ≤ reward j - cost j := by
  intro i j hij
  exact secondPrice_fin_reverse_chain_no_profit_of_adjacent_cost_equations
    reward cost hcost hij

/--
Theorem `lem:effort`, finite downward-deviation support: if the actual
applicant's downward effort interval is shorter and lies weakly to the left of
the boundary applicant's interval, convex increasing cost makes the actual cost
saving smaller than the boundary reward gap. Hence the downward deviation is
not profitable.
-/
theorem theorem_second_price_downward_no_profit_of_convex_boundary_gap
    {costFn : ℝ → ℝ} {e0 deviation actual boundaryLow boundaryHigh : ℝ}
    {rewardLow rewardHigh : ℝ}
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hdeviation_feasible : e0 ≤ deviation)
    (hboundaryLow_feasible : e0 ≤ boundaryLow)
    (hactual_gt_deviation : deviation < actual)
    (hactual_le_boundaryHigh : actual ≤ boundaryHigh)
    (hlen : actual - deviation < boundaryHigh - boundaryLow)
    (hboundaryGap :
      rewardHigh - rewardLow = costFn boundaryHigh - costFn boundaryLow) :
    rewardLow - costFn deviation ≤ rewardHigh - costFn actual :=
  secondPrice_downward_no_profit_of_convex_boundary_gap
    hcost_conv hcost_strict hdeviation_feasible hboundaryLow_feasible
    hactual_gt_deviation hactual_le_boundaryHigh hlen hboundaryGap

/--
Theorem `lem:effort` finite no-deviation core: adjacent source cost equations
imply that no finite band can profitably jump to any other finite band in
either direction.
-/
theorem theorem_second_price_finite_two_sided_no_profit_between
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
          cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
              - reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)) :
    (∀ {i j : Fin (n + 1)}, i ≤ j →
      reward j - cost j ≤ reward i - cost i)
    ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
      reward i - cost i ≤ reward j - cost j) :=
  secondPrice_fin_two_sided_no_profit_of_adjacent_cost_equations
    reward cost hcost

/--
Theorem `lem:effort` boundary-effort uniqueness: if a feasible boundary effort
solves the source cost equation and cost is strictly increasing on feasible
efforts, then that boundary effort is unique.
-/
theorem theorem_second_price_boundary_effort_unique
    {e0 target : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hcost_cont : Continuous cost)
    (hcost_atTop : Tendsto cost atTop atTop)
    (hlow : cost e0 ≤ target) :
    ∃! tilde, e0 ≤ tilde ∧ cost tilde = target :=
  secondPrice_boundaryEffort_unique_of_continuous_unbounded
    hcost_strict hcost_cont hcost_atTop hlow

/--
Theorem `lem:effort` finite boundary indifference: adjacent second-price cost
equations imply all finite boundary utilities `reward k - cost k` are equal.
-/
theorem theorem_second_price_finite_boundary_utilities_equal
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
          cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
              - reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)) :
    ∀ i j : Fin (n + 1), reward i - cost i = reward j - cost j :=
  secondPrice_fin_boundary_utilities_equal_of_adjacent_cost_equations
    reward cost hcost

/--
Theorem `lem:effort` finite boundary-effort construction: if source cost is
continuous, tends to infinity, is strictly increasing on feasible efforts, and
each finite boundary target lies above baseline cost, then the finite boundary
efforts exist uniquely and make all boundary utilities equal.
-/
theorem theorem_second_price_finite_boundary_efforts_exist_unique_and_indifferent
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 baseCost : ℝ} {costFn : ℝ → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hcost_cont : Continuous costFn)
    (hcost_atTop : Tendsto costFn atTop atTop)
    (hlow :
      ∀ i : Fin (n + 1),
        costFn e0 ≤ baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩)) :
    ∃ tilde : Fin (n + 1) → ℝ,
      (∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ i : Fin (n + 1),
        ∃! z, e0 ≤ z ∧
          costFn z =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward i - costFn (tilde i) ≤ reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward i - costFn (tilde i) =
          reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i)) :=
  secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent_of_continuous_unbounded
    reward hcost_strict hcost_cont hcost_atTop hlow

/--
Theorem `lem:effort` finite boundary-effort construction from monotone source
rewards: when the baseline band has weakly lowest reward, the above
low-target feasibility condition is derived in Lean.
-/
theorem theorem_second_price_finite_boundary_efforts_exist_unique_from_monotone_rewards
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 : ℝ} {costFn : ℝ → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hcost_cont : Continuous costFn)
    (hcost_atTop : Tendsto costFn atTop atTop)
    (hreward_base_le :
      ∀ i : Fin (n + 1), reward ⟨0, Nat.succ_pos n⟩ ≤ reward i) :
    ∃ tilde : Fin (n + 1) → ℝ,
      (∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            costFn e0 + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ i : Fin (n + 1),
        ∃! z, e0 ≤ z ∧
          costFn z =
            costFn e0 + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward i - costFn (tilde i) ≤ reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward i - costFn (tilde i) =
          reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i)) :=
  secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent_of_monotone_rewards
    reward hcost_strict hcost_cont hcost_atTop hreward_base_le

/--
Theorem `lem:effort` finite boundary-effort uniqueness as a function: any two
finite boundary-effort functions satisfying the same source cost equations
agree pointwise.
-/
theorem theorem_second_price_finite_boundary_efforts_function_unique
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 baseCost : ℝ} {costFn : ℝ → ℝ}
    {tilde₁ tilde₂ : Fin (n + 1) → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde₁_mem : ∀ i, e0 ≤ tilde₁ i)
    (htilde₂_mem : ∀ i, e0 ≤ tilde₂ i)
    (htilde₁ :
      ∀ i : Fin (n + 1),
        costFn (tilde₁ i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (htilde₂ :
      ∀ i : Fin (n + 1),
        costFn (tilde₂ i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩)) :
    tilde₁ = tilde₂ :=
  secondPrice_fin_boundaryEfforts_function_unique
    reward hcost_strict htilde₁_mem htilde₂_mem htilde₁ htilde₂

/--
Theorem `lem:effort` finite converse reduction: if an arbitrary finite-band
source best response has the same reward band when evaluated at the displayed
second-price formula, and if any underbid below that formula would create a
strict profitable deviation for a lower-band applicant, then the arbitrary
profile must equal the displayed formula pointwise.  The underbid-witness
premise is the remaining source converse argument; it is intentionally visible.
-/
theorem theorem_second_price_finite_effort_formula_unique_of_source_best_response_and_underbid_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hunderbid_profitable :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ y d,
            levelReward (rankLevel (rankOfEffort y (effort y))) -
                costFn (effort y) <
              levelReward (rankLevel (rankOfEffort y d)) - costFn d)
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_of_best_response_and_underbid_witness
    reward tilde cutoff actualBand hcost_strict heffort_feasible
    hactualLevel hformulaLevel hlevelReward hunderbid_profitable hbest

/--
Theorem `lem:effort` finite converse reduction, source-witness form: for any
attempted underbid below the displayed second-price formula, it is enough to
exhibit the lower-band applicant and deviation from the appendix, together
with the adjacent boundary cost equation. Lean then derives the strict
profitable deviation and forces equality with the displayed formula.
-/
theorem theorem_second_price_finite_effort_formula_unique_of_source_best_response_and_source_underbid_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hsource_underbid :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y d,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            rankLevel (rankOfEffort y d) = (actualBand x).val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            costFn d < costFn (tilde (actualBand x)) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_of_best_response_and_source_underbid_witness
    reward tilde cutoff actualBand hcost_strict heffort_feasible
    hactualLevel hformulaLevel hlevelReward hsource_underbid hbest

/--
Theorem `lem:effort` finite converse reduction, interval form: the source
appendix says that an underbid leaves a lower-band applicant an open interval
of deviations below the boundary effort that still reach the underbid
applicant's reward band. Given that interval and the adjacent boundary cost
equation, Lean chooses the deviation, derives the strict cost/profit
inequality, and forces equality with the displayed second-price formula.
-/
theorem theorem_second_price_finite_effort_formula_unique_of_source_best_response_and_lower_interval_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_interval :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α, ∃ lower : ℝ,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            e0 ≤ lower ∧
            e0 ≤ tilde (actualBand x) ∧
            lower < tilde (actualBand x) ∧
            (∀ d,
              lower < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_of_best_response_and_lower_interval_witness
    reward tilde cutoff actualBand hcost_strict heffort_feasible
    hactualLevel hformulaLevel hlevelReward hlower_interval hbest

/--
Theorem `lem:effort` finite converse reduction, cutoff-witness form: if every
underbid admits a lower-band boundary applicant whose source skill equals the
cutoff skill, and deviations between the computed score-matching effort and
the boundary effort reach the underbid applicant's band, then source best
response forces equality with the displayed second-price formula. Lean proves
the interval is nonempty from the underbid and the displayed formula.
-/
theorem theorem_second_price_finite_effort_formula_unique_of_source_best_response_and_lower_cutoff_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            e0 ≤ gInv (g (effort x) * f (theta x) / f (theta y)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_of_best_response_and_lower_cutoff_witness
    reward tilde cutoff actualBand hg_strict hInv hcost_strict
    heffort_feasible hf_theta_pos hactualLevel hformulaLevel hlevelReward
    hlower_cutoff hbest

/--
Theorem `lem:effort` finite converse reduction, almost-everywhere source
version: if source best-response inequalities and the lower-cutoff witness
argument hold on a full-measure good set, then any finite-band equilibrium
effort profile agrees almost everywhere with the displayed second-price effort
formula.  The lower-cutoff witness premise remains visible as the source
measure-zero boundary obligation.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_good_lower_cutoff_witness
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            e0 ≤ gInv (g (effort x) * f (theta x) / f (theta y)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_witness
    Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
    heffort_feasible hf_theta_pos hactualLevel hformulaLevel hlevelReward
    hlower_cutoff hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction, almost-everywhere ordered
source version: the source only needs to exhibit the lower cutoff applicant
and interval reachability on a full-measure good set. Lean derives feasibility
of the score-matching lower effort from source skill order, nonnegative effort
transfer, and the underbid inequality.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_good_ordered_lower_cutoff_witness
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_good_ordered_lower_cutoff_witness
    Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
    heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta hactualLevel
    hformulaLevel hlevelReward hlower_cutoff hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction, strongest current a.e.
source version: boundary cost equations supply the adjacent cost equality, and
source skill order supplies feasibility of the lower score-matching effort.
The visible witness is therefore the lower cutoff applicant plus interval
reachability on a full-measure good set.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_good_ordered_lower_cutoff_witness_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_good_ordered_lower_cutoff_witness_boundary_equations
    Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
    heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta htilde
    hactualLevel hformulaLevel hlevelReward hlower_cutoff hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction, lower-applicant a.e. source
version: if good-set applicants use their boundary efforts, the source witness
only needs a lower-band applicant at the cutoff skill and interval
reachability. Lean derives that applicant's band reward, boundary cost,
score-matching feasibility, and adjacent cost equation.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_good_lower_cutoff_applicant_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            actualBand y = prevBand ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_applicant_boundary_equations
    Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
    heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta htilde
    hactualLevel hformulaLevel hlevelReward heffort_boundary hlower_cutoff
    hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction, score-derived reachability
source version: the lower cutoff witness only names the lower-band applicant.
Lean derives interval reachability from explicit band-threshold facts saying
that strict score overtaking reaches at least the underbid applicant's band
and efforts below the boundary reach no higher than that band.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_good_lower_cutoff_applicant_score_reach_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hscore_overtake_reaches :
      ∀ x y d, Good x → Good y →
        g (effort x) * f (theta x) < g d * f (theta y) →
          actualBand x ≤ deviationBand y d)
    (hbelow_boundary_no_higher :
      ∀ x y d, Good x → Good y → d < tilde (actualBand x) →
        deviationBand y d ≤ actualBand x)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            actualBand y = prevBand ∧
            f (theta y) = f (cutoff (actualBand x)))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_applicant_score_reach_boundary_equations
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta
    htilde hactualLevel hdeviationLevel hformulaLevel hlevelReward
    heffort_boundary hscore_overtake_reaches hbelow_boundary_no_higher
    hlower_cutoff hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from global source support:
if the source supplies a lower cutoff applicant for every finite boundary,
then the underbid-specific lower applicant follows by instantiation. The
remaining visible model obligations are the full-measure good set, boundary
efforts, and score/boundary band-threshold facts.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_lower_cutoff_support_score_reach_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hscore_overtake_reaches :
      ∀ x y d, Good x → Good y →
        g (effort x) * f (theta x) < g d * f (theta y) →
          actualBand x ≤ deviationBand y d)
    (hbelow_boundary_no_higher :
      ∀ x y d, Good x → Good y → d < tilde (actualBand x) →
        deviationBand y d ≤ actualBand x)
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        f (theta y) = f (cutoff i))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_lower_cutoff_support_score_reach_boundary_equations
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta
    htilde hactualLevel hdeviationLevel hformulaLevel hlevelReward
    heffort_boundary hscore_overtake_reaches hbelow_boundary_no_higher
    hlower_cutoff_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from source cutoff order:
this is the strongest current finite a.e. converse row.  The paper-level
cutoff/type order and monotonicity of `f` imply the `f(cutoff) <= f(theta)`
condition used in the score-matching proof.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_lower_cutoff_support_score_reach_boundary_equations_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hscore_overtake_reaches :
      ∀ x y d, Good x → Good y →
        g (effort x) * f (theta x) < g d * f (theta y) →
          actualBand x ≤ deviationBand y d)
    (hbelow_boundary_no_higher :
      ∀ x y d, Good x → Good y → d < tilde (actualBand x) →
        deviationBand y d ≤ actualBand x)
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        f (theta y) = f (cutoff i))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_lower_cutoff_support_score_reach_boundary_equations_of_cutoff_order
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hcutoff_le_theta htilde hactualLevel hdeviationLevel hformulaLevel
    hlevelReward heffort_boundary hscore_overtake_reaches
    hbelow_boundary_no_higher hlower_cutoff_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction with source threshold
semantics.  This is the current strongest finite a.e. converse row: instead of
assuming the score/boundary reach conclusions directly, it uses finite-band
threshold semantics.  Boundary efforts are monotone, a deviation assigned to a
band must clear that band's boundary effort, deviations below a target band
have score no larger than a target-band applicant, and every source cutoff has
a good-set cutoff applicant.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_cutoff_support_thresholds_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_lower_score_bound :
      ∀ x y d, Good x → Good y →
        deviationBand y d < actualBand x →
          g d * f (theta y) ≤ g (effort x) * f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_thresholds_of_cutoff_order
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hcutoff_le_theta htilde_mono hdeviation_boundary
    hdeviation_lower_score_bound htilde hactualLevel hdeviationLevel
    hformulaLevel hlevelReward heffort_boundary hlower_cutoff_support
    hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction with band-target threshold
semantics.  This is the current strongest finite a.e. converse row: deviations
assigned below a target band have score at most that band's boundary target,
deviations assigned to a band must clear that band's boundary effort, boundary
efforts are monotone, and every source cutoff has a good-set cutoff applicant.
Lean derives the direct score-reach and boundary-reach facts used by the
underbid contradiction.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_cutoff_support_band_targets_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_below_target :
      ∀ y d i, Good y →
        deviationBand y d < i →
          g d * f (theta y) ≤ g (tilde i) * f (cutoff i))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_band_targets_of_cutoff_order
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hcutoff_le_theta htilde_mono hdeviation_boundary
    hdeviation_below_target htilde hactualLevel hdeviationLevel
    hformulaLevel hlevelReward heffort_boundary hlower_cutoff_support
    hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from per-band deviation score
upper bounds.  This is the current strongest finite a.e. converse row: every
deviation score is bounded by an upper bound for its assigned band, lower-band
upper bounds lie below later boundary targets, deviations assigned to a band
clear that band's boundary effort, boundary efforts are monotone, and every
source cutoff has a good-set cutoff applicant.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_cutoff_support_deviation_upper_bounds_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_target :
      ∀ {i j : Fin (n + 1)}, i < j →
        bandUpper i ≤ g (tilde j) * f (cutoff j))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_of_cutoff_order
    Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hcutoff_le_theta htilde_mono hdeviation_boundary
    hdeviation_score_le_upper hupper_le_target htilde hactualLevel
    hdeviationLevel hformulaLevel hlevelReward heffort_boundary
    hlower_cutoff_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from per-band deviation score
upper bounds and monotone boundary targets.  This is the current strongest
finite a.e. converse row: every deviation score is bounded by an upper bound
for its assigned band, each upper bound is below its own boundary target,
boundary targets are monotone, deviations assigned to a band clear that band's
boundary effort, boundary efforts are monotone, and every source cutoff has a
good-set cutoff applicant.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_cutoff_support_deviation_upper_bounds_and_monotone_targets_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_own_target :
      ∀ i : Fin (n + 1), bandUpper i ≤ g (tilde i) * f (cutoff i))
    (hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_and_monotone_targets_of_cutoff_order
    Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hcutoff_le_theta htilde_mono hdeviation_boundary
    hdeviation_score_le_upper hupper_le_own_target hbandTarget_mono
    htilde hactualLevel hdeviationLevel hformulaLevel hlevelReward
    heffort_boundary hlower_cutoff_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from source monotonicity and
per-band deviation score upper bounds.  This is the current strongest finite
a.e. converse row: monotone boundary efforts and cutoffs derive monotone
boundary targets, while per-band deviation score upper bounds and good-set
cutoff-applicant support provide the remaining source construction facts.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_global_cutoff_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_own_target :
      ∀ i : Fin (n + 1), bandUpper i ≤ g (tilde i) * f (cutoff i))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
    Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hf_cutoff_nonneg hcutoff_mono hcutoff_le_theta htilde_mono
    hdeviation_boundary hdeviation_score_le_upper hupper_le_own_target htilde
    hactualLevel hdeviationLevel hformulaLevel hlevelReward heffort_boundary
    hlower_cutoff_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from source monotonicity,
per-band deviation score upper bounds, and primitive cutoff-type support.  This
is the cleaner source-facing finite converse row: the source model supplies a
good-set applicant at each displayed cutoff type, and Lean recovers the
corresponding actual band internally.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_cutoff_type_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_own_target :
      ∀ i : Fin (n + 1), bandUpper i ≤ g (tilde i) * f (cutoff i))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ y : α, Good y ∧ theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
    Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hf_cutoff_nonneg hcutoff_mono hcutoff_le_theta htilde_mono
    hdeviation_boundary hdeviation_score_le_upper hupper_le_own_target htilde
    hactualLevel hdeviationLevel hformulaLevel hlevelReward heffort_boundary
    hcutoff_type_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from source threshold semantics.
This is the cleanest finite a.e. converse row: every deviation assigned to a
band has score at most that band's displayed boundary target, every displayed
cutoff type is represented on the good set, boundary efforts and cutoffs are
monotone, and best response holds on the good set.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_cutoff_type_support_source_thresholds_and_source_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_own_target :
      ∀ y d, Good y →
        g d * f (theta y) ≤
          g (tilde (deviationBand y d)) * f (cutoff (deviationBand y d)))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ y : α, Good y ∧ theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_source_thresholds_and_source_mono_of_cutoff_order
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
    hf_cutoff_nonneg hcutoff_mono hcutoff_le_theta htilde_mono
    hdeviation_boundary hdeviation_score_le_own_target htilde hactualLevel
    hdeviationLevel hformulaLevel hlevelReward heffort_boundary
    hcutoff_type_support hbest_good hgood_ae

/--
Theorem `lem:effort` finite converse reduction from source threshold semantics
and monotone reward levels.  Boundary-effort monotonicity is derived from the
displayed boundary cost equations, feasible boundary efforts, strict cost
monotonicity, and monotone source rewards.
-/
theorem theorem_second_price_finite_effort_formula_unique_ae_of_cutoff_type_support_source_thresholds_and_reward_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (hreward_mono : Monotone reward)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_own_target :
      ∀ y d, Good y →
        g d * f (theta y) ≤
          g (tilde (deviationBand y d)) * f (cutoff (deviationBand y d)))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ y : α, Good y ∧ theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) :=
  secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_source_thresholds_and_reward_mono_of_cutoff_order
    Good reward tilde cutoff actualBand deviationBand hg_strict hInv
    hcost_strict htilde_feasible heffort_feasible hg_nonneg hf_mono
    hf_theta_pos hcutoff_mono hcutoff_le_theta hreward_mono
    hdeviation_boundary hdeviation_score_le_own_target htilde hactualLevel
    hdeviationLevel hformulaLevel hlevelReward heffort_boundary hcutoff_type_support
    hbest_good hgood_ae

/--
Theorem `lem:effort` finite best-response bridge: if finite second-price
boundary costs make every boundary utility equal, the actual effort pays the
boundary cost of the actual reward band, and every deviation into a band costs
at least that band's boundary cost, then the source rank best-response
condition follows.  This exposes the remaining economic cost facts directly
instead of assuming best response as an unexplained primitive.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_costs
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward boundaryCost : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = boundaryCost (actualBand x))
    (hdeviationCost :
      ∀ x d, boundaryCost (deviationBand x d) ≤ costFn d)
    (hboundaryUtility :
      ∀ i j : Fin (n + 1),
        reward i - boundaryCost i = reward j - boundaryCost j) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_boundary_costs
    reward boundaryCost actualBand deviationBand hactualLevel
    hdeviationLevel hlevelReward hactualCost hdeviationCost hboundaryUtility

/--
Theorem `lem:effort` finite best-response bridge from boundary effort
equations: if the displayed finite boundary efforts satisfy
`cost(tilde i) = baseCost + (reward i - reward 0)`, and deviations into a band
cost at least that band's boundary effort, then source rank best-response
follows.  The equality of all boundary utilities is derived in Lean.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_equations
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations
    reward tilde actualBand deviationBand htilde hactualLevel
    hdeviationLevel hlevelReward hactualCost hdeviationCost

/--
Theorem `lem:effort` finite best-response bridge from boundary effort
equations with the source-shaped weak actual-cost condition: if an applicant's
chosen effort costs no more than the boundary effort for her realized band, and
every deviation into a band costs at least that band's boundary effort, then
source rank best response follows.  This matches the displayed second-price
formula inside a band, where non-boundary applicants can pay less than the
boundary type.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_equations_actual_le
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_actual_le
    reward tilde actualBand deviationBand htilde hactualLevel
    hdeviationLevel hlevelReward hactualCost_le hdeviationCost

/--
Theorem `lem:effort` finite best-response bridge for the displayed
second-price effort formula.  Boundary reachability and monotone cost derive
the actual-cost, same-band, and upward-deviation cost inequalities; downward
deviations remain as the source lower-band no-profit condition.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_equations_directional
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x))) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional
    reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_mono
    htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
    hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
    hup_reaches_boundary heffort_formula htilde hactualLevel hdeviationLevel
    hlevelReward hdownNoProfit

/--
Theorem `lem:effort` finite best-response bridge for the displayed
second-price effort formula, with the source-shaped downward comparison:
downward deviations are checked against the applicant's actual chosen effort,
not the boundary effort for her band. Boundary reachability and monotone cost
derive the actual-cost, same-band, and upward-deviation cost inequalities.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_equations_directional_actual_down
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x)) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional_actual_down
    reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_mono
    htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
    hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
    hup_reaches_boundary heffort_formula htilde hactualLevel hdeviationLevel
    hlevelReward hdownNoProfitActual

/--
Theorem `lem:effort` finite best-response bridge for the displayed
second-price effort formula, convex lower-deviation version: lower-band
no-profit is derived from the source convex boundary-gap argument rather than
assumed as a separate no-profit premise.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_equations_convex_down
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_effort_formula_convex_down
    reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
    hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
    hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
    hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
    hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
    hdown_actual_gt_deviation hdown_interval_len

/--
Theorem `lem:effort` a.e. finite best-response bridge for the displayed
second-price effort formula, convex lower-deviation version. This is the
measure-zero convention for the preceding pointwise best-response theorem.
-/
theorem theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponseAE_of_effort_formula_convex_down
    reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
    hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
    hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
    hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
    hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
    hdown_actual_gt_deviation hdown_interval_len

/--
Theorem `lem:effort` a.e. finite best-response bridge for the displayed
second-price effort formula, deriving the downward interval-length comparison
from the source's four multiplicative score equalities before applying the
convex boundary-gap argument.
-/
theorem theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down_from_score_equalities
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_effort_formula_convex_down_from_score_equalities
      reward tilde cutoff actualBand deviationBand
      downSkillLow downSkillHigh downScoreLow downScoreHigh
      hg_conc hg_strict hInv hcost_conv hcost_strict htilde_feasible
      hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
      hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
      hup_reaches_boundary heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_skillLow_pos hdown_skill_order
      hdown_scoreLow_nonneg hdown_score_order hdown_deviation_score
      hdown_actual_score hdown_boundaryLow_score hdown_boundaryHigh_score)

/--
Theorem `lem:effort` finite best-response bridge from boundary effort
thresholds: if source cost is monotone on feasible efforts, actual effort is
the displayed boundary effort for the actual band, and any deviation into a
band must meet that band's boundary effort, then source rank best-response
follows from the finite boundary equations.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_thresholds
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualEffort :
      ∀ x, effort x = tilde (actualBand x))
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponse_of_boundary_effort_thresholds
    reward tilde actualBand deviationBand hcost_mono htilde_feasible
    htilde hactualLevel hdeviationLevel hlevelReward hactualEffort
    hdeviationEffort

/--
Theorem `lem:effort` finite best-response bridge for the displayed boundary
effort function itself: if the actual profile is `tilde (actualBand x)`, the
actual-effort equality premise is built into the theorem statement.
-/
theorem theorem_second_price_finite_source_rank_best_response_of_boundary_effort_function
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) =
          (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward
      (fun x => tilde (actualBand x)) :=
  secondPrice_fin_sourceRankBestResponse_of_boundary_effort_function
    reward tilde actualBand deviationBand hcost_mono htilde_feasible htilde
    hactualLevel hdeviationLevel hlevelReward hdeviationEffort

/--
Theorem `lem:effort` a.e. finite best-response bridge from boundary effort
equations: the same finite boundary-equation construction gives an
almost-everywhere source rank best response under any applicant measure.
-/
theorem theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_equations
    reward tilde actualBand deviationBand htilde hactualLevel
    hdeviationLevel hlevelReward hactualCost hdeviationCost

/--
Theorem `lem:effort` a.e. finite best-response bridge from boundary effort
thresholds: source threshold-effort comparisons and boundary equations give an
almost-everywhere source rank best response under any applicant measure.
-/
theorem theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_thresholds
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualEffort :
      ∀ x, effort x = tilde (actualBand x))
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_thresholds
    reward tilde actualBand deviationBand hcost_mono htilde_feasible
    htilde hactualLevel hdeviationLevel hlevelReward hactualEffort
    hdeviationEffort

/--
Theorem `lem:effort` a.e. finite best-response bridge for the displayed
boundary-effort function: if the actual profile is the finite source
boundary-effort function itself, the actual-effort equality premise is
unnecessary.
-/
theorem theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_function
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) =
          (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward
      (fun x => tilde (actualBand x)) :=
  secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_function
    reward tilde actualBand deviationBand hcost_mono htilde_feasible htilde
    hactualLevel hdeviationLevel hlevelReward hdeviationEffort

/--
Theorem `lem:effort` finite score-order support: to show every lower band lies
below a higher band's boundary target, it is enough to give each band a score
upper bound and show those upper bounds are below later boundary targets.
-/
theorem theorem_second_price_finite_previous_bands_below_target_from_band_upper_bounds
    {α β : Type*} [Preorder β] {score : α → ℝ} {band : α → β}
    {bandUpper bandTarget : β → ℝ}
    (hscore_le_upper : ∀ y, score y ≤ bandUpper (band y))
    (hupper_le_target :
      ∀ {i j}, i < j → bandUpper i ≤ bandTarget j) :
    ∀ x y, band y < band x → score y ≤ bandTarget (band x) :=
  finiteBand_previous_bands_below_target_of_band_upper_bounds
    hscore_le_upper hupper_le_target

/--
Theorem `lem:effort` finite score-order support, source-max version: the
previous-band boundary-target condition follows from the displayed source
max-score formula, monotone boundary targets, and the fact that each baseline
score lies below its own band's boundary target.
-/
theorem theorem_second_price_finite_previous_bands_below_target_from_source_max_formula
    {α β : Type*} [Preorder β] {score theta : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (band x)) :
    ∀ x y, band y < band x → score y ≤ bandTarget (band x) :=
  finiteBand_previous_bands_below_target_of_source_max_formula
    hscore_formula hbandTarget_mono hbaseline_le_bandTarget

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint: finite
second-price boundary equations and threshold comparisons imply an a.e. source
best response, and the source-shaped gamma construction with `tie = preRank`
then preserves finite rank levels almost everywhere.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_boundary_thresholds_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ)
    (actualBand : α → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (hg_baseline_nonneg : 0 ≤ g e0)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x :=
    finiteBand_order_of_rankLevel_value hrankLevel_mono hactualBand_val
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    have hscore_within_band :
        ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
          score y ≤ score x :=
      finiteBand_within_score_mono_of_source_max_formula
        hf_mono hg_baseline_nonneg htheta_mono hscore_formula
    have hscore_between_bands :
        ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
      finiteBand_between_score_mono_of_boundary_targets
        hscore_formula hprevious_bands_below_target
    intro x y hpre
    have hband_le : actualBand y ≤ actualBand x :=
      hactualBand_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  exact Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint, source-max
version: the previous-band score-order premise is derived from the displayed
source max-score formula plus monotone boundary targets.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_source_max_order_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {g f : ℝ → ℝ} {e0 : ℝ}
    (rankLevel : ℝ → ℕ)
    (preRank score tie theta : α → ℝ)
    (actualBand : α → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  finiteBand_rankPreservationAE_of_source_max_formula_and_tie_eq_preRank
    rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
    hf_mono hbaseline_nonneg htheta_mono hscore_formula hbandTarget_mono
    hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint, source-max
version with weak actual costs: the source within-band second-price effort may
cost weakly less than the displayed boundary effort for its band, while any
deviation into a band must pay at least that band's boundary effort.  Together
with the displayed source max-score formula and source tie key, this gives
almost-everywhere rank preservation.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_source_max_order_actual_le_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    have hscore_within_band :
        ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
          score y ≤ score x :=
      finiteBand_within_score_mono_of_source_max_formula
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
    have hprevious_bands_below_target :
        ∀ x y, actualBand y < actualBand x →
          score y ≤ bandTarget (actualBand x) :=
      finiteBand_previous_bands_below_target_of_source_max_formula
        hscore_formula hbandTarget_mono hbaseline_le_bandTarget
    have hscore_between_bands :
        ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
      finiteBand_between_score_mono_of_boundary_targets
        hscore_formula hprevious_bands_below_target
    intro x y hpre
    have hband_le : actualBand y ≤ actualBand x :=
      hactualBand_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
        hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
  secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_actual_le_and_source_max_order_tie_eq_preRank
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward reward tilde actualBand deviationBand bandTarget htilde hactualLevel
    hdeviationLevel hlevelReward hactualCost_le hdeviationCost hpre_bound
    hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos hskill_eq hrankSkill_strict
    hpre_level_rank_order hscore_level_mono hscore_eq
    hpost_actual_ae
    hequal_score_level hpreRank_meas hscore_meas htie_meas hrankLevel_meas
    hpre_dist hpre_range hactualBand_order hf_mono htheta_mono
    hscore_formula hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint, source-max
version with the displayed second-price effort formula.  The actual-cost,
same-band, and upward-deviation cost checks are derived from boundary
reachability and monotone cost; only the source lower-band no-profit condition
remains explicit.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_source_max_order_directional_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x)))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    have hscore_within_band :
        ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
          score y ≤ score x :=
      finiteBand_within_score_mono_of_source_max_formula
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
    have hprevious_bands_below_target :
        ∀ x y, actualBand y < actualBand x →
          score y ≤ bandTarget (actualBand x) :=
      finiteBand_previous_bands_below_target_of_source_max_formula
        hscore_formula hbandTarget_mono hbaseline_le_bandTarget
    have hscore_between_bands :
        ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
      finiteBand_between_score_mono_of_boundary_targets
        hscore_formula hprevious_bands_below_target
    intro x y hpre
    have hband_le : actualBand y ≤ actualBand x :=
      hactualBand_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
        hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
  secondPrice_fin_rankPreservationAE_of_effort_formula_directional_and_source_max_order_tie_eq_preRank
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward reward tilde cutoff actualBand deviationBand bandTarget hInv
    htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
    hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
    hup_reaches_boundary heffort_formula htilde hactualLevel hdeviationLevel
    hlevelReward hdownNoProfit hpre_bound hpost_bound hcost_conv hcost_strict
    hg_conc hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hpost_actual hequal_score_level hpreRank_meas hscore_meas htie_meas
    hrankLevel_meas hpre_dist hpre_range hactualBand_order hf_mono
    htheta_mono hscore_formula hbandTarget_mono hbaseline_le_bandTarget
    htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint, source-shaped
downward version: the paper's displayed second-price effort formula is used for
the actual effort profile, and downward deviations are checked against the
applicant's actual chosen effort rather than the boundary effort for her band.
Actual, same-band, and upward costs are derived from boundary reachability and
monotone cost; only the source lower-band no-profit condition remains explicit.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_source_max_order_directional_actual_down_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    have hscore_within_band :
        ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
          score y ≤ score x :=
      finiteBand_within_score_mono_of_source_max_formula
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
    have hprevious_bands_below_target :
        ∀ x y, actualBand y < actualBand x →
          score y ≤ bandTarget (actualBand x) :=
      finiteBand_previous_bands_below_target_of_source_max_formula
        hscore_formula hbandTarget_mono hbaseline_le_bandTarget
    have hscore_between_bands :
        ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
      finiteBand_between_score_mono_of_boundary_targets
        hscore_formula hprevious_bands_below_target
    intro x y hpre
    have hband_le : actualBand y ≤ actualBand x :=
      hactualBand_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
        hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
  secondPrice_fin_rankPreservationAE_of_effort_formula_directional_actual_down_and_source_max_order_tie_eq_preRank
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward reward tilde cutoff actualBand deviationBand bandTarget hInv
    htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
    hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
    hup_reaches_boundary heffort_formula htilde hactualLevel hdeviationLevel
    hlevelReward hdownNoProfitActual hpre_bound hpost_bound hcost_conv
    hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
    hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
    hscore_level_mono hscore_eq hpost_actual hequal_score_level hpreRank_meas
    hscore_meas htie_meas hrankLevel_meas hpre_dist hpre_range hactualBand_order
    hf_mono htheta_mono hscore_formula hbandTarget_mono hbaseline_le_bandTarget
    htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint, convex
lower-deviation version: the displayed second-price effort formula gives the
actual profile, and the source downward-deviation check is derived from the
convex boundary-gap argument rather than assumed as a no-profit certificate.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_source_max_order_convex_down_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    have hscore_within_band :
        ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
          score y ≤ score x :=
      finiteBand_within_score_mono_of_source_max_formula
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
    have hprevious_bands_below_target :
        ∀ x y, actualBand y < actualBand x →
          score y ≤ bandTarget (actualBand x) :=
      finiteBand_previous_bands_below_target_of_source_max_formula
        hscore_formula hbandTarget_mono hbaseline_le_bandTarget
    have hscore_between_bands :
        ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
      finiteBand_between_score_mono_of_boundary_targets
        hscore_formula hprevious_bands_below_target
    intro x y hpre
    have hband_le : actualBand y ≤ actualBand x :=
      hactualBand_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K := by
    have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
      tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
        hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
    intro x
    simpa [hrank_eq x] using hpre_bound x
  exact
  secondPrice_fin_rankPreservationAE_of_effort_formula_convex_down_and_source_max_order_tie_eq_preRank
    K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
    levelReward reward tilde cutoff actualBand deviationBand bandTarget hInv
    htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
    hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
    hup_reaches_boundary heffort_formula htilde hactualLevel hdeviationLevel
    hlevelReward hdown_deviation_feasible hdown_actual_gt_deviation
    hdown_interval_len hpre_bound hpost_bound hcost_conv
    hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
    hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
    hscore_level_mono hscore_eq hpost_actual hequal_score_level hpreRank_meas
    hscore_meas htie_meas hrankLevel_meas hpre_dist hpre_range
    hactualBand_order hf_mono htheta_mono hscore_formula hbandTarget_mono
    hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint with the source
boundary score formula.  This specializes the convex lower-deviation endpoint
to the displayed boundary target `g(tilde_k) f(c_k)` and derives the
multiplicative score identity from the second-price effort formula, the
source skill identity `skill = f(theta)`, and the max-score formula.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_boundary_score_formula_convex_down_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)))
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤
        g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_eq : ∀ x, score x = g (effort x) * skill x :=
    secondPrice_fin_score_eq_of_effort_formula_and_source_max_formula
      tilde cutoff actualBand hg_strict.monotone hInv hf_theta_pos
      heffort_formula hskill_source hscore_formula
  exact
    theorem_second_price_finite_rank_preservationAE_of_source_max_order_convex_down_and_source_tie
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde cutoff actualBand deviationBand
      (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      hInv htilde_feasible hf_theta_pos hf_cutoff_pos
      hdeviation_same_feasible hdeviation_up_feasible
      hactual_reaches_boundary hsame_reaches_boundary hup_reaches_boundary
      heffort_formula htilde hactualLevel hdeviationLevel hlevelReward
      hdown_deviation_feasible hdown_actual_gt_deviation hdown_interval_len
      hpre_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
      hg_nonneg heffort_feasible hskill_pos hskill_eq hrankSkill_strict
      hpre_level_rank_order hscore_level_mono hscore_eq hpost_actual
      hequal_score_level hpreRank_meas hscore_meas htie_meas
      hrankLevel_meas hpre_dist hpre_range hactualBand_order hf_mono
      htheta_mono hscore_formula hbandTarget_mono hbaseline_le_bandTarget
      htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint with source
threshold-order reachability.  This replaces the three displayed product
reachability inequalities by the paper-facing facts that realized types are
above their cutoffs and deviations reaching a band use at least that band's
boundary effort.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_boundary_threshold_order_convex_down_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤
        g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) :=
    secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
      tilde cutoff actualBand deviationBand theta hg_strict.monotone
      hg_nonneg hf_mono (fun i => le_of_lt (hf_cutoff_pos i))
      hsame_boundary_le_deviation hcutoff_le_theta
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) :=
    secondPrice_up_reaches_boundary_of_boundary_le_deviation
      tilde cutoff actualBand deviationBand hg_strict.monotone
      (fun i => le_of_lt (hf_cutoff_pos i)) hup_boundary_le_deviation
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    rw [heffort_formula x]
    exact secondPriceEffort_ge_e0 e0 gInv g f
      (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)
  exact
    theorem_second_price_finite_rank_preservationAE_of_boundary_score_formula_convex_down_and_source_tie
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde cutoff actualBand deviationBand hInv
      htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
      hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
      hup_reaches_boundary heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_interval_len hpre_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hskill_source hrankSkill_strict
      hpre_level_rank_order hscore_level_mono hpost_actual hequal_score_level
      hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
      hpre_range hactualBand_order hf_mono htheta_mono hscore_formula
      hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus rank-preservation
endpoint.  From the displayed boundary cost equations, the second-price effort
formula, convex lower-deviation geometry, source score formula, and source tie
key, Lean derives both the a.e. best-response condition and preservation of
pre-effort rank levels.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_boundary_score_formula_convex_down_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)))
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤
        g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  constructor
  · exact
      theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
        hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
        hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
        hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
        hdown_actual_gt_deviation hdown_interval_len
  · exact
      theorem_second_price_finite_rank_preservationAE_of_boundary_score_formula_convex_down_and_source_tie
        K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
        levelReward reward tilde cutoff actualBand deviationBand hInv
        htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
        hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
        hup_reaches_boundary heffort_formula htilde hactualLevel
        hdeviationLevel hlevelReward hdown_deviation_feasible
        hdown_actual_gt_deviation hdown_interval_len hpre_bound hcost_conv
        hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
        hskill_pos hskill_eq hskill_source hrankSkill_strict
        hpre_level_rank_order hscore_level_mono hpost_actual hequal_score_level
        hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
        hpre_range hactualBand_order hf_mono htheta_mono hscore_formula
        hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus rank-preservation with
source threshold-order reachability.  The raw boundary-reachability product
inequalities are derived from cutoff/type order and boundary-effort threshold
facts before calling the bundled finite endpoint.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_boundary_threshold_order_convex_down_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
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
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤
        g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i) :=
    source_cutoff_pos_of_type_support hskill_pos hskill_source hcutoff_type_support
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) :=
    secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
      tilde cutoff actualBand deviationBand theta hg_strict.monotone
      hg_nonneg hf_mono (fun i => le_of_lt (hf_cutoff_pos i))
      hsame_boundary_le_deviation hcutoff_le_theta
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) :=
    secondPrice_up_reaches_boundary_of_boundary_le_deviation
      tilde cutoff actualBand deviationBand hg_strict.monotone
      (fun i => le_of_lt (hf_cutoff_pos i)) hup_boundary_le_deviation
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    rw [heffort_formula x]
    exact secondPriceEffort_ge_e0 e0 gInv g f
      (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_boundary_score_formula_convex_down_and_source_tie
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde cutoff actualBand deviationBand hInv
      htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
      hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
      hup_reaches_boundary heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_interval_len hpre_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hskill_source hrankSkill_strict
      hpre_level_rank_order hscore_level_mono hpost_actual hequal_score_level
      hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
      hpre_range hactualBand_order hf_mono htheta_mono hscore_formula
      hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus direct source-tie rank
preservation.  This is the clean finite source-facing endpoint: the
second-price best-response proof uses the displayed boundary cost equations
and threshold-order reachability, while rank preservation is proved directly
from the finite max-score formula and the public tie key `tie = preRank`.

Unlike the general transport bridge, this theorem does not ask for post-rank
boundedness, actual post-rank identification, score-level monotonicity, or
equal-score level certificates.  In the source-tie finite model, those are not
separate assumptions: monotone scores and source tie-breaking make the
tie-broken post-rank equal to the source pre-rank pointwise.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_boundary_threshold_order_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤
        g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i) := by
    intro i
    rcases hcutoff_type_support i with ⟨x, htheta⟩
    simpa [← htheta] using hf_theta_pos x
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) :=
    secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
      tilde cutoff actualBand deviationBand theta hg_strict.monotone
      hg_nonneg hf_mono (fun i => le_of_lt (hf_cutoff_pos i))
      hsame_boundary_le_deviation hcutoff_le_theta
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) :=
    secondPrice_up_reaches_boundary_of_boundary_le_deviation
      tilde cutoff actualBand deviationBand hg_strict.monotone
      (fun i => le_of_lt (hf_cutoff_pos i)) hup_boundary_le_deviation
  constructor
  · exact
      theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
        hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
        hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
        hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
        hdown_actual_gt_deviation hdown_interval_len
  · exact
      finiteBand_rankPreservationAE_of_source_max_formula_and_tie_eq_preRank
        rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus direct source-tie rank
preservation, using the source previous-band separation condition directly.

Compared with
`theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_boundary_threshold_order_direct_source_tie`,
this variant does not require the stronger own-band baseline bound.  The source
proof separates adjacent/lower bands by showing that every lower-band score is
below the later band's boundary target.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_previous_band_separation_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i) := by
    intro i
    rcases hcutoff_type_support i with ⟨x, htheta⟩
    simpa [← htheta] using hf_theta_pos x
  have hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d := by
    intro x d hsame
    exact le_trans (htilde_feasible (actualBand x))
      (hsame_boundary_le_deviation x d hsame)
  have hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d := by
    intro x d hup
    exact le_trans (htilde_feasible (deviationBand x d))
      (hup_boundary_le_deviation x d hup)
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) :=
    secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
      tilde cutoff actualBand deviationBand theta hg_strict.monotone
      hg_nonneg hf_mono (fun i => le_of_lt (hf_cutoff_pos i))
      hsame_boundary_le_deviation hcutoff_le_theta
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) :=
    secondPrice_up_reaches_boundary_of_boundary_le_deviation
      tilde cutoff actualBand deviationBand hg_strict.monotone
      (fun i => le_of_lt (hf_cutoff_pos i)) hup_boundary_le_deviation
  constructor
  · exact
      theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
        hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
        hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
        hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
        hdown_actual_gt_deviation hdown_interval_len
  · exact
      finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
        (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
        rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus arbitrary-tie
rank-level preservation.  The best-response proof uses source score equalities
for the downward-deviation geometry; the rank-preservation proof uses explicit
score-atom band bounds rather than `tie = preRank`.

The remaining rank premises are the auditable form of the paper-facing
tie-breaking condition: every score atom's tie-filled rank interval lies
between the lower and upper rank cutoffs for its source reward band, and
`rankLevel` is constant on that band interval.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_downward_score_equalities_and_score_atom_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (bandLower bandUpper : Fin (n + 1) → ℝ)
    (hatom_lower :
      ∀ x, bandLower (actualBand x) ≤
        (μ (scoreLowerContour score x)).toReal)
    (hatom_upper :
      ∀ x,
        (μ (scoreLowerContour score x)).toReal +
          (μ (scoreAtom score x)).toReal ≤ bandUpper (actualBand x))
    (hrank_band :
      ∀ x r,
        bandLower (actualBand x) ≤ r →
        r ≤ bandUpper (actualBand x) →
        rankLevel r = rankLevel (preRank x)) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d := by
    intro x d hsame
    exact le_trans (htilde_feasible (actualBand x))
      (hsame_boundary_le_deviation x d hsame)
  have hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d := by
    intro x d hup
    exact le_trans (htilde_feasible (deviationBand x d))
      (hup_boundary_le_deviation x d hup)
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) :=
    secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
      tilde cutoff actualBand deviationBand theta hg_strict.monotone
      hg_nonneg hf_mono (fun i => le_of_lt (hf_cutoff_pos i))
      hsame_boundary_le_deviation hcutoff_le_theta
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) :=
    secondPrice_up_reaches_boundary_of_boundary_le_deviation
      tilde cutoff actualBand deviationBand hg_strict.monotone
      (fun i => le_of_lt (hf_cutoff_pos i)) hup_boundary_le_deviation
  constructor
  · exact
      theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down_from_score_equalities
        reward tilde cutoff actualBand deviationBand downSkillLow
        downSkillHigh downScoreLow downScoreHigh hg_conc hg_strict hInv
        hcost_conv hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
        hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
        hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
        hdown_actual_gt_deviation hdown_skillLow_pos hdown_skill_order
        hdown_scoreLow_nonneg hdown_score_order hdown_deviation_score
        hdown_actual_score hdown_boundaryLow_score hdown_boundaryHigh_score
  · exact
      lemma_rank_preservation_ae_from_score_atom_band_bounds
        rankLevel hscore_meas htie_meas actualBand bandLower bandUpper
        hatom_lower hatom_upper hrank_band

/--
Theorem `lem:effort`, finite source-equilibrium plus direct source-tie rank
preservation, using source score equalities for the downward-deviation geometry.

Compared with the previous-band separation endpoint, this version does not
take the lower-band interval-length inequality as a premise.  It derives that
inequality from the paper's multiplicative score equalities and Appendix
Lemma `order_g`, then applies the convex boundary-gap argument.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_previous_band_separation_and_downward_score_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d := by
    intro x d hsame
    exact le_trans (htilde_feasible (actualBand x))
      (hsame_boundary_le_deviation x d hsame)
  have hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d := by
    intro x d hup
    exact le_trans (htilde_feasible (deviationBand x d))
      (hup_boundary_le_deviation x d hup)
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) :=
    secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
      tilde cutoff actualBand deviationBand theta hg_strict.monotone
      hg_nonneg hf_mono (fun i => le_of_lt (hf_cutoff_pos i))
      hsame_boundary_le_deviation hcutoff_le_theta
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) :=
    secondPrice_up_reaches_boundary_of_boundary_le_deviation
      tilde cutoff actualBand deviationBand hg_strict.monotone
      (fun i => le_of_lt (hf_cutoff_pos i)) hup_boundary_le_deviation
  constructor
  · exact
      theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_equations_convex_down_from_score_equalities
        reward tilde cutoff actualBand deviationBand downSkillLow
        downSkillHigh downScoreLow downScoreHigh hg_conc hg_strict hInv
        hcost_conv hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
        hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
        hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
        hdown_actual_gt_deviation hdown_skillLow_pos hdown_skill_order
        hdown_scoreLow_nonneg hdown_score_order hdown_deviation_score
        hdown_actual_score hdown_boundaryLow_score hdown_boundaryHigh_score
  · exact
      finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
        (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
        rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus direct source-tie rank
preservation, deriving previous-band separation from the displayed max-score
formula.  A lower-band score is a maximum of its own boundary target and
baseline score; target monotonicity and the lower-band baseline bound put both
terms below the later boundary target.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_lower_baseline_order_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hlower_baseline_le_later_target :
      ∀ x y, actualBand y < actualBand x →
        g e0 * f (theta y) ≤
          g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i) := by
    intro i
    rcases hcutoff_type_support i with ⟨x, htheta⟩
    simpa [← htheta] using hf_theta_pos x
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
      (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      hscore_formula hbandTarget_mono hlower_baseline_le_later_target
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_previous_band_separation_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward reward
      tilde cutoff actualBand deviationBand hInv htilde_feasible hf_theta_pos
      hcutoff_type_support hcutoff_le_theta hsame_boundary_le_deviation
      hup_boundary_le_deviation heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_interval_len hcost_conv hcost_strict
      hg_strict hg_nonneg hpreRank_meas hpre_dist hpre_range
      hactualBand_order hf_mono htheta_mono
      hscore_formula hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, strongest current finite direct source-tie endpoint.  This
combines the lower-baseline previous-band separation route with the source's
four multiplicative score equalities for downward deviations, so both the
downward effort order and the interval-length inequality are derived instead
of exposed as separate premises.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_lower_baseline_order_and_downward_score_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (hlower_baseline_le_later_target :
      ∀ x y, actualBand y < actualBand x →
        g e0 * f (theta y) ≤
          g (tilde (actualBand x)) * f (cutoff (actualBand x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
      (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      hscore_formula hbandTarget_mono hlower_baseline_le_later_target
  have hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x := by
    intro x d hdown
    exact
      (source_multiplicative_score_equalities_imply_effort_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)).1
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_previous_band_separation_and_downward_score_equalities_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward reward
      tilde cutoff actualBand deviationBand downSkillLow downSkillHigh
      downScoreLow downScoreHigh hInv htilde_feasible hf_theta_pos
      hf_cutoff_pos hcutoff_le_theta hsame_boundary_le_deviation
      hup_boundary_le_deviation heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_skillLow_pos hdown_skill_order
      hdown_scoreLow_nonneg hdown_score_order hdown_deviation_score
      hdown_actual_score hdown_boundaryLow_score hdown_boundaryHigh_score
      hcost_conv hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas
      hpre_dist hpre_range hactualBand_order hf_mono htheta_mono
      hscore_formula hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint with cutoff-interval
previous-band separation.  Lower-band separation is derived from the source
cutoff-interval order: every lower-band type is below the later band's cutoff.
Together with monotone `g`, monotone `f`, feasible boundary efforts, and the
source's downward multiplicative score equalities, this removes both the
previous-band baseline-score premise and the downward interval-length premise
from the paper-facing theorem surface.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_cutoff_interval_order_and_downward_score_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d)
    (hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_interval_upper :
      ∀ x y, actualBand y < actualBand x →
        theta y ≤ cutoff (actualBand x))
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x :=
    finiteBand_order_of_rankLevel_value hrankLevel_mono hactualBand_val
  have hlower_baseline_le_later_target :
      ∀ x y, actualBand y < actualBand x →
        g e0 * f (theta y) ≤
          g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_lower_baseline_le_later_target_of_cutoff_interval_order
      (band := actualBand) (theta := theta) (tilde := tilde)
      (cutoff := cutoff) hg_strict.monotone hg_nonneg hf_mono
      (fun x => le_of_lt (hf_theta_pos x)) htilde_feasible
      hcutoff_interval_upper
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_lower_baseline_order_and_downward_score_equalities_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward reward
      tilde cutoff actualBand deviationBand downSkillLow downSkillHigh
      downScoreLow downScoreHigh hInv htilde_feasible hf_theta_pos
      hf_cutoff_pos hcutoff_mono hreward_mono hcutoff_le_theta
      hsame_boundary_le_deviation hup_boundary_le_deviation heffort_formula
      htilde hactualLevel hdeviationLevel hlevelReward
      hdown_deviation_feasible hdown_skillLow_pos hdown_skill_order
      hdown_scoreLow_nonneg hdown_score_order hdown_deviation_score
      hdown_actual_score hdown_boundaryLow_score hdown_boundaryHigh_score
      hcost_conv hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas
      hpre_dist hpre_range hactualBand_order hf_mono htheta_mono
      hscore_formula hlower_baseline_le_later_target htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint with a single source
threshold-reachability premise for deviations.  If a deviation assigned to any
band uses at least that band's boundary effort, then Lean derives same-band
reachability, upward-band reachability, and downward-deviation feasibility
internally before invoking the cutoff-interval source-tie endpoint.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_source_threshold_reach_and_downward_score_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_boundary :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_interval_upper :
      ∀ x y, actualBand y < actualBand x →
        theta y ≤ cutoff (actualBand x))
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hsame_boundary_le_deviation :
      ∀ x d, deviationBand x d = actualBand x → tilde (actualBand x) ≤ d := by
    intro x d hsame
    simpa [hsame] using hdeviation_boundary x d
  have hup_boundary_le_deviation :
      ∀ x d, actualBand x < deviationBand x d →
        tilde (deviationBand x d) ≤ d := by
    intro x d _hup
    exact hdeviation_boundary x d
  have hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d := by
    intro x d _hdown
    exact le_trans (htilde_feasible (deviationBand x d))
      (hdeviation_boundary x d)
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_cutoff_interval_order_and_downward_score_equalities_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward reward
      tilde cutoff actualBand deviationBand downSkillLow downSkillHigh
      downScoreLow downScoreHigh hInv htilde_feasible hf_theta_pos
      hf_cutoff_pos hcutoff_mono hreward_mono hcutoff_le_theta
      hsame_boundary_le_deviation hup_boundary_le_deviation heffort_formula
      htilde hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_skillLow_pos hdown_skill_order hdown_scoreLow_nonneg
      hdown_score_order hdown_deviation_score hdown_actual_score
      hdown_boundaryLow_score hdown_boundaryHigh_score hcost_conv
      hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas hpre_dist
      hpre_range hrankLevel_mono hactualBand_val hf_mono htheta_mono
      hcutoff_interval_upper hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint with source rank-level
cutoff semantics.  This replaces the raw pairwise cutoff-interval premise by
the paper-shaped rule that every type in a strictly lower source rank level is
below the later level's displayed cutoff.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_rankLevel_cutoff_upper_and_source_threshold_reach_and_downward_score_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_boundary :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i) := by
    intro i
    rcases hcutoff_type_support i with ⟨x, htheta⟩
    simpa [← htheta] using hf_theta_pos x
  have hcutoff_interval_upper :
      ∀ x y, actualBand y < actualBand x →
        theta y ≤ cutoff (actualBand x) :=
    finiteBand_cutoff_interval_upper_of_rankLevel_value
      hactualBand_val hcutoff_upper_by_level
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_source_threshold_reach_and_downward_score_equalities_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward reward
      tilde cutoff actualBand deviationBand downSkillLow downSkillHigh
      downScoreLow downScoreHigh hInv htilde_feasible hf_theta_pos
      hf_cutoff_pos hcutoff_mono hreward_mono hcutoff_le_theta
      hdeviation_boundary heffort_formula htilde hactualLevel hdeviationLevel
      hlevelReward hdown_skillLow_pos hdown_skill_order hdown_scoreLow_nonneg
      hdown_score_order hdown_deviation_score hdown_actual_score
      hdown_boundaryLow_score hdown_boundaryHigh_score hcost_conv
      hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas hpre_dist
      hpre_range hrankLevel_mono hactualBand_val hf_mono htheta_mono
      hcutoff_interval_upper hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint with source rank-level
cutoffs and a score-threshold classifier for deviations.  This replaces the
stronger boundary-effort premise `tilde (deviationBand x d) <= d` by the
paper-shaped condition that a deviation assigned to a band reaches that band's
displayed score target.  Same-band and upward no-profit inputs are then
derived by Lean from the source cutoff order; downward geometry is still
derived from the paper's multiplicative score equalities.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_deviation_score_thresholds_and_rankLevel_cutoff_upper_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_feasible :
      ∀ (x : α) (d : ℝ), e0 ≤ d)
    (hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (theta x))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i) := by
    intro i
    rcases hcutoff_type_support i with ⟨x, htheta⟩
    simpa [← htheta] using hf_theta_pos x
  have hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x :=
    finiteBand_order_of_rankLevel_value hrankLevel_mono hactualBand_val
  have hcutoff_interval_upper :
      ∀ x y, actualBand y < actualBand x →
        theta y ≤ cutoff (actualBand x) :=
    finiteBand_cutoff_interval_upper_of_rankLevel_value
      hactualBand_val hcutoff_upper_by_level
  have hlower_baseline_le_later_target :
      ∀ x y, actualBand y < actualBand x →
        g e0 * f (theta y) ≤
          g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_lower_baseline_le_later_target_of_cutoff_interval_order
      (band := actualBand) (theta := theta) (tilde := tilde)
      (cutoff := cutoff) hg_strict.monotone hg_nonneg hf_mono
      (fun x => le_of_lt (hf_theta_pos x)) htilde_feasible
      hcutoff_interval_upper
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
      (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      hscore_formula hbandTarget_mono hlower_baseline_le_later_target
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hup_cutoff_upper :
      ∀ (x : α) (d : ℝ), actualBand x < deviationBand x d →
        theta x ≤ cutoff (deviationBand x d) := by
    intro x d hup
    exact hcutoff_upper_by_level (deviationBand x d) x (by
      rw [← hactualBand_val x]
      exact Fin.lt_def.mp hup)
  have hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x := by
    intro x d hdown
    exact
      (source_multiplicative_score_equalities_imply_effort_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)).1
  have hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d) := by
    intro x d hdown
    exact
      source_multiplicative_score_equalities_imply_effort_interval_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_conc hg_strict.monotone hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)
  constructor
  · exact
      secondPrice_fin_sourceRankBestResponseAE_of_score_thresholds_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hg_nonneg hInv
        hcost_conv hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hf_mono hdeviation_feasible hactual_reaches_boundary
        hdeviation_reaches_target hup_cutoff_upper heffort_formula htilde
        hactualLevel hdeviationLevel hlevelReward hdown_actual_gt_deviation
        hdown_interval_len
  · exact
      finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
        (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
        rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, feasible-domain finite direct source-tie endpoint with
source score-threshold semantics.  This is the source-shaped version of the
preceding bridge: deviations are only tested on the paper's feasible effort
domain, and the counterfactual rank classifier is exposed as the source fact
that a deviation assigned to a finite band reaches that band's displayed score
target.
-/
theorem theorem_second_price_finite_feasible_equilibrium_and_rank_preservationAE_of_deviation_score_thresholds_and_rankLevel_cutoff_upper_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (theta x))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
        levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x :=
    finiteBand_order_of_rankLevel_value hrankLevel_mono hactualBand_val
  have hcutoff_interval_upper :
      ∀ x y, actualBand y < actualBand x →
        theta y ≤ cutoff (actualBand x) :=
    finiteBand_cutoff_interval_upper_of_rankLevel_value
      hactualBand_val hcutoff_upper_by_level
  have hlower_baseline_le_later_target :
      ∀ x y, actualBand y < actualBand x →
        g e0 * f (theta y) ≤
          g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_lower_baseline_le_later_target_of_cutoff_interval_order
      (band := actualBand) (theta := theta) (tilde := tilde)
      (cutoff := cutoff) hg_strict.monotone hg_nonneg hf_mono
      (fun x => le_of_lt (hf_theta_pos x)) htilde_feasible
      hcutoff_interval_upper
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
      (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      hscore_formula hbandTarget_mono hlower_baseline_le_later_target
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hup_cutoff_upper :
      ∀ (x : α) (d : ℝ), actualBand x < deviationBand x d →
        theta x ≤ cutoff (deviationBand x d) := by
    intro x d hup
    exact hcutoff_upper_by_level (deviationBand x d) x (by
      rw [← hactualBand_val x]
      exact Fin.lt_def.mp hup)
  have hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x := by
    intro x d hdown
    exact
      (source_multiplicative_score_equalities_imply_effort_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)).1
  have hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d) := by
    intro x d hdown
    exact
      source_multiplicative_score_equalities_imply_effort_interval_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_conc hg_strict.monotone hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)
  constructor
  · exact
      secondPrice_fin_sourceRankBestResponseFeasibleAE_of_score_thresholds_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hg_nonneg hInv
        hcost_conv hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hf_mono hactual_reaches_boundary hdeviation_reaches_target
        hup_cutoff_upper heffort_formula htilde hactualLevel hdeviationLevel
        hlevelReward hdown_actual_gt_deviation hdown_interval_len
  · exact
      finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
        (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
        rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint from rank-level target
semantics.  This refines the score-threshold classifier endpoint by deriving
the classifier from the source multiplicative deviation score formula and the
rank-level lower target rule for each displayed finite band.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_rankLevel_targets_and_rankLevel_cutoff_upper_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ x : α, theta x = cutoff i)
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_feasible :
      ∀ (x : α) (d : ℝ), e0 ≤ d)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (theta x) :=
    finiteBand_deviation_reaches_target_of_rankLevel_target_lower
      hdeviationLevel hdeviation_score hrankLevel_target_lower
  exact
    theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_deviation_score_thresholds_and_rankLevel_cutoff_upper_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward reward
      tilde cutoff actualBand deviationBand downSkillLow downSkillHigh
      downScoreLow downScoreHigh hInv htilde_feasible hf_theta_pos
      hcutoff_type_support hcutoff_mono hreward_mono hcutoff_le_theta
      hdeviation_feasible hdeviation_reaches_target heffort_formula htilde
      hactualLevel hdeviationLevel hlevelReward hdown_skillLow_pos
      hdown_skill_order hdown_scoreLow_nonneg hdown_score_order
      hdown_deviation_score hdown_actual_score hdown_boundaryLow_score
      hdown_boundaryHigh_score hcost_conv hcost_strict hg_conc hg_strict
      hg_nonneg hpreRank_meas hpre_dist hpre_range hrankLevel_mono
      hactualBand_val hf_mono htheta_mono hcutoff_upper_by_level
      hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint on the source feasible
effort domain.  This is the same rank-level target/cutoff-upper route as
`theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_rankLevel_targets_and_rankLevel_cutoff_upper_direct_source_tie`,
but its best-response conclusion is the feasible-domain source equilibrium
(`d` is checked only when `e0 <= d`), matching the paper's effort domain and
removing the impossible global premise that every real-valued deviation is
feasible.
-/
theorem theorem_second_price_finite_feasible_equilibrium_and_rank_preservationAE_of_rankLevel_targets_and_rankLevel_cutoff_upper_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
        levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  have hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (theta x) :=
    finiteBand_deviation_reaches_target_of_rankLevel_target_lower
      hdeviationLevel hdeviation_score hrankLevel_target_lower
  have hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x :=
    finiteBand_order_of_rankLevel_value hrankLevel_mono hactualBand_val
  have hcutoff_interval_upper :
      ∀ x y, actualBand y < actualBand x →
        theta y ≤ cutoff (actualBand x) :=
    finiteBand_cutoff_interval_upper_of_rankLevel_value
      hactualBand_val hcutoff_upper_by_level
  have hlower_baseline_le_later_target :
      ∀ x y, actualBand y < actualBand x →
        g e0 * f (theta y) ≤
          g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_lower_baseline_le_later_target_of_cutoff_interval_order
      (band := actualBand) (theta := theta) (tilde := tilde)
      (cutoff := cutoff) hg_strict.monotone hg_nonneg hf_mono
      (fun x => le_of_lt (hf_theta_pos x)) htilde_feasible
      hcutoff_interval_upper
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  have hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)) :=
    secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg hf_mono
      (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono hcutoff_mono
  have hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
      (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      hscore_formula hbandTarget_mono hlower_baseline_le_later_target
  have hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    secondPrice_actual_reaches_boundary_of_cutoff_le_theta
      tilde cutoff actualBand theta hf_mono
      (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
  have hup_cutoff_upper :
      ∀ (x : α) (d : ℝ), actualBand x < deviationBand x d →
        theta x ≤ cutoff (deviationBand x d) := by
    intro x d hup
    exact hcutoff_upper_by_level (deviationBand x d) x (by
      rw [← hactualBand_val x]
      exact Fin.lt_def.mp hup)
  have hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x := by
    intro x d hdown
    exact
      (source_multiplicative_score_equalities_imply_effort_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)).1
  have hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d) := by
    intro x d hdown
    exact
      source_multiplicative_score_equalities_imply_effort_interval_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_conc hg_strict.monotone hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)
  constructor
  · exact
      secondPrice_fin_sourceRankBestResponseFeasibleAE_of_score_thresholds_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hg_nonneg hInv
        hcost_conv hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hf_mono hactual_reaches_boundary hdeviation_reaches_target
        hup_cutoff_upper heffort_formula htilde hactualLevel hdeviationLevel
        hlevelReward hdown_actual_gt_deviation hdown_interval_len
  · exact
      finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
        (bandTarget := fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
        rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint with finite bands
computed from the rank-level map itself.  The only classifier assumption is
that the source reward/rank map takes one of the displayed finite levels;
`actualBand` and `deviationBand` are then `rankLevel` packaged as `Fin`
indices, so they are not independent certificates.
-/
theorem theorem_second_price_finite_feasible_equilibrium_and_rank_preservationAE_of_bounded_rankLevel_targets_and_cutoff_upper_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hlevel_bound : ∀ z : ℝ, rankLevel z < n + 1)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)) ≤
        theta x)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = rankLevel (preRank x))
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreLow x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound
            (rankOfEffort x d))) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreHigh x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max
          (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
        levelReward effort ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  let actualBand : α → Fin (n + 1) :=
    fun x => finiteRankLevel rankLevel hlevel_bound (preRank x)
  let deviationBand : α → ℝ → Fin (n + 1) :=
    fun x d => finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d)
  exact
    theorem_second_price_finite_feasible_equilibrium_and_rank_preservationAE_of_rankLevel_targets_and_rankLevel_cutoff_upper_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta effort levelReward
      reward tilde cutoff actualBand deviationBand downSkillLow downSkillHigh
      downScoreLow downScoreHigh hInv htilde_feasible hf_theta_pos
      hf_cutoff_pos hcutoff_mono hreward_mono hcutoff_le_theta
      hdeviation_score hrankLevel_target_lower heffort_formula htilde
      (by
        intro x
        simpa [actualBand] using hactualLevel x)
      (by
        intro x d
        rfl)
      hlevelReward hdown_skillLow_pos hdown_skill_order
      hdown_scoreLow_nonneg hdown_score_order hdown_deviation_score
      hdown_actual_score hdown_boundaryLow_score hdown_boundaryHigh_score
      hcost_conv hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas
      hpre_dist hpre_range hrankLevel_mono
      (by
        intro x
        rfl)
      hf_mono htheta_mono hcutoff_upper_by_level hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie existence endpoint.  This is
the displayed-effort version of the bounded-rank-level theorem: the effort
profile is constructed as the source second-price formula, and Lean proves that
this constructed profile is a feasible-domain a.e. best response and preserves
rank levels, subject to the remaining explicit source threshold/boundary
conditions.
-/
theorem theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_bounded_rankLevel_targets_and_cutoff_upper_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hlevel_bound : ∀ z : ℝ, rankLevel z < n + 1)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_mono : Monotone reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)) ≤
        theta x)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel
          (rankOfEffort x
            (secondPriceEffort e0 gInv g f
              (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (theta x))) =
          rankLevel (preRank x))
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreHigh x d =
          g
            (secondPriceEffort e0 gInv g f
              (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (theta x)) *
            downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreLow x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound
            (rankOfEffort x d))) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downScoreHigh x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max
          (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    ∃ effort : α → ℝ,
      (∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (theta x)) ∧
      SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
          levelReward effort ∧
        (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
          (fun x => rankLevel (preRank x)) := by
  let effort : α → ℝ :=
    fun x =>
      secondPriceEffort e0 gInv g f
        (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
        (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
        (theta x)
  refine ⟨effort, ?_, ?_⟩
  · intro x
    rfl
  · exact
      theorem_second_price_finite_feasible_equilibrium_and_rank_preservationAE_of_bounded_rankLevel_targets_and_cutoff_upper_direct_source_tie
        preRank rankOfEffort rankLevel score tie theta effort levelReward
        reward tilde cutoff downSkillLow downSkillHigh downScoreLow
        downScoreHigh hlevel_bound hInv htilde_feasible hf_theta_pos
        hf_cutoff_pos hcutoff_mono hreward_mono hcutoff_le_theta
        hdeviation_score hrankLevel_target_lower
        (by
          intro x
          rfl)
        htilde hactualLevel hlevelReward hdown_skillLow_pos
        hdown_skill_order hdown_scoreLow_nonneg hdown_score_order
        hdown_deviation_score hdown_actual_score hdown_boundaryLow_score
        hdown_boundaryHigh_score hcost_conv hcost_strict hg_conc hg_strict
        hg_nonneg hpreRank_meas hpre_dist hpre_range hrankLevel_mono
        hf_mono htheta_mono hcutoff_upper_by_level hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie existence endpoint with the
downward score witnesses constructed internally.  The previous finite endpoint
exposed `downScoreLow` and `downScoreHigh` as auxiliary source rows; here they
are definitionally the two displayed boundary scores.  Their strict order is
derived from strict reward levels and the source boundary-cost equations, so
the paper-facing downward premises are only the low/high skill comparison and
the two multiplicative boundary equalities.
-/
theorem theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_bounded_rankLevel_targets_and_source_boundary_skill_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (downSkillLow downSkillHigh : α → ℝ → ℝ)
    (hlevel_bound : ∀ z : ℝ, rankLevel z < n + 1)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_strict : StrictMono reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)) ≤
        theta x)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel
          (rankOfEffort x
            (secondPriceEffort e0 gInv g f
              (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (theta x))) =
          rankLevel (preRank x))
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downSkillLow x d < downSkillHigh x d)
    (hdown_deviation_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g d * downSkillHigh x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound
            (rankOfEffort x d))) * downSkillLow x d)
    (hdown_actual_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g
          (secondPriceEffort e0 gInv g f
            (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (theta x)) *
          downSkillHigh x d =
            g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
              downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max
          (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    ∃ effort : α → ℝ,
      (∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (theta x)) ∧
      SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
          levelReward effort ∧
        (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
          (fun x => rankLevel (preRank x)) := by
  let actualBand : α → Fin (n + 1) :=
    fun x => finiteRankLevel rankLevel hlevel_bound (preRank x)
  let deviationBand : α → ℝ → Fin (n + 1) :=
    fun x d => finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d)
  let downScoreLow : α → ℝ → ℝ :=
    fun x d => g (tilde (deviationBand x d)) * downSkillLow x d
  let downScoreHigh : α → ℝ → ℝ :=
    fun x d => g (tilde (actualBand x)) * downSkillLow x d
  exact
    theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_bounded_rankLevel_targets_and_cutoff_upper_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta levelReward reward
      tilde cutoff downSkillLow downSkillHigh downScoreLow downScoreHigh
      hlevel_bound hInv htilde_feasible hf_theta_pos hf_cutoff_pos
      hcutoff_mono hreward_strict.monotone hcutoff_le_theta
      hdeviation_score hrankLevel_target_lower htilde hactualLevel
      hlevelReward hdown_skillLow_pos hdown_skill_order
      (by
        intro x d hdown
        simp [downScoreLow, deviationBand]
        exact mul_nonneg (hg_nonneg (tilde (finiteRankLevel rankLevel
          hlevel_bound (rankOfEffort x d)))) (le_of_lt
            (hdown_skillLow_pos x d hdown)))
      (by
        intro x d hdown
        simp [downScoreLow, downScoreHigh, actualBand, deviationBand]
        have htilde_lt :
            tilde (finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d)) <
              tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)) := by
          have hgap :
              reward (finiteRankLevel rankLevel hlevel_bound
                    (rankOfEffort x d)) -
                  reward ⟨0, Nat.succ_pos n⟩ <
                reward (finiteRankLevel rankLevel hlevel_bound (preRank x)) -
                  reward ⟨0, Nat.succ_pos n⟩ := by
            exact sub_lt_sub_right (hreward_strict hdown) _
          exact
            secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
              hcost_strict
              (htilde_feasible (finiteRankLevel rankLevel hlevel_bound
                (rankOfEffort x d)))
              (htilde_feasible (finiteRankLevel rankLevel hlevel_bound
                (preRank x)))
              (htilde (finiteRankLevel rankLevel hlevel_bound
                (rankOfEffort x d)))
              (htilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              hgap
        exact mul_lt_mul_of_pos_right (hg_strict htilde_lt)
          (hdown_skillLow_pos x d hdown))
      (by
        intro x d hdown
        simp [downScoreLow, deviationBand]
        exact (hdown_deviation_boundary_score x d hdown).symm)
      (by
        intro x d hdown
        simp [downScoreHigh, actualBand]
        exact (hdown_actual_boundary_score x d hdown).symm)
      (by
        intro x d hdown
        simp [downScoreLow, deviationBand])
      (by
        intro x d hdown
        simp [downScoreHigh, actualBand])
      hcost_conv hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas
      hpre_dist hpre_range hrankLevel_mono hf_mono htheta_mono
      hcutoff_upper_by_level hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie existence endpoint with the
counterfactual source-rank semantics exposed directly.  This legacy
compatibility endpoint is retained for proof-route comparison.  The
dashboard-facing finite-K endpoint below avoids overloading a single scalar as
both rank and score by constructing the counterfactual reward band from the
finite score-threshold classifier.
-/
theorem theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_source_deviation_thresholds_and_source_boundary_skill_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (downSkillLow downSkillHigh : α → ℝ → ℝ)
    (hlevel_bound : ∀ z : ℝ, rankLevel z < n + 1)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_strict : StrictMono reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)) ≤
        theta x)
    (hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d))) *
            f (cutoff
              (finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d))) ≤
          g d * f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel
          (rankOfEffort x
            (secondPriceEffort e0 gInv g f
              (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (theta x))) =
          rankLevel (preRank x))
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downSkillLow x d < downSkillHigh x d)
    (hdown_deviation_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g d * downSkillHigh x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound
            (rankOfEffort x d))) * downSkillLow x d)
    (hdown_actual_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g
          (secondPriceEffort e0 gInv g f
            (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (theta x)) *
          downSkillHigh x d =
            g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
              downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max
          (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    ∃ effort : α → ℝ,
      (∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (theta x)) ∧
      SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
          levelReward effort ∧
        (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
          (fun x => rankLevel (preRank x)) := by
  let actualBand : α → Fin (n + 1) :=
    fun x => finiteRankLevel rankLevel hlevel_bound (preRank x)
  let deviationBand : α → ℝ → Fin (n + 1) :=
    fun x d => finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d)
  let effort : α → ℝ :=
    fun x =>
      secondPriceEffort e0 gInv g f (tilde (actualBand x))
        (cutoff (actualBand x)) (theta x)
  let downScoreLow : α → ℝ → ℝ :=
    fun x d => g (tilde (deviationBand x d)) * downSkillLow x d
  let downScoreHigh : α → ℝ → ℝ :=
    fun x d => g (tilde (actualBand x)) * downSkillLow x d
  refine ⟨effort, ?_, ?_⟩
  · intro x
    rfl
  · exact
      theorem_second_price_finite_feasible_equilibrium_and_rank_preservationAE_of_deviation_score_thresholds_and_rankLevel_cutoff_upper_direct_source_tie
        preRank rankOfEffort rankLevel score tie theta effort levelReward
        reward tilde cutoff actualBand deviationBand downSkillLow
        downSkillHigh downScoreLow downScoreHigh hInv htilde_feasible
        hf_theta_pos hf_cutoff_pos hcutoff_mono hreward_strict.monotone
        (by
          intro x
          simpa [actualBand] using hcutoff_le_theta x)
        (by
          intro x d
          simpa [deviationBand] using hdeviation_reaches_target x d)
        (by
          intro x
          rfl)
        htilde
        (by
          intro x
          simpa [effort, actualBand] using hactualLevel x)
        (by
          intro x d
          rfl)
        hlevelReward
        (by
          intro x d hdown
          simpa [actualBand, deviationBand] using hdown_skillLow_pos x d hdown)
        (by
          intro x d hdown
          simpa [actualBand, deviationBand] using hdown_skill_order x d hdown)
        (by
          intro x d hdown
          simp [downScoreLow, deviationBand]
          exact mul_nonneg (hg_nonneg (tilde (finiteRankLevel rankLevel
            hlevel_bound (rankOfEffort x d)))) (le_of_lt
              (hdown_skillLow_pos x d hdown))
        )
        (by
          intro x d hdown
          simp [downScoreLow, downScoreHigh, actualBand, deviationBand]
          have htilde_lt :
              tilde (finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d)) <
                tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)) := by
            have hgap :
                reward (finiteRankLevel rankLevel hlevel_bound
                      (rankOfEffort x d)) -
                    reward ⟨0, Nat.succ_pos n⟩ <
                  reward (finiteRankLevel rankLevel hlevel_bound (preRank x)) -
                    reward ⟨0, Nat.succ_pos n⟩ := by
              exact sub_lt_sub_right (hreward_strict hdown) _
            exact
              secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
                hcost_strict
                (htilde_feasible (finiteRankLevel rankLevel hlevel_bound
                  (rankOfEffort x d)))
                (htilde_feasible (finiteRankLevel rankLevel hlevel_bound
                  (preRank x)))
                (htilde (finiteRankLevel rankLevel hlevel_bound
                  (rankOfEffort x d)))
                (htilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
                hgap
          exact mul_lt_mul_of_pos_right (hg_strict htilde_lt)
            (hdown_skillLow_pos x d hdown))
        (by
          intro x d hdown
          simp [downScoreLow, deviationBand]
          exact (hdown_deviation_boundary_score x d hdown).symm)
        (by
          intro x d hdown
          simp [downScoreHigh, actualBand]
          exact (hdown_actual_boundary_score x d hdown).symm)
        (by
          intro x d hdown
          simp [downScoreLow, deviationBand])
        (by
          intro x d hdown
          simp [downScoreHigh, actualBand])
        hcost_conv hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas
        hpre_dist hpre_range hrankLevel_mono
        (by
          intro x
          rfl)
        hf_mono htheta_mono hcutoff_upper_by_level
        (by
          intro x
          simpa [actualBand] using hscore_formula x)
        htie_eq

/--
Theorem `lem:effort`, finite direct source-tie endpoint without overloading a
single scalar as both rank and score.  Lean constructs the displayed
second-price effort profile, constructs the counterfactual reward band by the
finite score-threshold classifier `finiteScoreBand`, proves feasible-domain
finite-band best response directly, and separately proves rank preservation
from the source tie-broken score order.

Source status: source-facing finite-K endpoint for Lemma `lem:effort`.
-/
theorem theorem_second_price_finite_exists_feasible_band_best_response_and_rank_preservationAE_of_score_threshold_classifier_and_source_boundary_skill_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (downSkillLow downSkillHigh : α → ℝ → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_strict : StrictMono reward)
    (hcutoff_le_theta : ∀ x, cutoff (actualBand x) ≤ theta x)
    (hdeviation_bottom_reaches :
      ∀ x d, e0 ≤ d →
        g (tilde ⟨0, Nat.succ_pos n⟩) *
            f (cutoff ⟨0, Nat.succ_pos n⟩) ≤
          g d * f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hdown_skillLow_pos :
      ∀ x d,
        finiteScoreBand
            (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
            (g d * f (theta x)) < actualBand x →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteScoreBand
            (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
            (g d * f (theta x)) < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_deviation_boundary_score :
      ∀ x d,
        finiteScoreBand
            (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
            (g d * f (theta x)) < actualBand x →
        g d * downSkillHigh x d =
          g (tilde
            (finiteScoreBand
              (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
              (g d * f (theta x)))) * downSkillLow x d)
    (hdown_actual_boundary_score :
      ∀ x d,
        finiteScoreBand
            (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
            (g d * f (theta x)) < actualBand x →
        g
          (secondPriceEffort e0 gInv g f
            (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)) *
          downSkillHigh x d =
            g (tilde (actualBand x)) * downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hactualBand_val :
      ∀ x, (actualBand x).val = rankLevel (preRank x))
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    ∃ effort : α → ℝ,
      (∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)) ∧
      FiniteBandBestResponseFeasible e0 costFn reward actualBand
          (fun x d =>
            finiteScoreBand
              (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
              (g d * f (theta x)))
          effort ∧
        (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
          (fun x => rankLevel (preRank x)) := by
  let bandTarget : Fin (n + 1) → ℝ :=
    fun i => g (tilde i) * f (cutoff i)
  let deviationBand : α → ℝ → Fin (n + 1) :=
    fun x d => finiteScoreBand bandTarget (g d * f (theta x))
  let effort : α → ℝ :=
    fun x =>
      secondPriceEffort e0 gInv g f
        (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)
  refine ⟨effort, ?_, ?_⟩
  · intro x
    rfl
  · have hactualBand_order :
        ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x :=
      finiteBand_order_of_rankLevel_value hrankLevel_mono hactualBand_val
    have hcutoff_interval_upper :
        ∀ x y, actualBand y < actualBand x →
          theta y ≤ cutoff (actualBand x) :=
      finiteBand_cutoff_interval_upper_of_rankLevel_value
        hactualBand_val hcutoff_upper_by_level
    have hlower_baseline_le_later_target :
        ∀ x y, actualBand y < actualBand x →
          g e0 * f (theta y) ≤
            g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
      finiteBand_lower_baseline_le_later_target_of_cutoff_interval_order
        (band := actualBand) (theta := theta) (tilde := tilde)
        (cutoff := cutoff) hg_strict.monotone hg_nonneg hf_mono
        (fun x => le_of_lt (hf_theta_pos x)) htilde_feasible
        hcutoff_interval_upper
    have hgap_mono :
        Monotone (fun i : Fin (n + 1) =>
          reward i - reward ⟨0, Nat.succ_pos n⟩) := by
      intro i j hij
      exact sub_le_sub_right (hreward_strict.monotone hij) _
    have htilde_mono : Monotone tilde :=
      fun i j hij =>
        secondPrice_boundaryEffort_mono_of_rewardGap_mono
          hcost_strict (htilde_feasible i) (htilde_feasible j)
          (htilde i) (htilde j) (hgap_mono hij)
    have hbandTarget_mono : Monotone bandTarget :=
      secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg
        hf_mono (fun i => le_of_lt (hf_cutoff_pos i)) htilde_mono
        hcutoff_mono
    have hprevious_bands_below_target :
        ∀ x y, actualBand y < actualBand x →
          score y ≤ bandTarget (actualBand x) :=
      finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
        (bandTarget := bandTarget) hscore_formula hbandTarget_mono
        hlower_baseline_le_later_target
    have hactual_reaches_boundary :
        ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g (tilde (actualBand x)) * f (theta x) :=
      secondPrice_actual_reaches_boundary_of_cutoff_le_theta
        tilde cutoff actualBand theta hf_mono
        (fun x => hg_nonneg (tilde (actualBand x))) hcutoff_le_theta
    have hdeviation_reaches_target :
        ∀ x d, e0 ≤ d →
          bandTarget (deviationBand x d) ≤ g d * f (theta x) := by
      intro x d hd
      exact finiteScoreBand_target_le_of_bottom
        (target := bandTarget) (z := g d * f (theta x))
        (by
          simpa [bandTarget] using hdeviation_bottom_reaches x d hd)
    have hsame_reaches_boundary :
        ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
          g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
            g d * f (theta x) := by
      intro x d hd hsame
      simpa [bandTarget, deviationBand, hsame] using
        hdeviation_reaches_target x d hd
    have hup_cutoff_upper :
        ∀ (x : α) (d : ℝ), actualBand x < deviationBand x d →
          theta x ≤ cutoff (deviationBand x d) := by
      intro x d hup
      exact hcutoff_upper_by_level (deviationBand x d) x (by
        rw [← hactualBand_val x]
        exact Fin.lt_def.mp hup)
    have hup_reaches_boundary :
        ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
          g (tilde (deviationBand x d)) *
              f (cutoff (deviationBand x d)) ≤
            g d * f (cutoff (deviationBand x d)) := by
      intro x d hd hup
      exact le_trans (hdeviation_reaches_target x d hd)
        (mul_le_mul_of_nonneg_left
          (hf_mono (hup_cutoff_upper x d hup)) (hg_nonneg d))
    have htilde_strict_mono_on_bands :
        ∀ x d, deviationBand x d < actualBand x →
          tilde (deviationBand x d) < tilde (actualBand x) := by
      intro x d hdown
      have hgap :
          reward (deviationBand x d) - reward ⟨0, Nat.succ_pos n⟩ <
            reward (actualBand x) - reward ⟨0, Nat.succ_pos n⟩ := by
        exact sub_lt_sub_right (hreward_strict hdown) _
      exact
        secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
          hcost_strict (htilde_feasible (deviationBand x d))
          (htilde_feasible (actualBand x)) (htilde (deviationBand x d))
          (htilde (actualBand x)) hgap
    have hdown_scoreLow_nonneg :
        ∀ x d, deviationBand x d < actualBand x →
          0 ≤ g (tilde (deviationBand x d)) * downSkillLow x d := by
      intro x d hdown
      exact mul_nonneg (hg_nonneg (tilde (deviationBand x d)))
        (le_of_lt (hdown_skillLow_pos x d hdown))
    have hdown_score_order :
        ∀ x d, deviationBand x d < actualBand x →
          g (tilde (deviationBand x d)) * downSkillLow x d <
            g (tilde (actualBand x)) * downSkillLow x d := by
      intro x d hdown
      exact mul_lt_mul_of_pos_right
        (hg_strict (htilde_strict_mono_on_bands x d hdown))
        (hdown_skillLow_pos x d hdown)
    have hdown_actual_gt_deviation :
        ∀ x d, deviationBand x d < actualBand x → d < effort x := by
      intro x d hdown
      exact
        (source_multiplicative_score_equalities_imply_effort_order
          (g := g)
          (skillLow := downSkillLow x d)
          (skillHigh := downSkillHigh x d)
          (scoreLow := g (tilde (deviationBand x d)) * downSkillLow x d)
          (scoreHigh := g (tilde (actualBand x)) * downSkillLow x d)
          (e := d)
          (eToHigh := effort x)
          (eHighToLow := tilde (deviationBand x d))
          (eHigh := tilde (actualBand x))
          hg_strict
          (hdown_skillLow_pos x d hdown)
          (hdown_skill_order x d hdown)
          (hdown_scoreLow_nonneg x d hdown)
          (hdown_score_order x d hdown)
          (by
            dsimp [deviationBand] at hdown_deviation_boundary_score ⊢
            exact (hdown_deviation_boundary_score x d hdown).symm)
          (by
            dsimp [effort] at hdown_actual_boundary_score ⊢
            exact (hdown_actual_boundary_score x d hdown).symm)
          (by rfl)
          (by rfl)).1
    have hdown_interval_len :
        ∀ x d, deviationBand x d < actualBand x →
          effort x - d < tilde (actualBand x) - tilde (deviationBand x d) := by
      intro x d hdown
      exact
        source_multiplicative_score_equalities_imply_effort_interval_order
          (g := g)
          (skillLow := downSkillLow x d)
          (skillHigh := downSkillHigh x d)
          (scoreLow := g (tilde (deviationBand x d)) * downSkillLow x d)
          (scoreHigh := g (tilde (actualBand x)) * downSkillLow x d)
          (e := d)
          (eToHigh := effort x)
          (eHighToLow := tilde (deviationBand x d))
          (eHigh := tilde (actualBand x))
          hg_conc hg_strict.monotone hg_strict
          (hdown_skillLow_pos x d hdown)
          (hdown_skill_order x d hdown)
          (hdown_scoreLow_nonneg x d hdown)
          (hdown_score_order x d hdown)
          (by
            dsimp [deviationBand] at hdown_deviation_boundary_score ⊢
            exact (hdown_deviation_boundary_score x d hdown).symm)
          (by
            dsimp [effort] at hdown_actual_boundary_score ⊢
            exact (hdown_actual_boundary_score x d hdown).symm)
          (by rfl)
          (by rfl)
    constructor
    · exact
        secondPrice_fin_finiteBandBestResponseFeasible_of_effort_formula_convex_down_feasible_reach
          reward tilde cutoff actualBand deviationBand hg_strict hInv
          hcost_conv hcost_strict htilde_feasible hf_theta_pos
          hf_cutoff_pos hactual_reaches_boundary hsame_reaches_boundary
          hup_reaches_boundary (by intro x; rfl) htilde
          hdown_actual_gt_deviation hdown_interval_len
    · exact
        finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
          (bandTarget := bandTarget) rankLevel hpreRank_meas hpre_dist
          hpre_range hactualBand_order hf_mono (hg_nonneg e0)
          htheta_mono hscore_formula hprevious_bands_below_target htie_eq

/--
Theorem `lem:effort`, finite direct source-tie existence endpoint with
source score-band semantics.  This refines the preceding endpoint by deriving
the actual rank-level equality from the displayed second-price score formula:
the caller supplies lower/upper score bounds for each finite band and the
source classifier saying that scores in that band carry that rank level.
-/
theorem theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_score_band_bounds_and_source_boundary_skill_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (downSkillLow downSkillHigh : α → ℝ → ℝ)
    (hlevel_bound : ∀ z : ℝ, rankLevel z < n + 1)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_strict : StrictMono reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)) ≤
        theta x)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (hactual_score_upper :
      ∀ x,
        max
            (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
              f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
            (g e0 * f (theta x)) ≤
          bandUpper (finiteRankLevel rankLevel hlevel_bound (preRank x)))
    (hrank_score_band :
      ∀ i : Fin (n + 1), ∀ z,
        g (tilde i) * f (cutoff i) ≤ z →
        z ≤ bandUpper i →
        rankLevel z = i.val)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downSkillLow x d < downSkillHigh x d)
    (hdown_deviation_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g d * downSkillHigh x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound
            (rankOfEffort x d))) * downSkillLow x d)
    (hdown_actual_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g
          (secondPriceEffort e0 gInv g f
            (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (theta x)) *
          downSkillHigh x d =
            g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
              downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max
          (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    ∃ effort : α → ℝ,
      (∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (theta x)) ∧
      SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
          levelReward effort ∧
        (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
          (fun x => rankLevel (preRank x)) := by
  let actualBand : α → Fin (n + 1) :=
    fun x => finiteRankLevel rankLevel hlevel_bound (preRank x)
  have hactualLevel :
      ∀ x,
        rankLevel
          (rankOfEffort x
            (secondPriceEffort e0 gInv g f
              (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
              (theta x))) =
          rankLevel (preRank x) := by
    intro x
    have h :=
      finiteBand_actualLevel_of_secondPrice_score_band_bounds
        (tilde := tilde) (cutoff := cutoff) (bandUpper := bandUpper)
        (actualBand := actualBand) hg_strict.monotone hInv hf_theta_pos
        hdeviation_score
        (by
          intro y
          simpa [actualBand] using hactual_score_upper y)
        hrank_score_band x
    simpa [actualBand] using h
  exact
    theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_bounded_rankLevel_targets_and_source_boundary_skill_equalities_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta levelReward reward
      tilde cutoff downSkillLow downSkillHigh hlevel_bound hInv
      htilde_feasible hf_theta_pos hf_cutoff_pos hcutoff_mono
      hreward_strict hcutoff_le_theta hdeviation_score
      hrankLevel_target_lower htilde hactualLevel hlevelReward
      hdown_skillLow_pos hdown_skill_order hdown_deviation_boundary_score
      hdown_actual_boundary_score hcost_conv hcost_strict hg_conc
      hg_strict hg_nonneg hpreRank_meas hpre_dist hpre_range
      hrankLevel_mono hf_mono htheta_mono hcutoff_upper_by_level
      hscore_formula htie_eq

/--
Theorem `lem:effort`, finite direct source-tie existence endpoint with the
source score-band upper bound exposed in source form.  The caller states that
the realized source score lies below the upper boundary of its source band;
Lean rewrites that score through the displayed second-price formula to derive
the implementation-facing max-score upper bound used by the finite classifier.
-/
theorem theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_source_score_band_bounds_and_source_boundary_skill_equalities_direct_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (downSkillLow downSkillHigh : α → ℝ → ℝ)
    (hlevel_bound : ∀ z : ℝ, rankLevel z < n + 1)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hreward_strict : StrictMono reward)
    (hcutoff_le_theta :
      ∀ x, cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)) ≤
        theta x)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z)
    (hsource_score_upper :
      ∀ x, score x ≤
        bandUpper (finiteRankLevel rankLevel hlevel_bound (preRank x)))
    (hrank_score_band :
      ∀ i : Fin (n + 1), ∀ z,
        g (tilde i) * f (cutoff i) ≤ z →
        z ≤ bandUpper i →
        rankLevel z = i.val)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_skillLow_pos :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        downSkillLow x d < downSkillHigh x d)
    (hdown_deviation_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g d * downSkillHigh x d =
          g (tilde (finiteRankLevel rankLevel hlevel_bound
            (rankOfEffort x d))) * downSkillLow x d)
    (hdown_actual_boundary_score :
      ∀ x d,
        finiteRankLevel rankLevel hlevel_bound (rankOfEffort x d) <
          finiteRankLevel rankLevel hlevel_bound (preRank x) →
        g
          (secondPriceEffort e0 gInv g f
            (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
            (theta x)) *
          downSkillHigh x d =
            g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
              downSkillLow x d)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hrankLevel_mono : Monotone rankLevel)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i)
    (hscore_formula :
      ∀ x, score x =
        max
          (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
            f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
          (g e0 * f (theta x)))
    (htie_eq : ∀ x, tie x = preRank x) :
    ∃ effort : α → ℝ,
      (∀ x, effort x =
        secondPriceEffort e0 gInv g f
          (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x)))
          (theta x)) ∧
      SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
          levelReward effort ∧
        (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
          (fun x => rankLevel (preRank x)) := by
  have hactual_score_upper :
      ∀ x,
        max
            (g (tilde (finiteRankLevel rankLevel hlevel_bound (preRank x))) *
              f (cutoff (finiteRankLevel rankLevel hlevel_bound (preRank x))))
            (g e0 * f (theta x)) ≤
          bandUpper (finiteRankLevel rankLevel hlevel_bound (preRank x)) := by
    intro x
    simpa [hscore_formula x] using hsource_score_upper x
  exact
    theorem_second_price_finite_exists_feasible_equilibrium_and_rank_preservationAE_of_score_band_bounds_and_source_boundary_skill_equalities_direct_source_tie
      preRank rankOfEffort rankLevel score tie theta levelReward reward
      tilde cutoff bandUpper downSkillLow downSkillHigh hlevel_bound hInv
      htilde_feasible hf_theta_pos hf_cutoff_pos hcutoff_mono
      hreward_strict hcutoff_le_theta hdeviation_score
      hrankLevel_target_lower hactual_score_upper hrank_score_band htilde
      hlevelReward hdown_skillLow_pos hdown_skill_order
      hdown_deviation_boundary_score hdown_actual_boundary_score hcost_conv
      hcost_strict hg_conc hg_strict hg_nonneg hpreRank_meas hpre_dist
      hpre_range hrankLevel_mono hf_mono htheta_mono hcutoff_upper_by_level
      hscore_formula htie_eq

/--
Theorem `lem:effort`, finite-band rank-preservation endpoint, boundary-effort
function version: the paper's displayed finite boundary-effort function is used
as the actual effort profile, so the actual-effort equality and feasibility
premises are derived from the function itself.
-/
theorem theorem_second_price_finite_rank_preservationAE_of_boundary_effort_function_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) =
          (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    finiteBand_rankPreservationAE_of_source_max_formula_and_tie_eq_preRank
      rankLevel hpreRank_meas hpre_dist hpre_range hactualBand_order
      hf_mono (hg_nonneg e0) htheta_mono hscore_formula
      hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Theorem `lem:effort`, finite source-equilibrium plus rank-preservation
endpoint for the displayed boundary-effort function.  This combines the
finite best-response bridge for `x ↦ tilde (actualBand x)` with the
source-order rank-preservation theorem, so the boundary-effort function row
exposes the same paired conclusion as the stronger second-price formula rows.
-/
theorem theorem_second_price_finite_equilibrium_and_rank_preservationAE_of_boundary_effort_function_and_source_tie
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      MeasureTheory.Measure.map preRank μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward
        (fun x => tilde (actualBand x)) ∧
      (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
        (fun x => rankLevel (preRank x)) := by
  constructor
  · exact
      theorem_second_price_finite_source_rank_best_responseAE_of_boundary_effort_function
        reward tilde actualBand deviationBand hcost_strict.monotoneOn
        htilde_feasible htilde hactualLevel hdeviationLevel hlevelReward
        hdeviationEffort
  · exact
      theorem_second_price_finite_rank_preservationAE_of_boundary_effort_function_and_source_tie
        K preRank rankOfEffort rankLevel rankSkill skill score tie theta
        levelReward reward tilde actualBand deviationBand bandTarget htilde
        hactualLevel hdeviationLevel hlevelReward hdeviationEffort hpre_bound
        hcost_conv hcost_strict hg_conc hg_cont hg_strict hg_nonneg
        htilde_feasible hskill_pos hskill_eq hrankSkill_strict hpreRank_meas
        hpre_dist hpre_range hactualBand_order hf_mono htheta_mono
        hscore_formula hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Corollary `corr:effectcomparativestatics` boundary step: when the adjacent
reward gap in the second-price cost equation increases, the corresponding
boundary effort weakly increases under a strictly increasing cost function.
-/
theorem corollary_effort_comparative_statics_boundary_effort_mono
    {e0 baseCost gapLow gapHigh tildeLow tildeHigh : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeLow_mem : e0 ≤ tildeLow)
    (htildeHigh_mem : e0 ≤ tildeHigh)
    (hcostLow : cost tildeLow = baseCost + gapLow)
    (hcostHigh : cost tildeHigh = baseCost + gapHigh)
    (hgap : gapLow ≤ gapHigh) :
    tildeLow ≤ tildeHigh :=
  secondPrice_boundaryEffort_mono_of_rewardGap_mono
    hcost_strict htildeLow_mem htildeHigh_mem hcostLow hcostHigh hgap

/--
Corollary `corr:effectcomparativestatics` unchanged-gap step: if the relevant
adjacent reward gap is unchanged, the corresponding boundary effort is
unchanged under a strictly increasing cost function.
-/
theorem corollary_effort_comparative_statics_boundary_effort_unchanged
    {e0 baseCost gapLow gapHigh tildeLow tildeHigh : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeLow_mem : e0 ≤ tildeLow)
    (htildeHigh_mem : e0 ≤ tildeHigh)
    (hcostLow : cost tildeLow = baseCost + gapLow)
    (hcostHigh : cost tildeHigh = baseCost + gapHigh)
    (hgap : gapLow = gapHigh) :
    tildeLow = tildeHigh :=
  secondPrice_boundaryEffort_eq_of_rewardGap_eq
    hcost_strict htildeLow_mem htildeHigh_mem hcostLow hcostHigh hgap

/--
Corollary `corr:effectcomparativestatics` strict boundary step: on the part of
a band where the boundary effort is above the flat minimum-effort region, a
strictly larger adjacent reward gap gives a strictly larger boundary effort.
-/
theorem corollary_effort_comparative_statics_boundary_effort_strict
    {e0 baseCost gapLow gapHigh tildeLow tildeHigh : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeLow_mem : e0 ≤ tildeLow)
    (htildeHigh_mem : e0 ≤ tildeHigh)
    (hcostLow : cost tildeLow = baseCost + gapLow)
    (hcostHigh : cost tildeHigh = baseCost + gapHigh)
    (hgap : gapLow < gapHigh) :
    tildeLow < tildeHigh :=
  secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
    hcost_strict htildeLow_mem htildeHigh_mem hcostLow hcostHigh hgap

/--
Corollary `corr:effectcomparativestatics`, all-band boundary-equation layer:
for any finite or indexed family of source boundary efforts, each band effort
moves in the same direction as that band's reward-gap target under the source
cost equation.

Source status: source boundary-equation comparative-statics endpoint.
-/
theorem corollary_effort_comparative_statics_all_band_gap_order
    {β : Type*}
    {e0 baseCost : ℝ} {gapOld gapNew tildeOld tildeNew : β → ℝ}
    {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeOld_mem : ∀ k, e0 ≤ tildeOld k)
    (htildeNew_mem : ∀ k, e0 ≤ tildeNew k)
    (hcostOld : ∀ k, cost (tildeOld k) = baseCost + gapOld k)
    (hcostNew : ∀ k, cost (tildeNew k) = baseCost + gapNew k) :
    (∀ k, gapOld k ≤ gapNew k → tildeOld k ≤ tildeNew k)
    ∧ (∀ k, gapOld k = gapNew k → tildeOld k = tildeNew k)
    ∧ (∀ k, gapNew k ≤ gapOld k → tildeNew k ≤ tildeOld k) :=
  secondPrice_allBand_boundaryEffort_comparative_statics_of_gap_order
    hcost_strict htildeOld_mem htildeNew_mem hcostOld hcostNew

/--
Corollary `corr:effectcomparativestatics`, strict all-band boundary-equation
layer: under the same source boundary equations, any band's boundary effort
strictly increases when that band's reward-gap target strictly increases.

Source status: source boundary-equation strict comparative-statics endpoint.
-/
theorem corollary_effort_comparative_statics_all_band_gap_strict
    {β : Type*}
    {e0 baseCost : ℝ} {gapOld gapNew tildeOld tildeNew : β → ℝ}
    {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeOld_mem : ∀ k, e0 ≤ tildeOld k)
    (htildeNew_mem : ∀ k, e0 ≤ tildeNew k)
    (hcostOld : ∀ k, cost (tildeOld k) = baseCost + gapOld k)
    (hcostNew : ∀ k, cost (tildeNew k) = baseCost + gapNew k) :
    ∀ k, gapOld k < gapNew k → tildeOld k < tildeNew k :=
  secondPrice_allBand_boundaryEffort_strict_of_gap_strict
    hcost_strict htildeOld_mem htildeNew_mem hcostOld hcostNew

end LBG22StrategicRanking

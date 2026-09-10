import LBG22StrategicRanking.PaperInterface
import LBG22StrategicRanking.ArchivalStatements
import LBG22StrategicRanking.ApprovedMultitask
import LBG22StrategicRanking.MultidimensionalExamples
import LBG22StrategicRanking.MultitaskCounterexamples
import LBG22StrategicRanking.ApplicantWelfareCounterexamples
import LBG22StrategicRanking.GroupBaselineExamples
import LBG22StrategicRanking.EnvironmentExamples
import LBG22StrategicRanking.GroupSupportJunctionExamples
import LBG22StrategicRanking.UpperTailSkill

/-!
# Proofs of the strategic-ranking source statements
-/

namespace LBG22StrategicRanking.SourceProofs

open Set MeasureTheory

/-- All scalar source result contracts using `RankingEquilibrium` apply to
the stated score-priority equilibrium and conversely, without adding an
economic assumption or restricting the feasible deviations. -/
theorem rankingEquilibrium_scorePriority_iff
    {cost production skill tie effort score : ℝ → ℝ} {baseline rho : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hP : RankingPrimitives cost production skill baseline)
    (hpolicy : FiniteAdmissionPolicy n cutoff reward rho)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    RankingEquilibrium cost production skill tie n cutoff reward effort score ↔
      RankingScorePriorityEquilibrium cost production skill tie n cutoff reward effort score := by
  rcases hP with ⟨_, hp, _, _, _, _, hgM, _, _, _, hf, hf0⟩
  rcases hpolicy with ⟨_, _, _, hr, _⟩
  apply and_congr_right
  intro hs
  exact sourceFiniteBestResponse_ae_iff_scorePriority _ hp hgM hr.monotoneOn hf hf0 hs htie hinj

/-- The Section 4 equilibrium representation is equivalent under the same
source assumptions, including disjoint group supports and arbitrary known
injective priorities. -/
theorem environmentEquilibrium_scorePriority_iff
    {cost production skill : ℝ → ℝ} {psiA psiB baseline rho : ℝ}
    {tie effort score : Bool × ℝ → ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hP : RankingPrimitives cost production skill baseline)
    (hpolicy : FiniteAdmissionPolicy n cutoff reward rho) (hA : 0 < psiA) (hB : 0 < psiB)
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    EnvironmentEquilibrium cost production skill psiA psiB tie n cutoff reward effort score ↔
      EnvironmentScorePriorityEquilibrium cost production skill psiA psiB tie n cutoff reward effort score := by
  rcases hP with ⟨_, hp, _, _, _, _, hgM, _, _, _, hf, hf0⟩
  rcases hpolicy with ⟨_, _, _, hr, _⟩
  letI := noAtoms_map_sourceTwoGroup_of_injOn htie hinj
  apply and_congr_right
  intro hs
  exact scorePriorityBestResponse_ae_iff sourceTwoGroupMeasure _ hp hgM hr.monotoneOn
    (sourceEnvironmentSkill_positive_ae hf hf0 hA hB) hs htie

/-- Appendix B.1 needs no new positivity or budget assumption for the
boundary bridge: positive combined skill follows from simplex weights and
the source coordinate-skill primitives. -/
theorem multidimensionalEquilibrium_scorePriority_iff
    {m n : ℕ} {cost : ℝ → ℝ} {h rho : ℝ}
    {weight : Fin (m + 1) → ℝ} {skill : Fin (m + 1) → ℝ → ℝ}
    {cutoff reward : ℕ → ℝ} {effort : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ}
    {score tie : (Fin (m + 1) → ℝ) → ℝ}
    (hP : MultidimensionalPrimitives m cost h weight skill)
    (hpolicy : FiniteAdmissionPolicy n cutoff reward rho)
    (htie : Measurable tie) (hinj : InjOn tie {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}) :
    MultidimensionalEquilibrium m n cost h weight skill cutoff reward effort score tie ↔
      MultidimensionalScorePriorityEquilibrium m n cost h weight skill cutoff reward effort score tie := by
  rcases hP with ⟨hh, hw, hw1, hp, _, _, _, hf, hf0⟩
  rcases hpolicy with ⟨_, _, _, hr, _⟩
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  haveI : NoAtoms (sourceMultidimensionalPopulation (Fin (m + 1))) := by
    unfold sourceMultidimensionalPopulation
    infer_instance
  letI := noAtoms_map_tie_of_injOn_fullMeasure htie hinj
    (sourceMultidimensionalPopulation_ae_mem (Fin (m + 1)))
  apply and_congr_right
  intro hs
  exact sourceMultidimensionalBestResponse_ae_iff_scorePriority _ _ hp hh hr.monotoneOn
    ((sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos hw hw1 hf hf0).mono fun _ hx => hx.2)
    hs htie

/-- Appendix B.2's boundary clarification preserves every equilibrium at
every positive budget allowed by the public source primitives. No cost
normalization, unit-cost bound, or large-budget restriction is added. -/
theorem multitaskEquilibrium_scorePriority_iff
    {cost production skillM skillU : ℝ → ℝ} {B rho c : ℝ}
    {effortM effortU score tie : ℝ × ℝ → ℝ}
    (hP : MultitaskPrimitives cost production skillM skillU B rho)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (htie : Measurable tie)
    (hinj : InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1 ∧ x.2 ∈ Ioc (0 : ℝ) 1}) :
    MultitaskEquilibrium cost production skillM B rho c effortM effortU score tie ↔
      MultitaskScorePriorityEquilibrium cost production skillM B rho c effortM effortU score tie := by
  rcases hP with ⟨hB, hrho, hp, _, _, _, _, hg, _, hg0, hfc, hf, hf0, _⟩
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  have hmem : ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
      x.1 ∈ Ioc (0 : ℝ) 1 ∧ x.2 ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [(measurePreserving_fst (μ := unitRankMeasure) (ν := unitRankMeasure)).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioc),
      (measurePreserving_snd (μ := unitRankMeasure) (ν := unitRankMeasure)).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioc)] with x hx hy
    exact ⟨hx, hy⟩
  letI := noAtoms_map_tie_of_injOn_fullMeasure htie hinj hmem
  apply and_congr_right
  intro hs
  exact sourceIndependentHardBudgetBestResponse_ae_iff_scorePriority unitRankMeasure hB hrho.1
    (by linarith [hc.2, hrho.1]) (hp.mono Icc_subset_Ici_self) (hg.mono Icc_subset_Ici_self)
    hg0 hfc hf hf0 hs htie

theorem rankPreservation : RankPreservationSpec := by
  intro cost production skill tie effort score baseline rho n cutoff reward hP hpolicy htie hinj hEq
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, _, hf, hf0⟩
  rcases hpolicy with ⟨_, _, _, hr, _⟩
  have h := sourceFiniteEquilibrium_rank_preservation_of_sourcePrimitives
    (fun i : Fin (n + 1) => cutoff i) hb hp hpC hpN hp0 hg hgM hgC hg0 hf hf0 hr
    hEq.1 htie hinj hEq.2
  exact h.mono (fun _ ht => congrArg (fun i : Fin (n + 1) => reward i.val) ht)

theorem secondPriceEffort : SecondPriceEffortSpec := by
  intro cost production skill tie baseline rho n cutoff reward hP hpolicy htie hinj
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  rcases hpolicy with ⟨hc, hc0, hcn, hr, hr0, hrn, _⟩
  obtain ⟨E, hE, hpE, hm, hs, hu, hbest, hunique⟩ :=
    exists_unique_sourceFiniteBaselineEquilibrium_of_sourcePrimitives
      hb hp hpC hpN hp0 hg hgM hgC hg0 hc hc0 hcn hfc hf hf0 hr hr0 hrn htie hinj
  refine ⟨E, hE, hpE, hm, ⟨hs, hbest⟩, ?_, ?_, ?_⟩
  · exact hu.trans restrict_Ioc_eq_restrict_Icc.symm
  · have h := sourceFiniteEquilibrium_rank_preservation_of_sourcePrimitives
      (fun i : Fin (n + 1) => cutoff i) hb hp hpC hpN hp0 hg hgM hgC hg0 hf hf0 hr hs htie hinj hbest
    exact h.mono (fun _ ht => congrArg (fun i : Fin (n + 1) => reward i.val) ht)
  · intro otherEffort otherScore hEq
    exact hunique otherEffort otherScore hEq.1 hEq.2

/-- Proposition 3.1's pure-randomization conclusion survives for the whole
finite-policy class, without differentiability or extra shape restrictions. -/
theorem applicantWelfare_pureRandomization
    {cost production skill tie : ℝ → ℝ} {rho : ℝ}
    (hP : RankingPrimitives cost production skill 0)
    (_hrho : rho ∈ Ioo (0 : ℝ) 1)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    ∃ pureEffort pureScore : ℝ → ℝ,
      RankingEquilibrium cost production skill tie 0
        (fun k => if k = 0 then 0 else 1) (fun _ => rho) pureEffort pureScore ∧
      sourceFiniteApplicantWelfare cost pureEffort pureScore tie
        (fun _ : Fin 1 => 0) (fun _ => rho) = rho ∧
      ∀ (n : ℕ) (cutoff reward : ℕ → ℝ) (effort score : ℝ → ℝ),
        FiniteAdmissionPolicy n cutoff reward rho →
        RankingEquilibrium cost production skill tie n cutoff reward effort score →
        sourceFiniteApplicantWelfare cost effort score tie
          (fun i : Fin (n + 1) => cutoff i) reward ≤
        sourceFiniteApplicantWelfare cost pureEffort pureScore tie
          (fun _ : Fin 1 => 0) (fun _ => rho) := by
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  have h := sourcePureRandomization_equilibrium_and_welfare
    (production := production) (tie := tie) (rho := rho) hb hpN hp0 hfc
  refine ⟨(fun _ => 0), sourcePureRandomizationScore production skill 0,
    ⟨h.1, ?_⟩, h.2.2.2, ?_⟩
  · simpa only [Fin.eq_zero, Fin.val_zero, if_pos rfl] using h.2.1
  · intro n cutoff reward effort score hpolicy hEq
    rcases hpolicy with ⟨hc, hc0, hcn, hr, hr0, hrn, _, hcap⟩
    exact (sourceFiniteApplicantWelfare_maximized_by_pureRandomization_of_sourcePrimitives
      hb hp hpC hpN hp0 hg hgM hgC hg0 hc hc0 hcn hfc hf hf0 hr hr0 hrn hcap
      hEq.1 htie hinj hEq.2).2.2.2.2.2

/-- The universal two-level monotonicity clause fails in a smooth source
model with actual best responses and population welfare. -/
theorem applicantWelfare_refuted : ¬ ApplicantWelfareArchivalSpec := by
  intro hclaim
  have hP : RankingPrimitives (fun e : ℝ => e ^ 2) id ApplicantWelfareCounterexample.skill 0 :=
    ⟨le_rfl, (continuous_pow 2).continuousOn, quadraticCost_strictConvex,
      (fun e _ => sq_nonneg e), by norm_num, continuousOn_id, strictMono_id.strictMonoOn _,
      concaveOn_id (convex_Ici _), le_rfl, ApplicantWelfareCounterexample.skill_continuous,
      ApplicantWelfareCounterexample.skill_strictMono, by norm_num [ApplicantWelfareCounterexample.skill]⟩
  have hmono := (hclaim (fun e : ℝ => e ^ 2) id ApplicantWelfareCounterexample.skill id (3 / 10)
    hP (by norm_num) (differentiable_id.pow 2).differentiableOn differentiable_id.differentiableOn
    ApplicantWelfareCounterexample.skill_differentiable measurable_id (fun _ _ _ _ h => h)).2
    ApplicantWelfareCounterexample.effort ApplicantWelfareCounterexample.score
    (fun _ hc => ApplicantWelfareCounterexample.equilibrium hc measurable_id)
  exact (not_lt_of_ge (hmono (by norm_num : (1 / 10 : ℝ) ∈ Ioc 0 (1 - 3 / 10))
    (by norm_num : (1 / 5 : ℝ) ∈ Ioc 0 (1 - 3 / 10)) (by norm_num)))
    (ApplicantWelfareCounterexample.welfare_increases measurable_id (fun _ _ _ _ h => h))

/-- Proposition 3.1's monotonicity clause under concavity of log skill in
negative log upper-tail mass and geometric score-cost concavity. All actual
score-priority equilibria are covered; the conditions are local to this
comparison. `E` is the effort with cost one, which exists under the source
cost primitives and imposes no bound on feasible deviations. -/
theorem applicantWelfare_antitone_of_upperTailConcavity
    {cost production skill tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ} {E rho : ℝ}
    (hP : RankingPrimitives cost production skill 0)
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hE : 0 < E) (hpE : cost E = 1)
    (hfTail : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x => Real.log (skill (upperTailRank x))))
    (hscoreCost : ConcaveOn ℝ {z | production 0 < Real.exp z ∧ Real.exp z ≤ production E}
      (fun z => Real.log (cost (effortIntervalInverse production E (Real.exp z)))))
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hEq : ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      RankingScorePriorityEquilibrium cost production skill tie 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) :
    AntitoneOn (fun c => sourceFiniteApplicantWelfare cost (effort c) (score c) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c))
      (Ioc (0 : ℝ) (1 - rho)) := by
  rcases hP with ⟨_, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  have hfpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < skill t := fun t ht =>
    hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  apply sourceActualTwoLevelApplicantWelfare_antitone_of_skillRatio hrho.1 hE hpE hp hpC hpN hp0
    hg hgM hgC hg0 hfc hf hf0
    (fun _ hs => admittedTail_skill_ratio_monotone_of_upperTailConcavity hfpos
      (hf.monotoneOn.mono Ioc_subset_Icc_self) hfTail hs) hscoreCost htie hinj
    (fun c hc => (hEq c hc).1)
  intro c hc
  exact (sourceFiniteBestResponse_ae_iff_scorePriority _ hp hgM
    (sourceTwoLevelReward_strictMono hrho.1 (by linarith [hc.2, hrho.1])).monotoneOn hf hf0
    (hEq c hc).1 htie hinj).mpr (hEq c hc).2

/-- Both clauses of Proposition 3.1, with the primitive shape conditions
restricted to the two-level cutoff comparison. -/
theorem applicantWelfare : ApplicantWelfareSpec := by
  intro cost production skill tie rho hP hrho _ _ _ htie hinj
  refine ⟨applicantWelfare_pureRandomization hP hrho htie hinj, ?_⟩
  intro E hE hpE hfTail hscoreCost effort score hEq
  apply applicantWelfare_antitone_of_upperTailConcavity hP hrho hE hpE hfTail hscoreCost htie hinj
  rcases hP with ⟨_, hp, _, _, _, _, hgM, _, _, _, hf, hf0⟩
  intro c hc
  refine ⟨(hEq c hc).1, ?_⟩
  exact (sourceFiniteBestResponse_ae_iff_scorePriority _ hp hgM
    (sourceTwoLevelReward_strictMono hrho.1 (by linarith [hc.2, hrho.1])).monotoneOn hf hf0
    (hEq c hc).1 htie hinj).mp (hEq c hc).2

theorem privateUtility : PrivateUtilitySpec := by
  intro cost production skill tie effort score rho hP hrho _ _ _ htie hinj hEq
  rcases hP with ⟨_, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  exact sourceActualTwoLevelSchoolUtility_monotone_of_sourcePrimitives
    hrho.1 hrho.2 hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 htie hinj
    (fun c hc => (hEq c hc).1) (fun c hc => (hEq c hc).2)

theorem threeLevelImprovement : ThreeLevelImprovementSpec := by
  intro tie htie hinj
  let effort3 := sourceFiniteRankEffort (fun e => e ^ 2) id (fun t => t ^ 3) 1 2
    threeLevelQuadraticCutoff threeLevelQuadraticReward
  let score3 := sourceFiniteRankScore (fun e => e ^ 2) id (fun t => t ^ 3) 1 2
    threeLevelQuadraticCutoff threeLevelQuadraticReward
  let effortD := sourceFiniteRankEffort (fun e => e ^ 2) id (fun t => t ^ 3) 1 1
    (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2))
  let scoreD := sourceFiniteRankScore (fun e => e ^ 2) id (fun t => t ^ 3) 1 1
    (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2))
  obtain ⟨_, hs3, _, hsD, hb3, hbD, _, _, _, _, _, _, _, hlt⟩ :=
    threeLevelQuadraticEquilibrium_improves_deterministic tie htie hinj
  refine ⟨(fun e => e ^ 2), id, (fun t => t ^ 3), 1 / 2,
    threeLevelQuadraticCutoff, threeLevelQuadraticReward, effort3, score3, effortD, scoreD,
    ?_, (differentiable_id.pow 2).differentiableOn, differentiable_id.differentiableOn,
    (differentiable_id.pow 3).differentiableOn, ?_, ⟨hs3, hb3⟩, ?_, ?_⟩
  · exact ⟨le_rfl, (continuous_pow 2).continuousOn, quadraticCost_strictConvex,
      (fun _ _ => sq_nonneg _), by norm_num, continuousOn_id, strictMono_id.strictMonoOn _,
      concaveOn_id (convex_Ici _), le_rfl, (continuous_pow 3).continuousOn,
      cubicSkill_strictMono.strictMonoOn _, by norm_num⟩
  · refine ⟨threeLevelQuadraticCutoff_strictMono, ?_, ?_,
      threeLevelQuadraticReward_strictMono.strictMonoOn _, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [threeLevelQuadraticCutoff, threeLevelQuadraticReward, Fin.sum_univ_succ]
  · have hEq : RankingEquilibrium (fun e => e ^ 2) id (fun t => t ^ 3) tie 1
        (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2)) effortD scoreD :=
      ⟨hsD, hbD⟩
    norm_num only [sourceDeterministicCutoff, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact hEq
  · norm_num only [sourceDeterministicCutoff, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact hlt

theorem societalUtility : SocietalUtilitySpec := by
  intro tie htie hinj
  obtain ⟨effort, score, hfamily, _, hstar, hreward, hmax⟩ :=
    exists_sourceSqrtQuadraticSocietalUtility_interior_maximum
      (rho := 1 / 4) (by norm_num) (by norm_num) htie hinj
  refine ⟨(fun e => e ^ 2), Real.sqrt, id, 1 / 4, 4 / 7, effort, score, ?_,
    (differentiable_id.pow 2).differentiableOn, ?_, differentiable_id.differentiableOn,
    by norm_num, hstar, hreward, ?_, ?_⟩
  · exact ⟨le_rfl, (continuous_pow 2).continuousOn, quadraticCost_strictConvex,
      (fun _ _ => sq_nonneg _), by norm_num, Real.continuous_sqrt.continuousOn,
      Real.strictMonoOn_sqrt, Real.strictConcaveOn_sqrt.concaveOn, by norm_num,
      continuousOn_id, strictMono_id.strictMonoOn _, le_rfl⟩
  · intro e he
    exact (Real.hasDerivAt_sqrt he.ne').differentiableAt.differentiableWithinAt
  · intro c hc
    have h := hfamily c hc
    exact ⟨⟨h.2.1, h.2.2.1⟩, h.2.2.2.2⟩
  · intro c hc
    have h := hmax c ⟨hc.1.le, hc.2⟩
    exact ⟨h.1, h.2.1⟩

theorem environmentRankPreservation : EnvironmentRankPreservationSpec := by
  intro cost production skill effort score tie baseline rho psiA psiB n cutoff reward
    hP hpolicy hB hBA htie hinj hEq
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  rcases hpolicy with ⟨_, _, _, hr, _⟩
  have h := sourceEnvironmentEquilibrium_reward_preservation_of_sourcePrimitives
    (fun i : Fin (n + 1) => cutoff i) hb hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0
    (hB.trans hBA) hB hr hEq.1 htie hinj hEq.2
  exact ⟨h.1, h.2.2.2⟩

/-- Positive baseline production permits a positive-mass region in which
both admitted groups exert zero effort and have identical welfare. -/
theorem environmentWelfare_refuted : ¬ EnvironmentWelfareArchivalSpec := by
  intro hclaim
  have hP : RankingPrimitives (fun e : ℝ => e ^ 2) (fun e => 1 + e) id 0 := by
    refine ⟨le_rfl, (continuous_pow 2).continuousOn, quadraticCost_strictConvex,
      (fun e _ => sq_nonneg e), by norm_num, (continuous_const.add continuous_id).continuousOn,
      ?_, (concaveOn_const _ (convex_Ici _)).add (concaveOn_id (convex_Ici _)), by norm_num,
      continuousOn_id, strictMono_id.strictMonoOn _, le_rfl⟩
    intro x _ y _ hxy
    simpa only [add_comm] using add_lt_add_left hxy 1
  have h := BaselineGroupExample.strict_high_gap_claim_fails
    (a := 1 / 2) (delta := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    SeparatedEnvironmentExample.label_meas SeparatedEnvironmentExample.label_inj
  have hsource := hclaim (fun e : ℝ => e ^ 2) (fun e => 1 + e) id
    (BaselineGroupExample.effort (1 / 2) (1 / 2)) (BaselineGroupExample.score (1 / 2) (1 / 2))
    SeparatedEnvironmentExample.labelTie (BaselineGroupExample.capacity (1 / 2) (1 / 2))
    (3 * (1 / 2) / 4) 2 1 hP ⟨h.1, by norm_num [BaselineGroupExample.capacity]⟩ h.2.1
    (by norm_num) (by norm_num) (differentiable_id.pow 2).differentiableOn
    (differentiable_const 1 |>.add differentiable_id).differentiableOn
    differentiable_id.differentiableOn
    SeparatedEnvironmentExample.label_meas SeparatedEnvironmentExample.label_inj
    ⟨BaselineGroupExample.score_meas _ _, h.2.2.1⟩
  exact h.2.2.2 (hsource.2.1.mono (fun _ ht => ht.2))

/-- All admission and weak welfare comparisons survive. In the common
admission region the gap vanishes exactly when disadvantaged effort is zero;
positive disadvantaged effort gives a strict gap. -/
theorem environmentWelfareRecovery
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {rho c psiA psiB : ℝ}
    (hP : RankingPrimitives cost production skill 0) (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hB : 0 < psiB) (hBA : psiB < psiA)
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hEq : EnvironmentEquilibrium cost production skill psiA psiB tie 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) effort score) :
    (∀ group : Bool, ∀ᵐ t ∂unitRankMeasure,
      sourceTwoLevelReward rho c (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank sourceTwoGroupMeasure score tie (group, t))).val =
        if sourceGroupThreshold skill psiA psiB group c < t then rho / (1 - c) else 0) ∧
    (∀ᵐ t ∂unitRankMeasure,
      0 ≤ sourceActualGroupWelfareGap cost effort score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ∧
      (0 < effort (false, t) → 0 < sourceActualGroupWelfareGap cost effort score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t) ∧
      (sourceGroupThreshold skill psiA psiB false c < t →
        (sourceActualGroupWelfareGap cost effort score tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t = 0 ↔
          effort (false, t) = 0))) ∧
    ∀ pureEffort pureScore : Bool × ℝ → ℝ,
      EnvironmentEquilibrium cost production skill psiA psiB tie 0
        (fun k => if k = 0 then 0 else 1) (fun _ => rho) pureEffort pureScore →
      ∀ᵐ t ∂unitRankMeasure, sourceActualGroupWelfareGap cost pureEffort pureScore tie
        (fun _ : Fin 1 => 0) (fun _ => rho) t = 0 := by
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  have had := sourceActualGroupAdmission_of_sourcePrimitives hrho.1 hc hb hp hpC hpN hp0
    hg hgM hgC hg0 hfc hf hf0 hB hBA hEq.1 htie hinj hEq.2
  have hw := sourceActualGroupWelfareGap_of_sourcePrimitives
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) hb hp hpC hpN hp0 hg hgM hg0 hf hf0 hB hBA
    (sourceTwoLevelReward_strictMono hrho.1 (by linarith [hc.2, hrho.1])).monotoneOn hEq.2
  have hh := sourceActualGroupWelfareGap_high_region_of_sourcePrimitives hrho.1 hc hb hp hpC hpN hp0
    hg hgM hgC hg0 hfc hf hf0 hB hBA hEq.1 htie hinj hEq.2
  refine ⟨had, (hw.and hh).mono (fun _ ht => ⟨ht.1.1, ht.1.2.1, ht.2⟩), ?_⟩
  intro pureEffort pureScore hpure
  have hpureBR : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) pureScore tie
        (fun _ : Fin 1 => 0) (fun _ => rho) x (pureEffort x) := by
    simpa only [Fin.eq_zero, Fin.val_zero, if_pos rfl] using hpure.2
  exact sourceActualGroupWelfareGap_pureRandomization (fun _ : Fin 1 => 0) hb hpN hp0 hpureBR

/-- Proposition 4.2, including the exact positive-effort strictness condition. -/
theorem environmentWelfare : EnvironmentWelfareSpec := by
  intro cost production skill effort score tie rho c psiA psiB hP hrho hc hB hBA
    _ _ _ htie hinj hEq
  have h := environmentWelfareRecovery hP hrho hc hB hBA htie hinj hEq
  refine ⟨h.1, ?_, h.2.2⟩
  filter_upwards [h.2.1, sourceTwoGroupMeasure_ae_branch hEq.2 false] with t hw hBR
  refine ⟨hw.1, ?_⟩
  intro hhigh
  constructor
  · intro hpos
    by_contra he
    have he0 : effort (false, t) = 0 := le_antisymm (le_of_not_gt he) hBR.1
    have hz := (hw.2.2 hhigh).mpr he0
    linarith
  · exact hw.2.1

/-- The every-cutoff derivative assertion fails even with zero baseline
production, positive high-region effort, and smooth source primitives. -/
theorem welfareGapDerivative_refuted : ¬ WelfareGapDerivativeArchivalSpec := by
  intro hclaim
  have hP : RankingPrimitives (fun e : ℝ => e ^ 2) id SeparatedEnvironmentExample.latentSkill 0 :=
    ⟨le_rfl, (continuous_pow 2).continuousOn, quadraticCost_strictConvex,
      (fun e _ => sq_nonneg e), by norm_num, continuousOn_id, strictMono_id.strictMonoOn _,
      concaveOn_id (convex_Ici _), le_rfl, SeparatedEnvironmentExample.latent_cont,
      SeparatedEnvironmentExample.latent_mono, by norm_num [SeparatedEnvironmentExample.latentSkill]⟩
  have h := SupportJunctionExample.full_source_derivative_existence_counterexample
    SeparatedEnvironmentExample.label_meas SeparatedEnvironmentExample.label_inj
  have hd := hclaim (fun e : ℝ => e ^ 2) id SeparatedEnvironmentExample.latentSkill
    SupportJunctionExample.fullEffort SupportJunctionExample.fullScore SeparatedEnvironmentExample.labelTie
    (1 / 4) (3 / 2) 1 hP (by norm_num) (by norm_num) (by norm_num)
    (differentiable_id.pow 2).differentiableOn differentiable_id.differentiableOn
    (differentiable_const 1 |>.add differentiable_id).differentiableOn
    SeparatedEnvironmentExample.label_meas SeparatedEnvironmentExample.label_inj h.2.1
    (1 / 4) (by norm_num) (by simpa only [one_mul] using h.1)
  apply h.2.2
  filter_upwards [hd] with t ht hhigh
  obtain ⟨v, _, hv⟩ := ht hhigh
  exact (hv.hasDerivAt (Ioc_mem_nhds (by norm_num) (by norm_num))).differentiableAt

/-- More selective policies weakly increase the gap wherever both groups
remain admitted. The increase is strict when the policy change and the
initial disadvantaged effort are both positive. No differentiability or
additional shape restriction is required. -/
theorem welfareGapFiniteComparison
    {cost production skill : ℝ → ℝ} {effortC scoreC effortD scoreD tie : Bool × ℝ → ℝ}
    {rho c d psiA psiB : ℝ}
    (hP : RankingPrimitives cost production skill 0) (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) (hcd : c ≤ d)
    (hB : 0 < psiB) (hBA : psiB < psiA)
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hEqC : EnvironmentEquilibrium cost production skill psiA psiB tie 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) effortC scoreC)
    (hEqD : EnvironmentEquilibrium cost production skill psiA psiB tie 1
      (sourceTwoLevelCutoff d) (sourceTwoLevelReward rho d) effortD scoreD) :
    ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false d < t →
      sourceActualGroupWelfareGap cost effortC scoreC tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ≤
        sourceActualGroupWelfareGap cost effortD scoreD tie
          (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t ∧
      (c < d → 0 < effortC (false, t) →
        sourceActualGroupWelfareGap cost effortC scoreC tie
            (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t <
          sourceActualGroupWelfareGap cost effortD scoreD tie
            (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t) := by
  rcases hP with ⟨_, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  obtain ⟨K, _, hKN, hKP, hbound⟩ := sourceActualGroupWelfareGap_quantitative_of_sourcePrimitives
    hrho.1 hc hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 hB hBA hEqC.1 htie hinj hEqC.2
  filter_upwards [hbound d hd hcd effortD scoreD hEqD.1 hEqD.2,
    sourceTwoGroupMeasure_ae_branch hEqC.2 false] with t ht hBR
  intro hhigh
  have h := ht hhigh
  have hn := mul_nonneg (hKN t (hpN _ hBR.1)) (sub_nonneg.mpr hcd)
  refine ⟨by linarith, ?_⟩
  intro hlt he
  have hpEff : 0 < cost (effortC (false, t)) := by
    have hpm := sourceCost_strictMonoOn_of_strictConvex hpC hpN hp0
    simpa only [hp0] using hpm (by simp) he.le he
  have hpos := mul_pos (hKP t hpEff) (sub_pos.mpr hlt)
  linarith

/-- Every existing feasible derivative has the correct weak sign, and is
strictly positive at positive disadvantaged effort. This includes the
one-sided derivative at deterministic admission. Derivative existence is
not assumed as a model condition or asserted at every cutoff. -/
theorem welfareGapDerivativeRecovery
    {cost production skill : ℝ → ℝ} {effort score : ℝ → Bool × ℝ → ℝ}
    {tie : Bool × ℝ → ℝ} {rho c psiA psiB : ℝ}
    (hP : RankingPrimitives cost production skill 0) (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hB : 0 < psiB) (hBA : psiB < psiA)
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hEq : ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      EnvironmentEquilibrium cost production skill psiA psiB tie 1
        (sourceTwoLevelCutoff d) (sourceTwoLevelReward rho d) (effort d) (score d)) :
    ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t →
      ∀ v : ℝ, HasDerivWithinAt (fun d => sourceActualGroupWelfareGap cost (effort d) (score d) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t)
        v (Ioc (0 : ℝ) (1 - rho)) c →
        0 ≤ v ∧ (0 < effort c (false, t) → 0 < v) := by
  rcases hP with ⟨_, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  have hfeas {d : ℝ} (hd : d ∈ Icc (c / 2) c) : d ∈ Ioc (0 : ℝ) (1 - rho) :=
    ⟨by linarith [hc.1, hd.1], hd.2.trans hc.2⟩
  have h := sourceActualGroupWelfareGap_leftDeriv_of_sourcePrimitives
    (a := c / 2) hrho.1 hc (by linarith [hc.1]) (by linarith [hc.1])
    hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 hB hBA
    (fun d hd => (hEq d (hfeas hd)).1) htie hinj (fun d hd => (hEq d (hfeas hd)).2)
  filter_upwards [h] with t ht hhigh v hv
  exact (ht hhigh v (hv.mono_of_mem_nhdsWithin (Ioc_mem_nhdsLE_of_mem hc))).2

/-- The finite comparison and the signs of all existing feasible derivatives
give the full interpreted Proposition 4.3 without an everywhere-smoothness claim. -/
theorem welfareGapDerivative : WelfareGapDerivativeSpec := by
  intro cost production skill effort score tie rho psiA psiB hP hrho hB hBA _ _ _ htie hinj hEq
  constructor
  · intro c hc d hd hcd
    exact welfareGapFiniteComparison hP hrho hc hd hcd hB hBA htie hinj (hEq c hc) (hEq d hd)
  · intro c hc
    exact welfareGapDerivativeRecovery hP hrho hc hB hBA htie hinj hEq

/-- The canonical gap represents every actual equilibrium almost
everywhere in applicant rank at each fixed policy. For each fixed applicant
rank, that representative is monotone and differentiable almost everywhere
in the interior common-admission policy region. These two null-set
quantifiers concern different variables. -/
theorem welfareGapCanonicalRegularity
    {cost production skill : ℝ → ℝ} {rho psiA psiB : ℝ}
    (hP : RankingPrimitives cost production skill 0) (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hB : 0 < psiB) (hBA : psiB < psiA) :
    (∀ (c : ℝ), c ∈ Ioc (0 : ℝ) (1 - rho) → ∀ effort score tie : Bool × ℝ → ℝ,
      Measurable tie → InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1} →
      EnvironmentEquilibrium cost production skill psiA psiB tie 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) effort score →
      ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t →
        sourceActualGroupWelfareGap cost effort score tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t =
          sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t c) ∧
    ∀ t ∈ Ioc (0 : ℝ) 1,
      MonotoneOn (sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t)
        (Ioo (0 : ℝ) (min (1 - rho) (sourceDisadvantagedRank skill psiA psiB t))) ∧
      ∀ᵐ c ∂volume.restrict (Ioo (0 : ℝ) (min (1 - rho) (sourceDisadvantagedRank skill psiA psiB t))),
        DifferentiableAt ℝ (sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t) c ∧
        0 ≤ deriv (sourceCanonicalGroupWelfareGap cost production skill psiA psiB rho t) c := by
  rcases hP with ⟨_, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  constructor
  · intro c hc effort score tie htie hinj hEq
    exact sourceActualGroupWelfareGap_eq_canonical_of_sourcePrimitives hrho.1 hc
      hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 hB hBA hEq.1 htie hinj hEq.2
  · intro t ht
    exact ⟨sourceCanonicalGroupWelfareGap_monotoneOn hrho.1 ht
      hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 hB hBA,
      sourceCanonicalGroupWelfareGap_ae_differentiableAt hrho.1 ht
        hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 hB hBA⟩

theorem access : AccessSpec := by
  intro cost production skill effort score tie baseline rho psiA psiB hP hrho hB hBA htie hinj hEq
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  dsimp only
  rw [sourceActualDisadvantagedAccess_pureRandomization]
  refine ⟨rfl, ?_, ?_⟩
  · intro c hc
    exact (sourceActualDisadvantagedAccess_lt_pureRandomization_of_sourcePrimitives
      hrho.1 hc hb hp hpC hpN hp0 hg hgM hgC hg0 hfc hf hf0 hB hBA
      (hEq c hc).1 htie hinj (hEq c hc).2).2.2
  · intro hconv
    exact sourceActualDisadvantagedAccess_antitone_of_sourcePrimitives hrho.1 hb hp hpC hpN hp0
      hg hgM hgC hg0 hfc hf hf0 hconv hB hBA (fun c hc => (hEq c hc).1)
      htie hinj (fun c hc => (hEq c hc).2)

theorem effortComparativeStatics : EffortComparativeStaticsSpec := by
  intro cost production skill tie effort newEffort score newScore baseline rho n k j
    cutoff reward newReward hP hpolicy hnewPolicy _ _ hkj hjn hk hj heq htie hinj hEq hnewEq
  rcases hP with ⟨hb, hp, hpC, hpN, hp0, hg, hgM, hgC, hg0, hfc, hf, hf0⟩
  rcases hpolicy with ⟨hc, hc0, hcn, hr, hr0, hrn, _⟩
  rcases hnewPolicy with ⟨_, _, _, hr', hr0', hrn', _⟩
  have h := sourceActualFiniteEquilibrium_effort_reward_transfer_of_sourcePrimitives
    hb hp hpC hpN hp0 hg hgM hgC hg0 hc hc0 hcn hfc hf hf0 hr hr0 hrn hr' hr0' hrn'
    hkj hjn hk hj heq hEq.1 hnewEq.1 htie hinj hEq.2 hnewEq.2
  exact h.mono (fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩)

/-- Strictly increasing skill ranks identify applicants and map every
nonempty rank interval into the corresponding strict skill interval. -/
theorem preEffortSkillRegularity : PreEffortSkillRegularitySpec := by
  intro skill _hcont hf
  constructor
  · have hmem : ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hmem] with t ht
    intro u hu heq
    exact hf.injOn ⟨ht.1.le, ht.2⟩ hu heq
  · intro s hs t ht hst
    have hsub : Ioo s t ⊆ Ioc (0 : ℝ) 1 := fun u hu =>
      ⟨hs.1.trans_lt hu.1, hu.2.le.trans ht.2⟩
    have hmass : 0 < unitRankMeasure (Ioo s t) := by
      rw [unitRankMeasure, Measure.restrict_apply measurableSet_Ioo,
        inter_eq_left.mpr hsub, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hst)
    apply hmass.trans_le (measure_mono ?_)
    intro u hu
    have huI : u ∈ Icc (0 : ℝ) 1 := ⟨(hsub hu).1.le, (hsub hu).2⟩
    exact ⟨hf hs huI hu.1, hf huI ht hu.2⟩

/-- The printed strict equivalence fails even on every full-measure set in
an actual equilibrium with two nondegenerate, positively weighted skills. -/
theorem multidimensionalRank_refuted : ¬ MultidimensionalRankArchivalSpec := by
  intro hclaim
  have hc : (1 / 2 : ℝ) ∈ Ioc 0 (1 - 1 / 4) := by norm_num
  have hP : MultidimensionalPrimitives 1 (fun e => e ^ 2) 1
      MultidimensionalExample.weight MultidimensionalExample.skill := by
    refine ⟨by norm_num, MultidimensionalExample.weight_spec.1,
      MultidimensionalExample.weight_spec.2, (continuous_pow 2).continuousOn,
      quadraticCost_strictMono, quadraticCost_strictConvex.convexOn,
      (fun _ => continuousOn_id), (fun _ => strictMono_id.strictMonoOn _), ?_⟩
    intro i
    exact le_rfl
  have hpolicy : FiniteAdmissionPolicy 1 (sourceTwoLevelCutoff (1 / 2))
      (sourceTwoLevelReward (1 / 4) (1 / 2)) (1 / 4) := by
    refine ⟨sourceTwoLevelCutoff_strictMono (by norm_num), ?_, ?_,
      sourceTwoLevelReward_strictMono (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩ <;>
      norm_num [sourceTwoLevelCutoff, sourceTwoLevelReward, Fin.sum_univ_succ]
  have he := MultidimensionalExample.actual_equilibrium_family hc
  obtain ⟨good, hgood, hiff⟩ := hclaim 1 1 (fun e => e ^ 2) 1 (1 / 4)
    MultidimensionalExample.weight MultidimensionalExample.skill
    (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 4) (1 / 2))
    (MultidimensionalExample.effort (1 / 2)) (MultidimensionalExample.score (1 / 2))
    MultidimensionalExample.tie hP hpolicy MultidimensionalExample.tie_spec.1
    MultidimensionalExample.tie_spec.2.1.injOn ⟨he.1.1, he.2.mono (fun _ h => h.1)⟩
  obtain ⟨x, hx, y, hy, hindex, hreward⟩ :=
    MultidimensionalExample.strict_index_reward_iff_fails_on_every_fullMeasure_set hc hgood
  exact (ne_of_lt ((hiff x hx y hy).mpr hindex)) hreward

/-- The same primitive model preserves reward bands at the CDF of the
maximum weighted skill and puts all effort on its almost-everywhere unique
maximizing coordinate. Total effort remains endogenous. -/
theorem multidimensionalRankRecovery
    {m n : ℕ} {cost : ℝ → ℝ} {h rho : ℝ}
    {weight : Fin (m + 1) → ℝ} {skill : Fin (m + 1) → ℝ → ℝ}
    {cutoff reward : ℕ → ℝ} {effort : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ}
    {score tie : (Fin (m + 1) → ℝ) → ℝ}
    (hP : MultidimensionalPrimitives m cost h weight skill)
    (hpolicy : FiniteAdmissionPolicy n cutoff reward rho)
    (htie : Measurable tie) (hinj : InjOn tie {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1})
    (hEq : MultidimensionalEquilibrium m n cost h weight skill cutoff reward effort score tie) :
    Measure.map (sourceMultidimensionalPreRank weight skill)
      (sourceMultidimensionalPopulation (Fin (m + 1))) = unitRankMeasure ∧
    ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin (m + 1)),
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank (sourceMultidimensionalPopulation (Fin (m + 1))) score tie x) =
      finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (sourceMultidimensionalPreRank weight skill x) ∧
      ∃ best : Fin (m + 1), sourceMultidimensionalCoefficient weight skill x best =
          sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill x) ∧
        ∀ i, effort x i = if i = best then ∑ j, effort x j else 0 := by
  rcases hP with ⟨hh, hw, hw1, hp, hpM, hpC, hfc, hf, hf0⟩
  have h := sourceMultidimensionalEquilibrium_of_sourcePrimitives hh hw hw1 hp hpM hpC hfc hf hf0
    hpolicy.2.2.2.1 hEq.1 htie hinj hEq.2
  have hs := sourceMultidimensionalBestResponses_single_coordinate_ae hh hw hw1 hpM hfc hf hf0 hEq.2
  exact ⟨h.1, (h.2.and hs).mono (fun _ hx => ⟨hx.1.2, hx.2⟩)⟩

/-- Proposition B.1 with reward-band preservation and the single-coordinate
effort conclusion under the unchanged multidimensional primitives. -/
theorem multidimensionalRank : MultidimensionalRankSpec := by
  intro m n cost h rho weight skill cutoff reward effort score tie hP hpolicy htie hinj hEq
  exact (multidimensionalRankRecovery hP hpolicy htie hinj hEq).2.mono (fun _ hx =>
    ⟨congrArg (fun i : Fin (n + 1) => reward i.val) hx.1, hx.2⟩)

/-- The explicit unsupported-cutoff example satisfies the public primitive
conditions of the independent-rank multitask model. -/
theorem b2Counterexample_multitaskPrimitives :
    MultitaskPrimitives b2CounterexampleCost b2CounterexampleScoreTechnology
      b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
      b2CounterexampleBudget b2CounterexampleRho := by
  have hreg := b2Counterexample_sourcePrimitiveRegularity
  exact ⟨hreg.budget_pos, ⟨hreg.capacity_pos, hreg.capacity_lt_one⟩,
    (continuous_pow 2).continuousOn, hreg.cost_monotoneOn, hreg.cost_convexOn,
    hreg.cost_nonnegative, hreg.score_continuous.continuousOn, hreg.score_strictMono.strictMonoOn _,
    hreg.score_concaveOn, hreg.score_nonnegative 0 (by simp),
    hreg.measurableSkill_continuousOn, hreg.measurableSkill_strictMonoOn,
    by norm_num [b2CounterexampleMeasurableSkill], hreg.unmeasurableSkill_continuousOn,
    hreg.unmeasurableSkill_strictMonoOn, by norm_num [b2CounterexampleUnmeasurableSkill]⟩

/-- Universal interior-cutoff supportability is false under the actual
hard-budget model, even when its equilibrium utility is selection-independent. -/
theorem weightedPrivateUtility_refuted : ¬ WeightedPrivateUtilityArchivalSpec := by
  intro hclaim
  have hP := b2Counterexample_multitaskPrimitives
  have hfamily (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho)) :
      MultitaskEquilibrium b2CounterexampleCost b2CounterexampleScoreTechnology
        b2CounterexampleMeasurableSkill b2CounterexampleBudget b2CounterexampleRho c
        (MultitaskCounterexample.effortM c) (MultitaskCounterexample.effortU c)
        (MultitaskCounterexample.score c) MultitaskExample.tie := by
    have he := MultitaskCounterexample.equilibrium_and_canonical_utility hc
      MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn
    exact ⟨he.1.1, he.2.1⟩
  obtain ⟨beta, hbeta, hmax⟩ := hclaim b2CounterexampleCost b2CounterexampleScoreTechnology
    b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill b2CounterexampleBudget
    b2CounterexampleRho MultitaskCounterexample.effortM MultitaskCounterexample.effortU
    MultitaskCounterexample.score MultitaskExample.tie hP MultitaskExample.tie_spec.1
    MultitaskExample.tie_spec.2.1.injOn hfamily b2CounterexampleTargetCutoff
    (by norm_num [b2CounterexampleTargetCutoff, b2CounterexampleRho])
  obtain ⟨d, hd, _, hbetter⟩ := MultitaskCounterexample.actual_target_strictly_dominated_for_every_weight
    MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn hbeta
  exact (not_lt_of_ge (hmax d ⟨hd.1, hd.2.le⟩)) hbetter

/-- At every feasible cutoff, the explicit multitask counterexample has a
score-priority equilibrium and its actual admission lottery fills capacity.
The population, technology, budget, and publicly known tie rule are fixed. -/
theorem weightedPrivateUtility_scorePriority_counterexample_family
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho)) :
    MultitaskScorePriorityEquilibrium b2CounterexampleCost b2CounterexampleScoreTechnology
      b2CounterexampleMeasurableSkill b2CounterexampleBudget b2CounterexampleRho c
      (MultitaskCounterexample.effortM c) (MultitaskCounterexample.effortU c)
      (MultitaskCounterexample.score c) MultitaskExample.tie ∧
    independentSkillPopulation unitRankMeasure
      (scorePriorityMultitaskAdmissionEvent unitRankMeasure (MultitaskCounterexample.score c)
        MultitaskExample.tie b2CounterexampleRho c) = ENNReal.ofReal b2CounterexampleRho := by
  letI := MultitaskExample.tie_noAtoms
  have he := MultitaskCounterexample.equilibrium_and_canonical_utility hc
    MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn
  refine ⟨(multitaskEquilibrium_scorePriority_iff b2Counterexample_multitaskPrimitives hc
    MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn).mp ⟨he.1.1, he.2.1⟩, ?_⟩
  rw [scorePriorityMultitaskAdmissionEvent_measure_eq unitRankMeasure he.1.1
    MultitaskExample.tie_spec.1]
  exact he.2.2.1

/-- The interior cutoff `7/16` is not optimal for any positive pair of school
weights, for any selection of score-priority equilibria. The objective is
conditional utility under the actual boundary admission lottery, not an
exogenously supplied score or welfare formula. -/
theorem weightedPrivateUtility_scorePriority_unsupported
    (effortM effortU score : ℝ → ℝ × ℝ → ℝ)
    (hfamily : ∀ d ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho),
      MultitaskScorePriorityEquilibrium b2CounterexampleCost b2CounterexampleScoreTechnology
        b2CounterexampleMeasurableSkill b2CounterexampleBudget b2CounterexampleRho d
        (effortM d) (effortU d) (score d) MultitaskExample.tie)
    {beta : ℝ} (hbeta : beta ∈ Ioo (0 : ℝ) 1) :
    ∃ d ∈ Ioo (0 : ℝ) (1 - b2CounterexampleRho),
      scorePriorityMultitaskSchoolUtility unitRankMeasure b2CounterexampleScoreTechnology
        b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
        (effortM b2CounterexampleTargetCutoff) (effortU b2CounterexampleTargetCutoff)
        (score b2CounterexampleTargetCutoff) MultitaskExample.tie
        b2CounterexampleRho beta b2CounterexampleTargetCutoff <
      scorePriorityMultitaskSchoolUtility unitRankMeasure b2CounterexampleScoreTechnology
        b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
        (effortM d) (effortU d) (score d) MultitaskExample.tie b2CounterexampleRho beta d := by
  letI := MultitaskExample.tie_noAtoms
  have ht : b2CounterexampleTargetCutoff ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho) := by
    norm_num [b2CounterexampleTargetCutoff, b2CounterexampleRho]
  have hstrict (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho)) :=
    (multitaskEquilibrium_scorePriority_iff b2Counterexample_multitaskPrimitives hd
      MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn).mpr (hfamily d hd)
  obtain ⟨d, hd, hbetter⟩ := MultitaskCounterexample.target_unsupported_in_every_equilibrium_selection
    effortM effortU score (fun d hd => (hstrict d hd).1) (fun d hd => (hstrict d hd).2) hbeta
  refine ⟨d, hd, ?_⟩
  rw [scorePriorityMultitaskSchoolUtility_eq unitRankMeasure _ _ _ _ _
      (hfamily _ ht).1 MultitaskExample.tie_spec.1,
    scorePriorityMultitaskSchoolUtility_eq unitRankMeasure _ _ _ _ _
      (hfamily d ⟨hd.1, hd.2.le⟩).1 MultitaskExample.tie_spec.1]
  exact hbetter

theorem equalScoreRewards : EqualScoreRewardsSpec := by
  intro cost production skill tie effort score baseline rho n cutoff reward hP hpolicy hEq
  rcases hP with ⟨_, hp, _, _, _, _, hgM, _, _, _, hf, hf0⟩
  rcases hpolicy with ⟨_, _, _, hr, _⟩
  let good := {t | t ∈ Ioc (0 : ℝ) 1 ∧
    SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)}
  have hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good :=
    (ae_restrict_mem measurableSet_Ioc).and hEq.2
  refine ⟨good, hgood, ?_⟩
  intro x hx y hy hxy
  have hpos (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < skill t :=
    hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  exact sourceBestResponses_equal_score_equal_reward unitRankMeasure score tie x y hp hgM
    (monotone_finiteLowerRankReward _ hr.monotoneOn) (hpos x hx.1) (hpos y hy.1)
    hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1 hxy hx.2.2.2 hy.2.2.2

theorem nullDeviations : NullDeviationsSpec := by
  intro production skill tie effort deviatedEffort admission heq
  have hs : (fun t => production (effort t) * skill t) =ᵐ[unitRankMeasure]
      (fun t => production (deviatedEffort t) * skill t) :=
    heq.mono (fun _ h => by dsimp only; rw [h])
  exact ⟨Measure.map_congr hs, fun t v =>
    congrArg admission (counterfactualTieBrokenRank_congr_score hs t v)⟩

theorem costGap : CostGapSpec := by
  intro cost production skill score tie baseline rho n cutoff reward x y e eToHigh eHighToLow eHigh
    _ _ _ _ _ _ _ _ _ _ R hlow hhigh hbestLow hbestHigh
  linarith

theorem productionGap : ProductionGapSpec := by
  intro cost production skill baseline x y e eToHigh eHighToLow eHigh
    hP hx hy hxy he0 heToHigh heHighToLow htoHighHigh hhighToLowHigh hlow hhigh
  rcases hP with ⟨_, _, _, _, _, _, hgM, hgC, _, _, hf, hf0⟩
  have hb0 : 0 ≤ eToHigh := he0.trans heToHigh.le
  have hc0 : 0 ≤ eHighToLow := he0.trans heHighToLow.le
  have hd0 : 0 ≤ eHigh := hb0.trans htoHighHigh.le
  have had : e < eHigh := heToHigh.trans htoHighHigh
  have hskill : skill x < skill y := hf hx hy hxy
  have hskill0 : 0 ≤ skill x :=
    hf0.trans (hf.monotoneOn ⟨le_rfl, by norm_num⟩ hx hx.1)
  have hincpos : 0 < production eToHigh - production e :=
    sub_pos.mpr (hgM he0 hb0 heToHigh)
  have hinc : production eToHigh - production e < production eHigh - production eHighToLow := by
    by_contra hn
    have hle := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hskill0
    have hlt := mul_lt_mul_of_pos_left hskill hincpos
    nlinarith [hlow, hhigh]
  have hs1 : slope production eHighToLow eHigh ≤ slope production e eHigh := by
    have h := hgC.slope_anti (x := eHigh) hd0
      (show e ∈ Ici (0 : ℝ) \ {eHigh} from ⟨he0, by simpa using had.ne⟩)
      (show eHighToLow ∈ Ici (0 : ℝ) \ {eHigh} from ⟨hc0, by simpa using hhighToLowHigh.ne⟩)
      heHighToLow.le
    simpa only [slope_comm] using h
  have hs2 : slope production e eHigh ≤ slope production e eToHigh :=
    hgC.antitoneOn_slope_gt he0 ⟨hb0, heToHigh⟩ ⟨hd0, had⟩ htoHighHigh.le
  have hslope := hs1.trans hs2
  rw [slope_def_field, slope_def_field] at hslope
  have hcross := (div_le_div_iff₀ (sub_pos.mpr hhighToLowHigh) (sub_pos.mpr heToHigh)).mp hslope
  by_contra hn
  have hlen := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hincpos.le
  have hstrict := mul_lt_mul_of_pos_right hinc (sub_pos.mpr heToHigh)
  linarith

end LBG22StrategicRanking.SourceProofs

namespace LBG22StrategicRanking.ProofInterface

/-! Exact-type public proof endpoints. The implementation namespace remains
available to existing clients; these declarations are the sole selected
source-claim proof routes. -/

theorem rankPreservation : RankPreservationSpec := SourceProofs.rankPreservation

theorem secondPriceEffort : SecondPriceEffortSpec := SourceProofs.secondPriceEffort

theorem applicantWelfare : ApplicantWelfareSpec := SourceProofs.applicantWelfare

theorem privateUtility : PrivateUtilitySpec := SourceProofs.privateUtility

theorem threeLevelImprovement : ThreeLevelImprovementSpec := SourceProofs.threeLevelImprovement

theorem societalUtility : SocietalUtilitySpec := SourceProofs.societalUtility

theorem environmentRankPreservation : EnvironmentRankPreservationSpec := SourceProofs.environmentRankPreservation

theorem environmentWelfare : EnvironmentWelfareSpec := SourceProofs.environmentWelfare

theorem welfareGapDerivative : WelfareGapDerivativeSpec := SourceProofs.welfareGapDerivative

theorem access : AccessSpec := SourceProofs.access

theorem effortComparativeStatics : EffortComparativeStaticsSpec := SourceProofs.effortComparativeStatics

theorem preEffortSkillRegularity : PreEffortSkillRegularitySpec := SourceProofs.preEffortSkillRegularity

theorem multidimensionalRank : MultidimensionalRankSpec := SourceProofs.multidimensionalRank

theorem weightedPrivateUtility : WeightedPrivateUtilitySpec := SourceProofs.weightedPrivateUtility

theorem equalScoreRewards : EqualScoreRewardsSpec := SourceProofs.equalScoreRewards

theorem nullDeviations : NullDeviationsSpec := SourceProofs.nullDeviations

theorem costGap : CostGapSpec := SourceProofs.costGap

theorem productionGap : ProductionGapSpec := SourceProofs.productionGap

end LBG22StrategicRanking.ProofInterface

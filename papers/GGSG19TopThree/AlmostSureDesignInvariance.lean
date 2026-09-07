import GGSG19TopThree.MainTheorems
import AppliedModelingLib.Foundations.Probability.RenewalReward
import Mathlib.Probability.Independence.InfinitePi

/-!
# GGSG19 Proposition 1 on a canonical infinite iid voter path

The source definition and Proposition 1 are almost-sure statements.  This file
constructs the canonical countable product of the finite ranking law and closes
the strong-law bridge from strict expected score separation to eventual exact
recovery on almost every infinite voter path.
-/

open scoped BigOperators

namespace GGSG19TopThree

open AppliedModelingLib.Probability
open AppliedModelingLib.SocialChoice.Ranking
open MeasureTheory
open scoped Function ProbabilityTheory Topology

noncomputable section

/-- Canonical infinite iid path measure associated with a finite PMF. -/
noncomputable def finitePMFIidPathMeasure
    {Signal : Type*} [MeasurableSpace Signal]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) : Measure (ℕ → Signal) := by
  exact Measure.infinitePi (fun _ : ℕ => law.toMeasure)

instance finitePMFIidPathMeasure.isProbabilityMeasure
    {Signal : Type*} [MeasurableSpace Signal]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) :
    IsProbabilityMeasure (finitePMFIidPathMeasure law) := by
  unfold finitePMFIidPathMeasure
  infer_instance

/-- Cumulative score of a candidate on the first `N` coordinates of a path. -/
def iidPathCandidateScore
    {Candidate Signal : Type*}
    (score : Candidate → Signal → ℝ) (path : ℕ → Signal)
    (N : ℕ) (candidate : Candidate) : ℝ :=
  ∑ voter ∈ Finset.range N, score candidate (path voter)

/--
Strong law for a real statistic of a canonical infinite path drawn iid from a
finite PMF.  The limit is the finite PMF expectation used elsewhere in the
paper formalization.
-/
theorem ae_tendsto_finitePMFIidPath_empirical_mean
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      Filter.Tendsto
        (fun N : ℕ =>
          (∑ voter ∈ Finset.range N, statistic (path voter)) / N)
        Filter.atTop (nhds (AppliedModelingLib.pmfExp law statistic)) := by
  letI : MeasurableSpace Signal := ⊤
  let P : Measure (ℕ → Signal) := finitePMFIidPathMeasure law
  let X : ℕ → (ℕ → Signal) → ℝ := fun voter path => statistic (path voter)
  have hstat_meas : Measurable statistic := measurable_of_countable statistic
  have hX_meas : ∀ voter, Measurable (X voter) := by
    intro voter
    exact hstat_meas.comp (measurable_pi_apply voter)
  have htoLaw :
      ∀ voter,
        ProbabilityTheory.IdentDistrib
          (X voter) statistic P law.toMeasure := by
    intro voter
    dsimp [X, P]
    refine ⟨(hX_meas voter).aemeasurable, hstat_meas.aemeasurable, ?_⟩
    simp only [finitePMFIidPathMeasure]
    change Measure.map
        (statistic ∘ (fun path : ℕ → Signal => path voter))
        (Measure.infinitePi (fun _ : ℕ => law.toMeasure)) =
      Measure.map statistic law.toMeasure
    rw [← Measure.map_map hstat_meas (measurable_pi_apply voter),
      Measure.infinitePi_map_eval]
  have hX_integrable : Integrable (X 0) P := by
    exact (htoLaw 0).symm.integrable_snd Integrable.of_finite
  have hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X) := by
    have hiIndep : ProbabilityTheory.iIndepFun X P := by
      change ProbabilityTheory.iIndepFun
        (fun voter path => statistic (path voter))
        (Measure.infinitePi (fun _ : ℕ => law.toMeasure))
      exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => hstat_meas)
    intro i j hij
    exact hiIndep.indepFun hij
  have hX_ident :
      ∀ voter,
        ProbabilityTheory.IdentDistrib (X voter) (X 0) P P := by
    intro voter
    exact (htoLaw voter).trans (htoLaw 0).symm
  have hslln :=
    AppliedModelingLib.ae_tendsto_empirical_mean_real_of_iid
      X hX_integrable hX_indep hX_ident
  have hmean :
      (∫ path, X 0 path ∂P) = AppliedModelingLib.pmfExp law statistic := by
    calc
      (∫ path, X 0 path ∂P) =
          ∫ signal, statistic signal ∂law.toMeasure :=
        (htoLaw 0).integral_eq
      _ = AppliedModelingLib.pmfExp law statistic :=
        (AppliedModelingLib.pmfExp_eq_integral_toMeasure law statistic).symm
  simpa [P, X, hmean] using hslln

/--
A positive one-voter expected gap becomes an eventually strict cumulative gap
on almost every canonical iid path.
-/
theorem ae_eventually_iidPath_score_gap_pos_of_pmfExp_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (gap : Signal → ℝ)
    (hmean : 0 < AppliedModelingLib.pmfExp law gap) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ∀ᶠ N : ℕ in Filter.atTop,
        0 < ∑ voter ∈ Finset.range N, gap (path voter) := by
  letI : MeasurableSpace Signal := ⊤
  have hslln := ae_tendsto_finitePMFIidPath_empirical_mean law gap
  filter_upwards [hslln] with path hpath
  have havg :
      ∀ᶠ N : ℕ in Filter.atTop,
        0 < (∑ voter ∈ Finset.range N, gap (path voter)) / N :=
    hpath.eventually (Ioi_mem_nhds hmean)
  filter_upwards [havg, Filter.eventually_ge_atTop 1] with N hN hNpos
  have hcast : (0 : ℝ) < N := by exact_mod_cast hNpos
  exact (div_pos_iff_of_pos_right hcast).mp hN

/--
If every true-winner/true-loser one-voter score gap has positive expectation,
the canonical score-top selection is eventually exactly the true winner set
on almost every iid voter path.
-/
theorem ae_eventually_scoreTopSelectedSetOfCard_eq_of_crossTier_pmfExp_pos
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 < AppliedModelingLib.pmfExp law
          (fun signal => score pair.hi signal - score pair.lo signal)) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ∀ᶠ N : ℕ in Filter.atTop,
        scoreTopSelectedSetOfCard
            (iidPathCandidateScore score path N) winnerSet =
          winnerSet := by
  letI : MeasurableSpace Signal := ⊤
  have hpair :
      ∀ pair : CrossTierPair winnerSet,
        ∀ᵐ path ∂finitePMFIidPathMeasure law,
          ∀ᶠ N : ℕ in Filter.atTop,
            iidPathCandidateScore score path N pair.lo <
              iidPathCandidateScore score path N pair.hi := by
    intro pair
    have hgap :=
      ae_eventually_iidPath_score_gap_pos_of_pmfExp_pos
        law (fun signal => score pair.hi signal - score pair.lo signal)
        (hmean pair)
    filter_upwards [hgap] with path hpath
    filter_upwards [hpath] with N hN
    simpa [iidPathCandidateScore, Finset.sum_sub_distrib] using hN
  have hallAE :
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ pair : CrossTierPair winnerSet,
          ∀ᶠ N : ℕ in Filter.atTop,
            iidPathCandidateScore score path N pair.lo <
              iidPathCandidateScore score path N pair.hi :=
    MeasureTheory.ae_all_iff.mpr hpair
  filter_upwards [hallAE] with path hpath
  have hallN :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ pair : CrossTierPair winnerSet,
          iidPathCandidateScore score path N pair.lo <
            iidPathCandidateScore score path N pair.hi := by
    exact Filter.eventually_all.mpr hpath
  filter_upwards [hallN] with N hstrict
  let selected :=
    scoreTopSelectedSetOfCard
      (iidPathCandidateScore score path N) winnerSet
  by_contra hne
  obtain ⟨pair, herror⟩ :=
    exists_crossTier_score_error_of_wrong_scoreTopSelectedSet
      (iidPathCandidateScore score path N) winnerSet selected
      (scoreTopSelectedSetOfCard_card
        (iidPathCandidateScore score path N) winnerSet)
      (scoreTopSelectedSetOfCard_top
        (iidPathCandidateScore score path N) winnerSet)
      hne
  exact (not_le_of_gt (hstrict pair)) herror

/-- Canonical tiered score-top outcome on the first `N` voters of an iid path. -/
noncomputable def iidPathTieredPrefixOutcome
    {Stage Candidate Signal : Type*} [Fintype Candidate]
    [DecidableEq Candidate]
    (score : Candidate → Signal → ℝ)
    (targetPrefix : Stage → Finset Candidate)
    (path : ℕ → Signal) (N : ℕ) : Stage → Finset Candidate :=
  fun stage =>
    scoreTopSelectedSetOfCard
      (iidPathCandidateScore score path N) (targetPrefix stage)

/--
Strict top-prefix dominance gives the source's almost-sure tiered outcome
recovery statement for every reasonable positional score vector.
-/
theorem rankingTieredStrictPrefixDominance_implies_almostSure_designInvariance
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hdom :
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut <
                  rankingTopPrefixProb law hi cut) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        letI : MeasurableSpace (Ranking n) := ⊤
        ∀ᵐ path ∂finitePMFIidPathMeasure law,
          ∀ᶠ N : ℕ in Filter.atTop,
            iidPathTieredPrefixOutcome
                (rankingPrefixScore diff) targetPrefix path N =
              targetPrefix := by
  intro diff hdiff
  letI : MeasurableSpace (Ranking n) := ⊤
  have hstage :
      ∀ stage : Fin Stage,
        ∀ᵐ path ∂finitePMFIidPathMeasure law,
          ∀ᶠ N : ℕ in Filter.atTop,
            iidPathTieredPrefixOutcome
                (rankingPrefixScore diff) targetPrefix path N stage =
              targetPrefix stage := by
    intro stage
    exact
      ae_eventually_scoreTopSelectedSetOfCard_eq_of_crossTier_pmfExp_pos
        law (rankingPrefixScore diff) (targetPrefix stage)
        (fun pair =>
          pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
            law diff rankingInTopPrefix
            (hdom stage pair.hi pair.lo pair.hi_mem pair.lo_not_mem)
            hdiff)
  have hallAE :
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ stage : Fin Stage,
          ∀ᶠ N : ℕ in Filter.atTop,
            iidPathTieredPrefixOutcome
                (rankingPrefixScore diff) targetPrefix path N stage =
              targetPrefix stage :=
    MeasureTheory.ae_all_iff.mpr hstage
  filter_upwards [hallAE] with path hpath
  have hallN :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ stage : Fin Stage,
          iidPathTieredPrefixOutcome
              (rankingPrefixScore diff) targetPrefix path N stage =
            targetPrefix stage :=
    Filter.eventually_all.mpr hpath
  filter_upwards [hallN] with N hN
  exact funext hN

/--
At one reversed top-prefix cut, the corresponding reasonable indicator score
has an eventually strict reversed cumulative score gap almost surely.
-/
theorem ae_eventually_reverse_indicator_rankingPrefixScore_gap_pos
    {n : ℕ}
    (law : PMF (Ranking n))
    {hi lo : Candidate n} {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    let diff : RankingProperPrefixCut n → ℝ :=
      fun k => if k = cut then 1 else 0
    letI : MeasurableSpace (Ranking n) := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ∀ᶠ N : ℕ in Filter.atTop,
        iidPathCandidateScore (rankingPrefixScore diff) path N hi <
          iidPathCandidateScore (rankingPrefixScore diff) path N lo := by
  let diff : RankingProperPrefixCut n → ℝ :=
    fun k => if k = cut then 1 else 0
  letI : MeasurableSpace (Ranking n) := ⊤
  have hmean :
      0 < AppliedModelingLib.pmfExp law
        (fun ranking =>
          rankingPrefixScore diff lo ranking -
            rankingPrefixScore diff hi ranking) := by
    rw [AppliedModelingLib.pmfExp_sub]
    change 0 < AppliedModelingLib.pmfExp law
        (prefixScoreFromEvent diff rankingInTopPrefix lo) -
      AppliedModelingLib.pmfExp law
        (prefixScoreFromEvent diff rankingInTopPrefix hi)
    rw [
      pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore,
      pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore]
    simpa [rankingPrefixScore, rankingTopPrefixProb, prefixExpectedScore, diff,
      sub_pos] using hreverse
  have hgap :=
    ae_eventually_iidPath_score_gap_pos_of_pmfExp_pos
      law
      (fun ranking =>
        rankingPrefixScore diff lo ranking -
          rankingPrefixScore diff hi ranking)
      hmean
  filter_upwards [hgap] with path hpath
  filter_upwards [hpath] with N hN
  simpa [iidPathCandidateScore, Finset.sum_sub_distrib] using hN

/--
Source-shaped Proposition 1 on the canonical iid voter path, away from exact
cross-tier prefix ties.  The right side is the literal almost-sure convergence
of every reasonable positional scoring design to the same tiered outcome.
-/
theorem rankingTieredStrictPrefixDominance_iff_almostSure_designInvariance_of_noTie
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hNoTie :
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut ≠
                  rankingTopPrefixProb law hi cut) :
    (∀ stage : Fin Stage,
      ∀ hi lo : Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          letI : MeasurableSpace (Ranking n) := ⊤
          ∀ᵐ path ∂finitePMFIidPathMeasure law,
            ∀ᶠ N : ℕ in Filter.atTop,
              iidPathTieredPrefixOutcome
                  (rankingPrefixScore diff) targetPrefix path N =
                targetPrefix) := by
  constructor
  · exact
      rankingTieredStrictPrefixDominance_implies_almostSure_designInvariance
        law targetPrefix
  · intro hADI stage hi lo hhi hlo cut
    rcases lt_or_gt_of_ne (hNoTie stage hi lo hhi hlo cut) with hforward | hreverse
    · exact hforward
    · exfalso
      let diff : RankingProperPrefixCut n → ℝ :=
        fun k => if k = cut then 1 else 0
      letI : MeasurableSpace (Ranking n) := ⊤
      have hconverges := hADI diff (ReasonablePrefixWeights.indicator cut)
      have hreversed :=
        ae_eventually_reverse_indicator_rankingPrefixScore_gap_pos
          law hreverse
      have hfalse :
          ∀ᵐ path ∂finitePMFIidPathMeasure law, False := by
        filter_upwards [hconverges, hreversed] with path hconv hrev
        have heq :
            ∀ᶠ N : ℕ in Filter.atTop,
              iidPathTieredPrefixOutcome
                  (rankingPrefixScore diff) targetPrefix path N stage =
                targetPrefix stage := by
          filter_upwards [hconv] with N hN
          exact congrFun hN stage
        rcases (heq.and hrev).exists with ⟨N, hselected, hscore⟩
        have hhiSelected :
            hi ∈ scoreTopSelectedSetOfCard
              (iidPathCandidateScore (rankingPrefixScore diff) path N)
              (targetPrefix stage) := by
          change hi ∈ iidPathTieredPrefixOutcome
            (rankingPrefixScore diff) targetPrefix path N stage
          rw [hselected]
          exact hhi
        have hloNotSelected :
            lo ∉ scoreTopSelectedSetOfCard
              (iidPathCandidateScore (rankingPrefixScore diff) path N)
              (targetPrefix stage) := by
          change lo ∉ iidPathTieredPrefixOutcome
            (rankingPrefixScore diff) targetPrefix path N stage
          rw [hselected]
          exact hlo
        have hle :
            iidPathCandidateScore (rankingPrefixScore diff) path N lo ≤
              iidPathCandidateScore (rankingPrefixScore diff) path N hi := by
          exact
            scoreTopSelectedSetOfCard_top
              (iidPathCandidateScore (rankingPrefixScore diff) path N)
              (targetPrefix stage) hhiSelected hloNotSelected
        exact (not_lt_of_ge hle) hscore
      rcases hfalse.exists with ⟨_, h⟩
      exact h

end

end GGSG19TopThree

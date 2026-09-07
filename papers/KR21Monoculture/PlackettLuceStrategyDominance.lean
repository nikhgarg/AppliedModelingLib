import KR21Monoculture.GumbelPlackettLuceExact
import KR21Monoculture.Definition1FullRemoval
import KR21Monoculture.W11ScoreTransport

/-!
# Two-firm strategy dominance for Plackett--Luce

Section 3.1 says that, under Plackett--Luce, a firm should use the best
available ranking regardless of its competitor's choice.  This module gives a
precise two-firm meaning to that sentence.  A law is better only when it
weakly improves both the first-mover payoff and the expected best survivor
after every possible first hire.  No conclusion is inferred from strategy or
function names.

For the sequential Plackett--Luce law, a larger positive inverse temperature
has those semantic properties by coupling both laws to the same iid Gumbel
source and applying the existing score-contraction theorem.  IIA then turns
the algorithm/shared-ranking second-mover payoff into the same independent
reranking payoff, so the more accurate law is weakly dominant in the actual
two-firm game.  Weak dominance is the strongest unconditional conclusion:
equal temperatures and constant value profiles make strict dominance false.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/--
If one ranking law improves the first choice and every possible post-removal
choice, and sharing that law has the same second-mover payoff as independently
redrawing it, then using it weakly dominates the alternative in both rows of
the paper's two-firm game.

The hypotheses are stated entirely in terms of payoff-relevant distributions;
in particular, neither `algorithm` nor `human` is assumed better by name.
-/
theorem twoFirm_algorithm_weakly_dominates_of_semantic_improvement
    {n : ℕ} (algorithm human : PMF (Ranking n))
    (value : Candidate n → ℝ)
    (hfirst :
      expectedFirstMoverUtility human value ≤
        expectedFirstMoverUtility algorithm value)
    (hremaining : ∀ c : Candidate n,
      AccuracyFamily.expectedBestAfterRemoval human value c ≤
        AccuracyFamily.expectedBestAfterRemoval algorithm value c)
    (hshared : expectedSecondMoverShared algorithm value =
      expectedSecondMoverIndependent algorithm algorithm value) :
    let M : Model n :=
      { algorithmRanking := algorithm
        humanRanking := human
        value := value }
    Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
        Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
      Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
        Model.payoffAgainst M Strategy.human Strategy.human := by
  have hsecondAgainstAlgorithm :
      expectedSecondMoverIndependent human algorithm value ≤
        expectedSecondMoverIndependent algorithm algorithm value := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    exact pmfExp_le_pmfExp_of_forall_le algorithm _ _
      (fun ranking => hremaining (firstChoice ranking))
  have hsecondAgainstHuman :
      expectedSecondMoverIndependent human human value ≤
        expectedSecondMoverIndependent algorithm human value := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    exact pmfExp_le_pmfExp_of_forall_le human _ _
      (fun ranking => hremaining (firstChoice ranking))
  simp only [Model.payoffAgainst, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist]
  constructor
  · rw [hshared]
    linarith
  · linarith

/--
The companion two-firm comparison when the independent human law is the
semantically better one.  The shared-law equality still concerns the
alternative algorithmic law, because that is the only profile at which the
game reuses rather than redraws a ranking.
-/
theorem twoFirm_human_weakly_dominates_of_semantic_improvement
    {n : ℕ} (algorithm human : PMF (Ranking n))
    (value : Candidate n → ℝ)
    (hfirst :
      expectedFirstMoverUtility algorithm value ≤
        expectedFirstMoverUtility human value)
    (hremaining : ∀ c : Candidate n,
      AccuracyFamily.expectedBestAfterRemoval algorithm value c ≤
        AccuracyFamily.expectedBestAfterRemoval human value c)
    (hshared : expectedSecondMoverShared algorithm value =
      expectedSecondMoverIndependent algorithm algorithm value) :
    let M : Model n :=
      { algorithmRanking := algorithm
        humanRanking := human
        value := value }
    Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
        Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
      Model.payoffAgainst M Strategy.human Strategy.human ≥
        Model.payoffAgainst M Strategy.algorithm Strategy.human := by
  have hsecondAgainstAlgorithm :
      expectedSecondMoverIndependent algorithm algorithm value ≤
        expectedSecondMoverIndependent human algorithm value := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    exact pmfExp_le_pmfExp_of_forall_le algorithm _ _
      (fun ranking => hremaining (firstChoice ranking))
  have hsecondAgainstHuman :
      expectedSecondMoverIndependent algorithm human value ≤
        expectedSecondMoverIndependent human human value := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    exact pmfExp_le_pmfExp_of_forall_le human _ _
      (fun ranking => hremaining (firstChoice ranking))
  simp only [Model.payoffAgainst, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist]
  constructor
  · rw [hshared]
    linarith
  · linarith

/--
At positive accuracies, a higher Plackett--Luce inverse temperature weakly
improves the expected true value of the top ranked candidate in every nonempty
remaining set.  The proof transports the independently constructed
Plackett--Luce PMFs through the proved iid Gumbel representation and does not
take monotonicity as a property of the parameter's name.
-/
theorem plackettLuce_expectedBestInSet_le_of_accuracy_le
    {n : ℕ} (value : Candidate n → ℝ)
    {thetaH thetaA : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA)
    (remaining : Finset (Candidate n)) (hremaining : remaining.Nonempty) :
    expectedBestInSet (plackettLuceRankingPMF thetaH value) value remaining ≤
      expectedBestInSet (plackettLuceRankingPMF thetaA value) value remaining := by
  classical
  rcases lt_or_eq_of_le hthetaHA with hthetaHA | rfl
  · letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
      gumbelArrivalLaw_isProbabilityMeasure n
    have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
    let raw : (Candidate n → ℝ) → Candidate n → ℝ :=
      fun arrival i =>
        value i + scaleOneGumbelNoise arrival i / thetaH
    have hrawRank :
        Measurable (fun arrival => rankByScore (raw arrival)) := by
      apply measurable_rankByScore
      intro i
      dsimp [raw, scaleOneGumbelNoise]
      exact measurable_const.add
        ((measurable_scaleOneGumbelInnovation.comp (measurable_pi_apply i)).div
          measurable_const)
    have haccurateRank :
        Measurable (fun arrival =>
          rankByScore (fun i =>
            value i + scaleOneGumbelNoise arrival i / thetaA)) := by
      apply measurable_rankByScore
      intro i
      dsimp [scaleOneGumbelNoise]
      exact measurable_const.add
        ((measurable_scaleOneGumbelInnovation.comp (measurable_pi_apply i)).div
          measurable_const)
    let t : ℝ := thetaH / thetaA
    have ht0 : 0 ≤ t := le_of_lt (div_pos hthetaH hthetaA)
    have htlt1 : t < 1 := by
      dsimp [t]
      exact (div_lt_one hthetaA).mpr hthetaHA
    have hcontract_eq :
        (fun arrival =>
          rankByScore (fun i =>
            paper_appendixC_contractedScore t (value i) (raw arrival i))) =
          (fun arrival =>
            rankByScore (fun i =>
              value i + scaleOneGumbelNoise arrival i / thetaA)) := by
      funext arrival
      apply congrArg rankByScore
      funext i
      dsimp [t, raw, paper_appendixC_contractedScore]
      unfold KR21Monoculture.rumContractScore
      unfold AppliedModelingLib.Probability.rumContractScore
      field_simp [ne_of_gt hthetaH, ne_of_gt hthetaA]
      ring
    have hcontractRank :
        Measurable (fun arrival =>
          rankByScore (fun i =>
            paper_appendixC_contractedScore t (value i) (raw arrival i))) := by
      rw [hcontract_eq]
      exact haccurateRank
    have hcontractPmf :
        rankingPMFOfMeasure (gumbelArrivalLaw n)
            (fun arrival =>
              rankByScore (fun i =>
                paper_appendixC_contractedScore t (value i) (raw arrival i)))
            hcontractRank =
          rankingPMFOfMeasure (gumbelArrivalLaw n)
            (fun arrival =>
              rankByScore (fun i =>
                value i + scaleOneGumbelNoise arrival i / thetaA))
            haccurateRank := by
      apply rankingPMFOfMeasure_eq_of_measurePreserving
        (gumbelArrivalLaw n) (gumbelArrivalLaw n) id
        (MeasurePreserving.id (gumbelArrivalLaw n))
        (fun arrival =>
          rankByScore (fun i =>
            paper_appendixC_contractedScore t (value i) (raw arrival i)))
        hcontractRank
        (fun arrival =>
          rankByScore (fun i =>
            value i + scaleOneGumbelNoise arrival i / thetaA))
        haccurateRank
      intro arrival
      exact congrFun hcontract_eq arrival
    have hdistH :
        scaleOneGumbelRUMRankingPMF thetaH value =
          rankingPMFOfMeasure (gumbelArrivalLaw n)
            (fun arrival => rankByScore (raw arrival)) hrawRank := by
      apply rankingPMFOfMeasure_eq_of_measurePreserving
        (gumbelArrivalLaw n) (gumbelArrivalLaw n) id
        (MeasurePreserving.id (gumbelArrivalLaw n))
        (scaleOneGumbelRank thetaH value)
        (measurable_scaleOneGumbelRank thetaH value)
        (fun arrival => rankByScore (raw arrival)) hrawRank
      intro arrival
      simpa [scaleOneGumbelRank, scaleOneGumbelScores, raw] using
        (rankByScore_scaledNoise_eq_additiveScore value
          (scaleOneGumbelNoise arrival) hthetaH).symm
    have hdistA :
        scaleOneGumbelRUMRankingPMF thetaA value =
          rankingPMFOfMeasure (gumbelArrivalLaw n)
            (fun arrival =>
              rankByScore (fun i =>
                value i + scaleOneGumbelNoise arrival i / thetaA))
            haccurateRank := by
      apply rankingPMFOfMeasure_eq_of_measurePreserving
        (gumbelArrivalLaw n) (gumbelArrivalLaw n) id
        (MeasurePreserving.id (gumbelArrivalLaw n))
        (scaleOneGumbelRank thetaA value)
        (measurable_scaleOneGumbelRank thetaA value)
        (fun arrival =>
          rankByScore (fun i =>
            value i + scaleOneGumbelNoise arrival i / thetaA))
        haccurateRank
      intro arrival
      simpa [scaleOneGumbelRank, scaleOneGumbelScores] using
        (rankByScore_scaledNoise_eq_additiveScore value
          (scaleOneGumbelNoise arrival) hthetaA).symm
    have hmono :
        expectedBestInSet (scaleOneGumbelRUMRankingPMF thetaH value)
            value remaining ≤
          expectedBestInSet (scaleOneGumbelRUMRankingPMF thetaA value)
            value remaining := by
      calc
        expectedBestInSet (scaleOneGumbelRUMRankingPMF thetaH value)
            value remaining =
            expectedBestInSet
              (rankingPMFOfMeasure (gumbelArrivalLaw n)
                (fun arrival => rankByScore (raw arrival)) hrawRank)
              value remaining := by rw [hdistH]
        _ ≤ expectedBestInSet
              (rankingPMFOfMeasure (gumbelArrivalLaw n)
                (fun arrival =>
                  rankByScore (fun i =>
                    paper_appendixC_contractedScore t (value i) (raw arrival i)))
                hcontractRank)
              value remaining := by
          exact paper_appendixA_expectedBestInSet_monotonicity_of_measure_rankByScore_contraction
            (gumbelArrivalLaw n) value raw hrawRank hcontractRank ht0 htlt1 hremaining
        _ = expectedBestInSet (scaleOneGumbelRUMRankingPMF thetaA value)
              value remaining := by
          rw [hcontractPmf, ← hdistA]
    rw [scaleOneGumbelRUMRankingPMF_eq_plackettLuce thetaH value,
      scaleOneGumbelRUMRankingPMF_eq_plackettLuce thetaA value] at hmono
    exact hmono
  · exact le_rfl

/--
The exact payoff-relevant meaning of a higher Plackett--Luce temperature:
it weakly improves the first mover's choice and the choice after every possible
candidate removal.  The parameter names are intentionally neutral so this
lemma can be used for either available strategy.
-/
theorem plackettLuce_semantic_improvement_of_accuracy_le
    {n : ℕ} (value : Candidate n → ℝ)
    {thetaLow thetaHigh : ℝ}
    (hthetaLow : 0 < thetaLow) (hthetaLowHigh : thetaLow ≤ thetaHigh) :
    expectedFirstMoverUtility (plackettLuceRankingPMF thetaLow value) value ≤
        expectedFirstMoverUtility (plackettLuceRankingPMF thetaHigh value) value ∧
      ∀ removed : Candidate n,
        AccuracyFamily.expectedBestAfterRemoval
            (plackettLuceRankingPMF thetaLow value) value removed ≤
          AccuracyFamily.expectedBestAfterRemoval
            (plackettLuceRankingPMF thetaHigh value) value removed := by
  constructor
  · have h := plackettLuce_expectedBestInSet_le_of_accuracy_le value hthetaLow
      hthetaLowHigh Finset.univ (by exact ⟨0, Finset.mem_univ _⟩)
    simpa using h
  · intro removed
    have hremaining :
        (Finset.univ \ ({removed} : Finset (Candidate n))).Nonempty := by
      have hcard :
          ((Finset.univ : Finset (Candidate n)).erase removed).card = n + 1 := by
        simp [Candidate]
      have herase :
          ((Finset.univ : Finset (Candidate n)).erase removed).Nonempty :=
        Finset.card_pos.mp (by omega)
      simpa [Finset.sdiff_singleton_eq_erase] using herase
    have h := plackettLuce_expectedBestInSet_le_of_accuracy_le value hthetaLow
      hthetaLowHigh (Finset.univ \ ({removed} : Finset (Candidate n))) hremaining
    change
      AppliedModelingLib.SocialChoice.Ranking.expectedBestAfterRemoval
          (plackettLuceRankingPMF thetaLow value) value removed ≤
        AppliedModelingLib.SocialChoice.Ranking.expectedBestAfterRemoval
          (plackettLuceRankingPMF thetaHigh value) value removed
    simpa only [KR21Monoculture.expectedBestInSet_univ_sdiff_singleton]
      using h

/--
The source's Section 3.1 two-firm strategy conclusion, made explicit.  For
any realized candidate values and `0 < thetaH ≤ thetaA`, using the
Plackett--Luce law at `thetaA` weakly dominates using the law at `thetaH`,
against either algorithmic/shared or human/independent competition.

This is pointwise in the candidate values, so it is stronger than an
outer-distribution statement whenever the latter is defined.  It deliberately
states weak rather than strict dominance: equality is unavoidable for equal
accuracies or constant value profiles.
-/
theorem plackettLuce_more_accurate_algorithm_weakly_dominates
    {n : ℕ} (value : Candidate n → ℝ)
    {thetaH thetaA : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA) :
    let M : Model n :=
      { algorithmRanking := plackettLuceRankingPMF thetaA value
        humanRanking := plackettLuceRankingPMF thetaH value
        value := value }
    Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
        Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
      Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
        Model.payoffAgainst M Strategy.human Strategy.human := by
  rcases plackettLuce_semantic_improvement_of_accuracy_le value hthetaH hthetaHA with
    ⟨hfirst, hremaining⟩
  exact twoFirm_algorithm_weakly_dominates_of_semantic_improvement
    _ _ _ hfirst hremaining
    (plackettLuceRankingPMF_independent_eq_shared thetaA value).symm

/--
When the private human ranking has the higher Plackett--Luce temperature, it
weakly dominates the shared algorithmic ranking in both opponent rows.
-/
theorem plackettLuce_more_accurate_human_weakly_dominates
    {n : ℕ} (value : Candidate n → ℝ)
    {thetaA thetaH : ℝ} (hthetaA : 0 < thetaA) (hthetaAH : thetaA ≤ thetaH) :
    let M : Model n :=
      { algorithmRanking := plackettLuceRankingPMF thetaA value
        humanRanking := plackettLuceRankingPMF thetaH value
        value := value }
    Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
        Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
      Model.payoffAgainst M Strategy.human Strategy.human ≥
        Model.payoffAgainst M Strategy.algorithm Strategy.human := by
  rcases plackettLuce_semantic_improvement_of_accuracy_le value hthetaA hthetaAH with
    ⟨hfirst, hremaining⟩
  exact twoFirm_human_weakly_dominates_of_semantic_improvement
    _ _ _ hfirst hremaining
    (plackettLuceRankingPMF_independent_eq_shared thetaA value).symm

/--
Source-facing Section 3.1 endpoint.  The comparison is a semantic case split:
whichever available Plackett--Luce law has the weakly larger positive inverse
temperature weakly dominates in each of the two possible opponent rows.  At
equal temperatures both implications apply, so both strategies are weak best
responses; no strictness is asserted.
-/
theorem plackettLuce_best_available_weakly_dominates
    {n : ℕ} (value : Candidate n → ℝ)
    {thetaA thetaH : ℝ} (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking := plackettLuceRankingPMF thetaA value
        humanRanking := plackettLuceRankingPMF thetaH value
        value := value }
    (thetaH ≤ thetaA →
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
          Model.payoffAgainst M Strategy.human Strategy.human) ∧
      (thetaA ≤ thetaH →
        Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
          Model.payoffAgainst M Strategy.human Strategy.human ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.human) := by
  constructor
  · intro hthetaHA
    exact plackettLuce_more_accurate_algorithm_weakly_dominates
      value hthetaH hthetaHA
  · intro hthetaAH
    exact plackettLuce_more_accurate_human_weakly_dominates
      value hthetaA hthetaAH

end KR21Monoculture

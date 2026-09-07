import KR21Monoculture.LiteralDefinition1Theorem1Bridge
import AppliedModelingLib.Foundations.Math.IntervalCrossing

open AppliedModelingLib
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/-!
# Source Model and Proof Equations for KR21

This module exposes the source-facing two-firm model and equations (2)--(6)
without routing their review through a theorem-name convention.  The statements
spell out the strategy roles, equal-law condition, disagreement event, and
literal source payoff expressions.
-/

/--
Source Section 2.2's two-firm game semantics.  The algorithm-algorithm profile
shares one realized ranking; every other profile uses independent rankings.  A
labeled firm's payoff averages its first- and second-mover utilities because
the two-firm order is uniform.
-/
theorem source_two_firm_selection_game_semantics
    {n : Nat} (M : Model n) :
    Model.firstMoverEU M Strategy.algorithm =
        expectedFirstMoverUtility M.algorithmRanking M.value ∧
    Model.firstMoverEU M Strategy.human =
        expectedFirstMoverUtility M.humanRanking M.value ∧
    Model.secondMoverEU M Strategy.algorithm Strategy.algorithm =
        expectedSecondMoverShared M.algorithmRanking M.value ∧
    Model.secondMoverEU M Strategy.algorithm Strategy.human =
        expectedSecondMoverIndependent M.humanRanking M.algorithmRanking M.value ∧
    Model.secondMoverEU M Strategy.human Strategy.algorithm =
        expectedSecondMoverIndependent M.algorithmRanking M.humanRanking M.value ∧
    Model.secondMoverEU M Strategy.human Strategy.human =
        expectedSecondMoverIndependent M.humanRanking M.humanRanking M.value ∧
    ∀ self other : Strategy,
      Model.payoffAgainst M self other =
        (Model.firstMoverEU M self + Model.secondMoverEU M other self) / 2 := by
  simp [Model.firstMoverEU, Model.secondMoverEU, Model.rankingDist,
    Model.payoffAgainst]

/--
Equation (2): at equal accuracy, positive conditional first-versus-second gain
on top-choice disagreement is equivalent to an independent second mover
strictly preferring its own ranking to the shared ranking.  Positive event mass
is explicit because the source conditional expectation is otherwise undefined.
-/
theorem equation2_independent_reranking_payoff_equivalence
    {n : Nat} (mu : PMF (Ranking n)) (value : Candidate n -> Real)
    (hdisagreement : 0 < disagreementProb mu) :
    0 < disagreementConditionalGain mu value ↔
      expectedSecondMoverShared mu value <
        expectedSecondMoverIndependent mu mu value := by
  simpa [Model.PrefersIndependentReranking] using
    (prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos
      mu value hdisagreement).symm

/--
Equation (3): when the second mover's ranking and the first mover's ranking
are independent draws from the same law, its payoff gain is exactly the
expectation of the literal source gap on top-choice disagreement.  The first
coordinate is the independent second mover's ranking `pi`; the second is the
first mover's ranking `sigma`.
-/
theorem equation3_independent_reranking_payoff_identity
    {n : Nat} (mu : PMF (Ranking n)) (value : Candidate n -> Real) :
    expectedSecondMoverIndependent mu mu value -
        expectedSecondMoverShared mu value =
      pmfPairIndicatorExp mu mu disagreementEvent
        (fun pair =>
          value (firstChoice pair.1) - value (secondChoice pair.1)) := by
  calc
    _ = expectedRerankingGain mu value :=
      expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain mu value
    _ = pmfPairIndicatorExp mu mu disagreementEvent (pairRerankingGain value) :=
      expectedRerankingGain_eq_pairIndicatorExp mu value
    _ = pmfPairIndicatorExp mu mu disagreementEvent
          (fun pair =>
            value (firstChoice pair.1) - value (secondChoice pair.1)) := by
      unfold AppliedModelingLib.pmfPairIndicatorExp
      apply congrArg (AppliedModelingLib.pmfPairExp mu mu)
      funext pi sigma
      by_cases h : firstChoice pi = firstChoice sigma
      · have h' : pi 0 = sigma 0 := by
          simpa [firstChoice] using h
        simp [disagreementEvent, h']
      · have h' : pi 0 ≠ sigma 0 := by
          simpa [firstChoice] using h
        simp [disagreementEvent, h']

/--
Equation (4): its displayed numerator inequality is exactly strict best
response by the algorithm against an algorithmic opponent.
-/
theorem equation4_algorithm_best_response_against_algorithm_iff
    {n : Nat} (M : Model n) :
    (Model.firstMoverEU M Strategy.algorithm +
        Model.secondMoverEU M Strategy.algorithm Strategy.algorithm >
      Model.firstMoverEU M Strategy.human +
        Model.secondMoverEU M Strategy.algorithm Strategy.human) ↔
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm >
        Model.payoffAgainst M Strategy.human Strategy.algorithm :=
  (Model.payoffAgainst_gt_iff_sum_gt_sum
    (M := M) (s := Strategy.algorithm) (t := Strategy.human)
    (other := Strategy.algorithm)).symm

/--
Equation (5) from the literal finite-removal clauses of Definition 1.  The
strict full-set improvement gives the first-mover inequality, and weak
improvement after each singleton removal gives the second-mover inequality.
-/
theorem equation5_from_literal_definition1_removal
    {n : Nat} (F : AccuracyFamily n) (thetaA thetaH : Real)
    (hweak : ∀ remaining : Finset (Candidate n), remaining.Nonempty ->
      expectedBestInSet (F.dist thetaH) F.value remaining <=
        expectedBestInSet (F.dist thetaA) F.value remaining)
    (hstrict :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.human Strategy.algorithm >
      Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.human Strategy.human := by
  rcases theorem1RemovalMonotonicity_fields_of_literalFiniteRemoval
      (F := F) (thetaA := thetaA) (thetaH := thetaH) hweak hstrict with
    ⟨hfirst, hremaining⟩
  have hmono : AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
    ⟨hfirst, hremaining⟩
  have hlocal := AccuracyFamily.theorem1_algorithmAgainstHuman_gt_h_of_monotonicity
    F thetaA thetaH
    (AccuracyFamily.theorem1MonotonicityAt_of_removalMonotonicity
      F thetaA thetaH hmono)
  simpa [AccuracyFamily.theorem1_h,
    AccuracyFamily.theorem1_algorithmAgainstHuman] using hlocal

/--
Equation (6): a continuous sign change from `f < g` to `g < f` yields an
intermediate algorithm accuracy at which the two displayed payoffs against an
algorithmic opponent are equal.
-/
theorem equation6_indifference_threshold_of_sign_change
    {n : Nat} (F : AccuracyFamily n) (thetaH lo hi : Real)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        AccuracyFamily.theorem1_f F thetaA thetaH -
          AccuracyFamily.theorem1_g F thetaA thetaH)
      (Set.Icc lo hi))
    (hlo : AccuracyFamily.theorem1_f F lo thetaH <
      AccuracyFamily.theorem1_g F lo thetaH)
    (hhi : AccuracyFamily.theorem1_g F hi thetaH <
      AccuracyFamily.theorem1_f F hi thetaH) :
    ∃ thetaA, thetaH < thetaA ∧
      AccuracyFamily.theorem1_f F thetaA thetaH =
        AccuracyFamily.theorem1_g F thetaA thetaH := by
  have hzero :
      (0 : Real) ∈ Set.Icc
        (AccuracyFamily.theorem1_f F lo thetaH -
          AccuracyFamily.theorem1_g F lo thetaH)
        (AccuracyFamily.theorem1_f F hi thetaH -
          AccuracyFamily.theorem1_g F hi thetaH) := by
    constructor <;> linarith
  rcases intermediate_value_Icc (le_of_lt hlo_hi) hcontinuous hzero with
    ⟨thetaA, hthetaA, hzeroA⟩
  refine ⟨thetaA, hthetaH_lo.trans_le hthetaA.1, ?_⟩
  linarith

end KR21Monoculture

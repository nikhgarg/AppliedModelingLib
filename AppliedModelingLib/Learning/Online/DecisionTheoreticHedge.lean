import AppliedModelingLib.Learning.Online.Hedge
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Finite decision-theoretic Hedge

This module formalizes the reduction used in Theorem 5 of Freund--Schapire
(1997): at each round, Hedge allocates mass to experts and forms its decision
by sampling an expert according to that allocation and then sampling from the
expert's decision distribution.  The expected loss of that mixture is exactly
the allocation-weighted vector of expert expected losses.
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

open MeasureTheory

/--
One finite decision-theoretic prediction round.  The realized outcome need not
be finite: only the set of available decisions and the expert index set are
summed over in the reduction.
-/
structure FiniteDecisionHedgeRound (Expert Decision Outcome : Type*)
    [Fintype Expert] [DecidableEq Expert] [Fintype Decision] [DecidableEq Decision] where
  expertDecision : Expert → PMF Decision
  outcome : Outcome
  loss : Decision → Outcome → ℝ
  loss_mem_Icc : ∀ decision,
    0 ≤ loss decision outcome ∧ loss decision outcome ≤ 1

namespace FiniteDecisionHedgeRound

/-- The expected loss of each expert's distribution in one realized round. -/
noncomputable def inducedLoss
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Fintype Decision] [DecidableEq Decision]
    (round : FiniteDecisionHedgeRound Expert Decision Outcome) : Expert → ℝ :=
  fun expert => pmfExp (round.expertDecision expert) (fun decision => round.loss decision round.outcome)

/--
The learner decision obtained by the source prescription
`D = ∑_i p_i E_i`, represented as a PMF bind rather than as an informal
convex combination.
-/
noncomputable def mixedDecision
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Fintype Decision] [DecidableEq Decision]
    (round : FiniteDecisionHedgeRound Expert Decision Outcome)
    (allocation : PMF Expert) : PMF Decision :=
  allocation.bind round.expertDecision

/-- Every induced expert loss lies in the source interval `[0,1]`. -/
theorem inducedLoss_mem_Icc
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Fintype Decision] [DecidableEq Decision]
    (round : FiniteDecisionHedgeRound Expert Decision Outcome) (expert : Expert) :
    0 ≤ round.inducedLoss expert ∧ round.inducedLoss expert ≤ 1 := by
  constructor
  · exact pmfExp_nonneg_of_forall_nonneg (round.expertDecision expert) _
      (fun decision => (round.loss_mem_Icc decision).1)
  · exact pmfExp_le_of_forall_le (round.expertDecision expert) _ 1
      (fun decision => (round.loss_mem_Icc decision).2)

/--
The decision-mixture identity used in Theorem 5: the loss of `D` equals the
allocation expectation of the experts' expected losses.
-/
theorem mixedDecision_expectedLoss_eq_allocationExpectation
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Fintype Decision] [DecidableEq Decision]
    (round : FiniteDecisionHedgeRound Expert Decision Outcome)
    (allocation : PMF Expert) :
    pmfExp (round.mixedDecision allocation) (fun decision => round.loss decision round.outcome) =
      pmfExp allocation round.inducedLoss := by
  exact pmfExp_bind allocation round.expertDecision
    (fun decision => round.loss decision round.outcome)

/--
Run the decision-theoretic Hedge prescription through a finite list of
rounds.  At each stage, the current normalized source weights choose the
expert allocation and the induced expert-loss vector effects the next update.
-/
noncomputable def hedgeCumulativeDecisionLoss
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Decision] [DecidableEq Decision]
    (discount : ℝ) (hdiscount : 0 < discount) :
    HedgeWeightState Expert → List (FiniteDecisionHedgeRound Expert Decision Outcome) → ℝ
  | _, [] => 0
  | state, round :: rounds =>
      pmfExp (round.mixedDecision state.policy) (fun decision => round.loss decision round.outcome) +
        hedgeCumulativeDecisionLoss discount hdiscount
          (hedgeWeightStateStep state round.inducedLoss discount hdiscount) rounds

/--
The recursive decision-theoretic execution is exactly Hedge's cumulative
allocation loss on the induced expert-loss vectors.
-/
theorem hedgeCumulativeDecisionLoss_eq_hedgeWeightStateCumulativeLoss
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Decision] [DecidableEq Decision]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Expert)
    (rounds : List (FiniteDecisionHedgeRound Expert Decision Outcome)) :
    hedgeCumulativeDecisionLoss discount hdiscount state rounds =
      hedgeWeightStateCumulativeLoss discount hdiscount state (rounds.map inducedLoss) := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      change
        pmfExp (round.mixedDecision state.policy)
            (fun decision => round.loss decision round.outcome) +
            hedgeCumulativeDecisionLoss discount hdiscount
              (hedgeWeightStateStep state round.inducedLoss discount hdiscount) rounds =
          state.expectation round.inducedLoss +
            hedgeWeightStateCumulativeLoss discount hdiscount
              (hedgeWeightStateStep state round.inducedLoss discount hdiscount)
              (rounds.map inducedLoss)
      rw [ih]
      exact congrArg (fun x => x +
        hedgeWeightStateCumulativeLoss discount hdiscount
          (hedgeWeightStateStep state round.inducedLoss discount hdiscount)
          (rounds.map inducedLoss))
        (round.mixedDecision_expectedLoss_eq_allocationExpectation state.policy)

/--
Finite source model of Theorem 5.  For the source-tuned Hedge discount, the
decision distribution `D_t = ∑_i p_{t,i} E_{t,i}` has total expected loss at
most the best fixed expert's expected loss plus the displayed square-root
regret term.
-/
theorem hedgeCumulativeDecisionLoss_uniform_tuned_regret_bound
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Decision] [DecidableEq Decision]
    (state : HedgeWeightState Expert)
    (huniform : ∀ expert, state.weight expert = 1 / (Fintype.card Expert : ℝ))
    (rounds : List (FiniteDecisionHedgeRound Expert Decision Outcome))
    (lossBound : ℝ)
    (hbest_le_bound :
      Finset.univ.inf' Finset.univ_nonempty
        (fun expert => (rounds.map fun round => round.inducedLoss expert).sum) ≤ lossBound)
    (hlossBound_pos : 0 < lossBound)
    (hcard : 1 < Fintype.card Expert) :
    hedgeCumulativeDecisionLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Expert : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hcard_real : 1 < (Fintype.card Expert : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Expert : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Expert : ℝ) / lossBound := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlossBound_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state rounds ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun expert => (rounds.map fun round => round.inducedLoss expert).sum)) +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Expert : ℝ)) +
          Real.log (Fintype.card Expert : ℝ) := by
  have hbound := hedgeWeightState_uniform_tuned_regret_bound state huniform
    (rounds.map inducedLoss)
    (by
      intro loss hloss expert
      obtain ⟨round, hround, rfl⟩ := List.mem_map.mp hloss
      exact round.inducedLoss_mem_Icc expert)
    lossBound (by simpa only [List.map_map] using hbest_le_bound) hlossBound_pos hcard
  rw [hedgeCumulativeDecisionLoss_eq_hedgeWeightStateCumulativeLoss]
  simpa using hbound

/--
The horizon-based corollary of the finite Theorem-5 model.  Since every
round loss is at most one, `lossBound = rounds.length` is always available
when the path is nonempty.
-/
theorem hedgeCumulativeDecisionLoss_uniform_sqrt_regret_bound
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Decision] [DecidableEq Decision]
    (state : HedgeWeightState Expert)
    (huniform : ∀ expert, state.weight expert = 1 / (Fintype.card Expert : ℝ))
    (rounds : List (FiniteDecisionHedgeRound Expert Decision Outcome)) (hrounds : rounds ≠ [])
    (hcard : 1 < Fintype.card Expert) :
    hedgeCumulativeDecisionLoss
        (hedgeDiscountFromBounds (rounds.length : ℝ) (Real.log (Fintype.card Expert : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hlength_nat_pos : 0 < rounds.length := List.length_pos_of_ne_nil hrounds
          have hlength_pos : 0 < (rounds.length : ℝ) := by
            exact_mod_cast hlength_nat_pos
          have hcard_real : 1 < (Fintype.card Expert : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Expert : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Expert : ℝ) /
              (rounds.length : ℝ) := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state rounds ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun expert => (rounds.map fun round => round.inducedLoss expert).sum)) +
        Real.sqrt (2 * (rounds.length : ℝ) * Real.log (Fintype.card Expert : ℝ)) +
          Real.log (Fintype.card Expert : ℝ) := by
  have hbound := hedgeWeightState_uniform_sqrt_regret_bound state huniform
    (rounds.map inducedLoss) (by simpa using hrounds)
    (by
      intro loss hloss expert
      obtain ⟨round, hround, rfl⟩ := List.mem_map.mp hloss
      exact round.inducedLoss_mem_Icc expert)
    hcard
  rw [hedgeCumulativeDecisionLoss_eq_hedgeWeightStateCumulativeLoss]
  simpa using hbound

end FiniteDecisionHedgeRound

universe u v w

/--
A randomized decision game for a fixed finite expert set. Each value of
`Distribution` is injectively represented by an actual probability measure on
the source decision space. Expected loss is the integral of the source's
bounded measurable loss, and finite expert mixing is represented by the
corresponding weighted sum of measures.

The explicit measure representation keeps the reusable theorem independent of
a particular distribution data structure without weakening the paper's model
to an unrelated abstract carrier.
-/
structure GeneralDecisionHedgeGame (Expert : Type u) (Decision : Type v) (Outcome : Type w)
    [Fintype Expert] [DecidableEq Expert] [MeasurableSpace Decision] where
  /-- A representation of randomized decisions on the ambient decision space. -/
  Distribution : Type v
  /-- The probability measure represented by a randomized decision. -/
  toMeasure : Distribution → Measure Decision
  /-- The representation has no semantically distinct duplicate distributions. -/
  toMeasure_injective : Function.Injective toMeasure
  /-- Every represented randomized decision is a probability measure. -/
  toMeasure_isProbability : ∀ distribution, IsProbabilityMeasure (toMeasure distribution)
  /-- The source loss function on realized decisions and outcomes. -/
  loss : Decision → Outcome → ℝ
  /-- The source loss is measurable for every realized outcome. -/
  loss_measurable : ∀ outcome, Measurable (fun decision => loss decision outcome)
  /-- Source normalization of the realized loss to `[0,1]`. -/
  loss_mem_Icc : ∀ decision outcome,
    0 ≤ loss decision outcome ∧ loss decision outcome ≤ 1
  /-- Expected source loss of a randomized decision against an outcome. -/
  expectedLoss : Distribution → Outcome → ℝ
  /-- Expected loss is the integral of the source loss under the represented law. -/
  expectedLoss_eq_integral : ∀ distribution outcome,
    expectedLoss distribution outcome =
      ∫ decision, loss decision outcome ∂toMeasure distribution
  /-- Source normalization of expected loss to `[0,1]`. -/
  expectedLoss_mem_Icc : ∀ distribution outcome,
    0 ≤ expectedLoss distribution outcome ∧ expectedLoss distribution outcome ≤ 1
  /-- Finite convex mixing of the experts' randomized decisions. -/
  mixture : PMF Expert → (Expert → Distribution) → Distribution
  /-- The represented mixture is the source's weighted sum of expert laws. -/
  mixture_toMeasure : ∀ (allocation : PMF Expert) (expertDecision : Expert → Distribution),
    toMeasure (mixture allocation expertDecision) =
      ∑ expert, (allocation expert) • toMeasure (expertDecision expert)
  /-- Linearity of expected loss under the finite mixture. -/
  mixture_expectedLoss : ∀ (allocation : PMF Expert) (expertDecision : Expert → Distribution)
    (outcome : Outcome),
      expectedLoss (mixture allocation expertDecision) outcome =
        pmfExp allocation (fun expert => expectedLoss (expertDecision expert) outcome)

/-- One source Theorem-5 round in an abstract randomized decision game. -/
structure GeneralDecisionHedgeRound
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    (game : GeneralDecisionHedgeGame Expert Decision Outcome) where
  expertDecision : Expert → game.Distribution
  outcome : Outcome

namespace GeneralDecisionHedgeRound

/-- The expert expected-loss vector generated by one abstract decision round. -/
noncomputable def inducedLoss
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (round : GeneralDecisionHedgeRound game) : Expert → ℝ :=
  fun expert => game.expectedLoss (round.expertDecision expert) round.outcome

/-- The source decision `D = ∑_i p_i E_i` in an abstract decision game. -/
noncomputable def mixedDecision
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (round : GeneralDecisionHedgeRound game) (allocation : PMF Expert) : game.Distribution :=
  game.mixture allocation round.expertDecision

/-- Every induced expert loss is in the source interval `[0,1]`. -/
theorem inducedLoss_mem_Icc
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (round : GeneralDecisionHedgeRound game) (expert : Expert) :
    0 ≤ round.inducedLoss expert ∧ round.inducedLoss expert ≤ 1 := by
  exact game.expectedLoss_mem_Icc (round.expertDecision expert) round.outcome

/-- The expected-loss identity behind the Theorem-5 reduction. -/
theorem mixedDecision_expectedLoss_eq_allocationExpectation
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (round : GeneralDecisionHedgeRound game) (allocation : PMF Expert) :
    game.expectedLoss (round.mixedDecision allocation) round.outcome =
      pmfExp allocation round.inducedLoss := by
  exact game.mixture_expectedLoss allocation round.expertDecision round.outcome

/--
Execute the source decision-mixture prescription through a finite sequence of
abstract decision rounds.
-/
noncomputable def hedgeCumulativeDecisionLoss
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    [Nonempty Expert] {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (discount : ℝ) (hdiscount : 0 < discount) :
    HedgeWeightState Expert → List (GeneralDecisionHedgeRound game) → ℝ
  | _, [] => 0
  | state, round :: rounds =>
      game.expectedLoss (round.mixedDecision state.policy) round.outcome +
        hedgeCumulativeDecisionLoss discount hdiscount
          (hedgeWeightStateStep state round.inducedLoss discount hdiscount) rounds

/--
The abstract source execution is exactly Hedge's allocation loss on the
induced expert expected-loss path.
-/
theorem hedgeCumulativeDecisionLoss_eq_hedgeWeightStateCumulativeLoss
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    [Nonempty Expert] {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Expert)
    (rounds : List (GeneralDecisionHedgeRound game)) :
    hedgeCumulativeDecisionLoss discount hdiscount state rounds =
      hedgeWeightStateCumulativeLoss discount hdiscount state (rounds.map inducedLoss) := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      change
        game.expectedLoss (round.mixedDecision state.policy) round.outcome +
            hedgeCumulativeDecisionLoss discount hdiscount
              (hedgeWeightStateStep state round.inducedLoss discount hdiscount) rounds =
          state.expectation round.inducedLoss +
            hedgeWeightStateCumulativeLoss discount hdiscount
              (hedgeWeightStateStep state round.inducedLoss discount hdiscount)
              (rounds.map inducedLoss)
      rw [ih]
      exact congrArg (fun x => x +
        hedgeWeightStateCumulativeLoss discount hdiscount
          (hedgeWeightStateStep state round.inducedLoss discount hdiscount)
          (rounds.map inducedLoss))
        (round.mixedDecision_expectedLoss_eq_allocationExpectation state.policy)

/--
The full abstract decision-space form of Freund--Schapire (1997), Theorem 5.
It requires no finiteness of the decision or outcome space: all such structure
is encapsulated in the game distribution and its proved finite-mixture
expectation identity.
-/
theorem hedgeCumulativeDecisionLoss_uniform_tuned_regret_bound
    {Expert Decision Outcome : Type*} [Fintype Expert] [DecidableEq Expert]
    [MeasurableSpace Decision]
    [Nonempty Expert] {game : GeneralDecisionHedgeGame Expert Decision Outcome}
    (state : HedgeWeightState Expert)
    (huniform : ∀ expert, state.weight expert = 1 / (Fintype.card Expert : ℝ))
    (rounds : List (GeneralDecisionHedgeRound game))
    (lossBound : ℝ)
    (hbest_le_bound :
      Finset.univ.inf' Finset.univ_nonempty
        (fun expert => (rounds.map fun round => round.inducedLoss expert).sum) ≤ lossBound)
    (hlossBound_pos : 0 < lossBound)
    (hcard : 1 < Fintype.card Expert) :
    hedgeCumulativeDecisionLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Expert : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hcard_real : 1 < (Fintype.card Expert : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Expert : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Expert : ℝ) / lossBound := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlossBound_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state rounds ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun expert => (rounds.map fun round => round.inducedLoss expert).sum)) +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Expert : ℝ)) +
          Real.log (Fintype.card Expert : ℝ) := by
  have hbound := hedgeWeightState_uniform_tuned_regret_bound state huniform
    (rounds.map inducedLoss)
    (by
      intro loss hloss expert
      obtain ⟨round, hround, rfl⟩ := List.mem_map.mp hloss
      exact round.inducedLoss_mem_Icc expert)
    lossBound (by simpa only [List.map_map] using hbest_le_bound) hlossBound_pos hcard
  rw [hedgeCumulativeDecisionLoss_eq_hedgeWeightStateCumulativeLoss]
  simpa using hbound

end GeneralDecisionHedgeRound

end Online
end Learning
end AppliedModelingLib

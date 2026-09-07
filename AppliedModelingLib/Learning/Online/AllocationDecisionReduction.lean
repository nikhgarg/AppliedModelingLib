import AppliedModelingLib.Learning.Online.VovkLowerBound

/-!
# Allocation-to-decision reductions

Finite, history-dependent allocation policies and their exact reduction to the
unit-coordinate prediction game used in the Hedge Theorem-3 Appendix.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- A deterministic finite allocation policy chooses a simplex allocation from past loss vectors. -/
abbrev FiniteAllocationPolicy (Expert : Type*) [Fintype Expert] :=
  List (Expert → ℝ) → Expert → ℝ

/-- An allocation policy always returns a valid probability vector. -/
def FiniteAllocationPolicyAdmissible
    {Expert : Type*} [Fintype Expert] (policy : FiniteAllocationPolicy Expert) : Prop :=
  ∀ history : List (Expert → ℝ), FiniteProbabilitySimplex (policy history)

/-- The allocation-weighted loss of a finite loss vector. -/
noncomputable def allocationMixtureLoss
    {Expert : Type*} [Fintype Expert]
    (allocation loss : Expert → ℝ) : ℝ :=
  ∑ expert : Expert, allocation expert * loss expert

/--
Run an allocation policy on a remaining loss sequence after an already observed
loss history. The current allocation is chosen before the next loss is appended.
-/
noncomputable def allocationPolicyCumulativeLossFrom
    {Expert : Type*} [Fintype Expert] (policy : FiniteAllocationPolicy Expert) :
    List (Expert → ℝ) → List (Expert → ℝ) → ℝ
  | _history, [] => 0
  | history, loss :: losses =>
      allocationMixtureLoss (policy history) loss +
        allocationPolicyCumulativeLossFrom policy (history ++ [loss]) losses

/-- Cumulative allocation loss from the empty loss history. -/
noncomputable def allocationPolicyCumulativeLoss
    {Expert : Type*} [Fintype Expert]
    (policy : FiniteAllocationPolicy Expert) (losses : List (Expert → ℝ)) : ℝ :=
  allocationPolicyCumulativeLossFrom policy [] losses

/-- The cumulative loss of a fixed allocation expert on a finite loss sequence. -/
noncomputable def allocationExpertCumulativeLoss
    {Expert : Type*} (losses : List (Expert → ℝ)) (expert : Expert) : ℝ :=
  (losses.map fun loss => loss expert).sum

/--
The source `(c,a)` guarantee for a deterministic finite allocation policy.
Loss vectors are explicitly restricted to the source interval `[0,1]`.
-/
def FiniteAllocationPolicyBound
    {Expert : Type*} [Fintype Expert] [Nonempty Expert]
    (policy : FiniteAllocationPolicy Expert) (c a : ℝ) : Prop :=
  ∀ losses : List (Expert → ℝ),
    (∀ loss ∈ losses, ∀ expert, 0 ≤ loss expert ∧ loss expert ≤ 1) →
      allocationPolicyCumulativeLoss policy losses ≤
        c * finiteMin (allocationExpertCumulativeLoss losses) +
          a * Real.log (Fintype.card Expert : ℝ)

/-- One round of the unit-coordinate decision game, before a learner decision is chosen. -/
structure UnitCoordinateDecisionRound (Expert Coordinate : Type*)
    [Fintype Expert] [Fintype Coordinate] where
  expertDecision : Expert → Coordinate → ℝ
  expertDecision_mem : ∀ expert, FiniteProbabilitySimplex (expertDecision expert)
  outcome : Coordinate

/-- The allocation loss vector induced by a decision-game round. -/
noncomputable def UnitCoordinateDecisionRound.inducedLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateDecisionRound Expert Coordinate) : Expert → ℝ :=
  fun expert => unitCoordinateDecisionLoss (round.expertDecision expert) round.outcome

/-- Every induced allocation loss lies in the source range `[0,1]`. -/
theorem UnitCoordinateDecisionRound.inducedLoss_mem_Icc
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateDecisionRound Expert Coordinate) (expert : Expert) :
    0 ≤ round.inducedLoss expert ∧ round.inducedLoss expert ≤ 1 := by
  exact ⟨(round.expertDecision_mem expert).1 round.outcome,
    finiteProbabilitySimplex_coord_le_one (round.expertDecision_mem expert) round.outcome⟩

/--
The decision policy induced from an allocation policy: it applies that policy to
past induced loss vectors and mixes the experts' current simplex decisions.
-/
noncomputable def allocationPolicyToUnitCoordinateDecision
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert)
    (history : List (UnitCoordinateDecisionRound Expert Coordinate))
    (expertDecision : Expert → Coordinate → ℝ) : Coordinate → ℝ :=
  finiteSimplexMixture (policy (history.map UnitCoordinateDecisionRound.inducedLoss)) expertDecision

/-- The induced decision policy always makes a valid simplex decision. -/
theorem allocationPolicyToUnitCoordinateDecision_mem
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert) (hpolicy : FiniteAllocationPolicyAdmissible policy)
    (history : List (UnitCoordinateDecisionRound Expert Coordinate))
    (expertDecision : Expert → Coordinate → ℝ)
    (hexpertDecision : ∀ expert, FiniteProbabilitySimplex (expertDecision expert)) :
    FiniteProbabilitySimplex
      (allocationPolicyToUnitCoordinateDecision policy history expertDecision) := by
  exact finiteSimplexMixture_mem
    (policy (history.map UnitCoordinateDecisionRound.inducedLoss))
    (hpolicy (history.map UnitCoordinateDecisionRound.inducedLoss)) expertDecision hexpertDecision

/--
The decision-game loss accumulated by the policy induced from an allocation
policy, beginning from an already observed decision-game history.
-/
noncomputable def allocationPolicyDecisionCumulativeLossFrom
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert) :
    List (UnitCoordinateDecisionRound Expert Coordinate) →
      List (UnitCoordinateDecisionRound Expert Coordinate) → ℝ
  | _history, [] => 0
  | history, round :: rounds =>
      unitCoordinateDecisionLoss
          (allocationPolicyToUnitCoordinateDecision policy history round.expertDecision)
          round.outcome +
        allocationPolicyDecisionCumulativeLossFrom policy (history ++ [round]) rounds

/-- Cumulative decision-game loss from the empty decision-game history. -/
noncomputable def allocationPolicyDecisionCumulativeLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert)
    (rounds : List (UnitCoordinateDecisionRound Expert Coordinate)) : ℝ :=
  allocationPolicyDecisionCumulativeLossFrom policy [] rounds

/-- The cumulative loss of a fixed decision-game expert in the constructed rounds. -/
noncomputable def unitCoordinateDecisionExpertCumulativeLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (rounds : List (UnitCoordinateDecisionRound Expert Coordinate)) (expert : Expert) : ℝ :=
  (rounds.map fun round => round.inducedLoss expert).sum

/--
The decision-game `(c,a)` guarantee produced from a finite allocation policy.
The first conjunct states that the policy's current decision remains in the
simplex; the second is the source comparator guarantee over every finite horizon.
-/
def AllocationPolicyUnitCoordinateDecisionBound
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate] [Nonempty Expert]
    (policy : FiniteAllocationPolicy Expert) (c a : ℝ) : Prop :=
  (∀ history : List (UnitCoordinateDecisionRound Expert Coordinate),
    ∀ expertDecision : Expert → Coordinate → ℝ,
      (∀ expert, FiniteProbabilitySimplex (expertDecision expert)) →
        FiniteProbabilitySimplex
          (allocationPolicyToUnitCoordinateDecision policy history expertDecision)) ∧
    ∀ rounds : List (UnitCoordinateDecisionRound Expert Coordinate),
      allocationPolicyDecisionCumulativeLoss policy rounds ≤
        c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss rounds) +
          a * Real.log (Fintype.card Expert : ℝ)

/--
The policy-level reduction preserves cumulative loss exactly: the transformed
decision-game policy incurs the allocation policy's loss on the induced vectors.
-/
theorem allocationPolicyDecisionCumulativeLossFrom_eq_allocation
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert)
    (history : List (UnitCoordinateDecisionRound Expert Coordinate))
    (rounds : List (UnitCoordinateDecisionRound Expert Coordinate)) :
    allocationPolicyDecisionCumulativeLossFrom policy history rounds =
      allocationPolicyCumulativeLossFrom policy
        (history.map UnitCoordinateDecisionRound.inducedLoss)
        (rounds.map UnitCoordinateDecisionRound.inducedLoss) := by
  induction rounds generalizing history with
  | nil => rfl
  | cons round rounds ih =>
      simp only [allocationPolicyDecisionCumulativeLossFrom,
        allocationPolicyCumulativeLossFrom, List.map_cons]
      change allocationMixtureLoss
          (policy (history.map UnitCoordinateDecisionRound.inducedLoss)) round.inducedLoss +
        allocationPolicyDecisionCumulativeLossFrom policy (history ++ [round]) rounds =
          allocationMixtureLoss
            (policy (history.map UnitCoordinateDecisionRound.inducedLoss)) round.inducedLoss +
          allocationPolicyCumulativeLossFrom policy
            ((history.map UnitCoordinateDecisionRound.inducedLoss) ++ [round.inducedLoss])
            (rounds.map UnitCoordinateDecisionRound.inducedLoss)
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil]

/-- The policy-level reduction preserves cumulative loss from the initial history. -/
theorem allocationPolicyDecisionCumulativeLoss_eq_allocation
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert)
    (rounds : List (UnitCoordinateDecisionRound Expert Coordinate)) :
    allocationPolicyDecisionCumulativeLoss policy rounds =
      allocationPolicyCumulativeLoss policy
        (rounds.map UnitCoordinateDecisionRound.inducedLoss) := by
  exact allocationPolicyDecisionCumulativeLossFrom_eq_allocation policy [] rounds

/--
An allocation policy satisfying the source global guarantee induces a valid
decision-game policy with the same `(c,a)` guarantee. This closes the global
policy-guarantee transport in the Hedge Appendix reduction.
-/
theorem finiteAllocationPolicyBound_to_unitCoordinateDecisionBound
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate] [Nonempty Expert]
    (policy : FiniteAllocationPolicy Expert) (hpolicy : FiniteAllocationPolicyAdmissible policy)
    (c a : ℝ) (hbound : FiniteAllocationPolicyBound policy c a) :
    AllocationPolicyUnitCoordinateDecisionBound (Coordinate := Coordinate) policy c a := by
  constructor
  · intro history expertDecision hexpertDecision
    exact allocationPolicyToUnitCoordinateDecision_mem policy hpolicy history expertDecision
      hexpertDecision
  · intro rounds
    have hinduced_range :
        ∀ loss ∈ rounds.map UnitCoordinateDecisionRound.inducedLoss,
          ∀ expert, 0 ≤ loss expert ∧ loss expert ≤ 1 := by
      intro loss hloss expert
      obtain ⟨round, _hround, rfl⟩ := List.mem_map.1 hloss
      exact round.inducedLoss_mem_Icc expert
    rw [allocationPolicyDecisionCumulativeLoss_eq_allocation]
    have hcomparator :
        allocationExpertCumulativeLoss (rounds.map UnitCoordinateDecisionRound.inducedLoss) =
          unitCoordinateDecisionExpertCumulativeLoss rounds := by
      funext expert
      simp only [allocationExpertCumulativeLoss, unitCoordinateDecisionExpertCumulativeLoss,
        List.map_map, Function.comp_def]
    rw [← hcomparator]
    exact hbound (rounds.map UnitCoordinateDecisionRound.inducedLoss) hinduced_range

end Online
end Learning
end AppliedModelingLib

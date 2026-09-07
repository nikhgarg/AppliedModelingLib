import AppliedModelingLib.Learning.Online.AllocationDecisionReduction

/-!
# Finite unit-coordinate prediction game

The finite decision-game interface used in the Vovk dependency of the Hedge
Theorem-3 Appendix. A learner policy sees the current expert simplex decisions,
chooses a simplex decision, and is evaluated against the best fixed expert.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- A deterministic learner policy in the finite unit-coordinate prediction game. -/
abbrev UnitCoordinateDecisionPolicy (Expert Coordinate : Type*)
    [Fintype Expert] [Fintype Coordinate] :=
  List (UnitCoordinateDecisionRound Expert Coordinate) →
    (Expert → Coordinate → ℝ) → Coordinate → ℝ

/-- A decision policy always responds with a simplex decision. -/
def UnitCoordinateDecisionPolicyAdmissible
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) : Prop :=
  ∀ history : List (UnitCoordinateDecisionRound Expert Coordinate),
    ∀ expertDecision : Expert → Coordinate → ℝ,
      (∀ expert, FiniteProbabilitySimplex (expertDecision expert)) →
        FiniteProbabilitySimplex (policy history expertDecision)

/-- Cumulative learner loss of a decision policy, starting from a prior game history. -/
noncomputable def unitCoordinateDecisionPolicyCumulativeLossFrom
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) :
    List (UnitCoordinateDecisionRound Expert Coordinate) →
      List (UnitCoordinateDecisionRound Expert Coordinate) → ℝ
  | _history, [] => 0
  | history, round :: rounds =>
      unitCoordinateDecisionLoss (policy history round.expertDecision) round.outcome +
        unitCoordinateDecisionPolicyCumulativeLossFrom policy (history ++ [round]) rounds

/-- Cumulative learner loss of a decision policy from the empty game history. -/
noncomputable def unitCoordinateDecisionPolicyCumulativeLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (rounds : List (UnitCoordinateDecisionRound Expert Coordinate)) : ℝ :=
  unitCoordinateDecisionPolicyCumulativeLossFrom policy [] rounds

/-- The finite source `(c,a)` guarantee for a decision policy in the unit-coordinate game. -/
def UnitCoordinateDecisionPolicyBound
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate] [Nonempty Expert]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (c a : ℝ) : Prop :=
  UnitCoordinateDecisionPolicyAdmissible policy ∧
    ∀ rounds : List (UnitCoordinateDecisionRound Expert Coordinate),
      unitCoordinateDecisionPolicyCumulativeLoss policy rounds ≤
        c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss rounds) +
          a * Real.log (Fintype.card Expert : ℝ)

/-- The decision policy induced by an allocation policy in the Hedge Appendix reduction. -/
noncomputable def allocationPolicyAsUnitCoordinateDecisionPolicy
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : FiniteAllocationPolicy Expert) : UnitCoordinateDecisionPolicy Expert Coordinate :=
  fun history expertDecision =>
    allocationPolicyToUnitCoordinateDecision policy history expertDecision

/--
The policy-level allocation reduction is a valid decision-game `(c,a)` bound.
-/
theorem finiteAllocationPolicyBound_to_unitCoordinateDecisionPolicyBound
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate] [Nonempty Expert]
    (policy : FiniteAllocationPolicy Expert) (hpolicy : FiniteAllocationPolicyAdmissible policy)
    (c a : ℝ) (hbound : FiniteAllocationPolicyBound policy c a) :
    UnitCoordinateDecisionPolicyBound
      (allocationPolicyAsUnitCoordinateDecisionPolicy (Coordinate := Coordinate) policy) c a := by
  constructor
  · intro history expertDecision hexpertDecision
    exact allocationPolicyToUnitCoordinateDecision_mem policy hpolicy history expertDecision
      hexpertDecision
  · intro rounds
    have hloss_eq_from :
        ∀ (history : List (UnitCoordinateDecisionRound Expert Coordinate))
          (rounds : List (UnitCoordinateDecisionRound Expert Coordinate)),
          unitCoordinateDecisionPolicyCumulativeLossFrom
              (allocationPolicyAsUnitCoordinateDecisionPolicy (Coordinate := Coordinate) policy)
              history rounds =
            allocationPolicyDecisionCumulativeLossFrom policy history rounds := by
      intro history rounds
      induction rounds generalizing history with
      | nil => rfl
      | cons round rounds ih =>
          simp only [unitCoordinateDecisionPolicyCumulativeLossFrom,
            allocationPolicyDecisionCumulativeLossFrom,
            allocationPolicyAsUnitCoordinateDecisionPolicy]
          rw [ih (history ++ [round])]
    have hloss_eq : unitCoordinateDecisionPolicyCumulativeLoss
        (allocationPolicyAsUnitCoordinateDecisionPolicy (Coordinate := Coordinate) policy) rounds =
        allocationPolicyDecisionCumulativeLoss policy rounds := by
      exact hloss_eq_from [] rounds
    rw [hloss_eq]
    exact
      (finiteAllocationPolicyBound_to_unitCoordinateDecisionBound policy hpolicy c a
        hbound).2 rounds

/--
The finite unit-coordinate game is `(c,a)`-bounded when every finite expert set
admits an admissible policy with the source comparator guarantee.
-/
def finiteUnitCoordinateGameBounded (Coordinate : Type) [Fintype Coordinate]
    (c a : ℝ) : Prop :=
  ∀ (Expert : Type) [Fintype Expert] [Nonempty Expert],
    ∃ policy : UnitCoordinateDecisionPolicy Expert Coordinate,
      UnitCoordinateDecisionPolicyBound policy c a

/--
The corresponding global allocation premise, represented as a family of finite
allocation policies indexed by the expert type.
-/
def globalFiniteAllocationPolicyBounded (c a : ℝ) : Prop :=
  ∀ (Expert : Type) [Fintype Expert] [Nonempty Expert],
    ∃ policy : FiniteAllocationPolicy Expert,
      FiniteAllocationPolicyAdmissible policy ∧ FiniteAllocationPolicyBound policy c a

/--
The Hedge Appendix reduction turns the global allocation premise into the
finite unit-coordinate decision-game premise with identical constants.
-/
theorem globalFiniteAllocationPolicyBounded_to_finiteUnitCoordinateGameBounded
    {Coordinate : Type} [Fintype Coordinate] (c a : ℝ)
    (hbound : globalFiniteAllocationPolicyBounded c a) :
    finiteUnitCoordinateGameBounded Coordinate c a := by
  intro Expert _instExpert _instNonemptyExpert
  obtain ⟨policy, hpolicy, hpolicyBound⟩ := hbound Expert
  exact ⟨allocationPolicyAsUnitCoordinateDecisionPolicy policy,
    finiteAllocationPolicyBound_to_unitCoordinateDecisionPolicyBound policy hpolicy c a
      hpolicyBound⟩

end Online
end Learning
end AppliedModelingLib

import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionAffordanceSemantics
import Mathlib.Tactic

open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The extended-model demand rule turns local coalition affordability into a
global match.  The two premises are the source semantics: a coalition score is
the corresponding global score, and a student is unmatched exactly when no
global college is affordable.  No restriction on outside-college preferences
or scores is used.
-/
theorem theorem4_local_affordance_implies_global_match_of_unmatched_iff_no_global_affordance
    {C : ℕ} {Outcome GlobalCollege : Type*} [Fintype GlobalCollege]
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (globalCutoff : GlobalCollege → ℝ)
    (globalScore : Outcome → GlobalCollege → ℝ)
    (globalChoice : Outcome → Option GlobalCollege)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hcoalition_score :
      ∀ outcome : Outcome, ∀ c : Fin (C + 1),
        globalScore outcome (coalitionEmbedding c) =
          (localCoordinates outcome).1 + (localCoordinates outcome).2 c)
    (hunmatched_iff_no_global_affordance :
      ∀ outcome : Outcome,
        globalChoice outcome = none ↔
          ¬ cutoffCrossed (globalScore outcome) globalCutoff)
    (active : Finset (Fin (C + 1)))
    (localCutoff : Fin (C + 1) → ℝ)
    (hlocalCutoff :
      ∀ c : Fin (C + 1),
        localCutoff c = globalCutoff (coalitionEmbedding c)) :
    ∀ outcome : Outcome,
      theorem4CoalitionAffordanceEvent active localCutoff
          (localCoordinates outcome) →
        chosenInActive globalChoice
          (Finset.univ : Finset GlobalCollege) outcome := by
  intro outcome hlocal
  rcases hlocal with ⟨c, hc, hcross⟩
  have hglobal_cross :
      cutoffCrossed (globalScore outcome) globalCutoff := by
    refine ⟨coalitionEmbedding c, ?_⟩
    calc
      globalCutoff (coalitionEmbedding c) = localCutoff c :=
        (hlocalCutoff c).symm
      _ < (localCoordinates outcome).1 + (localCoordinates outcome).2 c :=
        hcross
      _ = globalScore outcome (coalitionEmbedding c) :=
        (hcoalition_score outcome c).symm
  cases hchoice : globalChoice outcome with
  | none =>
      exact False.elim
        ((hunmatched_iff_no_global_affordance outcome).mp hchoice hglobal_cross)
  | some d =>
      exact ⟨d, Finset.mem_univ _, hchoice⟩

end

end PG24NoisyMatchingMarkets

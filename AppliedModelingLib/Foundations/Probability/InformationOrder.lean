import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite Information Orders

Reusable finite-experiment garbling and Blackwell-sufficiency primitives.

## Main declarations

- `BlackwellSufficient`
- `BlackwellSufficient.bind`
- `BlackwellSufficient.map`
- `BlackwellSufficient.refl`
- `BlackwellSufficient.trans`
-/

namespace AppliedModelingLib

/--
A richer finite experiment `rich` Blackwell-suffices for a coarser experiment
`coarse` when the coarser signal can be generated from the richer signal by a
single garbling kernel, uniformly over latent states.
-/
def BlackwellSufficient {State RichSignal CoarseSignal : Type*}
    (rich : State → PMF RichSignal) (coarse : State → PMF CoarseSignal) : Prop :=
  ∃ garbling : RichSignal → PMF CoarseSignal,
    ∀ state, (rich state).bind garbling = coarse state

namespace BlackwellSufficient

/-- Blackwell sufficiency from an explicit garbling kernel. -/
theorem bind {State RichSignal CoarseSignal : Type*}
    (rich : State → PMF RichSignal)
    (garbling : RichSignal → PMF CoarseSignal) :
    BlackwellSufficient rich (fun state => (rich state).bind garbling) := by
  exact ⟨garbling, fun _ => rfl⟩

/-- Deterministic post-processing is a Blackwell garbling. -/
theorem map {State RichSignal CoarseSignal : Type*}
    (rich : State → PMF RichSignal) (f : RichSignal → CoarseSignal) :
    BlackwellSufficient rich (fun state => PMF.map f (rich state)) := by
  refine ⟨fun signal => PMF.pure (f signal), ?_⟩
  intro state
  simpa [Function.comp_def] using
    (PMF.bind_pure_comp (f := f) (p := rich state))

/-- Blackwell sufficiency is reflexive. -/
theorem refl {State Signal : Type*} (experiment : State → PMF Signal) :
    BlackwellSufficient experiment experiment := by
  refine ⟨fun signal => PMF.pure signal, ?_⟩
  intro state
  simp

/-- Blackwell sufficiency is transitive under composition of garblings. -/
theorem trans {State RichSignal MidSignal CoarseSignal : Type*}
    {rich : State → PMF RichSignal}
    {middle : State → PMF MidSignal}
    {coarse : State → PMF CoarseSignal}
    (hrich_mid : BlackwellSufficient rich middle)
    (hmid_coarse : BlackwellSufficient middle coarse) :
    BlackwellSufficient rich coarse := by
  rcases hrich_mid with ⟨garbleMiddle, hgarbleMiddle⟩
  rcases hmid_coarse with ⟨garbleCoarse, hgarbleCoarse⟩
  refine ⟨fun signal => (garbleMiddle signal).bind garbleCoarse, ?_⟩
  intro state
  rw [← PMF.bind_bind, hgarbleMiddle state, hgarbleCoarse state]

end BlackwellSufficient

end AppliedModelingLib

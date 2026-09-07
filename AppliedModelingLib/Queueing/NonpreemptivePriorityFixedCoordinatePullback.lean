import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceMeasurability

/-!
# Pulling back fixed priority-trace coordinates

Finite replay skeletons are independent of the carrier on which their real
coordinates are evaluated.  This module records the elementary pullback of
such coordinates along a measurable map.  It is useful when a replay over a
sample carrier is subsequently observed on a product carrier containing an
additional physical-time coordinate.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

variable {Ω Ξ : Type*}
variable {n : ℕ} {JobId : Type*}

/-- Pull a fixed-label priority job coordinate back along a carrier map. -/
def NonpreemptivePriorityFixedJobCoordinate.pullback
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId) (f : Ξ → Ω) :
    NonpreemptivePriorityFixedJobCoordinate Ξ n JobId :=
  { identifier := job.identifier
    priority := job.priority
    arrivalTime := job.arrivalTime ∘ f
    serviceWork := job.serviceWork ∘ f }

/-- Evaluation commutes with pulling a fixed job coordinate back. -/
theorem NonpreemptivePriorityFixedJobCoordinate.eval_pullback
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId) (f : Ξ → Ω)
    (xi : Ξ) :
    (job.pullback f).eval xi = job.eval (f xi) := by
  rfl

/-- Measurable fixed job coordinates remain measurable after a measurable
carrier pullback. -/
theorem NonpreemptivePriorityFixedJobCoordinate.CoordinatesMeasurable.pullback
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId}
    (hjob : job.CoordinatesMeasurable) (f : Ξ → Ω) (hf : Measurable f) :
    (job.pullback f).CoordinatesMeasurable := by
  exact ⟨hjob.1.comp hf, hjob.2.comp hf⟩

/-- Pull a fixed-shape priority state coordinate back along a carrier map. -/
def NonpreemptivePriorityFixedStateCoordinate.pullback
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) (f : Ξ → Ω) :
    NonpreemptivePriorityFixedStateCoordinate Ξ n JobId :=
  { currentTime := state.currentTime ∘ f
    active := state.active.map fun entry => (entry.1.pullback f, entry.2 ∘ f)
    waiting := fun i => (state.waiting i).map fun job => job.pullback f
    completed := state.completed.map fun entry => (entry.1.pullback f, entry.2 ∘ f) }

/-- Evaluation commutes with pulling a fixed state coordinate back. -/
theorem NonpreemptivePriorityFixedStateCoordinate.eval_pullback
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) (f : Ξ → Ω)
    (xi : Ξ) :
    (state.pullback f).eval xi = state.eval (f xi) := by
  rcases state with ⟨currentTime, active, waiting, completed⟩
  cases active <;>
    simp [NonpreemptivePriorityFixedStateCoordinate.pullback,
      NonpreemptivePriorityFixedStateCoordinate.eval,
      NonpreemptivePriorityFixedJobCoordinate.pullback,
      NonpreemptivePriorityFixedJobCoordinate.eval, Function.comp_def]

/-- Measurable fixed state coordinates remain measurable after a measurable
carrier pullback. -/
theorem NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.pullback
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId}
    (hstate : state.CoordinatesMeasurable) (f : Ξ → Ω) (hf : Measurable f) :
    (state.pullback f).CoordinatesMeasurable := by
  refine ⟨hstate.1.comp hf, ?_, ?_, ?_⟩
  · intro entry hentry
    rcases hactive : state.active with _ | ⟨job, residual⟩
    · simp [NonpreemptivePriorityFixedStateCoordinate.pullback, hactive] at hentry
    · simp only [NonpreemptivePriorityFixedStateCoordinate.pullback, hactive,
        Option.map_some] at hentry
      rcases hentry with ⟨rfl, rfl⟩
      have hcoords := hstate.2.1 (job, residual) (by simp [hactive])
      exact ⟨hcoords.1.pullback f hf, hcoords.2.comp hf⟩
  · intro i job hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, rfl⟩
    exact (hstate.2.2.1 i original horiginal).pullback f hf
  · intro entry hentry
    rcases List.mem_map.mp hentry with ⟨original, horiginal, rfl⟩
    have hcoords := hstate.2.2.2 original horiginal
    exact ⟨hcoords.1.pullback f hf, hcoords.2.comp hf⟩

end

end AppliedModelingLib.Queueing

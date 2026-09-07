import AppliedModelingLib.Foundations.Probability.KernelAdaptiveProduct

/-!
# Finite union bounds for adaptive kernels

This module gives the elementary finite-horizon failure bound for an
Ionescu--Tulcea trajectory.  A measurable bad event at round `r` may depend on
the entire public prefix through `r` and on the fresh outcome.  If its
conditional mass is at most `q r` for every prefix, then the probability that
any of the first `rounds` bad events occurs is at most the sum of those bounds.

No independence between the round events is assumed.  This is the appropriate
interface for adaptive noise mechanisms whose scale or requested accuracy may
depend on the public transcript.
-/

namespace AppliedModelingLib

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

noncomputable section

/-- A uniform bound on every section of an event bounds its mass under a
measure--kernel composition product. -/
theorem compProd_apply_le_of_forall
    {History Outcome : Type*}
    [MeasurableSpace History] [MeasurableSpace Outcome]
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (kernel : Kernel History Outcome) [IsMarkovKernel kernel]
    (event : Set (History × Outcome)) (hevent : MeasurableSet event)
    (bound : ℝ≥0∞)
    (hbound : ∀ history,
      kernel history (Prod.mk history ⁻¹' event) ≤ bound) :
    (historyLaw ⊗ₘ kernel) event ≤ bound := by
  rw [Measure.compProd_apply hevent]
  calc
    ∫⁻ history, kernel history (Prod.mk history ⁻¹' event) ∂historyLaw ≤
        ∫⁻ _history, bound ∂historyLaw := by
          exact lintegral_mono fun history ↦ hbound history
    _ = bound := by simp

/-- A conditional one-round bound transfers to the corresponding event on the
full adaptive trajectory. -/
theorem trajMeasure_roundEvent_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)]
    (bad : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hbad : ∀ round, MeasurableSet (bad round))
    (bound : ℕ → ℝ≥0∞)
    (hbound : ∀ round history,
      kernel round history (Prod.mk history ⁻¹' bad round) ≤ bound round)
    (round : ℕ) :
    Kernel.trajMeasure initialLaw kernel
        {trace | kernelAdaptiveRoundPair round trace ∈ bad round} ≤
      bound round := by
  let trajectory : Measure (ℕ → Outcome) :=
    Kernel.trajMeasure initialLaw kernel
  let historyLaw : Measure ((i : Finset.Iic round) → Outcome) :=
    trajectory.map (frestrictLe round)
  let pairMap : (ℕ → Outcome) → KernelAdaptiveRoundPair Outcome round :=
    kernelAdaptiveRoundPair round
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_frestrictLe round).aemeasurable
  have hpairMap : Measurable pairMap :=
    measurable_kernelAdaptiveRoundPair round
  have hjoint : trajectory.map pairMap = historyLaw ⊗ₘ kernel round := by
    dsimp [trajectory, historyLaw, pairMap]
    exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
  calc
    trajectory {trace | kernelAdaptiveRoundPair round trace ∈ bad round} =
        (trajectory.map pairMap) (bad round) := by
          rw [Measure.map_apply hpairMap (hbad round)]
          rfl
    _ = (historyLaw ⊗ₘ kernel round) (bad round) := by rw [hjoint]
    _ ≤ bound round := compProd_apply_le_of_forall historyLaw
      (kernel round) (bad round) (hbad round) (bound round) (hbound round)

/-- Adaptive finite union bound in the measure's native `ℝ≥0∞` scale. -/
theorem trajMeasure_exists_round_bad_le_sum
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)]
    (bad : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hbad : ∀ round, MeasurableSet (bad round))
    (bound : ℕ → ℝ≥0∞)
    (hbound : ∀ round history,
      kernel round history (Prod.mk history ⁻¹' bad round) ≤ bound round)
    (rounds : ℕ) :
    Kernel.trajMeasure initialLaw kernel
        {trace | ∃ round ∈ Finset.range rounds,
          kernelAdaptiveRoundPair round trace ∈ bad round} ≤
      ∑ round ∈ Finset.range rounds, bound round := by
  let trajectory : Measure (ℕ → Outcome) :=
    Kernel.trajMeasure initialLaw kernel
  have hevent :
      {trace | ∃ round ∈ Finset.range rounds,
        kernelAdaptiveRoundPair round trace ∈ bad round} =
        ⋃ round ∈ Finset.range rounds,
          {trace | kernelAdaptiveRoundPair round trace ∈ bad round} := by
    ext trace
    simp
  rw [hevent]
  calc
    trajectory (⋃ round ∈ Finset.range rounds,
        {trace | kernelAdaptiveRoundPair round trace ∈ bad round}) ≤
        ∑ round ∈ Finset.range rounds,
          trajectory {trace |
            kernelAdaptiveRoundPair round trace ∈ bad round} :=
      measure_biUnion_finset_le (Finset.range rounds) _
    _ ≤ ∑ round ∈ Finset.range rounds, bound round := by
      gcongr with round hround
      exact trajMeasure_roundEvent_le initialLaw kernel bad hbad bound hbound round

end

end AppliedModelingLib

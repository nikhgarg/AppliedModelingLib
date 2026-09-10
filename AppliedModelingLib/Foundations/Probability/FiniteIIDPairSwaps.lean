import AppliedModelingLib.Foundations.Probability.FiniteIID

/-!
# Pair swaps on finite iid samples

This module provides the measure-preserving coordinatewise pair swaps used by
ghost-sample symmetrization arguments.  It is deliberately independent of a
particular learning class or loss function.
-/

namespace AppliedModelingLib
namespace Probability

open MeasureTheory ProbabilityTheory

/-- A Boolean vector selects the first orientation at `true` and the swapped
orientation at `false` in each coordinate pair. -/
def finiteIIDPairSwap
    {Index Outcome : Type*} (swap : Index → Bool) :
    (Index → Outcome × Outcome) → Index → Outcome × Outcome :=
  fun sample index => if swap index then sample index else (sample index).swap

/-- The coordinatewise pair-orientation map is a measurable equivalence.  The
Boolean convention agrees with `finiteIIDPairSwap`: `true` keeps a coordinate
in its first orientation and `false` reverses it. -/
noncomputable def finiteIIDPairSwapMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sampleCount : ℕ) (swap : Fin sampleCount → Bool) :
    (Fin sampleCount → Outcome × Outcome) ≃ᵐ
      (Fin sampleCount → Outcome × Outcome) :=
  MeasurableEquiv.piCongrRight fun index =>
    if swap index then MeasurableEquiv.refl (Outcome × Outcome)
    else MeasurableEquiv.prodComm

@[simp]
theorem finiteIIDPairSwapMeasEquiv_apply
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sampleCount : ℕ) (swap : Fin sampleCount → Bool)
    (sample : Fin sampleCount → Outcome × Outcome) :
    finiteIIDPairSwapMeasEquiv sampleCount swap sample = finiteIIDPairSwap swap sample := by
  funext index
  by_cases hswap : swap index
  · simp [finiteIIDPairSwapMeasEquiv, MeasurableEquiv.piCongrRight,
      Equiv.piCongrRight_apply, finiteIIDPairSwap, hswap]
  · simp [finiteIIDPairSwapMeasEquiv, MeasurableEquiv.piCongrRight,
      Equiv.piCongrRight_apply, MeasurableEquiv.prodComm,
      Equiv.prodComm_apply, finiteIIDPairSwap, hswap]

/-- The coordinatewise pair representation of two iid finite samples. -/
noncomputable def finiteIIDPairingMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome] (sampleCount : ℕ) :
    (Fin sampleCount → Outcome × Outcome) ≃ᵐ
      (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome) :=
  MeasurableEquiv.arrowProdEquivProdArrow Outcome Outcome (Fin sampleCount)

@[simp]
theorem finiteIIDPairingMeasEquiv_apply
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sampleCount : ℕ) (sample : Fin sampleCount → Outcome × Outcome) :
    finiteIIDPairingMeasEquiv sampleCount sample =
      (fun index => (sample index).1, fun index => (sample index).2) := by
  rfl

@[simp]
theorem finiteIIDPairingMeasEquiv_symm_apply
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sampleCount : ℕ) (samples :
      (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome)) :
    (finiteIIDPairingMeasEquiv sampleCount).symm samples =
      fun index => (samples.1 index, samples.2 index) := by
  rfl

/-- Pairing coordinatewise iid pairs produces two independent iid samples. -/
theorem map_finiteIIDPairingMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] (sampleCount : ℕ) :
    Measure.map (finiteIIDPairingMeasEquiv (Outcome := Outcome) sampleCount)
      (finiteIIDSampleLaw (law.prod law) sampleCount) =
      (finiteIIDSampleLaw law sampleCount).prod (finiteIIDSampleLaw law sampleCount) := by
  letI : ∀ _ : Fin sampleCount, SigmaFinite law := fun _ => inferInstance
  simpa [finiteIIDPairingMeasEquiv, finiteIIDSampleLaw] using
    (measurePreserving_arrowProdEquivProdArrow Outcome Outcome (Fin sampleCount)
      (fun _ => law) (fun _ => law)).map_eq

/-- Swapping any chosen coordinate pairs preserves the finite iid product of
the equal-coordinate pair law. -/
theorem measurePreserving_finiteIIDPairSwap
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (swap : Fin sampleCount → Bool) :
    MeasurePreserving (finiteIIDPairSwap swap)
      (finiteIIDSampleLaw (law.prod law) sampleCount)
      (finiteIIDSampleLaw (law.prod law) sampleCount) := by
  letI : ∀ _ : Fin sampleCount, SigmaFinite (law.prod law) := fun _ => inferInstance
  let coordinateSwap : (index : Fin sampleCount) →
      Outcome × Outcome → Outcome × Outcome :=
    fun index pair => if swap index then pair else pair.swap
  change MeasurePreserving (fun sample index =>
      coordinateSwap index (sample index))
    (Measure.pi fun _ : Fin sampleCount => law.prod law)
    (Measure.pi fun _ : Fin sampleCount => law.prod law)
  apply measurePreserving_pi (fun _ : Fin sampleCount => law.prod law)
    (fun _ : Fin sampleCount => law.prod law)
  intro index
  by_cases hswap : swap index
  · simpa [coordinateSwap, hswap] using MeasurePreserving.id (law.prod law)
  · simpa [coordinateSwap, hswap] using
      (Measure.measurePreserving_swap (μ := law) (ν := law))

/-- A coordinatewise pair-orientation change preserves the iid pair law, in
the measurable-equivalence form used to transport integrals. -/
theorem measurePreserving_finiteIIDPairSwapMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (swap : Fin sampleCount → Bool) :
    MeasurePreserving (finiteIIDPairSwapMeasEquiv sampleCount swap)
      (finiteIIDSampleLaw (law.prod law) sampleCount)
      (finiteIIDSampleLaw (law.prod law) sampleCount) := by
  have hswap : (finiteIIDPairSwapMeasEquiv sampleCount swap :
      (Fin sampleCount → Outcome × Outcome) →
        Fin sampleCount → Outcome × Outcome) = finiteIIDPairSwap swap := by
    funext sample
    exact finiteIIDPairSwapMeasEquiv_apply sampleCount swap sample
  rw [hswap]
  exact measurePreserving_finiteIIDPairSwap law sampleCount swap

end Probability
end AppliedModelingLib

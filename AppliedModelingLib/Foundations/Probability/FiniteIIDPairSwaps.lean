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

/-- A Boolean vector swaps exactly its selected coordinate pairs. -/
def finiteIIDPairSwap
    {Index Outcome : Type*} (swap : Index → Bool) :
    (Index → Outcome × Outcome) → Index → Outcome × Outcome :=
  fun sample index => if swap index then sample index else (sample index).swap

/-- The coordinatewise pair representation of two iid finite samples. -/
noncomputable def finiteIIDPairingMeasEquiv
    {Outcome : Type*} [MeasurableSpace Outcome] (sampleCount : ℕ) :
    (Fin sampleCount → Outcome × Outcome) ≃ᵐ
      (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome) :=
  MeasurableEquiv.arrowProdEquivProdArrow Outcome Outcome (Fin sampleCount)

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

end Probability
end AppliedModelingLib

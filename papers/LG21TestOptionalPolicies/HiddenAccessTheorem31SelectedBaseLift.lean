import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralCutoff

/-!
# Selected-base transport for LG21 Theorem 3.1

This is a measure-theoretic composition lemma only.  A selected action law
identifies conditional objects only where the selected fibre has positive
mass; once a source argument proves that condition almost everywhere, its
selected-base conclusion may be transported to the original base law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Transport an a.e. selected-base fact to the original base law when every
selected fibre has positive mass almost everywhere.  This does not assign a
conditional object at a zero-mass fibre. -/
theorem lg21_ae_base_of_ae_normalizedSelectedBase_of_ae_positiveFibres
    {Base Signal : Type*} [MeasurableSpace Base] [MeasurableSpace Signal]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (kernel : Kernel Base Signal) [IsMarkovKernel kernel]
    (event : Set (Base × Signal)) (hevent : MeasurableSet event)
    {P : Base -> Prop}
    (hselected : ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw kernel event,
      P publicBase)
    (hpositive : ∀ᵐ publicBase ∂baseLaw,
      selectionMass kernel event publicBase ≠ 0) :
    ∀ᵐ publicBase ∂baseLaw, P publicBase := by
  have hraw : ∀ᵐ publicBase ∂baseLaw,
      selectionMass kernel event publicBase ≠ 0 → P publicBase :=
    ae_normalizedSelectedBase_to_ae_positiveFibres hevent hselected
  filter_upwards [hraw, hpositive] with publicBase hrawAt hpositiveAt
  exact hrawAt hpositiveAt

end

end LG21TestOptionalPolicies

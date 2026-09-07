import PG24NoisyMatchingMarkets.Theorem4SourceModelAdapter

/-!
# PG24 Theorem 4 Canonical Source Sampling

This realizes the local coalition sampling law directly from a source student
law and iid coalition noise.  In particular, the eta-by-iid marginal is not a
separate theorem-sized premise for this canonical source presentation.
-/

open MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

namespace PG24CoalitionSourceSampling

/--
The local source outcome consists of one rich student state and the coalition's
iid noise vector.  Rich student states may retain all preference and
outside-market information relevant to the demand rule.
-/
def canonical
    (C : ℕ) (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {StudentType : Type u} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (commonValue : StudentType → ℝ) (hcommonValue : Measurable commonValue) :
    PG24CoalitionSourceSampling C noiseLaw (Measure.map commonValue studentLaw)
      StudentType (StudentType × (Fin (C + 1) → ℝ)) where
  studentLaw := studentLaw
  studentLaw_isProbability := inferInstance
  outcomeLaw := studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
  outcomeLaw_isProbability := by infer_instance
  commonValue := commonValue
  commonValue_measurable := hcommonValue
  commonValue_map := rfl
  sourceStudent := Prod.fst
  coalitionNoise := Prod.snd
  sourceCoordinates_measurable := by
    change Measurable (id :
      StudentType × (Fin (C + 1) → ℝ) → StudentType × (Fin (C + 1) → ℝ))
    exact measurable_id
  sourceCoordinates_map := by
    change Measure.map id
      (studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))) =
        studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
    exact Measure.map_id

/--
For the canonical construction, the local coordinate law is a derived source
fact with eta definitionally equal to the common-value marginal.
-/
theorem canonical_localCoordinates_map_eq_commonValue_prod_iid
    (C : ℕ) (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {StudentType : Type u} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (commonValue : StudentType → ℝ) (hcommonValue : Measurable commonValue) :
    Measure.map
        (canonical C noiseLaw studentLaw commonValue hcommonValue).localCoordinates
        (canonical C noiseLaw studentLaw commonValue hcommonValue).outcomeLaw =
      (Measure.map commonValue studentLaw).prod
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) := by
  exact localCoordinates_map_eq_eta_prod_iid
    (canonical C noiseLaw studentLaw commonValue hcommonValue)

end PG24CoalitionSourceSampling

end

end PG24NoisyMatchingMarkets

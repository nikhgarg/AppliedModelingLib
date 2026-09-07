import PG24NoisyMatchingMarkets.Theorem4StudentTypedSourceAdapter
import Mathlib.Tactic

/-!
# PG24 Theorem 4 True-Value Source Bridge

This module derives the coalition score relation used by the local theorem
from the extended source model's true-value-vector condition.  In particular,
the almost-everywhere equality on source student states is transferred through
the declared source-coordinate sampling law, rather than assumed again on
realized outcomes.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

namespace PG24CoalitionSourceSampling

variable {C : ℕ} {noiseLaw eta : Measure ℝ}
variable {StudentType : Type v} [MeasurableSpace StudentType]
variable {Outcome : Type u} [MeasurableSpace Outcome]

/--
The source's exceptional set of students whose true coalition values do not
all agree.  Its nullity is the literal formulation of the first coalition
condition in the extended paper model.
-/
def theorem4CoalitionTrueValueDisagreement
    {GlobalCollege : Type w}
    (trueValue : StudentType → GlobalCollege → ℝ)
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege) : Set StudentType :=
  {student | ∃ college other : Fin (C + 1),
    trueValue student (coalitionEmbedding college) ≠
      trueValue student (coalitionEmbedding other)}

/--
Choose a common-value representative from one coalition coordinate.  The
source null-disagreement condition then yields the equality to that
representative at every coalition college almost everywhere.
-/
theorem coalition_trueValue_ae_of_pairwise_disagreement_null
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
    {GlobalCollege : Type w}
    (trueValue : StudentType → GlobalCollege → ℝ)
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (reference : Fin (C + 1))
    (hcommonValue_reference :
      ∀ᵐ student ∂sampling.studentLaw,
        sampling.commonValue student =
          trueValue student (coalitionEmbedding reference))
    (hdisagreement_null :
      sampling.studentLaw
        (theorem4CoalitionTrueValueDisagreement trueValue coalitionEmbedding) = 0) :
    ∀ᵐ student ∂sampling.studentLaw,
      ∀ college : Fin (C + 1),
        trueValue student (coalitionEmbedding college) = sampling.commonValue student := by
  classical
  have hagreement : ∀ᵐ student ∂sampling.studentLaw,
      ∀ college other : Fin (C + 1),
        trueValue student (coalitionEmbedding college) =
          trueValue student (coalitionEmbedding other) := by
    rw [ae_iff]
    change sampling.studentLaw
      {student | ¬ ∀ college other : Fin (C + 1),
        trueValue student (coalitionEmbedding college) =
          trueValue student (coalitionEmbedding other)} = 0
    simpa [theorem4CoalitionTrueValueDisagreement] using hdisagreement_null
  filter_upwards [hcommonValue_reference, hagreement] with
    student hreference hagreement
  intro college
  calc
    trueValue student (coalitionEmbedding college) =
        trueValue student (coalitionEmbedding reference) :=
      hagreement college reference
    _ = sampling.commonValue student := hreference.symm

/--
An almost-everywhere property of source student states holds for the source
student coordinate of almost every realized outcome.

The transfer uses `sourceCoordinates_map`; it is not an additional outcome
regularity assumption.
-/
theorem sourceStudent_ae_of_student_ae
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
    {p : StudentType → Prop}
    (hstudent : ∀ᵐ student ∂sampling.studentLaw, p student) :
    ∀ᵐ outcome ∂sampling.outcomeLaw, p (sampling.sourceStudent outcome) := by
  have hproduct :
      ∀ᵐ source : StudentType × (Fin (C + 1) → ℝ) ∂
        sampling.studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)),
        p source.1 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := sampling.studentLaw)
      (ν := Measure.pi (fun _ : Fin (C + 1) => noiseLaw))).ae hstudent
  have hcoordinates :
      ∀ᵐ source : StudentType × (Fin (C + 1) → ℝ) ∂
        Measure.map
          (fun outcome : Outcome =>
            (sampling.sourceStudent outcome, sampling.coalitionNoise outcome))
          sampling.outcomeLaw,
        p source.1 := by
    rw [sampling.sourceCoordinates_map]
    exact hproduct
  exact ae_of_ae_map sampling.sourceCoordinates_measurable.aemeasurable hcoordinates

/--
The paper's source-level true-value condition and source-score equation imply
the local coalition score relation.  The common-value equality is lifted from
`studentLaw` through the source-coordinate law.
-/
theorem coalition_score_ae_of_trueValue
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
    {GlobalCollege : Type w}
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (trueValue : StudentType → GlobalCollege → ℝ)
    (approximateScore : Outcome → GlobalCollege → ℝ)
    (hcoalition_trueValue :
      ∀ᵐ student ∂sampling.studentLaw,
        ∀ college : Fin (C + 1),
          trueValue student (coalitionEmbedding college) = sampling.commonValue student)
    (hscore_trueValue :
      ∀ᵐ outcome ∂sampling.outcomeLaw,
        ∀ college : Fin (C + 1),
          approximateScore outcome (coalitionEmbedding college) =
            trueValue (sampling.sourceStudent outcome) (coalitionEmbedding college) +
              sampling.coalitionNoise outcome college) :
    ∀ᵐ outcome ∂sampling.outcomeLaw,
      ∀ college : Fin (C + 1),
        approximateScore outcome (coalitionEmbedding college) =
          (sampling.localCoordinates outcome).1 +
            (sampling.localCoordinates outcome).2 college := by
  filter_upwards [sampling.sourceStudent_ae_of_student_ae hcoalition_trueValue,
    hscore_trueValue] with outcome htrueValue hscore
  intro college
  calc
    approximateScore outcome (coalitionEmbedding college) =
        trueValue (sampling.sourceStudent outcome) (coalitionEmbedding college) +
          sampling.coalitionNoise outcome college := hscore college
    _ = sampling.commonValue (sampling.sourceStudent outcome) +
          sampling.coalitionNoise outcome college := by rw [htrueValue college]
    _ = (sampling.localCoordinates outcome).1 +
          (sampling.localCoordinates outcome).2 college := rfl

/--
The source's pairwise null-disagreement condition can be used directly in the
true-value score bridge after choosing a measurable common-value
representative.
-/
theorem coalition_score_ae_of_trueValue_pairwise
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
    {GlobalCollege : Type w}
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (trueValue : StudentType → GlobalCollege → ℝ)
    (approximateScore : Outcome → GlobalCollege → ℝ)
    (reference : Fin (C + 1))
    (hcommonValue_reference :
      ∀ᵐ student ∂sampling.studentLaw,
        sampling.commonValue student =
          trueValue student (coalitionEmbedding reference))
    (hdisagreement_null :
      sampling.studentLaw
        (theorem4CoalitionTrueValueDisagreement trueValue coalitionEmbedding) = 0)
    (hscore_trueValue :
      ∀ᵐ outcome ∂sampling.outcomeLaw,
        ∀ college : Fin (C + 1),
          approximateScore outcome (coalitionEmbedding college) =
            trueValue (sampling.sourceStudent outcome) (coalitionEmbedding college) +
              sampling.coalitionNoise outcome college) :
    ∀ᵐ outcome ∂sampling.outcomeLaw,
      ∀ college : Fin (C + 1),
        approximateScore outcome (coalitionEmbedding college) =
          (sampling.localCoordinates outcome).1 +
            (sampling.localCoordinates outcome).2 college :=
  sampling.coalition_score_ae_of_trueValue coalitionEmbedding trueValue
    approximateScore
    (sampling.coalition_trueValue_ae_of_pairwise_disagreement_null
      trueValue coalitionEmbedding reference hcommonValue_reference
      hdisagreement_null)
    hscore_trueValue

end PG24CoalitionSourceSampling

namespace PG24StudentTypedSourceStableData

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Outcome : Type v} [MeasurableSpace Outcome]
variable {GlobalCollege : Type w} [Fintype GlobalCollege]
variable {Cutoff : Type x}

/--
Construct student-typed source data from the extended source model's true
values.  Preferences remain a function of `StudentType`; `coalition_score_ae`
is derived rather than supplied as an outcome-level premise.
-/
noncomputable def ofTrueValueSource
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
    (rankOfStudent : StudentType → GlobalCollege → ℕ)
    (rankOfStudent_injective :
      ∀ student : StudentType, Function.Injective (rankOfStudent student))
    (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
    (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
    (singletonDemandMeasurable :
      ∀ P : Cutoff, ∀ college : GlobalCollege,
        MeasurableSet
          {outcome : Outcome |
            theorem4DemandFromPreferences
                (fun outcome college =>
                  rankOfStudent (sampling.sourceStudent outcome) college)
                cutoffCoordinates globalScore P outcome = some college})
    (capacity : GlobalCollege → ℝ)
    (totalCapacity_eq : (∑ college : GlobalCollege, capacity college) = totalSupply)
    (selectedCutoff : Cutoff)
    (selectedCutoff_clearing :
      ∀ college : GlobalCollege,
        eventMass sampling.outcomeLaw
          (fun outcome =>
            theorem4DemandFromPreferences
                (fun outcome college =>
                  rankOfStudent (sampling.sourceStudent outcome) college)
                cutoffCoordinates globalScore selectedCutoff outcome = some college) =
          capacity college)
    (approximateScore : Outcome → GlobalCollege → ℝ)
    (globalScore_eq_approximateScore :
      ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
        globalScore P outcome college = approximateScore outcome college)
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (trueValue : StudentType → GlobalCollege → ℝ)
    (hcoalition_trueValue :
      ∀ᵐ student ∂sampling.studentLaw,
        ∀ college : Fin (C + 1),
          trueValue student (coalitionEmbedding college) = sampling.commonValue student)
    (hscore_trueValue :
      ∀ᵐ outcome ∂sampling.outcomeLaw,
        ∀ college : Fin (C + 1),
          approximateScore outcome (coalitionEmbedding college) =
            trueValue (sampling.sourceStudent outcome) (coalitionEmbedding college) +
              sampling.coalitionNoise outcome college) :
    PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
      StudentType Outcome GlobalCollege Cutoff where
  sampling := sampling
  rankOfStudent := rankOfStudent
  rankOfStudent_injective := rankOfStudent_injective
  cutoffCoordinates := cutoffCoordinates
  globalScore := globalScore
  singletonDemandMeasurable := singletonDemandMeasurable
  capacity := capacity
  totalCapacity_eq := totalCapacity_eq
  selectedCutoff := selectedCutoff
  selectedCutoff_clearing := selectedCutoff_clearing
  approximateScore := approximateScore
  globalScore_eq_approximateScore := globalScore_eq_approximateScore
  coalitionEmbedding := coalitionEmbedding
  coalition_score_ae :=
    sampling.coalition_score_ae_of_trueValue coalitionEmbedding trueValue
      approximateScore hcoalition_trueValue hscore_trueValue

end PG24StudentTypedSourceStableData

/--
One literal extended-model economy at a selected clearing cutoff.

This is a source-facing bundle, not a conclusion certificate: its fields are
exactly the extended-model primitives used in the paper.  In particular,
preferences are functions of the rich source-student state; coalition true
values agree almost everywhere; and the coalition score is true value plus
iid noise.  Bundling these inputs keeps Theorems 3 and 4 reviewable without
changing their quantifier order or replacing any hypothesis by a result.
-/
structure PG24TrueValueSourceStableData
    (C : ℕ) (noiseLaw eta : Measure ℝ) (totalSupply : ℝ)
    (StudentType : Type u) [MeasurableSpace StudentType]
    (Outcome : Type v) [MeasurableSpace Outcome]
    (GlobalCollege : Type w) [Fintype GlobalCollege]
    (Cutoff : Type x) where
  sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome
  rankOfStudent : StudentType → GlobalCollege → ℕ
  rankOfStudent_injective :
    ∀ student : StudentType, Function.Injective (rankOfStudent student)
  cutoffCoordinates : Cutoff → GlobalCollege → ℝ
  globalScore : Cutoff → Outcome → GlobalCollege → ℝ
  singletonDemandMeasurable :
    ∀ P : Cutoff, ∀ college : GlobalCollege,
      MeasurableSet
        {outcome : Outcome |
          theorem4DemandFromPreferences
              (fun outcome college =>
                rankOfStudent (sampling.sourceStudent outcome) college)
              cutoffCoordinates globalScore P outcome = some college}
  capacity : GlobalCollege → ℝ
  totalCapacity_eq : (∑ college : GlobalCollege, capacity college) = totalSupply
  selectedCutoff : Cutoff
  selectedCutoff_clearing :
    ∀ college : GlobalCollege,
      eventMass sampling.outcomeLaw
        (fun outcome =>
          theorem4DemandFromPreferences
              (fun outcome college =>
                rankOfStudent (sampling.sourceStudent outcome) college)
              cutoffCoordinates globalScore selectedCutoff outcome = some college) =
        capacity college
  approximateScore : Outcome → GlobalCollege → ℝ
  globalScore_eq_approximateScore :
    ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
      globalScore P outcome college = approximateScore outcome college
  coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege
  trueValue : StudentType → GlobalCollege → ℝ
  coalition_trueValue_ae :
    ∀ᵐ student ∂sampling.studentLaw,
      ∀ college : Fin (C + 1),
        trueValue student (coalitionEmbedding college) = sampling.commonValue student
  score_eq_trueValue_plus_noise_ae :
    ∀ᵐ outcome ∂sampling.outcomeLaw,
      ∀ college : Fin (C + 1),
        approximateScore outcome (coalitionEmbedding college) =
          trueValue (sampling.sourceStudent outcome) (coalitionEmbedding college) +
            sampling.coalitionNoise outcome college

namespace PG24TrueValueSourceStableData

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Outcome : Type v} [MeasurableSpace Outcome]
variable {GlobalCollege : Type w} [Fintype GlobalCollege]
variable {Cutoff : Type x}

/-- The local analytic data derived from the literal extended-model primitives. -/
noncomputable def toStudentTypedSourceStableData
    (data : PG24TrueValueSourceStableData C noiseLaw eta totalSupply
      StudentType Outcome GlobalCollege Cutoff) :
    PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
      StudentType Outcome GlobalCollege Cutoff :=
  PG24StudentTypedSourceStableData.ofTrueValueSource
    data.sampling data.rankOfStudent data.rankOfStudent_injective
    data.cutoffCoordinates data.globalScore data.singletonDemandMeasurable
    data.capacity data.totalCapacity_eq data.selectedCutoff
    data.selectedCutoff_clearing data.approximateScore
    data.globalScore_eq_approximateScore data.coalitionEmbedding data.trueValue
    data.coalition_trueValue_ae data.score_eq_trueValue_plus_noise_ae

end PG24TrueValueSourceStableData

end

end PG24NoisyMatchingMarkets

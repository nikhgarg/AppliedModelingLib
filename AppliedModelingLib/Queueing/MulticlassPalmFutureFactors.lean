import AppliedModelingLib.Queueing.MulticlassPalmInput
import AppliedModelingLib.Foundations.Probability.FiniteProductCoordinateFactors
import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureInputFactors
import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureIidSection
import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureTimeSliceSection
import Mathlib.Tactic

/-!
# Future IID factors in a multiclass Palm input

This module isolates the future marked renewal input of one passive class in
a finite multiclass Palm configuration.  Every other passive class, the
selected Palm path, and the isolated class's past/origin data remain in the
external state.  No queue response or stopping property is asserted here.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance multiclassPalmFutureFactorsDecidableEq : DecidableEq Class := Classical.decEq Class

/-- The passive classes other than one distinguished passive coordinate. -/
abbrev passiveClassComplement (i : Class) (j : {k : Class // k ≠ i}) :=
  {k : {l : Class // l ≠ i} // k ≠ j}

/-- The selected-Palm data independent of one passive class's future IID
arrival-gap/work stream. -/
abbrev MulticlassPalmFutureExternalCarrier
    (i : Class) (j : {k : Class // k ≠ i}) :=
  ((ℤ → ℝ) × (ℤ → ℝ)) ×
    ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
      (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))

/-- The full factor carrier obtained by exposing the future IID
arrival-gap/work stream of one passive class. -/
abbrev MulticlassPalmFutureFactorCarrier
    (i : Class) (j : {k : Class // k ≠ i}) :=
  MulticlassPalmFutureExternalCarrier i j × (ℕ → (ℝ × ℝ))

/-- Factor the future of one passive class into IID marked renewal coordinates,
retaining all other passive class paths and its own past/origin data. -/
def passiveStationaryPoissonWorkFutureFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    ({k : Class // k ≠ i} → StationaryPoissonWorkPath) →
      ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
        (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → (ℝ × ℝ)) :=
  fun omega =>
    Probability.Queueing.stateStationaryPoissonWorkFutureExternalIidFactors
      (piWithoutCoordinate (α := StationaryPoissonWorkPath) j omega)

theorem measurable_passiveStationaryPoissonWorkFutureFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measurable (passiveStationaryPoissonWorkFutureFactor i j) := by
  exact Probability.Queueing.measurable_stateStationaryPoissonWorkFutureExternalIidFactors.comp
    (measurable_piWithoutCoordinate (α := StationaryPoissonWorkPath) j)

/-- The finite independent passive-class product factors into an external
state and the literal IID future `(gap, work)` stream of class `j`. -/
theorem map_passiveStationaryPoissonWorkFutureFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measure.map (passiveStationaryPoissonWorkFutureFactor i j)
      (Measure.pi fun k : {k : Class // k ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)) =
      ((Measure.pi fun k : passiveClassComplement i j =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
        (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
          (ProbabilityTheory.expMeasure (1 : ℝ))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (IIDStream.measure
          ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ)))) := by
  let μ : {k : Class // k ≠ i} → Measure StationaryPoissonWorkPath := fun k =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate k.1.1)
  letI : ∀ k : {k : Class // k ≠ i}, IsProbabilityMeasure (μ k) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  change Measure.map (passiveStationaryPoissonWorkFutureFactor i j) (Measure.pi μ) = _
  calc
    Measure.map (passiveStationaryPoissonWorkFutureFactor i j) (Measure.pi μ) =
        Measure.map
          (Probability.Queueing.stateStationaryPoissonWorkFutureExternalIidFactors
            (σ := passiveClassComplement i j → StationaryPoissonWorkPath))
          (Measure.map (piWithoutCoordinate (α := StationaryPoissonWorkPath) j)
            (Measure.pi μ)) := by
          symm
          rw [Measure.map_map
            Probability.Queueing.measurable_stateStationaryPoissonWorkFutureExternalIidFactors
            (measurable_piWithoutCoordinate (α := StationaryPoissonWorkPath) j)]
          rfl
    _ = Measure.map
          (Probability.Queueing.stateStationaryPoissonWorkFutureExternalIidFactors
            (σ := passiveClassComplement i j → StationaryPoissonWorkPath))
          (ρ.prod (Probability.Queueing.stationaryPoissonWorkMeasure
            (arrivalRate j.1))) := by
          congr 1
          simpa [μ, ρ] using (map_piWithoutCoordinate μ j)
    _ =
        (ρ.prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (IIDStream.measure
            ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ)))) := by
          rw [Probability.Queueing.map_stateStationaryPoissonWorkFutureExternalIidFactors
            ρ (harrivalRate j.1)]
    _ =
        ((Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (IIDStream.measure
            ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ)))) := by rfl

/-- The passive-class factor is measure preserving onto its explicit
external-state/IID-product law. -/
theorem passiveStationaryPoissonWorkFutureFactor_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (passiveStationaryPoissonWorkFutureFactor i j)
      (Measure.pi fun k : {k : Class // k ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1))
      (
        ((Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (IIDStream.measure
            ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ))))
      ) := by
  exact ⟨measurable_passiveStationaryPoissonWorkFutureFactor i j,
    map_passiveStationaryPoissonWorkFutureFactor arrivalRate harrivalRate i j⟩

/-- Factor one passive class so that all arrival timing remains external and
only its future work-mark sequence is IID. -/
def passiveStationaryPoissonWorkFutureMarkFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    ({k : Class // k ≠ i} → StationaryPoissonWorkPath) →
      (((passiveClassComplement i j → StationaryPoissonWorkPath) ×
        (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → ℝ)) × (ℕ → ℝ) :=
  fun omega =>
    Probability.Queueing.stateStationaryPoissonWorkFutureExternalMarkFactors
      (piWithoutCoordinate (α := StationaryPoissonWorkPath) j omega)

theorem measurable_passiveStationaryPoissonWorkFutureMarkFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measurable (passiveStationaryPoissonWorkFutureMarkFactor i j) := by
  exact Probability.Queueing.measurable_stateStationaryPoissonWorkFutureExternalMarkFactors.comp
    (measurable_piWithoutCoordinate (α := StationaryPoissonWorkPath) j)

/-- The finite independent passive-class product factors into all timing and
an IID future work-mark sequence of the selected passive class. -/
theorem map_passiveStationaryPoissonWorkFutureMarkFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measure.map (passiveStationaryPoissonWorkFutureMarkFactor i j)
      (Measure.pi fun k : {k : Class // k ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)) =
      (((Measure.pi fun k : passiveClassComplement i j =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
        (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
          (ProbabilityTheory.expMeasure (1 : ℝ))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) := by
  let μ : {k : Class // k ≠ i} → Measure StationaryPoissonWorkPath := fun k =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate k.1.1)
  letI : ∀ k : {k : Class // k ≠ i}, IsProbabilityMeasure (μ k) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  change Measure.map (passiveStationaryPoissonWorkFutureMarkFactor i j)
    (Measure.pi μ) = _
  calc
    Measure.map (passiveStationaryPoissonWorkFutureMarkFactor i j) (Measure.pi μ) =
        Measure.map
          (Probability.Queueing.stateStationaryPoissonWorkFutureExternalMarkFactors
            (σ := passiveClassComplement i j → StationaryPoissonWorkPath))
          (Measure.map (piWithoutCoordinate (α := StationaryPoissonWorkPath) j)
            (Measure.pi μ)) := by
          symm
          rw [Measure.map_map
            Probability.Queueing.measurable_stateStationaryPoissonWorkFutureExternalMarkFactors
            (measurable_piWithoutCoordinate (α := StationaryPoissonWorkPath) j)]
          rfl
    _ = Measure.map
          (Probability.Queueing.stateStationaryPoissonWorkFutureExternalMarkFactors
            (σ := passiveClassComplement i j → StationaryPoissonWorkPath))
          (ρ.prod (Probability.Queueing.stationaryPoissonWorkMeasure
            (arrivalRate j.1))) := by
          congr 1
          simpa [μ, ρ] using (map_piWithoutCoordinate μ j)
    _ =
        ((ρ.prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) := by
          rw [Probability.Queueing.map_stateStationaryPoissonWorkFutureExternalMarkFactors
            ρ (harrivalRate j.1)]
    _ =
        (((Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) := by rfl

/-- The passive external-timing/future-mark factor is measure preserving. -/
theorem passiveStationaryPoissonWorkFutureMarkFactor_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (passiveStationaryPoissonWorkFutureMarkFactor i j)
      (Measure.pi fun k : {k : Class // k ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1))
      ((((Measure.pi fun k : passiveClassComplement i j =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
        (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
          (ProbabilityTheory.expMeasure (1 : ℝ))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  exact ⟨measurable_passiveStationaryPoissonWorkFutureMarkFactor i j,
    map_passiveStationaryPoissonWorkFutureMarkFactor arrivalRate harrivalRate i j⟩

/-- Factor the full selected-arrival carrier so that a passive class's full
arrival timing is external and its future service marks form the IID stream. -/
def multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      ((((ℤ → ℝ) × (ℤ → ℝ)) ×
        ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
          (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) × (ℕ → ℝ)) × (ℕ → ℝ) :=
  fun z =>
    let q := passiveStationaryPoissonWorkFutureMarkFactor i j z.2
    (((z.1, q.1.1), q.1.2), q.2)

theorem measurable_multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor i j) := by
  have hq : Measurable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
        passiveStationaryPoissonWorkFutureMarkFactor i j z.2) :=
    (measurable_passiveStationaryPoissonWorkFutureMarkFactor i j).comp
      (measurable_snd : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample Class i => z.2))
  have hq11 : Measurable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
        (passiveStationaryPoissonWorkFutureMarkFactor i j z.2).1.1) :=
    measurable_fst.comp (measurable_fst.comp hq)
  have hq12 : Measurable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
        (passiveStationaryPoissonWorkFutureMarkFactor i j z.2).1.2) :=
    measurable_snd.comp (measurable_fst.comp hq)
  have hq2 : Measurable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
        (passiveStationaryPoissonWorkFutureMarkFactor i j z.2).2) :=
    measurable_snd.comp hq
  exact ((measurable_fst.prodMk hq11).prodMk hq12).prodMk hq2

/-- Under the selected-arrival Palm law, every passive class has an exact
factorization into all nonfuture data, its full future timing path, and its
IID future work marks. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ((((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
        ((Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let passiveFactor := passiveStationaryPoissonWorkFutureMarkFactor i j
  let E : Measure (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) :=
    ((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
      (ProbabilityTheory.expMeasure (1 : ℝ))).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let A : Measure ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
      (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) :=
    (Measure.pi fun k : passiveClassComplement i j =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod E
  let G : Measure (ℕ → ℝ) :=
    Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)
  let M : Measure (ℕ → ℝ) :=
    Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (harrivalRate j.1)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure G := by
    dsimp [G]
    infer_instance
  letI : IsProbabilityMeasure M := by
    dsimp [M]
    infer_instance
  let TType : Type _ := (ℤ → ℝ) × (ℤ → ℝ)
  let AType : Type _ := (passiveClassComplement i j → StationaryPoissonWorkPath) ×
    (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))
  let Stream : Type _ := ℕ → ℝ
  let reassociate : TType × ((AType × Stream) × Stream) →
      ((TType × AType) × Stream) × Stream :=
    fun y => (((y.1, y.2.1.1), y.2.1.2), y.2.2)
  have hpassive : Measure.map passiveFactor passive.Pbase = (A.prod G).prod M := by
    change Measure.map passiveFactor passive.Pbase = (A.prod G).prod M
    simpa [passiveFactor, passive, multiclassStationaryPoissonWorkRestLaw,
      A, E, G, M] using
      (map_passiveStationaryPoissonWorkFutureMarkFactor arrivalRate harrivalRate i j)
  have hproduct :
      Measure.map (Prod.map id passiveFactor) (tagged.Ptag.prod passive.Pbase) =
        tagged.Ptag.prod ((A.prod G).prod M) := by
    rw [← Measure.map_prod_map _ _ measurable_id
      (measurable_passiveStationaryPoissonWorkFutureMarkFactor i j), Measure.map_id,
      hpassive]
  have hreassociate : MeasurePreserving reassociate
      (tagged.Ptag.prod ((A.prod G).prod M))
      (((tagged.Ptag.prod A).prod G).prod M) := by
    let h₁ := (measurePreserving_prodAssoc tagged.Ptag (A.prod G) M).symm
    let h₂ := ((measurePreserving_prodAssoc tagged.Ptag A G).symm).prod
      (MeasurePreserving.id M)
    convert h₂.comp h₁ using 1
  change Measure.map (reassociate ∘ Prod.map id passiveFactor)
    (tagged.Ptag.prod passive.Pbase) = ((tagged.Ptag.prod A).prod G).prod M
  calc
    Measure.map (reassociate ∘ Prod.map id passiveFactor)
        (tagged.Ptag.prod passive.Pbase) =
        Measure.map reassociate
          (Measure.map (Prod.map id passiveFactor)
            (tagged.Ptag.prod passive.Pbase)) := by
            symm
            rw [Measure.map_map hreassociate.measurable
              (measurable_id.prodMap
                (measurable_passiveStationaryPoissonWorkFutureMarkFactor i j))]
    _ = Measure.map reassociate (tagged.Ptag.prod ((A.prod G).prod M)) := by
          rw [hproduct]
    _ = ((tagged.Ptag.prod A).prod G).prod M := hreassociate.map_eq
    _ =
        (((((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
          ((Measure.pi fun k : passiveClassComplement i j =>
            Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
            (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ))).prod
              (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by rfl

/-- The full external-timing/future-mark factor is measure preserving. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      (((((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
        ((Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  exact ⟨measurable_multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor i j,
    map_multiclassStationaryPoissonWorkClassTaggedFutureMarkFactor
      arrivalRate harrivalRate i j⟩

/-- Factor the full selected-arrival carrier at one passive class, retaining
the selected Palm path and all nonfuture input as external data. -/
def multiclassStationaryPoissonWorkClassTaggedFutureFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
        ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
          (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) × (ℕ → (ℝ × ℝ)) :=
  fun z =>
    let q := passiveStationaryPoissonWorkFutureFactor i j z.2
    ((z.1, q.1), q.2)

/-- The full future-pair factor of a literal selected-Palm input retains a
valid equilibrium reconstruction of the isolated passive arrival path. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureFactor_mem_good
    (i : Class) (j : {k : Class // k ≠ i})
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ
        (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j z).2).1,
        (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j z).1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
  simp [multiclassStationaryPoissonWorkClassTaggedFutureFactor,
    passiveStationaryPoissonWorkFutureFactor,
    Probability.Queueing.stateStationaryPoissonWorkFutureExternalIidFactors,
    Probability.Queueing.stationaryPoissonWorkFutureExternalIidFactors,
    Probability.Queueing.equilibriumFutureExternalIidFactors,
    Probability.Queueing.stationaryPoissonWorkToEquilibrium,
    Probability.Queueing.equilibriumFutureExternalFactors,
    Probability.PoissonProcess.equilibriumToSuspension_apply_suspensionToEquilibrium,
    MeasurableEquiv.arrowProdEquivProdArrow, Probability.IIDStream.zip]

theorem measurable_multiclassStationaryPoissonWorkClassTaggedFutureFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j) := by
  exact MeasurableEquiv.prodAssoc.symm.measurable.comp
    (measurable_id.prodMap (measurable_passiveStationaryPoissonWorkFutureFactor i j))

/-- Under the concrete selected-arrival Palm law, the future marked renewal
input of every passive class is IID independently of the complete selected
path and all complementary passive data. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedFutureFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
        ((Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
          (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ))).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))).prod
        (IIDStream.measure
          ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
            (ProbabilityTheory.expMeasure (1 : ℝ)))) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let passiveFactor := passiveStationaryPoissonWorkFutureFactor i j
  let external : Measure
      ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
        (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) :=
    (Measure.pi fun k : passiveClassComplement i j =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
      (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
        (ProbabilityTheory.expMeasure (1 : ℝ))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))
  let future : Measure (ℕ → (ℝ × ℝ)) :=
    IIDStream.measure ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
      (ProbabilityTheory.expMeasure (1 : ℝ)))
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (arrivalRate j.1)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (harrivalRate j.1)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (harrivalRate j.1)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : IsProbabilityMeasure external := by
    dsimp [external]
    infer_instance
  letI : IsProbabilityMeasure future := by
    dsimp [future, IIDStream.measure]
    infer_instance
  change Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j)
    (tagged.Ptag.prod passive.Pbase) = _
  calc
    Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j)
        (tagged.Ptag.prod passive.Pbase) =
        Measure.map (MeasurableEquiv.prodAssoc.symm :
          ((ℤ → ℝ) × (ℤ → ℝ)) ×
              ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
                (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → (ℝ × ℝ)) →
            (((ℤ → ℝ) × (ℤ → ℝ)) ×
              ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
                (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) × (ℕ → (ℝ × ℝ)))
          (Measure.map (Prod.map id passiveFactor) (tagged.Ptag.prod passive.Pbase)) := by
          symm
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            (measurable_id.prodMap (measurable_passiveStationaryPoissonWorkFutureFactor i j))]
          rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm :
          ((ℤ → ℝ) × (ℤ → ℝ)) ×
              ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
                (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → (ℝ × ℝ)) →
            (((ℤ → ℝ) × (ℤ → ℝ)) ×
              ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
                (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) × (ℕ → (ℝ × ℝ)))
          (tagged.Ptag.prod (external.prod future)) := by
          rw [← Measure.map_prod_map _ _ measurable_id
            (measurable_passiveStationaryPoissonWorkFutureFactor i j),
            Measure.map_id]
          have hpassive : Measure.map passiveFactor passive.Pbase = external.prod future := by
            change Measure.map passiveFactor passive.Pbase = external.prod future
            simpa [passiveFactor, passive, multiclassStationaryPoissonWorkRestLaw,
              external, future] using
              (map_passiveStationaryPoissonWorkFutureFactor arrivalRate harrivalRate i j)
          rw [hpassive]
    _ = (tagged.Ptag.prod external).prod future := by
          exact (measurePreserving_prodAssoc tagged.Ptag external future).symm.map_eq
    _ =
        (((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
          ((Measure.pi fun k : passiveClassComplement i j =>
            Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
            (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ))).prod
              (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))).prod
          (IIDStream.measure
            ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ)))) := by rfl

/-- The selected-arrival factor map is measure preserving onto the explicit
external-state/IID-product carrier. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureFactor_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      (
        (((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
          ((Measure.pi fun k : passiveClassComplement i j =>
            Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
            (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ))).prod
              (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))).prod
          (IIDStream.measure
            ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ))))
      ) := by
  exact ⟨measurable_multiclassStationaryPoissonWorkClassTaggedFutureFactor i j,
    map_multiclassStationaryPoissonWorkClassTaggedFutureFactor arrivalRate harrivalRate i j⟩

/-- Reconstruct a full selected-Palm multiclass input from the external data
and future IID arrival-gap/work stream of one passive class. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    (((ℤ → ℝ) × (ℤ → ℝ)) ×
        ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
          (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) ×
      (ℕ → (ℝ × ℝ)) →
      MulticlassStationaryPoissonWorkClassTaggedSample Class i :=
  fun x =>
    let passive := Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
      (arrivalRate j.1) (harrivalRate j.1) (x.1.2.2, x.2)
    let rest := (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      (x.1.2.1, passive)
    (x.1.1, rest)

/-- The multiclass full-future reconstruction section is Borel measurable. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j) := by
  let input :
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
          ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
            (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) ×
        (ℕ → (ℝ × ℝ)) →
        (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → (ℝ × ℝ)) :=
    fun x => (x.1.2.2, x.2)
  have hinput : Measurable input :=
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  let passive :
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
          ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
            (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) ×
        (ℕ → (ℝ × ℝ)) → StationaryPoissonWorkPath :=
    Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
      (arrivalRate j.1) (harrivalRate j.1) ∘ input
  have hpassive : Measurable passive :=
    (Probability.Queueing.measurable_stationaryPoissonWorkFromFutureExternalIidFactors
      (arrivalRate j.1) (harrivalRate j.1)).comp hinput
  let rest :
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
          ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
            (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)))) ×
        (ℕ → (ℝ × ℝ)) →
        ({k : Class // k ≠ i} → StationaryPoissonWorkPath) :=
    (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm ∘
      fun x => (x.1.2.1, passive x)
  have hrest : Measurable rest :=
    (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm.measurable.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hpassive)
  exact (measurable_fst.comp measurable_fst).prodMk hrest

/-- Reconstructing the full future factor of a literal selected-Palm input
returns that input exactly. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_apply_factors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j
      (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j z) = z := by
  rcases z with ⟨selected, paths⟩
  have hpassive : Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
      (arrivalRate j.1) (harrivalRate j.1)
      (Probability.Queueing.stationaryPoissonWorkFutureExternalIidFactors (paths j)) = paths j :=
    Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors_apply_factors
      (arrivalRate j.1) (harrivalRate j.1) (paths j)
  apply Prod.ext
  · rfl
  · change (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
        Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
          (arrivalRate j.1) (harrivalRate j.1)
          (Probability.Queueing.stationaryPoissonWorkFutureExternalIidFactors
            ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2))) = paths
    rw [show (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2 = paths j by rfl,
      hpassive]
    exact MeasurableEquiv.symm_apply_apply (piWithoutCoordinateEquiv
      (α := StationaryPoissonWorkPath) j) paths

/-- The selected Palm path is retained entirely in the external component of
a full future-pair factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_selected_eq_of_fst_eq
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j) (hfst : x.1 = y.1) :
    (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j x).1 =
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j y).1 := by
  rcases x with ⟨external, stream⟩
  rcases y with ⟨otherExternal, otherStream⟩
  change external = otherExternal at hfst
  subst otherExternal
  rfl

/-- Every passive path other than the isolated future-pair coordinate is
retained entirely in the external component of a full factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_otherPassive_eq_of_fst_eq
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j)
    (k : {l : Class // l ≠ i}) (hkj : k ≠ j) (hfst : x.1 = y.1) :
    (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j x).2 k =
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j y).2 k := by
  rcases x with ⟨external, stream⟩
  rcases y with ⟨otherExternal, otherStream⟩
  change external = otherExternal at hfst
  subst otherExternal
  unfold multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
  dsimp only
  rw [piWithoutCoordinateEquiv_symm_apply_of_ne j _ k hkj,
    piWithoutCoordinateEquiv_symm_apply_of_ne j _ k hkj]

/-- Every arrival coordinate outside the isolated passive class is fixed by
the external part of a full future-pair factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_fst_eq_of_ne
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j)
    (k : Class) (m : ℤ) (hkj : k ≠ j.1) (hfst : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) k m =
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j y) k m := by
  by_cases hki : k = i
  · subst k
    unfold multiclassStationaryPoissonWorkClassTaggedArrival
    rw [dif_pos rfl, dif_pos rfl,
      multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_selected_eq_of_fst_eq
        arrivalRate harrivalRate i j x y hfst]
  · rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne i k hki,
      multiclassStationaryPoissonWorkClassTaggedArrival_of_ne i k hki]
    have hsub : (⟨k, hki⟩ : {l : Class // l ≠ i}) ≠ j := by
      intro h
      exact hkj (congrArg Subtype.val h)
    rw [multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_otherPassive_eq_of_fst_eq
      arrivalRate harrivalRate i j x y ⟨k, hki⟩ hsub hfst]

/-- Every work-mark coordinate outside the isolated passive class is fixed by
the external part of a full future-pair factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_eq_of_fst_eq_of_ne
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j)
    (k : Class) (m : ℤ) (hkj : k ≠ j.1) (hfst : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) k m =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j y) k m := by
  by_cases hki : k = i
  · subst k
    unfold multiclassStationaryPoissonWorkClassTaggedRequirementAt
    rw [dif_pos rfl, dif_pos rfl,
      multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_selected_eq_of_fst_eq
        arrivalRate harrivalRate i j x y hfst]
  · rw [multiclassStationaryPoissonWorkClassTaggedRequirementAt_of_ne i k hki,
      multiclassStationaryPoissonWorkClassTaggedRequirementAt_of_ne i k hki]
    have hsub : (⟨k, hki⟩ : {l : Class // l ≠ i}) ≠ j := by
      intro h
      exact hkj (congrArg Subtype.val h)
    rw [multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_otherPassive_eq_of_fst_eq
      arrivalRate harrivalRate i j x y ⟨k, hki⟩ hsub hfst]

/-- In a valid full-future reconstruction, the positive labels of the isolated
passive class occur at the renewal sums of its exposed IID gap coordinates. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_ofNat_succ
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (factors : MulticlassPalmFutureFactorCarrier i j) (n : ℕ)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ factors.2).1,
        factors.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1}) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j factors)
      j.1 (Int.ofNat (n + 1)) =
        Probability.PoissonProcess.arrivalTime n (fun r => (factors.2 r).1) := by
  unfold multiclassStationaryPoissonWorkClassTaggedArrival
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
  rw [dif_neg j.property]
  dsimp only
  rw [piWithoutCoordinateEquiv_symm_apply_self]
  change Probability.Queueing.stationaryPoissonWorkArrival
      (Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
        (arrivalRate j.1) (harrivalRate j.1) (factors.1.2.2, factors.2))
      (Int.ofNat (n + 1)) = _
  exact Probability.Queueing.stationaryPoissonWorkArrival_fromFutureExternalIidFactors_ofNat_succ
    (arrivalRate j.1) (harrivalRate j.1) factors.1.2.2 factors.2 n hgood

/-- On a good full future-pair factor, only a finite prefix of isolated
positive labels can arrive before any deterministic clock. -/
theorem exists_multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_prefix_bound
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (factors : MulticlassPalmFutureFactorCarrier i j) (t : ℝ)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ factors.2).1,
        factors.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1}) :
    ∃ N : ℕ, ∀ r,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j factors) j.1 (Int.ofNat (r + 1)) < t →
        r < N := by
  let future := (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ factors.2).1
  have hfuturePos : ∀ n, 0 < future n := by
    simpa [future] using
      (Probability.PoissonProcess.equilibriumToSuspension_future_pos_of_mem_good
        future factors.1.2.2.1.1 hgood)
  have hfuture : Filter.Tendsto (fun n : ℕ =>
      Probability.PoissonProcess.arrivalTime n future) Filter.atTop Filter.atTop := by
    simpa [future] using
      (Probability.PoissonProcess.tendsto_arrivalTime_equilibriumToSuspension_future_of_mem_good
        future factors.1.2.2.1.1 hgood)
  obtain ⟨N, hN⟩ := Probability.PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop
    future hfuture t
  refine ⟨N, ?_⟩
  intro r hr
  by_contra hnot
  have hNr : N ≤ r := Nat.le_of_not_gt hnot
  have hmono : Probability.PoissonProcess.arrivalTime N future ≤
      Probability.PoissonProcess.arrivalTime r future :=
    (Probability.PoissonProcess.arrivalTime_strictMono_of_positive future hfuturePos).monotone hNr
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_ofNat_succ
    arrivalRate harrivalRate i j factors r hgood] at hr
  change Probability.PoissonProcess.arrivalTime r future < t at hr
  linarith

/-- The isolated passive path in a full-future reconstruction is its direct
stationary marked-Poisson reconstruction from the external state and pair
stream. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_passivePath
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (factors : MulticlassPalmFutureFactorCarrier i j) :
    (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j factors).2 j =
      Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
        (arrivalRate j.1) (harrivalRate j.1) (factors.1.2.2, factors.2) := by
  unfold multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
  dsimp only
  rw [piWithoutCoordinateEquiv_symm_apply_self]

/-- The future work component of a full pair factor reconstructs as the
positive labelled work mark of the isolated passive class. -/
theorem multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_ofNat_succ
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (factors : MulticlassPalmFutureFactorCarrier i j) (n : ℕ) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j factors)
      j.1 (Int.ofNat (n + 1)) = (factors.2 n).2 := by
  unfold multiclassStationaryPoissonWorkClassTaggedRequirementAt
  rw [dif_neg j.property]
  rw [show (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j factors).2 j =
      Probability.Queueing.stationaryPoissonWorkFromFutureExternalIidFactors
        (arrivalRate j.1) (harrivalRate j.1) (factors.1.2.2, factors.2) by
      exact multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_passivePath
        arrivalRate harrivalRate i j factors]
  rfl

/-- Holding the external factor fixed preserves every nonpositive arrival of
the isolated passive class, even when its future IID pair stream changes. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_fst_eq_of_nonpositive
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j) (m : ℤ)
    (hfst : x.1 = y.1)
    (hgoodx : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hgoody : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ y.2).1, y.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hm : m ≤ 0) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) j.1 m =
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j y) j.1 m := by
  rcases x with ⟨external, stream⟩
  rcases y with ⟨otherExternal, otherStream⟩
  change external = otherExternal at hfst
  subst otherExternal
  unfold multiclassStationaryPoissonWorkClassTaggedArrival
  rw [dif_neg j.property, dif_neg j.property,
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_passivePath,
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_passivePath]
  exact Probability.Queueing.stationaryPoissonWorkArrival_fromFutureExternalIidFactors_eq_of_nonpositive
      (arrivalRate j.1) (harrivalRate j.1) external.2.2 stream otherStream m hgoodx hgoody hm

/-- Holding the external factor fixed preserves every nonpositive work mark
of the isolated passive class, regardless of its future IID pair stream. -/
theorem multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_eq_of_fst_eq_of_nonpositive
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j) (m : ℤ)
    (hfst : x.1 = y.1) (hm : m ≤ 0) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) j.1 m =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j y) j.1 m := by
  rcases x with ⟨external, stream⟩
  rcases y with ⟨otherExternal, otherStream⟩
  change external = otherExternal at hfst
  subst otherExternal
  unfold multiclassStationaryPoissonWorkClassTaggedRequirementAt
  rw [dif_neg j.property, dif_neg j.property,
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_passivePath,
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_passivePath]
  exact Probability.Queueing.stationaryPoissonWorkRequirement_fromFutureExternalIidFactors_eq_of_nonpositive
      (arrivalRate j.1) (harrivalRate j.1) external.2.2 stream otherStream m hm

/-- Separate one passive class at a deterministic future clock, retaining the
complete paths of the other passive classes and every part of the selected
class's input exposed by that clock. -/
def passiveStationaryPoissonWorkFutureTimeSliceFactor
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    ({k : Class // k ≠ i} → StationaryPoissonWorkPath) →
      (passiveClassComplement i j → StationaryPoissonWorkPath) ×
        (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
  fun omega =>
    let q := piWithoutCoordinate (α := StationaryPoissonWorkPath) j omega
    (q.1, Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s q.2)

theorem measurable_passiveStationaryPoissonWorkFutureTimeSliceFactor
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    Measurable (passiveStationaryPoissonWorkFutureTimeSliceFactor i j s) := by
  let q := piWithoutCoordinate (α := StationaryPoissonWorkPath) j
  exact (measurable_fst.comp (measurable_piWithoutCoordinate j)).prodMk
    ((Probability.Queueing.measurable_stationaryPoissonWorkFutureTimeSliceFactors s).comp
      (measurable_snd.comp (measurable_piWithoutCoordinate j)))

/-- Exact law of the passive-class deterministic-time factor. -/
theorem map_passiveStationaryPoissonWorkFutureTimeSliceFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (passiveStationaryPoissonWorkFutureTimeSliceFactor i j s)
      (Measure.pi fun k : {l : Class // l ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)) =
      (Measure.pi fun k : passiveClassComplement i j =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
        (Measure.map (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s)
          (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))) := by
  let μ : {k : Class // k ≠ i} → Measure StationaryPoissonWorkPath := fun k =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)
  let q := piWithoutCoordinate (α := StationaryPoissonWorkPath) j
  let F :
      (passiveClassComplement i j → StationaryPoissonWorkPath) × StationaryPoissonWorkPath →
        (passiveClassComplement i j → StationaryPoissonWorkPath) ×
          (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    Prod.map id (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s)
  letI : ∀ k : {l : Class // l ≠ i}, IsProbabilityMeasure (μ k) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate j.1)) :=
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate j.1)
  have hF : Measurable F := measurable_id.prodMap
    (Probability.Queueing.measurable_stationaryPoissonWorkFutureTimeSliceFactors s)
  change Measure.map (F ∘ q) (Measure.pi μ) = _
  rw [← Measure.map_map hF (measurable_piWithoutCoordinate j),
    map_piWithoutCoordinate μ j]
  change Measure.map F (ρ.prod
    (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))) =
      ρ.prod (Measure.map (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s)
        (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)))
  rw [← Measure.map_prod_map ρ
    (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)) measurable_id
      (Probability.Queueing.measurable_stationaryPoissonWorkFutureTimeSliceFactors s),
    Measure.map_id]

/-- Under the selected-arrival Palm law, isolate a passive class at a
deterministic future clock while retaining the complete selected path and all
other passive paths as external data. -/
def multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
        (passiveClassComplement i j → StationaryPoissonWorkPath)) ×
        (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
  fun z =>
    let q := passiveStationaryPoissonWorkFutureTimeSliceFactor i j s z.2
    ((z.1, q.1), q.2)

theorem measurable_multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor i j s) := by
  exact MeasurableEquiv.prodAssoc.symm.measurable.comp
    (measurable_id.prodMap (measurable_passiveStationaryPoissonWorkFutureTimeSliceFactor i j s))

/-- The fresh count exposed by a deterministic passive-class time slice is
the increment of that class's literal physical-time arrival count. -/
theorem canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor_eq_increment
    (i : Class) (j : {k : Class // k ≠ i}) (s h : ℝ) (hh : 0 ≤ h)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    Probability.PoissonProcess.canonicalRenewalCount h
      (multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor i j s z).2.2 =
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (s + h) -
          multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s := by
  change Probability.PoissonProcess.canonicalRenewalCount h
      (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s (z.2 j)).2 =
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (s + h) -
          multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s
  rw [AppliedModelingLib.Probability.Queueing.canonicalRenewalCount_stationaryPoissonWorkFutureTimeSliceFactors_eq_increment
    s h hh (z.2 j)]
  change Probability.PoissonProcess.canonicalRenewalCount (s + h)
      (Probability.PoissonProcess.suspensionToEquilibrium (z.2 j).1.1).1 -
        Probability.PoissonProcess.canonicalRenewalCount s
          (Probability.PoissonProcess.suspensionToEquilibrium (z.2 j).1.1).1 =
      Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1 (s + h) -
        Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1 s
  rw [AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_suspensionToEquilibrium_future_eq_suspensionBaseFutureCount,
    AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_suspensionToEquilibrium_future_eq_suspensionBaseFutureCount]

/-- The selected-arrival Palm law has the exact deterministic-time factor
law: all selected and complementary input is external to a passive class's
fresh residual arrival-gap tail. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor i j s)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ((Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate i)).Ptag.prod
        (Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1))).prod
        (Measure.map (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s)
          (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)
  let σ :=
    Measure.map (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s)
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))
  let passiveFactor := passiveStationaryPoissonWorkFutureTimeSliceFactor i j s
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : ∀ k : {l : Class // l ≠ i},
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate j.1)) :=
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate j.1)
  letI : IsProbabilityMeasure σ := by
    dsimp [σ]
    exact Measure.isProbabilityMeasure_map
      (Probability.Queueing.measurable_stationaryPoissonWorkFutureTimeSliceFactors s).aemeasurable
  change Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor i j s)
    (tagged.Ptag.prod passive.Pbase) = (tagged.Ptag.prod ρ).prod σ
  calc
    Measure.map (multiclassStationaryPoissonWorkClassTaggedFutureTimeSliceFactor i j s)
        (tagged.Ptag.prod passive.Pbase) =
        Measure.map (MeasurableEquiv.prodAssoc.symm :
          ((ℤ → ℝ) × (ℤ → ℝ)) ×
              ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
                (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) ×
                  (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) →
            (((ℤ → ℝ) × (ℤ → ℝ)) ×
              (passiveClassComplement i j → StationaryPoissonWorkPath)) ×
              (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) ×
                (ℕ × (ℕ → ℝ))) × (ℕ → ℝ))
          (Measure.map (Prod.map id passiveFactor) (tagged.Ptag.prod passive.Pbase)) := by
          symm
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            (measurable_id.prodMap
              (measurable_passiveStationaryPoissonWorkFutureTimeSliceFactor i j s))]
          rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm :
          ((ℤ → ℝ) × (ℤ → ℝ)) ×
              ((passiveClassComplement i j → StationaryPoissonWorkPath) ×
                (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) ×
                  (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) →
            (((ℤ → ℝ) × (ℤ → ℝ)) ×
              (passiveClassComplement i j → StationaryPoissonWorkPath)) ×
              (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) ×
                (ℕ × (ℕ → ℝ))) × (ℕ → ℝ))
          (tagged.Ptag.prod (ρ.prod σ)) := by
          rw [← Measure.map_prod_map _ _ measurable_id
            (measurable_passiveStationaryPoissonWorkFutureTimeSliceFactor i j s),
            Measure.map_id]
          have hpassive : Measure.map passiveFactor passive.Pbase = ρ.prod σ := by
            simpa [passiveFactor, passive, ρ, σ, multiclassStationaryPoissonWorkRestLaw] using
              (map_passiveStationaryPoissonWorkFutureTimeSliceFactor
                arrivalRate harrivalRate i j s hs)
          rw [hpassive]
    _ = (tagged.Ptag.prod ρ).prod σ := by
          exact (measurePreserving_prodAssoc tagged.Ptag ρ σ).symm.map_eq

/-- The selected Palm path and every passive path other than one distinguished
class, retained as external data while that class's stationary input is
isolated. -/
abbrev multiclassPalmPassiveClassTimeSliceState
    (i : Class) (j : {k : Class // k ≠ i}) :=
  ((ℤ → ℝ) × (ℤ → ℝ)) ×
    (passiveClassComplement i j → StationaryPoissonWorkPath)

/-- The selected-Palm data exposed through a deterministic clock for one
passive class, excluding its fresh residual arrival-gap tail. -/
abbrev multiclassPalmPassiveClassTimeSliceExternal
    (i : Class) (j : {k : Class // k ≠ i}) :=
  ((multiclassPalmPassiveClassTimeSliceState i j ×
    Probability.Queueing.StationaryPoissonWorkFutureTimeSliceBase) ×
    (ℕ × (ℕ → ℝ)))

/-- Isolate one passive stationary input, retaining the selected Palm path
and all other passive paths as an independent external state. -/
def multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      multiclassPalmPassiveClassTimeSliceState i j × StationaryPoissonWorkPath :=
  fun z =>
    let q := piWithoutCoordinate (α := StationaryPoissonWorkPath) j z.2
    ((z.1, q.1), q.2)

theorem measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j) := by
  exact MeasurableEquiv.prodAssoc.symm.measurable.comp
    (measurable_id.prodMap (measurable_piWithoutCoordinate (α := StationaryPoissonWorkPath) j))

/-- Exact selected-Palm law after isolating one passive stationary input. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ((Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate i)).Ptag.prod
        (Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1))).prod
        (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)
  let q := piWithoutCoordinate (α := StationaryPoissonWorkPath) j
  let A : MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      ((ℤ → ℝ) × (ℤ → ℝ)) ×
        ((passiveClassComplement i j → StationaryPoissonWorkPath) × StationaryPoissonWorkPath) :=
    Prod.map id q
  let r : ((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveClassComplement i j → StationaryPoissonWorkPath) × StationaryPoissonWorkPath) →
        multiclassPalmPassiveClassTimeSliceState i j × StationaryPoissonWorkPath :=
    MeasurableEquiv.prodAssoc.symm
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : ∀ k : {l : Class // l ≠ i},
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate j.1)) :=
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate j.1)
  have hq : Measurable q := measurable_piWithoutCoordinate (α := StationaryPoissonWorkPath) j
  have hA : Measurable A := measurable_id.prodMap hq
  have hr : Measurable r := MeasurableEquiv.prodAssoc.symm.measurable
  change Measure.map (r ∘ A) (tagged.Ptag.prod passive.Pbase) =
    (tagged.Ptag.prod ρ).prod
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))
  rw [← Measure.map_map hr hA, ← Measure.map_prod_map _ _ measurable_id hq, Measure.map_id]
  have hqmap : Measure.map q passive.Pbase =
      ρ.prod (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)) := by
    change Measure.map q passive.Pbase =
      ρ.prod (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))
    simpa [q, passive, ρ, multiclassStationaryPoissonWorkRestLaw] using
      (map_piWithoutCoordinate
        (fun k : {l : Class // l ≠ i} =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)) j)
  rw [hqmap]
  exact (measurePreserving_prodAssoc tagged.Ptag ρ
    (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))).symm.map_eq

/-- The full selected-Palm deterministic-time factor for one passive class. -/
def multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      multiclassPalmPassiveClassTimeSliceExternal i j × (ℕ → ℝ) :=
  fun z => Probability.Queueing.externalStationaryPoissonWorkFutureTimeSliceFactors s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j z)

theorem measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s) := by
  exact Probability.Queueing.measurable_externalStationaryPoissonWorkFutureTimeSliceFactors s |>.comp
    (measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j)

/-- The fresh tail in the selected-Palm passive-class time slice counts the
literal physical arrivals of that passive class in the following interval. -/
theorem canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_eq_increment
    (i : Class) (j : {k : Class // k ≠ i}) (s h : ℝ) (hh : 0 ≤ h)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    Probability.PoissonProcess.canonicalRenewalCount h
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 =
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (s + h) -
          multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s := by
  change Probability.PoissonProcess.canonicalRenewalCount h
      (Probability.Queueing.externalStationaryPoissonWorkFutureTimeSliceFactors s
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j z)).2 =
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (s + h) -
          multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s
  rw [AppliedModelingLib.Probability.Queueing.canonicalRenewalCount_externalStationaryPoissonWorkFutureTimeSliceFactors_eq_increment
    s h hh (multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j z)]
  change Probability.PoissonProcess.canonicalRenewalCount (s + h)
      (Probability.PoissonProcess.suspensionToEquilibrium (z.2 j).1.1).1 -
        Probability.PoissonProcess.canonicalRenewalCount s
          (Probability.PoissonProcess.suspensionToEquilibrium (z.2 j).1.1).1 =
      Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1 (s + h) -
        Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1 s
  rw [AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_suspensionToEquilibrium_future_eq_suspensionBaseFutureCount,
    AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_suspensionToEquilibrium_future_eq_suspensionBaseFutureCount]

/-- The fresh tail count is the cardinality of the literal right-closed
passive arrival window whose endpoints define the deterministic slice. -/
theorem canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_eq_card_rightClosed
    (i : Class) (j : {k : Class // k ≠ i}) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    Probability.PoissonProcess.canonicalRenewalCount h
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 =
        (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
          s (s + h) (z.2 j).1).card := by
  rw [canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_eq_increment
    i j s h hh z]
  exact Probability.PoissonProcess.suspensionBaseFutureCount_sub_eq_card_rightClosed
    (z.2 j).1 s (s + h) hs (by linarith)

/-- The passive time slice at the selected origin counts exactly the literal
physical arrivals of that class through its deterministic horizon. -/
theorem canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_zero_eq_futureCount
    (i : Class) (j : {k : Class // k ≠ i}) (t : ℝ) (ht : 0 ≤ t)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    Probability.PoissonProcess.canonicalRenewalCount t
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j 0 z).2 =
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j t := by
  rw [canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_eq_increment
    i j 0 t ht z]
  simp [multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount,
    Probability.PoissonProcess.suspensionBaseFutureCount_zero]

/-- Reconstruct a full selected-Palm multiclass input from the deterministic
time-slice factor of one passive class.  Away from the factor image, the only
totalization occurs in the reconstructed passive stationary input. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceFactors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    multiclassPalmPassiveClassTimeSliceExternal i j × (ℕ → ℝ) →
      MulticlassStationaryPoissonWorkClassTaggedSample Class i :=
  fun x =>
    let passive := Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceFactors
      (arrivalRate j.1) (harrivalRate j.1) s ((x.1.1.2, x.1.2), x.2)
    let rest := (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      (x.1.1.1.2, passive)
    (x.1.1.1.1, rest)

/-- The multiclass deterministic-time reconstruction section is Borel. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceFactors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceFactors
      arrivalRate harrivalRate i j s) := by
  let input : multiclassPalmPassiveClassTimeSliceExternal i j × (ℕ → ℝ) →
      Probability.Queueing.StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) :=
    fun x => ((x.1.1.2, x.1.2), x.2)
  have hinput : Measurable input :=
    ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  let passive : multiclassPalmPassiveClassTimeSliceExternal i j × (ℕ → ℝ) →
      StationaryPoissonWorkPath :=
    Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceFactors
      (arrivalRate j.1) (harrivalRate j.1) s ∘ input
  have hpassive : Measurable passive :=
    (Probability.Queueing.measurable_stationaryPoissonWorkFromFutureTimeSliceFactors
      (arrivalRate j.1) (harrivalRate j.1) s).comp hinput
  let rest : multiclassPalmPassiveClassTimeSliceExternal i j × (ℕ → ℝ) →
      ({k : Class // k ≠ i} → StationaryPoissonWorkPath) :=
    (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm ∘
      fun x => (x.1.1.1.2, passive x)
  have hrest : Measurable rest :=
    (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm.measurable.comp
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        hpassive)
  exact (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk hrest

/-- Reconstructing an actual selected-Palm deterministic-time factor recovers
the full multiclass input pointwise. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceFactors_apply_factors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceFactors
      arrivalRate harrivalRate i j s
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z) = z := by
  rcases z with ⟨selected, paths⟩
  have hpassive : Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceFactors
      (arrivalRate j.1) (harrivalRate j.1) s
      (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
        (paths j)) = paths j :=
    Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceFactors_apply_factors
      (arrivalRate j.1) (harrivalRate j.1) s (paths j)
  apply Prod.ext
  · rfl
  · change (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
        Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceFactors
          (arrivalRate j.1) (harrivalRate j.1) s
          (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
            ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2))) = paths
    rw [show (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2 = paths j by rfl,
      hpassive]
    exact MeasurableEquiv.symm_apply_apply (piWithoutCoordinateEquiv
      (α := StationaryPoissonWorkPath) j) paths

/-- Reconstruct a selected-Palm multiclass input from the deterministic
time-slice external data of one passive class, continuing that class with its
exposed backward renewal half rather than its fresh residual arrival tail. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    multiclassPalmPassiveClassTimeSliceExternal i j →
      MulticlassStationaryPoissonWorkClassTaggedSample Class i :=
  fun x =>
    let passive := Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
      (arrivalRate j.1) (harrivalRate j.1) s (x.1.2, x.2)
    let rest := (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      (x.1.1.2, passive)
    (x.1.1.1, rest)

/-- The external-only deterministic continuation of an isolated passive
class is Borel on the selected-Palm time-slice factor. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) :
    Measurable
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
        arrivalRate harrivalRate i j s) := by
  let input : multiclassPalmPassiveClassTimeSliceExternal i j →
      Probability.Queueing.StationaryPoissonWorkFutureTimeSliceExternal :=
    fun x => (x.1.2, x.2)
  have hinput : Measurable input :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  let passive : multiclassPalmPassiveClassTimeSliceExternal i j →
      StationaryPoissonWorkPath :=
    Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
      (arrivalRate j.1) (harrivalRate j.1) s ∘ input
  have hpassive : Measurable passive :=
    (Probability.Queueing.measurable_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
      (arrivalRate j.1) (harrivalRate j.1) s).comp hinput
  let rest : multiclassPalmPassiveClassTimeSliceExternal i j →
      ({k : Class // k ≠ i} → StationaryPoissonWorkPath) :=
    (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm ∘
      fun x => (x.1.1.2, passive x)
  have hrest : Measurable rest :=
    (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm.measurable.comp
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk hpassive)
  exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hrest

/-- For the isolated passive class, the multiclass continuation preserves the
complete forward renewal history exposed at the deterministic clock. -/
theorem canonicalRenewalPastHistory_multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
      arrivalRate harrivalRate i j s
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
    Probability.PoissonProcess.canonicalRenewalPastHistory s
      ((Probability.PoissonProcess.suspensionToEquilibrium
        ((w.2 j).1.1)).1) =
      Probability.PoissonProcess.canonicalRenewalPastHistory s
        ((Probability.PoissonProcess.suspensionToEquilibrium ((z.2 j).1.1)).1) := by
  rcases z with ⟨selected, paths⟩
  change Probability.PoissonProcess.canonicalRenewalPastHistory s
      ((Probability.PoissonProcess.suspensionToEquilibrium
        (((piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
          ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
            Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
              (arrivalRate j.1) (harrivalRate j.1) s
              (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
                ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2)).1)) j).1.1)).1 =
      Probability.PoissonProcess.canonicalRenewalPastHistory s
        ((Probability.PoissonProcess.suspensionToEquilibrium ((paths j).1.1)).1)
  rw [piWithoutCoordinateEquiv_symm_apply_self]
  rw [show (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2 = paths j by rfl]
  exact Probability.Queueing.canonicalRenewalPastHistory_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
    (arrivalRate j.1) (harrivalRate j.1) s hs (paths j)

/-- For the isolated passive class, every labelled arrival at or before the
deterministic clock is unchanged by the external-only continuation.  Thus a
finite multiclass queueing trace through that clock sees the literal same
passive arrival epochs. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_arrival_eq_of_le
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (k : ℤ)
    (hk : multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 k ≤ s) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
        arrivalRate harrivalRate i j s
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
      j.1 k =
    multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 k := by
  rcases z with ⟨selected, paths⟩
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne
    i j.1 j.2 (selected, paths) k] at hk
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne
    i j.1 j.2 (selected, paths) k]
  dsimp only [multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail,
    multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor]
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne i j.1 j.2]
  change Probability.Queueing.stationaryPoissonWorkArrival
      (((piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
        ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
          Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
            (arrivalRate j.1) (harrivalRate j.1) s
            (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
              ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2)).1)) j) k =
      Probability.Queueing.stationaryPoissonWorkArrival (paths j) k
  rw [piWithoutCoordinateEquiv_symm_apply_self]
  rw [show (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2 = paths j by rfl]
  change Probability.PoissonProcess.suspensionBaseArrival
      (Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
        (arrivalRate j.1) (harrivalRate j.1) s
        (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s (paths j)).1).1 k =
      Probability.PoissonProcess.suspensionBaseArrival (paths j).1 k
  change Probability.PoissonProcess.suspensionBaseArrival (paths j).1 k ≤ s at hk
  exact Probability.Queueing.suspensionBaseArrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_eq_of_le
    (arrivalRate j.1) (harrivalRate j.1) s hs (paths j) k hk

/-- The isolated passive arrival agrees through a deterministic clock if
either the original or reconstructed path places it there.  This symmetric
form identifies the literal finite pre-clock point set on both sides. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_arrival_eq_of_le_or_le
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (k : ℤ)
    (hk : multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 k ≤ s ∨
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        j.1 k ≤ s) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
        arrivalRate harrivalRate i j s
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
      j.1 k =
    multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 k := by
  rcases hk with hk | hk
  · exact multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_arrival_eq_of_le
      arrivalRate harrivalRate i j s hs z k hk
  rcases z with ⟨selected, paths⟩
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne
    i j.1 j.2 (selected, paths) k]
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne i j.1 j.2] at hk
  dsimp only [multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail,
    multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor,
    multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor] at hk ⊢
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_of_ne i j.1 j.2]
  change Probability.Queueing.stationaryPoissonWorkArrival
      (((piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
        ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
          Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
            (arrivalRate j.1) (harrivalRate j.1) s
            (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
              ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2)).1)) j) k =
      Probability.Queueing.stationaryPoissonWorkArrival (paths j) k
  rw [piWithoutCoordinateEquiv_symm_apply_self] at hk ⊢
  rw [show (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2 = paths j by rfl] at hk ⊢
  change Probability.PoissonProcess.suspensionBaseArrival
      (Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
        (arrivalRate j.1) (harrivalRate j.1) s
        (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s (paths j)).1).1 k =
      Probability.PoissonProcess.suspensionBaseArrival (paths j).1 k
  change Probability.PoissonProcess.suspensionBaseArrival
      (Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
        (arrivalRate j.1) (harrivalRate j.1) s
        (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s (paths j)).1).1 k ≤ s at hk
  exact Probability.Queueing.suspensionBaseArrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_eq_of_le_or_le
    (arrivalRate j.1) (harrivalRate j.1) s hs (paths j) k (Or.inr hk)

/-- The deterministic continuation leaves the complete selected Palm path
unchanged. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
      arrivalRate harrivalRate i j s
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1).1 =
      z.1 := by
  rcases z with ⟨selected, paths⟩
  rfl

/-- Every passive path other than the isolated coordinate is retained exactly
by the deterministic continuation. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_otherPassive_eq
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (k : {l : Class // l ≠ i}) (hkj : k ≠ j) :
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
      arrivalRate harrivalRate i j s
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1).2 k =
      z.2 k := by
  rcases z with ⟨selected, paths⟩
  change ((piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
        Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
          (arrivalRate j.1) (harrivalRate j.1) s
          (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
            ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2)).1)) k = paths k
  rw [piWithoutCoordinateEquiv_symm_apply_of_ne j _ k hkj]
  calc
    (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1 ⟨k, hkj⟩ =
        ((piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
          (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths)) k := by
        symm
        exact piWithoutCoordinateEquiv_symm_apply_of_ne j
          (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths) k hkj
    _ = paths k := congrFun ((piWithoutCoordinateEquiv
      (α := StationaryPoissonWorkPath) j).symm_apply_apply paths) k

/-- The isolated passive coordinate retains every one of its service-work
marks, even though its unexposed future arrival-gap tail is replaced. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_isolatedRequirement_eq
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (k : ℤ) :
    ((multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
      arrivalRate harrivalRate i j s
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1).2 j).2 k =
      (z.2 j).2 k := by
  rcases z with ⟨selected, paths⟩
  change (((piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).symm
      ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).1,
        Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
          (arrivalRate j.1) (harrivalRate j.1) s
          (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceFactors s
            ((piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2)).1)) j).2 k =
      (paths j).2 k
  rw [piWithoutCoordinateEquiv_symm_apply_self]
  rw [show (piWithoutCoordinate (α := StationaryPoissonWorkPath) j paths).2 = paths j by rfl]
  exact congrFun
    (Probability.Queueing.stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_work_apply_factors
      (arrivalRate j.1) (harrivalRate j.1) s (paths j)) k

/-- Exact selected-Palm law of the deterministic-time factor for one passive
class. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ((((Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate i)).Ptag.prod
        (Measure.pi fun k : passiveClassComplement i j =>
          Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1))).prod
        (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceBaseMeasure (arrivalRate j.1))).prod
        (Measure.map (Probability.PoissonProcess.canonicalRenewalPastHistory s)
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i)
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)
  let θ : Measure (multiclassPalmPassiveClassTimeSliceState i j) := tagged.Ptag.prod ρ
  let Q := multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j
  let E := Probability.Queueing.externalStationaryPoissonWorkFutureTimeSliceFactors
    (β := multiclassPalmPassiveClassTimeSliceState i j) s
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure θ := by
    dsimp [θ]
    infer_instance
  have hQ : Measurable Q :=
    measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j
  have hE : Measurable E :=
    Probability.Queueing.measurable_externalStationaryPoissonWorkFutureTimeSliceFactors s
  change Measure.map (E ∘ Q) _ = _
  rw [← Measure.map_map hE hQ,
    map_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor
      arrivalRate harrivalRate i j]
  simpa [E, θ] using
    (Probability.Queueing.map_externalStationaryPoissonWorkFutureTimeSliceFactors
      θ (harrivalRate j.1) hs)

/-- Selected-Palm deterministic-interval compensation for a passive class.
The multiplier may depend on the tagged path, every other passive class, and
the isolated class's complete history through the clock. -/
theorem integral_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (f : multiclassPalmPassiveClassTimeSliceExternal i j → ℝ) (hf : Measurable f) :
    ∫ z, f (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1 *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∫ z, f (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
        (arrivalRate j.1 * h) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i)
  let ρ : Measure (passiveClassComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)
  let θ : Measure (multiclassPalmPassiveClassTimeSliceState i j) := tagged.Ptag.prod ρ
  let Q := multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j
  let E := Probability.Queueing.externalStationaryPoissonWorkFutureTimeSliceFactors
    (β := multiclassPalmPassiveClassTimeSliceState i j) s
  let F := multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure θ := by
    dsimp [θ]
    infer_instance
  letI : IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate j.1)) :=
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate j.1)
  have hQ : Measurable Q :=
    measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor i j
  have hE : Measurable E :=
    Probability.Queueing.measurable_externalStationaryPoissonWorkFutureTimeSliceFactors s
  have hQmap : Measure.map Q
      (Probability.Palm.targetPassiveTaggedArrivalAtZero tagged
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      θ.prod (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)) := by
    simpa [Q, θ] using
      (map_multiclassStationaryPoissonWorkClassTaggedPassiveClassInputFactor
        arrivalRate harrivalRate i j)
  let hQlaw : ProbabilityTheory.HasLaw Q
      (θ.prod (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero tagged
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag :=
    ⟨hQ.aemeasurable, hQmap⟩
  have hrewardMeas : Measurable (fun u :
      multiclassPalmPassiveClassTimeSliceState i j × StationaryPoissonWorkPath =>
      f (E u).1 * (Probability.PoissonProcess.canonicalRenewalCount h (E u).2 : ℝ)) :=
    (hf.comp (measurable_fst.comp hE)).mul
      ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
        ((Probability.PoissonProcess.measurable_canonicalRenewalCount h).comp
          (measurable_snd.comp hE)))
  have hexternalMeas : Measurable (fun u :
      multiclassPalmPassiveClassTimeSliceState i j × StationaryPoissonWorkPath =>
      f (E u).1) := hf.comp (measurable_fst.comp hE)
  have hgeneric :=
    Probability.Queueing.integral_externalStationaryPoissonWorkFutureTimeSliceSelector_mul_arrivalCount
      θ (harrivalRate j.1) hs hh f hf
  change
    (∫ z, f (F z).1 * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero tagged
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) =
      (∫ z, f (F z).1 ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero tagged
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
        (arrivalRate j.1 * h)
  calc
    (∫ z, f (F z).1 * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero tagged
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) =
        ∫ u, f (E u).1 * (Probability.PoissonProcess.canonicalRenewalCount h (E u).2 : ℝ)
          ∂(θ.prod (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1))) := by
          simpa [F, E] using hQlaw.integral_comp (f := fun u =>
            f (E u).1 * (Probability.PoissonProcess.canonicalRenewalCount h (E u).2 : ℝ))
            hrewardMeas.aestronglyMeasurable
    _ = (∫ u, f (E u).1
          ∂(θ.prod (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)))) *
          (arrivalRate j.1 * h) := by
          simpa [E] using hgeneric
    _ = (∫ z, f (F z).1 ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero tagged
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
          (arrivalRate j.1 * h) := by
          rw [← hQlaw.integral_comp (f := fun u => f (E u).1)
            hexternalMeas.aestronglyMeasurable]
          congr 1

/-- A bounded selected-Palm time-slice selector times the following passive
arrival count is integrable.  This supplies the analytic premise for finite
grid compensation when the selector is a waiting or occupancy indicator. -/
theorem integrable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (f : multiclassPalmPassiveClassTimeSliceExternal i j → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun z =>
      f (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1 *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j s z).2 : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let R := Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)
  let F := multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (harrivalRate j.1)
  letI : IsProbabilityMeasure
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i)).Ptag :=
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i)).isProbability
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.Queueing.stationaryPoissonWorkFutureTimeSliceBaseMeasure (arrivalRate j.1)) := by
    simp [Probability.Queueing.stationaryPoissonWorkFutureTimeSliceBaseMeasure]
    infer_instance
  letI : IsProbabilityMeasure (Measure.map
      (Probability.PoissonProcess.canonicalRenewalPastHistory s)
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1))) :=
    Measure.isProbabilityMeasure_map
      (Probability.PoissonProcess.measurable_canonicalRenewalPastHistory s).aemeasurable
  have hF : Measurable F :=
    measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s
  have hresidualMap : Measure.map (fun z => (F z).2) P = R := by
    calc
      Measure.map (fun z => (F z).2) P = Measure.map Prod.snd (Measure.map F P) := by
        rw [Measure.map_map measurable_snd hF]
        rfl
      _ = R := by
        dsimp [P, F, R]
        rw [map_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
          arrivalRate harrivalRate i j s hs]
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  let hresidual : MeasurePreserving (fun z => (F z).2) P R :=
    ⟨measurable_snd.comp hF, hresidualMap⟩
  have hcount : Integrable (fun z =>
      (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ)) P := by
    have hbase := Probability.PoissonProcess.integrable_canonicalRenewalCount
      (rate := arrivalRate j.1) (t := h) (harrivalRate j.1) hh
    simpa [Function.comp_def] using hresidual.integrable_comp_of_integrable hbase
  have hselectedMeas : Measurable (fun z => f (F z).1) :=
    hf.comp (measurable_fst.comp hF)
  have hcountMeas : Measurable (fun z =>
      (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ)) :=
    (measurable_of_countable fun n : ℕ => (n : ℝ)).comp
      ((Probability.PoissonProcess.measurable_canonicalRenewalCount h).comp
        (measurable_snd.comp hF))
  refine Integrable.mono' (hcount.const_mul ‖C‖)
    (hselectedMeas.aestronglyMeasurable.mul hcountMeas.aestronglyMeasurable) ?_
  filter_upwards with z
  have hnonnegative : 0 ≤
      (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) :=
    Nat.cast_nonneg _
  calc
    ‖f (F z).1 * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ)‖ =
        ‖f (F z).1‖ * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) := by
          simp [norm_mul, Real.norm_eq_abs]
    _ ≤ C * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) :=
      mul_le_mul_of_nonneg_right (hbound (F z).1) hnonnegative
    _ = ‖C‖ * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hC]

/-- The literal passive-class arrival count through any fixed nonnegative
physical horizon is integrable under the selected-arrival Palm law. -/
theorem integrable_multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j t : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hbase : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      (Probability.PoissonProcess.canonicalRenewalCount t
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j 0 z).2 : ℝ)) P := by
    simpa [P] using
      (integrable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
        arrivalRate harrivalRate i j 0 t (le_refl 0) ht (fun _ => (1 : ℝ)) measurable_const
        1 (by norm_num) (fun _ => by norm_num))
  refine hbase.congr ?_
  filter_upwards with z
  rw [canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_zero_eq_futureCount
    i j t ht z]

/-- Finite-grid compensation for one passive Poisson input under a selected
Palm law.  At every grid point the selector may use all input data exposed by
that time; the next interval count is still compensated by its rate.  The
integrability premise is only the ordinary finite-sum hypothesis needed to
exchange the integral with the grid sum. -/
theorem integral_sum_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (h : ℝ) (hh : 0 ≤ h)
    (N : ℕ) (f : ℕ → multiclassPalmPassiveClassTimeSliceExternal i j → ℝ)
    (hf : ∀ r, Measurable (f r))
    (hintegrable : ∀ r, r < N →
      Integrable (fun z =>
        f r (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
          i j ((r : ℝ) * h) z).1 *
          (Probability.PoissonProcess.canonicalRenewalCount h
            (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
              i j ((r : ℝ) * h) z).2 : ℝ))
        (Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) :
    ∫ z, ∑ r ∈ Finset.range N,
      f r (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
        i j ((r : ℝ) * h) z).1 *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j ((r : ℝ) * h) z).2 : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∑ r ∈ Finset.range N,
        (∫ z, f r (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
          i j ((r : ℝ) * h) z).1
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
          (arrivalRate j.1 * h) := by
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro r hr
    exact integral_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount
      arrivalRate harrivalRate i j ((r : ℝ) * h) h
      (mul_nonneg (Nat.cast_nonneg r) hh) hh (f r) (hf r)
  · intro r hr
    exact hintegrable r (Finset.mem_range.mp hr)

/-- Finite-grid selected-Palm compensation for uniformly bounded selectors.
The boundedness hypothesis automatically supplies all finite-sum
integrability obligations. -/
theorem integral_sum_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) (h : ℝ) (hh : 0 ≤ h)
    (N : ℕ) (f : ℕ → multiclassPalmPassiveClassTimeSliceExternal i j → ℝ)
    (hf : ∀ r, Measurable (f r))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ r x, ‖f r x‖ ≤ C) :
    ∫ z, ∑ r ∈ Finset.range N,
      f r (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
        i j ((r : ℝ) * h) z).1 *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j ((r : ℝ) * h) z).2 : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∑ r ∈ Finset.range N,
        (∫ z, f r (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
          i j ((r : ℝ) * h) z).1
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
          (arrivalRate j.1 * h) := by
  apply integral_sum_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount
    arrivalRate harrivalRate i j h hh N f hf
  intro r hr
  exact integrable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
    arrivalRate harrivalRate i j ((r : ℝ) * h) h
    (mul_nonneg (Nat.cast_nonneg r) hh) hh (f r) (hf r) C hC (hbound r)

end

end AppliedModelingLib.Queueing

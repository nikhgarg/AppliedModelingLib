import AppliedModelingLib.Foundations.Probability.FiniteProductCoordinateFactors
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkPastRate
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastRate
import AppliedModelingLib.Queueing.MulticlassPalmInput

/-!
# Canonical strict-past input around a multiclass selected arrival

This module exposes the marked input strictly before a deterministic origin
and strictly before a selected class arrival in one common canonical renewal
representation.  It proves the stationary-side product law first.  The
selected-arrival product transport is built below from the concrete Campbell
carrier; queue states and response times are deliberately outside this input
layer.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance multiclassPalmPastInputDecidableEq : DecidableEq Class := Classical.decEq Class

/-- One class's canonical strict-past input: its backwards arrival-gap path
and the corresponding iid unit-work-mark path. -/
abbrev StationaryPoissonWorkPastCanonicalSample := (ℕ → ℝ) × (ℕ → ℝ)

/-- The strict past of one stationary marked-Poisson input, expressed in the
canonical backwards-renewal coordinates. -/
noncomputable def stationaryPoissonWorkPastCanonicalPath :
    StationaryPoissonWorkPath → StationaryPoissonWorkPastCanonicalSample :=
  fun z => Probability.Queueing.equilibriumPastMarkedInput
    (Probability.Queueing.stationaryPoissonWorkToEquilibrium z)

/-- The strict past of one stationary marked-Poisson input has the product of
its canonical exponential gap and unit-work laws. -/
theorem stationaryPoissonWorkPastCanonicalPath_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving stationaryPoissonWorkPastCanonicalPath
      (Probability.Queueing.stationaryPoissonWorkMeasure rate)
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  simpa [stationaryPoissonWorkPastCanonicalPath] using
    (Probability.Queueing.equilibriumPastMarkedInput_measurePreserving hrate).comp
      (Probability.Queueing.stationaryPoissonWorkToEquilibrium_measurePreserving hrate)

/-- The complete canonical strict-past input of a finite stationary
multiclass marked-Poisson system. -/
noncomputable def multiclassStationaryPoissonWorkPastCanonicalInput
    (omega : Class → StationaryPoissonWorkPath) :
    Class → StationaryPoissonWorkPastCanonicalSample :=
  fun j => stationaryPoissonWorkPastCanonicalPath (omega j)

/-- The strict-past input of the whole stationary multiclass system preserves
the product of the classwise canonical marked-renewal laws. -/
theorem multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j) :
    MeasurePreserving (multiclassStationaryPoissonWorkPastCanonicalInput (Class := Class))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (Measure.pi fun j =>
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let μ : Class → Measure StationaryPoissonWorkPath := fun j =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j)
  let ν : Class → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate j)
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (harrivalRate j)
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (by norm_num)
    dsimp [ν]
    infer_instance
  simpa [multiclassStationaryPoissonWorkPastCanonicalInput,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ, ν] using
    (MeasureTheory.measurePreserving_pi μ ν fun j =>
      stationaryPoissonWorkPastCanonicalPath_measurePreserving (harrivalRate j))

/-- Two renewal epochs from distinct canonical class coordinates do not
coincide almost surely.  The proof factors out one class coordinate and uses
the atomlessness of each fixed exponential-renewal arrival epoch; it does not
invoke a superposition theorem or any queue-state assertion. -/
theorem ae_multiclassCanonicalPastArrivalTime_ne_of_ne
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (firstClass secondClass : Class) (hclasses : secondClass ≠ firstClass)
    (firstIndex secondIndex : ℕ) :
    ∀ᵐ past ∂(Measure.pi fun j =>
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      Probability.PoissonProcess.arrivalTime firstIndex (past firstClass).1 ≠
        Probability.PoissonProcess.arrivalTime secondIndex (past secondClass).1 := by
  classical
  let ν : Class → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let νrest : {j : Class // j ≠ firstClass} →
      Measure StationaryPoissonWorkPastCanonicalSample := fun j => ν j.1
  let secondRest : {j : Class // j ≠ firstClass} := ⟨secondClass, hclasses⟩
  letI (j : Class) : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (harrivalRate j)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (harrivalRate j)
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (by norm_num)
    dsimp [ν]
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (νrest j) := fun j => by
    dsimp [νrest]
    infer_instance
  have hsplit := Probability.piWithoutCoordinate_measurePreserving ν firstClass
  have hproduct : ∀ᵐ q :
      ({j : Class // j ≠ firstClass} → StationaryPoissonWorkPastCanonicalSample) ×
        StationaryPoissonWorkPastCanonicalSample ∂(Measure.pi νrest).prod (ν firstClass),
      Probability.PoissonProcess.arrivalTime firstIndex q.2.1 ≠
        Probability.PoissonProcess.arrivalTime secondIndex (q.1 secondRest).1 := by
    have hleft : Measurable (fun q :
        ({j : Class // j ≠ firstClass} → StationaryPoissonWorkPastCanonicalSample) ×
          StationaryPoissonWorkPastCanonicalSample =>
        Probability.PoissonProcess.arrivalTime firstIndex q.2.1) :=
      (Probability.PoissonProcess.measurable_arrivalTime firstIndex).comp
        (measurable_fst.comp measurable_snd)
    have hright : Measurable (fun q :
        ({j : Class // j ≠ firstClass} → StationaryPoissonWorkPastCanonicalSample) ×
          StationaryPoissonWorkPastCanonicalSample =>
        Probability.PoissonProcess.arrivalTime secondIndex
          (q.1 secondRest).1) :=
      (Probability.PoissonProcess.measurable_arrivalTime secondIndex).comp
        (measurable_fst.comp
          ((measurable_pi_apply secondRest).comp measurable_fst))
    have hmeas : MeasurableSet {q :
        ({j : Class // j ≠ firstClass} → StationaryPoissonWorkPastCanonicalSample) ×
          StationaryPoissonWorkPastCanonicalSample |
          Probability.PoissonProcess.arrivalTime firstIndex q.2.1 ≠
          Probability.PoissonProcess.arrivalTime secondIndex
            (q.1 secondRest).1} :=
      (measurableSet_eq_fun hleft hright).compl
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas]
    apply Filter.Eventually.of_forall
    intro rest
    let target : ℝ := Probability.PoissonProcess.arrivalTime secondIndex
      (rest secondRest).1
    let source : Set (ℕ → ℝ) := {g |
      Probability.PoissonProcess.arrivalTime firstIndex g = target}
    have hsource : MeasurableSet source :=
      measurableSet_eq_fun
        (Probability.PoissonProcess.measurable_arrivalTime firstIndex) measurable_const
    have hfst : MeasurePreserving
        (Prod.fst : StationaryPoissonWorkPastCanonicalSample → ℕ → ℝ)
        (ν firstClass)
        (Probability.PoissonProcess.exponentialInterarrivalMeasure
          (arrivalRate firstClass)) := by
      exact MeasureTheory.measurePreserving_fst
    have hzero : ν firstClass {sample |
        Probability.PoissonProcess.arrivalTime firstIndex sample.1 = target} = 0 := by
      change ν firstClass (Prod.fst ⁻¹' source) = 0
      rw [← Measure.map_apply measurable_fst hsource, hfst.map_eq]
      exact Probability.PoissonProcess.arrivalTime_measure_singleton_eq_zero
        (harrivalRate firstClass) firstIndex target
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with sample hsample
    exact hsample
  have hproductMap : ∀ᵐ q :
      ({j : Class // j ≠ firstClass} → StationaryPoissonWorkPastCanonicalSample) ×
        StationaryPoissonWorkPastCanonicalSample ∂Measure.map
          (Probability.piWithoutCoordinate firstClass) (Measure.pi ν),
      Probability.PoissonProcess.arrivalTime firstIndex q.2.1 ≠
        Probability.PoissonProcess.arrivalTime secondIndex (q.1 secondRest).1 := by
    rw [hsplit.map_eq]
    exact hproduct
  have hpull := MeasureTheory.ae_of_ae_map
    (μ := Measure.pi ν) (f := Probability.piWithoutCoordinate firstClass)
    (p := fun q :
      ({j : Class // j ≠ firstClass} → StationaryPoissonWorkPastCanonicalSample) ×
        StationaryPoissonWorkPastCanonicalSample =>
      Probability.PoissonProcess.arrivalTime firstIndex q.2.1 ≠
        Probability.PoissonProcess.arrivalTime secondIndex (q.1 secondRest).1)
    hsplit.measurable.aemeasurable hproductMap
  simpa [ν, νrest, secondRest, Probability.piWithoutCoordinate_apply_self,
    Probability.piWithoutCoordinate_apply_of_ne firstClass secondClass hclasses] using hpull

/-- Every canonical class coordinate has strictly ordered renewal epochs almost
surely.  This is the within-class half of the collision-free strict-past
input law. -/
theorem ae_multiclassCanonicalPastArrivalTime_strictMono
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j) :
    ∀ᵐ past ∂(Measure.pi fun j =>
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ j : Class, StrictMono (fun index : ℕ =>
        Probability.PoissonProcess.arrivalTime index (past j).1) := by
  classical
  let ν : Class → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI (j : Class) : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (harrivalRate j)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    dsimp [ν]
    infer_instance
  rw [ae_all_iff]
  intro j
  have hcoordinate : MeasurePreserving (fun past :
      Class → StationaryPoissonWorkPastCanonicalSample => (past j).1)
      (Measure.pi ν)
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)) := by
    exact (MeasureTheory.measurePreserving_fst : MeasurePreserving Prod.fst
      (ν j)
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j))).comp
        (MeasureTheory.measurePreserving_eval ν j)
  refine MeasureTheory.ae_of_ae_map (μ := Measure.pi ν)
    (f := fun past : Class → StationaryPoissonWorkPastCanonicalSample => (past j).1)
    (p := fun gaps : ℕ → ℝ => StrictMono (fun index : ℕ =>
      Probability.PoissonProcess.arrivalTime index gaps))
    hcoordinate.measurable.aemeasurable ?_
  rw [hcoordinate.map_eq]
  exact Probability.PoissonProcess.ae_arrivalTime_strictMono (harrivalRate j)

/-- Under the finite product of independent canonical renewal coordinates,
two arrival epochs coincide only when both their class and their renewal index
coincide. -/
theorem ae_multiclassCanonicalPastArrivalTime_eq_iff
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j) :
    ∀ᵐ past ∂(Measure.pi fun j =>
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ firstClass secondClass : Class, ∀ firstIndex secondIndex : ℕ,
        Probability.PoissonProcess.arrivalTime firstIndex (past firstClass).1 =
            Probability.PoissonProcess.arrivalTime secondIndex (past secondClass).1 →
          firstClass = secondClass ∧ firstIndex = secondIndex := by
  classical
  have hstrict := ae_multiclassCanonicalPastArrivalTime_strictMono
    arrivalRate harrivalRate
  rw [ae_all_iff]
  intro firstClass
  rw [ae_all_iff]
  intro secondClass
  rw [ae_all_iff]
  intro firstIndex
  rw [ae_all_iff]
  intro secondIndex
  by_cases hclasses : secondClass = firstClass
  · subst secondClass
    filter_upwards [hstrict] with past hpast
    intro heq
    exact ⟨rfl, (hpast firstClass).injective heq⟩
  · filter_upwards [ae_multiclassCanonicalPastArrivalTime_ne_of_ne
      arrivalRate harrivalRate firstClass secondClass hclasses firstIndex secondIndex]
      with past hne
    intro heq
    exact (hne heq).elim

/-- The collision-free canonical arrival law transported to a stationary
multiclass marked-Poisson input. -/
theorem ae_multiclassStationaryPoissonWorkPastCanonicalArrivalTime_eq_iff
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      ∀ firstClass secondClass : Class, ∀ firstIndex secondIndex : ℕ,
        Probability.PoissonProcess.arrivalTime firstIndex
            (multiclassStationaryPoissonWorkPastCanonicalInput omega firstClass).1 =
          Probability.PoissonProcess.arrivalTime secondIndex
            (multiclassStationaryPoissonWorkPastCanonicalInput omega secondClass).1 →
          firstClass = secondClass ∧ firstIndex = secondIndex := by
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Class)
  have hmap := multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
    (Class := Class) arrivalRate harrivalRate
  refine MeasureTheory.ae_of_ae_map
    (μ := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (f := canonical)
    (p := fun past => ∀ firstClass secondClass : Class, ∀ firstIndex secondIndex : ℕ,
      Probability.PoissonProcess.arrivalTime firstIndex (past firstClass).1 =
          Probability.PoissonProcess.arrivalTime secondIndex (past secondClass).1 →
        firstClass = secondClass ∧ firstIndex = secondIndex)
    hmap.measurable.aemeasurable ?_
  rw [hmap.map_eq]
  exact ae_multiclassCanonicalPastArrivalTime_eq_iff arrivalRate harrivalRate

/-- Canonical strict-past input of the passive classes on a selected-arrival
carrier. -/
noncomputable def multiclassStationaryPoissonWorkRestPastCanonicalInput
    (i : Class) :
    ({j : Class // j ≠ i} → StationaryPoissonWorkPath) →
      ({j : Class // j ≠ i} → StationaryPoissonWorkPastCanonicalSample) :=
  fun w j => stationaryPoissonWorkPastCanonicalPath (w j)

/-- The passive strict-past paths retain their independent product law after
the selected class has been Palm-recentered. -/
theorem multiclassStationaryPoissonWorkRestPastCanonicalInput_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    MeasurePreserving (multiclassStationaryPoissonWorkRestPastCanonicalInput i)
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
      (Measure.pi fun j : {k : Class // k ≠ i} =>
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let μ : {j : Class // j ≠ i} → Measure StationaryPoissonWorkPath := fun j =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)
  let ν : {j : Class // j ≠ i} → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate j.1)
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (harrivalRate j.1)
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (by norm_num)
    dsimp [ν]
    infer_instance
  simpa [multiclassStationaryPoissonWorkRestPastCanonicalInput,
    multiclassStationaryPoissonWorkRestLaw, μ, ν] using
    (MeasureTheory.measurePreserving_pi μ ν fun j =>
      stationaryPoissonWorkPastCanonicalPath_measurePreserving (harrivalRate j.1))

/-- The complete canonical strict-past input observed at a selected class
arrival.  The distinguished coordinate is the selected Palm past; every
passive coordinate is the corresponding time-shifted stationary past. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
    (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      (Class → StationaryPoissonWorkPastCanonicalSample) :=
  fun z => (Probability.piWithoutCoordinateEquiv i).symm
    (multiclassStationaryPoissonWorkRestPastCanonicalInput i z.2,
      Probability.PoissonProcess.candidatePastMarkedInput z.1)

/-- The finite-window stationary-index reconciliation required of every
passive coordinate on a class-selected input. -/
def multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood
    (i : Class) (horizon : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) : Prop :=
  ∀ j : {j : Class // j ≠ i},
    Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (z.2 j).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium (z.2 j)).1

/-- The distinguished coordinate of the selected-arrival canonical past is
the literal Palm past. -/
theorem multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_self
    (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i z i =
      Probability.PoissonProcess.candidatePastMarkedInput z.1 := by
  exact Probability.piWithoutCoordinateEquiv_symm_apply_self i
    (multiclassStationaryPoissonWorkRestPastCanonicalInput i z.2,
      Probability.PoissonProcess.candidatePastMarkedInput z.1)

/-- A passive coordinate of the selected-arrival canonical past is exactly
the canonical past of that stationary passive path. -/
theorem multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_of_ne
    (i j : Class) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i z j =
      stationaryPoissonWorkPastCanonicalPath (z.2 ⟨j, hji⟩) := by
  rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput]
  simpa [multiclassStationaryPoissonWorkRestPastCanonicalInput] using
    (Probability.piWithoutCoordinateEquiv_symm_apply_of_ne i
      (multiclassStationaryPoissonWorkRestPastCanonicalInput i z.2,
        Probability.PoissonProcess.candidatePastMarkedInput z.1) j hji)

/-- The selected-arrival canonical strict-past input has exactly the same
full finite-class product law as the stationary canonical strict-past input.
This is an input-law equality, not yet an identification of the derived
remote-past queue state. -/
theorem multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      (Measure.pi fun j =>
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let ν : Class → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let νrest : {j : Class // j ≠ i} → Measure StationaryPoissonWorkPastCanonicalSample :=
    fun j => ν j.1
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (harrivalRate j)
    letI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
        (by norm_num)
    dsimp [ν]
    infer_instance
  have hselected : MeasurePreserving Probability.PoissonProcess.candidatePastMarkedInput
      tagged.Ptag (ν i) := by
    simpa [tagged, ν] using
      (Probability.PoissonProcess.candidatePastMarkedInput_measurePreserving
        (harrivalRate i))
  have hpassive : MeasurePreserving
      (multiclassStationaryPoissonWorkRestPastCanonicalInput i)
      passive.Pbase (Measure.pi νrest) := by
    simpa [passive, νrest, ν] using
      (multiclassStationaryPoissonWorkRestPastCanonicalInput_measurePreserving
        arrivalRate harrivalRate i)
  have hsplit : MeasurePreserving
      (fun z : ((ℤ → ℝ) × (ℤ → ℝ)) ×
        ({j : Class // j ≠ i} → StationaryPoissonWorkPath) =>
        (multiclassStationaryPoissonWorkRestPastCanonicalInput i z.2,
          Probability.PoissonProcess.candidatePastMarkedInput z.1))
      (tagged.Ptag.prod passive.Pbase) ((Measure.pi νrest).prod (ν i)) := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_swap (μ := ν i) (ν := Measure.pi νrest)).comp
        (hselected.prod hpassive)
  have hjoin := (Probability.piWithoutCoordinate_measurePreserving ν i).symm.comp hsplit
  simpa [tagged, passive, multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput,
    Function.comp_def] using hjoin

/-- The collision-free canonical arrival law transported to the full
class-selected Palm input. -/
theorem ae_multiclassStationaryPoissonWorkClassTaggedPastCanonicalArrivalTime_eq_iff
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ firstClass secondClass : Class, ∀ firstIndex secondIndex : ℕ,
        Probability.PoissonProcess.arrivalTime firstIndex
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i z firstClass).1 =
          Probability.PoissonProcess.arrivalTime secondIndex
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i z secondClass).1 →
          firstClass = secondClass ∧ firstIndex = secondIndex := by
  let selected := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i
  have hmap := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
    (Class := Class) arrivalRate harrivalRate i
  refine MeasureTheory.ae_of_ae_map
    (μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
    (f := selected)
    (p := fun past => ∀ firstClass secondClass : Class, ∀ firstIndex secondIndex : ℕ,
      Probability.PoissonProcess.arrivalTime firstIndex (past firstClass).1 =
          Probability.PoissonProcess.arrivalTime secondIndex (past secondClass).1 →
        firstClass = secondClass ∧ firstIndex = secondIndex)
    hmap.measurable.aemeasurable ?_
  rw [hmap.map_eq]
  exact ae_multiclassCanonicalPastArrivalTime_eq_iff arrivalRate harrivalRate

/-- The passive coordinates of a selected-arrival input satisfy their
finite-window stationary-index reconciliations almost surely. -/
theorem ae_multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (horizon : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood i horizon z := by
  classical
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let μ : {j : Class // j ≠ i} → Measure StationaryPoissonWorkPath := fun j =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate j.1)
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hpassivePi : ∀ᵐ w ∂Measure.pi μ,
      ∀ j : {j : Class // j ≠ i},
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (w j).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (w j)).1 := by
    rw [ae_all_iff]
    intro j
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval j)
      (p := fun w : StationaryPoissonWorkPath =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 w.1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium w).1)
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        (fun j : {j : Class // j ≠ i} => arrivalRate j.1)
        (fun j => harrivalRate j.1) j).measurable.aemeasurable ?_
    have hmap : Measure.map (Function.eval j) (Measure.pi μ) =
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j.1) := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          (fun j : {j : Class // j ≠ i} => arrivalRate j.1)
          (fun j => harrivalRate j.1) j).map_eq
    rw [hmap]
    exact
      Probability.Queueing.ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
        (harrivalRate j.1) horizon
  have hpassiveBase : ∀ᵐ w ∂passive.Pbase,
      ∀ j : {j : Class // j ≠ i},
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (w j).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (w j)).1 := by
    simpa only [passive, multiclassStationaryPoissonWorkRestLaw,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkShiftInvariantLaw,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
      hpassivePi
  have hpassive : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
      ∀ j : {j : Class // j ≠ i},
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (z.2 j).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (z.2 j)).1 := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.snd)
      (p := fun w => ∀ j : {j : Class // j ≠ i},
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (w j).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (w j)).1)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpassiveBase
  change ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
    multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood i horizon z
  simpa only [multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood] using
    hpassive

/-- The complete canonical strict past at a selected class arrival has the
same law as the complete canonical strict past at a stationary time origin.
This is the input-level PASTA transport that later queue-state replay lemmas
may consume; it neither assumes nor concludes an equality for the nonlinear
remote-past queue selector. -/
theorem multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_hasLaw_stationary
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    HasLaw (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i)
      (Measure.map (multiclassStationaryPoissonWorkPastCanonicalInput (Class := Class))
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)
  let stationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
    arrivalRate
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Class)
  let selected := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput i
  have hselected :=
    multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
      arrivalRate harrivalRate i
  have hstationary := multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
    (Class := Class) arrivalRate harrivalRate
  refine ⟨hselected.measurable.aemeasurable, ?_⟩
  change Measure.map selected tagged.Ptag = Measure.map canonical stationary
  exact hselected.map_eq.trans hstationary.map_eq.symm

end

end AppliedModelingLib.Queueing

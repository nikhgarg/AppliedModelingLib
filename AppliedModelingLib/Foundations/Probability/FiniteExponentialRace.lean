import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalNonexplosion
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import AppliedModelingLib.Foundations.Probability.Weighted

/-!
# Finite exponential-race event streams

This module gives the canonical event-clock representation of a finite race of
independent exponential clocks.  A race event consists of an exponential gap
at the total rate and a winner label sampled with probability proportional to
its rate.  The pairs are IID, so every total event-index prefix stop has a
fresh suffix with the same joint law.

The module constructs and analyses the total-clock/winner-label model itself.
A separate superposition bridge is required when a consumer starts from
individually presented Poisson paths.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

variable {Label : Type*} [Fintype Label] [MeasurableSpace Label]
  [MeasurableSingletonClass Label]

/-- The total rate of a finite family of exponential clocks. -/
def finiteExponentialRaceTotalRate (rate : Label → ℝ) : ℝ :=
  ∑ label, rate label

/-- The winner-label distribution in a finite exponential race. -/
noncomputable def finiteExponentialRaceLabelPMF
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) : PMF Label :=
  finiteWeightedPMF rate hnonneg (by
    simpa [finiteExponentialRaceTotalRate] using htotal)

/-- The law of one total-clock gap together with its winning label. -/
noncomputable def finiteExponentialRaceEventLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) : Measure (ℝ × Label) :=
  (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)).prod
    (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure

/-- One total-clock gap together with its winner label is a probability law. -/
theorem isProbabilityMeasure_finiteExponentialRaceEventLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) := by
  unfold finiteExponentialRaceEventLaw
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure htotal
  letI : IsProbabilityMeasure
      (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure := by
    infer_instance
  infer_instance

/-- The canonical IID event stream for a finite exponential race. -/
noncomputable def finiteExponentialRaceEventMeasure
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) : Measure (ℕ → ℝ × Label) :=
  IIDStream.measure (finiteExponentialRaceEventLaw rate hnonneg htotal)

/-- The `index`th total-clock gap and winner label. -/
def finiteExponentialRaceEvent
    (index : ℕ) : (ℕ → ℝ × Label) → ℝ × Label :=
  IIDStream.coordinate index

/-- The total-clock gap at a given event index. -/
def finiteExponentialRaceGap (index : ℕ) : (ℕ → ℝ × Label) → ℝ :=
  fun path => (finiteExponentialRaceEvent (Label := Label) index path).1

/-- The winner label at a given event index. -/
def finiteExponentialRaceWinner (index : ℕ) : (ℕ → ℝ × Label) → Label :=
  fun path => (finiteExponentialRaceEvent (Label := Label) index path).2

/-- The interarrival path obtained by retaining the total-clock gap at every
event. -/
def finiteExponentialRaceGapPath : (ℕ → ℝ × Label) → ℕ → ℝ :=
  fun path index => finiteExponentialRaceGap (Label := Label) index path

/-- The winning-label path of the finite race. -/
def finiteExponentialRaceWinnerPath : (ℕ → ℝ × Label) → ℕ → Label :=
  fun path index => finiteExponentialRaceWinner (Label := Label) index path

/-- Split a finite-race event path into its total-gap and winner-label paths. -/
def finiteExponentialRaceGapWinnerPaths :
    (ℕ → ℝ × Label) → (ℕ → ℝ) × (ℕ → Label) :=
  fun path => (finiteExponentialRaceGapPath (Label := Label) path,
    finiteExponentialRaceWinnerPath (Label := Label) path)

/-- Split a finite-race event path in label-then-gap order. -/
def finiteExponentialRaceWinnerGapPaths :
    (ℕ → ℝ × Label) → (ℕ → Label) × (ℕ → ℝ) :=
  fun path => (finiteExponentialRaceWinnerPath (Label := Label) path,
    finiteExponentialRaceGapPath (Label := Label) path)

/-- The `index`th epoch of the total event clock. -/
def finiteExponentialRaceArrivalTime (index : ℕ) : (ℕ → ℝ × Label) → ℝ :=
  fun path => PoissonProcess.arrivalTime index
    (finiteExponentialRaceGapPath (Label := Label) path)

/-- One race event has exactly the product of its total-gap and winner-label
laws. -/
theorem finiteExponentialRaceEvent_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) (index : ℕ) :
    HasLaw (finiteExponentialRaceEvent (Label := Label) index)
      (finiteExponentialRaceEventLaw rate hnonneg htotal)
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  exact IIDStream.coordinate_hasLaw
    (finiteExponentialRaceEventLaw rate hnonneg htotal) index

/-- The finite race's total event stream is a probability law. -/
theorem isProbabilityMeasure_finiteExponentialRaceEventMeasure
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    IsProbabilityMeasure (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  dsimp [finiteExponentialRaceEventMeasure, IIDStream.measure]
  infer_instance

/-- The total-clock coordinate of one event has the exponential law at the
sum of the component rates. -/
theorem finiteExponentialRaceGap_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) (index : ℕ) :
    HasLaw (finiteExponentialRaceGap (Label := Label) index)
      (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  refine ⟨?_, ?_⟩
  · simpa [finiteExponentialRaceGap, finiteExponentialRaceEvent] using
      (measurable_fst.comp (IIDStream.measurable_coordinate (α := ℝ × Label) index)).aemeasurable
  · change Measure.map (Prod.fst ∘ IIDStream.coordinate index)
      (IIDStream.measure (finiteExponentialRaceEventLaw rate hnonneg htotal)) = _
    rw [← Measure.map_map measurable_fst (IIDStream.measurable_coordinate index),
      (IIDStream.coordinate_hasLaw
        (finiteExponentialRaceEventLaw rate hnonneg htotal) index).map_eq]
    change Measure.map Prod.fst
      ((ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)).prod
        (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure) = _
    rw [Measure.map_fst_prod]
    simp

/-- The winner-label coordinate of one event has the normalized rate law. -/
theorem finiteExponentialRaceWinner_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) (index : ℕ) :
    HasLaw (finiteExponentialRaceWinner (Label := Label) index)
      (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure htotal
  refine ⟨?_, ?_⟩
  · simpa [finiteExponentialRaceWinner, finiteExponentialRaceEvent] using
      (measurable_snd.comp (IIDStream.measurable_coordinate (α := ℝ × Label) index)).aemeasurable
  · change Measure.map (Prod.snd ∘ IIDStream.coordinate index)
      (IIDStream.measure (finiteExponentialRaceEventLaw rate hnonneg htotal)) = _
    rw [← Measure.map_map measurable_snd (IIDStream.measurable_coordinate index),
      (IIDStream.coordinate_hasLaw
        (finiteExponentialRaceEventLaw rate hnonneg htotal) index).map_eq]
    change Measure.map Prod.snd
      ((ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)).prod
        (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure) = _
    rw [Measure.map_snd_prod]
    simp

/-- The probability of a particular winner is its rate divided by the total
rate. -/
theorem finiteExponentialRaceWinner_probability
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) (label : Label) :
    (finiteExponentialRaceLabelPMF rate hnonneg htotal label).toReal =
      rate label / finiteExponentialRaceTotalRate rate := by
  simpa [finiteExponentialRaceLabelPMF, finiteExponentialRaceTotalRate] using
    (finiteWeightedPMF_apply_toReal rate hnonneg
      htotal label)

/-- The whole total-gap path is Borel measurable. -/
theorem measurable_finiteExponentialRaceGapPath :
    Measurable (finiteExponentialRaceGapPath (Label := Label)) := by
  apply measurable_pi_lambda
  intro index
  simpa [finiteExponentialRaceGapPath, finiteExponentialRaceGap,
    finiteExponentialRaceEvent] using
    (measurable_fst.comp (IIDStream.measurable_coordinate (α := ℝ × Label) index))

/-- The complete winning-label path is Borel measurable. -/
theorem measurable_finiteExponentialRaceWinnerPath :
    Measurable (finiteExponentialRaceWinnerPath (Label := Label)) := by
  apply measurable_pi_lambda
  intro index
  simpa [finiteExponentialRaceWinnerPath, finiteExponentialRaceWinner,
    finiteExponentialRaceEvent] using
    (measurable_snd.comp (IIDStream.measurable_coordinate (α := ℝ × Label) index))

/-- Splitting a finite-race event path into gaps and labels is Borel. -/
theorem measurable_finiteExponentialRaceGapWinnerPaths :
    Measurable (finiteExponentialRaceGapWinnerPaths (Label := Label)) :=
  measurable_finiteExponentialRaceGapPath.prodMk
    measurable_finiteExponentialRaceWinnerPath

/-- Splitting a finite-race event path in label-then-gap order is Borel. -/
theorem measurable_finiteExponentialRaceWinnerGapPaths :
    Measurable (finiteExponentialRaceWinnerGapPaths (Label := Label)) :=
  measurable_finiteExponentialRaceWinnerPath.prodMk
    measurable_finiteExponentialRaceGapPath

/-- The total-gap coordinates of a finite race are mutually independent. -/
theorem iIndepFun_finiteExponentialRaceGap
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    iIndepFun (finiteExponentialRaceGap (Label := Label))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  simpa [finiteExponentialRaceGap, finiteExponentialRaceEvent, Function.comp_def] using
    (IIDStream.iIndepFun_coordinate
      (finiteExponentialRaceEventLaw rate hnonneg htotal)).comp
      (fun _ => Prod.fst) (fun _ => measurable_fst)

/-- The winning labels of a finite race are mutually independent. -/
theorem iIndepFun_finiteExponentialRaceWinner
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    iIndepFun (finiteExponentialRaceWinner (Label := Label))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  simpa [finiteExponentialRaceWinner, finiteExponentialRaceEvent, Function.comp_def] using
    (IIDStream.iIndepFun_coordinate
      (finiteExponentialRaceEventLaw rate hnonneg htotal)).comp
      (fun _ => Prod.snd) (fun _ => measurable_snd)

/-- Retaining the total gaps turns the race into the canonical exponential
renewal path at the total rate. -/
theorem finiteExponentialRaceGapPath_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    HasLaw (finiteExponentialRaceGapPath (Label := Label))
      (PoissonProcess.exponentialInterarrivalMeasure
        (finiteExponentialRaceTotalRate rate))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure htotal
  letI : IsProbabilityMeasure (finiteExponentialRaceEventMeasure rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventMeasure rate hnonneg htotal
  refine ⟨measurable_finiteExponentialRaceGapPath.aemeasurable, ?_⟩
  change Measure.map (fun path index => finiteExponentialRaceGap index path)
    (finiteExponentialRaceEventMeasure rate hnonneg htotal) = _
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun index => by
      simpa [finiteExponentialRaceGapPath] using
        (measurable_fst.comp
          (IIDStream.measurable_coordinate (α := ℝ × Label) index))) |>.mp
      (iIndepFun_finiteExponentialRaceGap rate hnonneg htotal)]
  simp only [PoissonProcess.exponentialInterarrivalMeasure]
  congr 1
  funext index
  exact (finiteExponentialRaceGap_hasLaw rate hnonneg htotal index).map_eq

/-- Retaining the winning labels gives the canonical IID label path with the
normalized rate law. -/
theorem finiteExponentialRaceWinnerPath_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    HasLaw (finiteExponentialRaceWinnerPath (Label := Label))
      (IIDStream.measure (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure)
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  letI : IsProbabilityMeasure (finiteExponentialRaceEventMeasure rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventMeasure rate hnonneg htotal
  refine ⟨measurable_finiteExponentialRaceWinnerPath.aemeasurable, ?_⟩
  change Measure.map (fun path index => finiteExponentialRaceWinner index path)
    (finiteExponentialRaceEventMeasure rate hnonneg htotal) = _
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun index => by
      simpa [finiteExponentialRaceWinner] using
        (measurable_snd.comp
          (IIDStream.measurable_coordinate (α := ℝ × Label) index))) |>.mp
      (iIndepFun_finiteExponentialRaceWinner rate hnonneg htotal)]
  congr 1
  funext index
  exact (finiteExponentialRaceWinner_hasLaw rate hnonneg htotal index).map_eq

/-- The total-gap path and winning-label path of a finite exponential race are
jointly a product of their canonical IID laws. -/
theorem finiteExponentialRaceGapWinnerPaths_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    HasLaw (finiteExponentialRaceGapWinnerPaths (Label := Label))
      ((IIDStream.measure
        (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate))).prod
        (IIDStream.measure (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)
  let ν : Measure Label := (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure htotal
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  refine ⟨measurable_finiteExponentialRaceGapWinnerPaths.aemeasurable, ?_⟩
  change Measure.map (finiteExponentialRaceGapWinnerPaths (Label := Label))
      (IIDStream.measure (μ.prod ν)) = (IIDStream.measure μ).prod (IIDStream.measure ν)
  have hzip : HasLaw (IIDStream.zip (α := ℝ) (β := Label))
      (IIDStream.measure (μ.prod ν)) ((IIDStream.measure μ).prod (IIDStream.measure ν)) :=
    IIDStream.zip_hasLaw μ ν
  rw [← hzip.map_eq, Measure.map_map
    measurable_finiteExponentialRaceGapWinnerPaths IIDStream.measurable_zip]
  change Measure.map
    (finiteExponentialRaceGapWinnerPaths (Label := Label) ∘
      IIDStream.zip (α := ℝ) (β := Label)) ((IIDStream.measure μ).prod (IIDStream.measure ν)) = _
  convert Measure.map_id using 1

/-- The winning-label path and total-gap path are jointly a product of their
canonical IID laws, in label-then-gap order. -/
theorem finiteExponentialRaceWinnerGapPaths_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    HasLaw (finiteExponentialRaceWinnerGapPaths (Label := Label))
      ((IIDStream.measure (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure).prod
        (IIDStream.measure
          (ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate))))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (finiteExponentialRaceTotalRate rate)
  let ν : Measure Label := (finiteExponentialRaceLabelPMF rate hnonneg htotal).toMeasure
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure htotal
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure μ) := by
    dsimp [IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure ν) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hswap : HasLaw (Prod.swap : (ℕ → ℝ) × (ℕ → Label) →
      (ℕ → Label) × (ℕ → ℝ))
      ((IIDStream.measure ν).prod (IIDStream.measure μ))
      ((IIDStream.measure μ).prod (IIDStream.measure ν)) :=
    (Measure.measurePreserving_swap
      (μ := IIDStream.measure μ) (ν := IIDStream.measure ν)).hasLaw
  simpa [finiteExponentialRaceWinnerGapPaths,
    finiteExponentialRaceGapWinnerPaths, Function.comp_def] using
    hswap.comp (finiteExponentialRaceGapWinnerPaths_hasLaw rate hnonneg htotal)

/-- The finite race has only finitely many events by every finite physical
time, almost surely. -/
theorem ae_finiteExponentialRaceArrivalTime_tendsto_atTop
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate) :
    ∀ᵐ path ∂finiteExponentialRaceEventMeasure rate hnonneg htotal,
      Tendsto (fun index => finiteExponentialRaceArrivalTime (Label := Label) index path)
        atTop atTop := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  have hmeas : AEMeasurable (finiteExponentialRaceGapPath (Label := Label))
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) :=
    measurable_finiteExponentialRaceGapPath.aemeasurable
  have hset : MeasurableSet {path : ℕ → ℝ |
      Tendsto (fun index => PoissonProcess.arrivalTime index path) atTop atTop} :=
    measurableSet_tendsto atTop
      (fun index => PoissonProcess.measurable_arrivalTime index)
  change ∀ᵐ path ∂finiteExponentialRaceEventMeasure rate hnonneg htotal,
    Tendsto (fun index => PoissonProcess.arrivalTime index
      (finiteExponentialRaceGapPath (Label := Label) path)) atTop atTop
  rw [← MeasureTheory.ae_map_iff hmeas hset,
    (finiteExponentialRaceGapPath_hasLaw rate hnonneg htotal).map_eq]
  exact PoissonProcess.ae_arrivalTime_tendsto_atTop htotal

/-- A total event-index prefix stop leaves the entire uninspected
total-gap/winner-label suffix with its original IID law. -/
theorem finiteExponentialRace_postTail_hasLaw
    (rate : Label → ℝ) (hnonneg : ∀ label, 0 ≤ rate label)
    (htotal : 0 < finiteExponentialRaceTotalRate rate)
    (stop : IIDStream.PrefixStoppingIndex (α := ℝ × Label)) :
    HasLaw stop.postTail
      (finiteExponentialRaceEventMeasure rate hnonneg htotal)
      (finiteExponentialRaceEventMeasure rate hnonneg htotal) := by
  letI : IsProbabilityMeasure (finiteExponentialRaceEventLaw rate hnonneg htotal) :=
    isProbabilityMeasure_finiteExponentialRaceEventLaw rate hnonneg htotal
  simpa [finiteExponentialRaceEventMeasure] using
    (IIDStream.PrefixStoppingIndex.postTail_hasLaw
      (finiteExponentialRaceEventLaw rate hnonneg htotal) stop)

/-- At a total event-index prefix stop, every later physical event epoch is
the stopped epoch plus the corresponding epoch of the fresh total-clock
suffix. -/
theorem finiteExponentialRaceArrivalTime_postTail
    (stop : IIDStream.PrefixStoppingIndex (α := ℝ × Label))
    (path : ℕ → ℝ × Label) (index : ℕ) :
    finiteExponentialRaceArrivalTime (Label := Label) (stop path + 1 + index) path =
      finiteExponentialRaceArrivalTime (Label := Label) (stop path) path +
        finiteExponentialRaceArrivalTime (Label := Label) index (stop.postTail path) := by
  change (∑ i ∈ Finset.range (stop path + 1 + index + 1),
      finiteExponentialRaceGap i path) =
    (∑ i ∈ Finset.range (stop path + 1), finiteExponentialRaceGap i path) +
      ∑ i ∈ Finset.range (index + 1), finiteExponentialRaceGap i (stop.postTail path)
  rw [show stop path + 1 + index + 1 = (stop path + 1) + (index + 1) by omega,
    Finset.sum_range_add]
  congr 1

end

end AppliedModelingLib.Probability

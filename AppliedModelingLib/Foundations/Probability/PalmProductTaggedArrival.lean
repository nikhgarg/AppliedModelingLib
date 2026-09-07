import AppliedModelingLib.Foundations.Probability.PalmArrivalPath
import AppliedModelingLib.Foundations.Probability.Processes.Palm.QueueLengthPASTA
import AppliedModelingLib.Foundations.Probability.Processes.Markov.StationaryTrajectory

/-!
# Independent product extension of a tagged arrival path

This is a concrete product-space construction: a stationary base state is
paired independently with the existing two-sided exponential-gap tagged path.
It constructs a real tagged probability law and proves the queue-state PASTA
distributional equality by a product-marginal calculation.  It is *not* a
Campbell/Palm construction of that law from a stationary point process, and it
does not supply M/M/1 queue dynamics or a real-time state/arrival coupling.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The trajectory-measure probability instance is available after unfolding the local wrapper. -/
instance stationaryTrajMeasure.isProbabilityMeasure
    {α : Type*} [MeasurableSpace α] {π : Measure α} [IsProbabilityMeasure π]
    {K : Kernel α α} [IsMarkovKernel K] :
    IsProbabilityMeasure (Queueing.stationaryTrajMeasure π K) := by
  unfold Queueing.stationaryTrajMeasure
  infer_instance

/-- Pair an arbitrary probability state law independently with the concrete two-sided
exponential-gap tagged path. -/
noncomputable def independentProductTaggedArrivalAtZero
    {Ω : Type*} [MeasurableSpace Ω] (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    (rate : ℝ) (hrate : 0 < rate) :
    Queueing.TaggedArrivalAtZero (Ω × (ℤ → ℝ)) where
  Ptag := Pstate.prod (twoSidedInterarrivalMeasure rate)
  isProbability := by
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    infer_instance
  arrivals := fun x => candidatePalmArrival x.2
  tag_at_zero := by
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    refine ae_of_ae_map (μ := Pstate.prod (twoSidedInterarrivalMeasure rate))
      (f := Prod.snd) (p := fun g : ℤ → ℝ => candidatePalmArrival g 0 = 0)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_candidatePalmArrival_tag_at_zero
  arrivals_strict := by
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    refine ae_of_ae_map (μ := Pstate.prod (twoSidedInterarrivalMeasure rate))
      (f := Prod.snd) (p := fun g : ℤ → ℝ => StrictMono (candidatePalmArrival g))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_candidatePalmArrival_strictMono hrate

/-- The state coordinate of the independent product tagged law retains its original marginal. -/
theorem independentProductTaggedArrivalAtZero_map_state
    {Ω : Type*} [MeasurableSpace Ω] (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    (rate : ℝ) (hrate : 0 < rate) :
    (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag.map Prod.fst = Pstate := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  change (Pstate.prod (twoSidedInterarrivalMeasure rate)).map Prod.fst = Pstate
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The gap coordinate of the independent product tagged law retains the candidate tagged-gap
law. -/
theorem independentProductTaggedArrivalAtZero_map_gaps
    {Ω : Type*} [MeasurableSpace Ω] (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    (rate : ℝ) (hrate : 0 < rate) :
    (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag.map Prod.snd =
      twoSidedInterarrivalMeasure rate := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  change (Pstate.prod (twoSidedInterarrivalMeasure rate)).map Prod.snd =
    twoSidedInterarrivalMeasure rate
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Each tagged gap in the product construction retains the exponential law. -/
theorem independentProductTaggedArrivalAtZero_gap_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    (rate : ℝ) (hrate : 0 < rate) (i : ℤ) :
    HasLaw (fun x : Ω × (ℤ → ℝ) => twoSidedGap i x.2)
      (ProbabilityTheory.expMeasure rate)
      (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag := by
  refine ⟨((measurable_twoSidedGap i).comp measurable_snd).aemeasurable, ?_⟩
  change (Pstate.prod (twoSidedInterarrivalMeasure rate)).map
      (fun x : Ω × (ℤ → ℝ) => twoSidedGap i x.2) = ProbabilityTheory.expMeasure rate
  calc
    (Pstate.prod (twoSidedInterarrivalMeasure rate)).map
        (fun x : Ω × (ℤ → ℝ) => twoSidedGap i x.2) =
        ((Pstate.prod (twoSidedInterarrivalMeasure rate)).map Prod.snd).map
          (twoSidedGap i) := by
      symm
      simpa [Function.comp_def] using
        (Measure.map_map (μ := Pstate.prod (twoSidedInterarrivalMeasure rate))
          (measurable_twoSidedGap i) measurable_snd)
    _ = (twoSidedInterarrivalMeasure rate).map (twoSidedGap i) := by
      letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
        isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = ProbabilityTheory.expMeasure rate := (twoSidedGap_hasLaw hrate i).map_eq

/-- Any measurable base-state statistic has its original law under the product tagged measure. -/
theorem independentProductTaggedArrivalAtZero_stateStatistic_hasLaw
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    (stateStatistic : Ω → β) (hstateStatistic : Measurable stateStatistic)
    (rate : ℝ) (hrate : 0 < rate) :
    HasLaw (fun x : Ω × (ℤ → ℝ) => stateStatistic x.1)
      (Pstate.map stateStatistic)
      (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag := by
  refine ⟨(hstateStatistic.comp measurable_fst).aemeasurable, ?_⟩
  change (Pstate.prod (twoSidedInterarrivalMeasure rate)).map
      (fun x : Ω × (ℤ → ℝ) => stateStatistic x.1) = Pstate.map stateStatistic
  calc
    (Pstate.prod (twoSidedInterarrivalMeasure rate)).map
        (fun x : Ω × (ℤ → ℝ) => stateStatistic x.1) =
        ((Pstate.prod (twoSidedInterarrivalMeasure rate)).map Prod.fst).map
          stateStatistic := by
      symm
      simpa [Function.comp_def] using
        (Measure.map_map (μ := Pstate.prod (twoSidedInterarrivalMeasure rate))
          hstateStatistic measurable_fst)
    _ = Pstate.map stateStatistic := by
      letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
        isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
      rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- A measurable base-state statistic is independent of every tagged gap coordinate in the
independent product construction. -/
theorem independentProductTaggedArrivalAtZero_stateStatistic_indep_gap
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    (stateStatistic : Ω → β) (hstateStatistic : Measurable stateStatistic)
    (rate : ℝ) (hrate : 0 < rate) (i : ℤ) :
    IndepFun (fun x : Ω × (ℤ → ℝ) => stateStatistic x.1)
      (fun x => twoSidedGap i x.2)
      (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  change IndepFun (fun x : Ω × (ℤ → ℝ) => stateStatistic x.1)
    (fun x => twoSidedGap i x.2) (Pstate.prod (twoSidedInterarrivalMeasure rate))
  exact indepFun_prod hstateStatistic (measurable_twoSidedGap i)

/-- A stationary embedded-chain coordinate can be adjoined to the concrete tagged arrival path
while retaining its invariant marginal.  This is a genuine joint probability law, but the
construction is independent and does not identify the chain's discrete index with real time. -/
theorem independentProductTaggedArrivalAtZero_stationaryTrajectory_coordinate_hasLaw
    {α : Type*} [MeasurableSpace α] {π : Measure α} [IsProbabilityMeasure π]
    {K : Kernel α α} [IsMarkovKernel K] (hstationary : Kernel.Invariant K π)
    (n : ℕ) (rate : ℝ) (hrate : 0 < rate) :
    HasLaw (fun x : (ℕ → α) × (ℤ → ℝ) => x.1 n) π
      (independentProductTaggedArrivalAtZero (Queueing.stationaryTrajMeasure π K) rate hrate).Ptag := by
  have h := independentProductTaggedArrivalAtZero_stateStatistic_hasLaw
    (Queueing.stationaryTrajMeasure π K) (fun x : ℕ → α => x n) (measurable_pi_apply n) rate hrate
  refine ⟨h.aemeasurable, ?_⟩
  exact h.map_eq.trans (Queueing.stationaryTrajMeasure_marginal hstationary n)

end

end AppliedModelingLib.Probability.PoissonProcess

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A concrete PASTA queue-state certificate obtained by independently adjoining the existing
two-sided tagged arrival path to a supplied stationary base state law.

The equality in this certificate is a genuine product-measure theorem.  It is
not evidence that this product law is the Palm transform of `base`; a
Campbell/Palm identity and queue dynamics remain separate obligations. -/
noncomputable def independentProductPalmPASTAQueueLengthCertificate
    {Ω : Type*} [MeasurableSpace Ω]
    (base : ShiftInvariantProbabilityLaw Ω) [IsProbabilityMeasure base.Pbase]
    (stationaryQueueLength : Ω → ℕ) (hstationaryQueueLength : Measurable stationaryQueueLength)
    (rate : ℝ) (hrate : 0 < rate) :
    PalmPASTAQueueLengthCertificate Ω (Ω × (ℤ → ℝ)) base
      (PoissonProcess.independentProductTaggedArrivalAtZero base.Pbase rate hrate) where
  stationaryQueueLength := stationaryQueueLength
  preArrivalQueueLength := fun x => stationaryQueueLength x.1
  stationaryQueueLength_measurable := hstationaryQueueLength
  preArrivalQueueLength_measurable := hstationaryQueueLength.comp measurable_fst
  pasta_queue_length :=
    PoissonProcess.independentProductTaggedArrivalAtZero_stateStatistic_hasLaw
      base.Pbase stationaryQueueLength hstationaryQueueLength rate hrate

end

end AppliedModelingLib.Probability.Palm

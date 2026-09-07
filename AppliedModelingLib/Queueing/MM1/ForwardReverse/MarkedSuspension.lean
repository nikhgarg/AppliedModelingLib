import AppliedModelingLib.Queueing.MM1.TwoSided.MarkedFactor
import AppliedModelingLib.Queueing.MM1.TwoSided.ReverseTrajectory
import AppliedModelingLib.Foundations.Probability.Processes.Palm.SelectedMarkedTransport
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Campbell
import Mathlib.Tactic

/-!
# Stationarity-facing forward/reverse marked M/M/1 suspension

This module uses the forward/reverse two-sided trajectory construction as the
stationarity-facing M/M/1 carrier. For the reversible uniformized M/M/1
kernel, detailed balance supplies its reverse-pair balance with the same
kernel in both directions. Edge marking is then deterministic and compatible
with integer relabeling, so any full unmarked shift theorem immediately gives
a full marked shift theorem and, through the Poisson suspension, a stationary
real-time law.

The generic construction is deliberately conditional on that still-open full
integer-shift theorem. It proves neither marked thinning, a Palm tag, PASTA,
nor a response-time statement.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

/-- The forward/reverse two-sided uniformized M/M/1 queue-length path. This
is the construction to which the generic reverse-pair finite-window proof
applies directly. -/
noncomputable def geoNNPMF_uniformized_forwardReverseTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) : Measure (ℤ → ℕ) :=
  forwardReverseTwoSidedTrajMeasure
    (geoNNPMF rho hrho).toMeasure
    (countablePMFKernel
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))
    (countablePMFKernel
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))

/-- The forward/reverse two-sided uniformized M/M/1 queue-length path is a
probability law. -/
theorem isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) :
    IsProbabilityMeasure (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel
    (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho))
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  let M : Measure (ℤ → ℕ) := forwardReverseTwoSidedTrajMeasure π K K
  have hMprob : IsProbabilityMeasure M := by
    let S : Measure ((ℕ → ℕ) × (ℕ → ℕ)) :=
      forwardReverseTwoSidedSourceMeasure π K K
    have hSprob : IsProbabilityMeasure S := by
      dsimp [S, forwardReverseTwoSidedSourceMeasure]
      letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
        unfold stationaryTrajMeasure
        infer_instance
      infer_instance
    letI : IsProbabilityMeasure S := hSprob
    change IsProbabilityMeasure (S.map spliceForwardReverse)
    exact Measure.isProbabilityMeasure_map measurable_spliceForwardReverse.aemeasurable
  exact hMprob

/-- Detailed balance specializes the generic reverse-pair compatibility to
the forward/reverse M/M/1 path with the same kernel in both directions. -/
theorem geoNNPMF_uniformized_forwardReverse_reversePairBalance
    (rho : ℝ≥0) (hrho : rho < 1) :
    Kernel.ReversePairBalance
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))) := by
  exact (geoNNPMF_detailedBalance rho hrho).compProd_swap

/-- The stationarity-facing two-sided path with a deterministic current-edge
arrival/potential-service mark. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) : Measure (ℤ → (ℕ × Bool)) :=
  (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho).map edgeMarkedPath

/-- The forward/reverse marked path conditioned on an arrival mark at its
embedded origin. This is the correct candidate embedded selected-event law;
identifying it with a real-time Palm law still requires the marked Campbell
transport. -/
noncomputable def geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) : Measure (ℤ → (ℕ × Bool)) :=
  (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)[|
    {x | (x 0).2 = true}]

/-- The forward/reverse edge-marked M/M/1 trajectory is a probability law. -/
theorem isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) :
    IsProbabilityMeasure (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let M : Measure (ℤ → ℕ) := geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  letI : IsProbabilityMeasure M :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  change IsProbabilityMeasure (M.map edgeMarkedPath)
  exact Measure.isProbabilityMeasure_map measurable_edgeMarkedPath.aemeasurable

/-- The time-zero state/current-mark coordinate has the geometric/Bernoulli
product law on the stationarity-facing forward/reverse path. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw (fun x : ℤ → (ℕ × Bool) => x 0)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel
    (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho))
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  let M : Measure (ℤ → ℕ) := forwardReverseTwoSidedTrajMeasure π K K
  let f : (ℤ → ℕ) → ℕ × Bool := fun x => edgeMarkedPath x 0
  have hf : Measurable f := by
    change Measurable (fun x : ℤ → ℕ =>
      markedEdgeProjection (x 0, x (0 + 1)))
    exact measurable_markedEdgeProjection.comp
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply (0 + 1)))
  have hpair : M.map (fun x => (x 0, x (1 : ℤ))) = π ⊗ₘ K := by
    exact forwardReverseTwoSidedTrajMeasure_zeroOnePair
      (geoNNPMF_uniformized_kernelInvariant rho hrho)
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  change Measure.map (fun x : ℤ → (ℕ × Bool) => x 0) (M.map edgeMarkedPath) = _
  calc
    Measure.map (fun x : ℤ → (ℕ × Bool) => x 0) (M.map edgeMarkedPath) =
        Measure.map f M := by
          rw [Measure.map_map (measurable_pi_apply 0) measurable_edgeMarkedPath]
          rfl
    _ = Measure.map markedEdgeProjection (M.map (fun x => (x 0, x (1 : ℤ)))) := by
          rw [Measure.map_map measurable_markedEdgeProjection
            ((measurable_pi_apply 0).prodMk (measurable_pi_apply (1 : ℤ)))]
          rfl
    _ = Measure.map markedEdgeProjection (π ⊗ₘ K) := by rw [hpair]
    _ = _ := by
      exact map_markedEdgeProjection_compProd_reflectedBirthDeathKernel π
        (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)

/-- Positivity of the arrival-mark event makes the embedded selected-event
law into a probability measure. -/
theorem isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1)
    (htrue : (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0) :
    IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure rho hrho) := by
  let M : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  letI : IsProbabilityMeasure M :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  have hmass : M {x | (x 0).2 = true} = B {true} := by
    simpa [M, B] using
      (measure_preState_ge_and_arrivalMark_eq_of_hasLaw
        (geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw rho hrho) 0)
  have hselected : M {x | (x 0).2 = true} ≠ 0 := by
    rw [hmass]
    exact htrue
  exact cond_isProbabilityMeasure hselected

/-- Under the embedded selected-event law, the pre-arrival queue state retains
the stationary geometric tail. This is a checked conditional embedded law,
not yet a real-time Palm/PASTA conclusion. -/
theorem geoNNPMF_uniformized_forwardReverseTrueMarkedTraj_state_tail
    (rho : ℝ≥0) (hrho : rho < 1)
    (htrue : (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0)
    (k : ℕ) :
    (geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure rho hrho)
        {x | k ≤ (x 0).1} =
      (geoNNPMF rho hrho).toMeasure {q | k ≤ q} := by
  letI : IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  unfold geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure
  exact cond_measure_preState_ge_eq_of_hasLaw (measurable_pi_apply 0)
    (geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw rho hrho)
    htrue k

/-- The full pre-arrival state marginal under the embedded true-mark
conditional path is the stationary geometric law. -/
theorem geoNNPMF_uniformized_forwardReverseTrueMarkedTraj_zero_state_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1)
    (htrue : (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0) :
    HasLaw (fun x : ℤ → (ℕ × Bool) => (x 0).1)
      (geoNNPMF rho hrho).toMeasure
      (geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure rho hrho) := by
  letI : IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  unfold geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure
  exact cond_state_hasLaw_of_stateMark_product (measurable_pi_apply 0)
    (geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw rho hrho)
    htrue

/-- Pair the conditional true-mark embedded path with an independent tagged
Poisson-gap path. This is a concrete tagged-arrival probability law; its
genuine real-time Palm provenance remains contingent on the marked all-event
Campbell transport. -/
noncomputable def geoNNPMF_uniformized_forwardReverseTrueMarkedTaggedArrivalAtZero
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (htrue : (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := by
  letI : IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure
      rho hrho htrue
  exact timedEmbeddedTaggedArrivalAtZero rate hrate
    (geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure rho hrho)

/-- The tagged conditional true-mark path has the stationary geometric
pre-arrival queue tail. This is a concrete tagged probability-space fact;
the later marked Campbell theorem is what will identify it as a Palm law. -/
theorem geoNNPMF_uniformized_forwardReverseTrueMarkedTaggedArrivalAtZero_preArrival_tail
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (htrue : (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0)
    (k : ℕ) :
    (geoNNPMF_uniformized_forwardReverseTrueMarkedTaggedArrivalAtZero
      hrate rho hrho htrue).Ptag {z | k ≤ (z.2 0).1} =
      (geoNNPMF rho hrho).toMeasure {q | k ≤ q} := by
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure P :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseTrueMarkedTrajMeasure
      rho hrho htrue
  have hpath := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    id measurable_id rate hrate
  have hstate : Measurable (fun x : ℤ → (ℕ × Bool) => (x 0).1) :=
    measurable_fst.comp (measurable_pi_apply 0)
  have hset : MeasurableSet {x : ℤ → (ℕ × Bool) | k ≤ (x 0).1} :=
    measurableSet_Ici.preimage hstate
  change (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      {z | k ≤ (z.2 0).1} = _
  calc
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
        {z | k ≤ (z.2 0).1} =
        Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => z.2)
          (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
          {x | k ≤ (x 0).1} := by
            rw [Measure.map_apply measurable_snd hset]
            rfl
    _ = P {x | k ≤ (x 0).1} := by
            have h := congrArg (fun μ : Measure (ℤ → (ℕ × Bool)) =>
              μ {x | k ≤ (x 0).1}) hpath.map_eq
            simpa using h
    _ = (geoNNPMF rho hrho).toMeasure {q | k ≤ q} := by
            exact geoNNPMF_uniformized_forwardReverseTrueMarkedTraj_state_tail
              rho hrho htrue k

/-- Full integer-shift preservation of the forward/reverse unmarked path
transfers to its deterministic edge-mark factor. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_intPathShift_measurePreserving_of_unmarked
    (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho))
    (k : ℤ) :
    MeasurePreserving (intPathShift k)
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  exact measurePreserving_intPathShift_map_of_commutes
    (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho) edgeMarkedPath
    measurable_edgeMarkedPath (fun j x => edgeMarkedPath_intPathShift j x) (hpath k)

/-- Couple the stationarity-facing marked M/M/1 path to the good Poisson
suspension. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure
    (rate : ℝ) (rho : ℝ≥0) (hrho : rho < 1) :
    Measure (GoodSuspensionState × (ℤ → (ℕ × Bool))) :=
  timedEmbeddedSuspensionProductMeasure rate
    (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)

/-- The stationary-suspension product retains the embedded time-zero
geometric/Bernoulli state-and-mark law. This is a coordinate marginal only;
it is not a Palm or thinning statement. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSuspension_zero_coordinate_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => z.2 0)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure rate rho hrho) := by
  let P : Measure GoodSuspensionState := goodSuspensionMeasure rate
  let Q : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let f : (ℤ → (ℕ × Bool)) → ℕ × Bool := fun x => x 0
  have hf : Measurable f := measurable_pi_apply 0
  have hlaw := geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw rho hrho
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : IsProbabilityMeasure Q :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  refine ⟨(hf.comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => f z.2)
      (P.prod Q) = _
  calc
    Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => f z.2)
        (P.prod Q) = Measure.map f (Measure.map Prod.snd (P.prod Q)) := by
          symm
          rw [Measure.map_map hf measurable_snd]
          rfl
    _ = Measure.map f Q := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = _ := hlaw.map_eq

/-- At embedded coordinate zero, the event of at least `k` jobs and an
arrival mark factors into its Bernoulli mark probability times the geometric
tail. This is not yet a real-time marked-point intensity or Palm identity. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSuspension_measure_state_ge_and_arrivalMark_eq
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) (k : ℕ) :
    (geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure rate rho hrho)
        {z | k ≤ (z.2 0).1 ∧ (z.2 0).2 = true} =
      (uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure {true} *
        (geoNNPMF rho hrho).toMeasure {q | k ≤ q} := by
  exact measure_preState_ge_and_arrivalMark_eq_of_hasLaw
    (geoNNPMF_uniformized_forwardReverseMarkedSuspension_zero_coordinate_hasLaw
      hrate rho hrho) k

/-- Package a full marked integer-shift theorem as a stationary real-time
forward/reverse M/M/1 suspension. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_intPathShift
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)) :
    Palm.ShiftInvariantProbabilityLaw (GoodSuspensionState × (ℤ → (ℕ × Bool))) := by
  letI : IsProbabilityMeasure (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  simpa only [geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure] using
    timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift hrate
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) hpath

/-- The full unmarked forward/reverse shift theorem therefore directly yields
the stationary real-time marked M/M/1 suspension required before the later
thinning and Palm layers. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)) :=
    geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_intPathShift
      hrate rho hrho
      (fun k =>
        geoNNPMF_uniformized_forwardReverseMarkedTraj_intPathShift_measurePreserving_of_unmarked
          rho hrho hpath k)

/-- The all-event tagged path law paired with the stationarity-facing
forward/reverse marked M/M/1 trajectory. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := by
  letI : IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  exact timedEmbeddedTaggedArrivalAtZero rate hrate
    (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)

/-- The generic product Campbell construction specializes directly to the
stationarity-facing forward/reverse marked M/M/1 trajectory. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedSuspensionCampbellCertificate_of_intPathShift
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_intPathShift
        hrate rho hrho hpath)
      (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho) := by
  letI : IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  simpa only [geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_intPathShift,
    geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero]
    using
      (timedEmbeddedCampbellCertificate_of_independentPath hrate
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) hpath)

/-- An unmarked full forward/reverse shift theorem transports through edge
marking and then instantiates the all-event marked Campbell certificate. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedSuspensionCampbellCertificate_of_unmarkedIntPathShift
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho hpath)
      (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho) := by
  letI : IsProbabilityMeasure
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let hmarked : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) :=
    fun k =>
      geoNNPMF_uniformized_forwardReverseMarkedTraj_intPathShift_measurePreserving_of_unmarked
        rho hrho hpath k
  simpa only [geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift]
    using
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionCampbellCertificate_of_intPathShift
        hrate rho hrho hmarked)

end

end AppliedModelingLib.Probability.Queueing

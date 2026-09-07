import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFixedReplayMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedServiceStartPredictability
import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedCoordinatePullback
import AppliedModelingLib.Foundations.Probability.EventuallyStableFiniteReplay
import Mathlib.Tactic

/-!
# Jointly Borel finite selected-priority replays

This module puts the finite selected/Palm replay on the product of its sample
carrier with a physical elapsed-time coordinate.  The construction keeps the
finite arrival ledger and the finite service skeleton explicit, so the joint
Borel assertion does not choose a remote-past representative.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The product carrier on which a selected/Palm sample is observed at an
elapsed physical time. -/
abbrev StationaryPriorityClassTaggedReplayProduct (i : Fin n) :=
  MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ

/-- Fixed selected/Palm job coordinates, pulled back to the sample-time
product carrier. -/
def stationaryPriorityClassTaggedProductFixedJobs
    (meanService : Fin n → ℝ) (i : Fin n)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    List (NonpreemptivePriorityFixedJobCoordinate
      (StationaryPriorityClassTaggedReplayProduct i)
      n (NonpreemptivePriorityArrivalIndex n)) :=
  labels.map fun q =>
    (stationaryPriorityClassTaggedFixedJobCoordinate meanService i q).pullback Prod.fst

/-- The product pullback of the fixed empty state at the left endpoint of a
finite selected replay. -/
def stationaryPriorityClassTaggedProductFixedPastInitial
    (i : Fin n) (older : ℝ) :
    NonpreemptivePriorityFixedStateCoordinate
      (StationaryPriorityClassTaggedReplayProduct i)
      n (NonpreemptivePriorityArrivalIndex n) :=
  (stationaryPriorityClassTaggedFixedPastInitial i older).pullback Prod.fst

/-- The static product coordinate after the historical finite ledger. -/
noncomputable def stationaryPriorityClassTaggedProductFixedPastAfterArrivals
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityArrivalTraceBranch
    (stationaryPriorityClassTaggedProductFixedPastInitial i older)
    (stationaryPriorityClassTaggedProductFixedJobs meanService i pastLabels)
    skeleton.pastArrivalSlots

/-- The static product coordinate after serving the finite historical ledger
through the selected arrival epoch. -/
noncomputable def stationaryPriorityClassTaggedProductFixedPastState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch (fun _ => 0)
    (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
      meanService i older pastLabels skeleton)
    skeleton.pastTerminalCompletionCount skeleton.pastTerminal

/-- The product coordinate immediately after admitting the selected customer. -/
noncomputable def stationaryPriorityClassTaggedProductFixedPostTagState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  NonpreemptivePriorityFixedStateCoordinate.admit
    (NonpreemptivePriorityFixedStateCoordinate.clearCompleted
      (stationaryPriorityClassTaggedProductFixedPastState
        meanService i older pastLabels skeleton))
    ((stationaryPriorityClassTaggedFixedJobCoordinate meanService i (Sigma.mk i 0)).pullback
      Prod.fst)

/-- The static product coordinate after the finite strict future ledger. -/
noncomputable def stationaryPriorityClassTaggedProductFixedPostFutureState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityArrivalTraceBranch
    (stationaryPriorityClassTaggedProductFixedPostTagState
      meanService i older pastLabels skeleton)
    (stationaryPriorityClassTaggedProductFixedJobs meanService i futureLabels)
    skeleton.futureArrivalSlots

/-- The static finite replay, advanced to the elapsed-time coordinate of the
product carrier. -/
noncomputable def stationaryPriorityClassTaggedProductFixedReplayState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch Prod.snd
    (stationaryPriorityClassTaggedProductFixedPostFutureState
      meanService i older pastLabels futureLabels skeleton)
    skeleton.futureTerminalCompletionCount skeleton.futureTerminal

/-- Fixed labelled jobs remain Borel after pulling the selected sample back
to the product carrier. -/
theorem stationaryPriorityClassTaggedProductFixedJobs_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    ∀ job ∈ stationaryPriorityClassTaggedProductFixedJobs meanService i labels,
      job.CoordinatesMeasurable := by
  intro job hjob
  rcases List.mem_map.mp hjob with ⟨label, _, rfl⟩
  exact (stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
    meanService i label).pullback Prod.fst measurable_fst

/-- Evaluating a product-pulled fixed label ledger yields the literal jobs of
the selected sample coordinate. -/
theorem eval_stationaryPriorityClassTaggedProductFixedJobs
    (meanService : Fin n → ℝ) (i : Fin n)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (p : StationaryPriorityClassTaggedReplayProduct i) :
    ((stationaryPriorityClassTaggedProductFixedJobs meanService i labels).map
      fun job => job.eval p) =
      labels.map fun q =>
        { identifier := q
          priority := q.1
          arrivalTime := stationaryPriorityClassTaggedArrival i p.1 q.1 q.2
          serviceWork := stationaryPriorityClassTaggedWorkRequirementAt
            meanService i p.1 q.1 q.2 } := by
  simp [stationaryPriorityClassTaggedProductFixedJobs,
    stationaryPriorityClassTaggedFixedJobCoordinate,
    NonpreemptivePriorityFixedJobCoordinate.pullback,
    NonpreemptivePriorityFixedJobCoordinate.eval, Function.comp_def]

/-- The fixed product empty state has Borel coordinates. -/
theorem stationaryPriorityClassTaggedProductFixedPastInitial_coordinatesMeasurable
    (i : Fin n) (older : ℝ) :
    (stationaryPriorityClassTaggedProductFixedPastInitial i older).CoordinatesMeasurable := by
  exact (emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable
    _ measurable_const).pullback Prod.fst measurable_fst

/-- The historical product replay state has Borel coordinates. -/
theorem stationaryPriorityClassTaggedProductFixedPastAfterArrivals_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable := by
  apply coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
  · exact stationaryPriorityClassTaggedProductFixedPastInitial_coordinatesMeasurable i older
  · exact stationaryPriorityClassTaggedProductFixedJobs_coordinatesMeasurable
      meanService i pastLabels

/-- The served historical product replay state has Borel coordinates. -/
theorem stationaryPriorityClassTaggedProductFixedPastState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedProductFixedPastState
      meanService i older pastLabels skeleton).CoordinatesMeasurable := by
  apply coordinatesMeasurable_runFixedPriorityAdvanceBranch
  · exact measurable_const
  · exact stationaryPriorityClassTaggedProductFixedPastAfterArrivals_coordinatesMeasurable
      meanService i older pastLabels skeleton

/-- The post-tag product replay state has Borel coordinates. -/
theorem stationaryPriorityClassTaggedProductFixedPostTagState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedProductFixedPostTagState
      meanService i older pastLabels skeleton).CoordinatesMeasurable := by
  apply NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.admit
  · exact NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.clearCompleted _
      (stationaryPriorityClassTaggedProductFixedPastState_coordinatesMeasurable
        meanService i older pastLabels skeleton)
  · exact (stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
      meanService i (Sigma.mk i 0)).pullback Prod.fst measurable_fst

/-- The pre-terminal product replay state has Borel coordinates. -/
theorem stationaryPriorityClassTaggedProductFixedPostFutureState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedProductFixedPostFutureState
      meanService i older pastLabels futureLabels skeleton).CoordinatesMeasurable := by
  apply coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
  · exact stationaryPriorityClassTaggedProductFixedPostTagState_coordinatesMeasurable
      meanService i older pastLabels skeleton
  · exact stationaryPriorityClassTaggedProductFixedJobs_coordinatesMeasurable
      meanService i futureLabels

/-- Every fixed selected replay skeleton is Borel jointly in the selected
sample and elapsed-time coordinates. -/
theorem stationaryPriorityClassTaggedProductFixedReplayState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedProductFixedReplayState
      meanService i older pastLabels futureLabels skeleton).CoordinatesMeasurable := by
  apply coordinatesMeasurable_runFixedPriorityAdvanceBranch
  · exact measurable_snd
  · exact stationaryPriorityClassTaggedProductFixedPostFutureState_coordinatesMeasurable
      meanService i older pastLabels futureLabels skeleton

/-- Membership of a fixed labelled future arrival in the strict ledger is
Borel jointly in the selected sample and elapsed horizon. -/
theorem measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_product
    (i : Fin n) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i p.1 p.2 q.1} := by
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    have hbase : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        (p.1.1.1, (0 : ℝ))) :=
      ((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk measurable_const
    have hcrossLeft : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed 0 (p.1.1.1, 0)) :=
      (Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed 0).comp hbase
    have hcrossRight : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed p.2 (p.1.1.1, 0)) :=
      Probability.PoissonProcess.measurable_uncurry_suspensionCrossingIndexPastClosed.comp
        (measurable_snd.prodMk hbase)
    have harrival : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        Probability.PoissonProcess.candidatePalmArrival p.1.1.1 qindex) :=
      (Probability.PoissonProcess.measurable_candidatePalmArrival qindex).comp
        ((measurable_fst.comp measurable_fst).comp measurable_fst)
    have hmember : MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
        qindex ∈ Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed
          0 p.2 p.1.1.1} := by
      simp only [Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed,
        Finset.mem_filter, Finset.mem_Icc, Set.setOf_and]
      exact ((measurableSet_le hcrossLeft measurable_const).inter
        (measurableSet_le measurable_const hcrossRight)).inter
          ((measurableSet_lt measurable_const harrival).inter
            (measurableSet_le harrival measurable_snd))
    simpa only [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      stationaryPriorityClassTaggedFutureArrivalIndices,
      stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_pos,
      Finset.mem_filter, Set.setOf_and] using
      hmember.inter (measurableSet_lt harrival measurable_snd)
  · have hsusp : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        (p.1.2 ⟨qclass, hqi⟩).1) :=
      (measurable_fst.comp ((measurable_pi_apply
        (X := fun _ : {j : Fin n // j ≠ i} => StationaryPoissonWorkPath)
        ⟨qclass, hqi⟩).comp measurable_snd)).comp measurable_fst
    have hraw : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        ((p.1.2 ⟨qclass, hqi⟩).1).1) :=
      measurable_subtype_coe.comp hsusp
    have hcrossLeft : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed 0
          ((p.1.2 ⟨qclass, hqi⟩).1).1) :=
      (Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed 0).comp hraw
    have hcrossRight : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed p.2
          ((p.1.2 ⟨qclass, hqi⟩).1).1) :=
      Probability.PoissonProcess.measurable_uncurry_suspensionCrossingIndexPastClosed.comp
        (measurable_snd.prodMk hraw)
    have harrival : Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
        Probability.PoissonProcess.suspensionBaseArrival (p.1.2 ⟨qclass, hqi⟩).1 qindex) :=
      (Probability.PoissonProcess.measurable_suspensionBaseArrival qindex).comp hsusp
    have hmember : MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
        qindex ∈ Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
          0 p.2 (p.1.2 ⟨qclass, hqi⟩).1} := by
      simp only [Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed,
        Finset.mem_filter, Finset.mem_Icc, Set.setOf_and]
      exact ((measurableSet_le hcrossLeft measurable_const).inter
        (measurableSet_le measurable_const hcrossRight)).inter
          ((measurableSet_lt measurable_const harrival).inter
            (measurableSet_le harrival measurable_snd))
    simpa only [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      stationaryPriorityClassTaggedFutureArrivalIndices,
      stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hqi,
      Finset.mem_filter, Set.setOf_and] using
      hmember.inter (measurableSet_lt harrival measurable_snd)

/-- A fixed strict future ledger is a Borel fiber on the selected
sample-time product carrier. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureArrivalLedgerBeforeHorizon_product_eq
    (i : Fin n) (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i p.1 p.2) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i p.1 p.2)} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_product
        i q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i p.1 p.2) ↔
          q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i p.1 p.2)} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {p : StationaryPriorityClassTaggedReplayProduct i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i p.1 p.2) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {p |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i p.1 p.2) ↔
          q ∈ labels} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The chronological strict future ledger has Borel fibers jointly in the
selected sample and elapsed-time coordinates. -/
theorem measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_product_eq
    (i : Fin n) (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i p.1 p.2 = labels} := by
  classical
  have hledger :=
    measurableSet_stationaryPriorityClassTaggedFutureArrivalLedgerBeforeHorizon_product_eq
      i labels.toFinset
  have hpairwise : MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i p.1)} := by
    simpa using (measurableSet_stationaryPriorityClassTaggedArrivalIndexList_pairwise
      i labels).preimage measurable_fst
  have hnodup : MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {p : StationaryPriorityClassTaggedReplayProduct i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i p.1 p.2 = labels} =
      ({p | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i p.1 p.2) = labels.toFinset} ∩
        {p | labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i p.1)}) ∩
          {p | labels.Nodup} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i p.1⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i p.1⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i p.1⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i p.1 p.2).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
                i p.1 p.2) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact Finset.pairwise_sort _ _
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i p.1⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i p.1⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i p.1) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i p.1⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
          i p.1 p.2)).sort
          (stationaryPriorityClassTaggedArrivalIndexLE i p.1) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i p.1)
        hnodup).mpr hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- A fixed historical and strict-future ledger fiber on the selected
sample-time product carrier. -/
def stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
    (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    Set (StationaryPriorityClassTaggedReplayProduct i) :=
  {p | canonicalStationaryPriorityClassTaggedArrivalWindowIndices i p.1 (-older) 0 =
      pastLabels ∧
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i p.1 p.2 = futureLabels}

/-- Every fixed product replay ledger fiber is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
    (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet (stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
      i older pastLabels futureLabels) := by
  exact ((measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
    i (-older) 0 pastLabels).preimage measurable_fst).inter
      (measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_product_eq
        i futureLabels)

/-- The product-side branch predicate for a fully fixed two-sided selected
replay.  Its last advance reads the elapsed-time coordinate. -/
def stationaryPriorityClassTaggedProductFixedReplayBranchMatches
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (p : StationaryPriorityClassTaggedReplayProduct i) : Prop :=
  fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedProductFixedPastInitial i older)
      (stationaryPriorityClassTaggedProductFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots p ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
          meanService i older pastLabels skeleton))
      (fun _ => 0)
      (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
        meanService i older pastLabels skeleton)
      skeleton.pastTerminalCompletionCount skeleton.pastTerminal p ∧
    fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedProductFixedPostTagState
        meanService i older pastLabels skeleton)
      (stationaryPriorityClassTaggedProductFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots p ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedProductFixedPostFutureState
          meanService i older pastLabels futureLabels skeleton))
      Prod.snd
      (stationaryPriorityClassTaggedProductFixedPostFutureState
        meanService i older pastLabels futureLabels skeleton)
      skeleton.futureTerminalCompletionCount skeleton.futureTerminal p

/-- Every fixed product-side finite replay branch is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedProductFixedReplayBranchMatches
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      stationaryPriorityClassTaggedProductFixedReplayBranchMatches
        meanService i older pastLabels futureLabels skeleton p} := by
  have hinitial :
      (stationaryPriorityClassTaggedProductFixedPastInitial i older).CoordinatesMeasurable :=
    stationaryPriorityClassTaggedProductFixedPastInitial_coordinatesMeasurable i older
  have hpastJobs := stationaryPriorityClassTaggedProductFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter :
      (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
        meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    stationaryPriorityClassTaggedProductFixedPastAfterArrivals_coordinatesMeasurable
      meanService i older pastLabels skeleton
  have hpast :
      (stationaryPriorityClassTaggedProductFixedPastState
        meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    stationaryPriorityClassTaggedProductFixedPastState_coordinatesMeasurable
      meanService i older pastLabels skeleton
  have hpostTag :
      (stationaryPriorityClassTaggedProductFixedPostTagState
        meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    stationaryPriorityClassTaggedProductFixedPostTagState_coordinatesMeasurable
      meanService i older pastLabels skeleton
  have hfutureJobs := stationaryPriorityClassTaggedProductFixedJobs_coordinatesMeasurable
    meanService i futureLabels
  have hfuture :
      (stationaryPriorityClassTaggedProductFixedPostFutureState meanService i older
        pastLabels futureLabels skeleton).CoordinatesMeasurable :=
    stationaryPriorityClassTaggedProductFixedPostFutureState_coordinatesMeasurable
      meanService i older pastLabels futureLabels skeleton
  convert ((measurableSet_fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedProductFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedProductFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs).inter
    (measurableSet_fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
          meanService i older pastLabels skeleton)) (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal)).inter
    ((measurableSet_fixedPriorityArrivalTraceBranchMatches _ hpostTag
      (stationaryPriorityClassTaggedProductFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs).inter
      (measurableSet_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs
          (stationaryPriorityClassTaggedProductFixedPostFutureState meanService i older
            pastLabels futureLabels skeleton)) Prod.snd measurable_snd
        _ hfuture skeleton.futureTerminalCompletionCount skeleton.futureTerminal)) using 1
  ext p
  simp [stationaryPriorityClassTaggedProductFixedReplayBranchMatches]
  aesop

/-- The countable product replay ledger/skeleton fibers cover every selected
sample and elapsed-time point. -/
theorem iUnion_stationaryPriorityClassTaggedProductFiniteReplayPiecesBeforeHorizon
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ) :
    ⋃ pastLabels : List (NonpreemptivePriorityArrivalIndex n),
      ⋃ futureLabels : List (NonpreemptivePriorityArrivalIndex n),
        ⋃ skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton,
          stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
            i older pastLabels futureLabels ∩
            {p | stationaryPriorityClassTaggedProductFixedReplayBranchMatches
              meanService i older pastLabels futureLabels skeleton p} = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_univ, iff_true]
  let pastLabels := canonicalStationaryPriorityClassTaggedArrivalWindowIndices
    i p.1 (-older) 0
  let futureLabels := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
    i p.1 p.2
  let initial := stationaryPriorityClassTaggedProductFixedPastInitial i older
  let pastJobs := stationaryPriorityClassTaggedProductFixedJobs meanService i pastLabels
  rcases exists_fixedPriorityArrivalTraceBranchMatches initial pastJobs p with
    ⟨pastArrivalSlots, hpastArrivals⟩
  let pastAfter := runFixedPriorityArrivalTraceBranch initial pastJobs pastArrivalSlots
  rcases exists_fixedPriorityAdvanceBranchMatches
    (totalFixedNonpreemptivePriorityWorkJobs pastAfter) (fun _ => 0) pastAfter p with
    ⟨pastTerminalCompletionCount, pastTerminal, hpastTerminal⟩
  let skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
    { pastArrivalSlots := pastArrivalSlots
      pastTerminalCompletionCount := pastTerminalCompletionCount
      pastTerminal := pastTerminal
      futureArrivalSlots := []
      futureTerminalCompletionCount := 0
      futureTerminal := .hold }
  let postTag := stationaryPriorityClassTaggedProductFixedPostTagState
    meanService i older pastLabels skeleton
  let futureJobs := stationaryPriorityClassTaggedProductFixedJobs meanService i futureLabels
  rcases exists_fixedPriorityArrivalTraceBranchMatches postTag futureJobs p with
    ⟨futureArrivalSlots, hfutureArrivals⟩
  let postFuture := runFixedPriorityArrivalTraceBranch postTag futureJobs futureArrivalSlots
  rcases exists_fixedPriorityAdvanceBranchMatches
    (totalFixedNonpreemptivePriorityWorkJobs postFuture) Prod.snd postFuture p with
    ⟨futureTerminalCompletionCount, futureTerminal, hfutureTerminal⟩
  let finalSkeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
    { pastArrivalSlots := pastArrivalSlots
      pastTerminalCompletionCount := pastTerminalCompletionCount
      pastTerminal := pastTerminal
      futureArrivalSlots := futureArrivalSlots
      futureTerminalCompletionCount := futureTerminalCompletionCount
      futureTerminal := futureTerminal }
  refine ⟨pastLabels, futureLabels, finalSkeleton, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩

/-- On a product fixed-ledger fiber and a matching service skeleton, the
product-coordinate replay evaluates to the literal finite strict replay at
the corresponding sample and elapsed time. -/
theorem stationaryPriorityClassTaggedProductFixedReplayState_eval_eq_finiteReplayStateBeforeHorizon_of_matches
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (p : StationaryPriorityClassTaggedReplayProduct i)
    (hledger : stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
      i older pastLabels futureLabels p)
    (hmatches : stationaryPriorityClassTaggedProductFixedReplayBranchMatches
      meanService i older pastLabels futureLabels skeleton p) :
    (stationaryPriorityClassTaggedProductFixedReplayState meanService i older
      pastLabels futureLabels skeleton).eval p =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i p.1 older p.2 := by
  rcases hledger with ⟨hpastLabels, hfutureLabels⟩
  rcases hmatches with ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  have hpastAfter :
      (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
        meanService i older pastLabels skeleton).eval p =
        runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
          (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
            meanService i p.1 (-older) 0) := by
    calc
      (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
          meanService i older pastLabels skeleton).eval p =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedProductFixedPastInitial i older).eval p)
            ((stationaryPriorityClassTaggedProductFixedJobs meanService i pastLabels).map
              fun job => job.eval p) := by
            simpa [stationaryPriorityClassTaggedProductFixedPastAfterArrivals] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedProductFixedPastInitial i older)
                (stationaryPriorityClassTaggedProductFixedJobs meanService i pastLabels)
                skeleton.pastArrivalSlots p hpastArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
            (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
              meanService i p.1 (-older) 0) := by
            rw [eval_stationaryPriorityClassTaggedProductFixedJobs]
            simp only [stationaryPriorityClassTaggedProductFixedPastInitial,
              NonpreemptivePriorityFixedStateCoordinate.eval_pullback,
              stationaryPriorityClassTaggedFixedPastInitial,
              emptyNonpreemptivePriorityFixedStateCoordinate_eval,
              canonicalStationaryPriorityClassTaggedArrivalWindowJobs]
            rw [hpastLabels]
            rfl
  have hpast :
      (stationaryPriorityClassTaggedProductFixedPastState
        meanService i older pastLabels skeleton).eval p =
        canonicalStationaryPriorityClassTaggedFiniteWindowState
          meanService i p.1 (-older) 0 := by
    calc
      (stationaryPriorityClassTaggedProductFixedPastState
          meanService i older pastLabels skeleton).eval p =
          advanceNonpreemptivePriorityWorkState
            (totalFixedNonpreemptivePriorityWorkJobs
              (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
                meanService i older pastLabels skeleton))
            0
            ((stationaryPriorityClassTaggedProductFixedPastAfterArrivals
              meanService i older pastLabels skeleton).eval p) := by
            simpa [stationaryPriorityClassTaggedProductFixedPastState] using
              (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
                (totalFixedNonpreemptivePriorityWorkJobs
                  (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
                    meanService i older pastLabels skeleton))
                (fun _ => 0)
                (stationaryPriorityClassTaggedProductFixedPastAfterArrivals
                  meanService i older pastLabels skeleton)
                skeleton.pastTerminalCompletionCount skeleton.pastTerminal p hpastTerminal)
      _ = canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i p.1 (-older) 0 := by
            rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval]
            rw [hpastAfter]
            rfl
  have hpostTag :
      (stationaryPriorityClassTaggedProductFixedPostTagState
        meanService i older pastLabels skeleton).eval p =
        admitNonpreemptivePriorityJob
          (clearNonpreemptivePriorityCompletionLedger
            (canonicalStationaryPriorityClassTaggedFiniteWindowState
              meanService i p.1 (-older) 0))
          (stationaryPriorityClassTaggedJob meanService i p.1) := by
    simp only [stationaryPriorityClassTaggedProductFixedPostTagState,
      NonpreemptivePriorityFixedStateCoordinate.eval_admit,
      NonpreemptivePriorityFixedStateCoordinate.eval_clearCompleted,
      NonpreemptivePriorityFixedJobCoordinate.eval_pullback]
    rw [hpast]
    rfl
  have hfuture :
      (stationaryPriorityClassTaggedProductFixedPostFutureState
        meanService i older pastLabels futureLabels skeleton).eval p =
        runNonpreemptivePriorityArrivalTrace
          (admitNonpreemptivePriorityJob
            (clearNonpreemptivePriorityCompletionLedger
              (canonicalStationaryPriorityClassTaggedFiniteWindowState
                meanService i p.1 (-older) 0))
            (stationaryPriorityClassTaggedJob meanService i p.1))
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
            meanService i p.1 p.2) := by
    calc
      (stationaryPriorityClassTaggedProductFixedPostFutureState
          meanService i older pastLabels futureLabels skeleton).eval p =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedProductFixedPostTagState
              meanService i older pastLabels skeleton).eval p)
            ((stationaryPriorityClassTaggedProductFixedJobs meanService i futureLabels).map
              fun job => job.eval p) := by
            simpa [stationaryPriorityClassTaggedProductFixedPostFutureState] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedProductFixedPostTagState
                  meanService i older pastLabels skeleton)
                (stationaryPriorityClassTaggedProductFixedJobs meanService i futureLabels)
                skeleton.futureArrivalSlots p hfutureArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (admitNonpreemptivePriorityJob
              (clearNonpreemptivePriorityCompletionLedger
                (canonicalStationaryPriorityClassTaggedFiniteWindowState
                  meanService i p.1 (-older) 0))
              (stationaryPriorityClassTaggedJob meanService i p.1))
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i p.1 p.2) := by
            rw [hpostTag, eval_stationaryPriorityClassTaggedProductFixedJobs]
            simp only [canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon]
            rw [hfutureLabels]
  calc
    (stationaryPriorityClassTaggedProductFixedReplayState meanService i older
        pastLabels futureLabels skeleton).eval p =
        advanceNonpreemptivePriorityWorkState
          (totalFixedNonpreemptivePriorityWorkJobs
            (stationaryPriorityClassTaggedProductFixedPostFutureState
              meanService i older pastLabels futureLabels skeleton))
          p.2
          ((stationaryPriorityClassTaggedProductFixedPostFutureState
            meanService i older pastLabels futureLabels skeleton).eval p) := by
          simpa [stationaryPriorityClassTaggedProductFixedReplayState] using
            (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
              (totalFixedNonpreemptivePriorityWorkJobs
                (stationaryPriorityClassTaggedProductFixedPostFutureState
                  meanService i older pastLabels futureLabels skeleton))
              Prod.snd
              (stationaryPriorityClassTaggedProductFixedPostFutureState meanService i older
                pastLabels futureLabels skeleton)
              skeleton.futureTerminalCompletionCount skeleton.futureTerminal p hfutureTerminal)
    _ = stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i p.1 older p.2 := by
          rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval, hfuture]
          rfl

/-- The strict finite selected-replay waiting observation is jointly Borel in
the selected/Palm sample and elapsed-time coordinates. -/
theorem measurable_uncurry_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ) :
    Measurable (fun p : StationaryPriorityClassTaggedReplayProduct i =>
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i p.1 older p.2) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    List (NonpreemptivePriorityArrivalIndex n) ×
      StationaryPriorityClassTaggedFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
        i older q.1 q.2.1 ∩
        {p | stationaryPriorityClassTaggedProductFixedReplayBranchMatches
          meanService i older q.1 q.2.1 q.2.2 p})
    ?_ ?_
    (fun p => stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i p.1 older p.2)
    (fun q => fixedNonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedProductFixedReplayState
        meanService i older q.1 q.2.1 q.2.2))
    ?_ ?_
  · intro q
    exact (measurableSet_stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
      i older q.1 q.2.1).inter
      (measurableSet_stationaryPriorityClassTaggedProductFixedReplayBranchMatches
        meanService i older q.1 q.2.1 q.2.2)
  · change (⋃ q : Piece,
        stationaryPriorityClassTaggedProductFiniteReplayLedgerFiberBeforeHorizon
          i older q.1 q.2.1 ∩
          {p | stationaryPriorityClassTaggedProductFixedReplayBranchMatches
            meanService i older q.1 q.2.1 q.2.2 p}) = Set.univ
    rw [Set.iUnion_prod']
    simp_rw [Set.iUnion_prod']
    exact iUnion_stationaryPriorityClassTaggedProductFiniteReplayPiecesBeforeHorizon
      meanService i older
  · intro q
    exact measurable_fixedNonpreemptivePriorityWaitingIdentifierIndicator
      (Sigma.mk i 0)
      (stationaryPriorityClassTaggedProductFixedReplayState
        meanService i older q.1 q.2.1 q.2.2)
  · intro q p hp
    rcases hp with ⟨hledger, hmatches⟩
    unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    symm
    change fixedNonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedProductFixedReplayState
          meanService i older q.1 q.2.1 q.2.2) p =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i p.1 older p.2)
    rw [fixedNonpreemptivePriorityWaitingIdentifierIndicator_eval]
    rw [stationaryPriorityClassTaggedProductFixedReplayState_eval_eq_finiteReplayStateBeforeHorizon_of_matches
      meanService i older q.1 q.2.1 q.2.2 p hledger hmatches]

/-- The real work contribution of a finite strict replay, with the elapsed
time restricted to the causal half-line. -/
noncomputable def stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
    (meanService : Fin n → ℝ) (i : Fin n) (horizon : ℕ) :
    StationaryPriorityClassTaggedReplayProduct i → ℝ := fun p =>
  if 0 ≤ p.2 then
    stationaryPriorityClassTaggedWorkRequirement meanService i p.1 *
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i p.1 (horizon : ℝ) p.2
  else 0

/-- The literal real-valued selected waiting-work coverage on the
sample-time product carrier. -/
noncomputable def stationaryPriorityClassTaggedWaitingWorkResponse
    (meanService : Fin n → ℝ) (i : Fin n) :
    StationaryPriorityClassTaggedReplayProduct i → ℝ := fun p =>
  if 0 ≤ p.2 ∧ p.2 < stationaryPriorityClassTaggedQueueWait meanService i p.1 then
    stationaryPriorityClassTaggedWorkRequirement meanService i p.1
  else 0

/-- Every finite work-weighted strict replay is jointly Borel. -/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
    (meanService : Fin n → ℝ) (i : Fin n) (horizon : ℕ) :
    Measurable (stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
      meanService i horizon) := by
  apply Measurable.ite
  · apply measurableSet_setOf.mpr
    exact measurable_const.le' measurable_snd
  · exact ((measurable_stationaryPriorityClassTaggedWorkRequirement meanService i).comp
      measurable_fst).mul
        (measurable_uncurry_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i (horizon : ℝ))
  · exact measurable_const

/-- The literal real waiting-work coverage is jointly Borel. -/
theorem measurable_stationaryPriorityClassTaggedWaitingWorkResponse
    (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (stationaryPriorityClassTaggedWaitingWorkResponse meanService i) := by
  apply Measurable.ite
  · apply measurableSet_setOf.mpr
    exact (measurable_const.le' measurable_snd).and
      (measurable_snd.lt
        ((measurable_stationaryPriorityClassTaggedQueueWait meanService i).comp
          measurable_fst))
  · exact (measurable_stationaryPriorityClassTaggedWorkRequirement meanService i).comp
      measurable_fst
  · exact measurable_const

/-- Under strict load, the real selected waiting-work coverage is the
eventual value of the jointly Borel finite replay sequence. -/
theorem ae_eventually_stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse_eq_waitingWorkResponse
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop, ∀ elapsed : ℝ,
        stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
          meanService i horizon (z, elapsed) =
        stationaryPriorityClassTaggedWaitingWorkResponse meanService i (z, elapsed) := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator_all
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hz
  rcases hz with ⟨cutoff, hcutoff, hstableReplay⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon elapsed
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have hlarge : cutoff ≤ (horizon : ℝ) := hceil.trans hcast
  by_cases helapsed : 0 ≤ elapsed
  · rw [show stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
        meanService i horizon (z, elapsed) =
        stationaryPriorityClassTaggedWorkRequirement meanService i z *
          stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
            meanService i z (horizon : ℝ) elapsed by
          simp [stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse, helapsed],
      hstableReplay (horizon : ℝ) hlarge elapsed helapsed]
    by_cases hwaiting : elapsed < stationaryPriorityClassTaggedQueueWait meanService i z
    · simp [stationaryPriorityClassTaggedWaitingWorkResponse, helapsed, hwaiting]
    · simp [stationaryPriorityClassTaggedWaitingWorkResponse, helapsed, hwaiting]
  · simp [stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse,
      stationaryPriorityClassTaggedWaitingWorkResponse, helapsed]

/-- The Borel limsup of finite strict replay work responses.  On stable
selected inputs it is the ordinary work spread over the waiting interval. -/
noncomputable def stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
    (meanService : Fin n → ℝ) (i : Fin n) :
    StationaryPriorityClassTaggedReplayProduct i → ℝ :=
  AppliedModelingLib.Probability.stabilizedFiniteReplayResponse
    (stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse meanService i)

/-- The stabilized selected waiting-work response is jointly Borel. -/
theorem measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
    (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
      meanService i) := by
  exact AppliedModelingLib.Probability.measurable_stabilizedFiniteReplayResponse
    (stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse meanService i)
    (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
      meanService i)

/-- Under the concrete selected-Palm product law, the stabilized Borel
response agrees almost everywhere with literal selected waiting-work
coverage. -/
theorem ae_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_waitingWorkResponse
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i =ᵐ[
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.prod
          MeasureTheory.volume]
      stationaryPriorityClassTaggedWaitingWorkResponse meanService i := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let F := stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse meanService i
  let G := stationaryPriorityClassTaggedWaitingWorkResponse meanService i
  have hslice : ∀ᵐ z ∂P, ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon (z, elapsed) = G (z, elapsed) := by
    filter_upwards [
      ae_eventually_stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse_eq_waitingWorkResponse
        arrivalRate meanService harrivalRate hmeanService hstable i] with z hz
    filter_upwards with elapsed
    exact hz.mono fun horizon hhorizon => hhorizon elapsed
  have heventually_meas : MeasurableSet {p : StationaryPriorityClassTaggedReplayProduct i |
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = G p} := by
    rw [show {p : StationaryPriorityClassTaggedReplayProduct i |
        ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = G p} =
        ⋃ threshold : ℕ, ⋂ horizon : ℕ, ⋂ (_ : threshold ≤ horizon),
          {p | F horizon p = G p} by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
          Filter.eventually_atTop]]
    apply MeasurableSet.iUnion
    intro threshold
    apply MeasurableSet.iInter
    intro horizon
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_eq_fun
      (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse
        meanService i horizon)
      (measurable_stationaryPriorityClassTaggedWaitingWorkResponse meanService i)
  have hproduct : ∀ᵐ p : StationaryPriorityClassTaggedReplayProduct i ∂
      (P.prod MeasureTheory.volume),
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = G p :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae heventually_meas).2 hslice
  simpa [stationaryPriorityClassTaggedStabilizedWaitingWorkResponse, F, G, P] using
    (AppliedModelingLib.Probability.ae_stabilizedFiniteReplayResponse_eq_of_ae_eventually_eq
      (P.prod MeasureTheory.volume) F G hproduct)

end

end AppliedModelingLib.Queueing

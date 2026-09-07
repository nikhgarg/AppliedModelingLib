import AppliedModelingLib.Queueing.StationaryPriorityInput
import AppliedModelingLib.Queueing.MulticlassPalmPastInput
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalLedger
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceReflection
import AppliedModelingLib.Queueing.NonpreemptivePriorityIdentifierTransport
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedCanonicalTrace
import Mathlib.Data.Sigma.Order
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.IdentDistrib

/-!
# Finite priority replay from canonical strict-past input

This module turns the canonical backwards-renewal coordinates of a finite
multiclass marked input into a literal finite priority trace.  The construction
is deterministic: it records physical negative arrival epochs and scaled work
requirements, while retaining a fixed index tie-breaker for exact replay.
It is the common replay surface to which stationary-time and selected-arrival
input laws can later be transported.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- A class label together with its index in a canonical backwards renewal
path. -/
abbrev NonpreemptivePriorityCanonicalPastIndex (n : ℕ) := Sigma fun _ : Fin n => ℕ

/-- The physical epoch of a canonical-past arrival.  Index zero is the most
recent arrival before the origin, so the backwards renewal clock is negated. -/
def nonpreemptivePriorityCanonicalPastArrivalTime
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (q : NonpreemptivePriorityCanonicalPastIndex n) : ℝ :=
  -Probability.PoissonProcess.arrivalTime q.2 (past q.1).1

/-- The class-scaled service work of a canonical-past arrival. -/
def nonpreemptivePriorityCanonicalPastServiceWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (q : NonpreemptivePriorityCanonicalPastIndex n) : ℝ :=
  meanService q.1 * (past q.1).2 q.2

/-- The labelled stationary arrival corresponding to one canonical-past
coordinate.  Each class uses the equilibrium backward enumeration. -/
def nonpreemptivePriorityStationaryPastReindex
    {n : ℕ} :
    NonpreemptivePriorityCanonicalPastIndex n → NonpreemptivePriorityArrivalIndex n :=
  fun q => ⟨q.1, Probability.PoissonProcess.equilibriumBackwardArrivalIndex q.2⟩

theorem Function.Injective.nonpreemptivePriorityStationaryPastReindex
    {n : ℕ} :
    Function.Injective (nonpreemptivePriorityStationaryPastReindex (n := n)) := by
  intro first second heq
  rcases first with ⟨firstClass, firstIndex⟩
  rcases second with ⟨secondClass, secondIndex⟩
  change (⟨firstClass,
      Probability.PoissonProcess.equilibriumBackwardArrivalIndex firstIndex⟩ :
        NonpreemptivePriorityArrivalIndex n) =
    ⟨secondClass,
      Probability.PoissonProcess.equilibriumBackwardArrivalIndex secondIndex⟩ at heq
  injection heq with hclass hindex
  subst secondClass
  have hcanonical : firstIndex = secondIndex :=
    Probability.PoissonProcess.equilibriumBackwardArrivalIndex_injective hindex
  subst secondIndex
  rfl

/-- The stationary physical epoch indexed by the equilibrium backward map is
exactly the epoch reconstructed from the canonical strict-past path. -/
theorem multiclassStationaryPoissonWorkArrival_stationaryPastReindex_eq_canonical
    {n : ℕ}
    (omega : Fin n → StationaryPoissonWorkPath)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega
        (Probability.PoissonProcess.equilibriumBackwardArrivalIndex q.2) =
      nonpreemptivePriorityCanonicalPastArrivalTime
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) q := by
  change Probability.PoissonProcess.suspensionBaseArrival (omega q.1).1
      (Probability.PoissonProcess.equilibriumBackwardArrivalIndex q.2) = _
  unfold Probability.PoissonProcess.suspensionBaseArrival
  rw [← Probability.PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium]
  rw [Probability.PoissonProcess.equilibriumBaseArrival_backwardIndex]
  rfl

/-- The stationary work mark indexed by the equilibrium backward map is the
corresponding canonical strict-past work mark, after class scaling. -/
theorem stationaryPriorityWorkRequirement_stationaryPastReindex_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    stationaryPriorityWorkRequirement meanService q.1 omega
        (Probability.PoissonProcess.equilibriumBackwardArrivalIndex q.2) =
      nonpreemptivePriorityCanonicalPastServiceWork meanService
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) q := by
  rfl

/-- The labelled raw index corresponding to a canonical strict-past
coordinate on a class-selected input.  The selected class uses negative Palm
labels, while passive classes use their equilibrium backward labels. -/
noncomputable def nonpreemptivePriorityClassTaggedPastReindex
    {n : ℕ} (selected : Fin n) :
    NonpreemptivePriorityCanonicalPastIndex n → NonpreemptivePriorityArrivalIndex n :=
  fun q => if hselected : q.1 = selected then
    ⟨q.1, Int.negSucc q.2⟩
  else
    ⟨q.1, Probability.PoissonProcess.equilibriumBackwardArrivalIndex q.2⟩

/-- The selected/Palm reindexing retains the complete class and renewal
coordinate, so it is injective. -/
theorem Function.Injective.nonpreemptivePriorityClassTaggedPastReindex
    {n : ℕ} (selected : Fin n) :
    Function.Injective (nonpreemptivePriorityClassTaggedPastReindex selected) := by
  intro first second heq
  rcases first with ⟨firstClass, firstIndex⟩
  rcases second with ⟨secondClass, secondIndex⟩
  have hclass : firstClass = secondClass := by
    unfold AppliedModelingLib.Queueing.nonpreemptivePriorityClassTaggedPastReindex at heq
    split at heq <;> split at heq <;> exact congrArg Sigma.fst heq
  subst secondClass
  by_cases hselected : firstClass = selected
  · simp only [AppliedModelingLib.Queueing.nonpreemptivePriorityClassTaggedPastReindex,
      dif_pos hselected] at heq
    have hindex : firstIndex = secondIndex := Int.negSucc.inj
      (congrArg Sigma.snd heq)
    subst secondIndex
    rfl
  · simp only [AppliedModelingLib.Queueing.nonpreemptivePriorityClassTaggedPastReindex,
      dif_neg hselected] at heq
    have hindex : firstIndex = secondIndex :=
      Probability.PoissonProcess.equilibriumBackwardArrivalIndex_injective
        (congrArg Sigma.snd heq)
    subst secondIndex
    rfl

/-- A selected-arrival physical past epoch agrees with the epoch reconstructed
from the selected coordinate's canonical past. -/
theorem stationaryPriorityClassTaggedArrival_classTaggedPastReindex_eq_canonical
    {n : ℕ} (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    stationaryPriorityClassTaggedArrival selected z q.1
        (nonpreemptivePriorityClassTaggedPastReindex selected q).2 =
      nonpreemptivePriorityCanonicalPastArrivalTime
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) q := by
  rcases q with ⟨j, k⟩
  by_cases hji : j = selected
  · subst j
    change stationaryPriorityClassTaggedArrival selected z selected
        (nonpreemptivePriorityClassTaggedPastReindex selected ⟨selected, k⟩).2 =
      -Probability.PoissonProcess.arrivalTime k
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z selected).1
    rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_self]
    simp only [nonpreemptivePriorityClassTaggedPastReindex, dif_pos,
      stationaryPriorityClassTaggedArrival, multiclassStationaryPoissonWorkClassTaggedArrival,
      Probability.PoissonProcess.candidatePalmArrival_negSucc,
      Probability.PoissonProcess.candidatePastMarkedInput]
    exact congrArg Neg.neg
      (congrFun (Probability.PoissonProcess.candidatePastGapSum_succ_eq_arrivalTime k) z.1.1)
  · change stationaryPriorityClassTaggedArrival selected z j
        (nonpreemptivePriorityClassTaggedPastReindex selected ⟨j, k⟩).2 =
      -Probability.PoissonProcess.arrivalTime k
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z j).1
    rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_of_ne selected j hji]
    simp only [nonpreemptivePriorityClassTaggedPastReindex,
      stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hji]
    change Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨j, hji⟩).1
        (Probability.PoissonProcess.equilibriumBackwardArrivalIndex k) = _
    unfold Probability.PoissonProcess.suspensionBaseArrival
    rw [← Probability.PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium]
    rw [Probability.PoissonProcess.equilibriumBaseArrival_backwardIndex]
    rfl

/-- The class-scaled work mark of a class-selected strict-past coordinate
agrees with its canonical marked-input coordinate. -/
theorem stationaryPriorityClassTaggedWorkRequirementAt_classTaggedPastReindex_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    stationaryPriorityClassTaggedWorkRequirementAt meanService selected z q.1
        (nonpreemptivePriorityClassTaggedPastReindex selected q).2 =
      nonpreemptivePriorityCanonicalPastServiceWork meanService
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) q := by
  rcases q with ⟨j, k⟩
  by_cases hji : j = selected
  · subst j
    change stationaryPriorityClassTaggedWorkRequirementAt meanService selected z selected
        (nonpreemptivePriorityClassTaggedPastReindex selected ⟨selected, k⟩).2 =
      meanService selected *
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z selected).2 k
    rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_self]
    simp [nonpreemptivePriorityClassTaggedPastReindex,
      stationaryPriorityClassTaggedWorkRequirementAt,
      multiclassStationaryPoissonWorkClassTaggedRequirementAt,
      Probability.PoissonProcess.candidatePastMarkedInput,
      Probability.PoissonProcess.candidatePastGapPath,
      Probability.PoissonProcess.twoSidedGap]
  · change stationaryPriorityClassTaggedWorkRequirementAt meanService selected z j
        (nonpreemptivePriorityClassTaggedPastReindex selected ⟨j, k⟩).2 =
      meanService j *
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z j).2 k
    rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_of_ne selected j hji]
    simp only [nonpreemptivePriorityClassTaggedPastReindex, dif_neg hji,
      stationaryPriorityClassTaggedWorkRequirementAt,
      stationaryPoissonWorkPastCanonicalPath,
      Probability.Queueing.equilibriumPastMarkedInput]
    rw [multiclassStationaryPoissonWorkClassTaggedRequirementAt_of_ne selected j hji]
    rfl

/-- The finite canonical-past index set whose arrivals lie in `[-horizon, 0)`.
The renewal count makes the ledger finite on every input path, independently
of whether that path later satisfies the almost-sure positivity properties of
an exponential law. -/
def nonpreemptivePriorityCanonicalPastWindowIndices
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) : Fin n → Finset ℕ :=
  fun i => Finset.range (Probability.PoissonProcess.canonicalRenewalCount horizon (past i).1)

/-- The finite class-index ledger selected by a canonical strict-past window. -/
def nonpreemptivePriorityCanonicalPastWindowIndexLedger
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) : Finset (NonpreemptivePriorityCanonicalPastIndex n) :=
  Finset.sigma Finset.univ
    (nonpreemptivePriorityCanonicalPastWindowIndices past horizon)

/-- If each stationary class window is represented by its equilibrium
backward enumeration, reindexing the canonical finite ledger gives exactly
the literal stationary finite ledger. -/
theorem nonpreemptivePriorityStationaryPastReindex_windowIndexLedger_eq
    {n : ℕ}
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1) :
    Finset.image (nonpreemptivePriorityStationaryPastReindex (n := n))
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) =
      nonpreemptivePriorityArrivalWindowIndices (fun i =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1) := by
  classical
  ext q
  rcases q with ⟨i, k⟩
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hmap⟩
    rcases q with ⟨j, m⟩
    simp only [nonpreemptivePriorityStationaryPastReindex, Sigma.mk.inj_iff] at hmap
    rcases hmap with ⟨hclass, hindex⟩
    subst j
    cases hindex
    have hmem : Probability.PoissonProcess.equilibriumBackwardArrivalIndex m ∈
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 := by
      rw [hindices i]
      apply Finset.mem_image.mpr
      refine ⟨m, ?_, rfl⟩
      simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
        nonpreemptivePriorityCanonicalPastWindowIndices,
        multiclassStationaryPoissonWorkPastCanonicalInput,
        stationaryPoissonWorkPastCanonicalPath,
        Probability.Queueing.equilibriumPastMarkedInput,
        Probability.PoissonProcess.equilibriumBackwardCount] using hq
    simpa [nonpreemptivePriorityArrivalWindowIndices] using hmem
  · intro hk
    have hmem : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices
        (-horizon) 0 (omega i).1 := by
      simpa [nonpreemptivePriorityArrivalWindowIndices] using hk
    rw [hindices i] at hmem
    rcases Finset.mem_image.mp hmem with ⟨m, hm, hindex⟩
    refine ⟨⟨i, m⟩, ?_, ?_⟩
    · simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
        nonpreemptivePriorityCanonicalPastWindowIndices,
        multiclassStationaryPoissonWorkPastCanonicalInput,
        stationaryPoissonWorkPastCanonicalPath,
        Probability.Queueing.equilibriumPastMarkedInput,
        Probability.PoissonProcess.equilibriumBackwardCount] using hm
    · simp only [nonpreemptivePriorityStationaryPastReindex]
      exact congrArg (Sigma.mk i) hindex

/-- Under a finite product of stationary marked-Poisson inputs, the literal
stationary past ledger is almost surely the reindexed canonical-past ledger. -/
theorem ae_nonpreemptivePriorityStationaryPastReindex_windowIndexLedger_eq
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      Finset.image (nonpreemptivePriorityStationaryPastReindex (n := n))
        (nonpreemptivePriorityCanonicalPastWindowIndexLedger
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) =
        nonpreemptivePriorityArrivalWindowIndices (fun i =>
          Probability.PoissonProcess.suspensionBaseArrivalIndices
            (-horizon) 0 (omega i).1) := by
  let μ : Fin n → Measure StationaryPoissonWorkPath := fun i =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate i)
  have hclass : ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate, ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1 := by
    rw [ae_all_iff]
    intro i
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun z : StationaryPoissonWorkPath =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 z.1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium z).1)
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).measurable.aemeasurable ?_
    have hmap : Measure.map (Function.eval i) (Measure.pi μ) =
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i) := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          arrivalRate harrivalRate i).map_eq
    rw [hmap]
    exact
      Probability.Queueing.ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
        (harrivalRate i) horizon
  filter_upwards [hclass] with omega hindices
  exact nonpreemptivePriorityStationaryPastReindex_windowIndexLedger_eq
    omega horizon hindices

/-- In every fixed strict-past window, distinct class-labelled stationary
arrivals have distinct physical epochs almost surely.  The proof transports
the canonical collision-free input law through the finite backward-label
reindexing; it does not use any queue-state assertion. -/
theorem ae_nonpreemptivePriorityStationaryPastWindow_noArrivalTies
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices (fun i =>
          Probability.PoissonProcess.suspensionBaseArrivalIndices
            (-horizon) 0 (omega i).1),
        ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices (fun i =>
            Probability.PoissonProcess.suspensionBaseArrivalIndices
              (-horizon) 0 (omega i).1),
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              first.1 omega first.2 =
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              second.1 omega second.2 → first = second := by
  filter_upwards [
    ae_nonpreemptivePriorityStationaryPastReindex_windowIndexLedger_eq
      arrivalRate harrivalRate horizon,
    ae_multiclassStationaryPoissonWorkPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate] with omega hledger hcollision
  intro first hfirst second hsecond heq
  have hfirstImage : first ∈ Finset.image
      (nonpreemptivePriorityStationaryPastReindex (n := n))
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) := by
    rw [hledger]
    exact hfirst
  have hsecondImage : second ∈ Finset.image
      (nonpreemptivePriorityStationaryPastReindex (n := n))
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) := by
    rw [hledger]
    exact hsecond
  rcases Finset.mem_image.mp hfirstImage with ⟨firstCanonical, _, hfirstEq⟩
  rcases Finset.mem_image.mp hsecondImage with ⟨secondCanonical, _, hsecondEq⟩
  have hfirstArrival :
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        firstCanonical.1 omega
        (nonpreemptivePriorityStationaryPastReindex firstCanonical).2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        first.1 omega first.2 := by
    simpa only using congrArg
      (fun q : NonpreemptivePriorityArrivalIndex n =>
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2)
      hfirstEq
  have hsecondArrival :
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        secondCanonical.1 omega
        (nonpreemptivePriorityStationaryPastReindex secondCanonical).2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        second.1 omega second.2 := by
    simpa only using congrArg
      (fun q : NonpreemptivePriorityArrivalIndex n =>
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2)
      hsecondEq
  have htime : Probability.PoissonProcess.arrivalTime firstCanonical.2
      (multiclassStationaryPoissonWorkPastCanonicalInput omega firstCanonical.1).1 =
      Probability.PoissonProcess.arrivalTime secondCanonical.2
        (multiclassStationaryPoissonWorkPastCanonicalInput omega secondCanonical.1).1 := by
    apply neg_injective
    calc
      -Probability.PoissonProcess.arrivalTime firstCanonical.2
          (multiclassStationaryPoissonWorkPastCanonicalInput omega firstCanonical.1).1 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            firstCanonical.1 omega
            (nonpreemptivePriorityStationaryPastReindex firstCanonical).2 := by
              symm
              exact multiclassStationaryPoissonWorkArrival_stationaryPastReindex_eq_canonical
                omega firstCanonical
      _ = Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            first.1 omega first.2 := hfirstArrival
      _ = Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 := heq
      _ = Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            secondCanonical.1 omega
            (nonpreemptivePriorityStationaryPastReindex secondCanonical).2 := hsecondArrival.symm
      _ = -Probability.PoissonProcess.arrivalTime secondCanonical.2
          (multiclassStationaryPoissonWorkPastCanonicalInput omega secondCanonical.1).1 :=
            multiclassStationaryPoissonWorkArrival_stationaryPastReindex_eq_canonical
              omega secondCanonical
  rcases hcollision firstCanonical.1 secondCanonical.1 firstCanonical.2
    secondCanonical.2 htime with ⟨hclass, hindex⟩
  have hcanonical : firstCanonical = secondCanonical := by
    rcases firstCanonical with ⟨firstClass, firstIndex⟩
    rcases secondCanonical with ⟨secondClass, secondIndex⟩
    simp only at hclass hindex
    subst secondClass
    subst secondIndex
    rfl
  calc
    first = nonpreemptivePriorityStationaryPastReindex firstCanonical := hfirstEq.symm
    _ = nonpreemptivePriorityStationaryPastReindex secondCanonical := by rw [hcanonical]
    _ = second := hsecondEq

/-- On a selected-arrival input, reindexing the canonical strict-past ledger
recovers the literal finite Palm/stationary arrival ledger.  The selected
coordinate uses its Palm negative labels; the passive coordinates use their
stationary equilibrium labels. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowIndexLedger_eq
    {n : ℕ} (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    Finset.image (nonpreemptivePriorityClassTaggedPastReindex selected)
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon) =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0) := by
  classical
  ext q
  rcases q with ⟨j, k⟩
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hmap⟩
    rcases q with ⟨l, m⟩
    by_cases hji : j = selected
    · subst j
      have hclass : l = selected := by
        unfold nonpreemptivePriorityClassTaggedPastReindex at hmap
        split at hmap <;> exact congrArg Sigma.fst hmap
      subst l
      simp only [nonpreemptivePriorityClassTaggedPastReindex] at hmap
      have hindex : Int.negSucc m = k := by
        exact congrArg Sigma.snd hmap
      subst k
      have hm : m < Probability.PoissonProcess.canonicalRenewalCount horizon
          (Probability.PoissonProcess.candidatePastGapPath z.1.1) := by
        simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
          nonpreemptivePriorityCanonicalPastWindowIndices,
          multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_self,
          Probability.PoissonProcess.candidatePastMarkedInput] using hq
      have hmem : Int.negSucc m ∈
          stationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0 selected := by
        rw [stationaryPriorityClassTaggedArrivalWindowIndices, dif_pos rfl]
        rw [Probability.PoissonProcess.palmTaggedArrivalIndices_neg_to_zero_eq_pastCanonicalIndices
          z.1.1 hgood horizon]
        exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩
      simpa [nonpreemptivePriorityArrivalWindowIndices] using hmem
    · have hclass : l = j := by
        unfold nonpreemptivePriorityClassTaggedPastReindex at hmap
        split at hmap <;> exact congrArg Sigma.fst hmap
      subst l
      simp only [nonpreemptivePriorityClassTaggedPastReindex, dif_neg hji] at hmap
      have hindex : Probability.PoissonProcess.equilibriumBackwardArrivalIndex m = k := by
        exact congrArg Sigma.snd hmap
      subst k
      have hq' : m < Probability.PoissonProcess.canonicalRenewalCount horizon
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z j).1 := by
        simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
          nonpreemptivePriorityCanonicalPastWindowIndices] using hq
      rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_of_ne
        selected j hji] at hq'
      have hm : m < Probability.PoissonProcess.canonicalRenewalCount horizon
          (Probability.PoissonProcess.equilibriumPastPath
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (z.2 ⟨j, hji⟩)).1) := by
        simpa [stationaryPoissonWorkPastCanonicalPath,
          Probability.Queueing.equilibriumPastMarkedInput] using hq'
      have hmem : Probability.PoissonProcess.equilibriumBackwardArrivalIndex m ∈
          stationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0 j := by
        rw [stationaryPriorityClassTaggedArrivalWindowIndices, dif_neg hji, hpassive j hji]
        exact Finset.mem_image.mpr ⟨m,
          (by simpa [Probability.PoissonProcess.equilibriumBackwardCount] using
            Finset.mem_range.mpr hm), rfl⟩
      simpa [nonpreemptivePriorityArrivalWindowIndices] using hmem
  · intro hk
    have hmem : k ∈
        stationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0 j := by
      simpa [nonpreemptivePriorityArrivalWindowIndices] using hk
    by_cases hji : j = selected
    · subst j
      rw [stationaryPriorityClassTaggedArrivalWindowIndices, dif_pos rfl] at hmem
      rw [Probability.PoissonProcess.palmTaggedArrivalIndices_neg_to_zero_eq_pastCanonicalIndices
        z.1.1 hgood horizon] at hmem
      rcases Finset.mem_image.mp hmem with ⟨m, hm, hindex⟩
      refine ⟨⟨selected, m⟩, ?_, ?_⟩
      · simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
          nonpreemptivePriorityCanonicalPastWindowIndices,
          multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_self,
          Probability.PoissonProcess.candidatePastMarkedInput] using hm
      · simp only [nonpreemptivePriorityClassTaggedPastReindex, dif_pos]
        exact congrArg (Sigma.mk selected) hindex
    · rw [stationaryPriorityClassTaggedArrivalWindowIndices, dif_neg hji,
        hpassive j hji] at hmem
      rcases Finset.mem_image.mp hmem with ⟨m, hm, hindex⟩
      refine ⟨⟨j, m⟩, ?_, ?_⟩
      · have hm' : m < Probability.PoissonProcess.canonicalRenewalCount horizon
            (Probability.PoissonProcess.equilibriumPastPath
              (Probability.Queueing.stationaryPoissonWorkToEquilibrium (z.2 ⟨j, hji⟩)).1) := by
          simpa [Probability.PoissonProcess.equilibriumBackwardCount] using hm
        have hm'' : m < Probability.PoissonProcess.canonicalRenewalCount horizon
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z j).1 := by
          rw [multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_of_ne
            selected j hji]
          simpa [stationaryPoissonWorkPastCanonicalPath,
            Probability.Queueing.equilibriumPastMarkedInput] using hm'
        simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
          nonpreemptivePriorityCanonicalPastWindowIndices,
          multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_of_ne] using hm''
      · simp only [nonpreemptivePriorityClassTaggedPastReindex, dif_neg hji]
        exact congrArg (Sigma.mk j) hindex

/-- A deterministic key that orders canonical-past arrivals by physical epoch
and then by their fixed stream label. -/
def nonpreemptivePriorityCanonicalPastIndexKey
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    ℝ ×ₗ (Fin n ×ₗ ℕ) :=
  toLex (nonpreemptivePriorityCanonicalPastArrivalTime past q,
    (toLex (q.1, q.2) : Fin n ×ₗ ℕ))

/-- The canonical-past key is injective because its second coordinate retains
the complete class/index label. -/
theorem Function.Injective.nonpreemptivePriorityCanonicalPastIndexKey
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample) :
    Function.Injective (nonpreemptivePriorityCanonicalPastIndexKey past) := by
  intro first second hkey
  have hindex : (toLex (first.1, first.2) : Fin n ×ₗ ℕ) =
      toLex (second.1, second.2) := by
    exact congrArg (fun key => (ofLex key).2) hkey
  have hpair : (first.1, first.2) = (second.1, second.2) := toLex_inj.mp hindex
  cases first
  cases second
  simp only [Prod.mk.injEq] at hpair
  rcases hpair with ⟨hclass, hnat⟩
  subst hclass
  subst hnat
  rfl

/-- A canonical-past ordering key whose secondary label is supplied by an
injective reindexing into another arrival ledger.  It supports transporting a
chronological replay through a change of finite stream labels. -/
def nonpreemptivePriorityReindexedPastIndexKey
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    ℝ ×ₗ (Σₗ i : Fin n, ℤ) :=
  toLex (nonpreemptivePriorityCanonicalPastArrivalTime past q,
    (toLex (reindex q) : Σₗ i : Fin n, ℤ))

/-- An injective relabelling keeps the reindexed chronological key injective. -/
theorem Function.Injective.nonpreemptivePriorityReindexedPastIndexKey
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex) :
    Function.Injective (nonpreemptivePriorityReindexedPastIndexKey past reindex) := by
  intro first second hkey
  have hindex : (toLex (reindex first) : Σₗ i : Fin n, ℤ) =
      toLex (reindex second) := by
    exact congrArg (fun key => (ofLex key).2) hkey
  exact hreindex (toLex_inj.mp hindex)

/-- The total chronological order induced by an injectively reindexed
canonical-past ledger. -/
def nonpreemptivePriorityReindexedPastIndexLE
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (first second : NonpreemptivePriorityCanonicalPastIndex n) : Prop :=
  nonpreemptivePriorityReindexedPastIndexKey past reindex first ≤
    nonpreemptivePriorityReindexedPastIndexKey past reindex second

theorem nonpreemptivePriorityReindexedPastIndexLE_trans
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    {first second third : NonpreemptivePriorityCanonicalPastIndex n}
    (hfirst : nonpreemptivePriorityReindexedPastIndexLE past reindex first second)
    (hsecond : nonpreemptivePriorityReindexedPastIndexLE past reindex second third) :
    nonpreemptivePriorityReindexedPastIndexLE past reindex first third := by
  exact hfirst.trans hsecond

theorem nonpreemptivePriorityReindexedPastIndexLE_total
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (first second : NonpreemptivePriorityCanonicalPastIndex n) :
    nonpreemptivePriorityReindexedPastIndexLE past reindex first second ∨
      nonpreemptivePriorityReindexedPastIndexLE past reindex second first := by
  exact le_total _ _

theorem nonpreemptivePriorityReindexedPastIndexLE_antisymm
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    {first second : NonpreemptivePriorityCanonicalPastIndex n}
    (hfirst : nonpreemptivePriorityReindexedPastIndexLE past reindex first second)
    (hsecond : nonpreemptivePriorityReindexedPastIndexLE past reindex second first) :
    first = second := by
  apply Function.Injective.nonpreemptivePriorityReindexedPastIndexKey past reindex hreindex
  exact le_antisymm hfirst hsecond

/-- The canonical ledger sorted by physical epoch and then by an injective
target-ledger label. -/
noncomputable def nonpreemptivePriorityReindexedPastWindowIndices
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (ledger : Finset (NonpreemptivePriorityCanonicalPastIndex n)) :
    List (NonpreemptivePriorityCanonicalPastIndex n) := by
  classical
  letI : DecidableRel (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨fun _ _ _ => nonpreemptivePriorityReindexedPastIndexLE_trans past reindex⟩
  letI : Std.Antisymm (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨fun _ _ => nonpreemptivePriorityReindexedPastIndexLE_antisymm past reindex hreindex⟩
  letI : Std.Total (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨nonpreemptivePriorityReindexedPastIndexLE_total past reindex⟩
  exact ledger.sort (nonpreemptivePriorityReindexedPastIndexLE past reindex)

/-- Sorting a finite canonical ledger and then applying an injective reindexing
is the same as sorting its image whenever the two order relations correspond
under that reindexing. -/
theorem Finset.map_sort_nonpreemptivePriorityReindexedPastIndex
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (ledger : Finset (NonpreemptivePriorityCanonicalPastIndex n))
    (targetLE : NonpreemptivePriorityArrivalIndex n →
      NonpreemptivePriorityArrivalIndex n → Prop)
    [DecidableRel targetLE]
    [IsTrans (NonpreemptivePriorityArrivalIndex n) targetLE]
    [Std.Antisymm targetLE]
    [Std.Total targetLE]
    (horder : ∀ first ∈ ledger, ∀ second ∈ ledger,
      nonpreemptivePriorityReindexedPastIndexLE past reindex first second ↔
        targetLE (reindex first) (reindex second)) :
    (nonpreemptivePriorityReindexedPastWindowIndices past reindex hreindex ledger).map reindex =
      (ledger.image reindex).sort targetLE := by
  classical
  unfold nonpreemptivePriorityReindexedPastWindowIndices
  letI : DecidableRel (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨fun _ _ _ => nonpreemptivePriorityReindexedPastIndexLE_trans past reindex⟩
  letI : Std.Antisymm (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨fun _ _ => nonpreemptivePriorityReindexedPastIndexLE_antisymm past reindex hreindex⟩
  letI : Std.Total (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨nonpreemptivePriorityReindexedPastIndexLE_total past reindex⟩
  let embedding : NonpreemptivePriorityCanonicalPastIndex n ↪
      NonpreemptivePriorityArrivalIndex n := ⟨reindex, hreindex⟩
  have hsort := Finset.map_sort (s := ledger)
    (r := nonpreemptivePriorityReindexedPastIndexLE past reindex)
    (r' := targetLE) (f := embedding) horder
  simpa [embedding, Finset.map_eq_image] using hsort

/-- At a finite stationary horizon, the reindexed canonical chronological
ledger maps exactly to the literal stationary chronological ledger. -/
theorem nonpreemptivePriorityStationaryPastReindex_windowIndices_eq_canonical
    {n : ℕ}
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1) :
    (nonpreemptivePriorityReindexedPastWindowIndices
      (multiclassStationaryPoissonWorkPastCanonicalInput omega)
      (nonpreemptivePriorityStationaryPastReindex (n := n))
      Function.Injective.nonpreemptivePriorityStationaryPastReindex
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon)).map
        (nonpreemptivePriorityStationaryPastReindex (n := n)) =
      canonicalStationaryPriorityArrivalWindowIndices omega (-horizon) 0 := by
  classical
  let past := multiclassStationaryPoissonWorkPastCanonicalInput omega
  let reindex := nonpreemptivePriorityStationaryPastReindex (n := n)
  let ledger := nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  have hkey : ∀ q : NonpreemptivePriorityCanonicalPastIndex n,
      nonpreemptivePriorityReindexedPastIndexKey past reindex q =
        stationaryPriorityArrivalIndexKey omega (reindex q) := by
    rintro ⟨i, k⟩
    change toLex
        (nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) ⟨i, k⟩,
          (toLex (nonpreemptivePriorityStationaryPastReindex ⟨i, k⟩) :
            Σₗ j : Fin n, ℤ)) =
      toLex
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega
          (Probability.PoissonProcess.equilibriumBackwardArrivalIndex k),
          (toLex (nonpreemptivePriorityStationaryPastReindex ⟨i, k⟩) :
            Σₗ j : Fin n, ℤ))
    apply congrArg toLex
    apply Prod.ext
    · exact (multiclassStationaryPoissonWorkArrival_stationaryPastReindex_eq_canonical
        omega ⟨i, k⟩).symm
    · rfl
  have horder : ∀ first ∈ ledger, ∀ second ∈ ledger,
      nonpreemptivePriorityReindexedPastIndexLE past reindex first second ↔
        stationaryPriorityArrivalIndexLE omega (reindex first) (reindex second) := by
    intro first _ second _
    unfold nonpreemptivePriorityReindexedPastIndexLE stationaryPriorityArrivalIndexLE
    rw [hkey first, hkey second]
  rw [Finset.map_sort_nonpreemptivePriorityReindexedPastIndex
    past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex
    ledger (stationaryPriorityArrivalIndexLE omega) horder]
  rw [show ledger = nonpreemptivePriorityCanonicalPastWindowIndexLedger
      (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon by rfl,
    nonpreemptivePriorityStationaryPastReindex_windowIndexLedger_eq omega horizon hindices]
  rfl

/-- The finite priority jobs attached to a canonical ledger sorted by an
injective target-label reindexing. -/
def nonpreemptivePriorityCanonicalPastJob
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    NonpreemptivePriorityJob n (NonpreemptivePriorityCanonicalPastIndex n) :=
  { identifier := q
    priority := q.1
    arrivalTime := nonpreemptivePriorityCanonicalPastArrivalTime past q
    serviceWork := nonpreemptivePriorityCanonicalPastServiceWork meanService past q }

/-- The finite priority jobs attached to a canonical ledger sorted by an
injective target-label reindexing. -/
def nonpreemptivePriorityReindexedPastWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (ledger : Finset (NonpreemptivePriorityCanonicalPastIndex n)) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityCanonicalPastIndex n)) :=
  (nonpreemptivePriorityReindexedPastWindowIndices past reindex hreindex ledger).map
    (nonpreemptivePriorityCanonicalPastJob meanService past)

/-- Relabelling one canonical stationary job by the equilibrium backward
enumeration gives the corresponding literal stationary job coordinate. -/
theorem nonpreemptivePriorityCanonicalPastJob_map_stationaryPastReindex_eq
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    nonpreemptivePriorityJobMapIdentifier
      (nonpreemptivePriorityStationaryPastReindex (n := n))
      (nonpreemptivePriorityCanonicalPastJob meanService
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) q) =
      stationaryPriorityArrivalJobCoordinate meanService
        (nonpreemptivePriorityStationaryPastReindex q) omega := by
  rcases q with ⟨i, k⟩
  unfold nonpreemptivePriorityJobMapIdentifier
    nonpreemptivePriorityCanonicalPastJob stationaryPriorityArrivalJobCoordinate
  simp only [nonpreemptivePriorityStationaryPastReindex]
  congr 1
  · exact (multiclassStationaryPoissonWorkArrival_stationaryPastReindex_eq_canonical
      omega ⟨i, k⟩).symm

/-- At any finite stationary horizon, mapping the reindexed canonical jobs
recovers the literal stationary chronological job list exactly. -/
theorem nonpreemptivePriorityStationaryPastReindex_windowJobs_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1) :
    (nonpreemptivePriorityReindexedPastWindowJobs meanService
      (multiclassStationaryPoissonWorkPastCanonicalInput omega)
      (nonpreemptivePriorityStationaryPastReindex (n := n))
      Function.Injective.nonpreemptivePriorityStationaryPastReindex
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon)).map
        (nonpreemptivePriorityJobMapIdentifier
          (nonpreemptivePriorityStationaryPastReindex (n := n))) =
      canonicalStationaryPriorityArrivalWindowJobs meanService omega (-horizon) 0 := by
  let past := multiclassStationaryPoissonWorkPastCanonicalInput omega
  let reindex := nonpreemptivePriorityStationaryPastReindex (n := n)
  let ledger := nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon
  have hindicesList :
      (nonpreemptivePriorityReindexedPastWindowIndices past reindex
        Function.Injective.nonpreemptivePriorityStationaryPastReindex ledger).map reindex =
        canonicalStationaryPriorityArrivalWindowIndices omega (-horizon) 0 := by
    exact nonpreemptivePriorityStationaryPastReindex_windowIndices_eq_canonical
      omega horizon hindices
  unfold nonpreemptivePriorityReindexedPastWindowJobs
  rw [List.map_map]
  calc
    (nonpreemptivePriorityReindexedPastWindowIndices past reindex
        Function.Injective.nonpreemptivePriorityStationaryPastReindex ledger).map
        (fun q => nonpreemptivePriorityJobMapIdentifier reindex
          (nonpreemptivePriorityCanonicalPastJob meanService past q)) =
      (nonpreemptivePriorityReindexedPastWindowIndices past reindex
        Function.Injective.nonpreemptivePriorityStationaryPastReindex ledger).map
        (fun q => stationaryPriorityArrivalJobCoordinate meanService (reindex q) omega) := by
          apply List.map_congr_left
          intro q _
          exact nonpreemptivePriorityCanonicalPastJob_map_stationaryPastReindex_eq
            meanService omega q
    _ = (canonicalStationaryPriorityArrivalWindowIndices omega (-horizon) 0).map
        (fun q => stationaryPriorityArrivalJobCoordinate meanService q omega) := by
          rw [← hindicesList, List.map_map]
          rfl
    _ = canonicalStationaryPriorityArrivalWindowJobs meanService omega (-horizon) 0 := by
          rfl

/-- The finite stationary scalar workload can be computed by replaying the
canonical strict-past ledger after it has been placed in the literal
stationary chronological order.  Identifier relabelling is irrelevant to the
scalar trace recursion. -/
theorem nonpreemptivePriorityStationaryPastReindex_windowTerminalResidualWork_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
      (nonpreemptivePriorityReindexedPastWindowJobs meanService
        (multiclassStationaryPoissonWorkPastCanonicalInput omega)
        (nonpreemptivePriorityStationaryPastReindex (n := n))
        Function.Injective.nonpreemptivePriorityStationaryPastReindex
        (nonpreemptivePriorityCanonicalPastWindowIndexLedger
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon)) 0 =
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0 := by
  rw [← nonpreemptivePriorityArrivalTraceTerminalResidualWork_mapIdentifier
    (nonpreemptivePriorityStationaryPastReindex (n := n)) (-horizon) 0 0]
  rw [nonpreemptivePriorityStationaryPastReindex_windowJobs_eq_canonical
    meanService omega horizon hindices]
  rfl

/-- The class-selected reindexing sends the chronologically sorted canonical
past ledger to the literal selected/Palm chronological ledger. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowIndices_eq_canonical
    {n : ℕ} (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    (nonpreemptivePriorityReindexedPastWindowIndices
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
      (nonpreemptivePriorityClassTaggedPastReindex selected)
      (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon)).map
        (nonpreemptivePriorityClassTaggedPastReindex selected) =
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0 := by
  classical
  let past := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z
  let reindex := nonpreemptivePriorityClassTaggedPastReindex selected
  let ledger := nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE selected z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE selected z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans selected z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE selected z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm selected z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE selected z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total selected z⟩
  have hkey : ∀ q : NonpreemptivePriorityCanonicalPastIndex n,
      nonpreemptivePriorityReindexedPastIndexKey past reindex q =
        stationaryPriorityClassTaggedArrivalIndexKey selected z (reindex q) := by
    rintro ⟨j, k⟩
    unfold nonpreemptivePriorityReindexedPastIndexKey
      stationaryPriorityClassTaggedArrivalIndexKey
    dsimp [past, reindex]
    have hclass : (nonpreemptivePriorityClassTaggedPastReindex selected ⟨j, k⟩).1 = j := by
      by_cases hselected : j = selected <;>
        simp [nonpreemptivePriorityClassTaggedPastReindex, hselected]
    apply congrArg toLex
    apply Prod.ext
    · change nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) ⟨j, k⟩ =
        stationaryPriorityClassTaggedArrival selected z
          (nonpreemptivePriorityClassTaggedPastReindex selected ⟨j, k⟩).1
          (nonpreemptivePriorityClassTaggedPastReindex selected ⟨j, k⟩).2
      rw [hclass]
      exact (stationaryPriorityClassTaggedArrival_classTaggedPastReindex_eq_canonical
        selected z ⟨j, k⟩).symm
    · rfl
  have horder : ∀ first ∈ ledger, ∀ second ∈ ledger,
      nonpreemptivePriorityReindexedPastIndexLE past reindex first second ↔
        stationaryPriorityClassTaggedArrivalIndexLE selected z
          (reindex first) (reindex second) := by
    intro first _ second _
    unfold nonpreemptivePriorityReindexedPastIndexLE
      stationaryPriorityClassTaggedArrivalIndexLE
    rw [hkey first, hkey second]
  rw [Finset.map_sort_nonpreemptivePriorityReindexedPastIndex
    past reindex (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
    ledger (stationaryPriorityClassTaggedArrivalIndexLE selected z) horder]
  rw [show ledger = nonpreemptivePriorityCanonicalPastWindowIndexLedger
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon by rfl,
    nonpreemptivePriorityClassTaggedPastReindex_windowIndexLedger_eq
      selected z hgood horizon hpassive]
  rfl

/-- Relabelling one canonical selected/Palm job gives its literal physical
selected/Palm arrival-job coordinate. -/
theorem nonpreemptivePriorityCanonicalPastJob_map_classTaggedPastReindex_eq
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    nonpreemptivePriorityJobMapIdentifier
      (nonpreemptivePriorityClassTaggedPastReindex selected)
      (nonpreemptivePriorityCanonicalPastJob meanService
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) q) =
      stationaryPriorityClassTaggedArrivalJobCoordinate meanService selected
        (nonpreemptivePriorityClassTaggedPastReindex selected q) z := by
  rcases q with ⟨j, k⟩
  unfold nonpreemptivePriorityJobMapIdentifier
    nonpreemptivePriorityCanonicalPastJob
    stationaryPriorityClassTaggedArrivalJobCoordinate
  have hclass : (nonpreemptivePriorityClassTaggedPastReindex selected ⟨j, k⟩).1 = j := by
    by_cases hselected : j = selected <;>
      simp [nonpreemptivePriorityClassTaggedPastReindex, hselected]
  congr 1
  · exact hclass.symm
  · rw [hclass]
    exact (stationaryPriorityClassTaggedArrival_classTaggedPastReindex_eq_canonical
      selected z ⟨j, k⟩).symm
  · rw [hclass]
    exact (stationaryPriorityClassTaggedWorkRequirementAt_classTaggedPastReindex_eq_canonical
      meanService selected z ⟨j, k⟩).symm

/-- At any selected/Palm finite horizon, mapping the reindexed canonical jobs
recovers the literal chronological selected/Palm job list exactly. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowJobs_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    (nonpreemptivePriorityReindexedPastWindowJobs meanService
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
      (nonpreemptivePriorityClassTaggedPastReindex selected)
      (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon)).map
        (nonpreemptivePriorityJobMapIdentifier
          (nonpreemptivePriorityClassTaggedPastReindex selected)) =
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService selected z
        (-horizon) 0 := by
  let past := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z
  let reindex := nonpreemptivePriorityClassTaggedPastReindex selected
  let ledger := nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon
  have hindicesList :
      (nonpreemptivePriorityReindexedPastWindowIndices past reindex
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) ledger).map
          reindex =
        canonicalStationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0 := by
    exact nonpreemptivePriorityClassTaggedPastReindex_windowIndices_eq_canonical
      selected z hgood horizon hpassive
  unfold nonpreemptivePriorityReindexedPastWindowJobs
  rw [List.map_map]
  calc
    (nonpreemptivePriorityReindexedPastWindowIndices past reindex
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) ledger).map
        (fun q => nonpreemptivePriorityJobMapIdentifier reindex
          (nonpreemptivePriorityCanonicalPastJob meanService past q)) =
      (nonpreemptivePriorityReindexedPastWindowIndices past reindex
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) ledger).map
        (fun q => stationaryPriorityClassTaggedArrivalJobCoordinate meanService selected
          (reindex q) z) := by
          apply List.map_congr_left
          intro q _
          exact nonpreemptivePriorityCanonicalPastJob_map_classTaggedPastReindex_eq
            meanService selected z q
    _ = (canonicalStationaryPriorityClassTaggedArrivalWindowIndices selected z (-horizon) 0).map
        (fun q => stationaryPriorityClassTaggedArrivalJobCoordinate meanService selected q z) := by
          rw [← hindicesList, List.map_map]
          rfl
    _ = canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService selected z
        (-horizon) 0 := by
          rfl

/-- Replaying a canonical selected-arrival past and then relabelling its
complete queue state gives exactly the literal selected-arrival finite replay.
Unlike the scalar-workload statement, this retains the active job, every FIFO
queue, and the completion ledger. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowRun_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    nonpreemptivePriorityWorkStateMapIdentifier
        (nonpreemptivePriorityClassTaggedPastReindex selected)
        (runNonpreemptivePriorityArrivalTrace
          { currentTime := -horizon
            active := none
            waiting := fun _ => []
            completed := [] }
          (nonpreemptivePriorityReindexedPastWindowJobs meanService
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
            (nonpreemptivePriorityClassTaggedPastReindex selected)
            (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
            (nonpreemptivePriorityCanonicalPastWindowIndexLedger
              (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
              horizon))) =
      runNonpreemptivePriorityArrivalTrace
        { currentTime := -horizon
          active := none
          waiting := fun _ => []
          completed := [] }
        (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService selected z
          (-horizon) 0) := by
  rw [nonpreemptivePriorityWorkStateMapIdentifier_run]
  simp [nonpreemptivePriorityWorkStateMapIdentifier]
  rw [nonpreemptivePriorityClassTaggedPastReindex_windowJobs_eq_canonical
    meanService selected z hgood horizon hpassive]

/-- The exact terminal state of a finite canonical selected-arrival replay,
after identifiers are relabelled, is the literal selected-arrival finite
window state.  In particular, the transport includes the service performed
after the last arrival before the observation epoch. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowState_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    nonpreemptivePriorityWorkStateMapIdentifier
        (nonpreemptivePriorityClassTaggedPastReindex selected)
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace
              (emptyNonpreemptivePriorityWorkState
                (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon))
              (nonpreemptivePriorityReindexedPastWindowJobs meanService
                (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
                (nonpreemptivePriorityClassTaggedPastReindex selected)
                (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
                (nonpreemptivePriorityCanonicalPastWindowIndexLedger
                  (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
                  horizon))))
          0
          (runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon))
            (nonpreemptivePriorityReindexedPastWindowJobs meanService
              (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
              (nonpreemptivePriorityClassTaggedPastReindex selected)
              (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
              (nonpreemptivePriorityCanonicalPastWindowIndexLedger
                (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
                horizon)))) =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-horizon) 0 := by
  let initial : NonpreemptivePriorityWorkState n
      (NonpreemptivePriorityCanonicalPastIndex n) :=
    emptyNonpreemptivePriorityWorkState (-horizon)
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (nonpreemptivePriorityReindexedPastWindowJobs meanService
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
      (nonpreemptivePriorityClassTaggedPastReindex selected)
      (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
        horizon))
  let literalInitial : NonpreemptivePriorityWorkState n
      (NonpreemptivePriorityArrivalIndex n) :=
    emptyNonpreemptivePriorityWorkState (-horizon)
  let literalAfterArrivals := runNonpreemptivePriorityArrivalTrace literalInitial
    (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService selected z
      (-horizon) 0)
  have hrun : nonpreemptivePriorityWorkStateMapIdentifier
      (nonpreemptivePriorityClassTaggedPastReindex selected) afterArrivals =
        literalAfterArrivals := by
    dsimp [afterArrivals, initial, literalAfterArrivals, literalInitial]
    exact nonpreemptivePriorityClassTaggedPastReindex_windowRun_eq_canonical
      meanService selected z hgood horizon hpassive
  have hcount : totalNonpreemptivePriorityWorkJobs afterArrivals =
      totalNonpreemptivePriorityWorkJobs literalAfterArrivals := by
    rw [← hrun]
    exact (totalNonpreemptivePriorityWorkJobs_mapIdentifier
      (nonpreemptivePriorityClassTaggedPastReindex selected) afterArrivals).symm
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  change nonpreemptivePriorityWorkStateMapIdentifier
      (nonpreemptivePriorityClassTaggedPastReindex selected)
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) 0 afterArrivals) =
    advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs literalAfterArrivals) 0 literalAfterArrivals
  rw [nonpreemptivePriorityWorkStateMapIdentifier_advance, hcount, hrun]

/-- The finite selected/Palm scalar workload can be computed by replaying the
canonical strict-past ledger after it has been placed in the literal
selected/Palm chronological order. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowTerminalResidualWork_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
      (nonpreemptivePriorityReindexedPastWindowJobs meanService
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
        (nonpreemptivePriorityClassTaggedPastReindex selected)
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
        (nonpreemptivePriorityCanonicalPastWindowIndexLedger
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon)) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-horizon) 0 := by
  rw [← nonpreemptivePriorityArrivalTraceTerminalResidualWork_mapIdentifier
    (nonpreemptivePriorityClassTaggedPastReindex selected) (-horizon) 0 0]
  rw [nonpreemptivePriorityClassTaggedPastReindex_windowJobs_eq_canonical
    meanService selected z hgood horizon hpassive]
  rfl

/-- The total order induced by the physical-time and stream-label key. -/
def nonpreemptivePriorityCanonicalPastIndexLE
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (first second : NonpreemptivePriorityCanonicalPastIndex n) : Prop :=
  nonpreemptivePriorityCanonicalPastIndexKey past first ≤
    nonpreemptivePriorityCanonicalPastIndexKey past second

theorem nonpreemptivePriorityCanonicalPastIndexLE_trans
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    {first second third : NonpreemptivePriorityCanonicalPastIndex n}
    (hfirst : nonpreemptivePriorityCanonicalPastIndexLE past first second)
    (hsecond : nonpreemptivePriorityCanonicalPastIndexLE past second third) :
    nonpreemptivePriorityCanonicalPastIndexLE past first third := by
  exact hfirst.trans hsecond

theorem nonpreemptivePriorityCanonicalPastIndexLE_total
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (first second : NonpreemptivePriorityCanonicalPastIndex n) :
    nonpreemptivePriorityCanonicalPastIndexLE past first second ∨
      nonpreemptivePriorityCanonicalPastIndexLE past second first := by
  exact le_total _ _

theorem nonpreemptivePriorityCanonicalPastIndexLE_antisymm
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    {first second : NonpreemptivePriorityCanonicalPastIndex n}
    (hfirst : nonpreemptivePriorityCanonicalPastIndexLE past first second)
    (hsecond : nonpreemptivePriorityCanonicalPastIndexLE past second first) :
    first = second := by
  apply Function.Injective.nonpreemptivePriorityCanonicalPastIndexKey past
  exact le_antisymm hfirst hsecond

/-- The chronologically ordered canonical-past index ledger. -/
noncomputable def canonicalNonpreemptivePriorityPastWindowIndices
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) : List (NonpreemptivePriorityCanonicalPastIndex n) := by
  classical
  letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
  letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
  letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
  exact (nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon).sort
    (nonpreemptivePriorityCanonicalPastIndexLE past)

/-- Membership in the canonical chronological ledger is exactly membership in
the corresponding finite renewal prefix. -/
theorem mem_canonicalNonpreemptivePriorityPastWindowIndices_iff
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) (q : NonpreemptivePriorityCanonicalPastIndex n) :
    q ∈ canonicalNonpreemptivePriorityPastWindowIndices past horizon ↔
      q.2 < Probability.PoissonProcess.canonicalRenewalCount horizon (past q.1).1 := by
  classical
  letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
  letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
  letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
  simp [canonicalNonpreemptivePriorityPastWindowIndices,
    nonpreemptivePriorityCanonicalPastWindowIndexLedger,
    nonpreemptivePriorityCanonicalPastWindowIndices]

/-- The canonical strict-past jobs, in deterministic chronological order. -/
noncomputable def canonicalNonpreemptivePriorityPastWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityCanonicalPastIndex n)) :=
  (canonicalNonpreemptivePriorityPastWindowIndices past horizon).map
    (nonpreemptivePriorityCanonicalPastJob meanService past)

/-- Canonical-past jobs inherit the finite ledger's time-and-label order. -/
theorem pairwise_nonpreemptivePriorityCanonicalPastIndexLE_windowIndices
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) :
    (canonicalNonpreemptivePriorityPastWindowIndices past horizon).Pairwise
      (nonpreemptivePriorityCanonicalPastIndexLE past) := by
  classical
  letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
  letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
  letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
  exact Finset.pairwise_sort _ _

/-- The canonical finite priority replay begins empty at `-horizon`, executes
all strict-past arrivals, and then supplies service through the origin. -/
def canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) : ℝ :=
  nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
    (canonicalNonpreemptivePriorityPastWindowJobs meanService past horizon) 0

/-- The physical epoch of a fixed canonical-past coordinate is Borel. -/
theorem measurable_nonpreemptivePriorityCanonicalPastArrivalTime
    {n : ℕ} (q : NonpreemptivePriorityCanonicalPastIndex n) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      nonpreemptivePriorityCanonicalPastArrivalTime past q) := by
  unfold nonpreemptivePriorityCanonicalPastArrivalTime
  exact measurable_neg.comp
    ((Probability.PoissonProcess.measurable_arrivalTime q.2).comp
      (measurable_fst.comp (measurable_pi_apply q.1)))

/-- The chronological comparison of two fixed canonical-past labels is a
Borel condition. -/
theorem measurableSet_nonpreemptivePriorityCanonicalPastIndexLE
    {n : ℕ} (first second : NonpreemptivePriorityCanonicalPastIndex n) :
    MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      nonpreemptivePriorityCanonicalPastIndexLE past first second} := by
  classical
  unfold nonpreemptivePriorityCanonicalPastIndexLE
    nonpreemptivePriorityCanonicalPastIndexKey
  simp only [Prod.Lex.toLex_le_toLex]
  let firstTime : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ :=
    fun past => nonpreemptivePriorityCanonicalPastArrivalTime past first
  let secondTime : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ :=
    fun past => nonpreemptivePriorityCanonicalPastArrivalTime past second
  have hfirst : Measurable firstTime := by
    simpa [firstTime] using
      measurable_nonpreemptivePriorityCanonicalPastArrivalTime first
  have hsecond : Measurable secondTime := by
    simpa [secondTime] using
      measurable_nonpreemptivePriorityCanonicalPastArrivalTime second
  by_cases hlabel : (toLex (first.1, first.2) : Fin n ×ₗ ℕ) ≤
      toLex (second.1, second.2)
  · simp only [Prod.Lex.toLex_le_toLex] at hlabel
    simpa [firstTime, secondTime, hlabel] using
      (hfirst.lt hsecond).or (hfirst.eq hsecond)
  · simp only [Prod.Lex.toLex_le_toLex] at hlabel
    simpa [firstTime, secondTime, hlabel] using hfirst.lt hsecond

/-- Pairwise chronological ordering of one fixed canonical-past label list
is Borel. -/
theorem measurableSet_nonpreemptivePriorityCanonicalPastIndexList_pairwise
    {n : ℕ} (labels : List (NonpreemptivePriorityCanonicalPastIndex n)) :
    MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      labels.Pairwise (nonpreemptivePriorityCanonicalPastIndexLE past)} := by
  induction labels with
  | nil => simp
  | cons first labels ih =>
      have hhead : MeasurableSet {past : Fin n →
          StationaryPoissonWorkPastCanonicalSample |
          ∀ later ∈ labels,
            nonpreemptivePriorityCanonicalPastIndexLE past first later} := by
        rw [show {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
            ∀ later ∈ labels,
              nonpreemptivePriorityCanonicalPastIndexLE past first later} =
            ⋂ later ∈ labels.toFinset, {past |
              nonpreemptivePriorityCanonicalPastIndexLE past first later} by
          ext past
          simp]
        exact labels.toFinset.measurableSet_biInter fun later _ =>
          measurableSet_nonpreemptivePriorityCanonicalPastIndexLE first later
      simpa only [List.pairwise_cons] using hhead.inter ih

/-- Membership of a fixed canonical-past label in a finite horizon ledger is
a Borel condition. -/
theorem measurableSet_mem_nonpreemptivePriorityCanonicalPastWindowIndexLedger
    {n : ℕ} (horizon : ℝ) (q : NonpreemptivePriorityCanonicalPastIndex n) :
    MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      q ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon} := by
  have hcount : Measurable (fun past : Fin n →
      StationaryPoissonWorkPastCanonicalSample =>
      Probability.PoissonProcess.canonicalRenewalCount horizon (past q.1).1) :=
    (Probability.PoissonProcess.measurable_canonicalRenewalCount horizon).comp
      (measurable_fst.comp (measurable_pi_apply q.1))
  simpa [nonpreemptivePriorityCanonicalPastWindowIndexLedger,
    nonpreemptivePriorityCanonicalPastWindowIndices] using
    (measurableSet_lt measurable_const hcount)

/-- Every fixed finite canonical-past ledger has a Borel fiber. -/
theorem measurableSet_nonpreemptivePriorityCanonicalPastWindowIndexLedger_eq
    {n : ℕ} (horizon : ℝ)
    (labels : Finset (NonpreemptivePriorityCanonicalPastIndex n)) :
    MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityCanonicalPastIndex n,
      MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
        q ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon} := by
    intro q
    exact measurableSet_mem_nonpreemptivePriorityCanonicalPastWindowIndexLedger horizon q
  have hfiber : ∀ q : NonpreemptivePriorityCanonicalPastIndex n,
      MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
        q ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon ↔
          q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {past : Fin n →
          StationaryPoissonWorkPastCanonicalSample |
          q ∉ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon = labels} =
      ⋂ q : NonpreemptivePriorityCanonicalPastIndex n, {past |
        q ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon ↔
          q ∈ labels} := by
    ext past
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The sorted canonical-past index ledger has a Borel fiber at each fixed
finite label list. -/
theorem measurableSet_canonicalNonpreemptivePriorityPastWindowIndices_eq
    {n : ℕ} (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n)) :
    MeasurableSet {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      canonicalNonpreemptivePriorityPastWindowIndices past horizon = labels} := by
  classical
  have hledger := measurableSet_nonpreemptivePriorityCanonicalPastWindowIndexLedger_eq
    horizon labels.toFinset
  have hpairwise := measurableSet_nonpreemptivePriorityCanonicalPastIndexList_pairwise
    labels
  have hnodup : MeasurableSet {past : Fin n →
      StationaryPoissonWorkPastCanonicalSample | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {past : Fin n → StationaryPoissonWorkPastCanonicalSample |
      canonicalNonpreemptivePriorityPastWindowIndices past horizon = labels} =
      ({past | nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon =
          labels.toFinset} ∩
        {past | labels.Pairwise (nonpreemptivePriorityCanonicalPastIndexLE past)}) ∩
          {past | labels.Nodup} := by
    ext past
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
          (nonpreemptivePriorityCanonicalPastIndexLE past) :=
        ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
      letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
        ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
      letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
        ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalNonpreemptivePriorityPastWindowIndices past horizon).toFinset =
            nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact pairwise_nonpreemptivePriorityCanonicalPastIndexLE_windowIndices past horizon
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
          (nonpreemptivePriorityCanonicalPastIndexLE past) :=
        ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
      letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
        ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
      letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
        ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
      have hsorted : labels.toFinset.sort
          (nonpreemptivePriorityCanonicalPastIndexLE past) = labels := by
        exact (List.toFinset_sort (r := nonpreemptivePriorityCanonicalPastIndexLE past)
          hnodup).mpr hpairwise
      unfold canonicalNonpreemptivePriorityPastWindowIndices
      rw [hledger, hsorted]
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- The variable coordinates of one fixed canonical-past job are Borel. -/
theorem nonpreemptivePriorityCanonicalPastJob_coordinatesMeasurable
    {n : ℕ} (meanService : Fin n → ℝ)
    (q : NonpreemptivePriorityCanonicalPastIndex n) :
    NonpreemptivePriorityJob.CoordinatesMeasurable
      (fun past => nonpreemptivePriorityCanonicalPastJob meanService past q) := by
  constructor
  · exact measurable_nonpreemptivePriorityCanonicalPastArrivalTime q
  · change Measurable (fun past : Fin n →
        StationaryPoissonWorkPastCanonicalSample =>
        meanService q.1 * (past q.1).2 q.2)
    exact measurable_const.mul
      ((measurable_pi_apply q.2).comp
        (measurable_snd.comp (measurable_pi_apply q.1)))

/-- The scalar terminal workload of a canonical finite strict-past replay is
Borel.  The proof conditions on its countable family of finite label lists. -/
theorem measurable_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (horizon : ℝ) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon) := by
  refine Probability.measurable_of_countable_measurable_cover
    (fun labels : List (NonpreemptivePriorityCanonicalPastIndex n) =>
      {past | canonicalNonpreemptivePriorityPastWindowIndices past horizon = labels})
    (fun labels =>
      measurableSet_canonicalNonpreemptivePriorityPastWindowIndices_eq horizon labels)
    ?_ (fun past =>
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon)
    (fun labels past => nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
      (evaluateNonpreemptivePriorityJobList
        (labels.map (fun q past =>
          nonpreemptivePriorityCanonicalPastJob meanService past q)) past) 0)
    ?_ ?_
  · ext past
    constructor
    · intro _
      simp
    · intro _
      exact Set.mem_iUnion.mpr
        ⟨canonicalNonpreemptivePriorityPastWindowIndices past horizon, rfl⟩
  · intro labels
    apply measurable_nonpreemptivePriorityArrivalTraceTerminalResidualWork_eval
      (fun _ => -horizon) (fun _ => 0) (fun _ => 0) measurable_const measurable_const
      measurable_const
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
    exact nonpreemptivePriorityCanonicalPastJob_coordinatesMeasurable meanService q
  · intro labels past hlabels
    simp only [canonicalNonpreemptivePriorityPastWindowTerminalResidualWork,
      canonicalNonpreemptivePriorityPastWindowJobs,
      nonpreemptivePriorityCanonicalPastJob,
      evaluateNonpreemptivePriorityJobList, List.map_map]
    rw [hlabels]
    rfl

/-- If a finite canonical ledger has no simultaneous physical arrivals, any
injective relabelling used only as a secondary sorting key gives the same
chronological canonical ledger.  This isolates the harmless tie-breaking
issue from the probabilistic no-collision argument. -/
theorem nonpreemptivePriorityReindexedPastWindowIndices_eq_canonical_of_noArrivalTies
    {n : ℕ}
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (horizon : ℝ)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime past first =
        nonpreemptivePriorityCanonicalPastArrivalTime past second → first = second) :
    nonpreemptivePriorityReindexedPastWindowIndices past reindex hreindex
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon) =
      canonicalNonpreemptivePriorityPastWindowIndices past horizon := by
  classical
  let ledger := nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon
  letI : DecidableRel (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨fun _ _ _ => nonpreemptivePriorityReindexedPastIndexLE_trans past reindex⟩
  letI : Std.Antisymm (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨fun _ _ => nonpreemptivePriorityReindexedPastIndexLE_antisymm past reindex hreindex⟩
  letI : Std.Total (nonpreemptivePriorityReindexedPastIndexLE past reindex) :=
    ⟨nonpreemptivePriorityReindexedPastIndexLE_total past reindex⟩
  letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
  letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
  letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
  have horder : ∀ first ∈ ledger, ∀ second ∈ ledger,
      nonpreemptivePriorityReindexedPastIndexLE past reindex first second ↔
        nonpreemptivePriorityCanonicalPastIndexLE past first second := by
    intro first hfirst second hsecond
    by_cases htime : nonpreemptivePriorityCanonicalPastArrivalTime past first =
        nonpreemptivePriorityCanonicalPastArrivalTime past second
    · have heq : first = second := hnoTies first hfirst second hsecond htime
      subst second
      simp [nonpreemptivePriorityReindexedPastIndexLE,
        nonpreemptivePriorityCanonicalPastIndexLE]
    · simp [nonpreemptivePriorityReindexedPastIndexLE,
        nonpreemptivePriorityCanonicalPastIndexLE,
        nonpreemptivePriorityReindexedPastIndexKey,
        nonpreemptivePriorityCanonicalPastIndexKey,
        Prod.Lex.toLex_le_toLex, htime]
  let identityEmbedding : NonpreemptivePriorityCanonicalPastIndex n ↪
      NonpreemptivePriorityCanonicalPastIndex n :=
    ⟨id, Function.injective_id⟩
  have hsort := Finset.map_sort
    identityEmbedding ledger
    (nonpreemptivePriorityReindexedPastIndexLE past reindex)
    (nonpreemptivePriorityCanonicalPastIndexLE past) horder
  have hmap_id : ∀ list : List (NonpreemptivePriorityCanonicalPastIndex n),
      list.map identityEmbedding = list := by
    intro list
    induction list with
    | nil => rfl
    | cons q list ih =>
        simp only [List.map_cons]
        rw [ih]
        rfl
  have hfinset_id : Finset.map identityEmbedding ledger = ledger := by
    ext q
    simp [identityEmbedding]
  rw [hfinset_id] at hsort
  change ledger.sort (nonpreemptivePriorityReindexedPastIndexLE past reindex) =
    ledger.sort (nonpreemptivePriorityCanonicalPastIndexLE past)
  exact (hmap_id _).symm.trans hsort

/-- Under the no-simultaneous-arrival condition, the scalar workload of a
relabelled finite replay is the workload of the canonical strict-past replay. -/
theorem nonpreemptivePriorityReindexedPastWindowTerminalResidualWork_eq_canonical_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (horizon : ℝ)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime past first =
        nonpreemptivePriorityCanonicalPastArrivalTime past second → first = second) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
      (nonpreemptivePriorityReindexedPastWindowJobs meanService past reindex hreindex
        (nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon)) 0 =
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
        meanService past horizon := by
  unfold nonpreemptivePriorityReindexedPastWindowJobs
    canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
    canonicalNonpreemptivePriorityPastWindowJobs
  rw [nonpreemptivePriorityReindexedPastWindowIndices_eq_canonical_of_noArrivalTies
    past reindex hreindex horizon hnoTies]

/-- On a collision-free finite stationary window, the literal stationary
terminal workload is exactly the canonical strict-past workload. -/
theorem stationaryPriorityFiniteWindowTerminalResidualWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) second → first = second) :
    stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0 =
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon := by
  exact (nonpreemptivePriorityStationaryPastReindex_windowTerminalResidualWork_eq_canonical
    meanService omega horizon hindices).symm.trans
      (nonpreemptivePriorityReindexedPastWindowTerminalResidualWork_eq_canonical_of_noArrivalTies
        meanService (multiclassStationaryPoissonWorkPastCanonicalInput omega)
        (nonpreemptivePriorityStationaryPastReindex (n := n))
        Function.Injective.nonpreemptivePriorityStationaryPastReindex horizon hnoTies)

/-- At every fixed finite horizon, the literal stationary replay and its
canonical strict-past replay have the same terminal workload almost surely. -/
theorem ae_stationaryPriorityFiniteWindowTerminalResidualWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0 =
        canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon := by
  have hpastIndices : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ i : Fin n,
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1 := by
    let μ : Fin n → Measure StationaryPoissonWorkPath := fun i =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
    letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
      Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
        (harrivalRate i)
    rw [ae_all_iff]
    intro i
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun z : StationaryPoissonWorkPath =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 z.1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium z).1)
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).measurable.aemeasurable ?_
    have hmap : Measure.map (Function.eval i) (Measure.pi μ) =
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i) := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          arrivalRate harrivalRate i).map_eq
    rw [hmap]
    exact
      Probability.Queueing.ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
        (harrivalRate i) horizon
  filter_upwards [
    hpastIndices,
    ae_multiclassStationaryPoissonWorkPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate] with omega hindices hcollision
  apply stationaryPriorityFiniteWindowTerminalResidualWork_eq_canonicalPast_of_noArrivalTies
    meanService omega horizon hindices
  intro first _ second _ heq
  rcases first with ⟨firstClass, firstIndex⟩
  rcases second with ⟨secondClass, secondIndex⟩
  have htime : Probability.PoissonProcess.arrivalTime firstIndex
      (multiclassStationaryPoissonWorkPastCanonicalInput omega firstClass).1 =
      Probability.PoissonProcess.arrivalTime secondIndex
        (multiclassStationaryPoissonWorkPastCanonicalInput omega secondClass).1 := by
    exact neg_injective (by simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
  rcases hcollision firstClass secondClass firstIndex secondIndex htime with
    ⟨hclasses, hindices⟩
  subst secondClass
  subst secondIndex
  rfl

/-- On a collision-free finite selected/Palm window, the literal selected/Palm
terminal workload is exactly the common canonical strict-past workload. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) second → first = second) :
    canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
      meanService selected z (-horizon) 0 =
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon := by
  exact (nonpreemptivePriorityClassTaggedPastReindex_windowTerminalResidualWork_eq_canonical
    meanService selected z hgood horizon hpassive).symm.trans
      (nonpreemptivePriorityReindexedPastWindowTerminalResidualWork_eq_canonical_of_noArrivalTies
        meanService (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
        (nonpreemptivePriorityClassTaggedPastReindex selected)
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) horizon hnoTies)

/-- At every fixed finite horizon, the literal selected-arrival replay and its
canonical strict-past replay have the same terminal workload almost surely. -/
theorem ae_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-horizon) 0 =
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate selected,
    ae_multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood
      arrivalRate harrivalRate selected horizon,
    ae_multiclassStationaryPoissonWorkClassTaggedPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate selected] with z hgood hpassive hcollision
  apply canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_canonicalPast_of_noArrivalTies
    meanService selected z hgood horizon
  · intro i hiselected
    exact hpassive ⟨i, hiselected⟩
  · intro first _ second _ heq
    rcases first with ⟨firstClass, firstIndex⟩
    rcases second with ⟨secondClass, secondIndex⟩
    have htime : Probability.PoissonProcess.arrivalTime firstIndex
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
          selected z firstClass).1 =
        Probability.PoissonProcess.arrivalTime secondIndex
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
            selected z secondClass).1 := by
      exact neg_injective (by
        simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
    rcases hcollision firstClass secondClass firstIndex secondIndex htime with
      ⟨hclasses, hindices⟩
    subst secondClass
    subst secondIndex
    rfl

/-- Natural-horizon literal stationary terminal workloads eventually equal the
causal remote-past workload almost surely. -/
theorem ae_eventually_stationaryPriorityFiniteWindowTerminalResidualWork_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
          (-(horizon : ℝ)) 0 =
        stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_eventually_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive hcoalesces
  filter_upwards [hcoalesces] with horizon hhorizon
  have hfinite : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
        (-(horizon : ℝ)) 0 := by
    simpa [stationaryPriorityFiniteWindowTerminalResidualWork] using
      totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon)) (by
            intro job hjob
            rcases (mem_stationaryPriorityArrivalWindowJobs_iff
              meanService omega (-(horizon : ℝ)) 0 job).mp hjob with
                ⟨i, k, _, hjob⟩
            subst job
            exact hpositive i k)
  exact hfinite.symm.trans hhorizon

/-- Natural-horizon literal selected-arrival terminal workloads eventually
equal the causal selected remote-past workload almost surely. -/
theorem ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
          meanService selected z (-(horizon : ℝ)) 0 =
        stationaryPriorityClassTaggedRemotePastResidualWork meanService selected z := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService selected,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate selected,
    ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable selected] with z hpositive hgood hcoalesces
  filter_upwards [hcoalesces] with horizon hhorizon
  have hfinite : totalNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService selected z (-(horizon : ℝ)) 0) =
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-(horizon : ℝ)) 0 := by
    simpa [canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork] using
      totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
        meanService selected z (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon)) hgood (by
            intro job hjob
            rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
              meanService selected z (-(horizon : ℝ)) 0 job).mp hjob with
                ⟨j, k, _, hcoordinate⟩
            subst job
            exact hpositive j k)
  exact hfinite.symm.trans hhorizon

/-- The finite stationary terminal workload has the law of the measurable
canonical strict-past replay. -/
theorem stationaryPriorityFiniteWindowTerminalResidualWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    HasLaw
      (fun omega =>
        stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0)
      (Measure.map
        (fun past =>
          canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
            meanService past horizon)
        (Measure.pi fun i =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun i =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
      meanService horizon).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_stationaryPriorityFiniteWindowTerminalResidualWork_eq_canonicalPast
      arrivalRate meanService harrivalRate horizon] with omega heq
  exact heq

/-- The finite selected-arrival terminal workload has the same measurable
canonical strict-past replay law. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    HasLaw
      (fun z => canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-horizon) 0)
      (Measure.map
        (fun past =>
          canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
            meanService past horizon)
        (Measure.pi fun i =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  let canonical := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun i =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate selected)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
      meanService horizon).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_canonicalPast
      arrivalRate meanService harrivalRate selected horizon] with z heq
  exact heq

/-- At every fixed finite horizon, the selected-arrival and stationary
priority replays have identical terminal-workload laws. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_hasLaw_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    HasLaw
      (fun z => canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-horizon) 0)
      (Measure.map
        (fun omega =>
          stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0)
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  have hstationary :=
    stationaryPriorityFiniteWindowTerminalResidualWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate horizon
  have hselected :=
    canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate selected horizon
  refine ⟨hselected.aemeasurable, ?_⟩
  exact hselected.map_eq.trans hstationary.map_eq.symm

/-- The causal selected-arrival remote-past workload has the stationary
remote-past workload law.  The proof transports the exact common finite-window
law through almost-sure eventual stabilization; it does not use an expectation
interchange. -/
theorem stationaryPriorityClassTaggedRemotePastResidualWork_hasLaw_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    HasLaw
      (stationaryPriorityClassTaggedRemotePastResidualWork meanService selected)
      (Measure.map (stationaryPriorityRemotePastResidualWork meanService)
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  let Pstationary :=
    Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected :=
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  letI : IsProbabilityMeasure Pstationary := by
    dsimp [Pstationary]
    exact
      Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
        arrivalRate harrivalRate
  letI : IsProbabilityMeasure Pselected := by
    dsimp [Pselected]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).isProbability
  let stationaryFinite : ℕ → (Fin n → (Probability.PoissonProcess.GoodSuspensionState ×
      (ℤ → ℝ))) → ℝ := fun horizon omega =>
    stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
      (-(horizon : ℝ)) 0
  let selectedFinite : ℕ →
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected → ℝ :=
    fun horizon z =>
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-(horizon : ℝ)) 0
  let stationaryRemote := stationaryPriorityRemotePastResidualWork meanService
  let selectedRemote :=
    stationaryPriorityClassTaggedRemotePastResidualWork meanService selected
  have hstationaryAE : ∀ᵐ omega ∂Pstationary,
      Tendsto (fun horizon => stationaryFinite horizon omega) Filter.atTop
        (nhds (stationaryRemote omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowTerminalResidualWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by
      simpa [stationaryFinite, stationaryRemote] using heventual)
  have hstationaryMeasure : TendstoInMeasure Pstationary stationaryFinite Filter.atTop
      stationaryRemote := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro horizon
      exact (measurable_stationaryPriorityFiniteWindowTerminalResidualWork
        meanService (-(horizon : ℝ)) 0).aestronglyMeasurable
    · exact hstationaryAE
  have hstationaryDistribution : TendstoInDistribution stationaryFinite Filter.atTop
      stationaryRemote (fun _ => Pstationary) Pstationary :=
    hstationaryMeasure.tendstoInDistribution (fun horizon =>
      (measurable_stationaryPriorityFiniteWindowTerminalResidualWork
        meanService (-(horizon : ℝ)) 0).aemeasurable)
  have hselectedAE : ∀ᵐ z ∂Pselected,
      Tendsto (fun horizon => selectedFinite horizon z) Filter.atTop
        (nhds (selectedRemote z)) := by
    filter_upwards [
      ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable selected] with z heventual
    exact tendsto_nhds_of_eventually_eq (by
      simpa [selectedFinite, selectedRemote] using heventual)
  have hselectedMeasure : TendstoInMeasure Pselected selectedFinite Filter.atTop
      selectedRemote := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro horizon
      exact
        (measurable_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
          meanService selected (-(horizon : ℝ)) 0).aestronglyMeasurable
    · exact hselectedAE
  have hselectedDistribution : TendstoInDistribution selectedFinite Filter.atTop
      selectedRemote (fun _ => Pselected) Pselected :=
    hselectedMeasure.tendstoInDistribution (fun horizon =>
      (measurable_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected (-(horizon : ℝ)) 0).aemeasurable)
  have hselectedToStationary : TendstoInDistribution selectedFinite Filter.atTop
      stationaryRemote (fun _ => Pselected) Pstationary := by
    refine ⟨?_, ?_, ?_⟩
    · intro horizon
      simpa [selectedFinite, Pselected] using
        (canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_hasLaw_stationary
          arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable
    · simpa [stationaryRemote, Pstationary] using
        (aemeasurable_stationaryPriorityRemotePastResidualWork
          arrivalRate meanService harrivalRate hmeanService hstable)
    · apply hstationaryDistribution.tendsto.congr'
      apply Filter.Eventually.of_forall
      intro horizon
      apply Subtype.ext
      simpa [stationaryFinite, selectedFinite, Pstationary, Pselected] using
        (canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_hasLaw_stationary
          arrivalRate meanService harrivalRate selected (horizon : ℝ)).map_eq.symm
  have hmap : Pstationary.map stationaryRemote = Pselected.map selectedRemote :=
    tendstoInDistribution_unique selectedFinite hselectedToStationary hselectedDistribution
  refine ⟨?_, ?_⟩
  · simpa [selectedRemote, Pselected] using
      (aemeasurable_stationaryPriorityClassTaggedRemotePastResidualWork
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  · simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using hmap.symm

/-- The selected-arrival remote workload is integrable exactly when the
stationary remote workload is integrable. -/
theorem integrable_stationaryPriorityClassTaggedRemotePastResidualWork_iff_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    Integrable (stationaryPriorityClassTaggedRemotePastResidualWork meanService selected)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag ↔
    Integrable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let Pstationary :=
    Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected :=
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let stationaryRemote := stationaryPriorityRemotePastResidualWork meanService
  let selectedRemote :=
    stationaryPriorityClassTaggedRemotePastResidualWork meanService selected
  have hstationary : HasLaw stationaryRemote (Pstationary.map stationaryRemote)
      Pstationary := ⟨by
        simpa [stationaryRemote, Pstationary] using
          (aemeasurable_stationaryPriorityRemotePastResidualWork
            arrivalRate meanService harrivalRate hmeanService hstable), rfl⟩
  have hselected : HasLaw selectedRemote (Pstationary.map stationaryRemote)
      Pselected := by
    simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
      (stationaryPriorityClassTaggedRemotePastResidualWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  exact (hstationary.identDistrib hselected).symm.integrable_iff

/-- The selected-arrival and stationary remote workloads have equal integrals
in the extended Bochner convention. -/
theorem integral_stationaryPriorityClassTaggedRemotePastResidualWork_eq_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    ∫ z, stationaryPriorityClassTaggedRemotePastResidualWork meanService selected z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag =
    ∫ omega, stationaryPriorityRemotePastResidualWork meanService omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  let Pstationary :=
    Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected :=
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let stationaryRemote := stationaryPriorityRemotePastResidualWork meanService
  let selectedRemote :=
    stationaryPriorityClassTaggedRemotePastResidualWork meanService selected
  have hstationary : HasLaw stationaryRemote (Pstationary.map stationaryRemote)
      Pstationary := ⟨by
        simpa [stationaryRemote, Pstationary] using
          (aemeasurable_stationaryPriorityRemotePastResidualWork
            arrivalRate meanService harrivalRate hmeanService hstable), rfl⟩
  have hselected : HasLaw selectedRemote (Pstationary.map stationaryRemote)
      Pselected := by
    simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
      (stationaryPriorityClassTaggedRemotePastResidualWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
    (hstationary.identDistrib hselected).symm.integral_eq

/-- Post-admission selected workload is integrable exactly when the stationary
remote workload is integrable.  The added tagged service mark is already an
integrable exponential observable. -/
theorem integrable_stationaryPriorityClassTaggedArrivalTotalWork_iff_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    Integrable (stationaryPriorityClassTaggedArrivalTotalWork meanService selected)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag ↔
    Integrable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let Pselected :=
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let remote := stationaryPriorityClassTaggedRemotePastResidualWork meanService selected
  let taggedWork := stationaryPriorityClassTaggedWorkRequirement meanService selected
  have htaggedWork : Integrable taggedWork Pselected := by
    simpa [taggedWork, Pselected] using
      (integrable_stationaryPriorityClassTaggedWorkRequirement
        arrivalRate meanService harrivalRate hmeanService selected)
  have hadd : Integrable (stationaryPriorityClassTaggedArrivalTotalWork
      meanService selected) Pselected ↔ Integrable remote Pselected := by
    simpa [stationaryPriorityClassTaggedArrivalTotalWork, remote, taggedWork] using
      (integrable_add_iff_integrable_left' htaggedWork)
  exact hadd.trans
    (integrable_stationaryPriorityClassTaggedRemotePastResidualWork_iff_stationary
      arrivalRate meanService harrivalRate hmeanService hstable selected)

/-- Once the stationary remote workload is integrable, post-admission selected
work has the stationary mean plus the selected class's mean service work. -/
theorem integral_stationaryPriorityClassTaggedArrivalTotalWork_eq_stationary_add_meanService
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n)
    (hintegrable : Integrable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) :
    ∫ z, stationaryPriorityClassTaggedArrivalTotalWork meanService selected z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag =
      (∫ omega, stationaryPriorityRemotePastResidualWork meanService omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) +
        meanService selected := by
  let Pselected :=
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let remote := stationaryPriorityClassTaggedRemotePastResidualWork meanService selected
  let taggedWork := stationaryPriorityClassTaggedWorkRequirement meanService selected
  have hremote : Integrable remote Pselected := by
    simpa [remote, Pselected] using
      (integrable_stationaryPriorityClassTaggedRemotePastResidualWork_iff_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected).mpr hintegrable
  have htaggedWork : Integrable taggedWork Pselected := by
    simpa [taggedWork, Pselected] using
      (integrable_stationaryPriorityClassTaggedWorkRequirement
        arrivalRate meanService harrivalRate hmeanService selected)
  calc
    ∫ z, stationaryPriorityClassTaggedArrivalTotalWork meanService selected z ∂Pselected =
        (∫ z, remote z ∂Pselected) + ∫ z, taggedWork z ∂Pselected := by
          simpa [stationaryPriorityClassTaggedArrivalTotalWork, remote, taggedWork] using
            (integral_add hremote htaggedWork)
    _ = (∫ omega, stationaryPriorityRemotePastResidualWork meanService omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) +
        meanService selected := by
          rw [integral_stationaryPriorityClassTaggedRemotePastResidualWork_eq_stationary
            arrivalRate meanService harrivalRate hmeanService hstable selected]
          simpa [taggedWork, Pselected] using
            (integral_stationaryPriorityClassTaggedWorkRequirement
              arrivalRate meanService harrivalRate hmeanService selected)

end

end AppliedModelingLib.Queueing

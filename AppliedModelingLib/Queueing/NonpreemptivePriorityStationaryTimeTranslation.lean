import AppliedModelingLib.Queueing.NonpreemptivePriorityIdentifierTransport
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastReplay
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityTimeTranslationTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityTagWaiting

/-!
# Time covariance of stationary priority-input windows

The stationary marked input action changes both physical time and the local
integer labels of each class's arrival stream.  This module records the
label restoration map and the exact membership transport for finite arrival
windows.  Subsequent results lift these ingredients through canonical ordering
and deterministic queue replay.
-/

namespace AppliedModelingLib
namespace Queueing

open ProbabilityTheory

noncomputable section

/-- Restore a class-labelled arrival index from shifted input coordinates to
the corresponding index in the original marked input. -/
def stationaryPriorityFlowRestoreIndex
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) :
    NonpreemptivePriorityArrivalIndex n → NonpreemptivePriorityArrivalIndex n :=
  fun q => ⟨q.1,
    Probability.PoissonProcess.suspensionCrossingIndexPastClosed
      offset (omega q.1).1.1 + q.2⟩

/-- The flow's label-restoration map is injective. -/
theorem Function.Injective.stationaryPriorityFlowRestoreIndex
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) :
    Function.Injective (stationaryPriorityFlowRestoreIndex omega offset) := by
  rintro ⟨firstClass, firstIndex⟩ ⟨secondClass, secondIndex⟩ heq
  change (⟨firstClass,
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega firstClass).1.1 + firstIndex⟩ :
      NonpreemptivePriorityArrivalIndex n) =
    ⟨secondClass,
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega secondClass).1.1 + secondIndex⟩ at heq
  injection heq with hclass hindex
  subst secondClass
  have hindices : firstIndex = secondIndex := by omega
  subst secondIndex
  rfl

/-- The injective embedding associated with stationary-input label restoration. -/
def stationaryPriorityFlowRestoreEmbedding
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) :
    NonpreemptivePriorityArrivalIndex n ↪ NonpreemptivePriorityArrivalIndex n :=
  ⟨stationaryPriorityFlowRestoreIndex omega offset,
    Function.Injective.stationaryPriorityFlowRestoreIndex omega offset⟩

/-- Label restoration under the stationary input flow is a bijection: on
each class it is just translation of the integer arrival index.  The
equivalence form is useful when a countable customer sum is moved between a
flow-coordinate state and the original physical-time labels. -/
noncomputable def stationaryPriorityFlowRestoreEquiv
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) :
    NonpreemptivePriorityArrivalIndex n ≃ NonpreemptivePriorityArrivalIndex n where
  toFun := stationaryPriorityFlowRestoreIndex omega offset
  invFun := fun q => ⟨q.1,
    q.2 - Probability.PoissonProcess.suspensionCrossingIndexPastClosed
      offset (omega q.1).1.1⟩
  left_inv := by
    rintro ⟨i, k⟩
    change (⟨i,
      (Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega i).1.1 + k) -
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed
          offset (omega i).1.1⟩ : NonpreemptivePriorityArrivalIndex n) = ⟨i, k⟩
    congr 1
    omega
  right_inv := by
    rintro ⟨i, k⟩
    change (⟨i,
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega i).1.1 +
        (k - Probability.PoissonProcess.suspensionCrossingIndexPastClosed
          offset (omega i).1.1)⟩ : NonpreemptivePriorityArrivalIndex n) = ⟨i, k⟩
    congr 1
    omega

@[simp]
theorem stationaryPriorityFlowRestoreEquiv_apply
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    stationaryPriorityFlowRestoreEquiv omega offset q =
      stationaryPriorityFlowRestoreIndex omega offset q := rfl

/-- Membership in a shifted finite arrival window is membership of the
restored label in the original physical window. -/
theorem mem_stationaryPriorityArrivalWindowIndices_flow_iff
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ) (i : Fin n) (k : ℤ) :
    k ∈ stationaryPriorityArrivalWindowIndices
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        (a - offset) (b - offset) i ↔
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed
          offset (omega i).1.1 + k ∈
        stationaryPriorityArrivalWindowIndices omega a b i := by
  unfold stationaryPriorityArrivalWindowIndices
  rw [Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff,
    Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff]
  change a - offset ≤ Probability.PoissonProcess.suspensionBaseArrival
      (Probability.PoissonProcess.goodSuspensionFlow offset (omega i).1) k ∧
      Probability.PoissonProcess.suspensionBaseArrival
        (Probability.PoissonProcess.goodSuspensionFlow offset (omega i).1) k <
          b - offset ↔
    a ≤ Probability.PoissonProcess.suspensionBaseArrival (omega i).1
      (Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega i).1.1 + k) ∧
      Probability.PoissonProcess.suspensionBaseArrival (omega i).1
        (Probability.PoissonProcess.suspensionCrossingIndexPastClosed
          offset (omega i).1.1 + k) < b
  rw [Probability.PoissonProcess.suspensionBaseArrival_goodSuspensionFlow]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- Restoring labels maps the shifted finite stationary arrival ledger
bijectively onto the original ledger. -/
theorem stationaryPriorityArrivalWindowIndexLedger_flow_restore
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ) :
    Finset.map (stationaryPriorityFlowRestoreEmbedding omega offset)
      (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          (a - offset) (b - offset))) =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a b) := by
  ext q
  rcases q with ⟨i, k⟩
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hrestore⟩
    rcases q with ⟨j, l⟩
    change stationaryPriorityFlowRestoreIndex omega offset ⟨j, l⟩ = ⟨i, k⟩ at hrestore
    injection hrestore with hclass hindex
    change j = i at hclass
    subst j
    have hmember : Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega i).1.1 + l ∈ stationaryPriorityArrivalWindowIndices omega a b i :=
      (mem_stationaryPriorityArrivalWindowIndices_flow_iff omega offset a b i l).mp
        (by simpa [nonpreemptivePriorityArrivalWindowIndices,
          stationaryPriorityArrivalWindowIndices] using hq)
    have hindex' : Probability.PoissonProcess.suspensionCrossingIndexPastClosed
        offset (omega i).1.1 + l = k := by
      simpa [stationaryPriorityFlowRestoreIndex] using hindex
    simpa [nonpreemptivePriorityArrivalWindowIndices,
      stationaryPriorityArrivalWindowIndices, hindex'] using hmember
  · intro hq
    let crossing : ℤ := Probability.PoissonProcess.suspensionCrossingIndexPastClosed
      offset (omega i).1.1
    have hmember : k - crossing ∈ stationaryPriorityArrivalWindowIndices
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        (a - offset) (b - offset) i := by
      apply (mem_stationaryPriorityArrivalWindowIndices_flow_iff
        omega offset a b i (k - crossing)).mpr
      have hcross : crossing + (k - crossing) = k := by
        dsimp [crossing]
        omega
      change Probability.PoissonProcess.suspensionCrossingIndexPastClosed
          offset (omega i).1.1 + (k - crossing) ∈
        stationaryPriorityArrivalWindowIndices omega a b i
      rw [show Probability.PoissonProcess.suspensionCrossingIndexPastClosed
          offset (omega i).1.1 = crossing by rfl, hcross]
      simpa [nonpreemptivePriorityArrivalWindowIndices,
        stationaryPriorityArrivalWindowIndices] using hq
    refine ⟨⟨i, k - crossing⟩, ?_, ?_⟩
    · simpa [nonpreemptivePriorityArrivalWindowIndices,
        stationaryPriorityArrivalWindowIndices] using hmember
    · change stationaryPriorityFlowRestoreIndex omega offset ⟨i, k - crossing⟩ =
        (⟨i, k⟩ : NonpreemptivePriorityArrivalIndex n)
      dsimp [stationaryPriorityFlowRestoreIndex, crossing]
      congr 1
      omega

/-- The epoch of a restored shifted label is the original physical epoch in
the translated time coordinate. -/
theorem stationaryPriorityArrivalTime_flow_restore
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) q.2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        (stationaryPriorityFlowRestoreIndex omega offset q).1 omega
        (stationaryPriorityFlowRestoreIndex omega offset q).2 - offset := by
  rcases q with ⟨i, k⟩
  simpa [stationaryPriorityFlowRestoreIndex] using
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival_flow
      omega offset i k)

/-- The class-scaled work mark of a restored shifted label is the original
work mark. -/
theorem stationaryPriorityWorkRequirement_flow_restore
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    stationaryPriorityWorkRequirement meanService q.1
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) q.2 =
      stationaryPriorityWorkRequirement meanService
        (stationaryPriorityFlowRestoreIndex omega offset q).1 omega
        (stationaryPriorityFlowRestoreIndex omega offset q).2 := by
  rcases q with ⟨i, k⟩
  simp only [stationaryPriorityFlowRestoreIndex, stationaryPriorityWorkRequirement]
  rw [Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement_flow]

/-- Translating the stationary input and translating the physical window in
the opposite direction preserve its scalar marked-work total.  Unlike the
state-valued replay covariance, this finite-sum identity needs no
no-simultaneous-arrivals premise. -/
theorem stationaryPriorityArrivalWindowTotalWork_flow
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ) :
    stationaryPriorityArrivalWindowTotalWork meanService
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
      (a - offset) (b - offset) =
      stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
  classical
  unfold stationaryPriorityArrivalWindowTotalWork
  apply Finset.sum_congr rfl
  intro i _
  let crossing : ℤ := Probability.PoissonProcess.suspensionCrossingIndexPastClosed
    offset (omega i).1.1
  refine Finset.sum_bij
    (f := fun k => stationaryPriorityWorkRequirement meanService i
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) k)
    (g := fun k => stationaryPriorityWorkRequirement meanService i omega k)
    (fun k _ => crossing + k) ?_ ?_ ?_ ?_
  · intro k hk
    exact (mem_stationaryPriorityArrivalWindowIndices_flow_iff omega offset a b i k).mp
      (by simpa [crossing] using hk)
  · intro first hfirst second hsecond heq
    dsimp [crossing] at heq
    omega
  · intro k hk
    refine ⟨k - crossing, ?_, ?_⟩
    · apply (mem_stationaryPriorityArrivalWindowIndices_flow_iff
        omega offset a b i (k - crossing)).mpr
      have hcross : crossing + (k - crossing) = k := by omega
      simpa [crossing, hcross] using hk
    · dsimp [crossing]
      omega
  · intro k hk
    simpa [crossing] using
      (stationaryPriorityWorkRequirement_flow_restore meanService omega offset ⟨i, k⟩)

/-- The backward marked-work aggregate after a stationary time shift is the
original aggregate on the corresponding physical interval ending at the
shift epoch. -/
theorem stationaryPriorityTotalPastWorkAggregate_flow_eq_window
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset t : ℝ) :
    stationaryPriorityTotalPastWorkAggregate meanService
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) t =
      stationaryPriorityArrivalWindowTotalWork meanService omega (offset - t) offset := by
  rw [← stationaryPriorityArrivalWindowTotalWork_neg_to_zero]
  convert stationaryPriorityArrivalWindowTotalWork_flow meanService omega offset
    (offset - t) offset using 1 <;> ring_nf

/-- On a nonpositive time shift, the shifted net input is the original net
input at the correspondingly longer horizon, up to the fixed initial-window
correction. -/
theorem stationaryPriorityNetPastInput_flow_eq_of_nonpos
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset t : ℝ) (hoffset : offset ≤ 0) (ht : 0 ≤ t) :
    stationaryPriorityNetPastInput meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) t =
      stationaryPriorityNetPastInput meanService omega (t - offset) +
        (-offset - stationaryPriorityTotalPastWorkAggregate meanService omega (-offset)) := by
  have hwindow := stationaryPriorityArrivalWindowTotalWork_neg_to_neg
    meanService omega (t - offset) (-offset) (by linarith) (by linarith)
  have hwindow' : stationaryPriorityArrivalWindowTotalWork meanService omega
      (offset - t) offset =
        stationaryPriorityTotalPastWorkAggregate meanService omega (t - offset) -
          stationaryPriorityTotalPastWorkAggregate meanService omega (-offset) := by
    convert hwindow using 1 <;> ring_nf
  unfold stationaryPriorityNetPastInput
  rw [stationaryPriorityTotalPastWorkAggregate_flow_eq_window, hwindow']
  ring

/-- On a nonnegative time shift and after the shifted origin, the shifted net
input is the original net input at the remaining horizon, plus the fixed work
accumulated between the two origins. -/
theorem stationaryPriorityNetPastInput_flow_eq_of_nonneg
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset t : ℝ) (hoffset : 0 ≤ offset) (ht : offset ≤ t) :
    stationaryPriorityNetPastInput meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) t =
      stationaryPriorityNetPastInput meanService omega (t - offset) +
        (-offset + stationaryPriorityArrivalWindowTotalWork meanService omega 0 offset) := by
  have happend := stationaryPriorityArrivalWindowTotalWork_append
    meanService omega (offset - t) 0 offset (by linarith) hoffset
  have hpast := stationaryPriorityArrivalWindowTotalWork_neg_to_zero
    meanService omega (t - offset)
  have hpast' : stationaryPriorityArrivalWindowTotalWork meanService omega
      (offset - t) 0 = stationaryPriorityTotalPastWorkAggregate meanService omega
        (t - offset) := by
    convert hpast using 1 <;> ring_nf
  rw [hpast'] at happend
  unfold stationaryPriorityNetPastInput
  rw [stationaryPriorityTotalPastWorkAggregate_flow_eq_window, happend]
  ring

/-- A stationary time shift preserves the property that the backward
net-input path tends to `-∞`.  The preceding identities reduce the shifted
path, eventually, to a translated copy of the original path. -/
theorem stationaryPriorityNetPastInput_flow_tendsto_atBot
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ)
    (hlimit : Filter.Tendsto (stationaryPriorityNetPastInput meanService omega)
      Filter.atTop Filter.atBot) :
    Filter.Tendsto
      (stationaryPriorityNetPastInput meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega))
      Filter.atTop Filter.atBot := by
  have htime : Filter.Tendsto (fun t : ℝ => t - offset)
      Filter.atTop Filter.atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (-offset) Filter.tendsto_id)
  have hshifted : Filter.Tendsto
      (fun t : ℝ => stationaryPriorityNetPastInput meanService omega (t - offset))
      Filter.atTop Filter.atBot := hlimit.comp htime
  by_cases hoffset : offset ≤ 0
  · let correction : ℝ := -offset -
      stationaryPriorityTotalPastWorkAggregate meanService omega (-offset)
    have hcorrected : Filter.Tendsto
        (fun t : ℝ => stationaryPriorityNetPastInput meanService omega (t - offset) +
          correction) Filter.atTop Filter.atBot :=
      Filter.tendsto_atBot_add_const_right Filter.atTop correction hshifted
    refine hcorrected.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact (stationaryPriorityNetPastInput_flow_eq_of_nonpos
      meanService omega offset t hoffset ht).symm
  · have hoffset' : 0 ≤ offset := by linarith
    let correction : ℝ := -offset +
      stationaryPriorityArrivalWindowTotalWork meanService omega 0 offset
    have hcorrected : Filter.Tendsto
        (fun t : ℝ => stationaryPriorityNetPastInput meanService omega (t - offset) +
          correction) Filter.atTop Filter.atBot :=
      Filter.tendsto_atBot_add_const_right Filter.atTop correction hshifted
    refine hcorrected.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop offset] with t ht
    exact (stationaryPriorityNetPastInput_flow_eq_of_nonneg
      meanService omega offset t hoffset' ht).symm

/-- Every stationary time shift of a path with negative-drifting backward
net input has a nonnegative maximizing cutoff. -/
theorem exists_stationaryPriorityNetPastCutoff_flow_of_tendsto_atBot
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ)
    (hlimit : Filter.Tendsto (stationaryPriorityNetPastInput meanService omega)
      Filter.atTop Filter.atBot) :
    ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) cutoff :=
  exists_stationaryPriorityNetPastCutoff_of_tendsto_atBot meanService _
    (stationaryPriorityNetPastInput_flow_tendsto_atBot meanService omega offset hlimit)

/-- Under strict total load, a stationary input almost surely admits a
nonnegative net-input cutoff after every deterministic time shift. -/
theorem ae_all_exists_stationaryPriorityNetPastCutoff_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ offset : ℝ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityNetPastCutoff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) cutoff := by
  filter_upwards [ae_tendsto_stationaryPriorityNetPastInput_atBot
    arrivalRate meanService harrivalRate hstable] with omega hlimit
  intro offset
  exact exists_stationaryPriorityNetPastCutoff_flow_of_tendsto_atBot
    meanService omega offset hlimit

/-- If a finite stationary window has no simultaneous physical arrivals,
restoring shifted labels carries its canonical chronology to the original
canonical chronology. -/
theorem canonicalStationaryPriorityArrivalWindowIndices_flow_restore_of_noArrivalTies
    {n : ℕ}
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second) :
    (canonicalStationaryPriorityArrivalWindowIndices
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
      (a - offset) (b - offset)).map
        (stationaryPriorityFlowRestoreEmbedding omega offset) =
      canonicalStationaryPriorityArrivalWindowIndices omega a b := by
  classical
  let shiftedLedger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
      (a - offset) (b - offset))
  let originalLedger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega a b)
  let restore := stationaryPriorityFlowRestoreEmbedding omega offset
  have hledger : Finset.map restore shiftedLedger = originalLedger := by
    simpa [shiftedLedger, originalLedger, restore] using
      stationaryPriorityArrivalWindowIndexLedger_flow_restore omega offset a b
  have hrestore_mem : ∀ q ∈ shiftedLedger,
      restore q ∈ originalLedger := by
    intro q hq
    rw [← hledger]
    exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
  have horder : ∀ first ∈ shiftedLedger, ∀ second ∈ shiftedLedger,
      stationaryPriorityArrivalIndexLE
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        first second ↔
        stationaryPriorityArrivalIndexLE omega (restore first) (restore second) := by
    intro first hfirst second hsecond
    have hfirstOriginal := hrestore_mem first hfirst
    have hsecondOriginal := hrestore_mem second hsecond
    by_cases htime :
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          (restore first).1 omega (restore first).2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          (restore second).1 omega (restore second).2
    · have hrestoreEq : restore first = restore second :=
        hnoTies (restore first) hfirstOriginal (restore second) hsecondOriginal htime
      have hfirstEq : first = second := restore.injective hrestoreEq
      subst second
      constructor <;> intro _ <;> exact le_rfl
    · let firstTime : ℝ :=
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          (restore first).1 omega (restore first).2
      let secondTime : ℝ :=
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          (restore second).1 omega (restore second).2
      have hfirstFlow :
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
            first.2 = firstTime - offset := by
        simpa [firstTime] using
          stationaryPriorityArrivalTime_flow_restore omega offset first
      have hsecondFlow :
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
            second.2 = secondTime - offset := by
        simpa [secondTime] using
          stationaryPriorityArrivalTime_flow_restore omega offset second
      change firstTime ≠ secondTime at htime
      unfold stationaryPriorityArrivalIndexLE stationaryPriorityArrivalIndexKey
      simp only [Prod.Lex.toLex_le_toLex]
      rw [hfirstFlow, hsecondFlow]
      change (firstTime - offset < secondTime - offset ∨
        (firstTime - offset = secondTime - offset ∧ toLex first ≤ toLex second)) ↔
        (firstTime < secondTime ∨
          (firstTime = secondTime ∧ toLex (restore first) ≤ toLex (restore second)))
      constructor
      · rintro (hless | ⟨heq, _⟩)
        · exact Or.inl (by linarith)
        · exact (htime (by linarith)).elim
      · rintro (hless | ⟨heq, _⟩)
        · exact Or.inl (by linarith)
        · exact (htime heq).elim
  letI : DecidableRel (stationaryPriorityArrivalIndexLE
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)⟩
  letI : Std.Antisymm
      (stationaryPriorityArrivalIndexLE
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)⟩
  letI : Std.Total
      (stationaryPriorityArrivalIndexLE
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)) :=
    ⟨stationaryPriorityArrivalIndexLE_total
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)⟩
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  have hsort := Finset.map_sort restore shiftedLedger
    (stationaryPriorityArrivalIndexLE
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega))
    (stationaryPriorityArrivalIndexLE omega) horder
  rw [hledger] at hsort
  change (shiftedLedger.sort (stationaryPriorityArrivalIndexLE
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega))).map restore =
    originalLedger.sort (stationaryPriorityArrivalIndexLE omega)
  exact hsort

/-- Restoring a shifted label and translating its physical time maps one
stationary job coordinate to the corresponding original coordinate. -/
theorem stationaryPriorityArrivalJobCoordinate_flow_restore
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    nonpreemptivePriorityJobMapIdentifier
        (stationaryPriorityFlowRestoreEmbedding omega offset)
        (stationaryPriorityArrivalJobCoordinate meanService q
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)) =
      translateNonpreemptivePriorityJob offset
        (stationaryPriorityArrivalJobCoordinate meanService
          (stationaryPriorityFlowRestoreIndex omega offset q) omega) := by
  rcases q with ⟨i, k⟩
  simp only [stationaryPriorityArrivalJobCoordinate,
    nonpreemptivePriorityJobMapIdentifier,
    translateNonpreemptivePriorityJob,
    stationaryPriorityFlowRestoreEmbedding,
    stationaryPriorityFlowRestoreIndex]
  rw [stationaryPriorityArrivalTime_flow_restore omega offset ⟨i, k⟩,
    stationaryPriorityWorkRequirement_flow_restore meanService omega offset ⟨i, k⟩]
  rfl

/-- After restoring labels, the stationary jobs in a collision-free shifted
window are exactly the translated original stationary job ledger. -/
theorem stationaryPriorityArrivalWindowJobs_flow_restore_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second) :
    (stationaryPriorityArrivalWindowJobs meanService
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
      (a - offset) (b - offset)).map
        (nonpreemptivePriorityJobMapIdentifier
          (stationaryPriorityFlowRestoreEmbedding omega offset)) =
      (stationaryPriorityArrivalWindowJobs meanService omega a b).map
        (translateNonpreemptivePriorityJob offset) := by
  have hindices := canonicalStationaryPriorityArrivalWindowIndices_flow_restore_of_noArrivalTies
    omega offset a b hnoTies
  unfold stationaryPriorityArrivalWindowJobs canonicalStationaryPriorityArrivalWindowJobs
  change ((canonicalStationaryPriorityArrivalWindowIndices
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
      (a - offset) (b - offset)).map
        (fun q => stationaryPriorityArrivalJobCoordinate meanService q
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega))).map
      (nonpreemptivePriorityJobMapIdentifier
        (stationaryPriorityFlowRestoreEmbedding omega offset)) =
    ((canonicalStationaryPriorityArrivalWindowIndices omega a b).map
      (fun q => stationaryPriorityArrivalJobCoordinate meanService q omega)).map
        (translateNonpreemptivePriorityJob offset)
  rw [← hindices]
  simp only [List.map_map]
  apply List.map_congr_left
  intro q hq
  exact stationaryPriorityArrivalJobCoordinate_flow_restore meanService omega offset q

/-- Restoring shifted labels carries the finite priority state of a
collision-free stationary window to the translated finite state of the
original window. -/
theorem stationaryPriorityFiniteWindowState_flow_restore_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second) :
    nonpreemptivePriorityWorkStateMapIdentifier
      (stationaryPriorityFlowRestoreEmbedding omega offset)
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        (a - offset) (b - offset)) =
      translateNonpreemptivePriorityWorkState offset
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  let restore := stationaryPriorityFlowRestoreEmbedding omega offset
  let shiftedJobs := stationaryPriorityArrivalWindowJobs meanService
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
    (a - offset) (b - offset)
  let originalJobs := stationaryPriorityArrivalWindowJobs meanService omega a b
  let shiftedInitial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (a - offset)
  let originalInitial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let shiftedAfter := runNonpreemptivePriorityArrivalTrace shiftedInitial shiftedJobs
  let originalAfter := runNonpreemptivePriorityArrivalTrace originalInitial originalJobs
  change nonpreemptivePriorityWorkStateMapIdentifier restore
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs shiftedAfter) (b - offset) shiftedAfter) =
    translateNonpreemptivePriorityWorkState offset
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs originalAfter) b originalAfter)
  have hinitial : nonpreemptivePriorityWorkStateMapIdentifier restore shiftedInitial =
      translateNonpreemptivePriorityWorkState offset originalInitial := by
    rfl
  have hjobs : shiftedJobs.map (nonpreemptivePriorityJobMapIdentifier restore) =
      originalJobs.map (translateNonpreemptivePriorityJob offset) := by
    simpa [shiftedJobs, originalJobs, restore] using
      stationaryPriorityArrivalWindowJobs_flow_restore_of_noArrivalTies
        meanService omega offset a b hnoTies
  have hafter : nonpreemptivePriorityWorkStateMapIdentifier restore shiftedAfter =
      translateNonpreemptivePriorityWorkState offset originalAfter := by
    calc
      nonpreemptivePriorityWorkStateMapIdentifier restore shiftedAfter =
          runNonpreemptivePriorityArrivalTrace
            (nonpreemptivePriorityWorkStateMapIdentifier restore shiftedInitial)
            (shiftedJobs.map (nonpreemptivePriorityJobMapIdentifier restore)) := by
              exact nonpreemptivePriorityWorkStateMapIdentifier_run restore shiftedInitial shiftedJobs
      _ = runNonpreemptivePriorityArrivalTrace
            (translateNonpreemptivePriorityWorkState offset originalInitial)
            (originalJobs.map (translateNonpreemptivePriorityJob offset)) := by
              rw [hinitial, hjobs]
      _ = translateNonpreemptivePriorityWorkState offset originalAfter := by
              symm
              exact translateNonpreemptivePriorityWorkState_run
                offset originalInitial originalJobs
  have hcount : totalNonpreemptivePriorityWorkJobs shiftedAfter =
      totalNonpreemptivePriorityWorkJobs originalAfter := by
    calc
      totalNonpreemptivePriorityWorkJobs shiftedAfter =
          totalNonpreemptivePriorityWorkJobs
            (nonpreemptivePriorityWorkStateMapIdentifier restore shiftedAfter) := by
              symm
              exact totalNonpreemptivePriorityWorkJobs_mapIdentifier restore shiftedAfter
      _ = totalNonpreemptivePriorityWorkJobs
            (translateNonpreemptivePriorityWorkState offset originalAfter) := by
              rw [hafter]
      _ = totalNonpreemptivePriorityWorkJobs originalAfter :=
        totalNonpreemptivePriorityWorkJobs_translate offset originalAfter
  rw [nonpreemptivePriorityWorkStateMapIdentifier_advance, hcount, hafter]
  symm
  exact translateNonpreemptivePriorityWorkState_advance
    offset (totalNonpreemptivePriorityWorkJobs originalAfter) b originalAfter

/-- Under a collision-free stationary time shift, a finite FIFO-membership
observation transports by the corresponding restored arrival identifier. -/
theorem nonpreemptivePriorityWaitingIdentifier_stationaryPriorityFiniteWindow_flow_restore_iff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second)
    (identifier : NonpreemptivePriorityArrivalIndex n) :
    nonpreemptivePriorityWaitingIdentifier identifier
        (stationaryPriorityFiniteWindowState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          (a - offset) (b - offset)) ↔
      nonpreemptivePriorityWaitingIdentifier
        (stationaryPriorityFlowRestoreIndex omega offset identifier)
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  let restore := stationaryPriorityFlowRestoreEmbedding omega offset
  let shiftedState := stationaryPriorityFiniteWindowState meanService
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
    (a - offset) (b - offset)
  let originalState := stationaryPriorityFiniteWindowState meanService omega a b
  have hstate : nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState =
      translateNonpreemptivePriorityWorkState offset originalState := by
    simpa [restore, shiftedState, originalState] using
      stationaryPriorityFiniteWindowState_flow_restore_of_noArrivalTies
        meanService omega offset a b hnoTies
  calc
    nonpreemptivePriorityWaitingIdentifier identifier shiftedState ↔
        nonpreemptivePriorityWaitingIdentifier (restore identifier)
          (nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState) := by
            symm
            exact nonpreemptivePriorityWaitingIdentifier_mapIdentifier_iff
              restore restore.injective identifier shiftedState
    _ ↔ nonpreemptivePriorityWaitingIdentifier (restore identifier)
          (translateNonpreemptivePriorityWorkState offset originalState) := by
            rw [hstate]
    _ ↔ nonpreemptivePriorityWaitingIdentifier (restore identifier) originalState :=
      nonpreemptivePriorityWaitingIdentifier_translate_iff
        (restore identifier) offset originalState

/-- Active residual work is invariant under a collision-free stationary
finite-window time shift. -/
theorem activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_flow
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second) :
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        (a - offset) (b - offset)) =
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  let restore := stationaryPriorityFlowRestoreEmbedding omega offset
  let shiftedState := stationaryPriorityFiniteWindowState meanService
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
    (a - offset) (b - offset)
  let originalState := stationaryPriorityFiniteWindowState meanService omega a b
  have hstate : nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState =
      translateNonpreemptivePriorityWorkState offset originalState := by
    simpa [restore, shiftedState, originalState] using
      stationaryPriorityFiniteWindowState_flow_restore_of_noArrivalTies
        meanService omega offset a b hnoTies
  calc
    activeNonpreemptivePriorityResidualWork shiftedState =
        activeNonpreemptivePriorityResidualWork
          (nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState) := by
            symm
            exact activeNonpreemptivePriorityResidualWork_mapIdentifier restore shiftedState
    _ = activeNonpreemptivePriorityResidualWork
          (translateNonpreemptivePriorityWorkState offset originalState) := by
            rw [hstate]
    _ = activeNonpreemptivePriorityResidualWork originalState :=
      activeNonpreemptivePriorityResidualWork_translate offset originalState

/-- The squared residual-service ledger is invariant under a collision-free
stationary finite-window time shift. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_stationaryPriorityFiniteWindow_flow
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second) :
    totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        (a - offset) (b - offset)) =
      totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  let restore := stationaryPriorityFlowRestoreEmbedding omega offset
  let shiftedState := stationaryPriorityFiniteWindowState meanService
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
    (a - offset) (b - offset)
  let originalState := stationaryPriorityFiniteWindowState meanService omega a b
  have hstate : nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState =
      translateNonpreemptivePriorityWorkState offset originalState := by
    simpa [restore, shiftedState, originalState] using
      stationaryPriorityFiniteWindowState_flow_restore_of_noArrivalTies
        meanService omega offset a b hnoTies
  calc
    totalNonpreemptivePrioritySquaredResidualWork shiftedState =
        totalNonpreemptivePrioritySquaredResidualWork
          (nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState) := by
            symm
            exact totalNonpreemptivePrioritySquaredResidualWork_mapIdentifier
              restore shiftedState
    _ = totalNonpreemptivePrioritySquaredResidualWork
          (translateNonpreemptivePriorityWorkState offset originalState) := by
            rw [hstate]
    _ = totalNonpreemptivePrioritySquaredResidualWork originalState :=
      totalNonpreemptivePrioritySquaredResidualWork_translate offset originalState

/-- At-least-as-urgent waiting work is invariant under a collision-free
stationary finite-window time shift. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_flow
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset a b : ℝ) (priority : Fin n)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
        (a - offset) (b - offset)) priority =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega a b) priority := by
  let restore := stationaryPriorityFlowRestoreEmbedding omega offset
  let shiftedState := stationaryPriorityFiniteWindowState meanService
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
    (a - offset) (b - offset)
  let originalState := stationaryPriorityFiniteWindowState meanService omega a b
  have hstate : nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState =
      translateNonpreemptivePriorityWorkState offset originalState := by
    simpa [restore, shiftedState, originalState] using
      stationaryPriorityFiniteWindowState_flow_restore_of_noArrivalTies
        meanService omega offset a b hnoTies
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent shiftedState priority =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (nonpreemptivePriorityWorkStateMapIdentifier restore shiftedState) priority := by
            symm
            exact priorityWaitingResidualWorkAtLeastAsUrgent_mapIdentifier
              restore shiftedState priority
    _ = priorityWaitingResidualWorkAtLeastAsUrgent
          (translateNonpreemptivePriorityWorkState offset originalState) priority := by
            rw [hstate]
    _ = priorityWaitingResidualWorkAtLeastAsUrgent originalState priority :=
      priorityWaitingResidualWorkAtLeastAsUrgent_translate offset originalState priority

/-- Distinct class-labelled stationary arrivals in any fixed finite physical
window have distinct epochs almost surely.  This is the strict-past
collision-free input law transported through the measure-preserving
stationary time action. -/
theorem ae_stationaryPriorityArrivalWindow_noArrivalTies
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
        ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b),
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              first.1 omega first.2 =
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              second.1 omega second.2 → first = second := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
    arrivalRate
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
    (Class := Fin n) b
  have hflowNoTies : ∀ᵐ omega ∂P,
      ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices (flow omega) (a - b) 0),
        ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices (flow omega) (a - b) 0),
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              first.1 (flow omega) first.2 =
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              second.1 (flow omega) second.2 → first = second := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := flow)
      (p := fun omega =>
        ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices omega (a - b) 0),
          ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices omega (a - b) 0),
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
                first.1 omega first.2 =
              Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
                second.1 omega second.2 → first = second)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
        arrivalRate harrivalRate b).measurable.aemeasurable ?_
    rw [(Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
      arrivalRate harrivalRate b).map_eq]
    simpa [stationaryPriorityArrivalWindowIndices] using
      (ae_nonpreemptivePriorityStationaryPastWindow_noArrivalTies
        arrivalRate harrivalRate (b - a))
  filter_upwards [hflowNoTies] with omega hnoTies
  intro first hfirst second hsecond heq
  let firstShifted : NonpreemptivePriorityArrivalIndex n := ⟨first.1,
    first.2 - Probability.PoissonProcess.suspensionCrossingIndexPastClosed
      b (omega first.1).1.1⟩
  let secondShifted : NonpreemptivePriorityArrivalIndex n := ⟨second.1,
    second.2 - Probability.PoissonProcess.suspensionCrossingIndexPastClosed
      b (omega second.1).1.1⟩
  have hfirstRestore : stationaryPriorityFlowRestoreIndex omega b firstShifted = first := by
    rcases first with ⟨firstClass, firstIndex⟩
    dsimp [firstShifted, stationaryPriorityFlowRestoreIndex]
    congr 1
    omega
  have hsecondRestore : stationaryPriorityFlowRestoreIndex omega b secondShifted = second := by
    rcases second with ⟨secondClass, secondIndex⟩
    dsimp [secondShifted, stationaryPriorityFlowRestoreIndex]
    congr 1
    omega
  have hfirstIndex : first.2 ∈ stationaryPriorityArrivalWindowIndices omega a b first.1 := by
    simpa [nonpreemptivePriorityArrivalWindowIndices] using hfirst
  have hsecondIndex : second.2 ∈ stationaryPriorityArrivalWindowIndices omega a b second.1 := by
    simpa [nonpreemptivePriorityArrivalWindowIndices] using hsecond
  have hfirstShiftedIndex : firstShifted.2 ∈
      stationaryPriorityArrivalWindowIndices (flow omega) (a - b) 0 firstShifted.1 := by
    have hmembership := (mem_stationaryPriorityArrivalWindowIndices_flow_iff
      omega b a b first.1 firstShifted.2).mpr
    apply (by simpa [flow, firstShifted] using hmembership)
    rcases first with ⟨firstClass, firstIndex⟩
    dsimp [firstShifted]
    convert hfirstIndex using 1
  have hsecondShiftedIndex : secondShifted.2 ∈
      stationaryPriorityArrivalWindowIndices (flow omega) (a - b) 0 secondShifted.1 := by
    have hmembership := (mem_stationaryPriorityArrivalWindowIndices_flow_iff
      omega b a b second.1 secondShifted.2).mpr
    apply (by simpa [flow, secondShifted] using hmembership)
    rcases second with ⟨secondClass, secondIndex⟩
    dsimp [secondShifted]
    convert hsecondIndex using 1
  have hfirstShifted : firstShifted ∈ nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices (flow omega) (a - b) 0) := by
    simpa [nonpreemptivePriorityArrivalWindowIndices] using hfirstShiftedIndex
  have hsecondShifted : secondShifted ∈ nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices (flow omega) (a - b) 0) := by
    simpa [nonpreemptivePriorityArrivalWindowIndices] using hsecondShiftedIndex
  have hfirstTime : Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      firstShifted.1 (flow omega) firstShifted.2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        first.1 omega first.2 - b := by
    calc
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          firstShifted.1 (flow omega) firstShifted.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            (stationaryPriorityFlowRestoreIndex omega b firstShifted).1 omega
            (stationaryPriorityFlowRestoreIndex omega b firstShifted).2 - b :=
              stationaryPriorityArrivalTime_flow_restore omega b firstShifted
      _ = Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            first.1 omega first.2 - b := by rw [hfirstRestore]
  have hsecondTime : Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      secondShifted.1 (flow omega) secondShifted.2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        second.1 omega second.2 - b := by
    calc
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          secondShifted.1 (flow omega) secondShifted.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            (stationaryPriorityFlowRestoreIndex omega b secondShifted).1 omega
            (stationaryPriorityFlowRestoreIndex omega b secondShifted).2 - b :=
              stationaryPriorityArrivalTime_flow_restore omega b secondShifted
      _ = Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 - b := by rw [hsecondRestore]
  have hshiftedEq : Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      firstShifted.1 (flow omega) firstShifted.2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        secondShifted.1 (flow omega) secondShifted.2 := by
    rw [hfirstTime, hsecondTime, heq]
  have hshifted : firstShifted = secondShifted := hnoTies firstShifted hfirstShifted
    secondShifted hsecondShifted hshiftedEq
  calc
    first = stationaryPriorityFlowRestoreIndex omega b firstShifted := hfirstRestore.symm
    _ = stationaryPriorityFlowRestoreIndex omega b secondShifted := by rw [hshifted]
    _ = second := hsecondRestore

/-- The literal multiclass stationary input has no simultaneous labelled
arrivals anywhere almost surely.  This countable exhaustion of the finite
window collision-free theorem is stable under later random time shifts. -/
theorem ae_stationaryPriorityArrival_noArrivalTies_all
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      ∀ first second : NonpreemptivePriorityArrivalIndex n,
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second := by
  have hfinite : ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      ∀ horizon : ℕ,
        ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) (horizon : ℝ)),
          ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) (horizon : ℝ)),
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
                first.1 omega first.2 =
              Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
                second.1 omega second.2 → first = second := by
    rw [MeasureTheory.ae_all_iff]
    intro horizon
    exact ae_stationaryPriorityArrivalWindow_noArrivalTies
      arrivalRate harrivalRate (-(horizon : ℝ)) (horizon : ℝ)
  filter_upwards [hfinite] with omega hfinite
  intro first second heq
  let radius : ℝ := max
    |Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2|
    |Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1 omega second.2|
  let horizon : ℕ := Nat.ceil radius + 1
  have hradius_le : radius ≤ (Nat.ceil radius : ℝ) := Nat.le_ceil _
  have hceil_lt : (Nat.ceil radius : ℝ) < (horizon : ℝ) := by
    dsimp [horizon]
    norm_num
  have hradius_lt : radius < (horizon : ℝ) := lt_of_le_of_lt hradius_le hceil_lt
  have hfirstabs : |Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      first.1 omega first.2| ≤ radius := le_max_left _ _
  have hsecondabs : |Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      second.1 omega second.2| ≤ radius := le_max_right _ _
  have hfirstbounds : -(horizon : ℝ) ≤
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 ∧
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 <
        (horizon : ℝ) := by
    constructor
    · exact (neg_le_neg (le_of_lt (hfirstabs.trans_lt hradius_lt))).trans (neg_abs_le _)
    · exact (le_abs_self _).trans_lt (hfirstabs.trans_lt hradius_lt)
  have hsecondbounds : -(horizon : ℝ) ≤
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1 omega second.2 ∧
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1 omega second.2 <
        (horizon : ℝ) := by
    constructor
    · exact (neg_le_neg (le_of_lt (hsecondabs.trans_lt hradius_lt))).trans (neg_abs_le _)
    · exact (le_abs_self _).trans_lt (hsecondabs.trans_lt hradius_lt)
  have hfirstmem : first ∈ nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) (horizon : ℝ)) := by
    simpa [nonpreemptivePriorityArrivalWindowIndices, stationaryPriorityArrivalWindowIndices,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
      Probability.Queueing.stationaryPoissonWorkArrival] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        (-(horizon : ℝ)) (horizon : ℝ) (omega first.1).1 first.2).mpr hfirstbounds
  have hsecondmem : second ∈ nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) (horizon : ℝ)) := by
    simpa [nonpreemptivePriorityArrivalWindowIndices, stationaryPriorityArrivalWindowIndices,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
      Probability.Queueing.stationaryPoissonWorkArrival] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        (-(horizon : ℝ)) (horizon : ℝ) (omega second.1).1 second.2).mpr hsecondbounds
  exact hfinite horizon first hfirstmem second hsecondmem heq

/-- Global collision-freedom is preserved by the stationary time action after
restoring the shifted integer labels. -/
theorem stationaryPriorityArrival_noArrivalTies_all_flow
    {n : ℕ}
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (offset : ℝ)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          first.1 omega first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
          second.1 omega second.2 → first = second) :
    ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          second.2 → first = second := by
  intro first second heq
  have hrestored : Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      (stationaryPriorityFlowRestoreIndex omega offset first).1 omega
      (stationaryPriorityFlowRestoreIndex omega offset first).2 =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
        (stationaryPriorityFlowRestoreIndex omega offset second).1 omega
        (stationaryPriorityFlowRestoreIndex omega offset second).2 := by
    linarith [stationaryPriorityArrivalTime_flow_restore omega offset first,
      stationaryPriorityArrivalTime_flow_restore omega offset second]
  have heqrestore := hnoTies (stationaryPriorityFlowRestoreIndex omega offset first)
    (stationaryPriorityFlowRestoreIndex omega offset second) hrestored
  exact (Function.Injective.stationaryPriorityFlowRestoreIndex omega offset) heqrestore

/-- Active residual work of a finite stationary replay is invariant almost
surely under a translated time origin. -/
theorem ae_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (offset a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          (a - offset) (b - offset)) =
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a b) := by
  filter_upwards [ae_stationaryPriorityArrivalWindow_noArrivalTies
    arrivalRate harrivalRate a b] with omega hnoTies
  exact activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_flow
    meanService omega offset a b hnoTies

/-- The squared residual-service ledger of a finite stationary replay is
invariant almost surely under a translated time origin. -/
theorem ae_totalNonpreemptivePrioritySquaredResidualWork_stationaryPriorityFiniteWindow_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (offset a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          (a - offset) (b - offset)) =
        totalNonpreemptivePrioritySquaredResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a b) := by
  filter_upwards [ae_stationaryPriorityArrivalWindow_noArrivalTies
    arrivalRate harrivalRate a b] with omega hnoTies
  exact totalNonpreemptivePrioritySquaredResidualWork_stationaryPriorityFiniteWindow_flow
    meanService omega offset a b hnoTies

/-- Waiting work in every priority class at least as urgent as `priority` is
invariant almost surely under a translated time origin. -/
theorem ae_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (offset a b : ℝ) (priority : Fin n) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega)
          (a - offset) (b - offset)) priority =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega a b) priority := by
  filter_upwards [ae_stationaryPriorityArrivalWindow_noArrivalTies
    arrivalRate harrivalRate a b] with omega hnoTies
  exact priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_flow
    meanService omega offset a b priority hnoTies

end

end Queueing
end AppliedModelingLib

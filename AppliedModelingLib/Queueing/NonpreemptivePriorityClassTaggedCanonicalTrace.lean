import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionLedger
import AppliedModelingLib.Queueing.NonpreemptivePriorityFifoPredecessors
import AppliedModelingLib.Queueing.NonpreemptivePriorityTraceProvenance
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionTimes
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedCompletionBound
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedLiveness
import AppliedModelingLib.Queueing.NonpreemptivePriorityFifoCompletionOrder
import AppliedModelingLib.Queueing.NonpreemptivePriorityStrictCompletionOrder
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceBusy

/-!
# Canonical finite traces for selected priority arrivals

The selected-arrival input has one Palm coordinate and stationary coordinates
for every passive class.  This module fixes a deterministic order for its
finite ledgers: physical arrival time first, followed by the class-index
label.  The convention makes adjacent half-open windows concatenate exactly,
including on paths with simultaneous arrivals.
-/

namespace AppliedModelingLib.Queueing

open ProbabilityTheory

noncomputable section

/-- A deterministic key for a labelled selected/Palm arrival.  Physical time
is primary; the fixed stream label resolves simultaneous epochs. -/
def stationaryPriorityClassTaggedArrivalIndexKey
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (q : NonpreemptivePriorityArrivalIndex n) :
    ℝ ×ₗ (Σₗ j : Fin n, ℤ) :=
  toLex (stationaryPriorityClassTaggedArrival i z q.1 q.2,
    (toLex q : Σₗ j : Fin n, ℤ))

/-- The selected-arrival key retains its stream label and is therefore
injective. -/
theorem Function.Injective.stationaryPriorityClassTaggedArrivalIndexKey
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    Function.Injective (stationaryPriorityClassTaggedArrivalIndexKey i z) := by
  intro first second hkey
  have hindex : (toLex first : Σₗ j : Fin n, ℤ) = toLex second := by
    exact congrArg (fun key => (ofLex key).2) hkey
  exact toLex_inj.mp hindex

/-- The total order induced by the selected-arrival time-and-label key. -/
def stationaryPriorityClassTaggedArrivalIndexLE
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (first second : NonpreemptivePriorityArrivalIndex n) : Prop :=
  stationaryPriorityClassTaggedArrivalIndexKey i z first ≤
    stationaryPriorityClassTaggedArrivalIndexKey i z second

/-- The canonical comparison of two fixed selected/Palm stream labels is a
Borel event.  Only their physical arrival coordinates are random. -/
theorem measurableSet_stationaryPriorityClassTaggedArrivalIndexLE
    {n : ℕ} (i : Fin n)
    (first second : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      stationaryPriorityClassTaggedArrivalIndexLE i z first second} := by
  classical
  unfold stationaryPriorityClassTaggedArrivalIndexLE
    stationaryPriorityClassTaggedArrivalIndexKey
  simp only [Prod.Lex.toLex_le_toLex]
  let firstTime : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
    fun z => stationaryPriorityClassTaggedArrival i z first.1 first.2
  let secondTime : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
    fun z => stationaryPriorityClassTaggedArrival i z second.1 second.2
  have hfirst : Measurable firstTime := by
    simpa [firstTime] using
      measurable_stationaryPriorityClassTaggedArrival i first.1 first.2
  have hsecond : Measurable secondTime := by
    simpa [secondTime] using
      measurable_stationaryPriorityClassTaggedArrival i second.1 second.2
  by_cases hlabel : (toLex first : Σₗ j : Fin n, ℤ) ≤ toLex second
  · simpa [firstTime, secondTime, hlabel] using
      (hfirst.lt hsecond).or (hfirst.eq hsecond)
  · simpa [firstTime, secondTime, hlabel] using measurableSet_lt hfirst hsecond

theorem stationaryPriorityClassTaggedArrivalIndexLE_trans
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    {first second third : NonpreemptivePriorityArrivalIndex n}
    (hfirst : stationaryPriorityClassTaggedArrivalIndexLE i z first second)
    (hsecond : stationaryPriorityClassTaggedArrivalIndexLE i z second third) :
    stationaryPriorityClassTaggedArrivalIndexLE i z first third := by
  exact hfirst.trans hsecond

theorem stationaryPriorityClassTaggedArrivalIndexLE_total
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (first second : NonpreemptivePriorityArrivalIndex n) :
    stationaryPriorityClassTaggedArrivalIndexLE i z first second ∨
      stationaryPriorityClassTaggedArrivalIndexLE i z second first := by
  exact le_total _ _

theorem stationaryPriorityClassTaggedArrivalIndexLE_antisymm
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    {first second : NonpreemptivePriorityArrivalIndex n}
    (hfirst : stationaryPriorityClassTaggedArrivalIndexLE i z first second)
    (hsecond : stationaryPriorityClassTaggedArrivalIndexLE i z second first) :
    first = second := by
  apply Function.Injective.stationaryPriorityClassTaggedArrivalIndexKey i z
  exact le_antisymm hfirst hsecond

/-- The canonically ordered selected/Palm index ledger in a finite physical
window. -/
noncomputable def canonicalStationaryPriorityClassTaggedArrivalWindowIndices
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) : List (NonpreemptivePriorityArrivalIndex n) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  exact (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z)

/-- The canonical selected/Palm index ledger is sorted by its deterministic
time-and-label order. -/
theorem pairwise_stationaryPriorityClassTaggedArrivalIndexLE_canonicalWindowIndices
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b).Pairwise
      (stationaryPriorityClassTaggedArrivalIndexLE i z) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  exact Finset.pairwise_sort _ _

/-- Membership in a canonical selected/Palm index ledger is precisely
membership in its literal classwise finite window. -/
theorem mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b ↔
      q.2 ∈ stationaryPriorityClassTaggedArrivalWindowIndices i z a b q.1 := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  simp [canonicalStationaryPriorityClassTaggedArrivalWindowIndices,
    nonpreemptivePriorityArrivalWindowIndices]

/-- Membership of one fixed Palm-stream index in a literal selected arrival
window is Borel, including the finite crossing-index bounds used to construct
the ledger. -/
theorem measurableSet_mem_palmTaggedArrivalIndices
    (a b : ℝ) (k : ℤ) :
    MeasurableSet {g : ℤ → ℝ |
      k ∈ Probability.PoissonProcess.palmTaggedArrivalIndices a b g} := by
  change MeasurableSet {g : ℤ → ℝ |
    k ∈ (Finset.Icc
      (Probability.PoissonProcess.suspensionCrossingIndexPastClosed a (g, 0))
      (Probability.PoissonProcess.suspensionCrossingIndexPastClosed b (g, 0))).filter
        (fun m => a ≤ Probability.PoissonProcess.candidatePalmArrival g m ∧
          Probability.PoissonProcess.candidatePalmArrival g m < b)}
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.setOf_and]
  have hcrossLeft : Measurable (fun g : ℤ → ℝ =>
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed a (g, 0)) := by
    exact (Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed a).comp
      (measurable_id.prodMk measurable_const)
  have hcrossRight : Measurable (fun g : ℤ → ℝ =>
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed b (g, 0)) := by
    exact (Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed b).comp
      (measurable_id.prodMk measurable_const)
  have harrival : Measurable (fun g : ℤ → ℝ =>
      Probability.PoissonProcess.candidatePalmArrival g k) :=
    Probability.PoissonProcess.measurable_candidatePalmArrival k
  exact ((measurableSet_le hcrossLeft measurable_const).inter
    (measurableSet_le measurable_const hcrossRight)).inter
      ((measurableSet_le measurable_const harrival).inter
        (measurableSet_lt harrival measurable_const))

/-- Membership of a fixed labelled index in a finite selected/Palm window is
a Borel event on the full multiclass tagged carrier. -/
theorem measurableSet_mem_stationaryPriorityClassTaggedArrivalWindowIndices
    {n : ℕ} (i : Fin n) (a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      q.2 ∈ stationaryPriorityClassTaggedArrivalWindowIndices i z a b q.1} := by
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
      (measurableSet_mem_palmTaggedArrivalIndices a b qindex).preimage
        (measurable_fst.comp measurable_fst)
  · have harrival : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨qclass, hqi⟩).1 qindex) :=
      (Probability.PoissonProcess.measurable_suspensionBaseArrival qindex).comp
        (measurable_fst.comp ((measurable_pi_apply
          (X := fun _ : {j : Fin n // j ≠ i} => StationaryPoissonWorkPath)
          ⟨qclass, hqi⟩).comp measurable_snd))
    have hmeas : MeasurableSet {z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        qindex ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a b
          (z.2 ⟨qclass, hqi⟩).1} := by
      apply measurableSet_setOf.mpr
      simpa only [Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff] using
        ((measurable_const.le' harrival).and (harrival.lt measurable_const))
    simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hqi] using hmeas

/-- Pairwise canonical ordering of a fixed finite selected/Palm label list is
a Borel condition. -/
theorem measurableSet_stationaryPriorityClassTaggedArrivalIndexList_pairwise
    {n : ℕ} (i : Fin n) (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i z)} := by
  induction labels with
  | nil => simp
  | cons first labels ih =>
      have hhead : MeasurableSet {z :
          MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
          ∀ later ∈ labels, stationaryPriorityClassTaggedArrivalIndexLE i z first later} := by
        rw [show {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
            ∀ later ∈ labels, stationaryPriorityClassTaggedArrivalIndexLE i z first later} =
              ⋂ later ∈ labels.toFinset, {z |
                stationaryPriorityClassTaggedArrivalIndexLE i z first later} by
          ext z
          simp]
        exact labels.toFinset.measurableSet_biInter fun later _ =>
          measurableSet_stationaryPriorityClassTaggedArrivalIndexLE i first later
      simpa only [List.pairwise_cons] using hhead.inter ih

/-- Each fixed finite selected/Palm index set is a Borel fiber of the
literal arrival ledger. -/
theorem measurableSet_stationaryPriorityClassTaggedArrivalWindowLedger_eq
    {n : ℕ} (i : Fin n) (a b : ℝ)
    (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityClassTaggedArrivalWindowIndices i a b q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) ↔ q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {z :
          MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {z |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) ↔ q ∈ labels} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The canonical sorted selected/Palm ledger has a Borel fiber at every
fixed finite label list. -/
theorem measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
    {n : ℕ} (i : Fin n) (a b : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b = labels} := by
  classical
  have hledger :=
    measurableSet_stationaryPriorityClassTaggedArrivalWindowLedger_eq i a b labels.toFinset
  have hpairwise :=
    measurableSet_stationaryPriorityClassTaggedArrivalIndexList_pairwise i labels
  have hnodup : MeasurableSet {z :
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b = labels} =
      ({z | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) = labels.toFinset} ∩
        {z | labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i z)}) ∩
          {z | labels.Nodup} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact pairwise_stationaryPriorityClassTaggedArrivalIndexLE_canonicalWindowIndices
          i z a b
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)).sort
          (stationaryPriorityClassTaggedArrivalIndexLE i z) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z)
        hnodup).mpr hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- Every canonical selected/Palm index in a half-open window occurs before
the right endpoint of that window. -/
theorem canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b) :
    stationaryPriorityClassTaggedArrival i z q.1 q.2 < b := by
  have hindex :=
    (mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff i z a b q).mp hq
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    have hwindow :=
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a b z.1.1 hgood qindex).mp
        (by simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using hwindow.2
  · have hwindow :=
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a b (z.2 ⟨qclass, hqi⟩).1 qindex).mp
        (by simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hqi] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hqi] using hwindow.2

/-- Every canonical selected/Palm index in a half-open window occurs at or
after the left endpoint of that window. -/
theorem canonicalStationaryPriorityClassTaggedArrivalIndex_left_le
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b) :
    a ≤ stationaryPriorityClassTaggedArrival i z q.1 q.2 := by
  have hindex :=
    (mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff i z a b q).mp hq
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    have hwindow :=
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a b z.1.1 hgood qindex).mp
        (by simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using hwindow.1
  · have hwindow :=
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a b (z.2 ⟨qclass, hqi⟩).1 qindex).mp
        (by simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hqi] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hqi] using hwindow.1

/-- All indices in the earlier member of two adjacent canonical selected
ledgers precede all indices in the later member. -/
theorem stationaryPriorityClassTaggedArrivalIndexLE_of_mem_adjacentCanonicalWindows
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a c b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q r : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a c)
    (hr : r ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z c b) :
    stationaryPriorityClassTaggedArrivalIndexLE i z q r := by
  unfold stationaryPriorityClassTaggedArrivalIndexLE
    stationaryPriorityClassTaggedArrivalIndexKey
  apply Prod.Lex.toLex_le_toLex.mpr
  left
  exact lt_of_lt_of_le
    (canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right i z a c hgood q hq)
    (canonicalStationaryPriorityClassTaggedArrivalIndex_left_le i z c b hgood r hr)

/-- Canonically ordered selected/Palm index ledgers concatenate exactly across
adjacent half-open physical windows. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowIndices_append
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a c b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hac : a ≤ c) (hcb : c ≤ b) :
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a c ++
        canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z c b := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let left := canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a c
  let right := canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z c b
  have hdisjoint : List.Disjoint left right := by
    rw [List.disjoint_iff_ne]
    intro q hq r hr heq
    subst r
    exact (not_le_of_gt
      (canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right i z a c hgood q hq))
      (canonicalStationaryPriorityClassTaggedArrivalIndex_left_le i z c b hgood q hr)
  have hnodup : (left ++ right).Nodup := by
    apply List.Nodup.append
    · exact Finset.sort_nodup _ _
    · exact Finset.sort_nodup _ _
    · exact hdisjoint
  have hpairwise : (left ++ right).Pairwise
      (stationaryPriorityClassTaggedArrivalIndexLE i z) := by
    rw [List.pairwise_append]
    refine ⟨pairwise_stationaryPriorityClassTaggedArrivalIndexLE_canonicalWindowIndices
      i z a c, pairwise_stationaryPriorityClassTaggedArrivalIndexLE_canonicalWindowIndices
        i z c b, ?_⟩
    intro q hq r hr
    exact stationaryPriorityClassTaggedArrivalIndexLE_of_mem_adjacentCanonicalWindows
      i z a c b hgood q r hq hr
  have hsorted : ((left ++ right).toFinset).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = left ++ right := by
    exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z) hnodup).mpr
      hpairwise
  have hledger : (left ++ right).toFinset =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) := by
    rw [List.toFinset_append]
    change (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a c).toFinset ∪
        (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z c b).toFinset = _
    rw [show (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a c).toFinset =
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedArrivalWindowIndices i z a c) by
      exact Finset.sort_toFinset _ _]
    rw [show (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z c b).toFinset =
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedArrivalWindowIndices i z c b) by
      exact Finset.sort_toFinset _ _]
    rw [← nonpreemptivePriorityArrivalWindowIndices_union]
    exact congrArg nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedArrivalWindowIndices_append i z a c b hgood hac hcb).symm
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = left ++ right
  rw [← hledger]
  exact hsorted

/-- The canonical selected/Palm job ledger for one finite physical window. -/
def canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b).map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
      serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- The two real coordinates attached to one fixed labelled selected/Palm
arrival. -/
def stationaryPriorityClassTaggedArrivalJobCoordinate
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (q : NonpreemptivePriorityArrivalIndex n) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i →
      NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) :=
  fun z =>
    { identifier := q
      priority := q.1
      arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
      serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- Fixed labelled selected/Palm jobs have measurable arrival and service-work
coordinates. -/
theorem stationaryPriorityClassTaggedArrivalJobCoordinate_coordinatesMeasurable
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (q : NonpreemptivePriorityArrivalIndex n) :
    NonpreemptivePriorityJob.CoordinatesMeasurable
      (stationaryPriorityClassTaggedArrivalJobCoordinate meanService i q) := by
  constructor
  · exact measurable_stationaryPriorityClassTaggedArrival i q.1 q.2
  · exact measurable_stationaryPriorityClassTaggedWorkRequirementAt
      meanService i q.1 q.2

/-- The same fixed labelled arrival in the fixed-event Borel interface.  Its
identifier and priority are static skeleton data, while the two real
coordinates remain the literal selected/Palm coordinates. -/
def stationaryPriorityClassTaggedFixedJobCoordinate
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (q : NonpreemptivePriorityArrivalIndex n) :
    NonpreemptivePriorityFixedJobCoordinate
      (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
      n (NonpreemptivePriorityArrivalIndex n) :=
  { identifier := q
    priority := q.1
    arrivalTime := fun z => stationaryPriorityClassTaggedArrival i z q.1 q.2
    serviceWork := fun z =>
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- Fixed selected/Palm labelled coordinates meet the generic Borel job
requirements. -/
theorem stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (q : NonpreemptivePriorityArrivalIndex n) :
    NonpreemptivePriorityFixedJobCoordinate.CoordinatesMeasurable
      (stationaryPriorityClassTaggedFixedJobCoordinate meanService i q) := by
  exact ⟨measurable_stationaryPriorityClassTaggedArrival i q.1 q.2,
    measurable_stationaryPriorityClassTaggedWorkRequirementAt meanService i q.1 q.2⟩

/-- The Borel response associated with a fixed candidate service order.  The
order is skeleton data; later trace lemmas will identify the matching literal
nonpreemptive-priority completion order on each skeleton fiber. -/
noncomputable def stationaryPriorityClassTaggedFixedServiceOrderResponse
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (startTime : ℝ)
    (order : List (NonpreemptivePriorityArrivalIndex n)) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
  fixedPriorityServiceResponse
    (fun q => decide (q = Sigma.mk i 0)) (fun _ => startTime)
    (order.map (stationaryPriorityClassTaggedFixedJobCoordinate meanService i))

/-- Every fixed selected/Palm candidate service order has a Borel tagged
response. -/
theorem measurable_stationaryPriorityClassTaggedFixedServiceOrderResponse
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (startTime : ℝ)
    (order : List (NonpreemptivePriorityArrivalIndex n)) :
    Measurable (stationaryPriorityClassTaggedFixedServiceOrderResponse
      meanService i startTime order) := by
  apply measurable_fixedPriorityServiceResponse
  · exact measurable_const
  · intro job hjob
    rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
    exact stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
      meanService i q

/-- A canonical selected/Palm job ledger contains exactly the jobs indexed by
its literal classwise finite window. -/
theorem mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b ↔
      ∃ (j : Fin n) (k : ℤ),
        k ∈ stationaryPriorityClassTaggedArrivalWindowIndices i z a b j ∧
          job =
            { identifier := Sigma.mk j k
              priority := j
              arrivalTime := stationaryPriorityClassTaggedArrival i z j k
              serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k } := by
  constructor
  · intro hjob
    rcases List.mem_map.mp hjob with ⟨q, hq, hcoordinate⟩
    refine ⟨q.1, q.2,
      (mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff i z a b q).mp hq,
      ?_⟩
    simpa using hcoordinate.symm
  · rintro ⟨j, k, hindex, rfl⟩
    apply List.mem_map.mpr
    refine ⟨Sigma.mk j k,
      (mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff i z a b
        (Sigma.mk j k)).mpr hindex, rfl⟩

/-- Within a canonical selected/Palm ledger, a job is determined by its
stream identifier.  The time and work fields are both the canonical
coordinates associated with that identifier. -/
theorem eq_stationaryPriorityClassTaggedJob_of_mem_canonicalArrivalWindowJobs_of_identifier_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hmember : job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
    (hidentifier : job.identifier = (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n)) :
    job = stationaryPriorityClassTaggedJob meanService i z := by
  rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z a b job).mp hmember with ⟨j, k, _, hjob⟩
  subst job
  cases hidentifier
  rfl

/-- The Palm-tagged customer is present in every canonical finite arrival
ledger whose physical window contains the tag epoch. -/
theorem stationaryPriorityClassTaggedJob_mem_canonicalArrivalWindow
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ha : a ≤ 0) (hb : 0 < b) :
    stationaryPriorityClassTaggedJob meanService i z ∈
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b := by
  apply (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z a b _).mpr
  refine ⟨i, 0, ?_, ?_⟩
  · simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        a b z.1.1 hgood 0).mpr
        (by simpa [Probability.PoissonProcess.candidatePalmArrival_zero] using ⟨ha, hb⟩)
  · rfl

/-- Under the concrete selected/Palm law, the tagged customer is almost
surely present in each canonical finite window containing its epoch. -/
theorem ae_stationaryPriorityClassTaggedJob_mem_canonicalArrivalWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Fin n) (a b : ℝ) (ha : a ≤ 0) (hb : 0 < b) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityClassTaggedJob meanService i z ∈
        canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hgood
  exact stationaryPriorityClassTaggedJob_mem_canonicalArrivalWindow
    meanService i z a b hgood ha hb

/-- Canonical selected/Palm job ledgers contain no duplicate labelled job. -/
theorem nodup_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b).Nodup := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
  apply List.Nodup.map
  · intro first second hjob
    simpa using congrArg NonpreemptivePriorityJob.identifier hjob
  · exact Finset.sort_nodup _ _

/-- Each canonical selected/Palm job occurs at or after its literal left
endpoint. -/
theorem left_le_arrivalTime_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) :
    a ≤ job.arrivalTime := by
  rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z a b job).mp hjob with ⟨j, k, hindex, rfl⟩
  simpa using canonicalStationaryPriorityClassTaggedArrivalIndex_left_le i z a b hgood
    (Sigma.mk j k)
    ((mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff
      i z a b (Sigma.mk j k)).mpr hindex)

/-- Each canonical selected/Palm job occurs strictly before the literal right
endpoint of its half-open window. -/
theorem arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) :
    job.arrivalTime < b := by
  rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z a b job).mp hjob with ⟨j, k, hindex, rfl⟩
  simpa using canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right i z a b hgood
    (Sigma.mk j k)
    ((mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff
      i z a b (Sigma.mk j k)).mpr hindex)

/-- The canonical selected/Palm job ledger is chronological in physical time. -/
theorem pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b).Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
  rw [List.pairwise_map]
  apply (pairwise_stationaryPriorityClassTaggedArrivalIndexLE_canonicalWindowIndices
    i z a b).imp
  intro first second horder
  unfold stationaryPriorityClassTaggedArrivalIndexLE
    stationaryPriorityClassTaggedArrivalIndexKey at horder
  exact Prod.Lex.monotone_fst _ _ horder

/-- Sorting the selected/Palm ledger by its deterministic total key preserves
its marked-work aggregate. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    nonpreemptivePriorityArrivalTraceServiceWork
      (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) =
      stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z a b := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
  unfold nonpreemptivePriorityArrivalTraceServiceWork
    canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices
    stationaryPriorityClassTaggedArrivalWindowTotalWork
  simp only [List.map_map]
  change (ledger.sort (stationaryPriorityClassTaggedArrivalIndexLE i z) |>.map
      (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)).sum = _
  calc
    (ledger.sort (stationaryPriorityClassTaggedArrivalIndexLE i z) |>.map
        (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)).sum =
        (ledger.toList.map fun q =>
          stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2).sum :=
      ((Finset.sort_perm_toList ledger
        (stationaryPriorityClassTaggedArrivalIndexLE i z)).map _).sum_eq
    _ = ∑ q ∈ ledger,
        stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 := by
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)
          ledger.nodup_toList).symm
    _ = stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z a b := by
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
        stationaryPriorityClassTaggedArrivalWindowTotalWork
      rw [Finset.sum_sigma]

/-- Canonical selected/Palm job ledgers concatenate exactly across adjacent
half-open physical windows. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowJobs_append
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a c b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hac : a ≤ c) (hcb : c ≤ b) :
    canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a c ++
        canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z c b := by
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
  rw [canonicalStationaryPriorityClassTaggedArrivalWindowIndices_append
    i z a c b hgood hac hcb, List.map_append]

/-- Execute the canonically ordered finite selected/Palm arrival ledger,
starting empty at the left endpoint and serving through the right endpoint. -/
def canonicalStationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) b afterArrivals

/-- At phase zero, the selected/Palm and global stationary canonical arrival
orders agree exactly: both use the same physical epochs with the same fixed
label tie-breaker. -/
theorem stationaryPriorityClassTaggedArrivalIndexLE_view_eq_stationary
    {n : ℕ} (i : Fin n) (omega : Fin n → StationaryPoissonWorkPath)
    (first second : NonpreemptivePriorityArrivalIndex n)
    (hphase : (omega i).1.1.2 = 0) :
    stationaryPriorityClassTaggedArrivalIndexLE i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) first second ↔
      stationaryPriorityArrivalIndexLE omega first second := by
  unfold stationaryPriorityClassTaggedArrivalIndexLE
    stationaryPriorityClassTaggedArrivalIndexKey
    stationaryPriorityArrivalIndexLE stationaryPriorityArrivalIndexKey
  simp only [Prod.Lex.toLex_le_toLex]
  simp only [stationaryPriorityClassTaggedArrival]
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_view_eq_multiclassArrival
    i first.1 omega first.2 hphase,
    multiclassStationaryPoissonWorkClassTaggedArrival_view_eq_multiclassArrival
      i second.1 omega second.2 hphase]

/-- The canonical finite index ledger of a selected/Palm view at phase zero
is the canonical ledger of the same global stationary input. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowIndices_view_eq_stationary
    {n : ℕ} (i : Fin n) (omega : Fin n → StationaryPoissonWorkPath)
    (a b : ℝ) (hphase : (omega i).1.1.2 = 0) :
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) a b =
      canonicalStationaryPriorityArrivalWindowIndices omega a b := by
  classical
  have hwindow := stationaryPriorityClassTaggedArrivalWindowIndices_view_eq_stationary
    i omega a b hphase
  have horder : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      stationaryPriorityClassTaggedArrivalIndexLE i
        (multiclassStationaryPoissonWorkClassTaggedView i omega) first second ↔
        stationaryPriorityArrivalIndexLE omega first second := by
    intro first second
    exact stationaryPriorityClassTaggedArrivalIndexLE_view_eq_stationary
      i omega first second hphase
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowIndices
    canonicalStationaryPriorityArrivalWindowIndices
  simp only [hwindow]
  congr 1
  funext first second
  apply propext
  exact horder first second

/-- The complete canonical job ledger of a phase-zero selected/Palm view is
the global stationary canonical job ledger, including both arrival and
service-work coordinates. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowJobs_view_eq_stationary
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (a b : ℝ) (hphase : (omega i).1.1.2 = 0) :
    canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) a b =
      stationaryPriorityArrivalWindowJobs meanService omega a b := by
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    stationaryPriorityArrivalWindowJobs canonicalStationaryPriorityArrivalWindowJobs
  rw [canonicalStationaryPriorityClassTaggedArrivalWindowIndices_view_eq_stationary
    i omega a b hphase]
  apply List.map_congr_left
  intro q _
  dsimp only
  congr 1
  · exact multiclassStationaryPoissonWorkClassTaggedArrival_view_eq_multiclassArrival
      i q.1 omega q.2 hphase
  · unfold stationaryPriorityClassTaggedWorkRequirementAt stationaryPriorityWorkRequirement
    rw [multiclassStationaryPoissonWorkClassTaggedRequirementAt_view_eq_multiclassRequirement]

/-- Executing a canonical selected/Palm finite replay at phase zero is exactly
the global stationary finite replay on that same input window. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowState_view_eq_stationary
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (a b : ℝ) (hphase : (omega i).1.1.2 = 0) :
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) a b =
      stationaryPriorityFiniteWindowState meanService omega a b := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
    stationaryPriorityFiniteWindowState
  dsimp only
  rw [canonicalStationaryPriorityClassTaggedArrivalWindowJobs_view_eq_stationary
    meanService i omega a b hphase]

/-- A Campbell-selected class arrival, recentered into its Palm input, has
the same canonical finite priority replay as the literal global input flowed
to that physical arrival epoch. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_eq_globalFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (a b : ℝ) :
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k) a b =
      stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k)
          (multiclassStationaryPoissonWorkClassAssemble i x)) a b := by
  rw [multiclassStationaryPoissonWorkClassCampbellRecenter_eq_taggedView_flow_at_baseArrival
    arrivalRate harrivalRate i x k]
  apply canonicalStationaryPriorityClassTaggedFiniteWindowState_view_eq_stationary
  exact multiclassStationaryPoissonWorkClassFlow_at_baseArrival_phase_zero
    arrivalRate harrivalRate i x k

/-- At phase zero, the selected/Palm and stationary finite input ledgers
carry exactly the same total service work.  This is the scalar counterpart of
the finite-state covariance and is useful when a backward net-input cutoff is
transported through a Campbell recentering. -/
theorem stationaryPriorityClassTaggedArrivalWindowTotalWork_view_eq_stationary
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (a b : ℝ) (hphase : (omega i).1.1.2 = 0) :
    stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) a b =
      stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
  calc
    stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i
        (multiclassStationaryPoissonWorkClassTaggedView i omega) a b =
        nonpreemptivePriorityArrivalTraceServiceWork
          (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i
            (multiclassStationaryPoissonWorkClassTaggedView i omega) a b) :=
      (nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
        meanService i (multiclassStationaryPoissonWorkClassTaggedView i omega) a b).symm
    _ = nonpreemptivePriorityArrivalTraceServiceWork
          (stationaryPriorityArrivalWindowJobs meanService omega a b) := by
      rw [canonicalStationaryPriorityClassTaggedArrivalWindowJobs_view_eq_stationary
        meanService i omega a b hphase]
    _ = stationaryPriorityArrivalWindowTotalWork meanService omega a b :=
      nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
        meanService omega a b

/-- The past marked-work aggregate of a phase-zero selected/Palm view is the
literal stationary past aggregate of the same input. -/
theorem stationaryPriorityTaggedTotalPastWorkAggregate_view_eq_stationary
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (t : ℝ) (hphase : (omega i).1.1.2 = 0) :
    stationaryPriorityTaggedTotalPastWorkAggregate meanService i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) t =
      stationaryPriorityTotalPastWorkAggregate meanService omega t := by
  rw [← stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero,
    ← stationaryPriorityArrivalWindowTotalWork_neg_to_zero]
  exact stationaryPriorityClassTaggedArrivalWindowTotalWork_view_eq_stationary
    meanService i omega (-t) 0 hphase

/-- Phase-zero selected and stationary inputs have the same backward
net-input path. -/
theorem stationaryPriorityTaggedNetPastInput_view_eq_stationary
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (t : ℝ) (hphase : (omega i).1.1.2 = 0) :
    stationaryPriorityTaggedNetPastInput meanService i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) t =
      stationaryPriorityNetPastInput meanService omega t := by
  unfold stationaryPriorityTaggedNetPastInput stationaryPriorityNetPastInput
  rw [stationaryPriorityTaggedTotalPastWorkAggregate_view_eq_stationary
    meanService i omega t hphase]

/-- A backward net-input cutoff is invariant under viewing a phase-zero
stationary input as a selected/Palm input. -/
theorem stationaryPriorityClassTaggedNetPastCutoff_view_iff_stationary
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (cutoff : ℝ) (hphase : (omega i).1.1.2 = 0) :
    stationaryPriorityClassTaggedNetPastCutoff meanService i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) cutoff ↔
      stationaryPriorityNetPastCutoff meanService omega cutoff := by
  constructor <;> intro h horizon hhorizon
  · simpa only [stationaryPriorityTaggedNetPastInput_view_eq_stationary
      meanService i omega horizon hphase,
      stationaryPriorityTaggedNetPastInput_view_eq_stationary
        meanService i omega cutoff hphase] using h horizon hhorizon
  · simpa only [stationaryPriorityTaggedNetPastInput_view_eq_stationary
      meanService i omega horizon hphase,
      stationaryPriorityTaggedNetPastInput_view_eq_stationary
        meanService i omega cutoff hphase] using h horizon hhorizon

/-- Recentring a labelled Campbell arrival transports a selected/Palm
net-input cutoff exactly to the stationary input flowed to that arrival. -/
theorem stationaryPriorityClassTaggedNetPastCutoff_campbellRecenter_iff_globalFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (cutoff : ℝ) :
    stationaryPriorityClassTaggedNetPastCutoff meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k) cutoff ↔
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k)
          (multiclassStationaryPoissonWorkClassAssemble i x)) cutoff := by
  rw [multiclassStationaryPoissonWorkClassCampbellRecenter_eq_taggedView_flow_at_baseArrival
    arrivalRate harrivalRate i x k]
  exact stationaryPriorityClassTaggedNetPastCutoff_view_iff_stationary
    meanService i
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
      (Probability.Queueing.timedEmbeddedArrival x.1 k)
      (multiclassStationaryPoissonWorkClassAssemble i x)) cutoff
    (multiclassStationaryPoissonWorkClassFlow_at_baseArrival_phase_zero
      arrivalRate harrivalRate i x k)

/-- The first physical completion epoch recorded for a fixed labelled job in
a finite queue state.  Completion records are prepended as service occurs, so
the ledger is read in chronological order to keep this observation unchanged
by later, unrelated continuations. -/
noncomputable def nonpreemptivePriorityRecordedCompletionTime
    {n : ℕ}
    (state : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) : Option ℝ :=
  (state.completed.reverse.find? fun entry => decide (entry.1.identifier = identifier)).map Prod.snd

/-- A completion observation depends only on the completion ledger. -/
theorem nonpreemptivePriorityRecordedCompletionTime_congr_completed
    {n : ℕ}
    (first second : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n)
    (hcompleted : first.completed = second.completed) :
    nonpreemptivePriorityRecordedCompletionTime first identifier =
      nonpreemptivePriorityRecordedCompletionTime second identifier := by
  unfold nonpreemptivePriorityRecordedCompletionTime
  rw [hcompleted]

/-- A successful first-completion lookup identifies an actual entry in the
finite completion ledger. -/
private theorem list_find?_eq_some_mem_and_predicate
    {α : Type*} (predicate : α → Bool) (entries : List α) (entry : α)
    (hfind : entries.find? predicate = some entry) :
    entry ∈ entries ∧ predicate entry = true := by
  induction entries with
  | nil => simp at hfind
  | cons head tail ih =>
      cases hp : predicate head with
      | false =>
          have htail : tail.find? predicate = some entry := by
            simpa [List.find?_cons, hp] using hfind
          rcases ih htail with ⟨hmem, hpredicate⟩
          exact ⟨List.mem_cons_of_mem _ hmem, hpredicate⟩
      | true =>
          have hentry : entry = head := by
            have hhead : head = entry := by
              simpa [List.find?_cons, hp] using hfind
            exact hhead.symm
          subst entry
          exact ⟨by simp, hp⟩

/-- A finite completion observation with value `completedAt` is supported by
the physical ledger at that timestamp. -/
theorem exists_completed_of_nonpreemptivePriorityRecordedCompletionTime_eq_some
    {n : ℕ}
    (state : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) (completedAt : ℝ)
    (hresponse : nonpreemptivePriorityRecordedCompletionTime state identifier = some completedAt) :
    ∃ job, job.identifier = identifier ∧ (job, completedAt) ∈ state.completed := by
  unfold nonpreemptivePriorityRecordedCompletionTime at hresponse
  rcases Option.map_eq_some_iff.mp hresponse with ⟨entry, hfind, htime⟩
  rcases list_find?_eq_some_mem_and_predicate
    (fun entry => decide (entry.1.identifier = identifier)) state.completed.reverse entry hfind with
      ⟨hmember, hidentifier⟩
  rcases entry with ⟨job, completedAt'⟩
  subst completedAt
  refine ⟨job, of_decide_eq_true hidentifier, ?_⟩
  exact List.mem_reverse.mp hmember

/-- A successful first-completion observation occurs no later than every
other matching record in a chronological finite completion ledger. -/
theorem nonpreemptivePriorityRecordedCompletionTime_le_of_eq_some
    {n : ℕ}
    (state : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) (completedAt : ℝ)
    (hchronological : nonpreemptivePriorityCompletionLedgerChronological state)
    (hresponse : nonpreemptivePriorityRecordedCompletionTime state identifier = some completedAt)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (otherCompletedAt : ℝ)
    (hidentifier : job.identifier = identifier)
    (hcompleted : (job, otherCompletedAt) ∈ state.completed) :
    completedAt ≤ otherCompletedAt := by
  unfold nonpreemptivePriorityRecordedCompletionTime at hresponse
  rcases Option.map_eq_some_iff.mp hresponse with ⟨entry, hfind, htime⟩
  rcases entry with ⟨foundJob, foundAt⟩
  subst completedAt
  have hsorted : state.completed.reverse.Pairwise
      (fun first second :
        NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) × ℝ =>
        first.2 ≤ second.2) := by
    exact List.Pairwise.reverse hchronological
  exact list_find?_time_le_of_pairwise Prod.snd
    (fun entry => decide (entry.1.identifier = identifier))
    state.completed.reverse (foundJob, foundAt) (job, otherCompletedAt)
    hsorted hfind (List.mem_reverse.mpr hcompleted) (by simp [hidentifier])

/-- If every record in a finite replay is strictly after an observational
origin, then so is every successful first-completion observation. -/
theorem nonpreemptivePriorityRecordedCompletionTime_pos_of_eq_some
    {n : ℕ}
    (origin : ℝ)
    (state : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) (completedAt : ℝ)
    (htimes : nonpreemptivePriorityCompletionTimesAfter origin state)
    (hresponse : nonpreemptivePriorityRecordedCompletionTime state identifier = some completedAt) :
    origin < completedAt := by
  rcases exists_completed_of_nonpreemptivePriorityRecordedCompletionTime_eq_some
    state identifier completedAt hresponse with ⟨job, _, hcompleted⟩
  exact htimes.2 job completedAt hcompleted

private theorem list_find?_append_eq_some_of_left
    {α : Type*} (predicate : α → Bool)
    (front tail : List α) (entry : α)
    (hfind : front.find? predicate = some entry) :
    (front ++ tail).find? predicate = some entry := by
  rw [List.find?_append, hfind]
  rfl

/-- Once a first completion observation has been recorded, prepending later
completion records cannot alter that first physical epoch. -/
theorem nonpreemptivePriorityRecordedCompletionTime_eq_of_ledgerExtension
    {n : ℕ}
    (earlier later : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) (completedAt : ℝ)
    (hextends : nonpreemptivePriorityCompletionLedgerExtension earlier later)
    (hearlier : nonpreemptivePriorityRecordedCompletionTime earlier identifier = some completedAt) :
    nonpreemptivePriorityRecordedCompletionTime later identifier = some completedAt := by
  rcases hextends with ⟨newlyCompleted, hledger⟩
  unfold nonpreemptivePriorityRecordedCompletionTime at hearlier ⊢
  rcases Option.map_eq_some_iff.mp hearlier with ⟨entry, hfind, htime⟩
  rw [hledger, List.reverse_append]
  rw [list_find?_append_eq_some_of_left _ _ _ _ hfind]
  simpa [htime]

/-- The first recorded completion time persists through every finite sequence
of later admissions and bounded service evolution. -/
theorem nonpreemptivePriorityRecordedCompletionTime_eq_of_run_advance
    {n : ℕ}
    (initial : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (jobs : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) )
    (fuel : ℕ) (terminal : ℝ)
    (identifier : NonpreemptivePriorityArrivalIndex n) (completedAt : ℝ)
    (hinitial : nonpreemptivePriorityRecordedCompletionTime initial identifier = some completedAt) :
    nonpreemptivePriorityRecordedCompletionTime
      (advanceNonpreemptivePriorityWorkState fuel terminal
        (runNonpreemptivePriorityArrivalTrace initial jobs)) identifier = some completedAt := by
  apply nonpreemptivePriorityRecordedCompletionTime_eq_of_ledgerExtension
    initial
      (advanceNonpreemptivePriorityWorkState fuel terminal
        (runNonpreemptivePriorityArrivalTrace initial jobs)) identifier completedAt
  · exact nonpreemptivePriorityCompletionLedgerExtension_trans initial
      (runNonpreemptivePriorityArrivalTrace initial jobs)
      (advanceNonpreemptivePriorityWorkState fuel terminal
        (runNonpreemptivePriorityArrivalTrace initial jobs))
      (nonpreemptivePriorityCompletionLedgerExtension_run initial jobs)
      (nonpreemptivePriorityCompletionLedgerExtension_advance fuel terminal
        (runNonpreemptivePriorityArrivalTrace initial jobs))
  · exact hinitial

/-- The finite-horizon response of the selected customer.  It is `none` when
the tag has not completed by the horizon; increasing the horizon supplies the
literal finite approximants for the eventual Palm response. -/
noncomputable def canonicalStationaryPriorityClassTaggedFiniteResponseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) : Option ℝ :=
  nonpreemptivePriorityRecordedCompletionTime
    (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b)
    (Sigma.mk i 0)

/-- The classwise finite ledger of arrivals strictly after the selected Palm
epoch and no later than a future horizon.  Its right-closed convention agrees
with the future-work aggregate used in the selected-input drift theorem, and
therefore excludes the selected customer itself. -/
def stationaryPriorityClassTaggedFutureArrivalIndices
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : Fin n → Finset ℤ :=
  fun j => if hji : j = i then
    Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed 0 t z.1.1
  else
    Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 t
      (z.2 ⟨j, hji⟩).1

/-- The portion of the right-closed future ledger that occurs strictly before
its queried horizon. -/
noncomputable def stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : Fin n → Finset ℤ :=
  fun j => (stationaryPriorityClassTaggedFutureArrivalIndices i z t j).filter
    (fun k => stationaryPriorityClassTaggedArrival i z j k < t)

/-- The complementary portion of the right-closed future ledger at its
queried horizon.  On a good arrival path its indices occur exactly at that
horizon. -/
noncomputable def stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : Fin n → Finset ℤ :=
  fun j => (stationaryPriorityClassTaggedFutureArrivalIndices i z t j).filter
    (fun k => ¬ stationaryPriorityClassTaggedArrival i z j k < t)

/-- Splitting a right-closed future ledger into its strict and boundary
portions is an exact finite-index partition. -/
theorem stationaryPriorityClassTaggedFutureArrivalIndices_eq_before_union_atHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    stationaryPriorityClassTaggedFutureArrivalIndices i z t = fun j =>
      stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t j ∪
        stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t j := by
  funext j
  ext k
  simp only [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
    stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hmember
    by_cases hlt : stationaryPriorityClassTaggedArrival i z j k < t
    · exact Or.inl ⟨hmember, hlt⟩
    · exact Or.inr ⟨hmember, hlt⟩
  · rintro (⟨hmember, _⟩ | ⟨hmember, _⟩) <;> exact hmember

/-- Membership of a fixed selected/Palm index in a right-closed future ledger
is Borel on the full tagged sample carrier. -/
theorem measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndices
    {n : ℕ} (i : Fin n) (t : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndices i z t q.1} := by
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using
      (Probability.PoissonProcess.measurableSet_mem_palmTaggedArrivalIndicesRightClosed
        0 t qindex).preimage (measurable_fst.comp measurable_fst)
  · have hpath : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        (z.2 ⟨qclass, hqi⟩).1) :=
      measurable_fst.comp ((measurable_pi_apply
        (X := fun _ : {j : Fin n // j ≠ i} => StationaryPoissonWorkPath)
        ⟨qclass, hqi⟩).comp measurable_snd)
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hqi] using
      (Probability.PoissonProcess.measurableSet_mem_suspensionBaseArrivalIndicesRightClosed
        0 t qindex).preimage hpath

/-- Membership in a finite right-closed future ledger remains Borel when its
horizon is supplied by a Borel coordinate of the selected-arrival carrier.
This is the random-time form needed when a finite replay is queried at a
fixed labelled arrival epoch. -/
theorem measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndices_of_measurable
    {n : ℕ} (i : Fin n)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndices i z (target z) q.1} := by
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    have hbase : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => (z.1.1, (0 : ℝ))) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_const
    have hcrossLeft : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed 0 (z.1.1, 0)) :=
      (Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed 0).comp hbase
    have hcrossRight : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed (target z) (z.1.1, 0)) :=
      Probability.PoissonProcess.measurable_uncurry_suspensionCrossingIndexPastClosed.comp
        (htarget.prodMk hbase)
    have harrival : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.candidatePalmArrival z.1.1 qindex) :=
      (Probability.PoissonProcess.measurable_candidatePalmArrival qindex).comp
        (measurable_fst.comp measurable_fst)
    have hmember : MeasurableSet {z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        qindex ∈ Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed
          0 (target z) z.1.1} := by
      simp only [Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed,
        Finset.mem_filter, Finset.mem_Icc, Set.setOf_and]
      exact ((measurableSet_le hcrossLeft measurable_const).inter
        (measurableSet_le measurable_const hcrossRight)).inter
          ((measurableSet_lt measurable_const harrival).inter
            (measurableSet_le harrival htarget))
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using hmember
  · have hsusp : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        (z.2 ⟨qclass, hqi⟩).1) :=
      measurable_fst.comp ((measurable_pi_apply
        (X := fun _ : {j : Fin n // j ≠ i} => StationaryPoissonWorkPath)
        ⟨qclass, hqi⟩).comp measurable_snd)
    have hraw : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        ((z.2 ⟨qclass, hqi⟩).1).1) :=
      measurable_subtype_coe.comp hsusp
    have hcrossLeft : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed 0
          ((z.2 ⟨qclass, hqi⟩).1).1) :=
      (Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed 0).comp hraw
    have hcrossRight : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.suspensionCrossingIndexPastClosed (target z)
          ((z.2 ⟨qclass, hqi⟩).1).1) :=
      Probability.PoissonProcess.measurable_uncurry_suspensionCrossingIndexPastClosed.comp
        (htarget.prodMk hraw)
    have harrival : Measurable (fun z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨qclass, hqi⟩).1 qindex) :=
      (Probability.PoissonProcess.measurable_suspensionBaseArrival qindex).comp hsusp
    have hmember : MeasurableSet {z :
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        qindex ∈ Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
          0 (target z) (z.2 ⟨qclass, hqi⟩).1} := by
      simp only [Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed,
        Finset.mem_filter, Finset.mem_Icc, Set.setOf_and]
      exact ((measurableSet_le hcrossLeft measurable_const).inter
        (measurableSet_le measurable_const hcrossRight)).inter
          ((measurableSet_lt measurable_const harrival).inter
            (measurableSet_le harrival htarget))
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hqi] using hmember

/-- On a good selected-arrival path, every index in the boundary portion of
the future ledger has arrival time exactly equal to the queried horizon. -/
theorem stationaryPriorityClassTaggedArrival_eq_horizon_of_mem_futureAtHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (j : Fin n) (k : ℤ)
    (hmember : k ∈ stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t j) :
    stationaryPriorityClassTaggedArrival i z j k = t := by
  have hfilter := Finset.mem_filter.mp hmember
  have hfull : k ∈ stationaryPriorityClassTaggedFutureArrivalIndices i z t j := by
    simpa [stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon] using hfilter.1
  have hnot : ¬ stationaryPriorityClassTaggedArrival i z j k < t := by
    simpa [stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon] using hfilter.2
  have hle : stationaryPriorityClassTaggedArrival i z j k ≤ t := by
    by_cases hji : j = i
    · subst j
      have hwindow := (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
        0 t z.1.1 hgood k).mp
          (by simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using hfull)
      simpa [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival] using hwindow.2
    · have hwindow := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
        0 t (z.2 ⟨j, hji⟩).1 k).mp
          (by simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hji] using hfull)
      simpa [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hwindow.2
  exact le_antisymm hle (le_of_not_gt hnot)

/-- The classwise arrivals in the later right-closed portion `(t, u]` of a
post-tag ledger.  It is kept separate from the earlier ledger so the endpoint
at `t` remains assigned unambiguously to the preceding finite execution. -/
def stationaryPriorityClassTaggedFutureArrivalIndicesAfter
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) : Fin n → Finset ℤ :=
  fun j => if hji : j = i then
    Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed t u z.1.1
  else
    Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed t u
      (z.2 ⟨j, hji⟩).1

/-- A right-closed post-tag ledger splits exactly at every nonnegative
intermediate horizon. -/
theorem stationaryPriorityClassTaggedFutureArrivalIndices_eq_union_after
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ht : 0 ≤ t) (htu : t ≤ u) :
    stationaryPriorityClassTaggedFutureArrivalIndices i z u =
      fun j => stationaryPriorityClassTaggedFutureArrivalIndices i z t j ∪
        stationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u j := by
  funext j
  by_cases hji : j = i
  · subst j
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices,
      stationaryPriorityClassTaggedFutureArrivalIndicesAfter] using
      (Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed_union
        0 t u z.1.1 hgood ht htu)
  · simpa [stationaryPriorityClassTaggedFutureArrivalIndices,
      stationaryPriorityClassTaggedFutureArrivalIndicesAfter, hji] using
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_union
        0 t u (z.2 ⟨j, hji⟩).1 ht htu)

/-- A deterministic chronological order for the selected-arrival future
ledger.  The physical epoch is primary and the immutable stream label resolves
any simultaneous arrivals. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalIndices
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : List (NonpreemptivePriorityArrivalIndex n) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  exact (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndices i z t)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z)

/-- The chronologically ordered future labels strictly before a horizon. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : List (NonpreemptivePriorityArrivalIndex n) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  exact (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z)

/-- Membership in the canonical strict-future ledger is exactly membership in
the physical open interval from the Palm tag to the queried horizon. -/
theorem mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q : NonpreemptivePriorityArrivalIndex n) :
    q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t ↔
      0 < stationaryPriorityClassTaggedArrival i z q.1 q.2 ∧
        stationaryPriorityClassTaggedArrival i z q.1 q.2 < t := by
  classical
  rw [show q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z t ↔ q ∈ nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t) by
    simp [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon]]
  rcases q with ⟨j, k⟩
  simp only [nonpreemptivePriorityArrivalWindowIndices, Finset.mem_sigma,
    Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst j
    rw [show k ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t i ↔
        k ∈ Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed 0 t z.1.1 ∧
          stationaryPriorityClassTaggedArrival i z i k < t by
      simp only [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
        stationaryPriorityClassTaggedFutureArrivalIndices, dif_pos,
        Finset.mem_filter]]
    rw [Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
      0 t z.1.1 hgood k]
    constructor
    · rintro ⟨⟨hleft, _⟩, hright⟩
      exact ⟨by simpa [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival] using hleft,
        by simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival] using hright⟩
    · rintro ⟨hleft, hright⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival] using hleft
      · exact (by simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival] using hright.le)
      · simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival] using hright
  · simp only [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      stationaryPriorityClassTaggedFutureArrivalIndices, Finset.mem_filter]
    rw [dif_neg hji]
    rw [Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff]
    constructor
    · rintro ⟨⟨hleft, _⟩, hright⟩
      exact ⟨by simpa [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hleft,
        by simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hright⟩
    · rintro ⟨hleft, hright⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hleft
      · exact (by simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hright.le)
      · simpa [stationaryPriorityClassTaggedArrival,
          multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hright

/-- If the selected Palm tag is the only arrival at its epoch, the finite
ledger on `[0,t)` is exactly the tag together with the strict-future ledger.
This isolates the only endpoint convention needed to continue a tagged
finite replay through a physical horizon. -/
theorem nonpreemptivePriorityArrivalWindowIndices_stationaryPriorityClassTagged_zero_to_eq_insert_future
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hzero : ∀ q : NonpreemptivePriorityArrivalIndex n,
      stationaryPriorityClassTaggedArrival i z q.1 q.2 = 0 → q = Sigma.mk i 0) :
    nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedArrivalWindowIndices i z 0 t) =
      insert (Sigma.mk i 0)
        (nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t)) := by
  ext ⟨j, k⟩
  simp only [Finset.mem_insert, nonpreemptivePriorityArrivalWindowIndices,
    Finset.mem_sigma, Finset.mem_univ, true_and]
  constructor
  · intro hmember
    by_cases htag : (Sigma.mk j k : NonpreemptivePriorityArrivalIndex n) = Sigma.mk i 0
    · exact Or.inl htag
    · right
      have hwindow : 0 ≤ stationaryPriorityClassTaggedArrival i z j k ∧
          stationaryPriorityClassTaggedArrival i z j k < t := by
        by_cases hji : j = i
        · subst j
          have hbounds := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
            0 t z.1.1 hgood k).mp (by
              simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hmember)
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using hbounds
        · have hbounds := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
            0 t (z.2 ⟨j, hji⟩).1 k).mp (by
              simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hmember)
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hbounds
      have hfuture : (Sigma.mk j k : NonpreemptivePriorityArrivalIndex n) ∈
          canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t := by
        apply (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
          i z t hgood (Sigma.mk j k)).mpr
        refine ⟨lt_of_le_of_ne hwindow.1 ?_, hwindow.2⟩
        intro htime
        apply htag
        exact hzero (Sigma.mk j k) htime.symm
      simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
        nonpreemptivePriorityArrivalWindowIndices] using hfuture
  · rintro (htag | hfuture)
    · cases htag
      have hbounds : 0 ≤ Probability.PoissonProcess.candidatePalmArrival z.1.1 0 ∧
          Probability.PoissonProcess.candidatePalmArrival z.1.1 0 < t := by
        rw [Probability.PoissonProcess.candidatePalmArrival_zero]
        exact ⟨le_rfl, ht⟩
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
        (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
          0 t z.1.1 hgood 0).mpr hbounds
    · have hfuture' : (Sigma.mk j k : NonpreemptivePriorityArrivalIndex n) ∈
          canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t := by
        simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
          nonpreemptivePriorityArrivalWindowIndices] using hfuture
      have htime := (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
        i z t hgood (Sigma.mk j k)).mp hfuture'
      by_cases hji : j = i
      · subst j
        have htime' : 0 < stationaryPriorityClassTaggedArrival i z i k ∧
            stationaryPriorityClassTaggedArrival i z i k < t := by
          simpa using htime
        have hpalm : k ∈ Probability.PoissonProcess.palmTaggedArrivalIndices 0 t z.1.1 :=
          (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
            0 t z.1.1 hgood k).mpr
              ⟨by simpa [stationaryPriorityClassTaggedArrival,
                multiclassStationaryPoissonWorkClassTaggedArrival] using htime'.1.le,
              by simpa [stationaryPriorityClassTaggedArrival,
                multiclassStationaryPoissonWorkClassTaggedArrival] using htime'.2⟩
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hpalm
      · have htime' : 0 < stationaryPriorityClassTaggedArrival i z j k ∧
            stationaryPriorityClassTaggedArrival i z j k < t := by
          simpa using htime
        have hpassive : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices 0 t
            (z.2 ⟨j, hji⟩).1 :=
          (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
            0 t (z.2 ⟨j, hji⟩).1 k).mpr
              ⟨by simpa [stationaryPriorityClassTaggedArrival,
                multiclassStationaryPoissonWorkClassTaggedArrival, hji] using htime'.1.le,
              by simpa [stationaryPriorityClassTaggedArrival,
                multiclassStationaryPoissonWorkClassTaggedArrival, hji] using htime'.2⟩
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hpassive

/-- Under the same isolated-tag hypothesis, canonical ordering puts the Palm
tag first and then lists exactly the arrivals strictly between zero and the
queried horizon. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowIndices_zero_to_eq_tag_cons_future
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hzero : ∀ q : NonpreemptivePriorityArrivalIndex n,
      stationaryPriorityClassTaggedArrival i z q.1 q.2 = 0 → q = Sigma.mk i 0) :
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z 0 t =
      Sigma.mk i 0 ::
        canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let future := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t
  have hnotmem : (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n) ∉ future := by
    intro htag
    have hpositive := (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
      i z t hgood (Sigma.mk i 0)).mp (by simpa [future] using htag)
    rw [stationaryPriorityClassTaggedArrival_tag_zero] at hpositive
    exact lt_irrefl _ hpositive.1
  have hnodup : (Sigma.mk i 0 :: future).Nodup := by
    exact List.nodup_cons.mpr ⟨hnotmem, Finset.sort_nodup _ _⟩
  have hpairwise : (Sigma.mk i 0 :: future).Pairwise
      (stationaryPriorityClassTaggedArrivalIndexLE i z) := by
    rw [List.pairwise_cons]
    refine ⟨?_, Finset.pairwise_sort _ _⟩
    intro q hq
    unfold stationaryPriorityClassTaggedArrivalIndexLE
      stationaryPriorityClassTaggedArrivalIndexKey
    apply Prod.Lex.toLex_le_toLex.mpr
    left
    rw [stationaryPriorityClassTaggedArrival_tag_zero]
    exact (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
      i z t hgood q).mp (by simpa [future] using hq) |>.1
  have hledger : (Sigma.mk i 0 :: future).toFinset =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices i z 0 t) := by
    rw [List.toFinset_cons]
    change insert (Sigma.mk i 0) (future.toFinset) = _
    rw [show future.toFinset = nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t) by
      exact Finset.sort_toFinset _ _]
    exact (nonpreemptivePriorityArrivalWindowIndices_stationaryPriorityClassTagged_zero_to_eq_insert_future
      i z t ht hgood hzero).symm
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i z 0 t)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = Sigma.mk i 0 :: future
  rw [← hledger]
  exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z)
    hnodup).mpr hpairwise

/-- The chronologically ordered future labels at a horizon. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : List (NonpreemptivePriorityArrivalIndex n) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  exact (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z)

/-- Each fixed finite selected/Palm future-index set is a Borel fiber of the
literal right-closed future ledger. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureArrivalLedger_eq
    {n : ℕ} (i : Fin n) (t : ℝ)
    (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z t) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z t)} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndices i t q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z t) ↔ q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {z :
          MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityClassTaggedFutureArrivalIndices i z t)} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z t) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {z |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z t) ↔ q ∈ labels} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The canonical sorted selected/Palm future ledger has a Borel fiber at
every fixed finite label list. -/
theorem measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_eq
    {n : ℕ} (i : Fin n) (t : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t = labels} := by
  classical
  have hledger :=
    measurableSet_stationaryPriorityClassTaggedFutureArrivalLedger_eq i t labels.toFinset
  have hpairwise :=
    measurableSet_stationaryPriorityClassTaggedArrivalIndexList_pairwise i labels
  have hnodup : MeasurableSet {z :
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t = labels} =
      ({z | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z t) = labels.toFinset} ∩
        {z | labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i z)}) ∩
          {z | labels.Nodup} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityClassTaggedFutureArrivalIndices i z t) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact Finset.pairwise_sort _ _
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z t)).sort
          (stationaryPriorityClassTaggedArrivalIndexLE i z) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z)
        hnodup).mpr hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- A fixed finite right-closed ledger is a Borel fiber even when the
horizon is a Borel coordinate of the selected-arrival carrier. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureArrivalLedger_eq_of_measurable
    {n : ℕ} (i : Fin n)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z)) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z))} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndices_of_measurable
        i target htarget q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z)) ↔ q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {z :
          MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z))} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z)) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {z |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z)) ↔ q ∈ labels} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The chronologically sorted right-closed ledger has a Borel fiber at a
Borel random horizon. -/
theorem measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_eq_of_measurable
    {n : ℕ} (i : Fin n)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z (target z) = labels} := by
  classical
  have hledger :=
    measurableSet_stationaryPriorityClassTaggedFutureArrivalLedger_eq_of_measurable
      i target htarget labels.toFinset
  have hpairwise :=
    measurableSet_stationaryPriorityClassTaggedArrivalIndexList_pairwise i labels
  have hnodup : MeasurableSet {z :
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z (target z) = labels} =
      ({z | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z)) = labels.toFinset} ∩
        {z | labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i z)}) ∩
          {z | labels.Nodup} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z (target z)).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z)) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact Finset.pairwise_sort _ _
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z (target z))).sort
          (stationaryPriorityClassTaggedArrivalIndexLE i z) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z)
        hnodup).mpr hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- Membership in the strict part of a finite future ledger is Borel at a
Borel random horizon. -/
theorem measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_of_measurable
    {n : ℕ} (i : Fin n)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z (target z) q.1} := by
  have hfull :=
    measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndices_of_measurable
      i target htarget q
  have harrival : Measurable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      stationaryPriorityClassTaggedArrival i z q.1 q.2) :=
    measurable_stationaryPriorityClassTaggedArrival i q.1 q.2
  simpa only [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
    Finset.mem_filter, Set.setOf_and] using
      hfull.inter (measurableSet_lt harrival htarget)

/-- A fixed strict finite future ledger is a Borel fiber at a Borel random
horizon. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureArrivalLedgerBeforeHorizon_eq_of_measurable
    {n : ℕ} (i : Fin n)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
          i z (target z)) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i z (target z))} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_of_measurable
        i target htarget q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i z (target z)) ↔ q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {z :
          MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
              i z (target z))} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
          i z (target z)) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {z |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i z (target z)) ↔ q ∈ labels} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The chronologically sorted strict ledger has a Borel fiber at a Borel
random horizon. -/
theorem measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_measurable
    {n : ℕ} (i : Fin n)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z (target z) = labels} := by
  classical
  have hledger :=
    measurableSet_stationaryPriorityClassTaggedFutureArrivalLedgerBeforeHorizon_eq_of_measurable
      i target htarget labels.toFinset
  have hpairwise :=
    measurableSet_stationaryPriorityClassTaggedArrivalIndexList_pairwise i labels
  have hnodup : MeasurableSet {z :
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z (target z) = labels} =
      ({z | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i z (target z)) = labels.toFinset} ∩
        {z | labels.Pairwise (stationaryPriorityClassTaggedArrivalIndexLE i z)}) ∩
          {z | labels.Nodup} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
            i z (target z)).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
                i z (target z)) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact Finset.pairwise_sort _ _
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
      letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
      letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
        ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
          i z (target z))).sort
          (stationaryPriorityClassTaggedArrivalIndexLE i z) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z)
        hnodup).mpr hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- A fixed pair of past and right-closed future ledgers for one finite
two-sided tagged replay.  These fibers isolate the remaining deterministic
completion-time measurability problem from the random ledger enumeration. -/
def stationaryPriorityClassTaggedFiniteReplayLedgerFiber
    {n : ℕ} (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
  {z | canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z (-older) 0 =
      pastLabels ∧
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t = futureLabels}

/-- Every fixed finite two-sided replay ledger fiber is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiber
    {n : ℕ} (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet (stationaryPriorityClassTaggedFiniteReplayLedgerFiber
      i older t pastLabels futureLabels) := by
  exact (measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
    i (-older) 0 pastLabels).inter
      (measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_eq
        i t futureLabels)

/-- The countable fixed-ledger fibers cover every selected/Palm sample. -/
theorem iUnion_stationaryPriorityClassTaggedFiniteReplayLedgerFiber
    {n : ℕ} (i : Fin n) (older t : ℝ) :
    ⋃ pastLabels : List (NonpreemptivePriorityArrivalIndex n),
      ⋃ futureLabels : List (NonpreemptivePriorityArrivalIndex n),
        stationaryPriorityClassTaggedFiniteReplayLedgerFiber i older t pastLabels futureLabels =
          Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z (-older) 0,
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t, rfl, rfl⟩

/-- A finite two-sided replay ledger with a Borel sample-dependent right
horizon.  The historical window remains fixed; only the queried future
endpoint varies with the carrier. -/
def stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
    {n : ℕ} (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
  {z | canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z (-older) 0 =
      pastLabels ∧
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z (target z) = futureLabels}

/-- Every fixed ledger fiber at a Borel random right horizon is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
    {n : ℕ} (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet (stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
      i older target pastLabels futureLabels) := by
  exact (measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
    i (-older) 0 pastLabels).inter
      (measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_eq_of_measurable
        i target htarget futureLabels)

/-- The countable fixed-ledger fibers cover every selected/Palm sample at a
Borel random right horizon. -/
theorem iUnion_stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
    {n : ℕ} (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ) :
    ⋃ pastLabels : List (NonpreemptivePriorityArrivalIndex n),
      ⋃ futureLabels : List (NonpreemptivePriorityArrivalIndex n),
        stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
          i older target pastLabels futureLabels = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z (-older) 0,
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z (target z), rfl, rfl⟩

/-- A finite two-sided replay ledger whose future portion contains only
arrivals strictly before a Borel sample-dependent right horizon. -/
def stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
    {n : ℕ} (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
  {z | canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z (-older) 0 =
      pastLabels ∧
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z (target z) = futureLabels}

/-- Every strict-ledger replay fiber at a Borel random right horizon is
Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
    {n : ℕ} (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet (stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
      i older target pastLabels futureLabels) := by
  exact (measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
    i (-older) 0 pastLabels).inter
      (measurableSet_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_measurable
        i target htarget futureLabels)

/-- The strict replay ledger fibers cover every selected/Palm sample at a
Borel random right horizon. -/
theorem iUnion_stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
    {n : ℕ} (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ) :
    ⋃ pastLabels : List (NonpreemptivePriorityArrivalIndex n),
      ⋃ futureLabels : List (NonpreemptivePriorityArrivalIndex n),
        stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
          i older target pastLabels futureLabels = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z (-older) 0,
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z (target z), rfl, rfl⟩

/-- A deterministic chronological order for the right-closed portion of a
selected-arrival future ledger after an intermediate physical horizon. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) : List (NonpreemptivePriorityArrivalIndex n) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  exact (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z)

/-- Membership in the canonical future ledger is membership in its literal
classwise right-closed physical interval. -/
theorem mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_iff
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t ↔
      q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndices i z t q.1 := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  simp [canonicalStationaryPriorityClassTaggedFutureArrivalIndices,
    nonpreemptivePriorityArrivalWindowIndices]

/-- Membership in the later canonical ledger is membership in its literal
right-closed interval `(t, u]`. -/
theorem mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter_iff
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u ↔
      q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u q.1 := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  simp [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter,
    nonpreemptivePriorityArrivalWindowIndices]

/-- Every index in a finite post-tag ledger occurs no later than its stated
horizon. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalIndex_le_horizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t) :
    stationaryPriorityClassTaggedArrival i z q.1 q.2 ≤ t := by
  have hindex := (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_iff
    i z t q).mp hq
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    have hwindow := (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
      0 t z.1.1 hgood qindex).mp
        (by simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using hwindow.2
  · have hwindow := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
      0 t (z.2 ⟨qclass, hqi⟩).1 qindex).mp
        (by simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hqi] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hqi] using hwindow.2

/-- Every index in a later right-closed ledger occurs strictly after its
left endpoint. -/
theorem horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalIndexAfter
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u) :
    t < stationaryPriorityClassTaggedArrival i z q.1 q.2 := by
  have hindex := (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter_iff
    i z t u q).mp hq
  rcases q with ⟨qclass, qindex⟩
  by_cases hqi : qclass = i
  · subst qclass
    have hwindow := (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
      t u z.1.1 hgood qindex).mp
        (by simpa [stationaryPriorityClassTaggedFutureArrivalIndicesAfter] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using hwindow.1
  · have hwindow := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
      t u (z.2 ⟨qclass, hqi⟩).1 qindex).mp
        (by simpa [stationaryPriorityClassTaggedFutureArrivalIndicesAfter, hqi] using hindex)
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hqi] using hwindow.1

/-- Every ledger index at or before an intermediate horizon precedes every
index in the later right-closed portion. -/
theorem stationaryPriorityClassTaggedArrivalIndexLE_of_mem_future_and_after
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (q r : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t)
    (hr : r ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u) :
    stationaryPriorityClassTaggedArrivalIndexLE i z q r := by
  unfold stationaryPriorityClassTaggedArrivalIndexLE
    stationaryPriorityClassTaggedArrivalIndexKey
  apply Prod.Lex.toLex_le_toLex.mpr
  left
  exact lt_of_le_of_lt
    (canonicalStationaryPriorityClassTaggedFutureArrivalIndex_le_horizon
      i z t hgood q hq)
    (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalIndexAfter
      i z t u hgood r hr)

/-- Chronologically ordered right-closed future ledgers concatenate exactly
across a nonnegative intermediate horizon. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalIndices_append_after
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ht : 0 ≤ t) (htu : t ≤ u) :
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z u =
      canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t ++
        canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let left := canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t
  let right := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u
  have hdisjoint : List.Disjoint left right := by
    rw [List.disjoint_iff_ne]
    intro q hq r hr heq
    subst r
    exact (not_le_of_gt
      (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalIndexAfter
        i z t u hgood q (by simpa [right] using hr)))
      (canonicalStationaryPriorityClassTaggedFutureArrivalIndex_le_horizon
        i z t hgood q (by simpa [left] using hq))
  have hnodup : (left ++ right).Nodup := by
    apply List.Nodup.append
    · exact Finset.sort_nodup _ _
    · exact Finset.sort_nodup _ _
    · exact hdisjoint
  have hpairwise : (left ++ right).Pairwise
      (stationaryPriorityClassTaggedArrivalIndexLE i z) := by
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.pairwise_sort _ _
    · exact Finset.pairwise_sort _ _
    · intro q hq r hr
      exact stationaryPriorityClassTaggedArrivalIndexLE_of_mem_future_and_after
        i z t u hgood q r (by simpa [left] using hq) (by simpa [right] using hr)
  have hsorted : ((left ++ right).toFinset).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = left ++ right := by
    exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z) hnodup).mpr
      hpairwise
  have hledger : (left ++ right).toFinset =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z u) := by
    rw [List.toFinset_append]
    change (canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t).toFinset ∪
        (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u).toFinset = _
    rw [show (canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t).toFinset =
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndices i z t) by
      exact Finset.sort_toFinset _ _]
    rw [show (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u).toFinset =
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u) by
      exact Finset.sort_toFinset _ _]
    rw [← nonpreemptivePriorityArrivalWindowIndices_union]
    exact congrArg nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedFutureArrivalIndices_eq_union_after
        i z t u hgood ht htu).symm
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndices i z u)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = left ++ right
  rw [← hledger]
  exact hsorted

/-- A right-closed future ledger is the chronological concatenation of its
strictly earlier and boundary-horizon portions. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalIndices_append_atHorizon
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t ++
        canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let left := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t
  let right := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t
  have hdisjoint : List.Disjoint left right := by
    rw [List.disjoint_iff_ne]
    intro q hq r hr heq
    subst r
    have hqindex : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z t q.1 := by
      simpa [left, canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
        nonpreemptivePriorityArrivalWindowIndices] using hq
    have hrindex : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon
        i z t q.1 := by
      simpa [right, canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon,
        nonpreemptivePriorityArrivalWindowIndices] using hr
    exact (Finset.mem_filter.mp hrindex).2 (Finset.mem_filter.mp hqindex).2
  have hnodup : (left ++ right).Nodup := by
    apply List.Nodup.append
    · exact Finset.sort_nodup _ _
    · exact Finset.sort_nodup _ _
    · exact hdisjoint
  have hpairwise : (left ++ right).Pairwise
      (stationaryPriorityClassTaggedArrivalIndexLE i z) := by
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.pairwise_sort _ _
    · exact Finset.pairwise_sort _ _
    · intro q hq r hr
      have hqindex : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
          i z t q.1 := by
        simpa [left, canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
          nonpreemptivePriorityArrivalWindowIndices] using hq
      have hrindex : r.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon
          i z t r.1 := by
        simpa [right, canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon,
          nonpreemptivePriorityArrivalWindowIndices] using hr
      unfold stationaryPriorityClassTaggedArrivalIndexLE
        stationaryPriorityClassTaggedArrivalIndexKey
      apply Prod.Lex.toLex_le_toLex.mpr
      left
      rw [stationaryPriorityClassTaggedArrival_eq_horizon_of_mem_futureAtHorizon
        i z t hgood r.1 r.2 hrindex]
      exact (Finset.mem_filter.mp hqindex).2
  have hsorted : ((left ++ right).toFinset).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = left ++ right := by
    exact (List.toFinset_sort (r := stationaryPriorityClassTaggedArrivalIndexLE i z) hnodup).mpr
      hpairwise
  have hledger : (left ++ right).toFinset =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndices i z t) := by
    rw [List.toFinset_append]
    change (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z t).toFinset ∪
        (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t).toFinset = _
    rw [show (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z t).toFinset = nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t) by
      exact Finset.sort_toFinset _ _]
    rw [show (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon
        i z t).toFinset = nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t) by
      exact Finset.sort_toFinset _ _]
    rw [← nonpreemptivePriorityArrivalWindowIndices_union]
    exact congrArg nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedFutureArrivalIndices_eq_before_union_atHorizon
        i z t).symm
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndices i z t)).sort
      (stationaryPriorityClassTaggedArrivalIndexLE i z) = left ++ right
  rw [← hledger]
  exact hsorted

/-- The literal finite list of post-tag priority jobs used to continue the
post-admission selected queue state. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t).map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
      serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- The literal post-tag jobs strictly before a queried future horizon. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t).map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
      serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- The canonical tag-plus-strict-future index decomposition preserves the
complete arrival-job records, so it is directly usable by a finite queue
replay. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowJobs_zero_to_eq_tag_cons_future
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hzero : ∀ q : NonpreemptivePriorityArrivalIndex n,
      stationaryPriorityClassTaggedArrival i z q.1 q.2 = 0 → q = Sigma.mk i 0) :
    canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z 0 t =
      stationaryPriorityClassTaggedJob meanService i z ::
        canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t := by
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
  rw [canonicalStationaryPriorityClassTaggedArrivalWindowIndices_zero_to_eq_tag_cons_future
    i z t ht hgood hzero]
  rfl

/-- The literal post-tag jobs at a queried future horizon. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon i z t).map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
      serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- The right-closed literal job ledger splits into jobs strictly before its
horizon followed by its boundary-horizon jobs. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t ++
        canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon meanService i z t := by
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
  rw [canonicalStationaryPriorityClassTaggedFutureArrivalIndices_append_atHorizon
    i z t hgood, List.map_append]

/-- Every job in the strict portion of the finite future ledger arrives
strictly before the queried horizon. -/
theorem arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t) :
    job.arrivalTime < t := by
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon at hjob
  rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
  have hqindex : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z t q.1 := by
    simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      nonpreemptivePriorityArrivalWindowIndices] using hq
  exact (Finset.mem_filter.mp hqindex).2

/-- In a passive class, every labelled arrival retained strictly before the
epoch of another labelled arrival has a strictly smaller class index. -/
theorem stationaryPriorityClassTaggedFutureArrivalIndex_lt_of_mem_beforeHorizon
    {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (k l : ℤ)
    (hmember : Sigma.mk j k ∈
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z (stationaryPriorityClassTaggedArrival i z j l)) :
    k < l := by
  have hindex : k ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z (stationaryPriorityClassTaggedArrival i z j l) j := by
    simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      nonpreemptivePriorityArrivalWindowIndices] using hmember
  have harrival : stationaryPriorityClassTaggedArrival i z j k <
      stationaryPriorityClassTaggedArrival i z j l :=
    (Finset.mem_filter.mp hindex).2
  by_contra hnot
  have hlk : l ≤ k := le_of_not_gt hnot
  have hreverse : stationaryPriorityClassTaggedArrival i z j l ≤
      stationaryPriorityClassTaggedArrival i z j k :=
    (strictMono_stationaryPriorityClassTaggedArrival_of_ne i j hji z).monotone hlk
  exact (not_le_of_gt harrival) hreverse

/-- Every job in the boundary portion of the finite future ledger arrives at
the queried horizon. -/
theorem arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
      meanService i z t) :
    job.arrivalTime = t := by
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon at hjob
  rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
  apply stationaryPriorityClassTaggedArrival_eq_horizon_of_mem_futureAtHorizon
    i z t hgood q.1 q.2
  simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon,
    nonpreemptivePriorityArrivalWindowIndices] using hq

/-- The literal jobs in the later right-closed portion of a future ledger. -/
noncomputable def canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u).map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
      serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 }

/-- Literal post-tag arrival jobs concatenate exactly across adjacent
right-closed horizons. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ht : 0 ≤ t) (htu : t ≤ u) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z u =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t ++
        canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z t u := by
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
  rw [canonicalStationaryPriorityClassTaggedFutureArrivalIndices_append_after
    i z t u hgood ht htu, List.map_append]

/-- The later literal-job ledger contains exactly the indexed selected/Palm
arrivals in its right-closed interval. -/
theorem mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z t u ↔
      ∃ (j : Fin n) (k : ℤ),
        k ∈ stationaryPriorityClassTaggedFutureArrivalIndicesAfter i z t u j ∧
          job =
            { identifier := Sigma.mk j k
              priority := j
              arrivalTime := stationaryPriorityClassTaggedArrival i z j k
              serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k } := by
  constructor
  · intro hjob
    rcases List.mem_map.mp hjob with ⟨q, hq, hcoordinate⟩
    refine ⟨q.1, q.2,
      (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter_iff i z t u q).mp hq,
      ?_⟩
    simpa using hcoordinate.symm
  · rintro ⟨j, k, hindex, rfl⟩
    apply List.mem_map.mpr
    refine ⟨Sigma.mk j k,
      (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAfter_iff i z t u
        (Sigma.mk j k)).mpr hindex, rfl⟩

/-- Every literal job in the later right-closed ledger arrives strictly after
the intermediate horizon. -/
theorem horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z t u) :
    t < job.arrivalTime := by
  rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
  simpa using
    horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalIndexAfter
      i z t u hgood q hq

/-- The canonical future job ledger contains exactly its indexed literal
post-tag arrivals. -/
theorem mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t ↔
      ∃ (j : Fin n) (k : ℤ),
        k ∈ stationaryPriorityClassTaggedFutureArrivalIndices i z t j ∧
          job =
            { identifier := Sigma.mk j k
              priority := j
              arrivalTime := stationaryPriorityClassTaggedArrival i z j k
              serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k } := by
  constructor
  · intro hjob
    rcases List.mem_map.mp hjob with ⟨q, hq, hcoordinate⟩
    refine ⟨q.1, q.2,
      (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_iff i z t q).mp hq,
      ?_⟩
    simpa using hcoordinate.symm
  · rintro ⟨j, k, hindex, rfl⟩
    apply List.mem_map.mpr
    refine ⟨Sigma.mk j k,
      (mem_canonicalStationaryPriorityClassTaggedFutureArrivalIndices_iff i z t
        (Sigma.mk j k)).mpr hindex, rfl⟩

/-- The finite post-tag ledger has no duplicate job labels. -/
theorem nodup_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t).Nodup := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobs
  apply List.Nodup.map
  · intro first second hjob
    simpa using congrArg NonpreemptivePriorityJob.identifier hjob
  · exact Finset.sort_nodup _ _

/-- Every job in the finite future ledger occurs strictly after the Palm tag. -/
theorem arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) :
    0 < job.arrivalTime := by
  rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
    meanService i z t job).mp hjob with ⟨j, k, hindex, rfl⟩
  by_cases hji : j = i
  · subst j
    have hselected : k ∈ Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed
        0 t z.1.1 := by
      simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using hindex
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
        0 t z.1.1 hgood k).mp hselected |>.1
  · have hpassive : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 t (z.2 ⟨j, hji⟩).1 := by
      simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hji] using hindex
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hji] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
        0 t (z.2 ⟨j, hji⟩).1 k).mp hpassive |>.1

/-- Every job in the finite future ledger occurs no later than its horizon. -/
theorem arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) :
    job.arrivalTime ≤ t := by
  rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
    meanService i z t job).mp hjob with ⟨j, k, hindex, rfl⟩
  by_cases hji : j = i
  · subst j
    have hselected : k ∈ Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed
        0 t z.1.1 := by
      simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using hindex
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
        0 t z.1.1 hgood k).mp hselected |>.2
  · have hpassive : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 t (z.2 ⟨j, hji⟩).1 := by
      simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hji] using hindex
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hji] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
        0 t (z.2 ⟨j, hji⟩).1 k).mp hpassive |>.2

/-- The selected customer itself is not duplicated in the strictly-post-tag
future ledger. -/
theorem stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedJob meanService i z ∉
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t := by
  intro htag
  have hpositive := arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    meanService i z t hgood _ htag
  rw [stationaryPriorityClassTaggedJob_arrivalTime] at hpositive
  exact lt_irrefl _ hpositive

/-- Enlarging a right-closed post-tag horizon retains every already listed
literal arrival. -/
theorem mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_mono
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (htu : t ≤ u)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) :
    job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z u := by
  rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
    meanService i z t job).mp hjob with ⟨j, k, hindex, rfl⟩
  apply (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
    meanService i z u _).mpr
  refine ⟨j, k, ?_, rfl⟩
  by_cases hji : j = i
  · subst j
    have hselected : k ∈ Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed
        0 t z.1.1 := by
      simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using hindex
    have hinterval := (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
      0 t z.1.1 hgood k).mp hselected
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices] using
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
        0 u z.1.1 hgood k).mpr ⟨hinterval.1, hinterval.2.trans htu⟩
  · have hpassive : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 t (z.2 ⟨j, hji⟩).1 := by
      simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hji] using hindex
    have hinterval := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
      0 t (z.2 ⟨j, hji⟩).1 k).mp hpassive
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hji] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
        0 u (z.2 ⟨j, hji⟩).1 k).mpr ⟨hinterval.1, hinterval.2.trans htu⟩

/-- The finite future jobs are chronological under the same deterministic
time-and-label convention as the finite remote-past traces. -/
theorem pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t).Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobs
  rw [List.pairwise_map]
  apply (Finset.pairwise_sort _ _).imp
  intro first second horder
  unfold stationaryPriorityClassTaggedArrivalIndexLE
    stationaryPriorityClassTaggedArrivalIndexKey at horder
  exact Prod.Lex.monotone_fst _ _ horder

/-- The finite right-closed future ledger carries exactly the cumulative
post-tag work used by the selected-input net-drift process. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    nonpreemptivePriorityArrivalTraceServiceWork
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) =
      stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndices i z t)
  unfold nonpreemptivePriorityArrivalTraceServiceWork
    canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices
  simp only [List.map_map]
  change (ledger.sort (stationaryPriorityClassTaggedArrivalIndexLE i z) |>.map
      (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)).sum = _
  calc
    (ledger.sort (stationaryPriorityClassTaggedArrivalIndexLE i z) |>.map
        (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)).sum =
        (ledger.toList.map fun q =>
          stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2).sum :=
      ((Finset.sort_perm_toList ledger
        (stationaryPriorityClassTaggedArrivalIndexLE i z)).map _).sum_eq
    _ = ∑ q ∈ ledger,
        stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 := by
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)
          ledger.nodup_toList).symm
    _ = stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t := by
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
        stationaryPriorityTaggedTotalFutureWorkAggregate
        stationaryPriorityTaggedFutureWorkAggregate
        stationaryPriorityClassTaggedFutureArrivalIndices
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hji]

/-- The scalar terminal workload of a canonical finite selected/Palm trace.
Unlike a full queue state, this real-valued observable has a direct
countable-fiber Borel construction. -/
def canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) : ℝ :=
  nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
    (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) b

/-- The terminal workload of every finite canonical selected/Palm arrival
window is Borel. -/
theorem measurable_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (a b : ℝ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService i z a b) := by
  refine Probability.measurable_of_countable_measurable_cover
    (fun labels : List (NonpreemptivePriorityArrivalIndex n) =>
      {z | canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b = labels})
    (fun labels =>
      measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
        i a b labels)
    ?_ (fun z =>
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService i z a b)
    (fun labels z => nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
      (evaluateNonpreemptivePriorityJobList
        (labels.map (stationaryPriorityClassTaggedArrivalJobCoordinate meanService i)) z) b)
    ?_ ?_
  · ext z
    constructor
    · intro _
      simp
    · intro _
      exact Set.mem_iUnion.mpr
        ⟨canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b, rfl⟩
  · intro labels
    apply measurable_nonpreemptivePriorityArrivalTraceTerminalResidualWork_eval
      (fun _ => a) (fun _ => 0) (fun _ => b) measurable_const measurable_const
      measurable_const
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
    exact stationaryPriorityClassTaggedArrivalJobCoordinate_coordinatesMeasurable
      meanService i q
  · intro labels z hlabels
    simp only [canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork,
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs,
      stationaryPriorityClassTaggedArrivalJobCoordinate,
      evaluateNonpreemptivePriorityJobList, List.map_map]
    rw [hlabels]
    rfl

/-- Canonical selected/Palm finite executions retain the class-FIFO
invariant. -/
theorem hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    hasClassConsistentWaiting
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b) := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
  apply hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
  exact hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState a

/-- Canonical selected/Palm finite executions are non-idling whenever work is
available. -/
theorem nonpreemptivePriorityWorkConserving_canonicalStationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    nonpreemptivePriorityWorkConserving
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b) := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply nonpreemptivePriorityWorkConserving_advance
  apply nonpreemptivePriorityWorkConserving_run
  exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a

/-- With positive work marks, the canonical selected/Palm trace follows the
scalar physical-time workload recursion. -/
theorem totalResidualWork_run_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hjobs : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z a b, 0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let jobs := canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b
    totalNonpreemptivePriorityResidualWork
        (runNonpreemptivePriorityArrivalTrace initial jobs) =
      nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
  dsimp only
  have htrace := totalNonpreemptivePriorityResidualWork_run_eq_arrivalTraceResidualWork
    (emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a)
    (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
    (by
      constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro j job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember)
    (nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a)
    (by
      intro job hjob
      exact left_le_arrivalTime_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z a b hgood job hjob)
    (pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z a b)
    hjobs
  simpa [emptyNonpreemptivePriorityWorkState,
    totalNonpreemptivePriorityResidualWork,
    activeNonpreemptivePriorityResidualWork, priorityWaitingResidualWork] using htrace

/-- The terminal service segment of a canonical selected/Palm execution obeys
the exact reflected-workload accounting law. -/
theorem totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_terminal
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hab : a ≤ b)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hjobs : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z a b, 0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
      (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
    totalNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b) =
      max 0 (totalNonpreemptivePriorityResidualWork afterArrivals -
        (b - afterArrivals.currentTime)) := by
  dsimp only
  apply totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [emptyNonpreemptivePriorityWorkState] using hab
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z a b hgood job hjob).le
  · apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro j job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  · apply nonpreemptivePriorityWorkConserving_run
    exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a
  · exact le_rfl

/-- A canonical selected/Palm finite execution has the scalar terminal
workload of its literal finite arrival ledger. -/
theorem totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hab : a ≤ b)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hjobs : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z a b, 0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
        (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) b := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let jobs := canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hrun : totalNonpreemptivePriorityResidualWork afterArrivals =
      nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
    simpa [initial, jobs, afterArrivals] using
      totalResidualWork_run_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z a b hgood hjobs
  have htime : afterArrivals.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime a jobs := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
    · intro job hjob
      simpa [initial, jobs] using
        left_le_arrivalTime_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
          meanService i z a b hgood job hjob
    · simpa [jobs] using
        pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
          meanService i z a b
  have hterminal :=
    totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_terminal
      meanService i z a b hab hgood hjobs
  change totalNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b) = _
  rw [hterminal, show totalNonpreemptivePriorityResidualWork afterArrivals =
    nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs from hrun, htime]
  rfl

/-- A canonical selected/Palm finite execution is clocked at its literal
right physical endpoint. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hab : a ≤ b)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b).currentTime = b := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply advanceNonpreemptivePriorityWorkState_currentTime_eq_target
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [emptyNonpreemptivePriorityWorkState] using hab
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z a b hgood job hjob).le
  · exact le_rfl

/-- A suffix of a canonical selected/Palm past ledger carries no more work
than the literal marked-work interval beginning at the suffix head. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_suffix_le_canonicalStationaryPriorityClassTaggedArrivalWindowTotalWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older cutoff : ℝ)
    (front suffix : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ other ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < other.serviceWork)
    (hsplit : canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z
      (-older) (-cutoff) = front ++ job :: suffix) :
    nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
      stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
        job.arrivalTime (-cutoff) := by
  let full := canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    meanService i z (-older) (-cutoff)
  let tailWindow := canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    meanService i z job.arrivalTime (-cutoff)
  have hjobFull : job ∈ full := by
    rw [show full = front ++ job :: suffix by exact hsplit]
    simp
  have htimeSorted : full.Pairwise (fun first second =>
      first.arrivalTime ≤ second.arrivalTime) := by
    exact pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff)
  have htailTime : ∀ other ∈ job :: suffix, job.arrivalTime ≤ other.arrivalTime := by
    have hsplitSorted : (front ++ job :: suffix).Pairwise (fun first second =>
        first.arrivalTime ≤ second.arrivalTime) := by
      rw [show full = front ++ job :: suffix by exact hsplit] at htimeSorted
      exact htimeSorted
    have htailSorted : (job :: suffix).Pairwise (fun first second =>
        first.arrivalTime ≤ second.arrivalTime) :=
      (List.pairwise_append.mp hsplitSorted).2.1
    rcases List.pairwise_cons.mp htailSorted with ⟨hhead, _⟩
    intro other hother
    rcases List.mem_cons.mp hother with rfl | hother
    · exact le_rfl
    · exact hhead other hother
  have htailSubset : (job :: suffix) ⊆ tailWindow := by
    intro other hother
    have hotherFull : other ∈ full := by
      rw [show full = front ++ job :: suffix by exact hsplit]
      exact List.mem_append_right _ hother
    have htime := htailTime other hother
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z (-older) (-cutoff) other).mp hotherFull with ⟨j, k, hindex, rfl⟩
    apply (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z job.arrivalTime (-cutoff) _).mpr
    refine ⟨j, k, ?_, rfl⟩
    by_cases hji : j = i
    · subst j
      have hfullBounds := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        (-older) (-cutoff) z.1.1 hgood k).mp (by
          simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices,
        stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival] using
        (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
          job.arrivalTime (-cutoff) z.1.1 hgood k).mpr
          ⟨by simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using htime, hfullBounds.2⟩
    · have hfullBounds :=
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          (-older) (-cutoff) (z.2 ⟨j, hji⟩).1 k).mp (by
            simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji,
        stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival] using
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          job.arrivalTime (-cutoff) (z.2 ⟨j, hji⟩).1 k).mpr
          ⟨by simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hji] using htime, hfullBounds.2⟩
  have hjobLeft : -older ≤ job.arrivalTime := by
    exact left_le_arrivalTime_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff) hgood job hjobFull
  have htailWindowSubset : tailWindow ⊆ full := by
    intro other hother
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z job.arrivalTime (-cutoff) other).mp hother with ⟨j, k, hindex, rfl⟩
    apply (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z (-older) (-cutoff) _).mpr
    refine ⟨j, k, ?_, rfl⟩
    by_cases hji : j = i
    · subst j
      have htailBounds := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        job.arrivalTime (-cutoff) z.1.1 hgood k).mp (by
          simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
        (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
          (-older) (-cutoff) z.1.1 hgood k).mpr
          ⟨hjobLeft.trans htailBounds.1, htailBounds.2⟩
    · have htailBounds :=
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          job.arrivalTime (-cutoff) (z.2 ⟨j, hji⟩).1 k).mp (by
            simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          (-older) (-cutoff) (z.2 ⟨j, hji⟩).1 k).mpr
          ⟨hjobLeft.trans htailBounds.1, htailBounds.2⟩
  have htailNodup : (job :: suffix).Nodup := by
    have hfullNodup := nodup_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff)
    change full.Nodup at hfullNodup
    rw [show full = front ++ job :: suffix by exact hsplit] at hfullNodup
    exact List.Nodup.of_append_right hfullNodup
  have htailSubperm : List.Subperm (job :: suffix) tailWindow :=
    htailNodup.subperm htailSubset
  rcases htailSubperm with ⟨middle, hperm, hsublist⟩
  calc
    nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) =
        ((job :: suffix).map fun other => other.serviceWork).sum := rfl
    _ = (middle.map fun other => other.serviceWork).sum := (hperm.map _).sum_eq.symm
    _ ≤ (tailWindow.map fun other => other.serviceWork).sum := by
      apply List.Sublist.sum_le_sum (hsublist.map fun other => other.serviceWork)
      intro work hwork
      rcases List.mem_map.mp hwork with ⟨other, hother, rfl⟩
      exact (hpositive other (htailWindowSubset hother)).le
    _ = stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
        job.arrivalTime (-cutoff) := by
      exact nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z job.arrivalTime (-cutoff)

/-- A selected/Palm net-input cutoff empties every canonical finite trace
started no later than that cutoff. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_canonicalStationaryPriorityClassTaggedNetPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < job.serviceWork) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-older) 0
      (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z
        (-older) (-cutoff)) (-cutoff) = 0 := by
  apply nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_all_suffixes_le
  · rw [show nonpreemptivePriorityArrivalTraceServiceWork
        (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z
          (-older) (-cutoff)) =
        stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
          (-older) (-cutoff) by
      exact nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z (-older) (-cutoff)]
    have hbound :=
      stationaryPriorityClassTaggedArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
        meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon
    linarith
  · intro front suffix job hsplit
    have hjobMem : job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z (-older) (-cutoff) := by
      rw [hsplit]
      simp
    have hjobBeforeCutoff : job.arrivalTime ≤ -cutoff :=
      (arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z (-older) (-cutoff) hgood job hjobMem).le
    have hjobHorizon : cutoff ≤ -job.arrivalTime := by
      linarith
    calc
      nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
          stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
            job.arrivalTime (-cutoff) :=
        nonpreemptivePriorityArrivalTraceServiceWork_suffix_le_canonicalStationaryPriorityClassTaggedArrivalWindowTotalWork
          meanService i z older cutoff front suffix job hgood hpositive hsplit
      _ ≤ -job.arrivalTime - cutoff := by
        simpa using
          stationaryPriorityClassTaggedArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
            meanService i z cutoff (-job.arrivalTime) hcutoff hgood hcutoffNonneg hjobHorizon
      _ = -cutoff - job.arrivalTime := by ring

/-- A canonical selected/Palm finite state begun before a net-input cutoff
has zero residual workload at that cutoff. -/
theorem totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_zero_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
          (-older) (-cutoff)) = 0 := by
  rw [totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
    meanService i z (-older) (-cutoff) (neg_le_neg horizon) hgood hpositive]
  exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_canonicalStationaryPriorityClassTaggedNetPastCutoff
    meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon hpositive

/-- Positive class means make every canonical selected/Palm finite ledger
carry strictly positive service work almost surely. -/
theorem ae_all_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_serviceWork_positive
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (a b : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b,
        0 < job.serviceWork := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hz
  intro job hjob
  rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z a b job).mp hjob with ⟨j, k, _, hcoordinate⟩
  subst job
  exact hz j k

/-- At a global selected/Palm net-input cutoff, every sufficiently remote
canonical finite start has the same live queue as an empty state at the
cutoff epoch. -/
theorem liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_empty_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < job.serviceWork) :
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
        (-older) (-cutoff))
      (emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-cutoff)) := by
  have hpositiveState : positiveNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
        (-older) (-cutoff)) := by
    unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
    dsimp only
    apply positiveNonpreemptivePriorityResidualWork_advance
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro j job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hpositive
  have htotal :=
    totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_zero_of_netPastCutoff
      meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon hpositive
  have htime :=
    canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
      meanService i z (-older) (-cutoff) (neg_le_neg horizon) hgood
  have hempty := liveEquivalent_emptyNonpreemptivePriorityWorkState_of_totalResidualWork_eq_zero
    (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
      (-older) (-cutoff)) hpositiveState htotal
  rw [htime] at hempty
  exact hempty

/-- All canonical selected/Palm traces begun before a global backward
net-input cutoff coalesce to the trace freshly begun at that cutoff. -/
theorem liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) 0, 0 < job.serviceWork) :
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-cutoff) 0) := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older)
  let front := canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    meanService i z (-older) (-cutoff)
  let suffix := canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    meanService i z (-cutoff) 0
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  have hleftCut : -older ≤ -cutoff := neg_le_neg horizon
  have hcutRight : -cutoff ≤ 0 := neg_nonpos.mpr hcutoffNonneg
  have hwholeAppend : canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) 0 = front ++ suffix := by
    exact canonicalStationaryPriorityClassTaggedArrivalWindowJobs_append
      meanService i z (-older) (-cutoff) 0 hgood hleftCut hcutRight
  have hfrontPositive : ∀ job ∈ front, 0 < job.serviceWork := by
    intro job hjob
    apply hpositive job
    rw [hwholeAppend]
    exact List.mem_append_left _ hjob
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterFront := by
    dsimp [afterFront]
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [initial, emptyNonpreemptivePriorityWorkState] at hactive
      · intro j job hmember
        simp [initial, emptyNonpreemptivePriorityWorkState] at hmember
    · exact hfrontPositive
  have hafterWork : nonpreemptivePriorityWorkConserving afterFront := by
    dsimp [afterFront]
    apply nonpreemptivePriorityWorkConserving_run
    exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState (-older)
  have hafterCutoff : afterFront.currentTime ≤ -cutoff := by
    dsimp [afterFront]
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [initial, emptyNonpreemptivePriorityWorkState] using hleftCut
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z (-older) (-cutoff) hgood job hjob).le
  have hfrontReset : totalNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
        (-older) (-cutoff)) = 0 := by
    apply totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_zero_of_netPastCutoff
      meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon
    exact hfrontPositive
  have hcutoffZero : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterFront) (-cutoff) afterFront) = 0 := by
    simpa [canonicalStationaryPriorityClassTaggedFiniteWindowState, initial, front, afterFront]
      using hfrontReset
  have hsuffixCutoff : ∀ job ∈ suffix, -cutoff ≤ job.arrivalTime := by
    intro job hjob
    exact left_le_arrivalTime_canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-cutoff) 0 hgood job hjob
  have hcontinuation := liveEquivalent_advance_run_from_empty_at_cutoff
    afterFront (-cutoff) 0 suffix hafterCutoff hcutRight hafterPositive hafterWork le_rfl
    hcutoffZero hsuffixCutoff
  have hleftState : canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-older) 0 =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace afterFront suffix)) 0
        (runNonpreemptivePriorityArrivalTrace afterFront suffix) := by
    unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
    dsimp only
    rw [hwholeAppend, runNonpreemptivePriorityArrivalTrace_append]
  have hrightState : canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-cutoff) 0 =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-cutoff)) suffix)) 0
        (runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-cutoff)) suffix) := by
    rfl
  rw [hleftState, hrightState]
  exact hcontinuation

/-- Under strict total load, canonical selected/Palm priority traces begun at
sufficiently remote past epochs almost surely coalesce at the observation
epoch. -/
theorem ae_exists_canonicalStationaryPriorityClassTaggedFiniteWindowState_remotePastLiveCoalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
          (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-cutoff) 0) := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hcutoff hpositive hgood
  rcases hcutoff with ⟨cutoff, hcutoffNonneg, hmaximum⟩
  refine ⟨cutoff, hcutoffNonneg, ?_⟩
  intro older horizon
  apply liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_of_netPastCutoff
    meanService i z cutoff older hmaximum hgood hcutoffNonneg horizon
  intro job hjob
  rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z (-older) 0 job).mp hjob with ⟨j, k, _, hcoordinate⟩
  subst job
  exact hpositive j k

/-- The Palm-tagged customer is absent from every finite trace ending at the
pre-arrival epoch.  The ledger is half-open at zero, whereas the selected job
arrives exactly at zero. -/
theorem stationaryPriorityClassTaggedJob_not_mem_canonicalPastArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedJob meanService i z ∉
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) 0 := by
  intro htag
  have hbefore := arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
    meanService i z (-older) 0 hgood _ htag
  rw [stationaryPriorityClassTaggedJob_arrivalTime] at hbefore
  exact lt_irrefl _ hbefore

/-- Before the Palm arrival, the finite literal replay has no representation
of the selected customer: queue transitions can only rearrange jobs from its
half-open input ledger. -/
theorem not_nonpreemptivePriorityWorkStateContainsJob_canonicalPastFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    ¬ nonpreemptivePriorityWorkStateContainsJob
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedJob meanService i z) := by
  intro hcontains
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState at hcontains
  dsimp only at hcontains
  have hafterArrivals : nonpreemptivePriorityWorkStateContainsJob
      (runNonpreemptivePriorityArrivalTrace
        (emptyNonpreemptivePriorityWorkState
          (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
        (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) 0))
      (stationaryPriorityClassTaggedJob meanService i z) :=
    nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ 0 _ _ hcontains
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse _ _ _ hafterArrivals with
      hempty | hledger
  · simpa [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState] using hempty
  · exact stationaryPriorityClassTaggedJob_not_mem_canonicalPastArrivalWindowJobs
      meanService i z older hgood hledger

/-- Every job represented by a finite pre-origin replay has an identifier
different from the selected Palm label.  This is the provenance form of the
half-open convention at the Palm origin. -/
theorem identifier_ne_selected_canonicalPastFiniteWindowState_of_contains
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0) job) :
    job.identifier ≠ (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n) := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState at hcontains
  dsimp only at hcontains
  have hafterArrivals : nonpreemptivePriorityWorkStateContainsJob
      (runNonpreemptivePriorityArrivalTrace
        (emptyNonpreemptivePriorityWorkState
          (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
        (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) 0)) job :=
    nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ 0 _ _ hcontains
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse _ _ _ hafterArrivals with
      hempty | hledger
  · simpa [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState] using hempty
  · intro hidentifier
    have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
      exact eq_stationaryPriorityClassTaggedJob_of_mem_canonicalArrivalWindowJobs_of_identifier_eq
        meanService i z (-older) 0 job hledger hidentifier
    apply stationaryPriorityClassTaggedJob_not_mem_canonicalPastArrivalWindowJobs
      meanService i z older hgood
    rwa [← htag]

/-- No literal job with a strictly positive arrival epoch can be represented
by a finite half-open pre-origin replay.  This is the record-level version of
the fact that the selected Palm observation begins after all of its past
input ledger. -/
theorem not_nonpreemptivePriorityWorkStateContainsJob_canonicalPastFiniteWindowState_of_arrivalTime_pos
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hpositive : 0 < job.arrivalTime) :
    ¬ nonpreemptivePriorityWorkStateContainsJob
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      job := by
  intro hcontains
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState at hcontains
  dsimp only at hcontains
  have hafterArrivals : nonpreemptivePriorityWorkStateContainsJob
      (runNonpreemptivePriorityArrivalTrace
        (emptyNonpreemptivePriorityWorkState
          (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
        (canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) 0))
      job :=
    nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ 0 _ _ hcontains
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse _ _ _ hafterArrivals with
      hempty | hledger
  · simp [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState] at hempty
  · have hbefore := arrivalTime_lt_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_right
      meanService i z (-older) 0 hgood job hledger
    linarith

/-- The causal selected/Palm priority state obtained from the remote past.
When the global cutoff does not exist the definition is empty; strict total
load gives the cutoff almost surely. -/
noncomputable def stationaryPriorityClassTaggedRemotePastState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) := by
  classical
  exact if hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff then
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
      (-hcutoff.choose) 0
  else
    emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) 0

/-- On a selected/Palm path with a global net-input cutoff, the causal
remote-past state is the literal finite trace begun at its selected cutoff. -/
theorem stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff) :
    stationaryPriorityClassTaggedRemotePastState meanService i z =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
        (-hcutoff.choose) 0 := by
  simp [stationaryPriorityClassTaggedRemotePastState, hcutoff]

/-- Whenever the selected and global finite replays have both coalesced to
their remote-past states, the Campbell-recentered selected pre-arrival state
and the global state viewed at that arrival are live-equivalent.  This is a
deterministic bridge; the probabilistic work is to supply the two eventual
coalescence hypotheses under their respective laws. -/
theorem liveEquivalent_stationaryPriorityClassTaggedRemotePastState_campbellRecenter_globalFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older : ℝ)
    (hselected : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k)))
    (hglobal : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k)
          (multiclassStationaryPoissonWorkClassAssemble i x))) ) :
    liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityClassTaggedRemotePastState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k))
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k)
          (multiclassStationaryPoissonWorkClassAssemble i x))) := by
  apply liveEquivalentNonpreemptivePriorityWorkState_trans
    (liveEquivalentNonpreemptivePriorityWorkState_symm hselected)
  simpa only [canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_eq_globalFlow
    arrivalRate meanService harrivalRate i x k (-older) 0] using hglobal

/-- The causal remote-past state contains no copy of the selected Palm
customer.  Its nonempty branch is a half-open pre-arrival finite replay and
its fallback branch is empty. -/
theorem not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    ¬ nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedRemotePastState meanService i z)
      (stationaryPriorityClassTaggedJob meanService i z) := by
  classical
  unfold stationaryPriorityClassTaggedRemotePastState
  split_ifs with hcutoff
  · exact not_nonpreemptivePriorityWorkStateContainsJob_canonicalPastFiniteWindowState
      meanService i z hcutoff.choose hgood
  · simp [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState]

/-- Every live or recorded job in the causal remote-past state has a stream
identifier different from the selected Palm label.  In the finite branch,
all such jobs come from a half-open pre-origin canonical ledger; the fallback
branch is empty. -/
theorem identifier_ne_selected_stationaryPriorityClassTaggedRemotePastState_of_contains
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedRemotePastState meanService i z) job) :
    job.identifier ≠ (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n) := by
  classical
  unfold stationaryPriorityClassTaggedRemotePastState at hcontains
  by_cases hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff
  · simp only [dif_pos hcutoff] at hcontains
    unfold canonicalStationaryPriorityClassTaggedFiniteWindowState at hcontains
    dsimp only at hcontains
    have hafterArrivals : nonpreemptivePriorityWorkStateContainsJob
        (runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-hcutoff.choose))
          (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
            meanService i z (-hcutoff.choose) 0)) job :=
      nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ 0 _ _ hcontains
    rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse _ _ _ hafterArrivals with
        hempty | hledger
    · simp [nonpreemptivePriorityWorkStateContainsJob,
        emptyNonpreemptivePriorityWorkState] at hempty
    · intro hidentifier
      have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
        exact eq_stationaryPriorityClassTaggedJob_of_mem_canonicalArrivalWindowJobs_of_identifier_eq
          meanService i z (-hcutoff.choose) 0 job hledger hidentifier
      apply stationaryPriorityClassTaggedJob_not_mem_canonicalPastArrivalWindowJobs
        meanService i z hcutoff.choose hgood
      rwa [← htag]
  · simp only [dif_neg hcutoff] at hcontains
    simp [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState] at hcontains

/-- A strictly post-origin literal job is absent from the causal remote-past
state, including its fallback empty branch. -/
theorem not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState_of_arrivalTime_pos
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : 0 < job.arrivalTime) :
    ¬ nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedRemotePastState meanService i z) job := by
  classical
  unfold stationaryPriorityClassTaggedRemotePastState
  split_ifs with hcutoff
  · exact not_nonpreemptivePriorityWorkStateContainsJob_canonicalPastFiniteWindowState_of_arrivalTime_pos
      meanService i z hcutoff.choose hgood job hpositive
  · simp [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState]

/-- Strict total load supplies a causal selected/Palm priority state to which
all sufficiently remote canonical finite traces coalesce. -/
theorem ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
          (stationaryPriorityClassTaggedRemotePastState meanService i z) := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hcutoff hpositive hgood
  refine ⟨hcutoff.choose, hcutoff.choose_spec.1, ?_⟩
  intro older horizon
  rw [stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
    meanService i z hcutoff]
  apply liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_of_netPastCutoff
    meanService i z hcutoff.choose older hcutoff.choose_spec.2 hgood
      hcutoff.choose_spec.1 horizon
  intro job hjob
  rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
    meanService i z (-older) 0 job).mp hjob with ⟨j, k, _, hcoordinate⟩
  subst job
  exact hpositive j k

/-- Aggregate unfinished work in the causal selected/Palm state obtained from
the remote past. -/
noncomputable def stationaryPriorityClassTaggedRemotePastResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : ℝ :=
  totalNonpreemptivePriorityResidualWork
    (stationaryPriorityClassTaggedRemotePastState meanService i z)

/-- The literal queue state immediately after the selected customer is
admitted at its Palm arrival epoch.  The completion ledger is reset at that
observation epoch: it is a record of the selected customer's future response,
whereas the coalesced remote-past ledger has no effect on the live queue. -/
noncomputable def stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  admitNonpreemptivePriorityJob
    (clearNonpreemptivePriorityCompletionLedger
      (stationaryPriorityClassTaggedRemotePastState meanService i z))
    (stationaryPriorityClassTaggedJob meanService i z)

/-- A strictly post-origin literal job is absent immediately after the Palm
tag is admitted.  The only record added at that epoch is the tag itself. -/
theorem not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedArrivalState_of_arrivalTime_pos
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : 0 < job.arrivalTime) :
    ¬ nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedArrivalState meanService i z) job := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hremote : ¬ nonpreemptivePriorityWorkStateContainsJob remote job := by
    simpa [remote] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState_of_arrivalTime_pos
        meanService i z job hgood hpositive
  intro hcontains
  change nonpreemptivePriorityWorkStateContainsJob (admitNonpreemptivePriorityJob cleared tag) job
    at hcontains
  rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse cleared tag job hcontains with
      hcleared | htag
  · apply hremote
    rcases hcleared with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  · subst job
    rw [stationaryPriorityClassTaggedJob_arrivalTime] at hpositive
    exact lt_irrefl _ hpositive

/-- The tagged-response observation begins with an empty completion ledger.
The causal pre-arrival history determines the live queue but cannot be
mistaken for a completion of the selected customer. -/
theorem completed_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    (stationaryPriorityClassTaggedArrivalState meanService i z).completed = [] := by
  rw [stationaryPriorityClassTaggedArrivalState,
    completed_admitNonpreemptivePriorityJob,
    completed_clearNonpreemptivePriorityCompletionLedger]

/-- Admission itself makes the selected customer's literal post-arrival
state work-conserving, independently of how its causal remote past was chosen. -/
theorem nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    nonpreemptivePriorityWorkConserving
      (stationaryPriorityClassTaggedArrivalState meanService i z) := by
  unfold stationaryPriorityClassTaggedArrivalState
  apply nonpreemptivePriorityWorkConserving_admit

/-- At the Palm admission epoch, the selected customer has one live queue
location: it cannot be both active and present in a class FIFO list.  The
remote-past construction contains no prior tag, and the admission transition
inserts exactly this new tagged record. -/
theorem not_exists_tag_active_and_waiting_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    ¬ ∃ (residual : ℝ) (j : Fin n),
      (stationaryPriorityClassTaggedArrivalState meanService i z).active =
          some (stationaryPriorityClassTaggedJob meanService i z, residual) ∧
        stationaryPriorityClassTaggedJob meanService i z ∈
          (stationaryPriorityClassTaggedArrivalState meanService i z).waiting j := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let prepared := startNextNonpreemptivePriorityJob cleared
  have hremote : ¬ nonpreemptivePriorityWorkStateContainsJob remote
      (stationaryPriorityClassTaggedJob meanService i z) := by
    simpa [remote] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
        meanService i z hgood
  have hcleared : ¬ nonpreemptivePriorityWorkStateContainsJob cleared
      (stationaryPriorityClassTaggedJob meanService i z) := by
    intro hcontains
    apply hremote
    rcases hcontains with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  have hprepared : ¬ nonpreemptivePriorityWorkStateContainsJob prepared
      (stationaryPriorityClassTaggedJob meanService i z) := by
    intro hcontains
    apply hcleared
    exact nonpreemptivePriorityWorkStateContainsJob_startNext_reverse
      cleared (stationaryPriorityClassTaggedJob meanService i z) (by
        simpa [prepared] using hcontains)
  intro hbad
  rcases hbad with ⟨residual, j, hactive, hwaiting⟩
  change (admitNonpreemptivePriorityJob cleared
    (stationaryPriorityClassTaggedJob meanService i z)).active =
      some (stationaryPriorityClassTaggedJob meanService i z, residual) at hactive
  change stationaryPriorityClassTaggedJob meanService i z ∈
    (admitNonpreemptivePriorityJob cleared
      (stationaryPriorityClassTaggedJob meanService i z)).waiting j at hwaiting
  cases hpreparedActive : prepared.active with
  | none =>
      apply hprepared
      exact Or.inr (Or.inl ⟨j, by
        simpa [admitNonpreemptivePriorityJob, prepared, hpreparedActive] using hwaiting⟩)
  | some active =>
      apply hprepared
      have hadmit : admitNonpreemptivePriorityJob cleared
          (stationaryPriorityClassTaggedJob meanService i z) =
          enqueueNonpreemptivePriorityJob prepared
            (stationaryPriorityClassTaggedJob meanService i z) := by
        simp [admitNonpreemptivePriorityJob, prepared, hpreparedActive]
      rw [hadmit] at hactive
      have hpair : active = (stationaryPriorityClassTaggedJob meanService i z, residual) :=
        Option.some.inj (by
          simpa [enqueueNonpreemptivePriorityJob, hpreparedActive] using hactive)
      exact Or.inl ⟨active.2, by simp [hpreparedActive, hpair]⟩

/-- The selected Palm customer occurs exactly once across the live queue and
the fresh completion ledger immediately after its admission.  This strengthens
the ordinary membership fact: the remote-past replay contains no tag, and the
single admission transition adds one literal record. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (stationaryPriorityClassTaggedJob meanService i z) = 1 := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  have hremote : ¬ nonpreemptivePriorityWorkStateContainsJob remote
      (stationaryPriorityClassTaggedJob meanService i z) := by
    simpa [remote] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
        meanService i z hgood
  have hcleared : ¬ nonpreemptivePriorityWorkStateContainsJob cleared
      (stationaryPriorityClassTaggedJob meanService i z) := by
    intro hcontains
    apply hremote
    rcases hcontains with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  have hzero : nonpreemptivePriorityWorkStateJobMultiplicity cleared
      (stationaryPriorityClassTaggedJob meanService i z) = 0 :=
    nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
      cleared (stationaryPriorityClassTaggedJob meanService i z) hcleared
  change nonpreemptivePriorityWorkStateJobMultiplicity
    (admitNonpreemptivePriorityJob cleared
      (stationaryPriorityClassTaggedJob meanService i z))
    (stationaryPriorityClassTaggedJob meanService i z) = 1
  rw [nonpreemptivePriorityWorkStateJobMultiplicity_admit_self, hzero]

/-- A same-class customer waiting in the causal remote past is not overtaken
when the selected customer is admitted at the Palm origin.  It either remains
ahead in the class FIFO list or is the job dispatched immediately before the
selected arrival joins that list. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_stationaryPriorityClassTaggedArrivalState_of_mem
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (earlier : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hpriority : earlier.priority = i)
    (hwaiting : earlier ∈
      (stationaryPriorityClassTaggedRemotePastState meanService i z).waiting i) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      earlier (stationaryPriorityClassTaggedJob meanService i z) := by
  unfold stationaryPriorityClassTaggedArrivalState
  apply nonpreemptivePriorityFifoPrecedesDisposition_admit_of_mem
  · simpa [stationaryPriorityClassTaggedJob] using hpriority
  · simpa [clearNonpreemptivePriorityCompletionLedger] using hwaiting

/-- Continue the literal post-admission selected queue state through the
finite future ledger and then serve it to its physical horizon. -/
noncomputable def stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals

/-- Continuing the tagged state through a finite literal future ledger cannot
duplicate the selected Palm customer: that right-closed ledger contains only
strictly post-tag arrivals, while pure service evolution preserves literal
record multiplicity. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) = 1 := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
  have hfuture : ∀ newJob ∈
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t,
      newJob ≠ stationaryPriorityClassTaggedJob meanService i z := by
    intro newJob hmember htag
    subst newJob
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood hmember
  have hrun : nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals
      (stationaryPriorityClassTaggedJob meanService i z) =
        nonpreemptivePriorityWorkStateJobMultiplicity
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (stationaryPriorityClassTaggedJob meanService i z) := by
    exact nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) hfuture
  change nonpreemptivePriorityWorkStateJobMultiplicity
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals)
    (stationaryPriorityClassTaggedJob meanService i z) = 1
  rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance, hrun]
  exact nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
    meanService i z hgood

/-- At every finite tagged-response horizon, the completion ledger can contain
at most one copy of the selected literal job.  Thus the record inserted by the
finite queue semantics is not an artifact of replay duplication. -/
theorem completedJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState_le_one
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityCompletedJobMultiplicity
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) ≤ 1 := by
  calc
    nonpreemptivePriorityCompletedJobMultiplicity
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
        (stationaryPriorityClassTaggedJob meanService i z) ≤
        nonpreemptivePriorityWorkStateJobMultiplicity
          (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
          (stationaryPriorityClassTaggedJob meanService i z) :=
      nonpreemptivePriorityCompletedJobMultiplicity_le _ _
    _ = 1 :=
      nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z t hgood

/-- Every same-class FIFO predecessor disposition present immediately after
the selected customer is admitted persists throughout a finite post-arrival
replay.  It is therefore available at every candidate tagged completion
horizon: an old same-class predecessor is still ahead of the tag, is active,
or has completed; future same-class arrivals can only be appended behind the
tag. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (earlier later : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition
      (stationaryPriorityClassTaggedArrivalState meanService i z) earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) earlier later := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
  have hafterArrivals : nonpreemptivePriorityFifoPrecedesDisposition
      afterArrivals earlier later := by
    simpa [afterArrivals] using
      nonpreemptivePriorityFifoPrecedesDisposition_run
        (stationaryPriorityClassTaggedArrivalState meanService i z)
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
        earlier later hdisposition
  simpa [afterArrivals] using
    nonpreemptivePriorityFifoPrecedesDisposition_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals
      earlier later hafterArrivals

/-- Every same-class customer that was waiting immediately before the Palm
arrival remains accounted for throughout every finite literal future trace:
it is still ahead of the selected job, active, or recorded as completed. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_stationaryPriorityClassTaggedFinitePostArrivalState_of_mem
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (earlier : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hpriority : earlier.priority = i)
    (hwaiting : earlier ∈
      (stationaryPriorityClassTaggedRemotePastState meanService i z).waiting i) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      earlier (stationaryPriorityClassTaggedJob meanService i z) := by
  apply nonpreemptivePriorityFifoPrecedesDisposition_stationaryPriorityClassTaggedFinitePostArrivalState
  exact nonpreemptivePriorityFifoPrecedesDisposition_stationaryPriorityClassTaggedArrivalState_of_mem
    meanService i z earlier hpriority hwaiting

/-- A completely finite two-sided replay: execute the selected/Palm ledger
from a finite past horizon to zero, clear its historical observations, admit
the distinguished customer, and continue through a finite future horizon. -/
noncomputable def stationaryPriorityClassTaggedFiniteReplayPostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (admitNonpreemptivePriorityJob
      (clearNonpreemptivePriorityCompletionLedger preArrival)
      (stationaryPriorityClassTaggedJob meanService i z))
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals

/-- In a completely finite two-sided replay, the selected stream identifier
still determines the uniquely admitted selected job. -/
theorem eq_stationaryPriorityClassTaggedJob_of_contains_finiteReplayPostArrivalState_of_identifier_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older t) job)
    (hidentifier : job.identifier = (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n)) :
    job = stationaryPriorityClassTaggedJob meanService i z := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalState at hcontains
  dsimp only at hcontains
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let cleared := clearNonpreemptivePriorityCompletionLedger preArrival
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let initial := admitNonpreemptivePriorityJob cleared tag
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hafter : nonpreemptivePriorityWorkStateContainsJob afterArrivals job := by
    exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ t _ _
      (by simpa [afterArrivals] using hcontains)
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse initial jobs job hafter with
      hinitial | hjobs
  · rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse cleared tag job
      (by simpa [initial] using hinitial) with hcleared | htag
    · have hpre : nonpreemptivePriorityWorkStateContainsJob preArrival job := by
        rcases hcleared with hactive | hwaiting | hcompleted
        · exact Or.inl (by
            simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
        · exact Or.inr (Or.inl (by
            simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
        · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
      exact (identifier_ne_selected_canonicalPastFiniteWindowState_of_contains
        meanService i z older hgood job (by simpa [preArrival] using hpre) hidentifier).elim
    · simpa [tag] using htag
  · have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
      rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
        meanService i z t job).mp (by simpa [jobs] using hjobs) with ⟨j, k, _, hjob⟩
      subst job
      cases hidentifier
      rfl
    apply False.elim
    apply stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood
    rwa [← htag]

/-- The completely finite two-sided replay retains exactly one literal copy
of the selected customer: finite past input excludes its Palm label, the
admission adds one copy, and the strictly post-origin future ledger adds none. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFiniteReplayPostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older t)
      (stationaryPriorityClassTaggedJob meanService i z) = 1 := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalState
  dsimp only
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let cleared := clearNonpreemptivePriorityCompletionLedger preArrival
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let initial := admitNonpreemptivePriorityJob cleared tag
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hpre : ¬ nonpreemptivePriorityWorkStateContainsJob preArrival tag := by
    simpa [preArrival, tag] using
      not_nonpreemptivePriorityWorkStateContainsJob_canonicalPastFiniteWindowState
        meanService i z older hgood
  have hcleared : ¬ nonpreemptivePriorityWorkStateContainsJob cleared tag := by
    intro hcontains
    apply hpre
    rcases hcontains with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  have hzero : nonpreemptivePriorityWorkStateJobMultiplicity cleared tag = 0 :=
    nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains cleared tag hcleared
  have hinitial : nonpreemptivePriorityWorkStateJobMultiplicity initial tag = 1 := by
    change nonpreemptivePriorityWorkStateJobMultiplicity
      (admitNonpreemptivePriorityJob cleared tag) tag = 1
    rw [nonpreemptivePriorityWorkStateJobMultiplicity_admit_self, hzero]
  have hjobs : ∀ newJob ∈ jobs, newJob ≠ tag := by
    intro newJob hmember hnew
    subst newJob
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood (by simpa [jobs, tag] using hmember)
  have hrun : nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag =
      nonpreemptivePriorityWorkStateJobMultiplicity initial tag := by
    exact nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
      initial jobs tag hjobs
  change nonpreemptivePriorityWorkStateJobMultiplicity
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals) tag = 1
  rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance, hrun, hinitial]

/-- The selected customer's completion observation in a fully finite
two-sided replay. -/
noncomputable def stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) : Option ℝ :=
  nonpreemptivePriorityRecordedCompletionTime
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older t)
    (Sigma.mk i 0)

/-- Whenever a finite past trace has the same live queue as the causal remote
past, the complete finite replay is exactly the causal finite post-arrival
execution. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_liveEquivalent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z)) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older t =
      stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalState
    stationaryPriorityClassTaggedFinitePostArrivalState
    stationaryPriorityClassTaggedArrivalState
  dsimp only
  rw [clearNonpreemptivePriorityCompletionLedger_eq_of_liveEquivalent _ _ hequivalent]

/-- The finite selected-customer response after admission is present exactly
when the tag has entered the completion ledger by the specified horizon. -/
noncomputable def stationaryPriorityClassTaggedFinitePostArrivalResponseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : Option ℝ :=
  nonpreemptivePriorityRecordedCompletionTime
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
    (Sigma.mk i 0)

/-- The finite replay and causal post-arrival response observations agree
whenever their pre-arrival live queues agree. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_liveEquivalent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z)) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z older t =
      stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_liveEquivalent
    meanService i z older t hequivalent]

/-- The selected customer's stationary response is the canonical limsup of
total two-sided finite replays at matching natural past and future horizons.
On the almost-sure coalescence-and-stabilization event below, this is the
literal physical completion epoch.  Each finite replay uses zero before the
tag has completed; outside the stabilization event the limsup still provides
a total real-valued version. -/
noncomputable def stationaryPriorityClassTaggedResponseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
  Probability.stabilizedFiniteReplayResponse fun horizon z =>
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z (horizon : ℝ) (horizon : ℝ)).getD 0

/-- A selected-Palm response has literal remote-past semantics when the
diagonal finite replays eventually equal it almost surely.  This is a
semantic property of the concrete queue construction, not an assumed
stationary-output certificate. -/
def IsStationaryPriorityClassTaggedRemotePastResponse
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (response : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ) : Prop :=
  ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
    ∀ᶠ horizon : ℕ in Filter.atTop,
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
        meanService i z (horizon : ℝ) (horizon : ℝ)).getD 0 = response z

/-- The selected customer's queue-wait observable: its literal response time
minus its own required service.  The nonpreemptive trace is the object whose
pathwise workload decomposition will identify this difference with service
completed before the tag starts. -/
noncomputable def stationaryPriorityClassTaggedQueueWait
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
  fun z => stationaryPriorityClassTaggedResponseTime meanService i z -
    stationaryPriorityClassTaggedWorkRequirement meanService i z

/-- An eventually constant sequence of literal two-sided finite replay
observations has its common value as the canonical stationary response. -/
theorem stationaryPriorityClassTaggedResponseTime_eq_of_eventually_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (completedAt : ℝ)
    (hstabilizes : ∀ᶠ horizon : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
        meanService i z (horizon : ℝ) (horizon : ℝ) =
        some completedAt) :
    stationaryPriorityClassTaggedResponseTime meanService i z = completedAt := by
  unfold stationaryPriorityClassTaggedResponseTime
  apply Probability.stabilizedFiniteReplayResponse_eq_of_eventually_eq
    (fun horizon z =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
        meanService i z (horizon : ℝ) (horizon : ℝ)).getD 0)
    (fun _ => completedAt) z
  filter_upwards [hstabilizes] with horizon hresponse
  rw [hresponse]
  rfl

/-- A completion timestamp observed for the selected customer at one
nonnegative right-closed horizon is unchanged at every later horizon.  The
later ledger consists only of arrivals after the intermediate horizon, so its
service evolution can only prepend completion records. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eq_of_le
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ht : 0 ≤ t) (htu : t ≤ u)
    (hresponse :
      stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t =
        some completedAt) :
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalResponseTime at hresponse ⊢
  apply nonpreemptivePriorityRecordedCompletionTime_eq_of_ledgerExtension
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u)
    (Sigma.mk i 0) completedAt
  · unfold stationaryPriorityClassTaggedFinitePostArrivalState
    dsimp only
    rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
      meanService i z t u hgood ht htu, runNonpreemptivePriorityArrivalTrace_append]
    apply nonpreemptivePriorityCompletionLedgerExtension_advance_run_from_cutoff
      (runNonpreemptivePriorityArrivalTrace
        (stationaryPriorityClassTaggedArrivalState meanService i z)
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t))
      t u
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z t u)
      htu
    intro job hjob
    exact le_of_lt
      (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
        meanService i z t u hgood job hjob)
  · exact hresponse

/-- Enlarging a nonnegative selected/Palm future horizon only prepends newly
completed jobs to its literal completion ledger. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ht : 0 ≤ t) (htu : t ≤ u) :
    nonpreemptivePriorityCompletionLedgerExtension
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
    meanService i z t u hgood ht htu, runNonpreemptivePriorityArrivalTrace_append]
  apply nonpreemptivePriorityCompletionLedgerExtension_advance_run_from_cutoff
    (runNonpreemptivePriorityArrivalTrace
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t))
    t u
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z t u)
    htu
  intro job hjob
  exact le_of_lt
    (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
      meanService i z t u hgood job hjob)

/-- On a nonexplosive selected-arrival path, the coalesced pre-arrival state
is clocked at the Palm origin. -/
theorem stationaryPriorityClassTaggedRemotePastState_currentTime_eq_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    (stationaryPriorityClassTaggedRemotePastState meanService i z).currentTime = 0 := by
  classical
  by_cases hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff
  · rw [stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService i z hcutoff]
    exact canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
      meanService i z (-hcutoff.choose) 0
      (neg_nonpos.mpr hcutoff.choose_spec.1) hgood
  · simp [stationaryPriorityClassTaggedRemotePastState, hcutoff,
      emptyNonpreemptivePriorityWorkState]

/-- The admitted selected customer starts from the same Palm-origin clock. -/
theorem stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    (stationaryPriorityClassTaggedArrivalState meanService i z).currentTime = 0 := by
  rw [stationaryPriorityClassTaggedArrivalState,
    admitNonpreemptivePriorityJob_currentTime]
  exact stationaryPriorityClassTaggedRemotePastState_currentTime_eq_zero
    meanService i z hgood

/-- The finite selected post-arrival execution is clocked at its stated
physical horizon whenever that horizon lies after the Palm origin. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).currentTime = t := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  apply advanceNonpreemptivePriorityWorkState_currentTime_eq_target
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood]
      exact ht
    · intro job hjob
      exact arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z t hgood job hjob
  · exact le_rfl

/-- The completion ledger at a finite post-tag horizon is unchanged if all
arrivals exactly at that horizon are omitted from the replay. -/
theorem completed_stationaryPriorityClassTaggedFinitePostArrivalState_eq_beforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed =
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (stationaryPriorityClassTaggedArrivalState meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z t))) t
        (runNonpreemptivePriorityArrivalTrace
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
            meanService i z t))).completed := by
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z t
  have hclock : initial.currentTime ≤ t := by
    rw [show initial.currentTime = 0 by
      exact stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero
        meanService i z hgood]
    exact ht
  have htail : ∀ job ∈ tail, job.arrivalTime = t := by
    intro job hjob
    exact arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
      meanService i z t hgood job (by simpa [tail] using hjob)
  have hfrontClock :
      (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ t := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · exact hclock
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z t job (by simpa [front] using hjob)).le
  have hsplit := canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
    meanService i z t hgood
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  rw [hsplit]
  simpa [initial, front, tail] using
    (completed_advance_run_append_of_all_arrivalTime_eq_target initial front tail t hfrontClock htail)

/-- The finite selected-customer completion observation is therefore
determined by arrivals strictly before its queried horizon. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eq_beforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t =
      nonpreemptivePriorityRecordedCompletionTime
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace
              (stationaryPriorityClassTaggedArrivalState meanService i z)
              (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
                meanService i z t))) t
          (runNonpreemptivePriorityArrivalTrace
            (stationaryPriorityClassTaggedArrivalState meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z t)))
        (Sigma.mk i 0) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalResponseTime
  apply nonpreemptivePriorityRecordedCompletionTime_congr_completed
  exact completed_stationaryPriorityClassTaggedFinitePostArrivalState_eq_beforeHorizon
    meanService i z t ht hgood

/-- Total unfinished work immediately after the selected customer is admitted. -/
noncomputable def stationaryPriorityClassTaggedArrivalTotalWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : ℝ :=
  stationaryPriorityClassTaggedRemotePastResidualWork meanService i z +
    stationaryPriorityClassTaggedWorkRequirement meanService i z

/-- Admission adds precisely the selected customer's marked service work to
the coalesced pre-arrival workload. -/
theorem totalResidualWork_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedArrivalState meanService i z) =
      stationaryPriorityClassTaggedArrivalTotalWork meanService i z := by
  rw [stationaryPriorityClassTaggedArrivalState,
    totalNonpreemptivePriorityResidualWork_admit,
    stationaryPriorityClassTaggedJob_serviceWork]
  rfl

/-- The selected service-work observable is Borel on the full selected-arrival
carrier. -/
theorem measurable_stationaryPriorityClassTaggedWorkRequirement
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (stationaryPriorityClassTaggedWorkRequirement meanService i) := by
  convert measurable_stationaryPriorityClassTaggedWorkRequirementAt meanService i i 0 using 1
  funext z
  exact stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate meanService i z

/-- Every sufficiently remote canonical finite trace has the same aggregate
unfinished work as the causal selected/Palm remote-past state. -/
theorem ae_exists_canonicalStationaryPriorityClassTaggedFiniteWindowState_remotePastResidualWork_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        totalNonpreemptivePriorityResidualWork
          (canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i z (-older) 0) =
          stationaryPriorityClassTaggedRemotePastResidualWork meanService i z := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonneg, hcoalesces⟩
  refine ⟨cutoff, hnonneg, ?_⟩
  intro older holder
  exact totalNonpreemptivePriorityResidualWork_eq_of_liveEquivalent
    (hcoalesces older holder)

/-- Natural-horizon canonical selected/Palm workloads eventually equal the
causal remote-past workload almost surely. -/
theorem ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowState_remotePastResidualWork_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        totalNonpreemptivePriorityResidualWork
          (canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i z (-(horizon : ℝ)) 0) =
          stationaryPriorityClassTaggedRemotePastResidualWork meanService i z := by
  filter_upwards [
    ae_exists_canonicalStationaryPriorityClassTaggedFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  exact hcoalesces (horizon : ℝ) (hceil.trans hcast)

/-- The causal selected/Palm remote-past workload is almost-everywhere
measurable.  Its finite approximants are literal canonical traces, so no
measurable queue-state selector is assumed. -/
theorem aemeasurable_stationaryPriorityClassTaggedRemotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedRemotePastResidualWork meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  refine Probability.aemeasurable_response_of_ae_eventually_eq
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
    (fun horizon z => canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
      meanService i z (-(horizon : ℝ)) 0)
    (stationaryPriorityClassTaggedRemotePastResidualWork meanService i)
    (fun horizon =>
      measurable_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService i (-(horizon : ℝ)) 0) ?_
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hpositive hgood hcoalesces
  filter_upwards [hcoalesces] with horizon hhorizon
  have hfinite : totalNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-(horizon : ℝ)) 0) =
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService i z (-(horizon : ℝ)) 0 := by
    simpa [canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork] using
      totalResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
        meanService i z (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon)) hgood (by
            intro job hjob
            rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
              meanService i z (-(horizon : ℝ)) 0 job).mp hjob with
                ⟨j, k, _, hcoordinate⟩
            subst job
            exact hpositive j k)
  exact hfinite.symm.trans hhorizon

/-- The total workload immediately after selected-customer admission is
almost-everywhere measurable under the concrete selected Palm law. -/
theorem aemeasurable_stationaryPriorityClassTaggedArrivalTotalWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedArrivalTotalWork meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  exact (aemeasurable_stationaryPriorityClassTaggedRemotePastResidualWork
    arrivalRate meanService harrivalRate hmeanService hstable i).add
      (measurable_stationaryPriorityClassTaggedWorkRequirement meanService i).aemeasurable

/-- Strictly positive jobs in a finite selected/Palm window leave only
strictly positive residual jobs in the resulting finite priority state. -/
theorem positiveNonpreemptivePriorityResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ)
    (hjobs : ∀ job ∈ canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z a b, 0 < job.serviceWork) :
    positiveNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b) := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · constructor
    · intro active hactive
      simp [emptyNonpreemptivePriorityWorkState] at hactive
    · intro j job hmember
      simp [emptyNonpreemptivePriorityWorkState] at hmember
  · exact hjobs

/-- Positive service marks make every post-admission causal selected state a
strictly positive-residual priority state.  The fallback empty remote past is
handled explicitly, so this pathwise fact does not assume stability. -/
theorem positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedArrivalState meanService i z) := by
  have htag : 0 < (stationaryPriorityClassTaggedJob meanService i z).serviceWork := by
    rw [stationaryPriorityClassTaggedJob_serviceWork]
    simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hpositive i 0
  unfold stationaryPriorityClassTaggedArrivalState
  by_cases hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff
  · apply positiveNonpreemptivePriorityResidualWork_admit _ _ _ htag
    rw [stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService i z hcutoff]
    apply positiveNonpreemptivePriorityResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z (-hcutoff.choose) 0 job).mp hjob with ⟨j, k, _, hjob⟩
    subst job
    exact hpositive j k
  · apply positiveNonpreemptivePriorityResidualWork_admit _ _ _ htag
    rw [show stationaryPriorityClassTaggedRemotePastState meanService i z =
        emptyNonpreemptivePriorityWorkState
          (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) 0 by
        simp [stationaryPriorityClassTaggedRemotePastState, hcutoff]]
    constructor
    · intro active hactive
      simp [clearNonpreemptivePriorityCompletionLedger,
        emptyNonpreemptivePriorityWorkState] at hactive
    · intro j job hmember
      simp [clearNonpreemptivePriorityCompletionLedger,
        emptyNonpreemptivePriorityWorkState] at hmember

/-- At the Palm epoch, the selected customer's own service requirement is a
lower bound on any later completion record.  The reset causal state is at
time zero and contains no old copy of the selected customer. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityTaggedCompletionLowerBound 0
      (stationaryPriorityClassTaggedJob meanService i z)
      (stationaryPriorityClassTaggedArrivalState meanService i z) := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hremoteTime : remote.currentTime = 0 := by
    simpa [remote] using stationaryPriorityClassTaggedRemotePastState_currentTime_eq_zero
      meanService i z hgood
  have hclearedTime : (0 : ℝ) ≤ cleared.currentTime := by
    rw [show cleared.currentTime = remote.currentTime by
      simp [cleared, clearNonpreemptivePriorityCompletionLedger], hremoteTime]
  have hremoteFresh : ¬ nonpreemptivePriorityWorkStateContainsJob remote tag := by
    simpa [remote, tag] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
        meanService i z hgood
  have hclearedFresh : ¬ nonpreemptivePriorityWorkStateContainsJob cleared tag := by
    intro hcontains
    apply hremoteFresh
    rcases hcontains with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  change nonpreemptivePriorityTaggedCompletionLowerBound 0 tag
    (admitNonpreemptivePriorityJob cleared tag)
  exact nonpreemptivePriorityTaggedCompletionLowerBound_admit_self_of_fresh
    0 tag cleared hclearedTime hclearedFresh

/-- A finite literal continuation of the Palm-tagged priority state preserves
the selected customer's completion lower bound.  Positive service marks keep
all residual-work hypotheses valid, and the right-closed future ledger
contains no second copy of the selected job. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    nonpreemptivePriorityTaggedCompletionLowerBound 0
      (stationaryPriorityClassTaggedJob meanService i z)
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hinitialBound : nonpreemptivePriorityTaggedCompletionLowerBound 0 tag initial := by
    simpa [initial, tag] using
      nonpreemptivePriorityTaggedCompletionLowerBound_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood
  have hinitialWork : nonnegativeNonpreemptivePriorityResidualWork initial := by
    simpa [initial] using
      (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
        meanService i z hpositive).nonnegative
  have hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork := by
    intro job hmember
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [jobs] using hmember) with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hjobsDistinct : ∀ job ∈ jobs, job ≠ tag := by
    intro job hmember htag
    subst job
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood (by simpa [jobs] using hmember)
  have hafterBound : nonpreemptivePriorityTaggedCompletionLowerBound 0 tag afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityTaggedCompletionLowerBound_run
      initial jobs 0 tag hinitialBound hinitialWork hjobsWork hjobsDistinct
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      initial jobs hinitialWork hjobsWork
  simpa [initial, jobs, afterArrivals, tag] using
    nonpreemptivePriorityTaggedCompletionLowerBound_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) 0 t tag afterArrivals
      hafterBound hafterWork

/-- A job represented in the post-admission Palm state with the selected
stream identifier is the selected job itself.  Clearing preserves the remote
state's identifier exclusion, while the admission transition adds only the
tag. -/
theorem eq_stationaryPriorityClassTaggedJob_of_contains_arrivalState_of_identifier_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedArrivalState meanService i z) job)
    (hidentifier : job.identifier = (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n)) :
    job = stationaryPriorityClassTaggedJob meanService i z := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let tag := stationaryPriorityClassTaggedJob meanService i z
  change nonpreemptivePriorityWorkStateContainsJob
    (admitNonpreemptivePriorityJob cleared tag) job at hcontains
  rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse cleared tag job hcontains with
      hcleared | htag
  · have hremote : nonpreemptivePriorityWorkStateContainsJob remote job := by
      rcases hcleared with hactive | hwaiting | hcompleted
      · exact Or.inl (by
          simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
      · exact Or.inr (Or.inl (by
          simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
      · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
    exact (identifier_ne_selected_stationaryPriorityClassTaggedRemotePastState_of_contains
      meanService i z job hgood (by simpa [remote] using hremote) hidentifier).elim
  · simpa [tag] using htag

/-- Throughout a finite right-closed post-tag replay, the selected stream
identifier still denotes the selected job.  The incoming ledger has no copy
of that label, and the initial causal state has the preceding uniqueness
property. -/
theorem eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) job)
    (hidentifier : job.identifier = (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n)) :
    job = stationaryPriorityClassTaggedJob meanService i z := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState at hcontains
  dsimp only at hcontains
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hafter : nonpreemptivePriorityWorkStateContainsJob afterArrivals job := by
    exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ t _ _
      (by simpa [afterArrivals] using hcontains)
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse initial jobs job hafter with
      hinitial | hjobs
  · exact eq_stationaryPriorityClassTaggedJob_of_contains_arrivalState_of_identifier_eq
      meanService i z job hgood (by simpa [initial] using hinitial) hidentifier
  · have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
      rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
        meanService i z t job).mp (by simpa [jobs] using hjobs) with ⟨j, k, _, hjob⟩
      subst job
      cases hidentifier
      rfl
    apply False.elim
    apply stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood
    rwa [← htag]

/-- A successful finite selected-response lookup cannot precede the selected
customer's own service requirement.  The lookup's stream label identifies the
unique selected job in the canonical finite replay, so the tagged completion
ledger lower bound applies to its recorded timestamp. -/
theorem stationaryPriorityClassTaggedWorkRequirement_le_finitePostArrivalResponseTime_of_eq_some
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t =
      some completedAt) :
    stationaryPriorityClassTaggedWorkRequirement meanService i z ≤ completedAt := by
  rcases exists_completed_of_nonpreemptivePriorityRecordedCompletionTime_eq_some
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
    (Sigma.mk i 0) completedAt (by
      simpa [stationaryPriorityClassTaggedFinitePostArrivalResponseTime] using hresponse) with
      ⟨job, hidentifier, hcompleted⟩
  have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
    exact eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
      meanService i z t job hgood (Or.inr (Or.inr ⟨completedAt, hcompleted⟩)) hidentifier
  subst job
  have hbound :=
    nonpreemptivePriorityTaggedCompletionLowerBound_stationaryPriorityClassTaggedFinitePostArrivalState
      meanService i z t hgood hpositive
  have htime := hbound.2.1 completedAt hcompleted
  simpa [stationaryPriorityClassTaggedJob_serviceWork] using htime

/-- The tagged observation clears all pre-origin completion records before
the selected customer is admitted, so its arrival state has no completion
records at all. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (stationaryPriorityClassTaggedArrivalState meanService i z) := by
  unfold stationaryPriorityClassTaggedArrivalState
  apply nonpreemptivePriorityCompletionTimesLeCurrentTime_admit
  intro job completedAt hcompleted
  simp [clearNonpreemptivePriorityCompletionLedger] at hcompleted

/-- The fresh tagged observation begins with an empty completion ledger.
Consequently, every completion subsequently recorded by a finite positive-work
continuation has a timestamp no later than that continuation's queue clock. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
  have harrivalWork : nonnegativeNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedArrivalState meanService i z) :=
    (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive).nonnegative
  have harrivalTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime
      (stationaryPriorityClassTaggedArrivalState meanService i z) := by
    exact nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
      meanService i z
  have hfutureWork : ∀ job ∈
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t,
      0 ≤ job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp hjob with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
      harrivalWork hfutureWork
  have hafterTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_run
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
      harrivalWork harrivalTimes hfutureWork
  simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals hafterWork hafterTimes

/-- A successful finite selected-response observation is recorded no later
than the physical horizon at which it is queried.  This is a direct ledger
fact, and is the finite-horizon ingredient in the later Palm tail bound. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_horizon_of_eq_some
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (ht : 0 ≤ t)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t =
      some completedAt) :
    completedAt ≤ t := by
  rcases exists_completed_of_nonpreemptivePriorityRecordedCompletionTime_eq_some
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
    (Sigma.mk i 0) completedAt (by
      simpa [stationaryPriorityClassTaggedFinitePostArrivalResponseTime] using hresponse) with
      ⟨job, _, hcompleted⟩
  have htime := nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedFinitePostArrivalState
    meanService i z t hpositive job completedAt hcompleted
  rw [stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
    meanService i z t ht hgood] at htime
  exact htime

/-- Completion records of a finite selected/Palm continuation are stored in
reverse chronological order.  The observation begins with a cleared ledger;
finite service evolution prepends each later record at the then-current clock. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    nonpreemptivePriorityCompletionLedgerChronological
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hinitialWork : nonnegativeNonpreemptivePriorityResidualWork initial := by
    simpa [initial] using
      (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
        meanService i z hpositive).nonnegative
  have hinitialTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial := by
    simpa [initial] using
      nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have hinitialChronological : nonpreemptivePriorityCompletionLedgerChronological initial := by
    unfold initial stationaryPriorityClassTaggedArrivalState
    apply nonpreemptivePriorityCompletionLedgerChronological_admit
    exact nonpreemptivePriorityCompletionLedgerChronological_clear
      (stationaryPriorityClassTaggedRemotePastState meanService i z)
  have hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork := by
    intro job hmember
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [jobs] using hmember) with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      initial jobs hinitialWork hjobsWork
  have hafterTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_run
      initial jobs hinitialWork hinitialTimes hjobsWork
  have hafterChronological : nonpreemptivePriorityCompletionLedgerChronological afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionLedgerChronological_run
      initial jobs hinitialWork hinitialTimes hinitialChronological hjobsWork
  simpa [initial, jobs, afterArrivals] using
    nonpreemptivePriorityCompletionLedgerChronological_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals hafterWork
      hafterTimes hafterChronological

/-- A finite selected-response lookup is the earliest completion record with
the selected stream label. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_of_eq_some
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t completedAt otherCompletedAt : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t =
      some completedAt)
    (hidentifier : job.identifier = (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n))
    (hcompleted : (job, otherCompletedAt) ∈
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed) :
    completedAt ≤ otherCompletedAt := by
  apply nonpreemptivePriorityRecordedCompletionTime_le_of_eq_some
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
    (Sigma.mk i 0) completedAt
  · exact nonpreemptivePriorityCompletionLedgerChronological_stationaryPriorityClassTaggedFinitePostArrivalState
      meanService i z t hpositive
  · simpa [stationaryPriorityClassTaggedFinitePostArrivalResponseTime] using hresponse
  · exact hidentifier
  · exact hcompleted

/-- Once the selected finite response has been observed, no selected-job
completion record can be strictly earlier than that response timestamp. -/
theorem not_stationaryPriorityClassTaggedFinitePostArrivalCompleted_lt_responseTime_of_eq_some
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t completedAt otherCompletedAt : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t =
      some completedAt)
    (hcompleted : (stationaryPriorityClassTaggedJob meanService i z, otherCompletedAt) ∈
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed) :
    ¬ otherCompletedAt < completedAt := by
  exact not_lt_of_ge
    (stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_of_eq_some
      meanService i z t completedAt otherCompletedAt
      (stationaryPriorityClassTaggedJob meanService i z) hpositive hresponse rfl hcompleted)

/-- Strictly before a later observed selected response, the finite arrival
ledger itself contains no completion record for the selected job.  This is
the record-level form needed by finite-trace busy-prefix accounting: a record
created during the ledger would persist through terminal service and every
later continuation. -/
theorem not_exists_stationaryPriorityClassTaggedCompleted_in_futureArrivalTrace_of_lt_responseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hslt : s < completedAt)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    ¬ ∃ recordedAt,
      (stationaryPriorityClassTaggedJob meanService i z, recordedAt) ∈
        (runNonpreemptivePriorityArrivalTrace
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s)).completed := by
  rintro ⟨recordedAt, hrecorded⟩
  have hrecordedState :
      (stationaryPriorityClassTaggedJob meanService i z, recordedAt) ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s).completed := by
    unfold stationaryPriorityClassTaggedFinitePostArrivalState
    dsimp only
    exact mem_completed_advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s)))
      s
      (runNonpreemptivePriorityArrivalTrace
        (stationaryPriorityClassTaggedArrivalState meanService i z)
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s))
      (stationaryPriorityClassTaggedJob meanService i z) recordedAt hrecorded
  have htime : recordedAt ≤ s := by
    have htime' :=
      nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hpositive
        (stationaryPriorityClassTaggedJob meanService i z) recordedAt hrecordedState
    rw [stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
      meanService i z s hs hgood] at htime'
    exact htime'
  have hextends :=
    nonpreemptivePriorityCompletionLedgerExtension_stationaryPriorityClassTaggedFinitePostArrivalState
      meanService i z s u hgood hs hsu
  rcases hextends with ⟨newlyCompleted, hledger⟩
  have hrecordedLater : (stationaryPriorityClassTaggedJob meanService i z, recordedAt) ∈
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u).completed := by
    rw [hledger]
    exact List.mem_append_right _ hrecordedState
  have hfirst : completedAt ≤ recordedAt := by
    exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_of_eq_some
      meanService i z u completedAt recordedAt
      (stationaryPriorityClassTaggedJob meanService i z) hpositive hresponse rfl hrecordedLater
  linarith

/-- Strictly before a later observed selected response, the selected job is
still live in the finite replay.  If it had already entered the completion
ledger, ledger extension and chronological first-completion lookup would put
that record both before and no earlier than the observed response. -/
theorem stationaryPriorityClassTaggedJob_live_in_finitePostArrivalState_of_lt_responseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hslt : s < completedAt)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    (∃ residual,
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual)) ∨
      ∃ priority,
        stationaryPriorityClassTaggedJob meanService i z ∈
          (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s).waiting priority := by
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let state := stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s
  have hcontains : nonpreemptivePriorityWorkStateContainsJob state tag := by
    unfold state stationaryPriorityClassTaggedFinitePostArrivalState
    dsimp only
    apply nonpreemptivePriorityWorkStateContainsJob_advance
    apply nonpreemptivePriorityWorkStateContainsJob_run
    unfold stationaryPriorityClassTaggedArrivalState
    exact nonpreemptivePriorityWorkStateContainsJob_admit_self _ _
  have hnotCompleted : ¬ ∃ recordedAt, (tag, recordedAt) ∈ state.completed := by
    rintro ⟨recordedAt, hrecorded⟩
    have htime : recordedAt ≤ s := by
      have htime' := nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hpositive tag recordedAt (by simpa [state] using hrecorded)
      rw [stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
        meanService i z s hs hgood] at htime'
      exact htime'
    have hextends :=
      nonpreemptivePriorityCompletionLedgerExtension_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s u hgood hs hsu
    rcases hextends with ⟨newlyCompleted, hledger⟩
    have hrecordedLater : (tag, recordedAt) ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u).completed := by
      rw [hledger]
      exact List.mem_append_right _ (by simpa [state] using hrecorded)
    have hfirst : completedAt ≤ recordedAt := by
      exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_of_eq_some
        meanService i z u completedAt recordedAt tag hpositive hresponse rfl
        hrecordedLater
    linarith
  rcases hcontains with hactive | hwaiting | hcompleted
  · exact Or.inl hactive
  · exact Or.inr hwaiting
  · exact (hnotCompleted hcompleted).elim

/-- An old same-class FIFO customer completes no later than the selected Palm
customer in every finite literal post-arrival continuation.  This is a
pathwise queue-discipline fact: it uses literal job uniqueness and physical
completion timestamps, not any stationary expectation identity. -/
theorem nonpreemptivePriorityFifoCompletionOrder_stationaryPriorityClassTaggedFinitePostArrivalState_of_mem
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (earlier : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hpriority : earlier.priority = i)
    (hwaiting : earlier ∈
      (stationaryPriorityClassTaggedRemotePastState meanService i z).waiting i) :
    nonpreemptivePriorityFifoCompletionOrder
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      earlier (stationaryPriorityClassTaggedJob meanService i z) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let arrivalState := stationaryPriorityClassTaggedArrivalState meanService i z
  let futureJobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace arrivalState futureJobs
  have hdistinct : earlier ≠ tag := by
    intro heq
    apply not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
      meanService i z hgood
    right
    left
    refine ⟨i, ?_⟩
    simpa [tag, heq] using hwaiting
  have harrivalWork : nonnegativeNonpreemptivePriorityResidualWork arrivalState := by
    exact (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive).nonnegative
  have harrivalMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity arrivalState tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity arrivalState tag = 1 by
      simpa [arrivalState, tag] using
        nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
          meanService i z hgood]
  have harrivalTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime arrivalState := by
    simpa [arrivalState] using
      nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have harrivalDisposition :
      nonpreemptivePriorityFifoPrecedesDisposition arrivalState earlier tag := by
    simpa [arrivalState, tag] using
      nonpreemptivePriorityFifoPrecedesDisposition_stationaryPriorityClassTaggedArrivalState_of_mem
        meanService i z earlier hpriority hwaiting
  have harrivalOrder : nonpreemptivePriorityFifoCompletionOrder arrivalState earlier tag := by
    intro tagTime htag
    rw [show arrivalState.completed = [] by
      simpa [arrivalState] using completed_stationaryPriorityClassTaggedArrivalState
        meanService i z] at htag
    simp at htag
  have hfutureWork : ∀ job ∈ futureJobs, 0 ≤ job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [futureJobs] using hjob) with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hfutureDistinct : ∀ job ∈ futureJobs, job ≠ tag := by
    intro job hjob htag
    subst job
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood (by simpa [futureJobs, tag] using hjob)
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      arrivalState futureJobs harrivalWork hfutureWork
  have hafterMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag =
        nonpreemptivePriorityWorkStateJobMultiplicity arrivalState tag by
      dsimp [afterArrivals]
      exact nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
        arrivalState futureJobs tag hfutureDistinct]
    exact harrivalMultiplicity
  have hafterTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_run
      arrivalState futureJobs harrivalWork harrivalTimes hfutureWork
  have hafterDisposition :
      nonpreemptivePriorityFifoPrecedesDisposition afterArrivals earlier tag := by
    simpa [afterArrivals] using nonpreemptivePriorityFifoPrecedesDisposition_run
      arrivalState futureJobs earlier tag harrivalDisposition
  have hafterOrder : nonpreemptivePriorityFifoCompletionOrder afterArrivals earlier tag := by
    simpa [afterArrivals] using nonpreemptivePriorityFifoCompletionOrder_run
      arrivalState futureJobs earlier tag hdistinct harrivalWork harrivalMultiplicity
      harrivalTimes harrivalDisposition harrivalOrder hfutureWork hfutureDistinct
  simpa [tag, arrivalState, futureJobs, afterArrivals] using
    nonpreemptivePriorityFifoCompletionOrder_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals earlier tag
      hdistinct hafterWork hafterMultiplicity hafterTimes hafterDisposition hafterOrder

/-- An old strictly higher-priority customer waiting at the Palm arrival
completes no later than the selected customer in every finite literal
continuation.  The active job's residual is accounted for separately; this
theorem identifies the already-queued strictly higher-priority contribution. -/
theorem nonpreemptivePriorityStrictCompletionOrder_stationaryPriorityClassTaggedFinitePostArrivalState_of_mem
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (earlier : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hpriority : earlier.priority < i)
    (hwaiting : earlier ∈
      (stationaryPriorityClassTaggedRemotePastState meanService i z).waiting earlier.priority) :
    nonpreemptivePriorityStrictCompletionOrder
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      earlier (stationaryPriorityClassTaggedJob meanService i z) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let arrivalState := stationaryPriorityClassTaggedArrivalState meanService i z
  let futureJobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace arrivalState futureJobs
  have hremoteClass : hasClassConsistentWaiting remote := by
    unfold remote stationaryPriorityClassTaggedRemotePastState
    split_ifs with hcutoff
    · exact hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0
    · exact hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState 0
  have hclearedClass : hasClassConsistentWaiting cleared := by
    intro j job hmember
    exact hremoteClass j job (by
      simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hmember)
  have harrivalClass : hasClassConsistentWaiting arrivalState := by
    change hasClassConsistentWaiting (admitNonpreemptivePriorityJob cleared tag)
    exact hasClassConsistentWaiting_admitNonpreemptivePriorityJob cleared tag hclearedClass
  have harrivalWork : nonnegativeNonpreemptivePriorityResidualWork arrivalState := by
    exact (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive).nonnegative
  have harrivalTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime arrivalState := by
    simpa [arrivalState] using
      nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have hclearedEarlier : earlier ∈ cleared.waiting earlier.priority := by
    simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting
  have hclearedNotTag : ¬ nonpreemptivePriorityWorkStateContainsJob cleared tag := by
    intro hcontains
    apply not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
      meanService i z hgood
    rcases hcontains with hactive | hwaiting' | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting'))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  have hclearedNotActiveTag : ∀ residual, cleared.active ≠ some (tag, residual) := by
    intro residual hactive
    exact hclearedNotTag (Or.inl ⟨residual, hactive⟩)
  have htagPriority : earlier.priority < tag.priority := by
    simpa [tag, stationaryPriorityClassTaggedJob] using hpriority
  have hdistinct : earlier ≠ tag := by
    intro heq
    have : earlier.priority = tag.priority := congrArg NonpreemptivePriorityJob.priority heq
    exact (not_lt_of_ge (by simpa [tag, stationaryPriorityClassTaggedJob] using this.ge)) htagPriority
  have hclearedDisposition :
      nonpreemptivePriorityStrictPrecedesDisposition cleared earlier tag := by
    apply nonpreemptivePriorityStrictPrecedesDisposition_of_contains
      cleared earlier tag hclearedClass
    · exact Or.inr (Or.inl ⟨earlier.priority, hclearedEarlier⟩)
    · exact hclearedNotActiveTag
  have harrivalDisposition :
      nonpreemptivePriorityStrictPrecedesDisposition arrivalState earlier tag := by
    simpa [arrivalState] using nonpreemptivePriorityStrictPrecedesDisposition_admit
      cleared earlier tag tag hclearedClass htagPriority hclearedDisposition
  have harrivalMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity arrivalState tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity arrivalState tag = 1 by
      simpa [arrivalState, tag] using
        nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
          meanService i z hgood]
  have harrivalOrder : nonpreemptivePriorityStrictCompletionOrder arrivalState earlier tag := by
    intro tagTime htag
    rw [show arrivalState.completed = [] by
      simpa [arrivalState] using completed_stationaryPriorityClassTaggedArrivalState
        meanService i z] at htag
    simp at htag
  have hfutureWork : ∀ job ∈ futureJobs, 0 ≤ job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [futureJobs] using hjob) with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hfutureDistinct : ∀ job ∈ futureJobs, job ≠ tag := by
    intro job hjob htag
    subst job
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood (by simpa [futureJobs, tag] using hjob)
  have hafterClass : hasClassConsistentWaiting afterArrivals := by
    simpa [afterArrivals] using hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
      arrivalState futureJobs harrivalClass
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      arrivalState futureJobs harrivalWork hfutureWork
  have hafterMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag =
        nonpreemptivePriorityWorkStateJobMultiplicity arrivalState tag by
      dsimp [afterArrivals]
      exact nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
        arrivalState futureJobs tag hfutureDistinct]
    exact harrivalMultiplicity
  have hafterTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_run
      arrivalState futureJobs harrivalWork harrivalTimes hfutureWork
  have hafterDisposition :
      nonpreemptivePriorityStrictPrecedesDisposition afterArrivals earlier tag := by
    simpa [afterArrivals] using nonpreemptivePriorityStrictPrecedesDisposition_run
      arrivalState futureJobs earlier tag harrivalClass htagPriority harrivalDisposition
  have hafterOrder : nonpreemptivePriorityStrictCompletionOrder afterArrivals earlier tag := by
    simpa [afterArrivals] using nonpreemptivePriorityStrictCompletionOrder_run
      arrivalState futureJobs earlier tag harrivalClass htagPriority hdistinct harrivalWork
      harrivalMultiplicity harrivalTimes harrivalDisposition harrivalOrder hfutureWork hfutureDistinct
  simpa [tag, remote, cleared, arrivalState, futureJobs, afterArrivals] using
    nonpreemptivePriorityStrictCompletionOrder_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals earlier tag
      hafterClass htagPriority hdistinct hafterWork hafterMultiplicity hafterTimes
      hafterDisposition hafterOrder

/-- A same-class customer arriving strictly after the Palm tag cannot complete
before that tag in any finite literal continuation.  Together with the
old-customer theorem above, this cleanly separates pre-existing same-class
work from post-tag same-class input in the pathwise wait decomposition. -/
theorem nonpreemptivePriorityFifoCompletionOrder_stationaryPriorityClassTaggedFinitePostArrivalState_tag_of_mem_future
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (later : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hpriority : later.priority = i)
    (hlater : later ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) :
    nonpreemptivePriorityFifoCompletionOrder
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) later := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let arrivalState := stationaryPriorityClassTaggedArrivalState meanService i z
  let futureJobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace arrivalState futureJobs
  have hfuturePositive : 0 < later.arrivalTime := by
    exact arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t hgood later hlater
  have hremoteClass : hasClassConsistentWaiting remote := by
    unfold remote stationaryPriorityClassTaggedRemotePastState
    split_ifs with hcutoff
    · exact hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0
    · exact hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState 0
  have hclearedClass : hasClassConsistentWaiting cleared := by
    intro j job hmember
    exact hremoteClass j job (by
      simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hmember)
  have harrivalClass : hasClassConsistentWaiting arrivalState := by
    change hasClassConsistentWaiting (admitNonpreemptivePriorityJob cleared tag)
    exact hasClassConsistentWaiting_admitNonpreemptivePriorityJob cleared tag hclearedClass
  have harrivalWork : nonnegativeNonpreemptivePriorityResidualWork arrivalState := by
    exact (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive).nonnegative
  have harrivalTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime arrivalState := by
    simpa [arrivalState] using
      nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have htagContains : nonpreemptivePriorityWorkStateContainsJob arrivalState tag := by
    change nonpreemptivePriorityWorkStateContainsJob
      (admitNonpreemptivePriorityJob cleared tag) tag
    exact nonpreemptivePriorityWorkStateContainsJob_admit_self cleared tag
  have hnotLater : ¬ nonpreemptivePriorityWorkStateContainsJob arrivalState later := by
    simpa [arrivalState] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedArrivalState_of_arrivalTime_pos
        meanService i z later hgood hfuturePositive
  have htagPriority : tag.priority = later.priority := by
    simpa [tag, stationaryPriorityClassTaggedJob] using hpriority.symm
  have hdistinct : tag ≠ later := by
    intro heq
    apply hnotLater
    simpa [heq] using htagContains
  have hfutureNodup : futureJobs.Nodup := by
    simpa [futureJobs] using
      nodup_canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  have hfutureWork : ∀ job ∈ futureJobs, 0 ≤ job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [futureJobs] using hjob) with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hfutureDistinctTag : ∀ job ∈ futureJobs, job ≠ tag := by
    intro job hjob hjobTag
    subst job
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood (by simpa [futureJobs, tag] using hjob)
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      arrivalState futureJobs harrivalWork hfutureWork
  have hafterTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_run
      arrivalState futureJobs harrivalWork harrivalTimes hfutureWork
  have hafterMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals later ≤ 1 := by
    have hzero : nonpreemptivePriorityWorkStateJobMultiplicity arrivalState later = 0 :=
      nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
        arrivalState later hnotLater
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals later =
        nonpreemptivePriorityWorkStateJobMultiplicity arrivalState later + 1 by
      dsimp [afterArrivals]
      exact nonpreemptivePriorityWorkStateJobMultiplicity_run_eq_add_one_of_nodup_mem
        arrivalState futureJobs later hfutureNodup (by simpa [futureJobs] using hlater), hzero]
  have hafterDisposition :
      nonpreemptivePriorityFifoPrecedesDisposition afterArrivals tag later := by
    simpa [afterArrivals] using
      nonpreemptivePriorityFifoPrecedesDisposition_run_of_mem
        arrivalState futureJobs tag later harrivalClass htagContains hfutureDistinctTag
        (by simpa [futureJobs] using hlater) htagPriority
  have hafterOrder : nonpreemptivePriorityFifoCompletionOrder afterArrivals tag later := by
    simpa [afterArrivals] using
      nonpreemptivePriorityFifoCompletionOrder_run_of_initial_contains
        arrivalState futureJobs tag later harrivalClass harrivalWork harrivalTimes htagContains hnotLater
        hfutureNodup (by simpa [futureJobs] using hlater) htagPriority hfutureWork
  simpa [tag, remote, cleared, arrivalState, futureJobs, afterArrivals] using
    nonpreemptivePriorityFifoCompletionOrder_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals tag later
      hdistinct hafterWork hafterMultiplicity hafterTimes hafterDisposition hafterOrder

/-- A strictly lower-priority customer arriving after the Palm tag cannot
complete before that tag in any finite literal continuation.  Unlike the
same-class FIFO fact, the argument uses the priority dispatch guard: a live
higher-priority tag is never bypassed when service next becomes available. -/
theorem nonpreemptivePriorityStrictCompletionOrder_stationaryPriorityClassTaggedFinitePostArrivalState_tag_of_mem_future
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (later : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hpriority : i < later.priority)
    (hlater : later ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) :
    nonpreemptivePriorityStrictCompletionOrder
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) later := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let arrivalState := stationaryPriorityClassTaggedArrivalState meanService i z
  let futureJobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace arrivalState futureJobs
  have hfuturePositive : 0 < later.arrivalTime := by
    exact arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t hgood later hlater
  have hremoteClass : hasClassConsistentWaiting remote := by
    unfold remote stationaryPriorityClassTaggedRemotePastState
    split_ifs with hcutoff
    · exact hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0
    · exact hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState 0
  have hclearedClass : hasClassConsistentWaiting cleared := by
    intro j job hmember
    exact hremoteClass j job (by
      simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hmember)
  have harrivalClass : hasClassConsistentWaiting arrivalState := by
    change hasClassConsistentWaiting (admitNonpreemptivePriorityJob cleared tag)
    exact hasClassConsistentWaiting_admitNonpreemptivePriorityJob cleared tag hclearedClass
  have harrivalWork : nonnegativeNonpreemptivePriorityResidualWork arrivalState := by
    exact (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive).nonnegative
  have harrivalTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime arrivalState := by
    simpa [arrivalState] using
      nonpreemptivePriorityCompletionTimesLeCurrentTime_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have htagContains : nonpreemptivePriorityWorkStateContainsJob arrivalState tag := by
    change nonpreemptivePriorityWorkStateContainsJob
      (admitNonpreemptivePriorityJob cleared tag) tag
    exact nonpreemptivePriorityWorkStateContainsJob_admit_self cleared tag
  have hnotLater : ¬ nonpreemptivePriorityWorkStateContainsJob arrivalState later := by
    simpa [arrivalState] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedArrivalState_of_arrivalTime_pos
        meanService i z later hgood hfuturePositive
  have htagPriority : tag.priority < later.priority := by
    simpa [tag, stationaryPriorityClassTaggedJob] using hpriority
  have hdistinct : tag ≠ later := by
    intro heq
    apply hnotLater
    simpa [heq] using htagContains
  have harrivalNotActive : ∀ residual, arrivalState.active ≠ some (later, residual) := by
    intro residual hactive
    exact hnotLater (Or.inl ⟨residual, hactive⟩)
  have harrivalDisposition :
      nonpreemptivePriorityStrictPrecedesDisposition arrivalState tag later := by
    exact nonpreemptivePriorityStrictPrecedesDisposition_of_contains
      arrivalState tag later harrivalClass htagContains harrivalNotActive
  have hfutureNodup : futureJobs.Nodup := by
    simpa [futureJobs] using
      nodup_canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  have hfutureWork : ∀ job ∈ futureJobs, 0 ≤ job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [futureJobs] using hjob) with ⟨j, k, _, hjob⟩
    subst job
    exact (hpositive j k).le
  have hafterClass : hasClassConsistentWaiting afterArrivals := by
    simpa [afterArrivals] using hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
      arrivalState futureJobs harrivalClass
  have hafterWork : nonnegativeNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using nonnegativeNonpreemptivePriorityResidualWork_run
      arrivalState futureJobs harrivalWork hfutureWork
  have hafterTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityCompletionTimesLeCurrentTime_run
      arrivalState futureJobs harrivalWork harrivalTimes hfutureWork
  have hafterMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals later ≤ 1 := by
    have hzero : nonpreemptivePriorityWorkStateJobMultiplicity arrivalState later = 0 :=
      nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
        arrivalState later hnotLater
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals later =
        nonpreemptivePriorityWorkStateJobMultiplicity arrivalState later + 1 by
      dsimp [afterArrivals]
      exact nonpreemptivePriorityWorkStateJobMultiplicity_run_eq_add_one_of_nodup_mem
        arrivalState futureJobs later hfutureNodup (by simpa [futureJobs] using hlater), hzero]
  have hafterDisposition :
      nonpreemptivePriorityStrictPrecedesDisposition afterArrivals tag later := by
    simpa [afterArrivals] using nonpreemptivePriorityStrictPrecedesDisposition_run
      arrivalState futureJobs tag later harrivalClass htagPriority harrivalDisposition
  have hafterOrder : nonpreemptivePriorityStrictCompletionOrder afterArrivals tag later := by
    simpa [afterArrivals] using
      nonpreemptivePriorityStrictCompletionOrder_run_of_initial_contains
        arrivalState futureJobs tag later harrivalClass harrivalWork harrivalTimes htagContains hnotLater
        hfutureNodup (by simpa [futureJobs] using hlater) htagPriority hfutureWork
  simpa [tag, remote, cleared, arrivalState, futureJobs, afterArrivals] using
    nonpreemptivePriorityStrictCompletionOrder_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals tag later
      hafterClass htagPriority hdistinct hafterWork hafterMultiplicity hafterTimes
      hafterDisposition hafterOrder

/-- Under the concrete positive exponential-mark input law, a selected
customer starts in a strictly positive-residual priority state almost surely. -/
theorem ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      positiveNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedArrivalState meanService i z) := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hpositive
  exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
    meanService i z hpositive

/-- The literal finite post-arrival queue has the scalar reflected-workload
value of its coalesced admission workload and right-closed future arrival
ledger. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_terminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork 0
        (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) t := by
  have htime : (stationaryPriorityClassTaggedArrivalState meanService i z).currentTime = 0 :=
    stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have htrace := totalNonpreemptivePriorityResidualWork_advance_run_eq_terminalResidualWork
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) t
    (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive)
    (nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
      meanService i z)
    (by rw [htime]; exact ht)
    (by
      intro job hjob
      rw [htime]
      exact (arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z t hgood job hjob).le)
    (pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t)
    (by
      intro job hjob
      exact arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z t hgood job hjob)
    (by
      intro job hjob
      rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
        meanService i z t job).mp hjob with ⟨j, k, _, hcoordinate⟩
      subst job
      exact hpositive j k)
  simpa [stationaryPriorityClassTaggedFinitePostArrivalState,
    stationaryPriorityClassTaggedArrivalTotalWork,
    totalResidualWork_stationaryPriorityClassTaggedArrivalState,
    htime] using htrace

/-- If the selected finite replay remains busy at every future admission and
at its terminal epoch, its aggregate residual work has the unreflected
work-conservation form.  This separates the deterministic no-idling
consequence of selected-job liveness from the probabilistic argument that
establishes the displayed positivity conditions. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_initial_add_futureServiceWork_sub_of_positive
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hterminal : 0 < totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t))
    (hprefix : ∀ (front suffix : List
      (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
      (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)),
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t =
        front ++ job :: suffix →
        0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork 0
          (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
          front job.arrivalTime) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) =
      stationaryPriorityClassTaggedArrivalTotalWork meanService i z +
        nonpreemptivePriorityArrivalTraceServiceWork
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) - t := by
  have hterminalTrace : 0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork 0
      (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) t := by
    rw [← totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_terminalResidualWork
      meanService i z t ht hgood hpositive]
    exact hterminal
  calc
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) =
        nonpreemptivePriorityArrivalTraceTerminalResidualWork 0
          (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) t :=
      totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_terminalResidualWork
        meanService i z t ht hgood hpositive
    _ = stationaryPriorityClassTaggedArrivalTotalWork meanService i z +
          nonpreemptivePriorityArrivalTraceServiceWork
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) - t :=
      by
        simpa using
          (nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_initial_add_serviceWork_sub_of_positive
            0 (stationaryPriorityClassTaggedArrivalTotalWork meanService i z) t
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
            hterminalTrace hprefix)

/-- A selected finite replay has unreflected aggregate work conservation when
the selected customer has not completed during its arrival ledger and the
terminal residual remains positive.  The first premise is a concrete
completion-ledger condition; a Palm-response argument can establish it
without inserting a separate busy-period assumption at every arrival. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_initial_add_futureServiceWork_sub_of_initialJob_not_completed
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hterminal : 0 < totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t))
    (hnotCompleted : ¬ ∃ completedAt,
      (stationaryPriorityClassTaggedJob meanService i z, completedAt) ∈
        (runNonpreemptivePriorityArrivalTrace
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)).completed) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) =
      stationaryPriorityClassTaggedArrivalTotalWork meanService i z +
        nonpreemptivePriorityArrivalTraceServiceWork
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) - t := by
  apply totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_initial_add_futureServiceWork_sub_of_positive
    meanService i z t ht hgood hpositive hterminal
  have htime : (stationaryPriorityClassTaggedArrivalState meanService i z).currentTime = 0 :=
    stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have hwork : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedArrivalState meanService i z) =
      stationaryPriorityClassTaggedArrivalTotalWork meanService i z :=
    totalResidualWork_stationaryPriorityClassTaggedArrivalState meanService i z
  intro front suffix job hsplit
  have hprefix :=
    nonpreemptivePriorityArrivalTraceTerminalResidualWork_pos_of_initialJob_not_completed
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z)
      (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
        meanService i z hpositive)
      (nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
        meanService i z)
      (by
        unfold stationaryPriorityClassTaggedArrivalState
        exact nonpreemptivePriorityWorkStateContainsJob_admit_self _ _)
      (by
        intro other hother
        rw [htime]
        exact (arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
          meanService i z t hgood other hother).le)
      (by
        intro other hother
        rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
          meanService i z t other).mp hother with ⟨j, k, _, hcoordinate⟩
        subst other
        exact hpositive j k)
      (pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z t)
      hnotCompleted front suffix job hsplit
  simpa only [htime, hwork] using hprefix

/-- A finite selected post-arrival execution is empty at its horizon whenever
the coalesced admission workload and every literal future suffix fit in the
available service intervals.  This is the deterministic record-low condition
that the selected-input negative-drift argument must supply. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_zero_of_all_suffixes_le
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hinitial : stationaryPriorityClassTaggedArrivalTotalWork meanService i z +
      nonpreemptivePriorityArrivalTraceServiceWork
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) ≤ t)
    (hsuffix : ∀ (front suffix : List
        (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
      (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)),
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t =
        front ++ job :: suffix →
      nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
        t - job.arrivalTime) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) = 0 := by
  rw [totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_terminalResidualWork
    meanService i z t ht hgood hpositive]
  exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_all_suffixes_le
    0 (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
    t (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t)
    (by simpa using hinitial) hsuffix

/-- The initial workload condition in the finite emptying lemma is exactly a
selected-input future-net inequality once the literal future ledger is
identified with its cumulative marked work. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_zero_of_netFuture_and_all_suffixes_le
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hnet : stationaryPriorityTaggedNetFutureInput meanService i z t ≤
      -stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
    (hsuffix : ∀ (front suffix : List
        (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
      (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)),
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t =
        front ++ job :: suffix →
      nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
        t - job.arrivalTime) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) = 0 := by
  apply totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_zero_of_all_suffixes_le
    meanService i z t ht hgood hpositive
  · rw [nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedFutureArrivalJobs]
    unfold stationaryPriorityTaggedNetFutureInput at hnet
    linarith
  · exact hsuffix

/-- Positive service marks preserve the strict residual-work invariant while
the selected post-admission queue is continued through any finite future
ledger. -/
theorem positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive
  · intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp hjob with ⟨j, k, _, hcoordinate⟩
    subst job
    exact hpositive j k

/-- The finite selected/Palm replay has strictly positive residual workload at
every nonnegative horizon strictly before an observed selected response.  The
selected job is still live there and all stored work marks are positive, so
the server cannot have an idle interval before that response. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_pos_of_lt_responseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hslt : s < completedAt)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    0 < totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) := by
  apply totalNonpreemptivePriorityResidualWork_pos_of_jobLive
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s)
    (stationaryPriorityClassTaggedJob meanService i z)
  · exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
      meanService i z s hpositive
  · exact stationaryPriorityClassTaggedJob_live_in_finitePostArrivalState_of_lt_responseTime
      meanService i z s u completedAt hgood hpositive hs hsu hslt hresponse

/-- Up to an observed selected response, the literal selected replay has
unreflected work conservation.  The selected job remains unfinished through
the whole finite arrival ledger, so the server has no idle reset before the
given horizon. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_initial_add_futureServiceWork_sub_of_lt_responseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hslt : s < completedAt)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) =
      stationaryPriorityClassTaggedArrivalTotalWork meanService i z +
        nonpreemptivePriorityArrivalTraceServiceWork
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s) - s := by
  apply totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_initial_add_futureServiceWork_sub_of_initialJob_not_completed
    meanService i z s hs hgood hpositive
  · exact totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_pos_of_lt_responseTime
      meanService i z s u completedAt hgood hpositive hs hsu hslt hresponse
  · exact not_exists_stationaryPriorityClassTaggedCompleted_in_futureArrivalTrace_of_lt_responseTime
      meanService i z s u completedAt hgood hpositive hs hsu hslt hresponse

/-- Before an observed selected completion, the final arrival-free part of
the finite replay has exact, unreflected service accounting.  The positive
tagged workload rules out an idle reset during that terminal interval. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_unreflectedTerminalResidualWork_of_lt_responseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hslt : s < completedAt)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) =
      nonpreemptivePriorityArrivalTraceResidualWork 0
        (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s) -
        (s - nonpreemptivePriorityArrivalTraceEndTime 0
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s)) := by
  have hterminal := totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_terminalResidualWork
    meanService i z s hs hgood hpositive
  have hstatePos := totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_pos_of_lt_responseTime
    meanService i z s u completedAt hgood hpositive hs hsu hslt hresponse
  rw [hterminal] at hstatePos ⊢
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork at hstatePos ⊢
  have hraw : 0 < nonpreemptivePriorityArrivalTraceResidualWork 0
      (stationaryPriorityClassTaggedArrivalTotalWork meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s) -
        (s - nonpreemptivePriorityArrivalTraceEndTime 0
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s)) := by
    by_contra hnot
    rw [max_eq_left (le_of_not_gt hnot)] at hstatePos
    linarith
  exact max_eq_right hraw.le

/-- Strict aggregate slack over a finite post-tag window supplies an actual
arrival-free completion prefix for the selected job.  Unlike terminal-emptying
arguments, this uses only total work: later arrivals may keep the queue busy
after the selected customer has already completed. -/
theorem exists_completedTime_stationaryPriorityClassTaggedArrivalPrefix_of_netFuture_lt
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hnet : stationaryPriorityTaggedNetFutureInput meanService i z t <
      -stationaryPriorityClassTaggedArrivalTotalWork meanService i z) :
    ∃ (front suffix : List
        (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
      (resetTime completedAt : ℝ),
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t =
        front ++ suffix ∧
        0 < resetTime ∧ resetTime ≤ t ∧
        (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
        (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
        totalNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace
                (stationaryPriorityClassTaggedArrivalState meanService i z) front))
            resetTime
            (runNonpreemptivePriorityArrivalTrace
              (stationaryPriorityClassTaggedArrivalState meanService i z) front)) = 0 ∧
        (stationaryPriorityClassTaggedJob meanService i z, completedAt) ∈
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace
                (stationaryPriorityClassTaggedArrivalState meanService i z) front))
            resetTime
            (runNonpreemptivePriorityArrivalTrace
              (stationaryPriorityClassTaggedArrivalState meanService i z) front)).completed := by
  let full := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  have hinitialPositive : positiveNonpreemptivePriorityResidualWork initial := by
    exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive
  have hinitialWork : nonpreemptivePriorityWorkConserving initial := by
    exact nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
      meanService i z
  have hinitialTime : initial.currentTime = 0 := by
    exact stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have hinitialNonneg : 0 ≤ totalNonpreemptivePriorityResidualWork initial := by
    exact totalNonpreemptivePriorityResidualWork_nonneg initial hinitialPositive.nonnegative
  have hstart : ∀ job ∈ full, initial.currentTime ≤ job.arrivalTime := by
    intro job hjob
    rw [hinitialTime]
    exact (arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t hgood job (by simpa [full] using hjob)).le
  have hsorted : full.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
    simpa [full] using
      pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z t
  have hend : ∀ job ∈ full, job.arrivalTime ≤ t := by
    intro job hjob
    exact arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t hgood job (by simpa [full] using hjob)
  have hfullPositive : ∀ job ∈ full, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp (by simpa [full] using hjob) with ⟨j, k, _, hcoordinate⟩
    subst job
    exact hpositive j k
  have hslack : totalNonpreemptivePriorityResidualWork initial +
      nonpreemptivePriorityArrivalTraceServiceWork full < t - initial.currentTime := by
    rw [totalResidualWork_stationaryPriorityClassTaggedArrivalState, hinitialTime]
    rw [show nonpreemptivePriorityArrivalTraceServiceWork full =
      stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t by
      simpa [full] using
        nonpreemptivePriorityArrivalTraceServiceWork_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
          meanService i z t]
    unfold stationaryPriorityTaggedNetFutureInput at hnet
    linarith
  rcases exists_nonpreemptivePriorityArrivalTrace_terminalReset_of_initial_add_serviceWork_lt
    initial.currentTime (totalNonpreemptivePriorityResidualWork initial) t full
    hinitialNonneg hstart hsorted hend hfullPositive hslack with
      ⟨front, suffix, resetTime, hsplit, hleft, hright, hfrontCut, hsuffix, hscalar⟩
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  let resetState := advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterFront) resetTime afterFront
  have hfrontStart : ∀ job ∈ front, initial.currentTime ≤ job.arrivalTime := by
    intro job hjob
    exact hstart job (by rw [hsplit]; exact List.mem_append_left _ hjob)
  have hfrontSorted : front.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
    rw [hsplit] at hsorted
    exact (List.pairwise_append.mp hsorted).1
  have hfrontPositive : ∀ job ∈ front, 0 < job.serviceWork := by
    intro job hjob
    exact hfullPositive job (by rw [hsplit]; exact List.mem_append_left _ hjob)
  have hresetPositive : positiveNonpreemptivePriorityResidualWork resetState := by
    dsimp [resetState]
    apply positiveNonpreemptivePriorityResidualWork_advance
    dsimp [afterFront]
    exact positiveNonpreemptivePriorityResidualWork_run initial front
      hinitialPositive hfrontPositive
  have hresetTotal : totalNonpreemptivePriorityResidualWork resetState = 0 := by
    calc
      totalNonpreemptivePriorityResidualWork resetState =
          nonpreemptivePriorityArrivalTraceTerminalResidualWork initial.currentTime
            (totalNonpreemptivePriorityResidualWork initial) front resetTime := by
              dsimp [resetState, afterFront]
              apply totalNonpreemptivePriorityResidualWork_advance_run_eq_terminalResidualWork
              · exact hinitialPositive
              · exact hinitialWork
              · exact hleft.le
              · exact hfrontStart
              · exact hfrontSorted
              · exact hfrontCut
              · exact hfrontPositive
      _ = 0 := hscalar
  have htagInitial : nonpreemptivePriorityWorkStateContainsJob initial
      (stationaryPriorityClassTaggedJob meanService i z) := by
    dsimp only [initial, stationaryPriorityClassTaggedArrivalState]
    exact nonpreemptivePriorityWorkStateContainsJob_admit_self _ _
  have htagAfter : nonpreemptivePriorityWorkStateContainsJob afterFront
      (stationaryPriorityClassTaggedJob meanService i z) := by
    dsimp [afterFront]
    exact nonpreemptivePriorityWorkStateContainsJob_run initial front
      (stationaryPriorityClassTaggedJob meanService i z) htagInitial
  have htagReset : nonpreemptivePriorityWorkStateContainsJob resetState
      (stationaryPriorityClassTaggedJob meanService i z) := by
    dsimp [resetState]
    exact nonpreemptivePriorityWorkStateContainsJob_advance
      (totalNonpreemptivePriorityWorkJobs afterFront) resetTime afterFront
      (stationaryPriorityClassTaggedJob meanService i z) htagAfter
  rcases exists_completedTime_of_nonpreemptivePriorityWorkStateContainsJob_of_totalResidualWork_eq_zero
    resetState (stationaryPriorityClassTaggedJob meanService i z)
    hresetPositive hresetTotal htagReset with ⟨completedAt, hcompleted⟩
  have hresetPos : 0 < resetTime := by
    simpa [hinitialTime] using hleft
  refine ⟨front, suffix, resetTime, completedAt, ?_, hresetPos, hright, hfrontCut,
    hsuffix, ?_, ?_⟩
  · simpa [full] using hsplit
  · simpa [initial, afterFront, resetState] using hresetTotal
  · simpa [initial, afterFront, resetState] using hcompleted

/-- Strict aggregate slack makes the canonical finite response observable
nonempty.  The proof first obtains an arrival-free reset prefix, then carries
the concrete completion record through all later admissions in the same finite
right-closed ledger. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none_of_netFuture_lt
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hnet : stationaryPriorityTaggedNetFutureInput meanService i z t <
      -stationaryPriorityClassTaggedArrivalTotalWork meanService i z) :
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t ≠ none := by
  rcases exists_completedTime_stationaryPriorityClassTaggedArrivalPrefix_of_netFuture_lt
    meanService i z t ht hgood hpositive hnet with
      ⟨front, suffix, resetTime, resetCompletedAt, hsplit, hresetPos,
        hresetEnd, hfrontCut, hsuffix, hresetZero, _⟩
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  have hinitialPositive : positiveNonpreemptivePriorityResidualWork initial := by
    exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive
  have hinitialWork : nonpreemptivePriorityWorkConserving initial := by
    exact nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
      meanService i z
  have hinitialTime : initial.currentTime = 0 := by
    exact stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have hfrontPositive : ∀ job ∈ front, 0 < job.serviceWork := by
    intro job hjob
    have hfull : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t := by
      rw [hsplit]
      exact List.mem_append_left _ hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z t job).mp hfull with ⟨j, k, _, hcoordinate⟩
    subst job
    exact hpositive j k
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterFront := by
    dsimp [afterFront]
    exact positiveNonpreemptivePriorityResidualWork_run initial front
      hinitialPositive hfrontPositive
  have hafterWork : nonpreemptivePriorityWorkConserving afterFront := by
    dsimp [afterFront]
    exact nonpreemptivePriorityWorkConserving_run initial front hinitialWork
  have hafterReset : afterFront.currentTime ≤ resetTime := by
    dsimp [afterFront]
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [hinitialTime]
      exact hresetPos.le
    · exact hfrontCut
  have htagInitial : nonpreemptivePriorityWorkStateContainsJob initial
      (stationaryPriorityClassTaggedJob meanService i z) := by
    dsimp only [initial, stationaryPriorityClassTaggedArrivalState]
    exact nonpreemptivePriorityWorkStateContainsJob_admit_self _ _
  have htagAfter : nonpreemptivePriorityWorkStateContainsJob afterFront
      (stationaryPriorityClassTaggedJob meanService i z) := by
    dsimp [afterFront]
    exact nonpreemptivePriorityWorkStateContainsJob_run initial front
      (stationaryPriorityClassTaggedJob meanService i z) htagInitial
  have hcompletion := exists_completedTime_advance_run_of_empty_at_cutoff
    afterFront resetTime t suffix (stationaryPriorityClassTaggedJob meanService i z)
    hafterReset hresetEnd hafterPositive hafterWork
    (by simpa [initial, afterFront] using hresetZero) htagAfter hsuffix
  rcases hcompletion with ⟨completedAt, hcompleted⟩
  have hstate : stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace afterFront suffix))
        t (runNonpreemptivePriorityArrivalTrace afterFront suffix) := by
    unfold stationaryPriorityClassTaggedFinitePostArrivalState
    dsimp only
    rw [hsplit, runNonpreemptivePriorityArrivalTrace_append]
  have hcompletedState :
      (stationaryPriorityClassTaggedJob meanService i z, completedAt) ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed := by
    rw [hstate]
    exact hcompleted
  intro hnone
  have hfind : ((stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed.reverse.find?
      fun entry => decide (entry.1.identifier = Sigma.mk i 0)) = none := by
    simpa [stationaryPriorityClassTaggedFinitePostArrivalResponseTime,
      nonpreemptivePriorityRecordedCompletionTime] using hnone
  have hnot := (List.find?_eq_none.mp hfind)
    (stationaryPriorityClassTaggedJob meanService i z, completedAt)
      (List.mem_reverse.mpr hcompletedState)
  simp [stationaryPriorityClassTaggedJob] at hnot

/-- If the finite post-arrival state is empty, the literal selected job occurs
in its completion ledger.  This is a deterministic queue-semantic statement;
the separate future record-low argument supplies the empty-state hypothesis. -/
theorem exists_completedTime_stationaryPriorityClassTaggedJob_of_totalResidualWork_eq_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (htotal : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) = 0) :
    ∃ completedAt,
      (stationaryPriorityClassTaggedJob meanService i z, completedAt) ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed := by
  apply exists_completedTime_of_nonpreemptivePriorityWorkStateContainsJob_of_totalResidualWork_eq_zero
    (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t)
    (stationaryPriorityClassTaggedJob meanService i z)
  · exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
      meanService i z t hpositive
  · exact htotal
  · unfold stationaryPriorityClassTaggedFinitePostArrivalState
    dsimp only
    apply nonpreemptivePriorityWorkStateContainsJob_advance
    apply nonpreemptivePriorityWorkStateContainsJob_run
    unfold stationaryPriorityClassTaggedArrivalState
    exact nonpreemptivePriorityWorkStateContainsJob_admit_self _ _

/-- An empty finite post-arrival state makes the selected completion lookup
nonempty.  Identifying that lookup's timestamp with the newly admitted job's
unique completion is a later freshness argument. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none_of_totalResidualWork_eq_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (htotal : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) = 0) :
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t ≠ none := by
  rcases exists_completedTime_stationaryPriorityClassTaggedJob_of_totalResidualWork_eq_zero
    meanService i z t hpositive htotal with ⟨completedAt, hcompleted⟩
  intro hnone
  have hfind : ((stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).completed.reverse.find?
      fun entry => decide (entry.1.identifier = Sigma.mk i 0)) = none := by
    simpa [stationaryPriorityClassTaggedFinitePostArrivalResponseTime,
      nonpreemptivePriorityRecordedCompletionTime] using hnone
  have hnot := (List.find?_eq_none.mp hfind)
    (stationaryPriorityClassTaggedJob meanService i z, completedAt)
      (List.mem_reverse.mpr hcompleted)
  simp [stationaryPriorityClassTaggedJob] at hnot

/-- The concrete positive exponential-mark law makes every finite selected
post-arrival execution a strictly positive-residual state almost surely. -/
theorem ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (t : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      positiveNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hpositive
  exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
    meanService i z t hpositive

/-- The causal selected/Palm pre-arrival workload is nonnegative almost
everywhere.  This is a consequence of its literal positive-work finite
remote-past realization, rather than a property imposed on a state selector. -/
theorem ae_nonnegative_stationaryPriorityClassTaggedRemotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      0 ≤ stationaryPriorityClassTaggedRemotePastResidualWork meanService i z := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hcutoff hpositive
  rw [stationaryPriorityClassTaggedRemotePastResidualWork,
    stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService i z hcutoff]
  apply totalNonpreemptivePriorityResidualWork_nonneg
  apply positiveNonpreemptivePriorityResidualWork.nonnegative
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · constructor
    · intro active hactive
      simp [emptyNonpreemptivePriorityWorkState] at hactive
    · intro j job hmember
      simp [emptyNonpreemptivePriorityWorkState] at hmember
  · intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z (-hcutoff.choose) 0 job).mp hjob with ⟨j, k, _, hjob⟩
    subst job
    exact hpositive j k

/-- A selected customer contributes strictly positive service work, so the
total workload immediately after admission is strictly positive almost surely. -/
theorem ae_positive_stationaryPriorityClassTaggedArrivalTotalWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      0 < stationaryPriorityClassTaggedArrivalTotalWork meanService i z := by
  filter_upwards [
    ae_nonnegative_stationaryPriorityClassTaggedRemotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hremote hpositive
  unfold stationaryPriorityClassTaggedArrivalTotalWork
  exact add_pos_of_nonneg_of_pos hremote
    (by simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate]
      using hpositive i 0)

/-- Strict total load drives the literal selected-input future net work below
the finite workload present immediately after admission, at some nonnegative
physical horizon almost surely.  This supplies the first of the two finite
emptying inequalities; the record-low suffix condition is separate. -/
theorem ae_exists_stationaryPriorityClassTaggedFutureNetBelowArrivalTotalWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ t : ℝ, 0 ≤ t ∧ stationaryPriorityTaggedNetFutureInput meanService i z t ≤
        -stationaryPriorityClassTaggedArrivalTotalWork meanService i z := by
  filter_upwards [
    ae_tendsto_stationaryPriorityTaggedNetFutureInput_atBot
      arrivalRate meanService harrivalRate hstable i] with z hlimit
  have htail : ∀ᶠ t : ℝ in Filter.atTop,
      stationaryPriorityTaggedNetFutureInput meanService i z t ≤
        -stationaryPriorityClassTaggedArrivalTotalWork meanService i z :=
    Filter.tendsto_atBot.1 hlimit _
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  let t : ℝ := max bound 0
  refine ⟨t, le_max_right _ _, ?_⟩
  exact hbound t (le_max_left _ _)

/-- Strict total load eventually gives strictly more elapsed service than the
selected post-arrival workload plus every future job in one finite ledger. -/
theorem ae_exists_stationaryPriorityClassTaggedFutureNetStrictlyBelowArrivalTotalWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ t : ℝ, 0 ≤ t ∧ stationaryPriorityTaggedNetFutureInput meanService i z t <
        -stationaryPriorityClassTaggedArrivalTotalWork meanService i z := by
  filter_upwards [
    ae_tendsto_stationaryPriorityTaggedNetFutureInput_atBot
      arrivalRate meanService harrivalRate hstable i] with z hlimit
  have htail : ∀ᶠ t : ℝ in Filter.atTop,
      stationaryPriorityTaggedNetFutureInput meanService i z t ≤
        -stationaryPriorityClassTaggedArrivalTotalWork meanService i z - 1 :=
    Filter.tendsto_atBot.1 hlimit _
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  let t : ℝ := max bound 0
  refine ⟨t, le_max_right _ _, ?_⟩
  have hvalue := hbound t (le_max_left _ _)
  linarith

/-- Under strict load, the concrete finite selected-customer response lookup
is almost surely nonempty at some finite right-closed future horizon. -/
theorem ae_exists_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ t : ℝ, 0 ≤ t ∧
        stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t ≠ none := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFutureNetStrictlyBelowArrivalTotalWork
      arrivalRate meanService harrivalRate hstable i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hnet hgood hpositive
  rcases hnet with ⟨t, ht, hnet⟩
  exact ⟨t, ht,
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none_of_netFuture_lt
      meanService i z t ht hgood hpositive hnet⟩

/-- Under strict total load, every sufficiently late literal post-arrival
execution has recorded the selected customer's completion. -/
theorem ae_eventually_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ t : ℝ in Filter.atTop,
        stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t ≠ none := by
  filter_upwards [
    ae_tendsto_stationaryPriorityTaggedNetFutureInput_atBot
      arrivalRate meanService harrivalRate hstable i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hlimit hgood hpositive
  have htail : ∀ᶠ t : ℝ in Filter.atTop,
      stationaryPriorityTaggedNetFutureInput meanService i z t ≤
        -stationaryPriorityClassTaggedArrivalTotalWork meanService i z - 1 :=
    Filter.tendsto_atBot.1 hlimit _
  filter_upwards [htail, Filter.eventually_ge_atTop (0 : ℝ)] with t hnet ht
  apply stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none_of_netFuture_lt
    meanService i z t ht hgood hpositive
  linarith

/-- Under strict total load, the finite right-closed response observations
almost surely stabilize at one physical completion epoch. -/
theorem ae_exists_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eventually_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ (t completedAt : ℝ), 0 ≤ t ∧
        ∀ᶠ u : ℝ in Filter.atTop,
          stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
            some completedAt := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hfinite hgood
  rcases hfinite with ⟨t, ht, hresponse⟩
  cases htime : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z t with
  | none => exact (hresponse htime).elim
  | some completedAt =>
      refine ⟨t, completedAt, ht, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop t] with u htu
      exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eq_of_le
        meanService i z t u completedAt hgood ht htu htime

/-- Sufficiently remote two-sided finite replays have exactly the same tagged
completion observation as the causal remote-past post-arrival execution. -/
theorem ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
          meanService i z (horizon : ℝ) (horizon : ℝ) =
          stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z
            (horizon : ℝ) := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalesces
  rcases hcoalesces with ⟨cutoff, _, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  apply stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_liveEquivalent
    meanService i z (horizon : ℝ) (horizon : ℝ)
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  exact hcoalesces (horizon : ℝ) (hceil.trans hcast)

/-- The canonical stationary response is almost surely the concrete physical
completion epoch selected by the stabilized finite replays. -/
theorem ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ (t completedAt : ℝ), 0 ≤ t ∧
        stationaryPriorityClassTaggedResponseTime meanService i z = completedAt ∧
        ∀ᶠ u : ℝ in Filter.atTop,
          stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
            some completedAt := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eventually_eq
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hstabilizes hreplay
  rcases hstabilizes with ⟨t, completedAt, ht, htail⟩
  refine ⟨t, completedAt, ht, ?_, htail⟩
  apply stationaryPriorityClassTaggedResponseTime_eq_of_eventually_eq
    meanService i z completedAt
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  have hpost : ∀ᶠ horizon : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z
        (horizon : ℝ) = some completedAt := by
    apply Filter.eventually_atTop.2
    refine ⟨Nat.ceil bound, ?_⟩
    intro horizon hhorizon
    have hceil : bound ≤ (Nat.ceil bound : ℝ) := Nat.le_ceil bound
    have hcast : (Nat.ceil bound : ℝ) ≤ (horizon : ℝ) := by
      exact_mod_cast hhorizon
    exact hbound (horizon : ℝ) (hceil.trans hcast)
  filter_upwards [hreplay, hpost] with horizon hfinite hpost
  rw [hfinite, hpost]

/-- Under strict total load, the canonical tagged response itself satisfies
the literal selected-Palm remote-past semantics.  The proof combines the
physical causal completion epoch with exact coalescence of sufficiently
remote finite replays; it introduces no separate stationarity hypothesis. -/
theorem isStationaryPriorityClassTaggedRemotePastResponse_canonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    IsStationaryPriorityClassTaggedRemotePastResponse
      arrivalRate meanService harrivalRate i
      (stationaryPriorityClassTaggedResponseTime meanService i) := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcompletion hreplay
  rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  rcases Filter.eventually_atTop.1 hreplay with ⟨replayBound, hreplayBound⟩
  apply Filter.eventually_atTop.2
  refine ⟨max (Nat.ceil bound) replayBound, ?_⟩
  intro horizon hhorizon
  have hceil : bound ≤ (Nat.ceil bound : ℝ) := Nat.le_ceil bound
  have hcastNat : Nat.ceil bound ≤ horizon :=
    (le_max_left _ _).trans hhorizon
  have hcast : (Nat.ceil bound : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hcastNat
  have hpost : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z (horizon : ℝ) = some completedAt :=
    hbound (horizon : ℝ) (hceil.trans hcast)
  have hfinite := hreplayBound horizon ((le_max_right _ _).trans hhorizon)
  rw [hfinite, hpost]
  simpa [hresponse]

/-- A strict post-tag net-work record low forces the literal stabilized Palm
response to have completed by that horizon.  Equivalently, the response tail
can only occur when the finite marked input has not yet supplied enough
service capacity to clear the post-arrival workload.  This is a pathwise
tail-containment result; obtaining its integrable quantitative bound is a
separate renewal-reward step. -/
theorem ae_stationaryPriorityClassTaggedResponseTime_le_of_netFuture_lt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityTaggedNetFutureInput meanService i z t <
          -stationaryPriorityClassTaggedArrivalTotalWork meanService i z →
        stationaryPriorityClassTaggedResponseTime meanService i z ≤ t := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hgood hpositive hcompletion
  intro hnet
  have hnonempty : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z t ≠ none :=
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none_of_netFuture_lt
      meanService i z t ht hgood hpositive hnet
  cases hfinite : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z t with
  | none => exact (hnonempty hfinite).elim
  | some observedAt =>
      have hobservation : observedAt ≤ t :=
        stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_horizon_of_eq_some
          meanService i z t observedAt hgood hpositive ht hfinite
      rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
      rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
      let u : ℝ := max t bound
      have htu : t ≤ u := le_max_left _ _
      have hfiniteU : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
          meanService i z u = some observedAt :=
        stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eq_of_le
          meanService i z t u observedAt hgood ht htu hfinite
      have htailU : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
          meanService i z u = some completedAt :=
        hbound u (le_max_right _ _)
      have heq : observedAt = completedAt :=
        Option.some.inj (hfiniteU.symm.trans htailU)
      calc
        stationaryPriorityClassTaggedResponseTime meanService i z = completedAt := hresponse
        _ = observedAt := heq.symm
        _ ≤ t := hobservation

/-- Hence, outside a fixed null set, a response exceeding `t` is possible
only when the literal post-tag net input has failed to fall below the negative
arrival workload by time `t`.  This is the event-form tail containment used
by a future quantitative renewal bound. -/
theorem ae_stationaryPriorityClassTaggedResponseTime_lt_imp_negArrivalWork_le_netFuture
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      t < stationaryPriorityClassTaggedResponseTime meanService i z →
        -stationaryPriorityClassTaggedArrivalTotalWork meanService i z ≤
          stationaryPriorityTaggedNetFutureInput meanService i z t := by
  filter_upwards [
    ae_stationaryPriorityClassTaggedResponseTime_le_of_netFuture_lt
      arrivalRate meanService harrivalRate hmeanService hstable i t ht] with z hbound
  intro htail
  by_contra hnot
  have hnet : stationaryPriorityTaggedNetFutureInput meanService i z t <
      -stationaryPriorityClassTaggedArrivalTotalWork meanService i z :=
    lt_of_not_ge hnot
  exact (not_lt_of_ge (hbound hnet)) htail

/-- On the full-measure stable selected-Palm carrier, total workload has exact
unreflected work conservation at every nonnegative time strictly before the
literal selected completion.  This packages the finite ledger result at the
actual stationary response, while leaving all expectation and truncation work
for a separate probabilistic argument. -/
theorem ae_exists_stationaryPriorityClassTaggedResponseTime_unreflectedWorkConservation
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ completedAt,
        stationaryPriorityClassTaggedResponseTime meanService i z = completedAt ∧
        ∀ s, 0 ≤ s → s < completedAt →
          totalNonpreemptivePriorityResidualWork
            (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) =
            stationaryPriorityClassTaggedArrivalTotalWork meanService i z +
              nonpreemptivePriorityArrivalTraceServiceWork
                (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s) - s := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hgood hpositive hcompletion
  rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
  refine ⟨completedAt, hresponse, ?_⟩
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  intro s hs hslt
  let u : ℝ := max s bound
  have hsu : s ≤ u := le_max_left _ _
  have hresponseU : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z u = some completedAt := by
    exact hbound u (le_max_right _ _)
  exact totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_initial_add_futureServiceWork_sub_of_lt_responseTime
    meanService i z s u completedAt hgood hpositive hs hsu hslt hresponseU

/-- The literal selected-customer queue wait is nonnegative almost surely.
On the concrete Palm event where finite replays stabilize to the physical
completion epoch, the finite tagged completion lower bound makes that epoch
at least the selected service requirement. -/
theorem ae_nonneg_stationaryPriorityClassTaggedQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hgood hpositive hcompletion
  rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  have hfinite := hbound bound le_rfl
  have hservice : stationaryPriorityClassTaggedWorkRequirement meanService i z ≤ completedAt := by
    exact stationaryPriorityClassTaggedWorkRequirement_le_finitePostArrivalResponseTime_of_eq_some
      meanService i z bound completedAt hgood hpositive hfinite
  unfold stationaryPriorityClassTaggedQueueWait
  rw [hresponse]
  exact sub_nonneg.mpr hservice

/-- At natural horizons, the total finite response replays almost surely
eventually equal the canonical stationary selected-customer response. -/
theorem ae_eventually_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_getD_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        (stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z
          (horizon : ℝ)).getD 0 =
          stationaryPriorityClassTaggedResponseTime meanService i z := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcompletion
  rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil bound, ?_⟩
  intro horizon hhorizon
  have hceil : bound ≤ (Nat.ceil bound : ℝ) := Nat.le_ceil bound
  have hcast : (Nat.ceil bound : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  rw [hbound (horizon : ℝ) (hceil.trans hcast), hresponse]
  rfl

/-- The total two-sided finite replays used in the response definition almost
surely eventually equal that canonical stationary response. -/
theorem ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
          meanService i z (horizon : ℝ) (horizon : ℝ)).getD 0 =
          stationaryPriorityClassTaggedResponseTime meanService i z := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcompletion hreplay
  rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  have hpost : ∀ᶠ horizon : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z
        (horizon : ℝ) = some completedAt := by
    apply Filter.eventually_atTop.2
    refine ⟨Nat.ceil bound, ?_⟩
    intro horizon hhorizon
    have hceil : bound ≤ (Nat.ceil bound : ℝ) := Nat.le_ceil bound
    have hcast : (Nat.ceil bound : ℝ) ≤ (horizon : ℝ) := by
      exact_mod_cast hhorizon
    exact hbound (horizon : ℝ) (hceil.trans hcast)
  filter_upwards [hreplay, hpost] with horizon hfinite hpost
  rw [hfinite, hpost, hresponse]
  rfl

/-- Measurability of the finite two-sided replay observables transports to
the canonical stationary response.  Establishing the displayed finite Borel
premise is the remaining model-specific measurable-replay obligation. -/
theorem aemeasurable_stationaryPriorityClassTaggedResponseTime_of_measurable_finiteReplays
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n)
    (hfinite : ∀ horizon : ℕ,
      Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
          meanService i z (horizon : ℝ) (horizon : ℝ)).getD 0)) :
    AEMeasurable (stationaryPriorityClassTaggedResponseTime meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  exact Probability.aemeasurable_response_of_ae_eventually_eq
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
    (fun horizon z =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
        meanService i z (horizon : ℝ) (horizon : ℝ)).getD 0)
    (stationaryPriorityClassTaggedResponseTime meanService i)
    hfinite
    (ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD_eq
      arrivalRate meanService harrivalRate hmeanService hstable i)

/-- Under the concrete selected Palm law and strict total load, the selected
customer has an almost-sure finite physical completion prefix.  The prefix is
constructed from literal arrivals and an actual arrival-free reset epoch, not
from a response-time certificate. -/
theorem ae_exists_stationaryPriorityClassTaggedArrivalCompletionPrefix
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ (t : ℝ) (front suffix : List
          (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
        (resetTime completedAt : ℝ),
        0 ≤ t ∧
        canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t =
          front ++ suffix ∧
        0 < resetTime ∧ resetTime ≤ t ∧
        (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
        (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
        totalNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace
                (stationaryPriorityClassTaggedArrivalState meanService i z) front))
            resetTime
            (runNonpreemptivePriorityArrivalTrace
              (stationaryPriorityClassTaggedArrivalState meanService i z) front)) = 0 ∧
        (stationaryPriorityClassTaggedJob meanService i z, completedAt) ∈
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace
                (stationaryPriorityClassTaggedArrivalState meanService i z) front))
            resetTime
            (runNonpreemptivePriorityArrivalTrace
              (stationaryPriorityClassTaggedArrivalState meanService i z) front)).completed := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFutureNetStrictlyBelowArrivalTotalWork
      arrivalRate meanService harrivalRate hstable i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hnet hgood hpositive
  rcases hnet with ⟨t, ht, hnet⟩
  rcases exists_completedTime_stationaryPriorityClassTaggedArrivalPrefix_of_netFuture_lt
    meanService i z t ht hgood hpositive hnet with
      ⟨front, suffix, resetTime, completedAt, hsplit, hresetPos, hresetEnd,
        hfront, hsuffix, hresetZero, hcompleted⟩
  exact ⟨t, front, suffix, resetTime, completedAt, ht, hsplit, hresetPos,
    hresetEnd, hfront, hsuffix, hresetZero, hcompleted⟩

end

end AppliedModelingLib.Queueing

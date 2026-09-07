import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFutureMarkPredictability
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedServiceStartPredictability
import AppliedModelingLib.Queueing.MulticlassPalmFutureFactors
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedResponseIntegrability
import AppliedModelingLib.Foundations.Math.Asymptotics

/-!
# Deterministic-time locality for finite priority replays

A finite priority ledger before a deterministic clock depends only on the
labelled arrivals and work marks exposed before that clock.  This module
provides the pathwise finite-ledger layer used by stopped Poisson
compensation arguments.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

open scoped MeasureTheory

/-- The right-closed passive-class arrival count through the tagged customer's
queue-wait horizon.  A later no-simultaneous-arrival lemma will identify this
with the strict pre-service count used in the priority work decomposition. -/
noncomputable def stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (j : {k : Fin n // k ≠ i}) : ℕ :=
  multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j
    (stationaryPriorityClassTaggedQueueWait meanService i z)

/-- The right-closed count through a nonnegative queue-wait horizon is the
cardinality of the literal stationary passive-arrival ledger. -/
theorem stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait_eq_card
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (j : {k : Fin n // k ≠ i})
    (hwait : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z) :
    stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
      meanService i z j =
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1).card := by
  exact multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_eq_card
    i z j _ hwait

/-- Membership in the strict finite post-tag ledger is exactly the literal
open physical interval `(0,t)`. -/
theorem mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (j : Fin n) (k : ℤ) :
    k ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t j ↔
      0 < stationaryPriorityClassTaggedArrival i z j k ∧
        stationaryPriorityClassTaggedArrival i z j k < t := by
  unfold stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
  rw [Finset.mem_filter]
  by_cases hji : j = i
  · subst j
    simp only [stationaryPriorityClassTaggedFutureArrivalIndices, dif_pos]
    rw [Probability.PoissonProcess.mem_palmTaggedArrivalIndicesRightClosed_iff
      0 t z.1.1 hgood k]
    simp only [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_pos]
    constructor
    · rintro ⟨⟨hpos, _⟩, hlt⟩
      exact ⟨hpos, hlt⟩
    · rintro ⟨hpos, hlt⟩
      exact ⟨⟨hpos, hlt.le⟩, hlt⟩
  · simp only [stationaryPriorityClassTaggedFutureArrivalIndices, dif_neg hji]
    rw [Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
      0 t (z.2 ⟨j, hji⟩).1 k]
    simp only [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hji]
    change (0 < Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨j, hji⟩).1 k ∧
        Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨j, hji⟩).1 k ≤ t) ∧
        Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨j, hji⟩).1 k < t ↔
      0 < Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨j, hji⟩).1 k ∧
        Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨j, hji⟩).1 k < t
    constructor
    · rintro ⟨⟨hpos, _⟩, hlt⟩
      exact ⟨hpos, hlt⟩
    · rintro ⟨hpos, hlt⟩
      exact ⟨⟨hpos, hlt.le⟩, hlt⟩

/-- Equality of all labelled arrivals that occur strictly before `t` fixes the
classwise strict future-index ledger. -/
theorem stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hgoodz : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1)
    (harrival : ∀ (j : Fin n) (k : ℤ),
      stationaryPriorityClassTaggedArrival i z j k < t ∨
        stationaryPriorityClassTaggedArrival i w j k < t →
      stationaryPriorityClassTaggedArrival i z j k =
        stationaryPriorityClassTaggedArrival i w j k) :
    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t =
      stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w t := by
  funext j
  ext k
  rw [mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
      i z t hgoodz j k,
    mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
      i w t hgoodw j k]
  constructor
  · intro hz
    have heq := harrival j k (Or.inl hz.2)
    rw [heq] at hz
    exact hz
  · intro hw
    have heq := harrival j k (Or.inr hw.2)
    rw [heq]
    exact hw

/-- Replacing the fresh future arrival-gap tail of one passive class leaves
every labelled priority arrival that either path places before the clock at
the same physical epoch. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_arrival_eq_of_lt
    {n : ℕ} (arrivalRate : Fin n → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (k : Fin n) (m : ℤ)
    (hbefore : stationaryPriorityClassTaggedArrival i z k m < s ∨
      stationaryPriorityClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        k m < s) :
    stationaryPriorityClassTaggedArrival i z k m =
      stationaryPriorityClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        k m := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  change stationaryPriorityClassTaggedArrival i z k m =
    stationaryPriorityClassTaggedArrival i w k m
  change stationaryPriorityClassTaggedArrival i z k m < s ∨
      stationaryPriorityClassTaggedArrival i w k m < s at hbefore
  by_cases hki : k = i
  · subst k
    simp only [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_pos]
    rw [multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
      arrivalRate harrivalRate i j s z]
  let k' : {l : Fin n // l ≠ i} := ⟨k, hki⟩
  by_cases hkj : k' = j
  · have hkval : k = j.1 := congrArg Subtype.val hkj
    subst k
    have heq :=
      multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_arrival_eq_of_le_or_le
        arrivalRate harrivalRate i j s hs z m
        (hbefore.imp le_of_lt le_of_lt)
    simpa [w] using heq.symm
  · simp only [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hki]
    change Probability.Queueing.stationaryPoissonWorkArrival (z.2 k') m =
      Probability.Queueing.stationaryPoissonWorkArrival (w.2 k') m
    rw [multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_otherPassive_eq
      arrivalRate harrivalRate i j s z k' hkj]

/-- The strict classwise priority ledger through a deterministic clock is
unchanged by the external-only passive continuation. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_futureIndices_eq
    {n : ℕ} (arrivalRate : Fin n → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z s =
      stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1) s := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  have hselected :=
    multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
      arrivalRate harrivalRate i j s z
  have hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1 := by
    rw [hselected]
    exact hgood
  change stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z s =
    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w s
  apply stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
    i z w s hgood hgoodw
  intro k m hbefore
  exact stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_arrival_eq_of_lt
    arrivalRate harrivalRate i j s hs z k m (by simpa [w] using hbefore)

/-- Equality of the finite pre-clock arrivals fixes the canonical chronological
strict ledger as well as its classwise point set. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hgoodz : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1)
    (harrival : ∀ (j : Fin n) (k : ℤ),
      stationaryPriorityClassTaggedArrival i z j k < t ∨
        stationaryPriorityClassTaggedArrival i w j k < t →
      stationaryPriorityClassTaggedArrival i z j k =
        stationaryPriorityClassTaggedArrival i w j k) :
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w t := by
  have hclass :=
    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
      i z w t hgoodz hgoodw harrival
  classical
  let S := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w t)
  let rz := stationaryPriorityClassTaggedArrivalIndexLE i z
  let rw' := stationaryPriorityClassTaggedArrivalIndexLE i w
  have hS : nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t) = S := by
    simpa [S] using congrArg nonpreemptivePriorityArrivalWindowIndices hclass
  have harrivalS : ∀ q : NonpreemptivePriorityArrivalIndex n, q ∈ S →
      stationaryPriorityClassTaggedArrival i z q.1 q.2 =
        stationaryPriorityClassTaggedArrival i w q.1 q.2 := by
    intro q hq
    have hcomponent : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z t q.1 := by
      rw [hclass]
      simpa [S, nonpreemptivePriorityArrivalWindowIndices] using hq
    have hlt :=
      (mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
        i z t hgoodz q.1 q.2).mp hcomponent |>.2
    exact harrival q.1 q.2 (Or.inl hlt)
  have horder : ∀ a ∈ S, ∀ b ∈ S, rz a b ↔ rw' a b := by
    intro a ha b hb
    unfold rz rw' stationaryPriorityClassTaggedArrivalIndexLE
      stationaryPriorityClassTaggedArrivalIndexKey
    rw [harrivalS a ha, harrivalS b hb]
  have pairwise_transfer : ∀ (l : List (NonpreemptivePriorityArrivalIndex n)),
      (∀ a ∈ l, ∀ b ∈ l, rz a b ↔ rw' a b) →
      l.Pairwise rw' → l.Pairwise rz := by
    intro l
    induction l with
    | nil =>
        intro _ _
        simp
    | cons a l ih =>
        intro hlocal hpair
        rw [List.pairwise_cons] at hpair ⊢
        constructor
        · intro b hb
          exact (hlocal a (by simp) b (List.mem_cons.mpr (Or.inr hb))).mpr
            (hpair.1 b hb)
        · apply ih
          · intro b hb c hc
            exact hlocal b (List.mem_cons_of_mem _ hb) c
              (List.mem_cons_of_mem _ hc)
          · exact hpair.2
  letI : DecidableRel rz := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rz :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm rz :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total rz :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  letI : DecidableRel rw' := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rw' :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i w⟩
  letI : Std.Antisymm rw' :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i w⟩
  letI : Std.Total rw' :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i w⟩
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t)).sort rz =
      (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w t)).sort rw'
  rw [hS]
  have hperm : List.Perm (S.sort rz) (S.sort rw') :=
    (Finset.sort_perm_toList S rz).trans (Finset.sort_perm_toList S rw').symm
  have hleft : (S.sort rz).Pairwise rz := Finset.pairwise_sort S rz
  have hrightw : (S.sort rw').Pairwise rw' := Finset.pairwise_sort S rw'
  have hright : (S.sort rw').Pairwise rz := by
    apply pairwise_transfer (S.sort rw')
    · intro a ha b hb
      exact horder a ((Finset.mem_sort rw').mp ha) b ((Finset.mem_sort rw').mp hb)
    · exact hrightw
  exact hperm.eq_of_pairwise' hleft hright

/-- The canonical chronological strict future-index ledger is unchanged by
the external-only deterministic continuation of one passive class. -/
theorem canonicalStationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_futureIndices_eq
    {n : ℕ} (arrivalRate : Fin n → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z s =
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1) s := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  have hselected :=
    multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
      arrivalRate harrivalRate i j s z
  have hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1 := by
    rw [hselected]
    exact hgood
  change canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z s =
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w s
  apply canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
    i z w s hgood hgoodw
  intro k m hbefore
  exact stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_arrival_eq_of_lt
    arrivalRate harrivalRate i j s hs z k m (by simpa [w] using hbefore)

/-- Equality of arrivals through a deterministic clock also fixes every
finite half-open priority input ledger whose right endpoint is at that clock
or earlier. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrival_eq_of_lt
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b s : ℝ) (hb : b ≤ s)
    (hgoodz : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1)
    (harrival : ∀ (j : Fin n) (k : ℤ),
      stationaryPriorityClassTaggedArrival i z j k < s ∨
        stationaryPriorityClassTaggedArrival i w j k < s →
      stationaryPriorityClassTaggedArrival i z j k =
        stationaryPriorityClassTaggedArrival i w j k) :
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i w a b := by
  have hclass : stationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      stationaryPriorityClassTaggedArrivalWindowIndices i w a b := by
    funext k
    ext m
    by_cases hki : k = i
    · subst k
      simp only [stationaryPriorityClassTaggedArrivalWindowIndices, dif_pos]
      rw [Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a b z.1.1 hgoodz,
        Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a b w.1.1 hgoodw]
      constructor
      · rintro ⟨haleft, haright⟩
        have haright' : stationaryPriorityClassTaggedArrival i z i m < b := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using haright
        have heq := harrival i m (Or.inl (haright'.trans_le hb))
        have heq' : Probability.PoissonProcess.candidatePalmArrival z.1.1 m =
            Probability.PoissonProcess.candidatePalmArrival w.1.1 m := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using heq
        rw [heq'] at haleft haright
        exact ⟨haleft, haright⟩
      · rintro ⟨haleft, haright⟩
        have haright' : stationaryPriorityClassTaggedArrival i w i m < b := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using haright
        have heq := harrival i m (Or.inr (haright'.trans_le hb))
        have heq' : Probability.PoissonProcess.candidatePalmArrival z.1.1 m =
            Probability.PoissonProcess.candidatePalmArrival w.1.1 m := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using heq
        rw [heq']
        exact ⟨haleft, haright⟩
    · simp only [stationaryPriorityClassTaggedArrivalWindowIndices, dif_neg hki]
      rw [Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff,
        Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff]
      constructor
      · rintro ⟨haleft, haright⟩
        have haright' : stationaryPriorityClassTaggedArrival i z k m < b := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hki] using haright
        have heq := harrival k m (Or.inl (haright'.trans_le hb))
        have heq' : Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨k, hki⟩).1 m =
            Probability.PoissonProcess.suspensionBaseArrival (w.2 ⟨k, hki⟩).1 m := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hki] using heq
        rw [heq'] at haleft haright
        exact ⟨haleft, haright⟩
      · rintro ⟨haleft, haright⟩
        have haright' : stationaryPriorityClassTaggedArrival i w k m < b := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hki] using haright
        have heq := harrival k m (Or.inr (haright'.trans_le hb))
        have heq' : Probability.PoissonProcess.suspensionBaseArrival (z.2 ⟨k, hki⟩).1 m =
            Probability.PoissonProcess.suspensionBaseArrival (w.2 ⟨k, hki⟩).1 m := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hki] using heq
        rw [heq']
        exact ⟨haleft, haright⟩
  classical
  let S := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i w a b)
  let rz := stationaryPriorityClassTaggedArrivalIndexLE i z
  let rw' := stationaryPriorityClassTaggedArrivalIndexLE i w
  have hS : nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedArrivalWindowIndices i z a b) = S := by
    simpa [S] using congrArg nonpreemptivePriorityArrivalWindowIndices hclass
  have harrivalS : ∀ q : NonpreemptivePriorityArrivalIndex n, q ∈ S →
      stationaryPriorityClassTaggedArrival i z q.1 q.2 =
        stationaryPriorityClassTaggedArrival i w q.1 q.2 := by
    intro q hq
    have hcomponent : q.2 ∈ stationaryPriorityClassTaggedArrivalWindowIndices
        i z a b q.1 := by
      rw [hclass]
      simpa [S, nonpreemptivePriorityArrivalWindowIndices] using hq
    have hcanonical : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z a b :=
      (mem_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_iff i z a b q).mpr
        hcomponent
    have hlt := canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right
      i z a b hgoodz q hcanonical
    exact harrival q.1 q.2 (Or.inl (hlt.trans_le hb))
  have horder : ∀ first ∈ S, ∀ second ∈ S, rz first second ↔ rw' first second := by
    intro first hfirst second hsecond
    unfold rz rw' stationaryPriorityClassTaggedArrivalIndexLE
      stationaryPriorityClassTaggedArrivalIndexKey
    rw [harrivalS first hfirst, harrivalS second hsecond]
  have pairwise_transfer : ∀ (l : List (NonpreemptivePriorityArrivalIndex n)),
      (∀ first ∈ l, ∀ second ∈ l, rz first second ↔ rw' first second) →
      l.Pairwise rw' → l.Pairwise rz := by
    intro l
    induction l with
    | nil =>
        intro _ _
        simp
    | cons first l ih =>
        intro hlocal hpair
        rw [List.pairwise_cons] at hpair ⊢
        constructor
        · intro second hsecond
          exact (hlocal first (by simp) second (List.mem_cons.mpr (Or.inr hsecond))).mpr
            (hpair.1 second hsecond)
        · apply ih
          · intro second hsecond third hthird
            exact hlocal second (List.mem_cons_of_mem _ hsecond) third
              (List.mem_cons_of_mem _ hthird)
          · exact hpair.2
  letI : DecidableRel rz := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rz :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm rz :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total rz :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  letI : DecidableRel rw' := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rw' :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i w⟩
  letI : Std.Antisymm rw' :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i w⟩
  letI : Std.Total rw' :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i w⟩
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)).sort rz =
      (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityClassTaggedArrivalWindowIndices i w a b)).sort rw'
  rw [hS]
  have hperm : List.Perm (S.sort rz) (S.sort rw') :=
    (Finset.sort_perm_toList S rz).trans (Finset.sort_perm_toList S rw').symm
  have hleft : (S.sort rz).Pairwise rz := Finset.pairwise_sort S rz
  have hrightw : (S.sort rw').Pairwise rw' := Finset.pairwise_sort S rw'
  have hright : (S.sort rw').Pairwise rz := by
    apply pairwise_transfer (S.sort rw')
    · intro first hfirst second hsecond
      exact horder first ((Finset.mem_sort rw').mp hfirst) second
        ((Finset.mem_sort rw').mp hsecond)
    · exact hrightw
  exact hperm.eq_of_pairwise' hleft hright

/-- A strict finite replay through a deterministic clock is unchanged when
every arrival and work mark that either input places before that clock agrees,
as do the selected Palm jobs. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_arrival_requirement_eq_of_lt
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (ht : 0 ≤ t)
    (hgoodz : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1)
    (htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w)
    (harrival : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m < t ∨
        stationaryPriorityClassTaggedArrival i w k m < t →
      stationaryPriorityClassTaggedArrival i z k m =
        stationaryPriorityClassTaggedArrival i w k m)
    (hrequirement : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m < t ∨
        stationaryPriorityClassTaggedArrival i w k m < t →
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z k m =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w k m) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i w older t := by
  have hpastIndices :=
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrival_eq_of_lt
      i z w (-older) 0 t ht hgoodz hgoodw harrival
  have hpast : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
      (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0 := by
    apply canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_jobs_eq meanService i z w
      (-older) 0
    unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    rw [hpastIndices]
    apply List.map_congr_left
    intro q hq
    have hqz : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0 := by
      rwa [hpastIndices]
    have hbeforeZero := canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right
      i z (-older) 0 hgoodz q hqz
    have hbefore : stationaryPriorityClassTaggedArrival i z q.1 q.2 < t :=
      hbeforeZero.trans_le ht
    rw [harrival q.1 q.2 (Or.inl hbefore),
      hrequirement q.1 q.2 (Or.inl hbefore)]
  have hfutureIndices :=
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
      i z w t hgoodz hgoodw harrival
  have hfuture : canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i w t := by
    unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    rw [hfutureIndices]
    apply List.map_congr_left
    intro q hq
    have hqz : q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z t := by
      rwa [hfutureIndices]
    have hcomponent : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z t q.1 := by
      simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
        nonpreemptivePriorityArrivalWindowIndices] using hqz
    have hbefore :=
      (mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
        i z t hgoodz q.1 q.2).mp hcomponent |>.2
    rw [harrival q.1 q.2 (Or.inl hbefore),
      hrequirement q.1 q.2 (Or.inl hbefore)]
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_pastState_eq
    meanService i z w older t t rfl hpast htag hfuture

/-- Under the same deterministic-time locality hypotheses, the selected
completion observation of the strict finite replay is unchanged. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_eq_of_arrival_requirement_eq_of_lt
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (ht : 0 ≤ t)
    (hgoodz : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1)
    (htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w)
    (harrival : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m < t ∨
        stationaryPriorityClassTaggedArrival i w k m < t →
      stationaryPriorityClassTaggedArrival i z k m =
        stationaryPriorityClassTaggedArrival i w k m)
    (hrequirement : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m < t ∨
        stationaryPriorityClassTaggedArrival i w k m < t →
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z k m =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w k m) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i z older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i w older t := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_arrival_requirement_eq_of_lt
    meanService i z w older t ht hgoodz hgoodw htag harrival hrequirement]

/-- Every scaled service-work coordinate is preserved by the deterministic
passive continuation. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_requirement_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (k : Fin n) (m : ℤ) :
    stationaryPriorityClassTaggedWorkRequirementAt meanService i z k m =
      stationaryPriorityClassTaggedWorkRequirementAt meanService i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        k m := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  change stationaryPriorityClassTaggedWorkRequirementAt meanService i z k m =
    stationaryPriorityClassTaggedWorkRequirementAt meanService i w k m
  by_cases hki : k = i
  · subst k
    simp only [stationaryPriorityClassTaggedWorkRequirementAt,
      multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_pos]
    rw [multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
      arrivalRate harrivalRate i j s z]
  let k' : {l : Fin n // l ≠ i} := ⟨k, hki⟩
  by_cases hkj : k' = j
  · have hkval : k = j.1 := congrArg Subtype.val hkj
    subst k
    simp only [stationaryPriorityClassTaggedWorkRequirementAt,
      multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg j.2]
    exact congrArg (fun r => meanService j.1 * r)
      (by simpa [w] using
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_isolatedRequirement_eq
          arrivalRate harrivalRate i j s z m).symm)
  · simp only [stationaryPriorityClassTaggedWorkRequirementAt,
      multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg hki]
    rw [multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_otherPassive_eq
      arrivalRate harrivalRate i j s z k' hkj]

/-- The executable finite priority-job replay strictly before a deterministic
clock is unchanged by continuing one passive arrival path from exposed data. -/
theorem canonicalStationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_futureJobs_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z s =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1) s := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  have hindices :=
    canonicalStationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_futureIndices_eq
      arrivalRate harrivalRate i j s hs z hgood
  change canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z s =
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w s
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
  rw [hindices]
  apply List.map_congr_left
  intro q hq
  have hqz : q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z s := by
    rwa [hindices]
  have hcomponent : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z s q.1 := by
    simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      nonpreemptivePriorityArrivalWindowIndices] using hqz
  have hbefore :=
    (mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
      i z s hgood q.1 q.2).mp hcomponent |>.2
  rw [stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_arrival_eq_of_lt
      arrivalRate harrivalRate i j s hs z q.1 q.2 (Or.inl hbefore),
    stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_requirement_eq
      arrivalRate meanService harrivalRate i j s z q.1 q.2]

/-- The continuation preserves the complete finite replay state accumulated
strictly before the Palm clock. -/
theorem canonicalStationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_pastState_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        (-older) 0 := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  have hselected :=
    multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
      arrivalRate harrivalRate i j s z
  have hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1 := by
    rw [hselected]
    exact hgood
  have hindices :=
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrival_eq_of_lt
      i z w (-older) 0 s hs hgood hgoodw (fun k m hbefore =>
        stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_arrival_eq_of_lt
          arrivalRate harrivalRate i j s hs z k m (by simpa [w] using hbefore))
  change canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0
  apply canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_jobs_eq meanService i z w
    (-older) 0
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
  rw [hindices]
  apply List.map_congr_left
  intro q hq
  have hqz : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices
      i z (-older) 0 := by
    rwa [hindices]
  have hbefore := canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right
    i z (-older) 0 hgood q hqz
  rw [stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_arrival_eq_of_lt
      arrivalRate harrivalRate i j s hs z q.1 q.2 (Or.inl (hbefore.trans_le hs)),
    stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_requirement_eq
      arrivalRate meanService harrivalRate i j s z q.1 q.2]

/-- The distinguished Palm job itself is unchanged by a deterministic
continuation of a different passive class. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_tag_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s : ℝ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1) := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  have hselected :=
    multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail_selected_eq
      arrivalRate harrivalRate i j s z
  have harrival : stationaryPriorityClassTaggedArrival i z i 0 =
      stationaryPriorityClassTaggedArrival i w i 0 := by
    simp only [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_pos]
    exact congrArg (fun path : ℤ → ℝ =>
      Probability.PoissonProcess.candidatePalmArrival path 0) (congrArg Prod.fst hselected).symm
  have hwork :=
    stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_requirement_eq
      arrivalRate meanService harrivalRate i j s z i 0
  change stationaryPriorityClassTaggedJob meanService i z =
    stationaryPriorityClassTaggedJob meanService i w
  unfold stationaryPriorityClassTaggedJob
  rw [harrival, hwork]

/-- A finite strict post-arrival replay at a deterministic clock is fixed by
the corresponding external time-slice data. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_finiteReplayState_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older s =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        older s := by
  let w := multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
    arrivalRate harrivalRate i j s
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1
  change stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older s =
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i w older s
  apply stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_pastState_eq
    meanService i z w older s s rfl
  · exact canonicalStationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_pastState_eq
      arrivalRate meanService harrivalRate i j s older hs z hgood
  · exact stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_tag_eq
      arrivalRate meanService harrivalRate i j s z
  · exact canonicalStationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_futureJobs_eq
      arrivalRate meanService harrivalRate i j s hs z hgood

/-- The bounded finite waiting observation is likewise fixed by the exposed
deterministic time slice. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_finiteReplayWaiting_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i z older s =
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
          arrivalRate harrivalRate i j s
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1)
        older s := by
  unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
  rw [stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_finiteReplayState_eq
    arrivalRate meanService harrivalRate i j s older hs z hgood]

/-- The finite tagged-waiting observation evaluated after continuation is a
measurable deterministic-time selector on the external time-slice carrier. -/
noncomputable def stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ) :
    multiclassPalmPassiveClassTimeSliceExternal i j → ℝ := fun x =>
  stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
    (multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
      arrivalRate harrivalRate i j s x) older s

theorem measurable_stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ) :
    Measurable (stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
      arrivalRate meanService harrivalRate i j s older) := by
  simpa [stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector] using
    (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
      meanService i older (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => s)
      measurable_const).comp
      (measurable_multiclassStationaryPoissonWorkClassTaggedPassiveClassFromTimeSliceExternalPastTail
        arrivalRate harrivalRate i j s)

/-- The deterministic finite waiting selector is a numeric indicator. -/
theorem norm_stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector_le_one
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ)
    (x : multiclassPalmPassiveClassTimeSliceExternal i j) :
    ‖stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
      arrivalRate meanService harrivalRate i j s older x‖ ≤ 1 := by
  unfold stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    nonpreemptivePriorityWaitingIdentifierIndicator
  split <;> norm_num

/-- A literal finite replay waiting observation is a numeric indicator. -/
theorem norm_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_le_one
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) :
    ‖stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z older t‖ ≤ 1 := by
  unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    nonpreemptivePriorityWaitingIdentifierIndicator
  split <;> norm_num

/-- Remote finite replays converge in selected-Palm mean at every deterministic
nonnegative clock to the literal tagged queue-wait indicator. -/
theorem tendsto_integral_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto (fun older : ℕ =>
      ∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z (older : ℝ) t
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
      Filter.atTop
      (nhds (∫ z, if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun older z =>
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z (older : ℝ) t
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
  have hmeas : ∀ older, AEStronglyMeasurable (F older) P := by
    intro older
    exact (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
      meanService i (older : ℝ)
      (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => t)
      measurable_const).aestronglyMeasurable
  have hbound : ∀ older, ∀ᵐ z ∂P, ‖F older z‖ ≤ (1 : ℝ) := by
    intro older
    filter_upwards with z
    exact norm_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_le_one
      meanService i z (older : ℝ) t
  have hlim : ∀ᵐ z ∂P, Filter.Tendsto (fun older : ℕ => F older z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator
      arrivalRate meanService harrivalRate hmeanService hstable i t ht] with z hz
    rcases hz with ⟨cutoff, _hcutoff, hcoalescence⟩
    rcases exists_nat_ge cutoff with ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro older holder
    exact hcoalescence (older : ℝ) (hN.trans (by exact_mod_cast holder))
  simpa [P, F, f] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) (fun _ => (1 : ℝ)) hmeas
      (MeasureTheory.integrable_const (μ := P) 1) hbound hlim)

/-- The same selected-Palm remote-past stabilization is valid after
multiplication by the selected customer's integrable service work.  This is
the deterministic-clock work-reward limit used when a finite customer
occupation is transported through Campbell's formula. -/
theorem tendsto_integral_stationaryPriorityClassTaggedWork_mul_finiteReplayWaitingIndicatorBeforeHorizon
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto (fun older : ℕ =>
      ∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z (older : ℝ) t
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
      Filter.atTop
      (nhds (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
        (if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let K := stationaryPriorityClassTaggedWorkRequirement meanService i
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun older z =>
    K z * stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z (older : ℝ) t
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    K z * (if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0)
  have hwork : Integrable K P := by
    simpa [K, P] using
      (integrable_stationaryPriorityClassTaggedWorkRequirement
        arrivalRate meanService harrivalRate hmeanService i)
  have hmeas : ∀ older, AEStronglyMeasurable (F older) P := by
    intro older
    exact hwork.aestronglyMeasurable.mul
      (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
        meanService i (older : ℝ)
        (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => t)
        measurable_const).aestronglyMeasurable
  have hbound : ∀ older, ∀ᵐ z ∂P, ‖F older z‖ ≤ K z := by
    intro older
    filter_upwards [ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hpositive
    have hKnonneg : 0 ≤ K z := by
      rw [show K z = stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 by
        exact stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate meanService i z]
      exact (hpositive i 0).le
    calc
      ‖F older z‖ = ‖K z‖ * ‖stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z (older : ℝ) t‖ := by
            dsimp [F]
            rw [abs_mul]
      _ = K z * ‖stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z (older : ℝ) t‖ := by
            rw [Real.norm_of_nonneg hKnonneg]
      _ ≤ K z * 1 := by
            exact mul_le_mul_of_nonneg_left
              (norm_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_le_one
                meanService i z (older : ℝ) t) hKnonneg
      _ = K z := mul_one _
  have hlim : ∀ᵐ z ∂P, Filter.Tendsto (fun older : ℕ => F older z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator
      arrivalRate meanService harrivalRate hmeanService hstable i t ht] with z hz
    rcases hz with ⟨cutoff, _hcutoff, hcoalescence⟩
    rcases exists_nat_ge cutoff with ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro older holder
    dsimp [F, f]
    rw [hcoalescence (older : ℝ) (hN.trans (by exact_mod_cast holder))]
  simpa [P, K, F, f] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) K hmeas hwork hbound hlim)

/-- The finite deterministic-time compensation integrands converge in
selected-Palm mean to the literal queue-wait indicator times the following
passive-class arrival count.  The fixed count is integrable, so the same
remote-past stabilization admits a count-valued dominating function. -/
theorem tendsto_integral_stationaryPriorityClassTaggedFiniteReplayWaiting_mul_arrivalCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s h : ℝ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) :
    Filter.Tendsto (fun older : ℕ =>
      ∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z (older : ℝ) s *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
      Filter.atTop
      (nhds (∫ z, (if s < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  let K : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    (Probability.PoissonProcess.canonicalRenewalCount h
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun older z =>
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z (older : ℝ) s * K z
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    (if s < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) * K z
  have hcount : Integrable K P := by
    simpa [K, P] using
      (integrable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
        arrivalRate harrivalRate i j s h hs hh (fun _ => (1 : ℝ)) measurable_const
        1 (by norm_num) (fun _ => by norm_num))
  have hmeas : ∀ older, AEStronglyMeasurable (F older) P := by
    intro older
    exact (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
      meanService i (older : ℝ)
      (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => s)
      measurable_const).aestronglyMeasurable.mul hcount.aestronglyMeasurable
  have hbound : ∀ older, ∀ᵐ z ∂P, ‖F older z‖ ≤ K z := by
    intro older
    filter_upwards with z
    have hKnonneg : 0 ≤ K z := by
      exact Nat.cast_nonneg _
    calc
      ‖F older z‖ = ‖stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z (older : ℝ) s‖ * ‖K z‖ := by
            change ‖stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
              meanService i z (older : ℝ) s * K z‖ = _
            rw [norm_mul]
      _ = ‖stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z (older : ℝ) s‖ * K z := by
            rw [Real.norm_of_nonneg hKnonneg]
      _ ≤ 1 * K z := by
            exact mul_le_mul_of_nonneg_right
              (norm_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_le_one
                meanService i z (older : ℝ) s) hKnonneg
      _ = K z := one_mul _
  have hlim : ∀ᵐ z ∂P, Filter.Tendsto (fun older : ℕ => F older z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator
      arrivalRate meanService harrivalRate hmeanService hstable i s hs] with z hz
    rcases hz with ⟨cutoff, _hcutoff, hcoalescence⟩
    rcases exists_nat_ge cutoff with ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro older holder
    dsimp [F, f]
    rw [hcoalescence (older : ℝ) (hN.trans (by exact_mod_cast holder))]
  simpa [P, F, f, K] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) K hmeas hcount hbound hlim)

/-- On a good selected suspension, the external time-slice selector evaluates
to the literal finite tagged-waiting observation. -/
theorem stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector_apply_factor
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s older : ℝ) (hs : 0 ≤ s)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
      arrivalRate meanService harrivalRate i j s older
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).1 =
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i z older s := by
  symm
  exact stationaryPriorityClassTaggedPassiveClassTimeSliceExternalPastTail_finiteReplayWaiting_eq
    arrivalRate meanService harrivalRate i j s older hs z hgood

/-- Deterministic-interval Palm compensation for a bounded finite tagged
waiting observation.  The next isolated-class arrival count has conditional
mean `arrivalRate j * h` even when the selector uses the complete queue
history exposed by the left endpoint `s`. -/
theorem integral_stationaryPriorityClassTaggedFiniteReplayWaiting_mul_arrivalCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s h older : ℝ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older s *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older s
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
        (arrivalRate j.1 * h) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let F := multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s
  let f := stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
    arrivalRate meanService harrivalRate i j s older
  have hselector : ∀ᵐ z ∂P,
      f (F z).1 =
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i z older s := by
    filter_upwards [ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hgood
    exact stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector_apply_factor
      arrivalRate meanService harrivalRate i j s older hs z hgood
  have hgeneral :=
    integral_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount
      arrivalRate harrivalRate i j s h hs hh f
      (measurable_stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
        arrivalRate meanService harrivalRate i j s older)
  change (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z older s * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) ∂P) =
    (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z older s ∂P) * (arrivalRate j.1 * h)
  calc
    (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older s * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) ∂P) =
      ∫ z, f (F z).1 * (Probability.PoissonProcess.canonicalRenewalCount h (F z).2 : ℝ) ∂P := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hselector] with z hz
        rw [hz]
    _ = (∫ z, f (F z).1 ∂P) * (arrivalRate j.1 * h) := by
      simpa [F, P, f] using hgeneral
    _ = (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older s ∂P) * (arrivalRate j.1 * h) := by
      apply congrArg (fun x : ℝ => x * (arrivalRate j.1 * h))
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hselector] with z hz
      rw [hz]

/-- Finite-grid deterministic-time compensation for the literal finite
tagged-waiting observations.  This is the count-level precursor to the
stopped marked-work argument. -/
theorem integral_sum_stationaryPriorityClassTaggedFiniteReplayWaiting_mul_arrivalCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (width older : ℝ)
    (hwidth : 0 ≤ width) (N : ℕ) :
    ∫ z, ∑ r ∈ Finset.range N,
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older ((r : ℝ) * width) *
        (Probability.PoissonProcess.canonicalRenewalCount width
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j ((r : ℝ) * width) z).2 : ℝ)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∑ r ∈ Finset.range N,
        (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older ((r : ℝ) * width)
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
          (arrivalRate j.1 * width) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i →
      multiclassPalmPassiveClassTimeSliceExternal i j × (ℕ → ℝ) := fun r =>
    multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j
      ((r : ℝ) * width)
  let f : ℕ → multiclassPalmPassiveClassTimeSliceExternal i j → ℝ := fun r =>
    stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
      arrivalRate meanService harrivalRate i j ((r : ℝ) * width) older
  have hselector : ∀ r, ∀ᵐ z ∂P,
      f r (F r z).1 =
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older ((r : ℝ) * width) := by
    intro r
    filter_upwards [ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hgood
    exact stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector_apply_factor
      arrivalRate meanService harrivalRate i j ((r : ℝ) * width) older
        (mul_nonneg (Nat.cast_nonneg r) hwidth) z hgood
  have hselectorAll : ∀ᵐ z ∂P, ∀ r ∈ Finset.range N,
      f r (F r z).1 =
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older ((r : ℝ) * width) := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact hselector r
  have hgeneral :=
    integral_sum_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
      arrivalRate harrivalRate i j width hwidth N f
      (fun r =>
        measurable_stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector
          arrivalRate meanService harrivalRate i j ((r : ℝ) * width) older)
      1 (by norm_num) (fun r x =>
        norm_stationaryPriorityClassTaggedPassiveClassTimeSliceFiniteReplayWaitingSelector_le_one
          arrivalRate meanService harrivalRate i j ((r : ℝ) * width) older x)
  change (∫ z, ∑ r ∈ Finset.range N,
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older ((r : ℝ) * width) *
        (Probability.PoissonProcess.canonicalRenewalCount width (F r z).2 : ℝ) ∂P) =
      ∑ r ∈ Finset.range N,
        (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older ((r : ℝ) * width) ∂P) * (arrivalRate j.1 * width)
  calc
    (∫ z, ∑ r ∈ Finset.range N,
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older ((r : ℝ) * width) *
          (Probability.PoissonProcess.canonicalRenewalCount width (F r z).2 : ℝ) ∂P) =
      ∫ z, ∑ r ∈ Finset.range N,
        f r (F r z).1 * (Probability.PoissonProcess.canonicalRenewalCount width (F r z).2 : ℝ) ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hselectorAll] with z hz
          apply Finset.sum_congr rfl
          intro r hr
          rw [hz r hr]
    _ = ∑ r ∈ Finset.range N,
        (∫ z, f r (F r z).1 ∂P) * (arrivalRate j.1 * width) := by
          simpa [F, f, P] using hgeneral
    _ = ∑ r ∈ Finset.range N,
        (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older ((r : ℝ) * width) ∂P) * (arrivalRate j.1 * width) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact congrArg (fun x : ℝ => x * (arrivalRate j.1 * width))
            (MeasureTheory.integral_congr_ae (hselector r))

/-- Literal selected-Palm deterministic-interval compensation.  While the
tagged customer is still waiting at a fixed clock `s`, the expected number of
following passive-class arrivals in the next interval is its waiting
probability times the Poisson exposure. -/
theorem integral_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s h : ℝ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ∫ z, (if s < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
      (Probability.PoissonProcess.canonicalRenewalCount h
        (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∫ z, if s < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
        (arrivalRate j.1 * h) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hleft :=
    tendsto_integral_stationaryPriorityClassTaggedFiniteReplayWaiting_mul_arrivalCount
      arrivalRate meanService harrivalRate hmeanService hstable i j s h hs hh
  have hwaiting :=
    tendsto_integral_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      arrivalRate meanService harrivalRate hmeanService hstable i s hs
  have hright : Filter.Tendsto (fun older : ℕ =>
      (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z (older : ℝ) s ∂P) * (arrivalRate j.1 * h))
      Filter.atTop
      (nhds ((∫ z, if s < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
        ∂P) * (arrivalRate j.1 * h))) := by
    simpa [P] using hwaiting.mul tendsto_const_nhds
  have hfinite : ∀ older : ℕ,
      (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z (older : ℝ) s *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
        ∂P) =
      (∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z (older : ℝ) s ∂P) * (arrivalRate j.1 * h) := by
    intro older
    simpa [P] using
      (integral_stationaryPriorityClassTaggedFiniteReplayWaiting_mul_arrivalCount
        arrivalRate meanService harrivalRate i j s h (older : ℝ) hs hh)
  have hright' : Filter.Tendsto (fun older : ℕ =>
      ∫ z, stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z (older : ℝ) s *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
        ∂P)
      Filter.atTop
      (nhds ((∫ z, if s < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
        ∂P) * (arrivalRate j.1 * h))) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall (fun older => (hfinite older).symm)
  simpa [P] using tendsto_nhds_unique hleft hright'

/-- The literal queue-wait indicator times a following fixed-interval arrival
count is integrable.  This is the analytic premise needed to add the genuine
selected-Palm compensation identities over finite deterministic grids. -/
theorem integrable_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (s h : ℝ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) :
    Integrable (fun z =>
      (if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) *
        (Probability.PoissonProcess.canonicalRenewalCount h
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let K : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    (Probability.PoissonProcess.canonicalRenewalCount h
      (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor i j s z).2 : ℝ)
  change Integrable (fun z =>
    (if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) * K z) P
  have hcount : Integrable K P := by
    simpa [K, P] using
      (integrable_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceSelector_mul_arrivalCount_of_norm_le
        arrivalRate harrivalRate i j s h hs hh (fun _ => (1 : ℝ)) measurable_const
        1 (by norm_num) (fun _ => by norm_num))
  have hqueue : AEMeasurable (stationaryPriorityClassTaggedQueueWait meanService i) P := by
    simpa [P] using aemeasurable_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hindicator : AEMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) P := by
    have hset : NullMeasurableSet
        {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
          s < stationaryPriorityClassTaggedQueueWait meanService i z} P :=
      nullMeasurableSet_lt aemeasurable_const hqueue
    let g : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
      {z | s < stationaryPriorityClassTaggedQueueWait meanService i z}.indicator (fun _ => (1 : ℝ))
    have hg : AEMeasurable g P := by
      exact (aemeasurable_const : AEMeasurable
        (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => (1 : ℝ)) P).indicator₀ hset
    have hEq : g =ᵐ[P] (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
        if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) := by
      filter_upwards with z
      by_cases hz : s < stationaryPriorityClassTaggedQueueWait meanService i z
      · simp [g, hz]
      · simp [g, hz]
    exact hg.congr hEq
  have hKmeas : AEStronglyMeasurable K P := hcount.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun z =>
      (if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) * K z) P :=
    by simpa only [Pi.mul_apply] using hindicator.aestronglyMeasurable.mul hKmeas
  refine Integrable.mono' hcount hmeas ?_
  filter_upwards with z
  have hKnonneg : 0 ≤ K z := Nat.cast_nonneg _
  calc
    ‖(if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) * K z‖ =
        ‖if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0‖ * ‖K z‖ :=
      norm_mul _ _
    _ = ‖if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0‖ * K z := by
      rw [Real.norm_of_nonneg hKnonneg]
    _ ≤ 1 * K z := by
      apply mul_le_mul_of_nonneg_right
      · split <;> norm_num
      · exact hKnonneg
    _ = K z := one_mul _

/-- On every deterministic grid cell, the fresh factor count in the
selected-Palm compensation identity is the cardinality of the corresponding
literal right-closed passive-arrival window. -/
theorem sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount_eq_card_windows
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (width : ℝ) (hwidth : 0 ≤ width) (N : ℕ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    ∑ r ∈ Finset.range N,
      (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
        (Probability.PoissonProcess.canonicalRenewalCount width
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j ((r : ℝ) * width) z).2 : ℝ) =
      ∑ r ∈ Finset.range N,
        (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
          ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
            ((r : ℝ) * width) (((r + 1 : ℕ) : ℝ) * width) (z.2 j).1).card : ℝ) := by
  apply Finset.sum_congr rfl
  intro r hr
  have hs : 0 ≤ (r : ℝ) * width :=
    mul_nonneg (Nat.cast_nonneg r) hwidth
  rw [canonicalRenewalCount_multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor_eq_card_rightClosed
    i j ((r : ℝ) * width) width hs hwidth z]
  have hright : (r : ℝ) * width + width = ((r + 1 : ℕ) : ℝ) * width := by
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hright]

/-- For a positive deterministic grid, the cells whose left endpoints precede
the queue-wait horizon form an initial segment.  Their literal right-closed
arrival windows therefore telescope to the count through the grid-rounded
horizon. -/
theorem sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount_eq_card_rightGridHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (width : ℝ) (hwidth : 0 < width) (N : ℕ)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    ∑ r ∈ Finset.range N,
      (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
        (Probability.PoissonProcess.canonicalRenewalCount width
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j ((r : ℝ) * width) z).2 : ℝ) =
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 (((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) * width)
        (z.2 j).1).card : ℝ) := by
  classical
  let w := stationaryPriorityClassTaggedQueueWait meanService i z
  let M : ℕ := min N (Nat.ceil (w / width))
  let F : ℕ → ℝ := fun r =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
      ((r : ℝ) * width) (((r + 1 : ℕ) : ℝ) * width) (z.2 j).1).card : ℝ)
  let g : ℕ → ℝ := fun r => if r < M then F r else 0
  rw [sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount_eq_card_windows
    meanService i j width hwidth.le N z]
  change ∑ r ∈ Finset.range N,
      (if (r : ℝ) * width < w then 1 else 0) * F r =
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 ((M : ℝ) * width) (z.2 j).1).card : ℝ)
  have hM : M ≤ N := by
    exact min_le_left _ _
  have hindicator : ∀ r : ℕ, r < N → ((r : ℝ) * width < w ↔ r < M) := by
    intro r hr
    constructor
    · intro h
      have hceil : r < Nat.ceil (w / width) := by
        rw [Nat.lt_ceil]
        exact (lt_div_iff₀ hwidth).2 h
      simpa [M] using (lt_min_iff.mpr ⟨hr, hceil⟩)
    · intro h
      have hmin : r < min N (Nat.ceil (w / width)) := by simpa [M] using h
      have hceil : r < Nat.ceil (w / width) := (lt_min_iff.mp hmin).2
      exact (lt_div_iff₀ hwidth).1 (by simpa only [Nat.lt_ceil] using hceil)
  have hsum : (∑ r ∈ Finset.range M, g r) = ∑ r ∈ Finset.range N, g r := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
    intro r hr hnot
    simp only [g]
    rw [if_neg]
    intro hrM
    exact hnot (Finset.mem_range.mpr hrM)
  have hgrid := Probability.PoissonProcess.card_suspensionBaseArrivalIndicesRightClosed_grid
    0 width (z.2 j).1 hwidth.le M
  have hgrid' :
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 ((M : ℝ) * width) (z.2 j).1).card : ℝ) =
        ∑ r ∈ Finset.range M, F r := by
    simp only [F]
    rw [← Nat.cast_sum]
    exact_mod_cast (by simpa using hgrid)
  calc
    ∑ r ∈ Finset.range N, (if (r : ℝ) * width < w then 1 else 0) * F r =
        ∑ r ∈ Finset.range N, g r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hiff := hindicator r (Finset.mem_range.mp hr)
          by_cases hrM : r < M
          · have hleft : (r : ℝ) * width < w := hiff.mpr hrM
            simp [g, hrM, hleft]
          · have hleft : ¬ (r : ℝ) * width < w := by
              intro h
              exact hrM (hiff.mp h)
            simp [g, hrM, hleft]
    _ = ∑ r ∈ Finset.range M, g r := hsum.symm
    _ = ∑ r ∈ Finset.range M, F r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [g, Finset.mem_range.mp hr]
    _ = ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
      0 ((M : ℝ) * width) (z.2 j).1).card : ℝ) := hgrid'.symm

/-- Finite-grid selected-Palm compensation for the literal queue-wait
indicator.  Each interval is exposed only through its deterministic left
endpoint, so the grid can be summed without an unproved random-horizon
stopping theorem. -/
theorem integral_sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (width : ℝ)
    (hwidth : 0 ≤ width) (N : ℕ) :
    ∫ z, ∑ r ∈ Finset.range N,
      (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
        (Probability.PoissonProcess.canonicalRenewalCount width
          (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
            i j ((r : ℝ) * width) z).2 : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∑ r ∈ Finset.range N,
        (∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
          (arrivalRate j.1 * width) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro r hr
    simpa [P] using
      (integral_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
        arrivalRate meanService harrivalRate hmeanService hstable i j ((r : ℝ) * width) width
        (mul_nonneg (Nat.cast_nonneg r) hwidth) hwidth)
  · intro r hr
    simpa [P] using
      (integrable_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
        arrivalRate meanService harrivalRate hmeanService hstable i j ((r : ℝ) * width) width
        (mul_nonneg (Nat.cast_nonneg r) hwidth) hwidth)

/-- At every fixed positive grid and finite cap, the expected literal passive
arrival count through the right-rounded queue-wait horizon is the exact sum
of deterministic-cell Poisson exposures.  No limit or random-horizon
compensation interchange is used here. -/
theorem integral_stationaryPriorityClassTaggedPassiveFutureCount_rightGridHorizon_eq_sum_exposure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (width : ℝ) (hwidth : 0 < width) (N : ℕ) :
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
      0 (((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) * width)
      (z.2 j).1).card : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∑ r ∈ Finset.range N,
        (∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) *
          (arrivalRate j.1 * width) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  calc
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
      0 (((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) * width)
      (z.2 j).1).card : ℝ) ∂P =
        ∫ z, ∑ r ∈ Finset.range N,
          (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
            (Probability.PoissonProcess.canonicalRenewalCount width
              (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
                i j ((r : ℝ) * width) z).2 : ℝ) ∂P := by
          apply integral_congr_ae
          filter_upwards with z
          exact (sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount_eq_card_rightGridHorizon
            meanService i j width hwidth N z).symm
    _ = ∑ r ∈ Finset.range N,
        (∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 ∂P) *
          (arrivalRate j.1 * width) := by
          simpa [P] using
            (integral_sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
              arrivalRate meanService harrivalRate hmeanService hstable i j width hwidth.le N)

/-- A capped reciprocal grid horizon is the minimum of its deterministic cap
and the right-rounded input. -/
theorem capped_reciprocal_rightGridHorizon_eq_min
    (T m : ℕ) (w : ℝ) :
    ((min ((m + 1) * T) (Nat.ceil (w / (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ)) =
      min (T : ℝ)
        ((Nat.ceil (w * ((m + 1 : ℕ) : ℝ)) : ℝ) /
          ((m + 1 : ℕ) : ℝ)) := by
  have hkpos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hkne : ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hkpos
  rw [Nat.cast_min, Nat.cast_mul]
  rw [show w / (1 / ((m + 1 : ℕ) : ℝ)) = w * ((m + 1 : ℕ) : ℝ) by
    field_simp]
  rw [min_mul_of_nonneg _ _ (by positivity : 0 ≤ (1 / ((m + 1 : ℕ) : ℝ)))]
  congr 1
  · field_simp
  · simp [div_eq_mul_inv]

/-- Refining a capped reciprocal grid sends its right-rounded horizon to the
capped input. -/
theorem tendsto_capped_reciprocal_rightGridHorizon
    (T : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    Filter.Tendsto (fun m : ℕ =>
      ((min ((m + 1) * T) (Nat.ceil (w / (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ))) Filter.atTop (nhds (min (T : ℝ) w)) := by
  have hrewrite : (fun m : ℕ =>
      ((min ((m + 1) * T) (Nat.ceil (w / (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ))) =
      (fun m : ℕ => min (T : ℝ)
        ((Nat.ceil (w * ((m + 1 : ℕ) : ℝ)) : ℝ) / ((m + 1 : ℕ) : ℝ))) := by
    funext m
    exact capped_reciprocal_rightGridHorizon_eq_min T m w
  rw [hrewrite]
  exact Filter.Tendsto.min tendsto_const_nhds
    (AppliedModelingLib.Math.tendsto_nat_ceil_mul_succ_cast_div hw)

/-- A capped reciprocal right-grid horizon lies weakly above its capped input. -/
theorem min_le_capped_reciprocal_rightGridHorizon
    (T m : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    min (T : ℝ) w ≤
      ((min ((m + 1) * T) (Nat.ceil (w / (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ)) := by
  rw [capped_reciprocal_rightGridHorizon_eq_min]
  apply min_le_min_left
  have hkpos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hkpos]
  exact Nat.le_ceil _

/-- A capped reciprocal right-grid horizon never exceeds its deterministic cap. -/
theorem capped_reciprocal_rightGridHorizon_le_cap
    (T m : ℕ) (w : ℝ) :
    ((min ((m + 1) * T) (Nat.ceil (w / (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ)) ≤ T := by
  rw [capped_reciprocal_rightGridHorizon_eq_min]
  exact min_le_left _ _

/-- The deterministic grid cells whose left endpoints precede a queue-wait
clock form precisely the initial segment selected by the upward rounding. -/
theorem sum_stationaryPriorityClassTaggedQueueWaitIndicators_eq_capped_ceil
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (width : ℝ) (hwidth : 0 < width)
    (N : ℕ) (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    ∑ r ∈ Finset.range N,
      (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) =
      (min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℝ) := by
  classical
  let w := stationaryPriorityClassTaggedQueueWait meanService i z
  let M : ℕ := min N (Nat.ceil (w / width))
  let g : ℕ → ℝ := fun r => if r < M then 1 else 0
  have hM : M ≤ N := min_le_left _ _
  have hindicator : ∀ r : ℕ, r < N → ((r : ℝ) * width < w ↔ r < M) := by
    intro r hr
    constructor
    · intro h
      have hceil : r < Nat.ceil (w / width) := by
        rw [Nat.lt_ceil]
        exact (lt_div_iff₀ hwidth).2 h
      simpa [M] using (lt_min_iff.mpr ⟨hr, hceil⟩)
    · intro h
      have hmin : r < min N (Nat.ceil (w / width)) := by simpa [M] using h
      have hceil : r < Nat.ceil (w / width) := (lt_min_iff.mp hmin).2
      exact (lt_div_iff₀ hwidth).1 (by simpa only [Nat.lt_ceil] using hceil)
  have hsum : (∑ r ∈ Finset.range M, g r) = ∑ r ∈ Finset.range N, g r := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
    intro r hr hnot
    simp only [g]
    rw [if_neg]
    intro hrM
    exact hnot (Finset.mem_range.mpr hrM)
  calc
    ∑ r ∈ Finset.range N, (if (r : ℝ) * width < w then 1 else 0) =
        ∑ r ∈ Finset.range N, g r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hiff := hindicator r (Finset.mem_range.mp hr)
          by_cases hrM : r < M
          · have hleft : (r : ℝ) * width < w := hiff.mpr hrM
            simp [g, hrM, hleft]
          · have hleft : ¬ (r : ℝ) * width < w := by
              intro h
              exact hrM (hiff.mp h)
            simp [g, hrM, hleft]
    _ = ∑ r ∈ Finset.range M, g r := hsum.symm
    _ = ∑ r ∈ Finset.range M, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [g, Finset.mem_range.mp hr]
    _ = (min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℝ) := by
      simp [M, w, Nat.cast_min]

/-- A capped grid horizon is the total width of the deterministic cells whose
left endpoints precede the queue-wait clock. -/
theorem capped_reciprocal_rightGridHorizon_eq_sum_queueWaitIndicators
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (width : ℝ) (hwidth : 0 < width)
    (N : ℕ) (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    ((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
        width =
      ∑ r ∈ Finset.range N,
        (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
          width := by
  rw [← Finset.sum_mul]
  rw [sum_stationaryPriorityClassTaggedQueueWaitIndicators_eq_capped_ceil
    meanService i width hwidth N z]
  rw [Nat.cast_min]

/-- A deterministic strict queue-wait indicator is integrable under the
selected-arrival Palm law. -/
theorem integrable_stationaryPriorityClassTaggedQueueWaitIndicator
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (s : ℝ) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  have hqueue : AEMeasurable (stationaryPriorityClassTaggedQueueWait meanService i) P := by
    simpa [P] using aemeasurable_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hset : NullMeasurableSet
      {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
        s < stationaryPriorityClassTaggedQueueWait meanService i z} P :=
    nullMeasurableSet_lt aemeasurable_const hqueue
  let g : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
    {z | s < stationaryPriorityClassTaggedQueueWait meanService i z}.indicator (fun _ => (1 : ℝ))
  have hg : AEMeasurable g P :=
    (aemeasurable_const : AEMeasurable
      (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => (1 : ℝ)) P).indicator₀ hset
  have hEq : g =ᵐ[P] (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) := by
    filter_upwards with z
    by_cases hz : s < stationaryPriorityClassTaggedQueueWait meanService i z <;> simp [g, hz]
  have hmeas : AEStronglyMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      if s < stationaryPriorityClassTaggedQueueWait meanService i z then (1 : ℝ) else 0) P :=
    hg.congr hEq |>.aestronglyMeasurable
  refine Integrable.mono' (MeasureTheory.integrable_const (μ := P) 1) hmeas ?_
  filter_upwards with z
  split <;> norm_num

/-- The expected capped grid horizon is the finite sum of its deterministic
cell-exposure probabilities times the cell width. -/
theorem integral_cappedRightGridHorizon_eq_sum_queueWaitIndicator
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (width : ℝ) (hwidth : 0 < width) (N : ℕ) :
    ∫ z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i,
      ((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
        width
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∑ r ∈ Finset.range N,
        (∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) * width := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  calc
    ∫ z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i,
        ((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
          width ∂P =
        ∫ z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i,
          ∑ r ∈ Finset.range N,
            (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
              width ∂P := by
          apply integral_congr_ae
          filter_upwards with z
          exact capped_reciprocal_rightGridHorizon_eq_sum_queueWaitIndicators
            meanService i width hwidth N z
    _ = ∑ r ∈ Finset.range N,
        ∫ z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i,
          (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
            width ∂P := by
          rw [MeasureTheory.integral_finset_sum]
          intro r hr
          exact (integrable_stationaryPriorityClassTaggedQueueWaitIndicator
            arrivalRate meanService harrivalRate hmeanService hstable i ((r : ℝ) * width)).mul_const width
    _ = ∑ r ∈ Finset.range N,
        (∫ z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i,
          if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 ∂P) *
            width := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [MeasureTheory.integral_mul_const]

/-- At every finite positive grid, selected-Palm passive-count compensation is
exactly the passive arrival rate times the expected capped grid horizon. -/
theorem integral_stationaryPriorityClassTaggedPassiveRightGridCard_eq_rate_mul_integral_horizon
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (width : ℝ) (hwidth : 0 < width) (N : ℕ) :
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
        width) (z.2 j).1).card : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate j.1 *
        (∫ z, ((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
          width
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  calc
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
        width) (z.2 j).1).card : ℝ) ∂P =
        ∑ r ∈ Finset.range N,
          (∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
            ∂P) * (arrivalRate j.1 * width) := by
          simpa [P] using
            (integral_stationaryPriorityClassTaggedPassiveFutureCount_rightGridHorizon_eq_sum_exposure
              arrivalRate meanService harrivalRate hmeanService hstable i j width hwidth N)
    _ = ∑ r ∈ Finset.range N,
        arrivalRate j.1 *
          ((∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
            ∂P) * width) := by
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = arrivalRate j.1 *
        ∑ r ∈ Finset.range N,
          ((∫ z, if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0
            ∂P) * width) := by
          rw [Finset.mul_sum]
    _ = arrivalRate j.1 *
        (∫ z, ((min N (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z / width)) : ℕ) : ℝ) *
          width ∂P) := by
          rw [integral_cappedRightGridHorizon_eq_sum_queueWaitIndicator
            arrivalRate meanService harrivalRate hmeanService hstable i width hwidth N]

/-- Each capped reciprocal grid horizon is integrable under the selected
arrival Palm law. -/
theorem integrable_cappedReciprocalRightGridHorizon
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (T m : ℕ) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ)))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let width : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
  let N : ℕ := (m + 1) * T
  have hwidth : 0 < width := by
    dsimp [width]
    positivity
  have hsum : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ∑ r ∈ Finset.range N,
        (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
          width) P := by
    refine MeasureTheory.integrable_finset_sum (Finset.range N) ?_
    intro r hr
    exact (integrable_stationaryPriorityClassTaggedQueueWaitIndicator
      arrivalRate meanService harrivalRate hmeanService hstable i ((r : ℝ) * width)).mul_const width
  apply hsum.congr
  filter_upwards with z
  simpa [P, N, width] using
    (capped_reciprocal_rightGridHorizon_eq_sum_queueWaitIndicators
      meanService i width hwidth N z).symm

/-- The expected capped reciprocal grid horizon converges to the expected
capped queue-wait clock. -/
theorem tendsto_integral_cappedReciprocalRightGridHorizon
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (T : ℕ) :
    Filter.Tendsto (fun m : ℕ =>
      ∫ z, ((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
          (1 / ((m + 1 : ℕ) : ℝ))
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
      Filter.atTop
      (nhds (∫ z, min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun m z =>
    ((min ((m + 1) * T)
      (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
        (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ))
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)
  have hmeas : ∀ m, AEStronglyMeasurable (F m) P := by
    intro m
    simpa [F, P] using
      (integrable_cappedReciprocalRightGridHorizon
        arrivalRate meanService harrivalRate hmeanService hstable i T m).aestronglyMeasurable
  have hbound : ∀ m, ∀ᵐ z ∂P, ‖F m z‖ ≤ (T : ℝ) := by
    intro m
    filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
    have hnonneg : 0 ≤ F m z := by
      exact (le_min (Nat.cast_nonneg T) hwait).trans
        (min_le_capped_reciprocal_rightGridHorizon T m hwait)
    calc
      ‖F m z‖ = F m z := Real.norm_of_nonneg hnonneg
      _ ≤ T := capped_reciprocal_rightGridHorizon_le_cap T m
        (stationaryPriorityClassTaggedQueueWait meanService i z)
  have hlim : ∀ᵐ z ∂P, Filter.Tendsto (fun m : ℕ => F m z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
    simpa [F, f] using tendsto_capped_reciprocal_rightGridHorizon T hwait
  simpa [P, F, f] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) (fun _ => (T : ℝ)) hmeas
      (MeasureTheory.integrable_const (μ := P) (T : ℝ)) hbound hlim)

/-- Along capped reciprocal grids, a literal passive physical arrival count
converges to the count at the capped queue-wait clock. -/
theorem tendsto_multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_capped_reciprocal_rightGridHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (T : ℕ) (hwait : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z) :
    Filter.Tendsto (fun m : ℕ =>
      (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j
        (((min ((m + 1) * T)
          (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
            (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
            (1 / ((m + 1 : ℕ) : ℝ))) : ℝ)) Filter.atTop
      (nhds (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j
        (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)) : ℝ)) := by
  unfold multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
  exact Probability.PoissonProcess.tendsto_coe_suspensionBaseFutureCount_of_tendsto_from_right
    (z.2 j).1 (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
    (fun m : ℕ =>
      ((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ)))
    (tendsto_capped_reciprocal_rightGridHorizon T hwait)
    (fun m => min_le_capped_reciprocal_rightGridHorizon T m hwait)

/-- At each fixed capped reciprocal grid, the literal right-closed passive
arrival count is integrable under the selected-arrival Palm law. -/
theorem integrable_stationaryPriorityClassTaggedPassiveRightGridCard
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (T m : ℕ) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (((min ((m + 1) * T)
          (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
            (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
            (1 / ((m + 1 : ℕ) : ℝ)))
        (z.2 j).1).card : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let width : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
  let N : ℕ := (m + 1) * T
  have hwidth : 0 ≤ width := by
    dsimp [width]
    positivity
  have hwidthpos : 0 < width := by
    dsimp [width]
    positivity
  have hsum : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ∑ r ∈ Finset.range N,
        (if (r : ℝ) * width < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0) *
          (Probability.PoissonProcess.canonicalRenewalCount width
            (multiclassStationaryPoissonWorkClassTaggedPassiveClassTimeSliceFactor
              i j ((r : ℝ) * width) z).2 : ℝ)) P := by
    refine MeasureTheory.integrable_finset_sum (Finset.range N) ?_
    intro r hr
    exact integrable_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount
      arrivalRate meanService harrivalRate hmeanService hstable i j ((r : ℝ) * width) width
      (mul_nonneg (Nat.cast_nonneg r) hwidth) hwidth
  apply hsum.congr
  filter_upwards with z
  simpa [P, N, width] using
    (sum_stationaryPriorityClassTaggedQueueWaitIndicator_mul_arrivalCount_eq_card_rightGridHorizon
      meanService i j width hwidthpos N z)

/-- Along capped reciprocal grids, the literal right-closed passive-arrival
ledger count converges to the count at the capped queue-wait clock. -/
theorem tendsto_stationaryPriorityClassTaggedPassiveRightGridCard
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (T : ℕ) (hwait : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z) :
    Filter.Tendsto (fun m : ℕ =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (((min ((m + 1) * T)
          (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
            (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
            (1 / ((m + 1 : ℕ) : ℝ)))
        (z.2 j).1).card : ℝ)) Filter.atTop
      (nhds ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
        (z.2 j).1).card : ℝ)) := by
  let w := stationaryPriorityClassTaggedQueueWait meanService i z
  let s : ℝ := min (T : ℝ) w
  let H : ℕ → ℝ := fun m =>
    ((min ((m + 1) * T)
      (Nat.ceil (w / (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
      (1 / ((m + 1 : ℕ) : ℝ))
  have hs : 0 ≤ s := le_min (Nat.cast_nonneg T) hwait
  have hH : ∀ m, 0 ≤ H m := by
    intro m
    exact (le_min (Nat.cast_nonneg T) hwait).trans
      (min_le_capped_reciprocal_rightGridHorizon T m hwait)
  have hcount :=
    tendsto_multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_capped_reciprocal_rightGridHorizon
      meanService i j z T hwait
  change Filter.Tendsto (fun m : ℕ =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 (H m)
        (z.2 j).1).card : ℝ)) Filter.atTop
      (nhds ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 s
        (z.2 j).1).card : ℝ))
  unfold multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount at hcount
  have htarget : Filter.Tendsto (fun m : ℕ =>
      (Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1 (H m) : ℝ))
      Filter.atTop
      (nhds ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 s
        (z.2 j).1).card : ℝ)) := by
    rw [Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount
      (z.2 j).1 s hs]
    exact hcount
  apply htarget.congr'
  filter_upwards with m
  exact congrArg (fun count : ℕ => (count : ℝ))
    (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount
      (z.2 j).1 (H m) (hH m)).symm

/-- The selected-Palm expectations of capped reciprocal-grid passive counts
converge to the expectation at the capped queue-wait horizon. -/
theorem tendsto_integral_stationaryPriorityClassTaggedPassiveRightGridCard
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (T : ℕ) :
    Filter.Tendsto (fun m : ℕ =>
      ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (((min ((m + 1) * T)
          (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
            (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
            (1 / ((m + 1 : ℕ) : ℝ)))
        (z.2 j).1).card : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
      Filter.atTop
      (nhds (∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
        (z.2 j).1).card : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun m z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
          (1 / ((m + 1 : ℕ) : ℝ)))
      (z.2 j).1).card : ℝ)
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
      (z.2 j).1).card : ℝ)
  let K : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (T : ℝ) : ℝ)
  have hmeas : ∀ m, AEStronglyMeasurable (F m) P := by
    intro m
    simpa [F, P] using
      (integrable_stationaryPriorityClassTaggedPassiveRightGridCard
        arrivalRate meanService harrivalRate hmeanService hstable i j T m).aestronglyMeasurable
  have hK : Integrable K P := by
    simpa [K, P] using
      (integrable_multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
        arrivalRate harrivalRate i j (T : ℝ) (Nat.cast_nonneg T))
  have hbound : ∀ m, ∀ᵐ z ∂P, ‖F m z‖ ≤ K z := by
    intro m
    filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
    let H : ℝ :=
      ((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
        (1 / ((m + 1 : ℕ) : ℝ))
    have hH : 0 ≤ H := by
      exact (le_min (Nat.cast_nonneg T) hwait).trans
        (min_le_capped_reciprocal_rightGridHorizon T m hwait)
    have hHT : H ≤ T := by
      exact capped_reciprocal_rightGridHorizon_le_cap T m
        (stationaryPriorityClassTaggedQueueWait meanService i z)
    have hcountNat :
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j H ≤
          multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (T : ℝ) := by
      unfold multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
      exact (Probability.PoissonProcess.monotone_suspensionBaseFutureCount (z.2 j).1) hHT
    have hcount :
        (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j H : ℝ) ≤ K z := by
      change (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j H : ℝ) ≤
        (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (T : ℝ) : ℝ)
      exact_mod_cast hcountNat
    have hcard :
        ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 H
          (z.2 j).1).card : ℝ) =
          (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j H : ℝ) := by
      exact congrArg (fun count : ℕ => (count : ℝ))
        (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_eq_card i z j H hH).symm
    calc
      ‖F m z‖ = ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 H
          (z.2 j).1).card : ℝ) := by
            rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      _ = (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j H : ℝ) := hcard
      _ ≤ K z := hcount
  have hlim : ∀ᵐ z ∂P, Filter.Tendsto (fun m : ℕ => F m z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
    simpa [F, f] using
      (tendsto_stationaryPriorityClassTaggedPassiveRightGridCard meanService i j z T hwait)
  simpa [P, F, f] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) K hmeas hK hbound hlim)

/-- For every finite deterministic cap, the expected literal passive arrival
count through the capped queue-wait clock is its arrival rate times the
expected capped queue wait. -/
theorem integral_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait_eq_rate_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (T : ℕ) :
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
      (z.2 j).1).card : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate j.1 *
        (∫ z, min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let A : ℕ → ℝ := fun m =>
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
            (1 / ((m + 1 : ℕ) : ℝ)))
      (z.2 j).1).card : ℝ) ∂P
  let B : ℕ → ℝ := fun m =>
    ∫ z, ((min ((m + 1) * T)
      (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
        (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
          (1 / ((m + 1 : ℕ) : ℝ)) ∂P
  have hleft : Filter.Tendsto A Filter.atTop
      (nhds (∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
        (z.2 j).1).card : ℝ) ∂P)) := by
    simpa [A, P] using
      (tendsto_integral_stationaryPriorityClassTaggedPassiveRightGridCard
        arrivalRate meanService harrivalRate hmeanService hstable i j T)
  have hgrid : Filter.Tendsto B Filter.atTop
      (nhds (∫ z, min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z) ∂P)) := by
    simpa [B, P] using
      (tendsto_integral_cappedReciprocalRightGridHorizon
        arrivalRate meanService harrivalRate hmeanService hstable i T)
  have hfinite : ∀ m : ℕ, A m = arrivalRate j.1 * B m := by
    intro m
    let width : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
    let N : ℕ := (m + 1) * T
    have hwidth : 0 < width := by
      dsimp [width]
      positivity
    simpa [A, B, P, N, width] using
      (integral_stationaryPriorityClassTaggedPassiveRightGridCard_eq_rate_mul_integral_horizon
        arrivalRate meanService harrivalRate hmeanService hstable i j width hwidth N)
  have hright : Filter.Tendsto (fun m : ℕ => arrivalRate j.1 * B m) Filter.atTop
      (nhds (arrivalRate j.1 *
        (∫ z, min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z) ∂P))) := by
    simpa [B] using tendsto_const_nhds.mul hgrid
  have hright' : Filter.Tendsto A Filter.atTop
      (nhds (arrivalRate j.1 *
        (∫ z, min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z) ∂P))) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall (fun m => (hfinite m).symm)
  exact tendsto_nhds_unique hleft hright'

/-- The literal right-closed passive arrival count through every capped
queue-wait clock has a finite first moment. -/
theorem integrable_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (T : ℕ) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
        (z.2 j).1).card : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let F : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun m z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (((min ((m + 1) * T)
        (Nat.ceil (stationaryPriorityClassTaggedQueueWait meanService i z /
          (1 / ((m + 1 : ℕ) : ℝ)))) : ℕ) : ℝ) *
            (1 / ((m + 1 : ℕ) : ℝ)))
      (z.2 j).1).card : ℝ)
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
      (z.2 j).1).card : ℝ)
  let K : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (T : ℝ) : ℝ)
  have hFmeas : ∀ m, AEStronglyMeasurable (F m) P := by
    intro m
    simpa [F, P] using
      (integrable_stationaryPriorityClassTaggedPassiveRightGridCard
        arrivalRate meanService harrivalRate hmeanService hstable i j T m).aestronglyMeasurable
  have hFlim : ∀ᵐ z ∂P, Filter.Tendsto (fun m : ℕ => F m z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
    simpa [F, f] using
      (tendsto_stationaryPriorityClassTaggedPassiveRightGridCard meanService i j z T hwait)
  have hfmeas : AEStronglyMeasurable f P :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hFmeas hFlim
  have hK : Integrable K P := by
    simpa [K, P] using
      (integrable_multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
        arrivalRate harrivalRate i j (T : ℝ) (Nat.cast_nonneg T))
  refine Integrable.mono' hK hfmeas ?_
  filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
    arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
  let s : ℝ := min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)
  have hs : 0 ≤ s := le_min (Nat.cast_nonneg T) hwait
  have hsT : s ≤ T := min_le_left _ _
  have hcountNat :
      multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s ≤
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (T : ℝ) := by
    unfold multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
    exact (Probability.PoissonProcess.monotone_suspensionBaseFutureCount (z.2 j).1) hsT
  have hcount :
      (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s : ℝ) ≤ K z := by
    change (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s : ℝ) ≤
      (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j (T : ℝ) : ℝ)
    exact_mod_cast hcountNat
  have hcard :
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 s
        (z.2 j).1).card : ℝ) =
        (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s : ℝ) := by
    exact congrArg (fun count : ℕ => (count : ℝ))
      (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_eq_card i z j s hs).symm
  calc
    ‖f z‖ = ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 s
        (z.2 j).1).card : ℝ) := by
          rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    _ = (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j s : ℝ) := hcard
    _ ≤ K z := hcount

/-- As the deterministic cap grows, the literal capped passive count is
eventually the full right-closed passive count on every sample path. -/
theorem tendsto_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    Filter.Tendsto (fun T : ℕ =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
        (z.2 j).1).card : ℝ)) Filter.atTop
      (nhds ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z)
        (z.2 j).1).card : ℝ)) := by
  apply tendsto_nhds_of_eventually_eq
  obtain ⟨N, hN⟩ := exists_nat_ge (stationaryPriorityClassTaggedQueueWait meanService i z)
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro T hNT
  have hwait : stationaryPriorityClassTaggedQueueWait meanService i z ≤ (T : ℝ) :=
    hN.trans (by exact_mod_cast hNT)
  rw [min_eq_right hwait]

/-- Almost surely, literal capped passive counts are nondecreasing in the
deterministic cap. -/
theorem ae_monotone_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Monotone (fun T : ℕ =>
        ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
          (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
          (z.2 j).1).card : ℝ)) := by
  filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
    arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
  intro T U hTU
  let sT : ℝ := min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)
  let sU : ℝ := min (U : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z)
  have hsT : 0 ≤ sT := le_min (Nat.cast_nonneg T) hwait
  have hsU : 0 ≤ sU := le_min (Nat.cast_nonneg U) hwait
  have hsTU : sT ≤ sU := by
    apply min_le_min_right
    exact_mod_cast hTU
  have hcountNat :
      multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j sT ≤
        multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j sU := by
    unfold multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
    exact (Probability.PoissonProcess.monotone_suspensionBaseFutureCount (z.2 j).1) hsTU
  have hcount :
      (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j sT : ℝ) ≤
        (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j sU : ℝ) := by
    exact_mod_cast hcountNat
  calc
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 sT
      (z.2 j).1).card : ℝ) =
        (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j sT : ℝ) := by
          exact congrArg (fun count : ℕ => (count : ℝ))
            (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_eq_card i z j sT hsT).symm
    _ ≤ (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j sU : ℝ) := hcount
    _ = ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 sU
      (z.2 j).1).card : ℝ) := by
          exact congrArg (fun count : ℕ => (count : ℝ))
            (multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_eq_card i z j sU hsU)

/-- The full literal right-closed passive count through the queue-wait clock
is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_stationaryPriorityClassTaggedPassiveCount_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    AEStronglyMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z)
        (z.2 j).1).card : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  change AEStronglyMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z)
      (z.2 j).1).card : ℝ)) P
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun (T : ℕ) z => ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
      (z.2 j).1).card : ℝ)) ?_ ?_
  · intro T
    simpa [P] using
      (integrable_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j T).aestronglyMeasurable
  · filter_upwards with z
    simpa [P] using
      (tendsto_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait meanService i j z)

/-- The full literal right-closed passive arrival count through the queue-wait
clock has a finite first moment. -/
theorem integrable_stationaryPriorityClassTaggedPassiveCount_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z)
        (z.2 j).1).card : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let f : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun T z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
      (z.2 j).1).card : ℝ)
  let F : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z)
      (z.2 j).1).card : ℝ)
  let g : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ENNReal := fun T z =>
    ENNReal.ofReal (f T z)
  let G : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ENNReal := fun z =>
    ENNReal.ofReal (F z)
  let W : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
    stationaryPriorityClassTaggedQueueWait meanService i
  have hfint : ∀ T, Integrable (f T) P := by
    intro T
    simpa [f, P] using
      (integrable_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j T)
  have hfnonneg : ∀ T, 0 ≤ᵐ[P] f T := by
    intro T
    filter_upwards with z
    exact Nat.cast_nonneg _
  have hFmeas : AEStronglyMeasurable F P := by
    simpa [F, P] using
      (aestronglyMeasurable_stationaryPriorityClassTaggedPassiveCount_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hFnonneg : 0 ≤ᵐ[P] F := by
    filter_upwards with z
    exact Nat.cast_nonneg _
  have hWint : Integrable W P := by
    simpa [W, P] using
      (integrable_stationaryPriorityClassTaggedQueueWait_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hWnonneg : 0 ≤ᵐ[P] W := by
    simpa [W, P] using
      (ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hWintnonneg : 0 ≤ ∫ z, W z ∂P :=
    MeasureTheory.integral_nonneg_of_ae hWnonneg
  let C : ℝ := arrivalRate j.1 * (∫ z, W z ∂P)
  have hboundInt : ∀ T, ∫ z, f T z ∂P ≤ C := by
    intro T
    have hminnonneg : 0 ≤ᵐ[P] (fun z => min (T : ℝ) (W z)) := by
      filter_upwards [hWnonneg] with z hz
      exact le_min (Nat.cast_nonneg T) hz
    have hminle : ∫ z, min (T : ℝ) (W z) ∂P ≤ ∫ z, W z ∂P :=
      MeasureTheory.integral_mono_of_nonneg hminnonneg hWint
        (Filter.Eventually.of_forall fun z => min_le_right _ _)
    have hrate : 0 ≤ arrivalRate j.1 := (harrivalRate j.1).le
    have hmul := mul_le_mul_of_nonneg_left hminle hrate
    simpa [f, W, C, P] using
      (integral_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait_eq_rate_mul_integral
        arrivalRate meanService harrivalRate hmeanService hstable i j T).trans_le hmul
  have hgmono : ∀ᵐ z ∂P, Monotone (fun T => g T z) := by
    filter_upwards [ae_monotone_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i j] with z hz
    intro T U hTU
    exact ENNReal.ofReal_le_ofReal (hz hTU)
  have hglim : ∀ᵐ z ∂P, Filter.Tendsto (fun T : ℕ => g T z)
      Filter.atTop (nhds (G z)) := by
    filter_upwards with z
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simpa [f, F] using
      (tendsto_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait meanService i j z)
  have hlinTendsto : Filter.Tendsto (fun T => ∫⁻ z, g T z ∂P) Filter.atTop
      (nhds (∫⁻ z, G z ∂P)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      (fun T => (hfint T).aestronglyMeasurable.aemeasurable.ennreal_ofReal) hgmono hglim
  have hlinbound : ∀ T, ∫⁻ z, g T z ∂P ≤ ENNReal.ofReal C := by
    intro T
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfint T) (hfnonneg T)]
    exact ENNReal.ofReal_le_ofReal (hboundInt T)
  have hlimit_le : ∫⁻ z, G z ∂P ≤ ENNReal.ofReal C :=
    le_of_tendsto hlinTendsto (Filter.Eventually.of_forall hlinbound)
  have hlinne : ∫⁻ z, G z ∂P ≠ ⊤ :=
    (hlimit_le.trans_lt ENNReal.ofReal_lt_top).ne
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFmeas hFnonneg).mp
  simpa [G, F] using hlinne

/-- The full literal right-closed passive count through the queue-wait clock
has expectation equal to the passive arrival rate times the mean queue wait. -/
theorem integral_stationaryPriorityClassTaggedPassiveCount_queueWait_eq_rate_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫ z, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z)
      (z.2 j).1).card : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let f : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun T z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (min (T : ℝ) (stationaryPriorityClassTaggedQueueWait meanService i z))
      (z.2 j).1).card : ℝ)
  let F : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z)
      (z.2 j).1).card : ℝ)
  let W : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
    stationaryPriorityClassTaggedQueueWait meanService i
  have hfint : ∀ T, Integrable (f T) P := by
    intro T
    simpa [f, P] using
      (integrable_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j T)
  have hFint : Integrable F P := by
    simpa [F, P] using
      (integrable_stationaryPriorityClassTaggedPassiveCount_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hcountmono : ∀ᵐ z ∂P, Monotone (fun T => f T z) := by
    simpa [f, P] using
      (ae_monotone_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hcountlim : ∀ᵐ z ∂P, Filter.Tendsto (fun T : ℕ => f T z)
      Filter.atTop (nhds (F z)) := by
    filter_upwards with z
    simpa [f, F] using
      (tendsto_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait meanService i j z)
  have hleft : Filter.Tendsto (fun T => ∫ z, f T z ∂P) Filter.atTop
      (nhds (∫ z, F z ∂P)) :=
    MeasureTheory.integral_tendsto_of_tendsto_of_monotone hfint hFint hcountmono hcountlim
  have hWint : Integrable W P := by
    simpa [W, P] using
      (integrable_stationaryPriorityClassTaggedQueueWait_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hWnonneg : 0 ≤ᵐ[P] W := by
    simpa [W, P] using
      (ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hwaitmeas : ∀ (T : ℕ), AEStronglyMeasurable (fun z => min (T : ℝ) (W z)) P := by
    intro T
    exact ((aemeasurable_const : AEMeasurable
      (fun _ : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i => (T : ℝ)) P).min
        hWint.aemeasurable).aestronglyMeasurable
  have hwaitbound : ∀ (T : ℕ), ∀ᵐ z ∂P, ‖min (T : ℝ) (W z)‖ ≤ W z := by
    intro T
    filter_upwards [hWnonneg] with z hz
    have hminnonneg : 0 ≤ min (T : ℝ) (W z) := le_min (Nat.cast_nonneg T) hz
    rw [Real.norm_of_nonneg hminnonneg]
    exact min_le_right _ _
  have hwaitlim : ∀ᵐ z ∂P, Filter.Tendsto (fun T : ℕ => min (T : ℝ) (W z))
      Filter.atTop (nhds (W z)) := by
    filter_upwards with z
    apply tendsto_nhds_of_eventually_eq
    obtain ⟨N, hN⟩ := exists_nat_ge (W z)
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro T hNT
    exact min_eq_right (hN.trans (by exact_mod_cast hNT))
  have hrightBase : Filter.Tendsto (fun (T : ℕ) => ∫ z, min (T : ℝ) (W z) ∂P) Filter.atTop
      (nhds (∫ z, W z ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := fun T z => min (T : ℝ) (W z)) (f := W) W
      hwaitmeas hWint hwaitbound hwaitlim
  have hfinite : ∀ (T : ℕ), (∫ z, f T z ∂P) =
      arrivalRate j.1 * (∫ z, min (T : ℝ) (W z) ∂P) := by
    intro T
    simpa [f, W, P] using
      (integral_stationaryPriorityClassTaggedPassiveCount_cappedQueueWait_eq_rate_mul_integral
        arrivalRate meanService harrivalRate hmeanService hstable i j T)
  have hright : Filter.Tendsto (fun (T : ℕ) =>
      arrivalRate j.1 * (∫ z, min (T : ℝ) (W z) ∂P)) Filter.atTop
      (nhds (arrivalRate j.1 * (∫ z, W z ∂P))) := by
    simpa using tendsto_const_nhds.mul hrightBase
  have hright' : Filter.Tendsto (fun (T : ℕ) => ∫ z, f T z ∂P) Filter.atTop
      (nhds (arrivalRate j.1 * (∫ z, W z ∂P))) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall (fun T => (hfinite T).symm)
  simpa [F, W, P] using tendsto_nhds_unique hleft hright'

/-- The named right-closed passive count through a tagged queue-wait horizon
has a finite first moment. -/
theorem integrable_stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
        meanService i z j : ℝ))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hcard : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z)
        (z.2 j).1).card : ℝ)) P := by
    simpa [P] using
      (integrable_stationaryPriorityClassTaggedPassiveCount_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  refine hcard.congr ?_
  filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
    arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
  exact congrArg (fun q : ℕ => (q : ℝ))
    (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait_eq_card
      meanService i z j hwait).symm

/-- The named right-closed passive count through a tagged queue-wait horizon
has expectation equal to the passive arrival rate times the mean queue wait. -/
theorem integral_stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait_eq_rate_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫ z, (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
      meanService i z j : ℝ)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have heq : (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
        meanService i z j : ℝ)) =ᵐ[P]
      fun z => ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z)
        (z.2 j).1).card : ℝ) := by
    filter_upwards [ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwait
    exact congrArg (fun q : ℕ => (q : ℝ))
      (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait_eq_card
        meanService i z j hwait)
  rw [integral_congr_ae heq]
  simpa [P] using
    (integral_stationaryPriorityClassTaggedPassiveCount_queueWait_eq_rate_mul_integral
      arrivalRate meanService harrivalRate hmeanService hstable i j)

/-- The finite strict-before-wait index is almost-everywhere strongly
measurable under the factored selected-Palm law. -/
theorem aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkQueueWaitCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    AEStronglyMeasurable (fun x =>
      (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ))
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun cap x =>
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap x : ℝ)) ?_ ?_
  · intro cap
    simpa [M] using
      (aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j cap)
  · filter_upwards with x
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2
      ⟨stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x, ?_⟩
    intro cap hcap
    exact congrArg (fun q : ℕ => (q : ℝ))
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_eq_min
        meanService i j cap x |>.trans (min_eq_right hcap))

/-- The finite strict-before-wait index has a finite first moment.  Its
pathwise bound by the physical right-closed count transfers the established
selected-Palm count integrability through the future-mark factorization. -/
theorem integrable_stationaryPriorityClassTaggedFutureMarkQueueWaitCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    Integrable (fun x =>
      (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ))
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  have hback : MeasurePreserving e.symm M P := by
    exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
      arrivalRate harrivalRate i j).symm e
  have hphysical : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i z)
        (z.2 j).1).card : ℝ)) P := by
    simpa [P] using
      (integrable_stationaryPriorityClassTaggedPassiveCount_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hbound : Integrable (fun x =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i (e.symm x))
        ((e.symm x).2 j).1).card : ℝ)) M := by
    simpa [e, Function.comp_def] using hback.integrable_comp_of_integrable hphysical
  have hmeas : AEStronglyMeasurable (fun x =>
      (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ)) M := by
    simpa [M] using
      (aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast stationaryPriorityClassTaggedFutureMarkQueueWaitCount_le_rightClosedCard
    meanService i j x

/-- The literal finite strict-before-wait marked-work sum has a finite first
moment.  Monotone convergence transfers the capped predictable identities,
while the finite expected strict count supplies the uniform bound. -/
theorem integrable_stationaryPriorityClassTaggedFutureMarkQueueWaitWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    Integrable (stationaryPriorityClassTaggedFutureMarkQueueWaitWork
      meanService i j)
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let f : ℕ → MulticlassPalmFutureMarkFactorCarrier i j → ℝ := fun cap =>
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork meanService i j cap
  let F : MulticlassPalmFutureMarkFactorCarrier i j → ℝ :=
    stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j
  let g : ℕ → MulticlassPalmFutureMarkFactorCarrier i j → ENNReal := fun cap x =>
    ENNReal.ofReal (f cap x)
  let G : MulticlassPalmFutureMarkFactorCarrier i j → ENNReal := fun x =>
    ENNReal.ofReal (F x)
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  have hmarks : ∀ᵐ x ∂M, ∀ r : ℕ, 0 ≤ x.2 r := by
    refine ae_of_ae_map (μ := M) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ r : ℕ, 0 ≤ ξ r)
      measurable_snd.aemeasurable ?_
    simpa [M, Probability.PoissonProcess.interarrival] using
      (Probability.PoissonProcess.ae_all_interarrival_nonnegative
        (by norm_num : (0 : ℝ) < 1))
  have hfint : ∀ cap, Integrable (f cap) M := by
    intro cap
    simpa [f, M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        arrivalRate meanService harrivalRate hmeanService hstable i j cap)
  have hfnonneg : ∀ cap, 0 ≤ᵐ[M] f cap := by
    intro cap
    filter_upwards [hmarks] with x hx
    unfold f stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
    apply Finset.sum_nonneg
    intro r _
    split
    · exact mul_nonneg (hmeanService j.1).le (hx r)
    · exact le_rfl
  have hFmeas : AEStronglyMeasurable F M := by
    simpa [F, M] using
      (aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkQueueWaitWork
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hFnonneg : 0 ≤ᵐ[M] F := by
    filter_upwards [hmarks] with x hx
    unfold F stationaryPriorityClassTaggedFutureMarkQueueWaitWork
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (hmeanService j.1).le (hx r)
  let C : ℝ :=
    (∫ x, (stationaryPriorityClassTaggedFutureMarkQueueWaitCount
      meanService i j x : ℝ) ∂M) * meanService j.1
  have hcountint : Integrable (fun x =>
      (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ)) M := by
    simpa [M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hboundInt : ∀ cap, ∫ x, f cap x ∂M ≤ C := by
    intro cap
    have hpointwise : ∀ x,
        (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap x : ℝ) ≤
          (stationaryPriorityClassTaggedFutureMarkQueueWaitCount
            meanService i j x : ℝ) := by
      intro x
      rw [stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_eq_min]
      exact_mod_cast min_le_right cap
        (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x)
    have hcountle :
        (∫ x, (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap x : ℝ) ∂M) ≤
          ∫ x, (stationaryPriorityClassTaggedFutureMarkQueueWaitCount
            meanService i j x : ℝ) ∂M := by
      apply MeasureTheory.integral_mono_ae
        (integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          arrivalRate meanService harrivalRate hmeanService hstable i j cap)
        hcountint
      exact Filter.Eventually.of_forall hpointwise
    have hmul := mul_le_mul_of_nonneg_right hcountle (hmeanService j.1).le
    simpa [f, C, M] using
      (integral_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork_eq_mean_mul_count
        arrivalRate meanService harrivalRate hmeanService hstable i j cap).trans_le hmul
  have hgmono : ∀ᵐ x ∂M, Monotone (fun cap => g cap x) := by
    filter_upwards [hmarks] with x hx
    intro cap cap' hcap
    exact ENNReal.ofReal_le_ofReal
      (monotone_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        meanService i j x (hmeanService j.1).le hx hcap)
  have hglim : ∀ᵐ x ∂M, Filter.Tendsto (fun cap : ℕ => g cap x)
      Filter.atTop (nhds (G x)) := by
    filter_upwards with x
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simpa [f, F, g, G] using
      (tendsto_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        meanService i j x)
  have hlinTendsto : Filter.Tendsto (fun cap => ∫⁻ x, g cap x ∂M)
      Filter.atTop (nhds (∫⁻ x, G x ∂M)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      (fun cap => (hfint cap).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      hgmono hglim
  have hlinbound : ∀ cap, ∫⁻ x, g cap x ∂M ≤ ENNReal.ofReal C := by
    intro cap
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hfint cap) (hfnonneg cap)]
    exact ENNReal.ofReal_le_ofReal (hboundInt cap)
  have hlimit_le : ∫⁻ x, G x ∂M ≤ ENNReal.ofReal C :=
    le_of_tendsto hlinTendsto (Filter.Eventually.of_forall hlinbound)
  have hlinne : ∫⁻ x, G x ∂M ≠ ⊤ :=
    (hlimit_le.trans_lt ENNReal.ofReal_lt_top).ne
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFmeas hFnonneg).mp
  simpa [G, F] using hlinne

/-- The expected literal strict-before-wait marked work is the isolated
class's mean requirement times the expected strict-before-wait count. -/
theorem integral_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_mean_mul_count
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫ x, stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      (∫ x, (stationaryPriorityClassTaggedFutureMarkQueueWaitCount
        meanService i j x : ℝ)
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))) *
        meanService j.1 := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let f : ℕ → MulticlassPalmFutureMarkFactorCarrier i j → ℝ := fun cap =>
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork meanService i j cap
  let F : MulticlassPalmFutureMarkFactorCarrier i j → ℝ :=
    stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j
  let c : ℕ → MulticlassPalmFutureMarkFactorCarrier i j → ℝ := fun cap x =>
    (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
      meanService i j cap x : ℝ)
  let C : MulticlassPalmFutureMarkFactorCarrier i j → ℝ := fun x =>
    (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ)
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  have hmarks : ∀ᵐ x ∂M, ∀ r : ℕ, 0 ≤ x.2 r := by
    refine ae_of_ae_map (μ := M) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ r : ℕ, 0 ≤ ξ r)
      measurable_snd.aemeasurable ?_
    simpa [M, Probability.PoissonProcess.interarrival] using
      (Probability.PoissonProcess.ae_all_interarrival_nonnegative
        (by norm_num : (0 : ℝ) < 1))
  have hfint : ∀ cap, Integrable (f cap) M := by
    intro cap
    simpa [f, M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        arrivalRate meanService harrivalRate hmeanService hstable i j cap)
  have hFint : Integrable F M := by
    simpa [F, M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkQueueWaitWork
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hfmono : ∀ᵐ x ∂M, Monotone (fun cap => f cap x) := by
    filter_upwards [hmarks] with x hx
    exact monotone_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
      meanService i j x (hmeanService j.1).le hx
  have hflim : ∀ᵐ x ∂M, Filter.Tendsto (fun cap : ℕ => f cap x)
      Filter.atTop (nhds (F x)) := by
    filter_upwards with x
    simpa [f, F] using
      (tendsto_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        meanService i j x)
  have hwork : Filter.Tendsto (fun cap => ∫ x, f cap x ∂M)
      Filter.atTop (nhds (∫ x, F x ∂M)) :=
    MeasureTheory.integral_tendsto_of_tendsto_of_monotone hfint hFint hfmono hflim
  have hcint : ∀ cap, Integrable (c cap) M := by
    intro cap
    simpa [c, M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j cap)
  have hCint : Integrable C M := by
    simpa [C, M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hcmono : ∀ᵐ x ∂M, Monotone (fun cap => c cap x) := by
    filter_upwards with x
    intro cap cap' hcap
    change
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap x : ℝ) ≤
        (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap' x : ℝ)
    exact_mod_cast
      (monotone_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j x hcap)
  have hclim : ∀ᵐ x ∂M, Filter.Tendsto (fun cap : ℕ => c cap x)
      Filter.atTop (nhds (C x)) := by
    filter_upwards with x
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2
      ⟨stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x, ?_⟩
    intro cap hcap
    exact congrArg (fun q : ℕ => (q : ℝ))
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_eq_min
        meanService i j cap x |>.trans (min_eq_right hcap))
  have hcount : Filter.Tendsto (fun cap => ∫ x, c cap x ∂M)
      Filter.atTop (nhds (∫ x, C x ∂M)) :=
    MeasureTheory.integral_tendsto_of_tendsto_of_monotone hcint hCint hcmono hclim
  have hright : Filter.Tendsto (fun cap =>
      (∫ x, c cap x ∂M) * meanService j.1) Filter.atTop
      (nhds ((∫ x, C x ∂M) * meanService j.1)) := by
    simpa using hcount.mul tendsto_const_nhds
  have hright' : Filter.Tendsto (fun cap => ∫ x, f cap x ∂M)
      Filter.atTop (nhds ((∫ x, C x ∂M) * meanService j.1)) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall (fun cap => by
      simpa [f, c, M] using
        (integral_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork_eq_mean_mul_count
          arrivalRate meanService harrivalRate hmeanService hstable i j cap).symm)
  simpa [F, C, M] using tendsto_nhds_unique hwork hright'

end

end AppliedModelingLib.Queueing

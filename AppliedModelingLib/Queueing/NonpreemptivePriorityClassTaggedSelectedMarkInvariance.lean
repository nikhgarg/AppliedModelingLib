import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFirstZero
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedDeterministicTimeLocality
import AppliedModelingLib.Queueing.MulticlassPalmSelectedMarkFactors

/-!
# Selected-service-mark invariance of pre-arrival priority state

Changing only the selected Palm customer's service mark leaves every input
coordinate strictly before its arrival unchanged.  Consequently, every fixed
finite pre-arrival priority replay is fixed by the external factor.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A fixed finite replay ending at the selected arrival epoch is unchanged
when only the selected zero-indexed service mark is changed. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_selectedMarkExternal_fst
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (older : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1)
    (hxy : x.1 = y.1) :
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
        (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)
        (-older) 0 := by
  let z := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x
  let w := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y
  have hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1 := by
    rw [← multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_selectedArrivalPath_eq_of_fst_eq
      i x y hxy]
    exact hgood
  have harrival : ∀ (j : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z j m =
        stationaryPriorityClassTaggedArrival i w j m := by
    intro j m
    simpa [z, w, stationaryPriorityClassTaggedArrival] using
      multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_arrival_eq_of_fst_eq
        i x y j m hxy
  have hindices : canonicalStationaryPriorityClassTaggedArrivalWindowIndices
      i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i w (-older) 0 := by
    apply canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrival_eq_of_lt
      i z w (-older) 0 0 le_rfl hgood hgoodw
    intro j m _
    exact harrival j m
  apply canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_jobs_eq
    meanService i z w (-older) 0
  apply canonicalStationaryPriorityClassTaggedArrivalWindowJobs_eq_of_indices_eq
    meanService i z w (-older) 0 hindices harrival
  intro q hq
  rcases q with ⟨j, m⟩
  by_cases hji : j = i
  · subst j
    have hbefore : stationaryPriorityClassTaggedArrival i z i m < 0 := by
      exact canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right
        i z (-older) 0 hgood (Sigma.mk i m) hq
    have hm : m ≠ 0 := by
      intro hm
      subst m
      have hzero : stationaryPriorityClassTaggedArrival i z i 0 = 0 := by
        exact multiclassStationaryPoissonWorkClassTaggedArrival_tag_zero i z
      linarith
    unfold stationaryPriorityClassTaggedWorkRequirementAt
    exact congrArg (fun work => meanService i * work)
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_requirement_eq_of_fst_eq
        i x y i m (Or.inr hm) hxy)
  · unfold stationaryPriorityClassTaggedWorkRequirementAt
    exact congrArg (fun work => meanService j * work)
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_requirement_eq_of_fst_eq
        i x y j m (Or.inl hji) hxy)

/-- Once both remote-past constructions have coalesced to finite windows, the
selected service mark leaves the active residual and inclusive urgent waiting
work immediately before the selected arrival unchanged. -/
theorem stationaryPriorityClassTagged_preArrivalStateComponents_eq_of_selectedMarkExternal_fst
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1)
    (hz : ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
      liveEquivalentNonpreemptivePriorityWorkState
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
          (-older) 0)
        (stationaryPriorityClassTaggedRemotePastState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)))
    (hw : ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
      liveEquivalentNonpreemptivePriorityWorkState
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)
          (-older) 0)
        (stationaryPriorityClassTaggedRemotePastState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)))
    (hxy : x.1 = y.1) :
    stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) ∧
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) =
      stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) := by
  let z := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x
  let w := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y
  rcases hz with ⟨cutoffZ, _, hcoalesceZ⟩
  rcases hw with ⟨cutoffW, _, hcoalesceW⟩
  let older := max cutoffZ cutoffW
  have hfinite : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z
      (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0 := by
    exact canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_selectedMarkExternal_fst
      meanService i x y older (by simpa [z] using hgood) hxy
  have hcoalesceZ' : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z) := by
    exact hcoalesceZ older (le_max_left _ _)
  have hcoalesceW' : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i w) := by
    exact hcoalesceW older (le_max_right _ _)
  have hfiniteLive : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0) := by
    rw [hfinite]
    exact ⟨rfl, rfl, rfl⟩
  have hremote : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityClassTaggedRemotePastState meanService i z)
      (stationaryPriorityClassTaggedRemotePastState meanService i w) := by
    exact liveEquivalentNonpreemptivePriorityWorkState_trans
      (liveEquivalentNonpreemptivePriorityWorkState_symm hcoalesceZ')
      (liveEquivalentNonpreemptivePriorityWorkState_trans hfiniteLive hcoalesceW')
  constructor
  · exact activeNonpreemptivePriorityResidualWork_eq_of_liveEquivalent hremote
  · exact priorityWaitingResidualWorkAtLeastAsUrgent_eq_of_liveEquivalent hremote i

/-- The strict future job ledger through any fixed horizon is unchanged when
only the selected zero-indexed service mark changes. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_selectedMarkExternal_fst
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (t : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1)
    (hxy : x.1 = y.1) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) t := by
  let z := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x
  let w := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y
  have hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1 := by
    rw [← multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_selectedArrivalPath_eq_of_fst_eq
      i x y hxy]
    exact hgood
  have harrival : ∀ (j : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z j m =
        stationaryPriorityClassTaggedArrival i w j m := by
    intro j m
    simpa [z, w, stationaryPriorityClassTaggedArrival] using
      multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_arrival_eq_of_fst_eq
        i x y j m hxy
  have hindices := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrival_eq_of_lt
    i z w t hgood hgoodw (fun j m _ => harrival j m)
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
  rw [hindices]
  apply List.map_congr_left
  intro q hq
  rcases q with ⟨j, m⟩
  have hqz : Sigma.mk j m ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z t := by
    rwa [hindices]
  have hcomponent : m ∈ stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z t j := by
    simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      nonpreemptivePriorityArrivalWindowIndices] using hqz
  have hbefore :=
    (mem_stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_iff
      i z t hgood j m).mp hcomponent |>.1
  have hrequirement : stationaryPriorityClassTaggedWorkRequirementAt meanService i z j m =
      stationaryPriorityClassTaggedWorkRequirementAt meanService i w j m := by
    unfold stationaryPriorityClassTaggedWorkRequirementAt
    apply congrArg (fun work => meanService j * work)
    by_cases hji : j = i
    · subst j
      have hm : m ≠ 0 := by
        intro hm
        subst m
        have hzero : stationaryPriorityClassTaggedArrival i z i 0 = 0 :=
          multiclassStationaryPoissonWorkClassTaggedArrival_tag_zero i z
        linarith
      exact multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_requirement_eq_of_fst_eq
        i x y i m (Or.inr hm) hxy
    · exact multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_requirement_eq_of_fst_eq
        i x y j m (Or.inl hji) hxy
  rw [harrival j m, hrequirement]

/-- The strictly higher-priority input-work ledger is therefore independent
of the selected customer's own service mark. -/
theorem stationaryPriorityClassTaggedStrictArrivalWorkBeforeHorizon_eq_of_selectedMarkExternal_fst
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (t : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1)
    (hxy : x.1 = y.1) :
    nonpreemptivePriorityTaggedStrictArrivalWork
        (stationaryPriorityClassTaggedJob meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x))
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) t) =
      nonpreemptivePriorityTaggedStrictArrivalWork
        (stationaryPriorityClassTaggedJob meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y))
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) t) := by
  rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_selectedMarkExternal_fst
    meanService i x y t hgood hxy]
  apply nonpreemptivePriorityTaggedStrictArrivalWork_eq_of_priority_eq
  rfl

/-- The selected queue-wait time is fixed by the selected-mark external
factor once the first-zero characterization holds on both compared inputs. -/
theorem stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_firstZero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1)
    (hz : ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
      liveEquivalentNonpreemptivePriorityWorkState
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
          (-older) 0)
        (stationaryPriorityClassTaggedRemotePastState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)))
    (hw : ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
      liveEquivalentNonpreemptivePriorityWorkState
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)
          (-older) 0)
        (stationaryPriorityClassTaggedRemotePastState meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)))
    (hwaitX : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x))
    (hwaitY : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y))
    (hzeroX : stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
      (stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)) = 0)
    (hzeroY : stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)
      (stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y)) = 0)
    (hposX : ∀ t : ℝ, 0 ≤ t → t < stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) →
      0 < stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) t)
    (hposY : ∀ t : ℝ, 0 ≤ t → t < stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) →
      0 < stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) t)
    (hxy : x.1 = y.1) :
    stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) =
      stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) := by
  let z := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x
  let w := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y
  have hcomponents :=
    stationaryPriorityClassTagged_preArrivalStateComponents_eq_of_selectedMarkExternal_fst
      meanService i x y hgood hz hw hxy
  have hledgerEq : ∀ t : ℝ,
      stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i z t =
        stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i w t := by
    intro t
    unfold stationaryPriorityClassTaggedPreServiceLedgerExpression
    rw [hcomponents.1, hcomponents.2,
      stationaryPriorityClassTaggedStrictArrivalWorkBeforeHorizon_eq_of_selectedMarkExternal_fst
        meanService i x y t hgood hxy]
  apply eq_of_first_zero_of_pos_before
    (stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i z)
    (stationaryPriorityClassTaggedQueueWait meanService i z)
    (stationaryPriorityClassTaggedQueueWait meanService i w)
  · simpa [z] using hwaitX
  · simpa [w] using hwaitY
  · simpa [z] using hzeroX
  · rw [hledgerEq]
    simpa [w] using hzeroY
  · intro t ht hlt
    simpa [z] using hposX t ht hlt
  · intro t ht hlt
    rw [hledgerEq]
    simpa [w] using hposY t ht hlt

/-- The compact first-zero data package is sufficient to make the selected
queue wait independent of the isolated selected service mark. -/
theorem stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_firstZeroData
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1)
    (hdataX : stationaryPriorityClassTaggedFirstZeroData meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x))
    (hdataY : stationaryPriorityClassTaggedFirstZeroData meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y))
    (hxy : x.1 = y.1) :
    stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) =
      stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) := by
  rcases hdataX with ⟨_, hz, hwaitX, hzeroX, hposX⟩
  rcases hdataY with ⟨_, hw, hwaitY, hzeroY, hposY⟩
  exact stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_firstZero
    meanService i x y hgood hz hw hwaitX hwaitY hzeroX hzeroY hposX hposY hxy

/-- The first-zero characterization transports to the explicit product law
that separates the selected service mark from all external queueing input. -/
theorem ae_multiclassPalmSelectedMarkExternal_firstZeroData
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ x ∂(((((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
      (ProbabilityTheory.expMeasure (1 : ℝ)))),
      stationaryPriorityClassTaggedFirstZeroData meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let E : Measure (MulticlassPalmSelectedMarkExternalCarrier i) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let e := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure B :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpres : MeasurePreserving e P (E.prod B) := by
    simpa [e, P, E, B] using
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv_measurePreserving
        arrivalRate harrivalRate i)
  have hsource : ∀ᵐ z ∂P,
      stationaryPriorityClassTaggedFirstZeroData meanService i z := by
    simpa [P] using
      (ae_stationaryPriorityClassTaggedFirstZeroData
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hback : MeasurePreserving e.symm (E.prod B) P := by
    exact hpres.symm e
  rw [← hback.map_eq] at hsource
  simpa [e] using ae_of_ae_map hback.measurable.aemeasurable hsource

/-- Under two independent draws of the selected service mark over one common
external input, the tagged queue wait agrees almost surely.  This is the
pairwise product-law form of own-service-work invariance. -/
theorem ae_stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_pair
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ q ∂
      (((((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
        (ProbabilityTheory.expMeasure (1 : ℝ))).prod
        (ProbabilityTheory.expMeasure (1 : ℝ))),
      stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i q.1) =
      stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i
          (q.1.1, q.2)) := by
  let E : Measure (MulticlassPalmSelectedMarkExternalCarrier i) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure B :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hdata : ∀ᵐ x ∂(E.prod B),
      stationaryPriorityClassTaggedFirstZeroData meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) := by
    simpa [E, B] using
      (ae_multiclassPalmSelectedMarkExternal_firstZeroData
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hfirst : MeasurePreserving Prod.fst ((E.prod B).prod B) (E.prod B) :=
    measurePreserving_fst
  have hreplace : MeasurePreserving (Prod.map Prod.fst id) ((E.prod B).prod B) (E.prod B) := by
    exact (measurePreserving_fst : MeasurePreserving Prod.fst (E.prod B) E).prod
      (MeasurePreserving.id B)
  have hdataFirst : ∀ᵐ q ∂((E.prod B).prod B),
      stationaryPriorityClassTaggedFirstZeroData meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i q.1) :=
    hfirst.quasiMeasurePreserving.ae hdata
  have hdataReplace : ∀ᵐ q ∂((E.prod B).prod B),
      stationaryPriorityClassTaggedFirstZeroData meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i
          (q.1.1, q.2)) := by
    simpa only [Prod.map_apply] using hreplace.quasiMeasurePreserving.ae hdata
  filter_upwards [hdataFirst, hdataReplace] with q hdataFirst hdataReplace
  have hgood := hdataFirst.1
  exact stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_firstZeroData
    meanService i q.1 (q.1.1, q.2) hgood hdataFirst hdataReplace rfl

/-- The selected customer's queue wait has the same expectation after
multiplication by its separated unit-exponential service mark.  The proof
uses two independent marks over one external input, rather than choosing a
distinguished value of a continuous mark. -/
theorem integral_multiclassPalmSelectedMarkExternal_queueWait_mul_selectedMark
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∫ x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ,
        stationaryPriorityClassTaggedQueueWait meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) * x.2 ∂
      (((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
        (ProbabilityTheory.expMeasure (1 : ℝ)) =
      ∫ x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ,
        stationaryPriorityClassTaggedQueueWait meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) ∂
      (((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
        (ProbabilityTheory.expMeasure (1 : ℝ)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let E : Measure (MulticlassPalmSelectedMarkExternalCarrier i) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let e := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i
  let w : MulticlassPalmSelectedMarkExternalCarrier i × ℝ → ℝ := fun x =>
    stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
  let M := (E.prod B).prod B
  let reorder : (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ →
      (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ :=
    fun q => ((q.1.1, q.2), q.1.2)
  let F : (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ → ℝ :=
    fun q => w q.1 * q.1.2
  let K : (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ → ℝ :=
    fun q => w q.1 * q.2
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure B :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpres : MeasurePreserving e P (E.prod B) := by
    simpa [e, P, E, B] using
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv_measurePreserving
        arrivalRate harrivalRate i)
  have hback : MeasurePreserving e.symm (E.prod B) P := by
    exact hpres.symm e
  have hwSource : AEMeasurable (stationaryPriorityClassTaggedQueueWait meanService i) P := by
    simpa [P] using aemeasurable_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hw : AEMeasurable w (E.prod B) := by
    simpa [w, e, Function.comp_def] using
      hwSource.comp_quasiMeasurePreserving hback.quasiMeasurePreserving
  have hleft : AEMeasurable (fun x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ =>
      w x * x.2) (E.prod B) := hw.mul measurable_snd.aemeasurable
  have hfirst : MeasurePreserving Prod.fst M (E.prod B) :=
    measurePreserving_fst
  have hreorder : MeasurePreserving reorder M M := by
    let hassoc := measurePreserving_prodAssoc E B B
    let hswap := (MeasurePreserving.id E).prod
      (Measure.measurePreserving_swap (μ := B) (ν := B))
    let hunassoc := (measurePreserving_prodAssoc E B B).symm
    convert hunassoc.comp (hswap.comp hassoc) using 1
  have hpair : ∀ᵐ q ∂M,
      w q.1 = w (q.1.1, q.2) := by
    simpa [M, E, B, w] using
      (ae_stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_pair
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hFK : F =ᵐ[M] K ∘ reorder := by
    filter_upwards [hpair] with q hq
    simp only [F, K, reorder, Function.comp_apply]
    rw [hq]
  have hK : AEMeasurable K M := by
    exact (hw.comp_quasiMeasurePreserving hfirst.quasiMeasurePreserving).mul
      measurable_snd.aemeasurable
  change ∫ x, w x * x.2 ∂(E.prod B) = ∫ x, w x ∂(E.prod B)
  calc
    ∫ x, w x * x.2 ∂(E.prod B) = ∫ q, F q ∂M := by
      symm
      simpa [F] using hfirst.hasLaw.integral_comp hleft.aestronglyMeasurable
    _ = ∫ q, (K ∘ reorder) q ∂M := integral_congr_ae hFK
    _ = ∫ q, K q ∂M := by
      simpa [K] using hreorder.hasLaw.integral_comp hK.aestronglyMeasurable
    _ = (∫ x, w x ∂(E.prod B)) * (∫ y, y ∂B) := by
      exact MeasureTheory.integral_prod_mul w id
    _ = ∫ x, w x ∂(E.prod B) := by
      rw [AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num : (0 : ℝ) < 1)]
      simp [B]

/-- In the selected-mark product coordinates, the tagged customer's physical
service requirement is its class mean times the isolated unit-exponential
mark. -/
theorem stationaryPriorityClassTaggedWorkRequirement_eq_mean_mul_selectedMarkFactor
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    stationaryPriorityClassTaggedWorkRequirement meanService i z = meanService i *
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 := by
  calc
    stationaryPriorityClassTaggedWorkRequirement meanService i z = meanService i *
        multiclassStationaryPoissonWorkClassTaggedRequirementAt i z i 0 := by
          simp [stationaryPriorityClassTaggedWorkRequirement,
            multiclassStationaryPoissonWorkClassTaggedRequirement,
            multiclassStationaryPoissonWorkClassTaggedRequirementAt]
    _ = meanService i *
        (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 := by
          rw [multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors_snd]

/-- The tagged customer's physical service requirement is mean-independent of
its queue wait under the stable selected-Palm law.  This is the service-weighted
waiting reward used in customer-level waiting-occupation compensation. -/
theorem integral_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
        stationaryPriorityClassTaggedQueueWait meanService i z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      meanService i * ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂
        (Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let E : Measure (MulticlassPalmSelectedMarkExternalCarrier i) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let e := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i
  let w : MulticlassPalmSelectedMarkExternalCarrier i × ℝ → ℝ := fun x =>
    stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure B :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpres : MeasurePreserving e P (E.prod B) := by
    simpa [e, P, E, B] using
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv_measurePreserving
        arrivalRate harrivalRate i)
  have hback : MeasurePreserving e.symm (E.prod B) P := by
    exact hpres.symm e
  have hwSource : AEMeasurable (stationaryPriorityClassTaggedQueueWait meanService i) P := by
    simpa [P] using aemeasurable_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hw : AEMeasurable w (E.prod B) := by
    simpa [w, e, Function.comp_def] using
      hwSource.comp_quasiMeasurePreserving hback.quasiMeasurePreserving
  have he : ∀ z, e z =
      multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z := by
    intro z
    rfl
  have hfrom : ∀ z,
      w (e z) = stationaryPriorityClassTaggedQueueWait meanService i z := by
    intro z
    change stationaryPriorityClassTaggedQueueWait meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i
          (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z)) =
      stationaryPriorityClassTaggedQueueWait meanService i z
    rw [multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_apply]
  have hmark : ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z *
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 ∂P =
      ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P := by
    calc
      ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z *
          (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 ∂P =
          ∫ x, w x * x.2 ∂(E.prod B) := by
            calc
              ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z *
                  (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 ∂P =
                  ∫ z, w (e z) * (e z).2 ∂P := by
                    apply integral_congr_ae
                    filter_upwards with z
                    rw [hfrom z, he z]
              _ = ∫ x, w x * x.2 ∂(E.prod B) :=
                hpres.hasLaw.integral_comp
                  (hw.mul measurable_snd.aemeasurable).aestronglyMeasurable
      _ = ∫ x, w x ∂(E.prod B) := by
            exact integral_multiclassPalmSelectedMarkExternal_queueWait_mul_selectedMark
              arrivalRate meanService harrivalRate hmeanService hstable i
      _ = ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P := by
            calc
              ∫ x, w x ∂(E.prod B) = ∫ z, w (e z) ∂P :=
                (hpres.hasLaw.integral_comp hw.aestronglyMeasurable).symm
              _ = ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P := by
                apply integral_congr_ae
                filter_upwards with z
                rw [hfrom z]
  change ∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
      stationaryPriorityClassTaggedQueueWait meanService i z ∂P =
    meanService i * ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P
  calc
    ∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
        stationaryPriorityClassTaggedQueueWait meanService i z ∂P =
        ∫ z, meanService i * (stationaryPriorityClassTaggedQueueWait meanService i z *
          (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2) ∂P := by
          apply integral_congr_ae
          filter_upwards with z
          rw [stationaryPriorityClassTaggedWorkRequirement_eq_mean_mul_selectedMarkFactor]
          ring
    _ = meanService i * ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z *
        (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 ∂P := by
          rw [integral_const_mul]
    _ = meanService i * ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P := by
          rw [hmark]

end

end AppliedModelingLib.Queueing

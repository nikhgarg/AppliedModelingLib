import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalPastReward
import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkRate
import LG24ServiceLevelAgreements.SLA2026TargetPalmRenewalReward
import Mathlib.Tactic

/-!
# Past target-Palm marked-renewal input for the SLA source

This module records only the literal negative-time target source trace under
the genuine target/passive Palm law.  For past label `Int.negSucc n`, the
finite ledger is exactly the target arrival indices in
`[candidatePalmArrival gap (Int.negSucc n), 0)`.  The endpoint at zero is
excluded, so the tagged job itself is not silently counted as past work.

There is no queue, reset, stationarity, response, or tail conclusion here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal negative-time target arrival used as a remote finite-ledger
start.  `n = 0` is the job immediately before the Palm tag. -/
def stationaryAdmittedTargetPalmPastStart
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  candidatePalmArrival z.1.1 (Int.negSucc n)

/-- The positive elapsed magnitude from the target Palm tag to a literal past
target arrival. -/
def stationaryAdmittedTargetPalmPastElapsedTime
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  markedRenewalPastElapsedTime
    (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- The actual finite target ledger on the half-open interval from the `n`th
past target arrival through, but excluding, the Palm epoch zero. -/
def stationaryAdmittedTargetPalmPastLedgerIndices
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Finset Int :=
  palmTaggedArrivalIndices (stationaryAdmittedTargetPalmPastStart target z n) 0 z.1.1

/-- Total literal target work in the past finite ledger. -/
def stationaryAdmittedTargetPalmPastLedgerWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  (stationaryAdmittedTargetPalmPastLedgerIndices target z n).sum fun i => z.1.2 i

/-- The literal target ledger for an arbitrary backward physical-time window
`[-t, 0)`.  This is kept separate from the arrival-epoch specialization so
the half-open endpoint convention remains visible. -/
def stationaryAdmittedTargetPalmPastWindowLedgerIndices
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (t : Real) : Finset Int :=
  palmTaggedArrivalIndices (-t) 0 z.1.1

/-- Total literal target work in the arbitrary half-open past window
`[-t, 0)`. -/
def stationaryAdmittedTargetPalmPastWindowLedgerWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (t : Real) : Real :=
  (stationaryAdmittedTargetPalmPastWindowLedgerIndices target z t).sum fun i => z.1.2 i

/-- The cumulative source work of the literal past labels
`Int.negSucc 0, ..., Int.negSucc n`. -/
def stationaryAdmittedTargetPalmPastCumulativeWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  markedRenewalPastCumulativeWork
    (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- The remote target start is exactly minus its recorded positive elapsed
past time. -/
theorem stationaryAdmittedTargetPalmPastStart_eq_neg_elapsedTime
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) :
    stationaryAdmittedTargetPalmPastStart target z n =
      -stationaryAdmittedTargetPalmPastElapsedTime target z n := by
  rfl

/-- On a good tagged gap path, the literal `[-elapsed, 0)` target ledger is
exactly the finite set of negative labels from `Int.negSucc 0` through
`Int.negSucc n`. -/
theorem stationaryAdmittedTargetPalmPastLedgerIndices_eq_range_image
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hgood : palmTaggedArrivalGoodCarrier z.1.1) (n : Nat) :
    stationaryAdmittedTargetPalmPastLedgerIndices target z n =
      (Finset.range (n + 1)).image Int.negSucc := by
  ext i
  constructor
  · intro hmem
    have hinter := (mem_palmTaggedArrivalIndices_iff
      (stationaryAdmittedTargetPalmPastStart target z n) 0 z.1.1 hgood.1 i).mp hmem
    have hstrict := suspensionGoodGapPath_strictMono z.1.1 hgood.1
    have hi_neg : i < 0 := by
      by_contra hnot
      have hzero_le : (0 : Int) ≤ i := le_of_not_gt hnot
      have harrival := hstrict.monotone hzero_le
      rw [hgood.2] at harrival
      linarith [hinter.2]
    rcases Int.eq_negSucc_of_lt_zero hi_neg with ⟨j, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_range]
    by_contra hnot
    have hnj : n < j := by omega
    have hindex : Int.negSucc j < Int.negSucc n := by
      simp only [Int.negSucc_eq]
      omega
    have harrival := hstrict hindex
    exact (not_lt_of_ge hinter.1) harrival
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨j, hj, rfl⟩
    apply (mem_palmTaggedArrivalIndices_iff
      (stationaryAdmittedTargetPalmPastStart target z n) 0 z.1.1 hgood.1 _).mpr
    constructor
    · have hjn : j ≤ n := by
        simp only [Finset.mem_range] at hj
        omega
      apply (suspensionGoodGapPath_strictMono z.1.1 hgood.1).monotone
      simp only [Int.negSucc_eq]
      omega
    · have harrival := (suspensionGoodGapPath_strictMono z.1.1 hgood.1)
        (Int.negSucc_lt_zero j)
      rw [hgood.2] at harrival
      exact harrival

/-- The finite literal target ledger has precisely the past marked-renewal
work sum.  The start endpoint is included and the Palm tag at zero is not. -/
theorem stationaryAdmittedTargetPalmPastLedgerWork_eq_cumulativeWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hgood : palmTaggedArrivalGoodCarrier z.1.1) (n : Nat) :
    stationaryAdmittedTargetPalmPastLedgerWork target z n =
      stationaryAdmittedTargetPalmPastCumulativeWork target z n := by
  rw [stationaryAdmittedTargetPalmPastLedgerWork,
    stationaryAdmittedTargetPalmPastLedgerIndices_eq_range_image target z hgood n]
  rw [Finset.sum_image]
  · rfl
  · intro a _ha b _hb hab
    exact Int.negSucc.inj hab

/-- On a good target Palm gap path, the literal finite ledger for `[-t,0)`
is the canonical past-renewal range, with its negative labels retained
exactly.  This is a deterministic endpoint identity. -/
theorem stationaryAdmittedTargetPalmPastWindowLedgerIndices_eq_canonicalRangeImage
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hgood : palmTaggedArrivalGoodCarrier z.1.1) (t : Real) :
    stationaryAdmittedTargetPalmPastWindowLedgerIndices target z t =
      (Finset.range (canonicalRenewalCount t (candidatePastGapPath z.1.1))).image
        Int.negSucc := by
  have hstrict := suspensionGoodGapPath_strictMono z.1.1 hgood.1
  have hdiv : Tendsto
      (fun n : Nat => arrivalTime n (candidatePastGapPath z.1.1)) atTop atTop := by
    simpa [candidatePastGapPath, suspensionPastPath] using
      (suspensionGoodGapPath_past z.1.1 hgood.1)
  have hmono : Monotone
      (fun n : Nat => arrivalTime n (candidatePastGapPath z.1.1)) := by
    apply arrivalTime_mono_of_nonnegative
    intro n
    exact (hgood.1.1 (Int.negSucc n)).le
  ext i
  constructor
  · intro hmem
    have hinter := (mem_palmTaggedArrivalIndices_iff (-t) 0 z.1.1 hgood.1 i).mp hmem
    have hi_neg : i < 0 := by
      by_contra hnot
      have hzero_le : (0 : Int) ≤ i := le_of_not_gt hnot
      have harrival := hstrict.monotone hzero_le
      rw [hgood.2] at harrival
      linarith [hinter.2]
    rcases Int.eq_negSucc_of_lt_zero hi_neg with ⟨j, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_range]
    apply (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
      (candidatePastGapPath z.1.1) hdiv hmono t j).mpr
    rw [candidatePalmArrival_negSucc] at hinter
    simpa [candidatePastGapSum, arrivalTime, candidatePastGapPath, interarrival] using
      (neg_le_neg_iff.mp hinter.1)
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨j, hj, rfl⟩
    apply (mem_palmTaggedArrivalIndices_iff (-t) 0 z.1.1 hgood.1 _).mpr
    constructor
    · rw [candidatePalmArrival_negSucc]
      have harrival : arrivalTime j (candidatePastGapPath z.1.1) ≤ t :=
        (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
          (candidatePastGapPath z.1.1) hdiv hmono t j).mp
          (by simpa only [Finset.mem_range] using hj)
      have hsum : candidatePastGapSum z.1.1 (j + 1) ≤ t := by
        simpa [candidatePastGapSum, arrivalTime, candidatePastGapPath, interarrival] using harrival
      linarith
    · have harrival := hstrict (Int.negSucc_lt_zero j)
      rw [hgood.2] at harrival
      exact harrival

/-- The arbitrary literal `[-t,0)` target-work ledger is the canonical marked
work sum of the same past gap and work paths. -/
theorem stationaryAdmittedTargetPalmPastWindowLedgerWork_eq_canonicalMarkedWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hgood : palmTaggedArrivalGoodCarrier z.1.1) (t : Real) :
    stationaryAdmittedTargetPalmPastWindowLedgerWork target z t =
      canonicalMarkedWork (candidatePastGapPath z.1.1)
        (candidatePastGapPath z.1.2) t := by
  rw [stationaryAdmittedTargetPalmPastWindowLedgerWork,
    stationaryAdmittedTargetPalmPastWindowLedgerIndices_eq_canonicalRangeImage target z hgood t,
    canonicalMarkedWork, Finset.sum_image]
  · rfl
  · intro a _ha b _hb hab
    exact Int.negSucc.inj hab

/-- Measurability of the literal negative-index gap reindexing used for both
the target arrival path and its work-mark path. -/
theorem sla2026_measurable_candidatePastGapPath :
    Measurable candidatePastGapPath := by
  refine measurable_pi_iff.2 fun n => ?_
  exact measurable_twoSidedGap (Int.negSucc n)

/-- The literal negative-index reindexing of a two-sided exponential path has
the canonical one-sided exponential renewal law. -/
theorem sla2026_candidatePastGapPath_measurePreserving
    {rate : Real} (hrate : 0 < rate) :
    MeasurePreserving candidatePastGapPath
      (twoSidedInterarrivalMeasure rate)
      (exponentialInterarrivalMeasure rate) :=
  ⟨sla2026_measurable_candidatePastGapPath,
    (candidatePastGapPath_hasLaw hrate).map_eq⟩

/-- In the literal marked two-sided source product, the past gap path has its
canonical rate-`rate` exponential renewal law. -/
theorem twoSidedMarkedRenewalPastGapPath_fst_measurePreserving
    {rate : Real} (hrate : 0 < rate) :
    MeasurePreserving
      (fun z : TwoSidedMarkedRenewalSample => candidatePastGapPath z.1)
      (twoSidedMarkedRenewalMeasure rate)
      (exponentialInterarrivalMeasure rate) := by
  let μg : Measure (Int -> Real) := twoSidedInterarrivalMeasure rate
  let μw : Measure (Int -> Real) := twoSidedInterarrivalMeasure (1 : Real)
  letI : IsProbabilityMeasure μg := isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hfst : MeasurePreserving
      (Prod.fst : (Int -> Real) × (Int -> Real) -> Int -> Real)
      (μg.prod μw) μg := measurePreserving_fst
  simpa [twoSidedMarkedRenewalMeasure, μg, μw, Function.comp_def] using
    (sla2026_candidatePastGapPath_measurePreserving hrate).comp hfst

/-- In the same literal marked source product, the negative-index work marks
have the canonical unit-exponential work-path law. -/
theorem twoSidedMarkedRenewalPastWorkPath_snd_measurePreserving
    {rate : Real} (hrate : 0 < rate) :
    MeasurePreserving
      (fun z : TwoSidedMarkedRenewalSample => candidatePastGapPath z.2)
      (twoSidedMarkedRenewalMeasure rate)
      (exponentialInterarrivalMeasure (1 : Real)) := by
  let μg : Measure (Int -> Real) := twoSidedInterarrivalMeasure rate
  let μw : Measure (Int -> Real) := twoSidedInterarrivalMeasure (1 : Real)
  letI : IsProbabilityMeasure μg := isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hsnd : MeasurePreserving
      (Prod.snd : (Int -> Real) × (Int -> Real) -> Int -> Real)
      (μg.prod μw) μw := measurePreserving_snd
  simpa [twoSidedMarkedRenewalMeasure, μg, μw, Function.comp_def] using
    (sla2026_candidatePastGapPath_measurePreserving
      (rate := (1 : Real)) (by norm_num)).comp hsnd

/-- The canonical marked work accumulated along the literal past half of a
two-sided marked renewal source has real-time rate `rate`. -/
theorem ae_tendsto_twoSidedMarkedRenewalPastCanonicalWork_div_atTop
    {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (candidatePastGapPath z.1)
            (candidatePastGapPath z.2) t / t)
        atTop (nhds rate) := by
  exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    hrate
    (fun z : TwoSidedMarkedRenewalSample => candidatePastGapPath z.1)
    (fun z : TwoSidedMarkedRenewalSample => candidatePastGapPath z.2)
    (twoSidedMarkedRenewalPastGapPath_fst_measurePreserving hrate)
    (twoSidedMarkedRenewalPastWorkPath_snd_measurePreserving hrate)

/-- Under the genuine target/passive Palm law, the literal target past gap and
work paths have their real-time canonical marked-work source rate. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmPastCanonicalWork_div_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (candidatePastGapPath z.1.1)
            (candidatePastGapPath z.1.2) t / t)
        atTop (nhds (M.admittedRate target)) := by
  have hlaw := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hmap : ∀ᵐ x ∂Measure.map
      (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (candidatePastGapPath x.1)
            (candidatePastGapPath x.2) t / t)
        atTop (nhds (M.admittedRate target)) := by
    rw [hlaw.map_eq]
    exact ae_tendsto_twoSidedMarkedRenewalPastCanonicalWork_div_atTop
      (M.admittedRate_pos target)
  simpa [stationaryAdmittedTargetPalmMarkedRenewalSample] using
    (Measure.tendsto_ae_map hlaw.aemeasurable hmap)

/-- The actual literal target work in the half-open window `[-t,0)` has
real-time source rate `admittedRate` under the genuine target/passive Palm
law. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmPastWindowLedgerWork_div_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          stationaryAdmittedTargetPalmPastWindowLedgerWork target z t / t)
        atTop (nhds (M.admittedRate target)) := by
  filter_upwards [M.ae_stationaryAdmittedTargetPassivePalmGoodCarrier target,
    M.ae_tendsto_stationaryAdmittedTargetPalmPastCanonicalWork_div_atTop target]
    with z hgood hwork
  have hfun :
      (fun t : Real =>
        stationaryAdmittedTargetPalmPastWindowLedgerWork target z t / t) =
      fun t : Real =>
        canonicalMarkedWork (candidatePastGapPath z.1.1)
          (candidatePastGapPath z.1.2) t / t := by
    funext t
    rw [stationaryAdmittedTargetPalmPastWindowLedgerWork_eq_canonicalMarkedWork
      target z hgood t]
  rw [hfun]
  exact hwork

/-- Under the genuine target/passive Palm law, literal cumulative past target
work divided by literal elapsed past time has source rate `admittedRate`.
This is a marked-renewal input law, not a queue conclusion. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmPastCumulativeWork_div_elapsedTime
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : Nat =>
          stationaryAdmittedTargetPalmPastCumulativeWork target z n /
            stationaryAdmittedTargetPalmPastElapsedTime target z n)
        atTop (nhds (M.admittedRate target)) := by
  have hlaw := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hmap : ∀ᵐ x ∂Measure.map
      (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : Nat =>
          markedRenewalPastCumulativeWork x n / markedRenewalPastElapsedTime x n)
        atTop (nhds (M.admittedRate target)) := by
    rw [hlaw.map_eq]
    exact ae_tendsto_markedRenewalPastWork_div_elapsedTime
      (M.admittedRate_pos target)
  simpa [stationaryAdmittedTargetPalmPastCumulativeWork,
    stationaryAdmittedTargetPalmPastElapsedTime] using
    (Measure.tendsto_ae_map hlaw.aemeasurable hmap)

/-- The literal positive elapsed times of successively older target arrivals
diverge under the genuine target/passive Palm law. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmPastElapsedTime_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto (fun n : Nat => stationaryAdmittedTargetPalmPastElapsedTime target z n)
        atTop atTop := by
  let rate := M.admittedRate target
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (M.admittedRate_pos target)
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hsource : ∀ᵐ x ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto (fun n : Nat => markedRenewalPastElapsedTime x n) atTop atTop := by
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : Real)))
      (f := Prod.fst)
      (p := fun gap : Int -> Real =>
        Tendsto (fun n : Nat => candidatePastGapSum gap (n + 1)) atTop atTop)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_candidatePastGapSum_succ_tendsto_atTop (M.admittedRate_pos target)
  have hlaw := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hmap : ∀ᵐ x ∂Measure.map
      (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto (fun n : Nat => markedRenewalPastElapsedTime x n) atTop atTop := by
    rw [hlaw.map_eq]
    simpa [rate, markedRenewalPastElapsedTime_eq_candidatePastGapSum] using hsource
  simpa [stationaryAdmittedTargetPalmPastElapsedTime] using
    (Measure.tendsto_ae_map hlaw.aemeasurable hmap)

/-- The actual half-open target ledger at successive literal past-arrival
starts has its marked-work rate.  Its denominator is `-start`, the positive
elapsed time from that real source arrival to the Palm epoch. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmPastLedgerWork_div_neg_start
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : Nat =>
          stationaryAdmittedTargetPalmPastLedgerWork target z n /
            (-stationaryAdmittedTargetPalmPastStart target z n))
        atTop (nhds (M.admittedRate target)) := by
  filter_upwards [M.ae_stationaryAdmittedTargetPassivePalmGoodCarrier target,
    M.ae_tendsto_stationaryAdmittedTargetPalmPastCumulativeWork_div_elapsedTime target]
    with z hgood hrate
  have hfun :
      (fun n : Nat =>
        stationaryAdmittedTargetPalmPastLedgerWork target z n /
          (-stationaryAdmittedTargetPalmPastStart target z n)) =
      fun n : Nat =>
        stationaryAdmittedTargetPalmPastCumulativeWork target z n /
          stationaryAdmittedTargetPalmPastElapsedTime target z n := by
    funext n
    rw [stationaryAdmittedTargetPalmPastLedgerWork_eq_cumulativeWork target z hgood n,
      stationaryAdmittedTargetPalmPastStart_eq_neg_elapsedTime]
    simp only [neg_neg]
  rw [hfun]
  exact hrate

/-- The negative of each literal remote target start is its elapsed past time,
and therefore tends to infinity under the target/passive Palm source law. -/
theorem ae_tendsto_neg_stationaryAdmittedTargetPalmPastStart_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto (fun n : Nat => -stationaryAdmittedTargetPalmPastStart target z n)
        atTop atTop := by
  filter_upwards [M.ae_tendsto_stationaryAdmittedTargetPalmPastElapsedTime_atTop target]
    with z htime
  have hfun :
      (fun n : Nat => -stationaryAdmittedTargetPalmPastStart target z n) =
      fun n : Nat => stationaryAdmittedTargetPalmPastElapsedTime target z n := by
    funext n
    rw [stationaryAdmittedTargetPalmPastStart_eq_neg_elapsedTime]
    simp only [neg_neg]
  rw [hfun]
  exact htime

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements

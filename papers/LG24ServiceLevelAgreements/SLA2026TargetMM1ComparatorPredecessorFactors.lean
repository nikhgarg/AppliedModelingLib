import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalPredecessorFactors
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorResponse
import Mathlib.Tactic

/-!
# Predecessor innovation factor for the direct target M/M/1 comparator

This file turns the generic direct-source predecessor factorization into the
actual causal response input for the one-arrival Lindley equation.  The
predecessor-to-current interarrival gap is intentionally kept outside the
second factor.  The second factor contains exactly the predecessor's own
work, its older work, and its older gaps; it is sufficient to reconstruct the
predecessor response and contains no copy of the displayed innovation.

The result is a source-native independence bridge.  It neither solves the
Lindley fixed point nor asserts an M/M/1 tail formula.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace DirectMarkedRenewalComparator

/-- The causal input seen from the predecessor tag: its own work, the older
work path, and the older gap path. -/
abbrev PredecessorCausalInput := (ℝ × (ℕ → ℝ)) × (ℕ → ℝ)

/-- The direct product law carried by a predecessor causal input at admitted
arrival rate `rate`. -/
noncomputable def predecessorCausalInputMeasure (rate : ℝ) :
    Measure PredecessorCausalInput :=
  ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
    (exponentialInterarrivalMeasure rate)

/-- Work of the predecessor tag itself. -/
def predecessorCausalTagWork (x : PredecessorCausalInput) : Real := x.1.1

/-- Literal work of the `n`th job before the predecessor tag. -/
def predecessorCausalRemotePastBatch (x : PredecessorCausalInput) (n : Nat) : Real :=
  x.1.2 n

/-- Constant service available after that older job and before its newer
neighbour. -/
def predecessorCausalRemotePastService (serviceRate : Real)
    (x : PredecessorCausalInput) (n : Nat) : Real :=
  serviceRate * x.2 n

/-- Finite chronological replay of a predecessor causal input. -/
def predecessorCausalFinitePreTagWorkload (serviceRate : Real)
    (x : PredecessorCausalInput) (remoteStart : Nat) : Real :=
  lateBatchPreWorkload
    (reverseRemotePastIncrement (predecessorCausalRemotePastBatch x) remoteStart)
    (reverseRemotePastIncrement (predecessorCausalRemotePastService serviceRate x) remoteStart)
    remoteStart

/-- The remote finite replays of a predecessor causal input eventually
stabilize. -/
def PredecessorCausalPreTagCoalesces (serviceRate : Real)
    (x : PredecessorCausalInput) : Prop :=
  ∃ K, ∀ N ≥ K,
    predecessorCausalFinitePreTagWorkload serviceRate x N =
      predecessorCausalFinitePreTagWorkload serviceRate x K

/-- Totalized selected predecessor workload.  As for the original direct
functional, the fallback is used only away from coalescence. -/
noncomputable def predecessorCausalPreTagWorkload (serviceRate : Real)
    (x : PredecessorCausalInput) : Real := by
  classical
  exact if h : PredecessorCausalPreTagCoalesces serviceRate x then
    predecessorCausalFinitePreTagWorkload serviceRate x (Nat.find h)
  else 0

/-- Literal FCFS response reconstructed from the predecessor causal input. -/
noncomputable def predecessorCausalResponse (serviceRate : Real)
    (x : PredecessorCausalInput) : Real :=
  (predecessorCausalPreTagWorkload serviceRate x + predecessorCausalTagWork x) /
    serviceRate

/-- Globally measurable limsup version of the predecessor causal workload. -/
noncomputable def measurablePredecessorCausalPreTagWorkload (serviceRate : Real)
    (x : PredecessorCausalInput) : Real :=
  limsup (fun n => predecessorCausalFinitePreTagWorkload serviceRate x n) atTop

/-- Globally measurable limsup version of the predecessor causal response. -/
noncomputable def measurablePredecessorCausalResponse (serviceRate : Real)
    (x : PredecessorCausalInput) : Real :=
  (measurablePredecessorCausalPreTagWorkload serviceRate x +
    predecessorCausalTagWork x) / serviceRate

/-- Finite causal replays are measurable in all literal input coordinates. -/
theorem measurable_predecessorCausalFinitePreTagWorkload
    (serviceRate : Real) (remoteStart : Nat) :
    Measurable (fun x : PredecessorCausalInput =>
      predecessorCausalFinitePreTagWorkload serviceRate x remoteStart) := by
  let batch : Nat → PredecessorCausalInput → Real :=
    fun i x => reverseRemotePastIncrement
      (predecessorCausalRemotePastBatch x) remoteStart i
  let service : Nat → PredecessorCausalInput → Real :=
    fun i x => reverseRemotePastIncrement
      (predecessorCausalRemotePastService serviceRate x) remoteStart i
  have hbatch : ∀ i, Measurable (batch i) := by
    intro i
    simpa [batch, reverseRemotePastIncrement, predecessorCausalRemotePastBatch] using
      (measurable_pi_apply (remoteStart - (i + 1))).comp
        (measurable_snd.comp measurable_fst)
  have hservice : ∀ i, Measurable (service i) := by
    intro i
    simpa [service, reverseRemotePastIncrement, predecessorCausalRemotePastService] using
      measurable_const.mul
        ((measurable_pi_apply (remoteStart - (i + 1))).comp measurable_snd)
  have hpost : ∀ n : Nat, Measurable (fun x : PredecessorCausalInput =>
      lateBatchPostWorkload (fun i => batch i x) (fun i => service i x) n) := by
    intro n
    induction n with
    | zero =>
        simpa [lateBatchPostWorkload] using hbatch 0
    | succ n hn =>
        simpa [lateBatchPostWorkload, lateBatchUpdate] using
          ((hn.sub (hservice n)).max measurable_const).add (hbatch (n + 1))
  cases remoteStart with
  | zero =>
      simpa [predecessorCausalFinitePreTagWorkload, batch, service,
        lateBatchPreWorkload] using
        (measurable_const : Measurable (fun _ : PredecessorCausalInput => (0 : Real)))
  | succ n =>
      simpa [predecessorCausalFinitePreTagWorkload, batch, service,
        lateBatchPreWorkload] using ((hpost n).sub (hservice n)).max measurable_const

/-- The limsup predecessor workload is globally measurable. -/
theorem measurable_measurablePredecessorCausalPreTagWorkload (serviceRate : Real) :
    Measurable (measurablePredecessorCausalPreTagWorkload serviceRate) := by
  unfold measurablePredecessorCausalPreTagWorkload
  exact Measurable.limsup
    (fun n => measurable_predecessorCausalFinitePreTagWorkload serviceRate n)

/-- The limsup predecessor response is globally measurable. -/
theorem measurable_measurablePredecessorCausalResponse (serviceRate : Real) :
    Measurable (measurablePredecessorCausalResponse serviceRate) := by
  exact
    (measurable_measurablePredecessorCausalPreTagWorkload serviceRate).add
      (measurable_fst.comp measurable_fst) |>.div measurable_const

/-- The causal factor of an original sample exactly reproduces the finite
pre-tag replay seen after moving the tag one literal arrival backwards. -/
theorem predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) (remoteStart : Nat) :
    predecessorCausalFinitePreTagWorkload serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2 remoteStart =
      finitePreTagWorkload serviceRate
        (twoSidedMarkedRenewalIndexShift (-1) z) remoteStart := by
  congr 2

/-- Coalescence is preserved exactly by the causal factor/recentering
identification. -/
theorem predecessorCausalPreTagCoalesces_iff_indexShift_negOne
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    PredecessorCausalPreTagCoalesces serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2 ↔
      PreTagCoalesces serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro N hN
    rw [← predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne,
      ← predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne]
    exact hK N hN
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro N hN
    rw [predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne,
      predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne]
    exact hK N hN

/-- The selected predecessor workload is literally the selected workload of
the one-arrival-recentered direct sample. -/
theorem predecessorCausalPreTagWorkload_eq_indexShift_negOne
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    predecessorCausalPreTagWorkload serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2 =
      preTagWorkload serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) := by
  classical
  by_cases h : PredecessorCausalPreTagCoalesces serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2
  · have hshift : PreTagCoalesces serviceRate
      (twoSidedMarkedRenewalIndexShift (-1) z) :=
        (predecessorCausalPreTagCoalesces_iff_indexShift_negOne serviceRate z).1 h
    rw [predecessorCausalPreTagWorkload, dif_pos h, preTagWorkload, dif_pos hshift]
    have hfind : Nat.find h = Nat.find hshift := by
      apply Nat.find_congr'
      intro n
      change
        (∀ N ≥ n, predecessorCausalFinitePreTagWorkload serviceRate
          (markedRenewalPredecessorGapShiftedPastFactors z).2 N =
          predecessorCausalFinitePreTagWorkload serviceRate
            (markedRenewalPredecessorGapShiftedPastFactors z).2 n) ↔
          (∀ N ≥ n, finitePreTagWorkload serviceRate
            (twoSidedMarkedRenewalIndexShift (-1) z) N =
            finitePreTagWorkload serviceRate
              (twoSidedMarkedRenewalIndexShift (-1) z) n)
      constructor <;> intro hn N hN
      · rw [← predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne,
            ← predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne]
        exact hn N hN
      · rw [predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne,
            predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne]
        exact hn N hN
    rw [hfind, predecessorCausalFinitePreTagWorkload_eq_indexShift_negOne]
  · have hshift : ¬ PreTagCoalesces serviceRate
      (twoSidedMarkedRenewalIndexShift (-1) z) := by
        intro hshift
        exact h ((predecessorCausalPreTagCoalesces_iff_indexShift_negOne serviceRate z).2 hshift)
    rw [predecessorCausalPreTagWorkload, dif_neg h, preTagWorkload, dif_neg hshift]

/-- The literal predecessor response is a function only of the causal factor
and is exactly the response after recentering one arrival backwards. -/
theorem predecessorCausalResponse_eq_indexShift_negOne
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    predecessorCausalResponse serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2 =
      response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) := by
  unfold predecessorCausalResponse response predecessorCausalTagWork tagWork
  rw [predecessorCausalPreTagWorkload_eq_indexShift_negOne]
  rfl

/-- The measurable causal workload is the limsup workload of the recentered
direct sample, pointwise rather than merely almost everywhere. -/
theorem measurablePredecessorCausalPreTagWorkload_eq_indexShift_negOne
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    measurablePredecessorCausalPreTagWorkload serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2 =
      measurablePreTagWorkload serviceRate
        (twoSidedMarkedRenewalIndexShift (-1) z) := by
  unfold measurablePredecessorCausalPreTagWorkload measurablePreTagWorkload
  congr 1

/-- The measurable causal response is the measurable direct response after
one-arrival recentering. -/
theorem measurablePredecessorCausalResponse_eq_indexShift_negOne
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    measurablePredecessorCausalResponse serviceRate
      (markedRenewalPredecessorGapShiftedPastFactors z).2 =
      measurableResponse serviceRate
        (twoSidedMarkedRenewalIndexShift (-1) z) := by
  unfold measurablePredecessorCausalResponse measurableResponse
  rw [measurablePredecessorCausalPreTagWorkload_eq_indexShift_negOne]
  rfl

/-- The displayed innovation coordinate on the original source carrier. -/
def predecessorGap (z : TwoSidedMarkedRenewalSample) : Real :=
  (markedRenewalPredecessorGapShiftedPastFactors z).1

/-- The exact causal input extracted from the original source carrier. -/
def predecessorCausalInput (z : TwoSidedMarkedRenewalSample) : PredecessorCausalInput :=
  (markedRenewalPredecessorGapShiftedPastFactors z).2

/-- The predecessor innovation is precisely the physical gap from the
predecessor target arrival to the current target arrival. -/
theorem predecessorGap_eq_markedRenewalPastGap
    (z : TwoSidedMarkedRenewalSample) :
    predecessorGap z = markedRenewalPastGap z 0 := by
  rfl

/-- The causal factor response viewed back on the original marked-renewal
source carrier. -/
noncomputable def measurablePredecessorCausalResponseOnSource
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) : Real :=
  measurablePredecessorCausalResponse serviceRate (predecessorCausalInput z)

theorem measurable_predecessorGap : Measurable predecessorGap := by
  exact measurable_fst.comp measurable_markedRenewalPredecessorGapShiftedPastFactors

theorem measurable_predecessorCausalInput : Measurable predecessorCausalInput := by
  exact measurable_snd.comp measurable_markedRenewalPredecessorGapShiftedPastFactors

theorem measurable_measurablePredecessorCausalResponseOnSource
    (serviceRate : Real) :
    Measurable (measurablePredecessorCausalResponseOnSource serviceRate) := by
  exact (measurable_measurablePredecessorCausalResponse serviceRate).comp
    measurable_predecessorCausalInput

/-- The source pair of innovation and causal input has the exact direct
product law. -/
theorem map_predecessorGapAndCausalInput_twoSidedMarkedRenewalMeasure
    {rate : Real} (hrate : 0 < rate) :
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
      (predecessorGap z, predecessorCausalInput z))
      (twoSidedMarkedRenewalMeasure rate) =
      (expMeasure rate).prod (predecessorCausalInputMeasure rate) := by
  simpa [predecessorGap, predecessorCausalInput, predecessorCausalInputMeasure] using
    map_markedRenewalPredecessorGapShiftedPastFactors_twoSidedMarkedRenewalMeasure hrate

/-- The predecessor innovation has its literal rate-`rate` exponential law. -/
theorem predecessorGap_hasLaw
    {rate : Real} (hrate : 0 < rate) :
    HasLaw predecessorGap (expMeasure rate) (twoSidedMarkedRenewalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (predecessorCausalInputMeasure rate) := by
    unfold predecessorCausalInputMeasure
    infer_instance
  refine ⟨measurable_predecessorGap.aemeasurable, ?_⟩
  calc
    Measure.map predecessorGap (twoSidedMarkedRenewalMeasure rate) =
        Measure.map Prod.fst
          (Measure.map (fun z : TwoSidedMarkedRenewalSample =>
            (predecessorGap z, predecessorCausalInput z))
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map measurable_fst
            (measurable_predecessorGap.prodMk measurable_predecessorCausalInput)]
          rfl
    _ = Measure.map Prod.fst
        ((expMeasure rate).prod (predecessorCausalInputMeasure rate)) := by
          rw [map_predecessorGapAndCausalInput_twoSidedMarkedRenewalMeasure hrate]
    _ = expMeasure rate := by
          rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The direct source response induced by the predecessor causal input has
its literal pushforward law under the corresponding product factor. -/
theorem measurablePredecessorCausalResponseOnSource_hasLaw
    {rate : Real} (serviceRate : Real) (hrate : 0 < rate) :
    HasLaw (measurablePredecessorCausalResponseOnSource serviceRate)
      (Measure.map (measurablePredecessorCausalResponse serviceRate)
        (predecessorCausalInputMeasure rate))
      (twoSidedMarkedRenewalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (predecessorCausalInputMeasure rate) := by
    unfold predecessorCausalInputMeasure
    infer_instance
  refine ⟨(measurable_measurablePredecessorCausalResponseOnSource serviceRate).aemeasurable,
    ?_⟩
  calc
    Measure.map (measurablePredecessorCausalResponseOnSource serviceRate)
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map (measurablePredecessorCausalResponse serviceRate)
          (Measure.map predecessorCausalInput
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map (measurable_measurablePredecessorCausalResponse serviceRate)
            measurable_predecessorCausalInput]
          rfl
    _ = Measure.map (measurablePredecessorCausalResponse serviceRate)
        (predecessorCausalInputMeasure rate) := by
          have hpair := map_predecessorGapAndCausalInput_twoSidedMarkedRenewalMeasure hrate
          have hsecond :
              Measure.map predecessorCausalInput (twoSidedMarkedRenewalMeasure rate) =
                predecessorCausalInputMeasure rate := by
            calc
              Measure.map predecessorCausalInput (twoSidedMarkedRenewalMeasure rate) =
                  Measure.map Prod.snd
                    (Measure.map (fun z : TwoSidedMarkedRenewalSample =>
                      (predecessorGap z, predecessorCausalInput z))
                      (twoSidedMarkedRenewalMeasure rate)) := by
                    symm
                    rw [Measure.map_map measurable_snd
                      (measurable_predecessorGap.prodMk measurable_predecessorCausalInput)]
                    rfl
              _ = Measure.map Prod.snd
                  ((expMeasure rate).prod (predecessorCausalInputMeasure rate)) := by
                    rw [hpair]
              _ = predecessorCausalInputMeasure rate := by
                    rw [Measure.map_snd_prod, measure_univ, one_smul]
          rw [hsecond]

/-- Joint law of the predecessor gap and the response produced from the
causal factor.  This is the usable product-law form of their independence. -/
theorem predecessorGapAndMeasurableCausalResponseOnSource_hasLaw
    {rate : Real} (serviceRate : Real) (hrate : 0 < rate) :
    HasLaw (fun z : TwoSidedMarkedRenewalSample =>
      (predecessorGap z,
        measurablePredecessorCausalResponseOnSource serviceRate z))
      ((expMeasure rate).prod
        (Measure.map (measurablePredecessorCausalResponse serviceRate)
          (predecessorCausalInputMeasure rate)))
      (twoSidedMarkedRenewalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (predecessorCausalInputMeasure rate) := by
    unfold predecessorCausalInputMeasure
    infer_instance
  have hfactor := map_predecessorGapAndCausalInput_twoSidedMarkedRenewalMeasure hrate
  refine ⟨(measurable_predecessorGap.prodMk
    (measurable_measurablePredecessorCausalResponseOnSource serviceRate)).aemeasurable, ?_⟩
  calc
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        (predecessorGap z,
          measurablePredecessorCausalResponseOnSource serviceRate z))
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map (Prod.map id (measurablePredecessorCausalResponse serviceRate))
          (Measure.map (fun z : TwoSidedMarkedRenewalSample =>
            (predecessorGap z, predecessorCausalInput z))
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map
            (measurable_id.prodMap
              (measurable_measurablePredecessorCausalResponse serviceRate))
            (measurable_predecessorGap.prodMk measurable_predecessorCausalInput)]
          rfl
    _ = Measure.map (Prod.map id (measurablePredecessorCausalResponse serviceRate))
        ((expMeasure rate).prod (predecessorCausalInputMeasure rate)) := by
          rw [hfactor]
    _ = (expMeasure rate).prod
        (Measure.map (measurablePredecessorCausalResponse serviceRate)
          (predecessorCausalInputMeasure rate)) := by
          rw [← Measure.map_prod_map _ _ measurable_id
            (measurable_measurablePredecessorCausalResponse serviceRate), Measure.map_id]

/-- The predecessor-to-current gap is independent of the response produced
from the older causal input. -/
theorem indepFun_predecessorGap_measurableCausalResponseOnSource
    {rate : Real} (serviceRate : Real) (hrate : 0 < rate) :
    predecessorGap ⟂ᵢ[twoSidedMarkedRenewalMeasure rate]
      measurablePredecessorCausalResponseOnSource serviceRate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (predecessorCausalInputMeasure rate) := by
    unfold predecessorCausalInputMeasure
    infer_instance
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (twoSidedMarkedRenewalMeasure rate) := by
    unfold twoSidedMarkedRenewalMeasure
    infer_instance
  apply (indepFun_iff_map_prod_eq_prod_map_map
    measurable_predecessorGap.aemeasurable
    (measurable_measurablePredecessorCausalResponseOnSource serviceRate).aemeasurable).2
  rw [(predecessorGapAndMeasurableCausalResponseOnSource_hasLaw
      (serviceRate := serviceRate) hrate).map_eq,
    (predecessorGap_hasLaw hrate).map_eq,
    (measurablePredecessorCausalResponseOnSource_hasLaw
      (serviceRate := serviceRate) hrate).map_eq]

/-- Under strict direct stability, the measurable causal-factor response
agrees almost surely with the selected direct response after a one-arrival
recenter. -/
theorem ae_measurableCausalResponseOnSource_eq_indexShift_negOne_response_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    measurablePredecessorCausalResponseOnSource serviceRate =ᵐ[
      twoSidedMarkedRenewalMeasure rate]
      fun z => response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) := by
  have hshift : MeasurePreserving (twoSidedMarkedRenewalIndexShift (-1))
      (twoSidedMarkedRenewalMeasure rate) (twoSidedMarkedRenewalMeasure rate) :=
    twoSidedMarkedRenewalIndexShift_measurePreserving hrate (-1)
  have hresponse : response serviceRate =ᵐ[twoSidedMarkedRenewalMeasure rate]
      measurableResponse serviceRate :=
    ae_response_eq_measurableResponse_of_rate_lt hrate hstable
  have hresponseMap : ∀ᵐ x ∂Measure.map (twoSidedMarkedRenewalIndexShift (-1))
      (twoSidedMarkedRenewalMeasure rate),
      response serviceRate x = measurableResponse serviceRate x := by
    rw [hshift.map_eq]
    exact hresponse
  have hresponseShift : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) =
        measurableResponse serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) :=
    Measure.tendsto_ae_map hshift.measurable.aemeasurable hresponseMap
  filter_upwards [hresponseShift] with z hz
  exact (measurablePredecessorCausalResponse_eq_indexShift_negOne serviceRate z).trans hz.symm

/-- Consequently, the physical predecessor-to-current gap is independent of
the literal selected response at the predecessor arrival under strict direct
stability. -/
theorem indepFun_predecessorGap_indexShift_negOne_response_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    predecessorGap ⟂ᵢ[twoSidedMarkedRenewalMeasure rate]
      (fun z => response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z)) := by
  refine (indepFun_predecessorGap_measurableCausalResponseOnSource
    (serviceRate := serviceRate) hrate).congr (Filter.Eventually.of_forall fun _ => rfl) ?_
  exact ae_measurableCausalResponseOnSource_eq_indexShift_negOne_response_of_rate_lt
    hrate hstable

end DirectMarkedRenewalComparator

end

end LG24ServiceLevelAgreements

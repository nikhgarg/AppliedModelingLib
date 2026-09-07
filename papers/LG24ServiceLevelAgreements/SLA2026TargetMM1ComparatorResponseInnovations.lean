import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorFixedPoint
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorPredecessorFactors
import Mathlib.Tactic

/-!
# Independent innovations in the direct marked-renewal response recursion

The direct response recurrence uses the current tag work together with the
predecessor-to-current gap and the predecessor response.  This module proves
the exact product decomposition needed for that recurrence on the literal
marked-renewal carrier.  The current work is separated from the complete
negative-time input, while the predecessor response is reconstructed only
from that negative-time input.

The measurable predecessor response is used first, so that the factorization
is an exact statement of pushforward measures.  Strict stability then
transports the result to the selected predecessor response almost surely.
No M/M/1 fixed-point solution or tail formula is asserted here.
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

/-- Algebraic normalization of a service-rate workload update into its
response-time form. -/
private theorem normalize_response_update
    (work predecessorWork gap tagWork serviceRate : Real)
    (hservice : 0 < serviceRate) :
    (max (work + predecessorWork - serviceRate * gap) 0 + tagWork) / serviceRate =
      max ((work + predecessorWork) / serviceRate - gap) 0 +
        tagWork / serviceRate := by
  rw [add_div]
  congr 1
  rw [show (work + predecessorWork) / serviceRate - gap =
      (work + predecessorWork - serviceRate * gap) / serviceRate by
        field_simp [ne_of_gt hservice]]
  simpa using
    (max_div_div_right hservice.le
      (work + predecessorWork - serviceRate * gap) 0).symm

/-- On coalescent samples, the direct response itself obeys the literal
one-arrival M/M/1 response recursion: the predecessor response loses the
physical gap, is reflected at zero, then receives the current tag's own
service time. -/
theorem response_eq_indexShift_negOne_response_update_of_coalesces
    (serviceRate : Real) (hservice : 0 < serviceRate)
    (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z)
    (hshiftcoal : PreTagCoalesces serviceRate
      (twoSidedMarkedRenewalIndexShift (-1) z)) :
    response serviceRate z =
      max
        (response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) -
          predecessorGap z) 0 +
        tagWork z / serviceRate := by
  rw [response_eq_indexShift_negOne_update_of_coalesces
    serviceRate z hcoal hshiftcoal]
  change
    (max
      (preTagWorkload serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) +
        tagWork (twoSidedMarkedRenewalIndexShift (-1) z) -
          serviceRate * predecessorGap z) 0 + tagWork z) / serviceRate =
      max
        ((preTagWorkload serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) +
          tagWork (twoSidedMarkedRenewalIndexShift (-1) z)) / serviceRate -
          predecessorGap z) 0 +
        tagWork z / serviceRate
  exact normalize_response_update
    (preTagWorkload serviceRate (twoSidedMarkedRenewalIndexShift (-1) z))
    (tagWork (twoSidedMarkedRenewalIndexShift (-1) z))
    (predecessorGap z) (tagWork z) serviceRate hservice

/-- Strict stability makes the literal direct response recursion hold almost
surely on the direct marked-renewal source. -/
theorem ae_response_eq_indexShift_negOne_response_update_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      response serviceRate z =
        max
          (response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) -
            predecessorGap z) 0 +
          tagWork z / serviceRate := by
  have hservice : 0 < serviceRate := lt_trans hrate hstable
  have hcoal : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      PreTagCoalesces serviceRate z :=
    ae_preTagCoalesces_of_rate_lt hrate hstable
  have hshiftMap : MeasurePreserving (twoSidedMarkedRenewalIndexShift (-1))
      (twoSidedMarkedRenewalMeasure rate) (twoSidedMarkedRenewalMeasure rate) :=
    twoSidedMarkedRenewalIndexShift_measurePreserving hrate (-1)
  have hshiftCoalMap : ∀ᵐ x ∂Measure.map
      (twoSidedMarkedRenewalIndexShift (-1)) (twoSidedMarkedRenewalMeasure rate),
      PreTagCoalesces serviceRate x := by
    rw [hshiftMap.map_eq]
    exact hcoal
  have hshiftCoal : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      PreTagCoalesces serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) :=
    Measure.tendsto_ae_map hshiftMap.measurable.aemeasurable hshiftCoalMap
  filter_upwards [hcoal, hshiftCoal] with z hz hzshift
  exact response_eq_indexShift_negOne_response_update_of_coalesces
    serviceRate hservice z hz hzshift

/-- One response-time update from a current tag work mark, a physical
predecessor gap, and a predecessor response. -/
def responseUpdate (serviceRate : Real) (x : ℝ × (ℝ × ℝ)) : Real :=
  max (x.2.2 - x.2.1) 0 + x.1 / serviceRate

theorem measurable_responseUpdate (serviceRate : Real) :
    Measurable (responseUpdate serviceRate) := by
  unfold responseUpdate
  exact
    ((measurable_snd.comp measurable_snd).sub
      (measurable_fst.comp measurable_snd)).max measurable_const |>.add
      (measurable_fst.div measurable_const)

/-- From the current-tag work/past factor, retain the physical predecessor
gap and exactly the predecessor causal input.  The current tag work is not
read by this map. -/
def tagWorkPastToPredecessorGapCausalInput
    (x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :
    ℝ × PredecessorCausalInput :=
  (x.2 0, ((x.1.2 0, fun n => x.1.2 (n + 1)), fun n => x.2 (n + 1)))

theorem measurable_tagWorkPastToPredecessorGapCausalInput :
    Measurable tagWorkPastToPredecessorGapCausalInput := by
  unfold tagWorkPastToPredecessorGapCausalInput
  let hworkTail : Measurable (fun x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) => x.1.2) :=
    measurable_snd.comp measurable_fst
  let hgapTail : Measurable (fun x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) => x.2) :=
    measurable_snd
  exact
    ((measurable_pi_apply 0).comp hgapTail).prodMk
      ((((measurable_pi_apply 0).comp hworkTail).prodMk
        (measurable_pi_iff.2 fun n =>
          (measurable_pi_apply (n + 1)).comp hworkTail)).prodMk
        (measurable_pi_iff.2 fun n =>
          (measurable_pi_apply (n + 1)).comp hgapTail))

/-- Apply the measurable predecessor response to the causal input retained
from the literal current-tag past factor. -/
noncomputable def tagWorkPastToPredecessorGapAndMeasurableResponse
    (serviceRate : Real) (x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) : ℝ × ℝ :=
  let y := tagWorkPastToPredecessorGapCausalInput x
  (y.1, measurablePredecessorCausalResponse serviceRate y.2)

theorem measurable_tagWorkPastToPredecessorGapAndMeasurableResponse
    (serviceRate : Real) :
    Measurable (tagWorkPastToPredecessorGapAndMeasurableResponse serviceRate) := by
  unfold tagWorkPastToPredecessorGapAndMeasurableResponse
  exact (measurable_fst.comp measurable_tagWorkPastToPredecessorGapCausalInput).prodMk
    ((measurable_measurablePredecessorCausalResponse serviceRate).comp
      (measurable_snd.comp measurable_tagWorkPastToPredecessorGapCausalInput))

/-- The current work/past factor reconstructs the literal predecessor gap
and causal input without using the current tag work. -/
theorem tagWorkPastToPredecessorGapCausalInput_apply
    (z : TwoSidedMarkedRenewalSample) :
    tagWorkPastToPredecessorGapCausalInput (markedRenewalTagWorkPastFactors z) =
      (predecessorGap z, predecessorCausalInput z) := by
  rfl

/-- Accordingly, the response pair reconstructed from the past factor is
the existing measurable predecessor-gap/response pair on the source. -/
theorem tagWorkPastToPredecessorGapAndMeasurableResponse_apply
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    tagWorkPastToPredecessorGapAndMeasurableResponse serviceRate
      (markedRenewalTagWorkPastFactors z) =
      (predecessorGap z,
        measurablePredecessorCausalResponseOnSource serviceRate z) := by
  unfold tagWorkPastToPredecessorGapAndMeasurableResponse
    measurablePredecessorCausalResponseOnSource
  rw [tagWorkPastToPredecessorGapCausalInput_apply]

/-- The negative-time marked history contains all negative work and gap
coordinates, but not the current tag work. -/
abbrev NegativeTimeMarkedHistory := (ℕ → ℝ) × (ℕ → ℝ)

/-- Separate the current tag work from the two negative-time coordinate
paths already retained by `markedRenewalTagWorkPastFactors`. -/
def tagWorkPastToTagAndNegativeTimeHistory
    (x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :
    ℝ × NegativeTimeMarkedHistory :=
  (x.1.1, (x.1.2, x.2))

theorem measurable_tagWorkPastToTagAndNegativeTimeHistory :
    Measurable tagWorkPastToTagAndNegativeTimeHistory := by
  unfold tagWorkPastToTagAndNegativeTimeHistory
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The current tag work and the complete negative-time marked history have
the corresponding product law on the literal source carrier. -/
theorem map_tagWorkAndNegativeTimeHistory_twoSidedMarkedRenewalMeasure
    {rate : Real} (hrate : 0 < rate) :
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
      tagWorkPastToTagAndNegativeTimeHistory (markedRenewalTagWorkPastFactors z))
      (twoSidedMarkedRenewalMeasure rate) =
      (expMeasure (1 : ℝ)).prod
        ((exponentialInterarrivalMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure rate)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  calc
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        tagWorkPastToTagAndNegativeTimeHistory (markedRenewalTagWorkPastFactors z))
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map tagWorkPastToTagAndNegativeTimeHistory
          (Measure.map markedRenewalTagWorkPastFactors
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map measurable_tagWorkPastToTagAndNegativeTimeHistory
            measurable_markedRenewalTagWorkPastFactors]
          rfl
    _ = Measure.map tagWorkPastToTagAndNegativeTimeHistory
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure rate)) := by
          rw [map_markedRenewalTagWorkPastFactors_twoSidedMarkedRenewalMeasure hrate]
    _ = (expMeasure (1 : ℝ)).prod
        ((exponentialInterarrivalMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure rate)) := by
          change Measure.map MeasurableEquiv.prodAssoc
            (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
              (exponentialInterarrivalMeasure rate)) = _
          rw [Measure.prodAssoc_prod]

/-- Read the current predecessor gap and the predecessor's causal input from
the negative-time marked history. -/
def negativeTimeHistoryToPredecessorGapCausalInput
    (x : NegativeTimeMarkedHistory) :
    ℝ × PredecessorCausalInput :=
  (x.2 0, ((x.1 0, fun n => x.1 (n + 1)), fun n => x.2 (n + 1)))

theorem measurable_negativeTimeHistoryToPredecessorGapCausalInput :
    Measurable negativeTimeHistoryToPredecessorGapCausalInput := by
  unfold negativeTimeHistoryToPredecessorGapCausalInput
  exact
    ((measurable_pi_apply 0).comp measurable_snd).prodMk
      ((((measurable_pi_apply 0).comp measurable_fst).prodMk
        (measurable_pi_iff.2 fun n =>
          (measurable_pi_apply (n + 1)).comp measurable_fst)).prodMk
        (measurable_pi_iff.2 fun n =>
          (measurable_pi_apply (n + 1)).comp measurable_snd))

/-- Apply the measurable predecessor response to the causal input recovered
from negative-time history. -/
noncomputable def negativeTimeHistoryToPredecessorGapAndMeasurableResponse
    (serviceRate : Real) (x : NegativeTimeMarkedHistory) : ℝ × ℝ :=
  let y := negativeTimeHistoryToPredecessorGapCausalInput x
  (y.1, measurablePredecessorCausalResponse serviceRate y.2)

theorem measurable_negativeTimeHistoryToPredecessorGapAndMeasurableResponse
    (serviceRate : Real) :
    Measurable (negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate) := by
  unfold negativeTimeHistoryToPredecessorGapAndMeasurableResponse
  exact (measurable_fst.comp measurable_negativeTimeHistoryToPredecessorGapCausalInput).prodMk
    ((measurable_measurablePredecessorCausalResponse serviceRate).comp
      (measurable_snd.comp measurable_negativeTimeHistoryToPredecessorGapCausalInput))

/-- The source predecessor gap and measurable predecessor response are a
function only of negative-time history. -/
theorem negativeTimeHistoryToPredecessorGapAndMeasurableResponse_apply
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate
      (tagWorkPastToTagAndNegativeTimeHistory
        (markedRenewalTagWorkPastFactors z)).2 =
      (predecessorGap z,
        measurablePredecessorCausalResponseOnSource serviceRate z) := by
  rfl

/-- Pushing negative-time history through the predecessor gap/response
reconstruction gives the already-proved direct predecessor pair law. -/
private theorem map_negativeTimeHistoryToPredecessorGapAndMeasurableResponse_of_rate_pos
    {rate : Real} (serviceRate : Real) (hrate : 0 < rate) :
    Measure.map (negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate)
      ((exponentialInterarrivalMeasure (1 : ℝ)).prod
        (exponentialInterarrivalMeasure rate)) =
      (expMeasure rate).prod
        (Measure.map (measurablePredecessorCausalResponse serviceRate)
          (predecessorCausalInputMeasure rate)) := by
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
  let P : Measure NegativeTimeMarkedHistory :=
    (exponentialInterarrivalMeasure (1 : ℝ)).prod
      (exponentialInterarrivalMeasure rate)
  let F : TwoSidedMarkedRenewalSample → ℝ × NegativeTimeMarkedHistory :=
    fun z => tagWorkPastToTagAndNegativeTimeHistory
      (markedRenewalTagWorkPastFactors z)
  let q : NegativeTimeMarkedHistory → ℝ × ℝ :=
    negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate
  have hF : Measurable F :=
    measurable_tagWorkPastToTagAndNegativeTimeHistory.comp
      measurable_markedRenewalTagWorkPastFactors
  have hq : Measurable q :=
    measurable_negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate
  have hfactor : Measure.map F (twoSidedMarkedRenewalMeasure rate) =
      (expMeasure (1 : ℝ)).prod P := by
    simpa [F, P] using
      map_tagWorkAndNegativeTimeHistory_twoSidedMarkedRenewalMeasure hrate
  have hpairfun : ((q ∘ Prod.snd) ∘ F) =
      fun z : TwoSidedMarkedRenewalSample =>
        (predecessorGap z,
          measurablePredecessorCausalResponseOnSource serviceRate z) := by
    funext z
    simpa [q, F] using
      negativeTimeHistoryToPredecessorGapAndMeasurableResponse_apply serviceRate z
  calc
    Measure.map (negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate)
        ((exponentialInterarrivalMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure rate)) =
        Measure.map q (Measure.map Prod.snd ((expMeasure (1 : ℝ)).prod P)) := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = Measure.map (q ∘ Prod.snd) ((expMeasure (1 : ℝ)).prod P) := by
          rw [Measure.map_map hq measurable_snd]
    _ = Measure.map (q ∘ Prod.snd)
        (Measure.map F (twoSidedMarkedRenewalMeasure rate)) := by
          rw [hfactor]
    _ = Measure.map ((q ∘ Prod.snd) ∘ F)
        (twoSidedMarkedRenewalMeasure rate) := by
          rw [Measure.map_map (hq.comp measurable_snd) hF]
    _ = Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        (predecessorGap z,
          measurablePredecessorCausalResponseOnSource serviceRate z))
        (twoSidedMarkedRenewalMeasure rate) := by rw [hpairfun]
    _ = (expMeasure rate).prod
        (Measure.map (measurablePredecessorCausalResponse serviceRate)
          (predecessorCausalInputMeasure rate)) :=
      (predecessorGapAndMeasurableCausalResponseOnSource_hasLaw
        (serviceRate := serviceRate) hrate).map_eq

/-- Exact source-native joint product law for the current tag work and the
predecessor gap/response pair.  The second factor is generated entirely
from negative-time input, so this is stronger than separate pairwise
independence assertions. -/
theorem tagWorkAndPredecessorGapAndMeasurableCausalResponseOnSource_hasLaw
    {rate : Real} (serviceRate : Real) (hrate : 0 < rate) :
    HasLaw (fun z : TwoSidedMarkedRenewalSample =>
      (tagWork z,
        (predecessorGap z,
          measurablePredecessorCausalResponseOnSource serviceRate z)))
      ((expMeasure (1 : ℝ)).prod
        ((expMeasure rate).prod
          (Measure.map (measurablePredecessorCausalResponse serviceRate)
            (predecessorCausalInputMeasure rate))))
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
  let P : Measure NegativeTimeMarkedHistory :=
    (exponentialInterarrivalMeasure (1 : ℝ)).prod
      (exponentialInterarrivalMeasure rate)
  let F : TwoSidedMarkedRenewalSample → ℝ × NegativeTimeMarkedHistory :=
    fun z => tagWorkPastToTagAndNegativeTimeHistory
      (markedRenewalTagWorkPastFactors z)
  let q : NegativeTimeMarkedHistory → ℝ × ℝ :=
    negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate
  have hF : Measurable F :=
    measurable_tagWorkPastToTagAndNegativeTimeHistory.comp
      measurable_markedRenewalTagWorkPastFactors
  have hq : Measurable q :=
    measurable_negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate
  have hfactor : Measure.map F (twoSidedMarkedRenewalMeasure rate) =
      (expMeasure (1 : ℝ)).prod P := by
    simpa [F, P] using
      map_tagWorkAndNegativeTimeHistory_twoSidedMarkedRenewalMeasure hrate
  have htriplefun : ((Prod.map id q) ∘ F) =
      fun z : TwoSidedMarkedRenewalSample =>
        (tagWork z,
          (predecessorGap z,
            measurablePredecessorCausalResponseOnSource serviceRate z)) := by
    funext z
    simp only [Function.comp_apply]
    change (twoSidedGap 0 z.2,
      negativeTimeHistoryToPredecessorGapAndMeasurableResponse serviceRate
        (tagWorkPastToTagAndNegativeTimeHistory
          (markedRenewalTagWorkPastFactors z)).2) = _
    rw [negativeTimeHistoryToPredecessorGapAndMeasurableResponse_apply]
    rfl
  refine ⟨(measurable_tagWork.prodMk
    (measurable_predecessorGap.prodMk
      (measurable_measurablePredecessorCausalResponseOnSource serviceRate))).aemeasurable,
    ?_⟩
  calc
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        (tagWork z,
          (predecessorGap z,
            measurablePredecessorCausalResponseOnSource serviceRate z)))
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map (Prod.map id q)
          (Measure.map F (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map (measurable_id.prodMap hq) hF]
          exact congrArg (fun f => Measure.map f (twoSidedMarkedRenewalMeasure rate)) htriplefun
    _ = Measure.map (Prod.map id q) ((expMeasure (1 : ℝ)).prod P) := by
          rw [hfactor]
    _ = (expMeasure (1 : ℝ)).prod (Measure.map q P) := by
          rw [← Measure.map_prod_map _ _ measurable_id hq, Measure.map_id]
    _ = (expMeasure (1 : ℝ)).prod
        ((expMeasure rate).prod
          (Measure.map (measurablePredecessorCausalResponse serviceRate)
            (predecessorCausalInputMeasure rate))) := by
          rw [show Measure.map q P =
            (expMeasure rate).prod
              (Measure.map (measurablePredecessorCausalResponse serviceRate)
                (predecessorCausalInputMeasure rate)) by
              simpa [q, P] using
                map_negativeTimeHistoryToPredecessorGapAndMeasurableResponse_of_rate_pos
                  serviceRate hrate]

/-- The current tag work is independent of the complete predecessor
gap/response pair on the literal source carrier. -/
theorem indepFun_tagWork_predecessorGapAndMeasurableCausalResponseOnSource
    {rate : Real} (serviceRate : Real) (hrate : 0 < rate) :
    tagWork ⟂ᵢ[twoSidedMarkedRenewalMeasure rate]
      (fun z : TwoSidedMarkedRenewalSample =>
        (predecessorGap z,
          measurablePredecessorCausalResponseOnSource serviceRate z)) := by
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
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_tagWork.aemeasurable
    (measurable_predecessorGap.prodMk
      (measurable_measurablePredecessorCausalResponseOnSource serviceRate)).aemeasurable).2
  rw [(tagWorkAndPredecessorGapAndMeasurableCausalResponseOnSource_hasLaw
      (serviceRate := serviceRate) hrate).map_eq,
    (show HasLaw tagWork (expMeasure (1 : ℝ))
      (twoSidedMarkedRenewalMeasure rate) by
        simpa [tagWork] using twoSidedMarkedRenewal_tagWork_hasLaw hrate).map_eq,
    (predecessorGapAndMeasurableCausalResponseOnSource_hasLaw
      (serviceRate := serviceRate) hrate).map_eq]

/-- Under strict stability, the measurable predecessor pair is the selected
predecessor response after moving the tag one literal arrival backwards. -/
theorem ae_predecessorGapAndMeasurableCausalResponseOnSource_eq_indexShift_negOne_response
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    (fun z : TwoSidedMarkedRenewalSample =>
      (predecessorGap z,
        measurablePredecessorCausalResponseOnSource serviceRate z)) =ᵐ[
          twoSidedMarkedRenewalMeasure rate]
      fun z => (predecessorGap z,
        response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z)) := by
  filter_upwards [
    ae_measurableCausalResponseOnSource_eq_indexShift_negOne_response_of_rate_lt
      hrate hstable] with z hz
  exact Prod.ext rfl hz

/-- The exact measured joint product law transfers to the selected direct
response recurrence on the stable source event. -/
theorem tagWorkAndPredecessorGapAndIndexShiftResponse_hasLaw_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    HasLaw (fun z : TwoSidedMarkedRenewalSample =>
      (tagWork z,
        (predecessorGap z,
          response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z))))
      ((expMeasure (1 : ℝ)).prod
        ((expMeasure rate).prod
          (Measure.map (measurablePredecessorCausalResponse serviceRate)
            (predecessorCausalInputMeasure rate))))
      (twoSidedMarkedRenewalMeasure rate) := by
  apply (tagWorkAndPredecessorGapAndMeasurableCausalResponseOnSource_hasLaw
    (serviceRate := serviceRate) hrate).congr
  filter_upwards [
    ae_predecessorGapAndMeasurableCausalResponseOnSource_eq_indexShift_negOne_response
      hrate hstable] with z hz
  exact Prod.ext rfl hz.symm

/-- In the stable direct source model, the current tag work is independent
of the joint pair consisting of the physical predecessor gap and the selected
predecessor response. -/
theorem indepFun_tagWork_predecessorGapAndIndexShiftResponse_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    tagWork ⟂ᵢ[twoSidedMarkedRenewalMeasure rate]
      (fun z : TwoSidedMarkedRenewalSample =>
        (predecessorGap z,
          response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z))) := by
  refine (indepFun_tagWork_predecessorGapAndMeasurableCausalResponseOnSource
    (serviceRate := serviceRate) hrate).congr
      (Filter.Eventually.of_forall fun _ => rfl) ?_
  exact ae_predecessorGapAndMeasurableCausalResponseOnSource_eq_indexShift_negOne_response
    hrate hstable

/-- Under strict direct stability, the causal-factor response law is exactly
the selected direct response law.  The equality is proved through the
literal shifted source, not by identifying the two functions pointwise off
the coalescence event. -/
theorem measurablePredecessorCausalResponse_measure_eq_response_measure_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    Measure.map (measurablePredecessorCausalResponse serviceRate)
      (predecessorCausalInputMeasure rate) =
      Measure.map (response serviceRate) (twoSidedMarkedRenewalMeasure rate) := by
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
  calc
    Measure.map (measurablePredecessorCausalResponse serviceRate)
        (predecessorCausalInputMeasure rate) =
        Measure.map (measurablePredecessorCausalResponseOnSource serviceRate)
          (twoSidedMarkedRenewalMeasure rate) :=
      (measurablePredecessorCausalResponseOnSource_hasLaw
        serviceRate hrate).map_eq.symm
    _ = Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z))
        (twoSidedMarkedRenewalMeasure rate) := by
          apply Measure.map_congr
          exact ae_measurableCausalResponseOnSource_eq_indexShift_negOne_response_of_rate_lt
            hrate hstable
    _ = Measure.map (response serviceRate)
        (twoSidedMarkedRenewalMeasure rate) :=
      (response_indexShift_negOne_hasLaw_of_rate_lt hrate hstable).map_eq

/-- The stable joint innovation law with the predecessor response expressed
using the direct response marginal itself. -/
theorem tagWorkAndPredecessorGapAndIndexShiftResponse_hasLaw_with_responseLaw_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    HasLaw (fun z : TwoSidedMarkedRenewalSample =>
      (tagWork z,
        (predecessorGap z,
          response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z))))
      ((expMeasure (1 : ℝ)).prod
        ((expMeasure rate).prod
          (Measure.map (response serviceRate)
            (twoSidedMarkedRenewalMeasure rate))))
      (twoSidedMarkedRenewalMeasure rate) := by
  rw [← measurablePredecessorCausalResponse_measure_eq_response_measure_of_rate_lt
    hrate hstable]
  exact tagWorkAndPredecessorGapAndIndexShiftResponse_hasLaw_of_rate_lt
    hrate hstable

/-- The direct stable response law is a stationary fixed point of the exact
literal response update driven by an independent unit-exponential current
work mark and rate-`rate` physical gap.  This is the complete source-native
probabilistic reduction; solving this fixed point's tail remains a separate
analytic obligation. -/
theorem response_hasLaw_responseUpdateFixedPoint_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    HasLaw (response serviceRate)
      (Measure.map (responseUpdate serviceRate)
        ((expMeasure (1 : ℝ)).prod
          ((expMeasure rate).prod
            (Measure.map (response serviceRate)
              (twoSidedMarkedRenewalMeasure rate)))))
      (twoSidedMarkedRenewalMeasure rate) := by
  let L : Measure (ℝ × (ℝ × ℝ)) :=
    (expMeasure (1 : ℝ)).prod
      ((expMeasure rate).prod
        (Measure.map (response serviceRate)
          (twoSidedMarkedRenewalMeasure rate)))
  let X : TwoSidedMarkedRenewalSample → ℝ × (ℝ × ℝ) :=
    fun z => (tagWork z,
      (predecessorGap z,
        response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z)))
  have hX : HasLaw X L (twoSidedMarkedRenewalMeasure rate) := by
    simpa [X, L] using
      tagWorkAndPredecessorGapAndIndexShiftResponse_hasLaw_with_responseLaw_of_rate_lt
        hrate hstable
  have hUpdate : HasLaw (responseUpdate serviceRate)
      (Measure.map (responseUpdate serviceRate) L) L :=
    ⟨(measurable_responseUpdate serviceRate).aemeasurable, rfl⟩
  apply hUpdate.comp hX |>.congr
  filter_upwards [
    ae_response_eq_indexShift_negOne_response_update_of_rate_lt hrate hstable] with z hz
  simpa [X, responseUpdate, Function.comp_apply] using hz

end DirectMarkedRenewalComparator

end

end LG24ServiceLevelAgreements

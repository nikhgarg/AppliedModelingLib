import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorFiniteReplayLaw
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorResponseInnovations
import Mathlib.Tactic

/-!
# Response law from a causal negative-history workload

The direct marked-renewal source separates the selected job's own work mark
from the complete negative-time work/gap history.  This module records the
measure-level consequence needed after a causal workload construction has
identified the law of a measurable functional of that history.  It does not
assume a stationary workload law: that law remains an explicit input to the
two theorems below and is discharged by the remote-past uniqueness proof.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators ENNReal MeasureTheory

noncomputable section

namespace DirectMarkedRenewalComparator

/-- Attach the literal selected job's own work mark to a workload functional
of the complete negative-time history.  The workload is intentionally a
function of the history only, so the source factorization below can establish
the required independence rather than taking it as a queueing assumption. -/
def responseFromNegativeHistory (serviceRate : ℝ)
    (preWorkload : NegativeTimeHistory → ℝ)
    (z : TwoSidedMarkedRenewalSample) : ℝ :=
  preWorkload (directNegativeTimeHistory z) + tagWork z / serviceRate

theorem measurable_responseFromNegativeHistory
    (serviceRate : ℝ) (preWorkload : NegativeTimeHistory → ℝ)
    (hpreWorkload : Measurable preWorkload) :
    Measurable (responseFromNegativeHistory serviceRate preWorkload) := by
  unfold responseFromNegativeHistory
  exact (hpreWorkload.comp measurable_directNegativeTimeHistory).add
    (measurable_tagWork.div measurable_const)

/-- A measurable functional of the complete negative-time history is jointly
distributed with the literal tag work as the product of its history law and a
fresh unit-exponential mark.  This is a source-factor statement: neither a
stationary state nor an iid queue recursion is introduced here. -/
theorem map_negativeHistoryFunctional_and_tagWork
    {arrivalRate : ℝ} (harrival : 0 < arrivalRate)
    (preWorkload : NegativeTimeHistory → ℝ)
    (hpreWorkload : Measurable preWorkload) :
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
      (preWorkload (directNegativeTimeHistory z), tagWork z))
      (twoSidedMarkedRenewalMeasure arrivalRate) =
      (Measure.map preWorkload (negativeTimeHistoryMeasure arrivalRate)).prod
        (expMeasure (1 : ℝ)) := by
  let E : Measure ℝ := expMeasure (1 : ℝ)
  let H : Measure NegativeTimeHistory := negativeTimeHistoryMeasure arrivalRate
  let S : Measure TwoSidedMarkedRenewalSample :=
    twoSidedMarkedRenewalMeasure arrivalRate
  let sourceFactor : TwoSidedMarkedRenewalSample → ℝ × NegativeTimeHistory :=
    fun z => (tagWork z, directNegativeTimeHistory z)
  let reorder : ℝ × NegativeTimeHistory → ℝ × ℝ :=
    fun x => (preWorkload x.2, x.1)
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    exact isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_negativeTimeHistoryMeasure harrival
  have hsourceFactor : Measurable sourceFactor := by
    exact measurable_tagWork.prodMk measurable_directNegativeTimeHistory
  have hfactor : Measure.map sourceFactor S = E.prod H := by
    simpa [sourceFactor, S, E, H, tagWork, directNegativeTimeHistory,
      tagWorkPastToTagAndNegativeTimeHistory,
      markedRenewalTagWorkPastFactors, negativeTimeHistoryMeasure] using
      (map_tagWorkAndNegativeTimeHistory_twoSidedMarkedRenewalMeasure harrival)
  have hReorder : Measurable reorder := by
    exact (hpreWorkload.comp measurable_snd).prodMk measurable_fst
  have hReorder_eq : reorder = Prod.swap ∘ Prod.map id preWorkload := by
    funext x
    rfl
  calc
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        (preWorkload (directNegativeTimeHistory z), tagWork z)) S =
        Measure.map reorder (Measure.map sourceFactor S) := by
          change Measure.map (reorder ∘ sourceFactor) S = _
          rw [← Measure.map_map hReorder hsourceFactor]
    _ = Measure.map reorder (E.prod H) := by rw [hfactor]
    _ = Measure.map Prod.swap
        (Measure.map (Prod.map id preWorkload) (E.prod H)) := by
          rw [hReorder_eq]
          rw [← Measure.map_map measurable_swap
            (measurable_id.prodMap hpreWorkload)]
    _ = Measure.map Prod.swap
        ((Measure.map id E).prod (Measure.map preWorkload H)) := by
          rw [← Measure.map_prod_map E H measurable_id hpreWorkload]
    _ = (Measure.map preWorkload H).prod E := by
          rw [Measure.map_id, Measure.prod_swap]

/-- If a causal negative-history workload has the M/M/1 candidate pre-work
law, appending the literal independent selected work mark has the exact
exponential response law.  The theorem is deliberately about the concrete
source function defined above; a separate pathwise theorem must identify that
function with the canonical direct response. -/
theorem map_responseFromNegativeHistory_eq_expMeasure_slack_of_preWorkloadLaw
    {arrivalRate serviceRate : ℝ} (harrival : 0 < arrivalRate)
    (hstable : arrivalRate < serviceRate)
    (preWorkload : NegativeTimeHistory → ℝ)
    (hpreWorkload : Measurable preWorkload)
    (hpreLaw : Measure.map preWorkload (negativeTimeHistoryMeasure arrivalRate) =
      candidatePreWorkloadLaw arrivalRate serviceRate) :
    Measure.map (responseFromNegativeHistory serviceRate preWorkload)
      (twoSidedMarkedRenewalMeasure arrivalRate) =
      expMeasure (comparatorSlackRate arrivalRate serviceRate) := by
  let pair : TwoSidedMarkedRenewalSample → ℝ × ℝ :=
    fun z => (preWorkload (directNegativeTimeHistory z), tagWork z)
  let addServiceTime : ℝ × ℝ → ℝ :=
    fun x => x.1 + x.2 / serviceRate
  have hpair : Measure.map pair (twoSidedMarkedRenewalMeasure arrivalRate) =
      (candidatePreWorkloadLaw arrivalRate serviceRate).prod (expMeasure (1 : ℝ)) := by
    rw [show pair = fun z : TwoSidedMarkedRenewalSample =>
      (preWorkload (directNegativeTimeHistory z), tagWork z) by rfl,
      map_negativeHistoryFunctional_and_tagWork harrival preWorkload hpreWorkload,
      hpreLaw]
  have haddServiceTime : Measurable addServiceTime := by
    exact measurable_fst.add (measurable_snd.div measurable_const)
  have hpairMeas : Measurable pair := by
    exact (hpreWorkload.comp measurable_directNegativeTimeHistory).prodMk measurable_tagWork
  calc
    Measure.map (responseFromNegativeHistory serviceRate preWorkload)
        (twoSidedMarkedRenewalMeasure arrivalRate) =
        Measure.map addServiceTime
          (Measure.map pair (twoSidedMarkedRenewalMeasure arrivalRate)) := by
          change Measure.map (addServiceTime ∘ pair)
            (twoSidedMarkedRenewalMeasure arrivalRate) = _
          rw [← Measure.map_map haddServiceTime hpairMeas]
    _ = Measure.map addServiceTime
        ((candidatePreWorkloadLaw arrivalRate serviceRate).prod
          (expMeasure (1 : ℝ))) := by rw [hpair]
    _ = expMeasure (comparatorSlackRate arrivalRate serviceRate) := by
      simpa [addServiceTime] using
        map_candidatePreWorkload_add_unitWork_div_eq_expMeasure_slack harrival hstable

/-- The exact strict tail of the response built from a candidate-law causal
negative-history workload.  The threshold is nonnegative because the source
paper's response guarantee is a positive-delay statement; no unmentioned
atom convention is needed for this strict-tail identity. -/
theorem responseFromNegativeHistory_strictTail_eq_exp_of_preWorkloadLaw
    {arrivalRate serviceRate : ℝ} (harrival : 0 < arrivalRate)
    (hstable : arrivalRate < serviceRate)
    (preWorkload : NegativeTimeHistory → ℝ)
    (hpreWorkload : Measurable preWorkload)
    (hpreLaw : Measure.map preWorkload (negativeTimeHistoryMeasure arrivalRate) =
      candidatePreWorkloadLaw arrivalRate serviceRate)
    (delay : ℝ) (hdelay : 0 ≤ delay) :
    (twoSidedMarkedRenewalMeasure arrivalRate).real
      {z | delay < responseFromNegativeHistory serviceRate preWorkload z} =
      Real.exp (-(comparatorSlackRate arrivalRate serviceRate * delay)) := by
  let response := responseFromNegativeHistory serviceRate preWorkload
  let S : Measure TwoSidedMarkedRenewalSample :=
    twoSidedMarkedRenewalMeasure arrivalRate
  let slack := comparatorSlackRate arrivalRate serviceRate
  have hslack : 0 < slack := by
    dsimp [slack, comparatorSlackRate]
    linarith
  have hresponseMeas : Measurable response := by
    exact measurable_responseFromNegativeHistory serviceRate preWorkload hpreWorkload
  have hresponseLaw : Measure.map response S = expMeasure slack := by
    simpa [response, S, slack] using
      map_responseFromNegativeHistory_eq_expMeasure_slack_of_preWorkloadLaw
        harrival hstable preWorkload hpreWorkload hpreLaw
  let model : AppliedModelingLib.Probability.Exponential.Model := ⟨slack, hslack⟩
  calc
    S.real {z | delay < response z} =
        (Measure.map response S).real (Set.Ioi delay) := by
          change (S (response ⁻¹' Set.Ioi delay)).toReal = _
          rw [← Measure.map_apply hresponseMeas measurableSet_Ioi]
          rfl
    _ = (expMeasure slack).real (Set.Ioi delay) := by rw [hresponseLaw]
    _ = Real.exp (-(slack * delay)) := by
      simpa [model, AppliedModelingLib.Probability.Exponential.Model.measure] using
        model.measure_Ioi_toReal hdelay

/-- The canonical direct response obtained from the completed causal
negative-history workload.  This remains a literal function of the direct
two-sided source: the selected mark is not folded into the past history. -/
noncomputable def negativeTimeCausalResponse (serviceRate : ℝ)
    (z : TwoSidedMarkedRenewalSample) : ℝ :=
  responseFromNegativeHistory serviceRate
    (negativeTimeCausalWorkload serviceRate) z

/-- The causal direct response has the exact stable M/M/1 exponential law.
This is a pushforward statement for the concrete negative-history
construction, not an assumption about a stationary queue state. -/
theorem map_negativeTimeCausalResponse_eq_expMeasure_slack
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Measure.map (negativeTimeCausalResponse serviceRate)
      (twoSidedMarkedRenewalMeasure arrivalRate) =
      expMeasure (comparatorSlackRate arrivalRate serviceRate) := by
  unfold negativeTimeCausalResponse
  exact map_responseFromNegativeHistory_eq_expMeasure_slack_of_preWorkloadLaw
    harrival hstable (negativeTimeCausalWorkload serviceRate)
    (measurable_negativeTimeCausalWorkload serviceRate)
    (map_negativeTimeCausalWorkload_eq_candidatePreWorkloadLaw harrival hstable)

/-- Exact strict positive-delay tail of the concrete causal direct response.
The named nonnegative threshold retains the source paper's response-time
domain explicitly. -/
theorem negativeTimeCausalResponse_strictTail_eq_exp
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (delay : ℝ) (hdelay : 0 ≤ delay) :
    (twoSidedMarkedRenewalMeasure arrivalRate).real
      {z | delay < negativeTimeCausalResponse serviceRate z} =
      Real.exp (-(comparatorSlackRate arrivalRate serviceRate * delay)) := by
  unfold negativeTimeCausalResponse
  exact responseFromNegativeHistory_strictTail_eq_exp_of_preWorkloadLaw
    harrival hstable (negativeTimeCausalWorkload serviceRate)
    (measurable_negativeTimeCausalWorkload serviceRate)
    (map_negativeTimeCausalWorkload_eq_candidatePreWorkloadLaw harrival hstable)
    delay hdelay

/-- The newly constructed causal response agrees almost surely with the
globally measurable version of the pre-existing literal finite-replay
response.  The equality uses only the proved positive-rate scaling of the
workload recursion and the source's strict-stability coalescence event. -/
theorem ae_negativeTimeCausalResponse_eq_measurableResponse_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    negativeTimeCausalResponse serviceRate =ᵐ[
      twoSidedMarkedRenewalMeasure arrivalRate]
      measurableResponse serviceRate := by
  have hservice : 0 < serviceRate := lt_trans harrival hstable
  filter_upwards [
    ae_directTimeCausalWorkload_eq_measurablePreTagWorkload_div_of_rate_lt
      harrival hstable] with z hwork
  unfold negativeTimeCausalResponse responseFromNegativeHistory
  change directTimeCausalWorkload serviceRate z + tagWork z / serviceRate =
    (measurablePreTagWorkload serviceRate z + tagWork z) / serviceRate
  rw [hwork]
  field_simp [ne_of_gt hservice]

/-- The selected direct response from the original finite-replay surface
agrees almost surely with the source-native causal construction. -/
theorem ae_response_eq_negativeTimeCausalResponse_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    response serviceRate =ᵐ[twoSidedMarkedRenewalMeasure arrivalRate]
      negativeTimeCausalResponse serviceRate := by
  filter_upwards [
    ae_response_eq_measurableResponse_of_rate_lt harrival hstable,
    ae_negativeTimeCausalResponse_eq_measurableResponse_of_rate_lt
      harrival hstable] with z hresponse hcausal
  exact hresponse.trans hcausal.symm

/-- Exact strict response tail for the existing direct finite-replay
comparator.  This closes the analytic M/M/1 law through a causal construction
of the literal source path, rather than an asserted stationary queue law. -/
theorem response_strictTail_eq_exp_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (delay : ℝ) (hdelay : 0 ≤ delay) :
    (twoSidedMarkedRenewalMeasure arrivalRate).real
      {z | delay < response serviceRate z} =
      Real.exp (-(comparatorSlackRate arrivalRate serviceRate * delay)) := by
  have hresponse : response serviceRate =ᵐ[
      twoSidedMarkedRenewalMeasure arrivalRate]
      negativeTimeCausalResponse serviceRate :=
    ae_response_eq_negativeTimeCausalResponse_of_rate_lt harrival hstable
  have hevent : {z | delay < response serviceRate z} =ᵐ[
      twoSidedMarkedRenewalMeasure arrivalRate]
      {z | delay < negativeTimeCausalResponse serviceRate z} := by
    filter_upwards [hresponse] with z hz
    exact congrArg (fun x : ℝ => delay < x) hz
  calc
    (twoSidedMarkedRenewalMeasure arrivalRate).real
        {z | delay < response serviceRate z} =
        (twoSidedMarkedRenewalMeasure arrivalRate).real
          {z | delay < negativeTimeCausalResponse serviceRate z} := by
          exact congrArg ENNReal.toReal (MeasureTheory.measure_congr hevent)
    _ = Real.exp (-(comparatorSlackRate arrivalRate serviceRate * delay)) :=
      negativeTimeCausalResponse_strictTail_eq_exp harrival hstable delay hdelay

end DirectMarkedRenewalComparator

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Exact strict tail for the literal admitted target-only comparator under
the actual SLA target-Palm source.  The result transports the direct causal
law through the already proved source-law equivalence; it introduces no
independent stationary-comparator assumption. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_exp_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate delay : ℝ) (hstable : M.admittedRate target < serviceRate)
    (hdelay : 0 ≤ delay) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < stationaryAdmittedTargetPalmComparatorResponse target serviceRate z} =
      Real.exp (-(DirectMarkedRenewalComparator.comparatorSlackRate
        (M.admittedRate target) serviceRate * delay)) := by
  calc
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
        {z | delay < stationaryAdmittedTargetPalmComparatorResponse target serviceRate z} =
        (twoSidedMarkedRenewalMeasure (M.admittedRate target)).real
          {x | delay < DirectMarkedRenewalComparator.response serviceRate x} :=
      M.stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_directMarkedRenewal_of_admittedRate_lt
        target serviceRate delay hstable
    _ = Real.exp (-(DirectMarkedRenewalComparator.comparatorSlackRate
        (M.admittedRate target) serviceRate * delay)) :=
      DirectMarkedRenewalComparator.response_strictTail_eq_exp_of_rate_lt
        (M.admittedRate_pos target) hstable delay hdelay

/-- The source display's target-local GPS slack supplies the strict
input-stability premise for the exact target comparator tail. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_exp_of_gpsParameters
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay : ℝ)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 ≤ delay) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < stationaryAdmittedTargetPalmComparatorResponse target
        (G.capacity * G.weight target) z} =
      Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)) := by
  have htail := M.stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_exp_of_admittedRate_lt
    target (G.capacity * G.weight target) delay
    hstable hdelay
  simpa [DirectMarkedRenewalComparator.comparatorSlackRate] using htail

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements

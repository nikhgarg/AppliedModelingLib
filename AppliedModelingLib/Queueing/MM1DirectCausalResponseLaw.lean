import AppliedModelingLib.Queueing.MM1DirectCausalWorkloadLaw
import AppliedModelingLib.Queueing.StationaryPerformance

/-!
# Direct M/M/1 causal response law

This module derives the response-time law of a constant-rate FCFS queue from
its literal two-sided marked-renewal input.  The pre-arrival causal workload is
kept separate from the selected job's independent service mark.
-/

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators ENNReal MeasureTheory

noncomputable section

namespace MM1DirectCausal

/-- Attach a selected job's service mark to a workload determined entirely by
the negative-time history. -/
def responseFromNegativeTimeHistory (serviceRate : ℝ)
    (preWorkload : NegativeTimeHistory → ℝ)
    (z : TwoSidedMarkedRenewalSample) : ℝ :=
  preWorkload (directNegativeTimeHistory z) + tagWork z / serviceRate

theorem measurable_responseFromNegativeTimeHistory
    (serviceRate : ℝ) (preWorkload : NegativeTimeHistory → ℝ)
    (hpreWorkload : Measurable preWorkload) :
    Measurable (responseFromNegativeTimeHistory serviceRate preWorkload) := by
  unfold responseFromNegativeTimeHistory
  exact (hpreWorkload.comp measurable_directNegativeTimeHistory).add
    (measurable_tagWork.div measurable_const)

/-- Separate the current service-work mark from the complete negative-time
arrival/work history carried by the marked-renewal factorization. -/
def tagWorkPastToTagAndNegativeTimeHistory
    (x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :
    ℝ × NegativeTimeHistory :=
  (x.1.1, (x.1.2, x.2))

theorem measurable_tagWorkPastToTagAndNegativeTimeHistory :
    Measurable tagWorkPastToTagAndNegativeTimeHistory := by
  unfold tagWorkPastToTagAndNegativeTimeHistory
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The selected work mark and the complete negative-time history have their
independent product law on the literal marked-renewal source. -/
theorem map_tagWorkAndNegativeTimeHistory_twoSidedMarkedRenewalMeasure
    {arrivalRate : ℝ} (harrival : 0 < arrivalRate) :
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
      tagWorkPastToTagAndNegativeTimeHistory (markedRenewalTagWorkPastFactors z))
      (twoSidedMarkedRenewalMeasure arrivalRate) =
      (expMeasure (1 : ℝ)).prod
        ((exponentialInterarrivalMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure arrivalRate)) := by
  letI : IsProbabilityMeasure (expMeasure arrivalRate) :=
    isProbabilityMeasure_expMeasure harrival
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure arrivalRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrival
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  calc
    Measure.map (fun z : TwoSidedMarkedRenewalSample =>
        tagWorkPastToTagAndNegativeTimeHistory (markedRenewalTagWorkPastFactors z))
        (twoSidedMarkedRenewalMeasure arrivalRate) =
        Measure.map tagWorkPastToTagAndNegativeTimeHistory
          (Measure.map markedRenewalTagWorkPastFactors
            (twoSidedMarkedRenewalMeasure arrivalRate)) := by
          symm
          rw [Measure.map_map measurable_tagWorkPastToTagAndNegativeTimeHistory
            measurable_markedRenewalTagWorkPastFactors]
          rfl
    _ = Measure.map tagWorkPastToTagAndNegativeTimeHistory
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure arrivalRate)) := by
          rw [map_markedRenewalTagWorkPastFactors_twoSidedMarkedRenewalMeasure harrival]
    _ = (expMeasure (1 : ℝ)).prod
        ((exponentialInterarrivalMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure arrivalRate)) := by
          change Measure.map MeasurableEquiv.prodAssoc
            (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
              (exponentialInterarrivalMeasure arrivalRate)) = _
          rw [Measure.prodAssoc_prod]

/-- A negative-history functional and the selected job's work mark have the
product law induced by the marked-renewal input. -/
theorem map_negativeTimeHistoryFunctional_and_tagWork
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

/-- If a negative-history workload has the stationary M/M/1 pre-arrival law,
then appending the independent selected work mark has the stable response law. -/
theorem map_responseFromNegativeTimeHistory_eq_expMeasure_slack_of_preWorkloadLaw
    {arrivalRate serviceRate : ℝ} (harrival : 0 < arrivalRate)
    (hstable : arrivalRate < serviceRate)
    (preWorkload : NegativeTimeHistory → ℝ)
    (hpreWorkload : Measurable preWorkload)
    (hpreLaw : Measure.map preWorkload (negativeTimeHistoryMeasure arrivalRate) =
      mm1PreArrivalWorkloadLaw arrivalRate serviceRate) :
    Measure.map (responseFromNegativeTimeHistory serviceRate preWorkload)
      (twoSidedMarkedRenewalMeasure arrivalRate) =
      expMeasure (mm1SlackRate arrivalRate serviceRate) := by
  let pair : TwoSidedMarkedRenewalSample → ℝ × ℝ :=
    fun z => (preWorkload (directNegativeTimeHistory z), tagWork z)
  let addServiceTime : ℝ × ℝ → ℝ :=
    fun x => x.1 + x.2 / serviceRate
  have hpair : Measure.map pair (twoSidedMarkedRenewalMeasure arrivalRate) =
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
        (expMeasure (1 : ℝ)) := by
    rw [show pair = fun z : TwoSidedMarkedRenewalSample =>
      (preWorkload (directNegativeTimeHistory z), tagWork z) by rfl,
      map_negativeTimeHistoryFunctional_and_tagWork harrival preWorkload hpreWorkload,
      hpreLaw]
  have haddServiceTime : Measurable addServiceTime := by
    exact measurable_fst.add (measurable_snd.div measurable_const)
  have hpairMeas : Measurable pair := by
    exact (hpreWorkload.comp measurable_directNegativeTimeHistory).prodMk measurable_tagWork
  calc
    Measure.map (responseFromNegativeTimeHistory serviceRate preWorkload)
        (twoSidedMarkedRenewalMeasure arrivalRate) =
        Measure.map addServiceTime
          (Measure.map pair (twoSidedMarkedRenewalMeasure arrivalRate)) := by
          change Measure.map (addServiceTime ∘ pair)
            (twoSidedMarkedRenewalMeasure arrivalRate) = _
          rw [← Measure.map_map haddServiceTime hpairMeas]
    _ = Measure.map addServiceTime
        ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
          (expMeasure (1 : ℝ))) := by rw [hpair]
    _ = expMeasure (mm1SlackRate arrivalRate serviceRate) := by
      simpa [addServiceTime] using
        map_mm1PreArrivalWorkload_add_unitWork_div_eq_expMeasure_slack harrival hstable

/-- The direct causal response obtained from the negative-time workload and
the selected job's work mark. -/
noncomputable def negativeTimeCausalResponse (serviceRate : ℝ)
    (z : TwoSidedMarkedRenewalSample) : ℝ :=
  responseFromNegativeTimeHistory serviceRate
    (negativeTimeCausalWorkload serviceRate) z

theorem measurable_negativeTimeCausalResponse (serviceRate : ℝ) :
    Measurable (negativeTimeCausalResponse serviceRate) := by
  unfold negativeTimeCausalResponse
  exact measurable_responseFromNegativeTimeHistory serviceRate
    (negativeTimeCausalWorkload serviceRate)
    (measurable_negativeTimeCausalWorkload serviceRate)

/-- The causal direct response has the exact stable M/M/1 exponential law. -/
theorem map_negativeTimeCausalResponse_eq_expMeasure_slack
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Measure.map (negativeTimeCausalResponse serviceRate)
      (twoSidedMarkedRenewalMeasure arrivalRate) =
      expMeasure (mm1SlackRate arrivalRate serviceRate) := by
  unfold negativeTimeCausalResponse
  exact map_responseFromNegativeTimeHistory_eq_expMeasure_slack_of_preWorkloadLaw
    harrival hstable (negativeTimeCausalWorkload serviceRate)
    (measurable_negativeTimeCausalWorkload serviceRate)
    (map_negativeTimeCausalWorkload_eq_mm1PreArrivalWorkloadLaw harrival hstable)

/-- The exact strict tail of the direct causal response. -/
theorem negativeTimeCausalResponse_strictTail_eq_exp
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (delay : ℝ) (hdelay : 0 ≤ delay) :
    (twoSidedMarkedRenewalMeasure arrivalRate).real
      {z | delay < negativeTimeCausalResponse serviceRate z} =
      Real.exp (-(mm1SlackRate arrivalRate serviceRate * delay)) := by
  let response := negativeTimeCausalResponse serviceRate
  let S : Measure TwoSidedMarkedRenewalSample :=
    twoSidedMarkedRenewalMeasure arrivalRate
  let slack := mm1SlackRate arrivalRate serviceRate
  have hslack : 0 < slack := by
    dsimp [slack, mm1SlackRate]
    linarith
  have hresponseMeas : Measurable response := by
    exact measurable_negativeTimeCausalResponse serviceRate
  have hresponseLaw : Measure.map response S = expMeasure slack := by
    simpa [response, S, slack] using
      map_negativeTimeCausalResponse_eq_expMeasure_slack harrival hstable
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

/-- The causal response is nonnegative almost surely under stable input. -/
theorem ae_nonnegative_negativeTimeCausalResponse_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure arrivalRate,
      0 ≤ negativeTimeCausalResponse serviceRate z := by
  let response := negativeTimeCausalResponse serviceRate
  let source : Measure TwoSidedMarkedRenewalSample :=
    twoSidedMarkedRenewalMeasure arrivalRate
  let slack := mm1SlackRate arrivalRate serviceRate
  have hslack : 0 < slack := by
    dsimp [slack, mm1SlackRate]
    linarith
  have hmap : Measure.map response source = expMeasure slack := by
    simpa [response, source, slack] using
      map_negativeTimeCausalResponse_eq_expMeasure_slack harrival hstable
  let model : AppliedModelingLib.Probability.Exponential.Model := ⟨slack, hslack⟩
  refine MeasureTheory.ae_of_ae_map (μ := source) (f := response)
    (p := fun value : ℝ => 0 ≤ value)
    (measurable_negativeTimeCausalResponse serviceRate).aemeasurable ?_
  change ∀ᵐ value ∂Measure.map response source, 0 ≤ value
  rw [hmap]
  simpa [model] using model.ae_nonnegative

/-- The negative-time causal response agrees almost surely with the
measurable finite-replay response under strict input stability. -/
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
  unfold negativeTimeCausalResponse responseFromNegativeTimeHistory
  change directTimeCausalWorkload serviceRate z + tagWork z / serviceRate =
    (measurablePreTagWorkload serviceRate z + tagWork z) / serviceRate
  rw [hwork]
  field_simp [ne_of_gt hservice]

/-- The literal direct finite-replay response agrees almost surely with its
causal negative-time construction. -/
theorem ae_response_eq_negativeTimeCausalResponse_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    response serviceRate =ᵐ[twoSidedMarkedRenewalMeasure arrivalRate]
      negativeTimeCausalResponse serviceRate := by
  filter_upwards [
    ae_response_eq_measurableResponse_of_rate_lt harrival hstable,
    ae_negativeTimeCausalResponse_eq_measurableResponse_of_rate_lt harrival hstable]
    with z hresponse hcausal
  exact hresponse.trans hcausal.symm

/-- The literal finite-replay direct response is nonnegative almost surely. -/
theorem ae_nonnegative_response_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure arrivalRate,
      0 ≤ response serviceRate z := by
  filter_upwards [
    ae_response_eq_negativeTimeCausalResponse_of_rate_lt harrival hstable,
    ae_nonnegative_negativeTimeCausalResponse_of_rate_lt harrival hstable]
    with z hresponse hnonnegative
  rw [hresponse]
  exact hnonnegative

/-- The literal direct M/M/1 response has the stable exponential strict tail. -/
theorem response_strictTail_eq_exp_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (delay : ℝ) (hdelay : 0 ≤ delay) :
    (twoSidedMarkedRenewalMeasure arrivalRate).real
      {z | delay < response serviceRate z} =
      Real.exp (-(mm1SlackRate arrivalRate serviceRate * delay)) := by
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
    _ = Real.exp (-(mm1SlackRate arrivalRate serviceRate * delay)) :=
      negativeTimeCausalResponse_strictTail_eq_exp harrival hstable delay hdelay

/-- The literal direct M/M/1 response is integrable under strict stability. -/
theorem integrable_response_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Integrable (response serviceRate) (twoSidedMarkedRenewalMeasure arrivalRate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure arrivalRate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure harrival
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (twoSidedMarkedRenewalMeasure arrivalRate) := by
    unfold twoSidedMarkedRenewalMeasure
    infer_instance
  exact integrable_of_exponential_responseTail
    (twoSidedMarkedRenewalMeasure arrivalRate) (response serviceRate)
    (mm1SlackRate arrivalRate serviceRate)
    (aemeasurable_response_of_rate_lt harrival hstable).aestronglyMeasurable
    (ae_nonnegative_response_of_rate_lt harrival hstable)
    (sub_pos.mpr hstable)
    (fun delay hdelay =>
      response_strictTail_eq_exp_of_rate_lt harrival hstable delay hdelay)

/-- The mean literal direct M/M/1 response is reciprocal spare capacity. -/
theorem integral_response_eq_inv_mm1SlackRate_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    ∫ z, response serviceRate z ∂twoSidedMarkedRenewalMeasure arrivalRate =
      (mm1SlackRate arrivalRate serviceRate)⁻¹ := by
  exact integral_eq_inv_of_exponential_responseTail
    (twoSidedMarkedRenewalMeasure arrivalRate) (response serviceRate)
    (mm1SlackRate arrivalRate serviceRate)
    (integrable_response_of_rate_lt harrival hstable)
    (ae_nonnegative_response_of_rate_lt harrival hstable)
    (sub_pos.mpr hstable)
    (fun delay hdelay =>
      response_strictTail_eq_exp_of_rate_lt harrival hstable delay hdelay)

end MM1DirectCausal

end

end AppliedModelingLib.Queueing

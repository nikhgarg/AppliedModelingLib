import AppliedModelingLib.Queueing.MM1CausalWorkload
import AppliedModelingLib.Queueing.MM1DirectCausalWorkload
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTwoStreamHeadTail
import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalFactors
import AppliedModelingLib.Foundations.Probability.ExponentialRateScaling
import AppliedModelingLib.Foundations.Probability.ExponentialUnequalRateConvolution
import AppliedModelingLib.Queueing.Lindley.RemotePastMonotonicity
import Mathlib.Tactic

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators ENNReal MeasureTheory

noncomputable section

namespace MM1DirectCausal

abbrev NegativeTimeHistory := (ℕ → ℝ) × (ℕ → ℝ)

def negativeTimeHistoryMeasure (arrivalRate : ℝ) : Measure NegativeTimeHistory :=
  (exponentialInterarrivalMeasure (1 : ℝ)).prod
    (exponentialInterarrivalMeasure arrivalRate)

def negativeTimeHistoryTail (h : NegativeTimeHistory) : NegativeTimeHistory :=
  (fun n => h.1 (n + 1), fun n => h.2 (n + 1))

def initialNegativeTimeHistoryHeadTailFactors
    (x : ℝ × NegativeTimeHistory) :
    (ℝ × NegativeTimeHistory) × (ℝ × ℝ) :=
  ((x.1, negativeTimeHistoryTail x.2), (x.2.1 0, x.2.2 0))

theorem measurable_negativeTimeHistoryTail :
    Measurable negativeTimeHistoryTail := by
  exact
    (measurable_pi_iff.2 fun n => measurable_pi_apply (n + 1) |>.comp measurable_fst).prodMk
      (measurable_pi_iff.2 fun n => measurable_pi_apply (n + 1) |>.comp measurable_snd)

theorem measurable_initialNegativeTimeHistoryHeadTailFactors :
    Measurable initialNegativeTimeHistoryHeadTailFactors := by
  exact
    (measurable_fst.prodMk
      (measurable_negativeTimeHistoryTail.comp measurable_snd)).prodMk
      (((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd)))

theorem isProbabilityMeasure_negativeTimeHistoryMeasure
    {arrivalRate : ℝ} (harrival : 0 < arrivalRate) :
    IsProbabilityMeasure (negativeTimeHistoryMeasure arrivalRate) := by
  unfold negativeTimeHistoryMeasure
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure arrivalRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrival
  infer_instance

def directNegativeTimeHistory (z : TwoSidedMarkedRenewalSample) : NegativeTimeHistory :=
  ((markedRenewalTagWorkPastFactors z).1.2, (markedRenewalTagWorkPastFactors z).2)

theorem measurable_directNegativeTimeHistory :
    Measurable directNegativeTimeHistory := by
  exact
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd).comp
      measurable_markedRenewalTagWorkPastFactors

theorem directNegativeTimeHistory_eq_markedRenewalPast
    (z : TwoSidedMarkedRenewalSample) :
    directNegativeTimeHistory z =
      (fun n => markedRenewalPastWork z n, fun n => markedRenewalPastGap z n) := by
  rfl

theorem map_directNegativeTimeHistory_twoSidedMarkedRenewalMeasure
    {arrivalRate : ℝ} (harrival : 0 < arrivalRate) :
    Measure.map directNegativeTimeHistory (twoSidedMarkedRenewalMeasure arrivalRate) =
      negativeTimeHistoryMeasure arrivalRate := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure arrivalRate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure harrival
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure arrivalRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrival
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hfactor :
      Measure.map markedRenewalTagWorkPastFactors
        (twoSidedMarkedRenewalMeasure arrivalRate) =
        ((expMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure arrivalRate) := by
    exact map_markedRenewalTagWorkPastFactors_twoSidedMarkedRenewalMeasure harrival
  let retain : ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) → NegativeTimeHistory :=
    fun x => (x.1.2, x.2)
  have hretain : Measurable retain := by
    exact (measurable_snd.comp measurable_fst).prodMk measurable_snd
  calc
    Measure.map directNegativeTimeHistory (twoSidedMarkedRenewalMeasure arrivalRate) =
        Measure.map retain
          (Measure.map markedRenewalTagWorkPastFactors
            (twoSidedMarkedRenewalMeasure arrivalRate)) := by
            change Measure.map (retain ∘ markedRenewalTagWorkPastFactors)
              (twoSidedMarkedRenewalMeasure arrivalRate) = _
            rw [← Measure.map_map hretain
              measurable_markedRenewalTagWorkPastFactors]
    _ = Measure.map retain
        (((expMeasure (1 : ℝ)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure arrivalRate)) := by
          rw [hfactor]
    _ = negativeTimeHistoryMeasure arrivalRate := by
          change Measure.map (Prod.map Prod.snd id)
            (((expMeasure (1 : ℝ)).prod
              (exponentialInterarrivalMeasure (1 : ℝ))).prod
              (exponentialInterarrivalMeasure arrivalRate)) = _
          rw [← Measure.map_prod_map _ _ measurable_snd measurable_id]
          rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_id]
          rfl

def timeIncrement (serviceRate : ℝ)
    (h : NegativeTimeHistory) (n : ℕ) : ℝ :=
  h.1 n / serviceRate - h.2 n

def directTimeIncrement (serviceRate : ℝ)
    (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  timeIncrement serviceRate (directNegativeTimeHistory z) n

noncomputable def negativeTimeCausalWorkload (serviceRate : ℝ)
    (h : NegativeTimeHistory) : ℝ :=
  remotePastCausalWorkload (timeIncrement serviceRate h)

noncomputable def directTimeCausalWorkload (serviceRate : ℝ)
    (z : TwoSidedMarkedRenewalSample) : ℝ :=
  remotePastCausalWorkload (directTimeIncrement serviceRate z)

theorem directTimeCausalWorkload_eq_negativeTimeCausalWorkload
    (serviceRate : ℝ) (z : TwoSidedMarkedRenewalSample) :
    directTimeCausalWorkload serviceRate z =
      negativeTimeCausalWorkload serviceRate (directNegativeTimeHistory z) := by
  rfl

def timeReplay (serviceRate initial : ℝ)
    (h : NegativeTimeHistory) (remoteStart : ℕ) : ℝ :=
  remotePastReplayFrom initial (timeIncrement serviceRate h) remoteStart

theorem directTimeIncrement_eq_remotePastIncrement_div
    {serviceRate : ℝ} (hservice : 0 < serviceRate)
    (z : TwoSidedMarkedRenewalSample) (n : ℕ) :
    directTimeIncrement serviceRate z n =
      (remotePastBatch z n - remotePastService serviceRate z n) / serviceRate := by
  unfold directTimeIncrement timeIncrement directNegativeTimeHistory
    remotePastBatch remotePastService markedRenewalPastWork markedRenewalPastGap
    markedRenewalTagWorkPastFactors
  field_simp [ne_of_gt hservice]

theorem remotePastCumulativeNetInput_directTimeIncrement_eq_div
    {serviceRate : ℝ} (hservice : 0 < serviceRate)
    (z : TwoSidedMarkedRenewalSample) (N : ℕ) :
    remotePastCumulativeNetInput (directTimeIncrement serviceRate z) N =
      remotePastCumulativeNetInput
        (fun i => remotePastBatch z i - remotePastService serviceRate z i) N /
        serviceRate := by
  unfold remotePastCumulativeNetInput
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  exact directTimeIncrement_eq_remotePastIncrement_div hservice z n

theorem directTimeEmptyReplay_eq_timeReplay_zero
    (serviceRate : ℝ) (z : TwoSidedMarkedRenewalSample) (N : ℕ) :
    remotePastEmptyReplay (directTimeIncrement serviceRate z) N =
      timeReplay serviceRate 0 (directNegativeTimeHistory z) N := by
  unfold remotePastEmptyReplay timeReplay remotePastReplayFrom
    directTimeIncrement
  exact congrFun (lindleyWorkload_eq_from_zero _) N

private theorem lindleyWorkload_div_pos
    {serviceRate : ℝ} (hservice : 0 < serviceRate)
    (d : ℕ → ℝ) : ∀ N : ℕ,
      lindleyWorkload (fun n => d n / serviceRate) N =
        lindleyWorkload d N / serviceRate := by
  intro N
  induction N with
  | zero => simp [lindleyWorkload]
  | succ N ih =>
      change max 0
          (lindleyWorkload (fun n => d n / serviceRate) N + d N / serviceRate) =
        max 0 (lindleyWorkload d N + d N) / serviceRate
      rw [ih, ← add_div]
      calc
        max 0 ((lindleyWorkload d N + d N) / serviceRate) =
            max ((lindleyWorkload d N + d N) / serviceRate) 0 := max_comm _ _
        _ = max (lindleyWorkload d N + d N) 0 / serviceRate := by
            simpa using
              (max_div_div_right hservice.le (lindleyWorkload d N + d N) 0)
        _ = max 0 (lindleyWorkload d N + d N) / serviceRate := by
            rw [max_comm]

theorem timeReplay_zero_eq_finitePreTagWorkload_div
    {serviceRate : ℝ} (hservice : 0 < serviceRate)
    (z : TwoSidedMarkedRenewalSample) (N : ℕ) :
    timeReplay serviceRate 0 (directNegativeTimeHistory z) N =
      finitePreTagWorkload serviceRate z N / serviceRate := by
  let d : ℕ → ℝ := fun i =>
    remotePastBatch z i - remotePastService serviceRate z i
  have hreverse :
      reverseRemotePastIncrement (directTimeIncrement serviceRate z) N =
        fun j => reverseRemotePastIncrement d N j / serviceRate := by
    funext j
    change directTimeIncrement serviceRate z (N - (j + 1)) =
      (remotePastBatch z (N - (j + 1)) -
        remotePastService serviceRate z (N - (j + 1))) / serviceRate
    exact directTimeIncrement_eq_remotePastIncrement_div hservice z _
  have hfinite : finitePreTagWorkload serviceRate z N =
      lindleyWorkload (reverseRemotePastIncrement d N) N := by
    calc
      finitePreTagWorkload serviceRate z N =
          lindleyWorkload
            (fun j => reverseRemotePastIncrement (remotePastBatch z) N j -
              reverseRemotePastIncrement (remotePastService serviceRate z) N j) N := by
            unfold finitePreTagWorkload
            exact congrFun (lateBatchPreWorkload_eq_lindleyWorkload _ _) N
      _ = lindleyWorkload (reverseRemotePastIncrement d N) N := by
            rfl
  unfold timeReplay
  change remotePastReplayFrom 0 (directTimeIncrement serviceRate z) N = _
  unfold remotePastReplayFrom
  rw [← congrFun (lindleyWorkload_eq_from_zero _) N, hreverse,
    lindleyWorkload_div_pos hservice (reverseRemotePastIncrement d N) N, ← hfinite]

theorem ae_tendsto_directTimeCumulativeNetInput_atBot_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure arrivalRate,
      Tendsto (remotePastCumulativeNetInput (directTimeIncrement serviceRate z))
        atTop atBot := by
  have hservice : 0 < serviceRate := lt_trans harrival hstable
  have hneg : 1 - serviceRate / arrivalRate < 0 := by
    rw [sub_neg]
    exact (lt_div_iff₀ harrival).2 (by simpa using hstable)
  have hunscaled : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure arrivalRate,
      Tendsto
        (remotePastCumulativeNetInput
          (fun i => remotePastBatch z i - remotePastService serviceRate z i))
        atTop atBot := by
    filter_upwards [
      ae_tendsto_markedRenewalPastCumulativeNetWork_div_nat_succ harrival]
      with z hz
    have hsucc_atBot : Tendsto
        (fun n : ℕ =>
          remotePastCumulativeNetInput
            (fun i => remotePastBatch z i - remotePastService serviceRate z i)
            (n + 1))
        atTop atBot := by
      have hrewrite :
          (fun n : ℕ =>
            remotePastCumulativeNetInput
              (fun i => remotePastBatch z i - remotePastService serviceRate z i)
              (n + 1) / ((n + 1 : ℕ) : ℝ)) =
            fun n : ℕ =>
              markedRenewalPastCumulativeNetWork serviceRate z n /
                ((n + 1 : ℕ) : ℝ) := by
          funext n
          rw [remotePastCumulativeNetInput_succ]
      have hratio : Tendsto
          (fun n : ℕ =>
            remotePastCumulativeNetInput
              (fun i => remotePastBatch z i - remotePastService serviceRate z i)
              (n + 1) / ((n + 1 : ℕ) : ℝ))
          atTop (nhds (1 - serviceRate / arrivalRate)) := by
        rw [hrewrite]
        exact hz
      exact tendsto_atBot_of_tendsto_div_nat_succ_neg _ _ hratio hneg
    exact tendsto_atBot_of_tendsto_succ_atBot _ hsucc_atBot
  filter_upwards [hunscaled] with z hz
  rw [show remotePastCumulativeNetInput (directTimeIncrement serviceRate z) =
      fun N => remotePastCumulativeNetInput
        (fun i => remotePastBatch z i - remotePastService serviceRate z i) N /
          serviceRate by
        funext N
        exact remotePastCumulativeNetInput_directTimeIncrement_eq_div hservice z N]
  exact hz.atBot_div_const hservice

def timeStep (serviceRate : ℝ) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  max (x.1 + x.2.1 / serviceRate - x.2.2) 0

theorem measurable_timeStep (serviceRate : ℝ) :
    Measurable (timeStep serviceRate) := by
  unfold timeStep
  exact
    ((measurable_fst.add
      ((measurable_fst.comp measurable_snd).div measurable_const)).sub
        (measurable_snd.comp measurable_snd)).max measurable_const

private theorem lindleyWorkloadFrom_congr_of_forall_lt
    (initial : ℝ) {increment₁ increment₂ : ℕ → ℝ} {n : ℕ}
    (h : ∀ j < n, increment₁ j = increment₂ j) :
    lindleyWorkloadFrom initial increment₁ n =
      lindleyWorkloadFrom initial increment₂ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change max 0 (lindleyWorkloadFrom initial increment₁ n + increment₁ n) =
        max 0 (lindleyWorkloadFrom initial increment₂ n + increment₂ n)
      rw [ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))),
        h n (Nat.lt_succ_self n)]

theorem timeReplay_succ_eq_tail_update
    (serviceRate initial : ℝ) (h : NegativeTimeHistory) (N : ℕ) :
    timeReplay serviceRate initial h (N + 1) =
      timeStep serviceRate
        (timeReplay serviceRate initial (negativeTimeHistoryTail h) N,
          (h.1 0, h.2 0)) := by
  unfold timeReplay timeStep
  let d : ℕ → ℝ := timeIncrement serviceRate h
  let dtail : ℕ → ℝ := timeIncrement serviceRate (negativeTimeHistoryTail h)
  have hpre :
      lindleyWorkloadFrom initial (reverseRemotePastIncrement d (N + 1)) N =
        lindleyWorkloadFrom initial (reverseRemotePastIncrement dtail N) N := by
    apply lindleyWorkloadFrom_congr_of_forall_lt
    intro j hj
    change timeIncrement serviceRate h (N + 1 - (j + 1)) =
      timeIncrement serviceRate (negativeTimeHistoryTail h) (N - (j + 1))
    have hindex : N + 1 - (j + 1) = (N - (j + 1)) + 1 := by omega
    rw [hindex]
    rfl
  change lindleyWorkloadFrom initial (reverseRemotePastIncrement d (N + 1)) (N + 1) =
    max
      (lindleyWorkloadFrom initial (reverseRemotePastIncrement dtail N) N +
        h.1 0 / serviceRate - h.2 0) 0
  rw [show lindleyWorkloadFrom initial (reverseRemotePastIncrement d (N + 1)) (N + 1) =
      max 0 (lindleyWorkloadFrom initial (reverseRemotePastIncrement d (N + 1)) N +
        reverseRemotePastIncrement d (N + 1) N) by rfl,
    hpre]
  have hlast : reverseRemotePastIncrement d (N + 1) N =
      h.1 0 / serviceRate - h.2 0 := by
    simp [reverseRemotePastIncrement, d, timeIncrement]
  rw [hlast]
  calc
    max 0
        (lindleyWorkloadFrom initial (reverseRemotePastIncrement dtail N) N +
          (h.1 0 / serviceRate - h.2 0)) =
        max
          (lindleyWorkloadFrom initial (reverseRemotePastIncrement dtail N) N +
            (h.1 0 / serviceRate - h.2 0)) 0 := max_comm _ _
    _ = max
        (lindleyWorkloadFrom initial (reverseRemotePastIncrement dtail N) N +
          h.1 0 / serviceRate - h.2 0) 0 := by
            congr 1
            ring

theorem measurable_timeReplay (serviceRate : ℝ) (N : ℕ) :
    Measurable (fun x : ℝ × NegativeTimeHistory =>
      timeReplay serviceRate x.1 x.2 N) := by
  induction N with
  | zero =>
      change Measurable (fun x : ℝ × NegativeTimeHistory => x.1)
      exact measurable_fst
  | succ N ih =>
      rw [show (fun x : ℝ × NegativeTimeHistory =>
        timeReplay serviceRate x.1 x.2 (N + 1)) =
        fun x => timeStep serviceRate
          (timeReplay serviceRate x.1 (negativeTimeHistoryTail x.2) N,
            (x.2.1 0, x.2.2 0)) by
          funext x
          exact timeReplay_succ_eq_tail_update serviceRate x.1 x.2 N]
      apply (measurable_timeStep serviceRate).comp
      exact
        ((ih.comp (measurable_fst.prodMk
          (measurable_negativeTimeHistoryTail.comp measurable_snd))).prodMk
          (((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))

theorem measurable_negativeTimeCausalWorkload (serviceRate : ℝ) :
    Measurable (negativeTimeCausalWorkload serviceRate) := by
  unfold negativeTimeCausalWorkload remotePastCausalWorkload
  apply Measurable.limsup
  intro N
  have hinput : Measurable (fun h : NegativeTimeHistory => ((0 : ℝ), h)) := by
    exact measurable_const.prodMk measurable_id
  have hreplay := (measurable_timeReplay serviceRate N).comp hinput
  have heq :
      (fun h : NegativeTimeHistory =>
        remotePastEmptyReplay (timeIncrement serviceRate h) N) =
      fun h => timeReplay serviceRate 0 h N := by
    funext h
    unfold remotePastEmptyReplay timeReplay remotePastReplayFrom
    exact congrFun (lindleyWorkload_eq_from_zero _) N
  rw [heq]
  exact hreplay

theorem measurable_directTimeCausalWorkload (serviceRate : ℝ) :
    Measurable (directTimeCausalWorkload serviceRate) := by
  unfold directTimeCausalWorkload remotePastCausalWorkload
  apply Measurable.limsup
  intro N
  have hinput : Measurable (fun z : TwoSidedMarkedRenewalSample =>
      ((0 : ℝ), directNegativeTimeHistory z)) := by
    exact measurable_const.prodMk measurable_directNegativeTimeHistory
  have hreplay := (measurable_timeReplay serviceRate N).comp hinput
  simpa only [directTimeEmptyReplay_eq_timeReplay_zero] using hreplay

theorem mm1PreArrivalWorkloadLaw_conv_serviceTime_eq_expMeasure_slack
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    mm1PreArrivalWorkloadLaw arrivalRate serviceRate ∗ expMeasure serviceRate =
      expMeasure (mm1SlackRate arrivalRate serviceRate) := by
  have hslack : 0 < mm1SlackRate arrivalRate serviceRate :=
    sub_pos.mpr hstable
  have hservice : 0 < serviceRate := lt_trans harrival hstable
  have hsum : mm1SlackRate arrivalRate serviceRate + arrivalRate = serviceRate := by
    unfold mm1SlackRate
    linarith
  letI : IsProbabilityMeasure (expMeasure (mm1SlackRate arrivalRate serviceRate)) :=
    isProbabilityMeasure_expMeasure hslack
  letI : IsProbabilityMeasure (expMeasure arrivalRate) :=
    isProbabilityMeasure_expMeasure harrival
  letI : IsProbabilityMeasure (expMeasure serviceRate) :=
    isProbabilityMeasure_expMeasure hservice
  unfold mm1PreArrivalWorkloadLaw
  rw [Measure.add_conv, Measure.conv_smul_left, Measure.conv_smul_left,
    Measure.dirac_zero_conv]
  simpa [hsum] using
    (weighted_expMeasure_unequalRate_conv_eq_expMeasure hslack harrival)

theorem map_mm1PreArrivalWorkload_add_unitWork_div_eq_expMeasure_slack
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Measure.map (fun x : ℝ × ℝ => x.1 + x.2 / serviceRate)
      ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
        (expMeasure (1 : ℝ))) =
      expMeasure (mm1SlackRate arrivalRate serviceRate) := by
  have hservice : 0 < serviceRate := lt_trans harrival hstable
  letI : IsProbabilityMeasure (mm1PreArrivalWorkloadLaw arrivalRate serviceRate) :=
    isProbabilityMeasure_mm1PreArrivalWorkloadLaw harrival hstable
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (expMeasure serviceRate) :=
    isProbabilityMeasure_expMeasure hservice
  let hdiv : Measurable (fun x : ℝ => x / serviceRate) :=
    measurable_id.div measurable_const
  calc
    Measure.map (fun x : ℝ × ℝ => x.1 + x.2 / serviceRate)
        ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
          (expMeasure (1 : ℝ))) =
        Measure.map (fun x : ℝ × ℝ => x.1 + x.2)
          (Measure.map (Prod.map id (fun x : ℝ => x / serviceRate))
            ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
              (expMeasure (1 : ℝ)))) := by
          rw [Measure.map_map (measurable_fst.add measurable_snd)
            (measurable_id.prodMap hdiv)]
          rfl
    _ = Measure.map (fun x : ℝ × ℝ => x.1 + x.2)
          ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
            (expMeasure serviceRate)) := by
          rw [← Measure.map_prod_map _ _ measurable_id hdiv, Measure.map_id,
            map_div_unitExpMeasure_eq_expMeasure hservice]
    _ = (mm1PreArrivalWorkloadLaw arrivalRate serviceRate) ∗
          (expMeasure serviceRate) := by
          rfl
    _ = expMeasure (mm1SlackRate arrivalRate serviceRate) :=
      mm1PreArrivalWorkloadLaw_conv_serviceTime_eq_expMeasure_slack harrival hstable

theorem map_timeStep_mm1PreArrivalWorkloadLaw_prod
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Measure.map (timeStep serviceRate)
      ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
        ((expMeasure (1 : ℝ)).prod (expMeasure arrivalRate))) =
      mm1PreArrivalWorkloadLaw arrivalRate serviceRate := by
  have hservice : 0 < serviceRate := lt_trans harrival hstable
  let M : Measure ℝ := mm1PreArrivalWorkloadLaw arrivalRate serviceRate
  let E : Measure ℝ := expMeasure (1 : ℝ)
  let A : Measure ℝ := expMeasure arrivalRate
  let R : Measure ℝ := expMeasure (mm1SlackRate arrivalRate serviceRate)
  letI : IsProbabilityMeasure M := by
    exact isProbabilityMeasure_mm1PreArrivalWorkloadLaw harrival hstable
  letI : IsProbabilityMeasure E := by
    exact isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure A := by
    exact isProbabilityMeasure_expMeasure harrival
  letI : IsProbabilityMeasure R := by
    exact isProbabilityMeasure_expMeasure (sub_pos.mpr hstable)
  let assoc : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  let sumDiv : ℝ × ℝ → ℝ :=
    fun x => x.1 + x.2 / serviceRate
  let combine : (ℝ × ℝ) × ℝ → ℝ × ℝ :=
    fun x => (sumDiv x.1, x.2)
  have hassoc : Measurable assoc := MeasurableEquiv.prodAssoc.symm.measurable
  have hsumDiv : Measurable sumDiv := by
    exact measurable_fst.add (measurable_snd.div measurable_const)
  have hcombine : Measurable combine := by
    exact hsumDiv.comp measurable_fst |>.prodMk measurable_snd
  have hassocLaw :
      Measure.map assoc (M.prod (E.prod A)) = (M.prod E).prod A := by
    simpa [assoc] using (measurePreserving_prodAssoc M E A).symm.map_eq
  have hcombineLaw :
      Measure.map combine ((M.prod E).prod A) = R.prod A := by
    calc
      Measure.map combine ((M.prod E).prod A) =
          Measure.map (Prod.map sumDiv id)
            ((M.prod E).prod A) := by
            rfl
      _ = (Measure.map sumDiv (M.prod E)).prod (Measure.map id A) := by
            rw [Measure.map_prod_map _ _ hsumDiv measurable_id]
      _ = R.prod A := by
            rw [map_mm1PreArrivalWorkload_add_unitWork_div_eq_expMeasure_slack
              harrival hstable, Measure.map_id]
  have hstep : timeStep serviceRate =
      exponentialReflectedDifference ∘ combine ∘ assoc := by
    funext x
    rfl
  calc
    Measure.map (timeStep serviceRate) (M.prod (E.prod A)) =
        Measure.map exponentialReflectedDifference
          (Measure.map combine (Measure.map assoc (M.prod (E.prod A)))) := by
          rw [hstep]
          symm
          rw [Measure.map_map measurable_exponentialReflectedDifference hcombine,
            Measure.map_map
              (measurable_exponentialReflectedDifference.comp hcombine) hassoc]
          rfl
    _ = Measure.map exponentialReflectedDifference (R.prod A) := by
          rw [hassocLaw, hcombineLaw]
    _ = M := by
          simpa [M, R, A] using
            (mm1PreArrivalWorkloadLaw_eq_reflectedDifference harrival hstable).symm

theorem timeReplay_hasLaw_of_initialHeadTailFactor
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (hfactor :
      Measure.map initialNegativeTimeHistoryHeadTailFactors
        ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
          (negativeTimeHistoryMeasure arrivalRate)) =
        ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
          (negativeTimeHistoryMeasure arrivalRate)).prod
          ((expMeasure (1 : ℝ)).prod (expMeasure arrivalRate)))
    (N : ℕ) :
    HasLaw
      (fun x : ℝ × NegativeTimeHistory =>
        timeReplay serviceRate x.1 x.2 N)
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate)
      ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
        (negativeTimeHistoryMeasure arrivalRate)) := by
  let M : Measure ℝ := mm1PreArrivalWorkloadLaw arrivalRate serviceRate
  let H : Measure NegativeTimeHistory := negativeTimeHistoryMeasure arrivalRate
  let I : Measure (ℝ × ℝ) := (expMeasure (1 : ℝ)).prod (expMeasure arrivalRate)
  let P : Measure (ℝ × NegativeTimeHistory) := M.prod H
  letI : IsProbabilityMeasure M := by
    exact isProbabilityMeasure_mm1PreArrivalWorkloadLaw harrival hstable
  letI : IsProbabilityMeasure H := by
    exact isProbabilityMeasure_negativeTimeHistoryMeasure harrival
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
      isProbabilityMeasure_expMeasure (by norm_num)
    letI : IsProbabilityMeasure (expMeasure arrivalRate) :=
      isProbabilityMeasure_expMeasure harrival
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hfactor' : Measure.map initialNegativeTimeHistoryHeadTailFactors P = P.prod I := by
    simpa [M, H, I, P] using hfactor
  have hstep : Measure.map (timeStep serviceRate) (M.prod I) = M := by
    simpa [M, I] using
      map_timeStep_mm1PreArrivalWorkloadLaw_prod harrival hstable
  change HasLaw
    (fun x : ℝ × NegativeTimeHistory =>
      timeReplay serviceRate x.1 x.2 N) M P
  induction N with
  | zero =>
      refine ⟨(measurable_timeReplay serviceRate 0).aemeasurable, ?_⟩
      change Measure.map (fun x : ℝ × NegativeTimeHistory => x.1) P = M
      rw [Measure.map_fst_prod, measure_univ, one_smul]
  | succ N hN =>
      let replay : ℝ × NegativeTimeHistory → ℝ :=
        fun x => timeReplay serviceRate x.1 x.2 N
      let F : (ℝ × NegativeTimeHistory) × (ℝ × ℝ) → ℝ × (ℝ × ℝ) :=
        fun x => (replay x.1, x.2)
      have hReplayMeas : Measurable replay := by
        exact measurable_timeReplay serviceRate N
      have hFmeas : Measurable F := by
        exact (hReplayMeas.comp measurable_fst).prodMk measurable_snd
      have hFlaw : Measure.map F (P.prod I) = M.prod I := by
        calc
          Measure.map F (P.prod I) =
              (Measure.map replay P).prod (Measure.map id I) := by
                change Measure.map (Prod.map replay id) (P.prod I) = _
                rw [Measure.map_prod_map P I hReplayMeas measurable_id]
          _ = M.prod I := by
                rw [show Measure.map replay P = M by
                  simpa [replay] using hN.map_eq, Measure.map_id]
      have hsuccfun :
          (fun x : ℝ × NegativeTimeHistory =>
            timeReplay serviceRate x.1 x.2 (N + 1)) =
          timeStep serviceRate ∘ F ∘ initialNegativeTimeHistoryHeadTailFactors := by
        funext x
        change timeReplay serviceRate x.1 x.2 (N + 1) =
          timeStep serviceRate
            (timeReplay serviceRate x.1 (negativeTimeHistoryTail x.2) N,
              (x.2.1 0, x.2.2 0))
        exact timeReplay_succ_eq_tail_update serviceRate x.1 x.2 N
      refine ⟨(measurable_timeReplay serviceRate (N + 1)).aemeasurable, ?_⟩
      change Measure.map
        (fun x : ℝ × NegativeTimeHistory =>
          timeReplay serviceRate x.1 x.2 (N + 1)) P = M
      rw [hsuccfun]
      calc
        Measure.map
            (timeStep serviceRate ∘ F ∘ initialNegativeTimeHistoryHeadTailFactors) P =
            Measure.map (timeStep serviceRate)
              (Measure.map F
                (Measure.map initialNegativeTimeHistoryHeadTailFactors P)) := by
              rw [← Measure.map_map (measurable_timeStep serviceRate)
                (hFmeas.comp measurable_initialNegativeTimeHistoryHeadTailFactors),
                ← Measure.map_map hFmeas
                  measurable_initialNegativeTimeHistoryHeadTailFactors]
        _ = Measure.map (timeStep serviceRate) (Measure.map F (P.prod I)) := by
              rw [hfactor']
        _ = Measure.map (timeStep serviceRate) (M.prod I) := by
              rw [hFlaw]
        _ = M := hstep

theorem timeReplay_hasLaw
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (N : ℕ) :
    HasLaw
      (fun x : ℝ × NegativeTimeHistory =>
        timeReplay serviceRate x.1 x.2 N)
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate)
      ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
        (negativeTimeHistoryMeasure arrivalRate)) := by
  letI : IsProbabilityMeasure (mm1PreArrivalWorkloadLaw arrivalRate serviceRate) :=
    isProbabilityMeasure_mm1PreArrivalWorkloadLaw harrival hstable
  apply timeReplay_hasLaw_of_initialHeadTailFactor harrival hstable _ N
  simpa [initialNegativeTimeHistoryHeadTailFactors, negativeTimeHistoryTail,
    negativeTimeHistoryMeasure, initialTwoStreamHeadTailFactors] using
    (map_initialTwoStreamHeadTailFactors
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate)
      (leftRate := (1 : ℝ)) (rightRate := arrivalRate) (by norm_num) harrival)

theorem timeReplay_directMarkedRenewal_hasLaw
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (N : ℕ) :
    HasLaw
      (fun x : ℝ × TwoSidedMarkedRenewalSample =>
        timeReplay serviceRate x.1 (directNegativeTimeHistory x.2) N)
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate)
      ((mm1PreArrivalWorkloadLaw arrivalRate serviceRate).prod
        (twoSidedMarkedRenewalMeasure arrivalRate)) := by
  let M : Measure ℝ := mm1PreArrivalWorkloadLaw arrivalRate serviceRate
  let H : Measure NegativeTimeHistory := negativeTimeHistoryMeasure arrivalRate
  let S : Measure TwoSidedMarkedRenewalSample :=
    twoSidedMarkedRenewalMeasure arrivalRate
  letI : IsProbabilityMeasure M := by
    exact isProbabilityMeasure_mm1PreArrivalWorkloadLaw harrival hstable
  letI : IsProbabilityMeasure H := by
    exact isProbabilityMeasure_negativeTimeHistoryMeasure harrival
  letI : IsProbabilityMeasure S := by
    dsimp [S, twoSidedMarkedRenewalMeasure]
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure arrivalRate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure harrival
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
    infer_instance
  let historyMap : ℝ × TwoSidedMarkedRenewalSample → ℝ × NegativeTimeHistory :=
    Prod.map id directNegativeTimeHistory
  have hhistoryMapMeas : Measurable historyMap := by
    exact measurable_id.prodMap measurable_directNegativeTimeHistory
  have hhistory : HasLaw historyMap (M.prod H) (M.prod S) := by
    refine ⟨hhistoryMapMeas.aemeasurable, ?_⟩
    calc
      Measure.map historyMap (M.prod S) =
          (Measure.map id M).prod
            (Measure.map directNegativeTimeHistory S) := by
            change Measure.map (Prod.map id directNegativeTimeHistory) (M.prod S) = _
            rw [← Measure.map_prod_map M S measurable_id
              measurable_directNegativeTimeHistory]
      _ = M.prod H := by
            rw [Measure.map_id,
              map_directNegativeTimeHistory_twoSidedMarkedRenewalMeasure harrival]
  have htime : HasLaw
      (fun x : ℝ × NegativeTimeHistory =>
        timeReplay serviceRate x.1 x.2 N) M (M.prod H) := by
    simpa [M, H] using timeReplay_hasLaw harrival hstable N
  simpa [historyMap, Function.comp_def, M, S] using htime.comp hhistory

theorem directTimeCausalWorkload_hasLaw
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    HasLaw (directTimeCausalWorkload serviceRate)
      (mm1PreArrivalWorkloadLaw arrivalRate serviceRate)
      (twoSidedMarkedRenewalMeasure arrivalRate) := by
  let M : Measure ℝ := mm1PreArrivalWorkloadLaw arrivalRate serviceRate
  let S : Measure TwoSidedMarkedRenewalSample :=
    twoSidedMarkedRenewalMeasure arrivalRate
  let P : Measure (ℝ × TwoSidedMarkedRenewalSample) := M.prod S
  letI : IsProbabilityMeasure M := by
    exact isProbabilityMeasure_mm1PreArrivalWorkloadLaw harrival hstable
  letI : IsProbabilityMeasure S := by
    dsimp [S, twoSidedMarkedRenewalMeasure]
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure arrivalRate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure harrival
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hsnd : Measure.map Prod.snd P = S := by
    dsimp [P]
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hnonnegM : ∀ᵐ w ∂M, 0 ≤ w := by
    simpa [M] using ae_nonnegative_mm1PreArrivalWorkloadLaw harrival hstable
  have hinitial : ∀ᵐ x ∂P, 0 ≤ x.1 := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := Prod.fst)
      measurable_fst.aemeasurable ?_
    change ∀ᵐ w ∂Measure.map Prod.fst P, 0 ≤ w
    rw [show Measure.map Prod.fst P = M by
      dsimp [P]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact hnonnegM
  have hlimS : ∀ᵐ z ∂S,
      Tendsto (remotePastCumulativeNetInput (directTimeIncrement serviceRate z))
        atTop atBot := by
    simpa [S] using
      ae_tendsto_directTimeCumulativeNetInput_atBot_of_rate_lt harrival hstable
  have hlim : ∀ᵐ x ∂P,
      Tendsto (remotePastCumulativeNetInput
        (fun n => directTimeIncrement serviceRate x.2 n)) atTop atBot := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := Prod.snd)
      (p := fun z : TwoSidedMarkedRenewalSample =>
        Tendsto (remotePastCumulativeNetInput (directTimeIncrement serviceRate z))
          atTop atBot)
      measurable_snd.aemeasurable ?_
    change ∀ᵐ z ∂Measure.map Prod.snd P,
      Tendsto (remotePastCumulativeNetInput (directTimeIncrement serviceRate z))
        atTop atBot
    rw [hsnd]
    exact hlimS
  have hreplayMeas : ∀ n, Measurable (fun x : ℝ × TwoSidedMarkedRenewalSample =>
      remotePastReplayFrom x.1
        (fun k => directTimeIncrement serviceRate x.2 k) n) := by
    intro n
    change Measurable (fun x : ℝ × TwoSidedMarkedRenewalSample =>
      timeReplay serviceRate x.1 (directNegativeTimeHistory x.2) n)
    exact (measurable_timeReplay serviceRate n).comp
      (measurable_fst.prodMk
        (measurable_directNegativeTimeHistory.comp measurable_snd))
  have hcausalMeas : Measurable (fun x : ℝ × TwoSidedMarkedRenewalSample =>
      remotePastCausalWorkload (fun k => directTimeIncrement serviceRate x.2 k)) := by
    change Measurable (fun x : ℝ × TwoSidedMarkedRenewalSample =>
      directTimeCausalWorkload serviceRate x.2)
    exact (measurable_directTimeCausalWorkload serviceRate).comp measurable_snd
  have hreplayLaw : ∀ n, HasLaw
      (fun x : ℝ × TwoSidedMarkedRenewalSample =>
        remotePastReplayFrom x.1
          (fun k => directTimeIncrement serviceRate x.2 k) n) M P := by
    intro n
    simpa [M, S, P, timeReplay, directTimeIncrement] using
      timeReplay_directMarkedRenewal_hasLaw harrival hstable n
  have hproductLaw : HasLaw
      (fun x : ℝ × TwoSidedMarkedRenewalSample =>
        directTimeCausalWorkload serviceRate x.2) M P := by
    simpa [directTimeCausalWorkload] using
      (hasLaw_remotePastCausalWorkload_of_all_replayLaws P
        (fun x : ℝ × TwoSidedMarkedRenewalSample => x.1)
        (fun x : ℝ × TwoSidedMarkedRenewalSample =>
          fun n => directTimeIncrement serviceRate x.2 n)
        M hinitial hlim hreplayMeas hcausalMeas hreplayLaw)
  have hignore :
      Measure.map
        (fun x : ℝ × TwoSidedMarkedRenewalSample =>
          directTimeCausalWorkload serviceRate x.2) P =
        Measure.map (directTimeCausalWorkload serviceRate) S := by
    change Measure.map
      (directTimeCausalWorkload serviceRate ∘ Prod.snd) P = _
    rw [← Measure.map_map (measurable_directTimeCausalWorkload serviceRate)
      measurable_snd, hsnd]
  refine ⟨(measurable_directTimeCausalWorkload serviceRate).aemeasurable, ?_⟩
  calc
    Measure.map (directTimeCausalWorkload serviceRate) S =
        Measure.map
          (fun x : ℝ × TwoSidedMarkedRenewalSample =>
            directTimeCausalWorkload serviceRate x.2) P := hignore.symm
    _ = M := hproductLaw.map_eq

theorem integrable_directTimeCausalWorkload
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Integrable (directTimeCausalWorkload serviceRate)
      (twoSidedMarkedRenewalMeasure arrivalRate) := by
  have hhas := directTimeCausalWorkload_hasLaw harrival hstable
  have hmeasure :
      Measure.map (directTimeCausalWorkload serviceRate)
        (twoSidedMarkedRenewalMeasure arrivalRate) =
        mm1PreArrivalWorkloadLaw arrivalRate serviceRate := hhas.map_eq
  have hid : Integrable (fun w : ℝ => w)
      (Measure.map (directTimeCausalWorkload serviceRate)
        (twoSidedMarkedRenewalMeasure arrivalRate)) := by
    rw [hmeasure]
    exact integrable_id_mm1PreArrivalWorkloadLaw hstable
  simpa only [Function.comp_apply] using
    (integrable_map_measure (measurable_id.aestronglyMeasurable)
      hhas.aemeasurable).mp hid

theorem timeReplay_zero_le_directTimeCausalWorkload_of_tendsto_atBot
    {serviceRate : ℝ} (z : TwoSidedMarkedRenewalSample)
    (hlim : Tendsto
      (remotePastCumulativeNetInput (directTimeIncrement serviceRate z))
      atTop atBot)
    (N : ℕ) :
    timeReplay serviceRate 0 (directNegativeTimeHistory z) N ≤
      directTimeCausalWorkload serviceRate z := by
  let d : ℕ → ℝ := directTimeIncrement serviceRate z
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hmax⟩
  have hcausal : directTimeCausalWorkload serviceRate z =
      remotePastEmptyReplay d K := by
    exact remotePastCausalWorkload_eq_emptyReplay_of_global_cutoff d K hmax
  have htime : timeReplay serviceRate 0 (directNegativeTimeHistory z) N =
      remotePastEmptyReplay d N := by
    exact (directTimeEmptyReplay_eq_timeReplay_zero serviceRate z N).symm
  rw [htime, hcausal]
  rcases le_total N K with hNK | hKN
  · simpa [remotePastEmptyReplay] using
      lindleyWorkload_reverseRemotePast_mono d N K hNK
  · have hcarried : (0 : ℝ) +
      (remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K) ≤ 0 := by
      linarith [hmax N]
    have hcoalesces :=
      lindleyWorkloadFrom_reverseRemotePast_coalesces_at_present_of_global_cutoff
        (initial := (0 : ℝ)) d K N (by norm_num) hKN hmax hcarried
    exact le_of_eq (by
      simpa [remotePastReplayFrom, remotePastEmptyReplay, lindleyWorkload_eq_from_zero] using
        hcoalesces)

/-- Every finite zero-start replay is bounded by its causal remote-past
workload whenever the cumulative increment path has negative long-run drift. -/
theorem timeReplay_zero_le_negativeTimeCausalWorkload_of_tendsto_atBot
    {serviceRate : ℝ} (h : NegativeTimeHistory)
    (hlim : Tendsto
      (remotePastCumulativeNetInput (timeIncrement serviceRate h))
      atTop atBot)
    (N : ℕ) :
    timeReplay serviceRate 0 h N ≤ negativeTimeCausalWorkload serviceRate h := by
  let d : ℕ → ℝ := timeIncrement serviceRate h
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hmax⟩
  have hcausal : negativeTimeCausalWorkload serviceRate h =
      remotePastEmptyReplay d K := by
    exact remotePastCausalWorkload_eq_emptyReplay_of_global_cutoff d K hmax
  have htime : timeReplay serviceRate 0 h N = remotePastEmptyReplay d N := by
    change lindleyWorkloadFrom 0 (reverseRemotePastIncrement d N) N =
      lindleyWorkload (reverseRemotePastIncrement d N) N
    exact (congrFun (lindleyWorkload_eq_from_zero (reverseRemotePastIncrement d N)) N).symm
  rw [htime, hcausal]
  rcases le_total N K with hNK | hKN
  · simpa [remotePastEmptyReplay] using
      lindleyWorkload_reverseRemotePast_mono d N K hNK
  · have hcarried : (0 : ℝ) +
      (remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K) ≤ 0 := by
      linarith [hmax N]
    have hcoalesces :=
      lindleyWorkloadFrom_reverseRemotePast_coalesces_at_present_of_global_cutoff
        (initial := (0 : ℝ)) d K N (by norm_num) hKN hmax hcarried
    exact le_of_eq (by
      simpa [remotePastReplayFrom, remotePastEmptyReplay, lindleyWorkload_eq_from_zero] using
        hcoalesces)

/-- Under its explicit product law, every finite zero-start replay is almost
surely bounded by the causal negative-time workload. -/
theorem ae_timeReplay_zero_le_negativeTimeCausalWorkload_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    (N : ℕ) :
    ∀ᵐ h ∂negativeTimeHistoryMeasure arrivalRate,
      timeReplay serviceRate 0 h N ≤ negativeTimeCausalWorkload serviceRate h := by
  rw [← map_directNegativeTimeHistory_twoSidedMarkedRenewalMeasure harrival]
  refine (MeasureTheory.ae_map_iff measurable_directNegativeTimeHistory.aemeasurable
    (p := fun h : NegativeTimeHistory =>
      timeReplay serviceRate 0 h N ≤ negativeTimeCausalWorkload serviceRate h)
    (measurableSet_le ((measurable_timeReplay serviceRate N).comp
      (measurable_const.prodMk measurable_id))
      (measurable_negativeTimeCausalWorkload serviceRate))).2 ?_
  filter_upwards [
    ae_tendsto_directTimeCumulativeNetInput_atBot_of_rate_lt harrival hstable]
    with z hlim
  simpa [directTimeCausalWorkload_eq_negativeTimeCausalWorkload] using
    timeReplay_zero_le_directTimeCausalWorkload_of_tendsto_atBot z hlim N

theorem directTimeCausalWorkload_eq_measurablePreTagWorkload_div_of_tendsto_atBot
    {serviceRate : ℝ} (hservice : 0 < serviceRate)
    (z : TwoSidedMarkedRenewalSample)
    (hlim : Tendsto
      (remotePastCumulativeNetInput (directTimeIncrement serviceRate z))
      atTop atBot)
    (hcoal : PreTagCoalesces serviceRate z) :
    directTimeCausalWorkload serviceRate z =
      measurablePreTagWorkload serviceRate z / serviceRate := by
  have heventual : ∀ᶠ N : ℕ in atTop,
      timeReplay serviceRate 0 (directNegativeTimeHistory z) N =
        directTimeCausalWorkload serviceRate z := by
    simpa [timeReplay, directTimeCausalWorkload, directTimeIncrement] using
      (eventually_remotePastReplayFrom_eq_causalWorkload_of_tendsto_atBot
        (initial := (0 : ℝ)) (directTimeIncrement serviceRate z) (by norm_num) hlim)
  rcases preTagWorkload_eq_finite_of_coalesces serviceRate z hcoal with ⟨K, hK⟩
  rcases Filter.eventually_atTop.1 heventual with ⟨N, hN⟩
  let L := max N K
  have hNL : N ≤ L := le_max_left _ _
  have hKL : K ≤ L := le_max_right _ _
  calc
    directTimeCausalWorkload serviceRate z =
        timeReplay serviceRate 0 (directNegativeTimeHistory z) L :=
      (hN L hNL).symm
    _ = finitePreTagWorkload serviceRate z L / serviceRate :=
      timeReplay_zero_eq_finitePreTagWorkload_div hservice z L
    _ = preTagWorkload serviceRate z / serviceRate := by
      rw [← hK L hKL]
    _ = measurablePreTagWorkload serviceRate z / serviceRate := by
      rw [preTagWorkload_eq_measurablePreTagWorkload_of_coalesces
        serviceRate z hcoal]

theorem ae_directTimeCausalWorkload_eq_measurablePreTagWorkload_div_of_rate_lt
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    directTimeCausalWorkload serviceRate =ᵐ[
      twoSidedMarkedRenewalMeasure arrivalRate]
      fun z => measurablePreTagWorkload serviceRate z / serviceRate := by
  have hservice : 0 < serviceRate := lt_trans harrival hstable
  filter_upwards [
    ae_tendsto_directTimeCumulativeNetInput_atBot_of_rate_lt harrival hstable,
    ae_preTagCoalesces_of_rate_lt harrival hstable] with z hlim hcoal
  exact directTimeCausalWorkload_eq_measurablePreTagWorkload_div_of_tendsto_atBot
    hservice z hlim hcoal

theorem map_negativeTimeCausalWorkload_eq_mm1PreArrivalWorkloadLaw
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Measure.map (negativeTimeCausalWorkload serviceRate)
      (negativeTimeHistoryMeasure arrivalRate) =
      mm1PreArrivalWorkloadLaw arrivalRate serviceRate := by
  calc
    Measure.map (negativeTimeCausalWorkload serviceRate)
        (negativeTimeHistoryMeasure arrivalRate) =
        Measure.map (negativeTimeCausalWorkload serviceRate)
          (Measure.map directNegativeTimeHistory
            (twoSidedMarkedRenewalMeasure arrivalRate)) := by
          rw [map_directNegativeTimeHistory_twoSidedMarkedRenewalMeasure harrival]
    _ = Measure.map
        (negativeTimeCausalWorkload serviceRate ∘ directNegativeTimeHistory)
          (twoSidedMarkedRenewalMeasure arrivalRate) := by
          rw [Measure.map_map (measurable_negativeTimeCausalWorkload serviceRate)
            measurable_directNegativeTimeHistory]
    _ = Measure.map (directTimeCausalWorkload serviceRate)
          (twoSidedMarkedRenewalMeasure arrivalRate) := by
          rfl
    _ = mm1PreArrivalWorkloadLaw arrivalRate serviceRate :=
      (directTimeCausalWorkload_hasLaw harrival hstable).map_eq

/-- A stable negative-time M/M/1 causal workload has an integrable square. -/
theorem integrable_sq_negativeTimeCausalWorkload
    {arrivalRate serviceRate : ℝ}
    (harrival : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    Integrable (fun h : NegativeTimeHistory =>
      (negativeTimeCausalWorkload serviceRate h) ^ 2)
      (negativeTimeHistoryMeasure arrivalRate) := by
  let workload : NegativeTimeHistory → ℝ :=
    negativeTimeCausalWorkload serviceRate
  have hmeasure : Measure.map workload (negativeTimeHistoryMeasure arrivalRate) =
      mm1PreArrivalWorkloadLaw arrivalRate serviceRate := by
    simpa [workload] using
      map_negativeTimeCausalWorkload_eq_mm1PreArrivalWorkloadLaw harrival hstable
  have hsquare : Integrable (fun w : ℝ => w ^ 2)
      (Measure.map workload (negativeTimeHistoryMeasure arrivalRate)) := by
    rw [hmeasure]
    exact integrable_sq_mm1PreArrivalWorkloadLaw hstable
  have hmeas : AEMeasurable workload (negativeTimeHistoryMeasure arrivalRate) :=
    (measurable_negativeTimeCausalWorkload serviceRate).aemeasurable
  simpa [workload, Function.comp_apply] using
    (integrable_map_measure (measurable_id.aestronglyMeasurable.pow 2) hmeas).mp hsquare

end MM1DirectCausal

end

end AppliedModelingLib.Queueing

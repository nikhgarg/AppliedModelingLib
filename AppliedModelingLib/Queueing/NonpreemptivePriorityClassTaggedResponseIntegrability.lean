import AppliedModelingLib.Foundations.Probability.ResponseTailIntegrability
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastCapacitySplit
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFixedReplayMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedResponseTail
import AppliedModelingLib.Queueing.StationaryPriorityInputMGF

/-!
# Integrability of a selected priority response

This module combines the deterministic response-tail split with the exact
fixed-horizon marked-Poisson input transform.  The theorem is parameterized by
an explicit allocation of a future-work threshold across classes; a separate
real-analysis construction supplies such parameters from strict total load.
-/

namespace AppliedModelingLib.Queueing

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The literal selected-Palm nonpreemptive-priority response has a finite
first moment whenever its future-input Chernoff exponents are all strictly
negative.  The hypotheses expose a concrete threshold allocation and tilt,
rather than assuming integrability of the response. -/
theorem integrable_stationaryPriorityClassTaggedResponseTime_of_exponential_tail_parameters
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (futureShare tilt : ℝ) (classThresholdRate : Fin n → ℝ)
    (hfutureShare_lt_one : futureShare < 1)
    (hthresholdSum : ∑ j, classThresholdRate j ≤ futureShare)
    (htilt_nonnegative : 0 ≤ tilt)
    (htilt : ∀ j, tilt * meanService j < 1)
    (hexponent : ∀ j, -tilt * classThresholdRate j + arrivalRate j *
      (1 / (1 - tilt * meanService j) - 1) < 0) :
    Integrable (stationaryPriorityClassTaggedResponseTime meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hcard : 0 < Fintype.card (Fin n) := by simpa using hn
  have hresponse_nonnegative : ∀ᵐ z ∂μ,
      0 ≤ stationaryPriorityClassTaggedResponseTime meanService i z := by
    filter_upwards [
      ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i,
      ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
        arrivalRate meanService harrivalRate hmeanService i] with z hwait hservice
    unfold stationaryPriorityClassTaggedQueueWait at hwait
    have : 0 < stationaryPriorityClassTaggedWorkRequirement meanService i z := by
      simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hservice i 0
    linarith
  have hinitial_nonnegative : ∀ᵐ z ∂μ,
      0 ≤ stationaryPriorityClassTaggedArrivalTotalWork meanService i z := by
    filter_upwards [ae_positive_stationaryPriorityClassTaggedArrivalTotalWork
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hz
    exact hz.le
  apply Probability.integrable_of_ae_nonnegative_of_exponential_tail_split μ
    (stationaryPriorityClassTaggedResponseTime meanService i)
    (stationaryPriorityClassTaggedArrivalTotalWork meanService i)
    (aemeasurable_stationaryPriorityClassTaggedResponseTime
      arrivalRate meanService harrivalRate hmeanService hstable i)
    hresponse_nonnegative
    (MM1DirectCausal.integrable_stationaryPriorityClassTaggedArrivalTotalWork_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable i)
    hinitial_nonnegative
    (by linarith : 0 < 1 - futureShare)
    (fun j => -tilt * classThresholdRate j + arrivalRate j *
      (1 / (1 - tilt * meanService j) - 1))
    hexponent
  intro t ht
  have hsplit := ae_stationaryPriorityClassTaggedResponseTime_lt_imp_arrivalWork_or_futureWork
    arrivalRate meanService harrivalRate hmeanService hstable i t futureShare ht.le
  let responseTail : Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
    {z | t < stationaryPriorityClassTaggedResponseTime meanService i z}
  let arrivalTail : Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
    {z | (1 - futureShare) * t ≤
      stationaryPriorityClassTaggedArrivalTotalWork meanService i z}
  let futureTail : Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
    {z | futureShare * t ≤
      stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t}
  have hsubset : responseTail ≤ᵐ[μ] (arrivalTail ∪ futureTail : Set _) := by
    filter_upwards [hsplit] with z hz
    simpa [responseTail, arrivalTail, futureTail] using hz
  have hfutureRaw := measure_stationaryPriorityTaggedTotalFutureWork_ge_le_exponentialSum
    arrivalRate meanService harrivalRate i t futureShare tilt ht.le classThresholdRate
      hcard hthresholdSum htilt_nonnegative htilt
  have hfuture : μ futureTail ≤ ∑ j, ENNReal.ofReal (Real.exp
      ((-tilt * classThresholdRate j + arrivalRate j *
        (1 / (1 - tilt * meanService j) - 1)) * t)) := by
    simpa [μ, futureTail] using hfutureRaw
  calc
    μ {z | t < stationaryPriorityClassTaggedResponseTime meanService i z} ≤
        μ ({z | (1 - futureShare) * t ≤
          stationaryPriorityClassTaggedArrivalTotalWork meanService i z} ∪
          {z | futureShare * t ≤
            stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t}) :=
      by simpa [responseTail, arrivalTail, futureTail] using measure_mono_ae hsubset
    _ ≤ μ {z | (1 - futureShare) * t ≤
          stationaryPriorityClassTaggedArrivalTotalWork meanService i z} +
        μ {z | futureShare * t ≤
          stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} :=
      measure_union_le _ _
    _ ≤ μ {z | (1 - futureShare) * t ≤
          stationaryPriorityClassTaggedArrivalTotalWork meanService i z} +
        ∑ j, ENNReal.ofReal (Real.exp
          ((-tilt * classThresholdRate j + arrivalRate j *
            (1 / (1 - tilt * meanService j) - 1)) * t)) := by
      simpa [arrivalTail, futureTail, add_comm] using
        add_le_add_left hfuture (μ arrivalTail)

/-- A small exponential tilt has a strictly negative compound-Poisson
Chernoff exponent when the threshold exceeds the corresponding traffic load
by a positive margin. -/
theorem exponential_chernoff_exponent_neg_of_load_margin
    {arrival mean tilt margin : ℝ}
    (hmean : 0 < mean)
    (hload_lt_one : arrival * mean < 1)
    (hmargin : 0 < margin) (hmargin_lt_one : margin < 1)
    (htilt : 0 < tilt) (hsmall : tilt * mean ≤ margin / 4) :
    -tilt * (arrival * mean + margin) + arrival *
      (1 / (1 - tilt * mean) - 1) < 0 := by
  let x := tilt * mean
  have hxnonneg : 0 ≤ x := by
    exact mul_nonneg htilt.le hmean.le
  have hx_margin : x < margin * (1 - x) := by
    dsimp [x]
    nlinarith [sq_nonneg margin]
  have hload_mul : arrival * mean * x ≤ x := by
    simpa using mul_le_mul_of_nonneg_right hload_lt_one.le hxnonneg
  have hproduct : arrival * mean * x < margin * (1 - x) :=
    hload_mul.trans_lt hx_margin
  have hden : 0 < 1 - x := by
    nlinarith
  have hquot : arrival * mean * x / (1 - x) < margin := by
    exact (div_lt_iff₀ hden).2 hproduct
  have hratio : 1 / (1 - tilt * mean) - 1 = x / (1 - x) := by
    change 1 / (1 - x) - 1 = x / (1 - x)
    field_simp [ne_of_gt hden]
    ring
  have hsplit : arrival * mean / (1 - x) =
      arrival * mean + arrival * mean * x / (1 - x) := by
    field_simp [ne_of_gt hden]
    ring
  have hinter : -(arrival * mean + margin) + arrival * mean / (1 - x) < 0 := by
    rw [hsplit]
    linarith
  rw [hratio]
  calc
    -tilt * (arrival * mean + margin) + arrival * (x / (1 - x)) =
        tilt * (-(arrival * mean + margin) + arrival * mean / (1 - x)) := by
      dsimp [x]
      ring
    _ < 0 := mul_neg_of_pos_of_neg htilt hinter

/-- Strict total load admits a future-work threshold allocation and an
exponential tilt for which every literal selected-Palm input Chernoff bound
decays exponentially. -/
theorem exists_stationaryPriorityClassTaggedResponseTailParameters_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∃ futureShare tilt : ℝ, ∃ classThresholdRate : Fin n → ℝ,
      futureShare < 1 ∧
      (∑ j, classThresholdRate j) ≤ futureShare ∧
      0 ≤ tilt ∧
      (∀ j, tilt * meanService j < 1) ∧
      ∀ j, -tilt * classThresholdRate j + arrivalRate j *
        (1 / (1 - tilt * meanService j) - 1) < 0 := by
  let ρ : ℝ := ∑ j, arrivalRate j * meanService j
  let margin : ℝ := (1 - ρ) / (4 * (n : ℝ))
  let totalMean : ℝ := ∑ j, meanService j
  let scale : ℝ := 1 + totalMean
  have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hone_n : 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hnNat)
  have htotalMean_nonneg : 0 ≤ totalMean := by
    dsimp [totalMean]
    exact Finset.sum_nonneg fun j _ => (hmeanService j).le
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (harrivalRate j).le (hmeanService j).le
  have hρ_lt_one : ρ < 1 := by simpa [ρ] using hstable
  have hgap : 0 < 1 - ρ := by linarith
  have hfour_n : 0 < 4 * (n : ℝ) := by positivity
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact div_pos hgap hfour_n
  have hmargin_lt_one : margin < 1 := by
    dsimp [margin]
    apply (div_lt_iff₀ hfour_n).2
    nlinarith [hone_n]
  have hdouble : 2 * (n : ℝ) * margin = (1 - ρ) / 2 := by
    dsimp [margin]
    field_simp [ne_of_gt hn]
    ring
  have hscale : 0 < scale := by
    dsimp [scale]
    linarith
  have htilt : 0 < margin / (4 * scale) := by
    exact div_pos hmargin (by positivity)
  have hmean_le_total : ∀ j, meanService j ≤ totalMean := by
    intro j
    dsimp [totalMean]
    exact Finset.single_le_sum (fun k _ => (hmeanService k).le) (Finset.mem_univ j)
  have hsmall : ∀ j, (margin / (4 * scale)) * meanService j ≤ margin / 4 := by
    intro j
    have hmean_le_scale : meanService j ≤ scale := by
      dsimp [scale]
      linarith [hmean_le_total j]
    have hratio : meanService j / scale ≤ 1 := by
      apply (div_le_iff₀ hscale).2
      nlinarith
    calc
      (margin / (4 * scale)) * meanService j =
          (margin / 4) * (meanService j / scale) := by
        field_simp [ne_of_gt hscale]
      _ ≤ (margin / 4) * 1 := by
        exact mul_le_mul_of_nonneg_left hratio (by linarith [hmargin])
      _ = margin / 4 := by ring
  refine ⟨ρ + 2 * (n : ℝ) * margin, margin / (4 * scale),
    fun j => arrivalRate j * meanService j + margin, ?_, ?_, htilt.le, ?_, ?_⟩
  · rw [hdouble]
    linarith
  · rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa [ρ] using (show ρ + (n : ℝ) * margin ≤
        ρ + 2 * (n : ℝ) * margin by nlinarith)
  · intro j
    exact (hsmall j).trans_lt (by nlinarith [hmargin_lt_one])
  · intro j
    have hload_le : arrivalRate j * meanService j ≤ ρ := by
      dsimp [ρ]
      exact Finset.single_le_sum (fun k _ =>
        mul_nonneg (harrivalRate k).le (hmeanService k).le) (Finset.mem_univ j)
    apply exponential_chernoff_exponent_neg_of_load_margin (hmeanService j)
      (hload_le.trans_lt hρ_lt_one) hmargin hmargin_lt_one htilt
    exact hsmall j

/-- Under strict total load, the literal selected-Palm response in the
nonpreemptive-priority queue has a finite first moment. -/
theorem integrable_stationaryPriorityClassTaggedResponseTime_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    Integrable (stationaryPriorityClassTaggedResponseTime meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  rcases exists_stationaryPriorityClassTaggedResponseTailParameters_of_totalStable
    arrivalRate meanService harrivalRate hmeanService hstable i with
      ⟨futureShare, tilt, classThresholdRate, hfutureShare, hthresholdSum,
        htilt_nonnegative, htilt, hexponent⟩
  exact integrable_stationaryPriorityClassTaggedResponseTime_of_exponential_tail_parameters
    arrivalRate meanService harrivalRate hmeanService hstable i futureShare tilt
      classThresholdRate hfutureShare hthresholdSum htilt_nonnegative htilt hexponent

/-- Under strict total load, the literal selected-Palm queue-wait observable
also has a finite first moment. -/
theorem integrable_stationaryPriorityClassTaggedQueueWait_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    Integrable (stationaryPriorityClassTaggedQueueWait meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  exact integrable_stationaryPriorityClassTaggedQueueWait_of_response
    arrivalRate meanService harrivalRate hmeanService i
    (integrable_stationaryPriorityClassTaggedResponseTime_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable i)

/-- The selected-Palm mean queue wait is the mean physical response minus the
mean tagged service requirement under strict total load. -/
theorem integral_stationaryPriorityClassTaggedQueueWait_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∫ z, stationaryPriorityClassTaggedResponseTime meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) -
        meanService i := by
  exact integral_stationaryPriorityClassTaggedQueueWait_of_response
    arrivalRate meanService harrivalRate hmeanService i
    (integrable_stationaryPriorityClassTaggedResponseTime_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable i)

end

end AppliedModelingLib.Queueing

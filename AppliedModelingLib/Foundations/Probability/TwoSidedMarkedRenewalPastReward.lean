import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalReward
import Mathlib.Tactic

/-!
# Past-half marked two-sided renewal-reward strong laws

This module records the source-input laws for the negative-index half of a
two-sided marked renewal path.  The past index convention is literal:
`Int.negSucc n` is the job immediately before the tag when `n = 0`, then the
next older job when `n = 1`, and so on.  Consequently, elapsed time is stored
as a positive magnitude from the tagged epoch back to that past job.

It does not construct a queue, a reset, a Palm response, or a stationary
workload.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory

noncomputable section

/-- The `n`th past interarrival gap, where `n = 0` means integer index `-1`. -/
def markedRenewalPastGap (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  twoSidedGap (Int.negSucc n) z.1

/-- The work mark of the literal past job at integer index `Int.negSucc n`. -/
def markedRenewalPastWork (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  twoSidedGap (Int.negSucc n) z.2

/--
The positive elapsed-time magnitude from the tagged epoch to the `n`th past
arrival.  It sums the exact past gaps with indices `0, ..., n`.
-/
def markedRenewalPastElapsedTime (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), markedRenewalPastGap z j

/-- Cumulative work of literal past jobs with indices `Int.negSucc 0, ..., Int.negSucc n`. -/
def markedRenewalPastCumulativeWork (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), markedRenewalPastWork z j

/--
Cumulative past work minus service capacity times positive elapsed past time.
This is indexed outward from the tag, so it is a source-input net increment,
not a forward queue workload evolution.
-/
def markedRenewalPastCumulativeNetWork (capacity : ℝ)
    (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (markedRenewalPastWork z j - capacity * markedRenewalPastGap z j)

theorem markedRenewalPastElapsedTime_eq_candidatePastGapSum
    (z : TwoSidedMarkedRenewalSample) (n : ℕ) :
    markedRenewalPastElapsedTime z n = candidatePastGapSum z.1 (n + 1) := by
  rfl

theorem markedRenewalPastCumulativeNetWork_div_nat_succ_eq
    (capacity : ℝ) (z : TwoSidedMarkedRenewalSample) (n : ℕ) :
    markedRenewalPastCumulativeNetWork capacity z n / ((n + 1 : ℕ) : ℝ) =
      markedRenewalPastCumulativeWork z n / ((n + 1 : ℕ) : ℝ) -
        capacity * (markedRenewalPastElapsedTime z n / ((n + 1 : ℕ) : ℝ)) := by
  simp only [markedRenewalPastCumulativeNetWork, markedRenewalPastCumulativeWork,
    markedRenewalPastElapsedTime, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

/-- The empirical mean of literal past work marks is one almost surely. -/
theorem ae_tendsto_markedRenewalPastCumulativeWork_div_nat_succ
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ => markedRenewalPastCumulativeWork z n / ((n + 1 : ℕ) : ℝ))
        atTop (nhds 1) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure 1) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  refine ae_of_ae_map
    (μ := (twoSidedInterarrivalMeasure rate).prod (twoSidedInterarrivalMeasure 1))
    (f := Prod.snd) (p := fun work : ℤ → ℝ =>
      Tendsto
        (fun n : ℕ =>
          (∑ j ∈ Finset.range (n + 1), twoSidedGap (Int.negSucc j) work) /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds 1))
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hmap : ∀ᵐ path ∂Measure.map candidatePastGapPath
      (twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto
        (fun n : ℕ => arrivalTime n path / ((n + 1 : ℕ) : ℝ))
        atTop (nhds 1) := by
    rw [(candidatePastGapPath_hasLaw (rate := (1 : ℝ)) (by norm_num)).map_eq]
    simpa using ae_tendsto_arrivalTime_div_nat_succ (rate := (1 : ℝ)) (by norm_num)
  have hpast := Measure.tendsto_ae_map
    (candidatePastGapPath_hasLaw (rate := (1 : ℝ)) (by norm_num)).aemeasurable hmap
  filter_upwards [hpast] with work hwork
  simpa [arrivalTime, candidatePastGapPath, interarrival] using hwork

/-- The empirical mean of positive elapsed time along literal past gaps is `1 / rate` almost surely. -/
theorem ae_tendsto_markedRenewalPastElapsedTime_div_nat_succ
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ => markedRenewalPastElapsedTime z n / ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure 1) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  refine ae_of_ae_map
    (μ := (twoSidedInterarrivalMeasure rate).prod (twoSidedInterarrivalMeasure 1))
    (f := Prod.fst) (p := fun gap : ℤ → ℝ =>
      Tendsto
        (fun n : ℕ =>
          (∑ j ∈ Finset.range (n + 1), twoSidedGap (Int.negSucc j) gap) /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)))
    measurable_fst.aemeasurable ?_
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmap : ∀ᵐ path ∂Measure.map candidatePastGapPath
      (twoSidedInterarrivalMeasure rate),
      Tendsto
        (fun n : ℕ => arrivalTime n path / ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)) := by
    rw [(candidatePastGapPath_hasLaw hrate).map_eq]
    exact ae_tendsto_arrivalTime_div_nat_succ hrate
  have hpast := Measure.tendsto_ae_map
    (candidatePastGapPath_hasLaw hrate).aemeasurable hmap
  filter_upwards [hpast] with gap hgap
  simpa [arrivalTime, candidatePastGapPath, interarrival] using hgap

/-- Past cumulative work divided by its positive elapsed time converges almost surely to `rate`. -/
theorem ae_tendsto_markedRenewalPastWork_div_elapsedTime
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ =>
          markedRenewalPastCumulativeWork z n / markedRenewalPastElapsedTime z n)
        atTop (nhds rate) := by
  have hwork := ae_tendsto_markedRenewalPastCumulativeWork_div_nat_succ hrate
  have hgap := ae_tendsto_markedRenewalPastElapsedTime_div_nat_succ hrate
  have hgap_ne : (1 / rate : ℝ) ≠ 0 := by
    exact one_div_ne_zero (ne_of_gt hrate)
  filter_upwards [hwork, hgap] with z hwork_z hgap_z
  have hratio := AppliedModelingLib.tendsto_div_of_tendsto_of_ne hwork_z hgap_z hgap_ne
  have hlimit : (1 / (1 / rate) : ℝ) = rate := by
    rw [one_div_div]
    simp
  rw [hlimit] at hratio
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n hn
  have hnat_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hnat_ne]

/-- The empirical past net input per literal past arrival has drift `1 - capacity / rate`. -/
theorem ae_tendsto_markedRenewalPastCumulativeNetWork_div_nat_succ
    {rate capacity : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ =>
          markedRenewalPastCumulativeNetWork capacity z n /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 - capacity / rate)) := by
  filter_upwards [ae_tendsto_markedRenewalPastCumulativeWork_div_nat_succ hrate,
    ae_tendsto_markedRenewalPastElapsedTime_div_nat_succ hrate] with z hwork hgap
  rw [show (fun n : ℕ =>
      markedRenewalPastCumulativeNetWork capacity z n / ((n + 1 : ℕ) : ℝ)) =
        fun n : ℕ =>
          markedRenewalPastCumulativeWork z n / ((n + 1 : ℕ) : ℝ) -
            capacity * (markedRenewalPastElapsedTime z n / ((n + 1 : ℕ) : ℝ)) by
      funext n
      exact markedRenewalPastCumulativeNetWork_div_nat_succ_eq capacity z n]
  simpa [div_eq_mul_inv] using hwork.sub (hgap.const_mul capacity)

end

end AppliedModelingLib.Probability.PoissonProcess

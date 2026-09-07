import AppliedModelingLib.Foundations.Probability.TwoSidedExponentialWorkStrongLaw
import AppliedModelingLib.Foundations.Probability.RenewalReward
import Mathlib.Tactic

/-!
# Marked two-sided renewal-reward strong laws

This module combines the two source-side laws retained by a tagged renewal
input: a two-sided exponential interarrival path of rate `rate`, and an
independent two-sided unit-exponential work-mark path.  It records only their
forward arrival-epoch empirical laws under the literal product measure.  In
particular, it does not construct a queue, a reset, a Palm response, or a
stationary workload.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory

noncomputable section

/-- A two-sided renewal path together with its independent unit-work path. -/
abbrev TwoSidedMarkedRenewalSample := (ℤ → ℝ) × (ℤ → ℝ)

/-- The literal product input law for a rate-`rate` marked renewal stream. -/
noncomputable def twoSidedMarkedRenewalMeasure (rate : ℝ) :
    Measure TwoSidedMarkedRenewalSample :=
  (twoSidedInterarrivalMeasure rate).prod (twoSidedInterarrivalMeasure 1)

/-- The nonnegative-index gap used by the forward tagged renewal half. -/
def markedRenewalFutureGap (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  candidateFutureGapPath z.1 n

/-- The iid unit-work mark paired with the `n`th forward gap. -/
def markedRenewalFutureWork (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  twoSidedGap (Int.ofNat n) z.2

/-- The epoch of the `n`th forward marked arrival, including indices `0, ..., n`. -/
def markedRenewalArrivalEpoch (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  arrivalTime n (candidateFutureGapPath z.1)

/-- Cumulative work of the first `n + 1` forward marked arrivals. -/
def markedRenewalCumulativeWork (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), markedRenewalFutureWork z j

/-- Cumulative work minus `capacity` times elapsed interarrival time. -/
def markedRenewalCumulativeNetWork (capacity : ℝ)
    (z : TwoSidedMarkedRenewalSample) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (markedRenewalFutureWork z j - capacity * markedRenewalFutureGap z j)

theorem markedRenewalArrivalEpoch_eq_sum
    (z : TwoSidedMarkedRenewalSample) (n : ℕ) :
    markedRenewalArrivalEpoch z n =
      ∑ j ∈ Finset.range (n + 1), markedRenewalFutureGap z j := by
  rfl

theorem markedRenewalCumulativeNetWork_div_nat_succ_eq
    (capacity : ℝ) (z : TwoSidedMarkedRenewalSample) (n : ℕ) :
    markedRenewalCumulativeNetWork capacity z n / ((n + 1 : ℕ) : ℝ) =
      markedRenewalCumulativeWork z n / ((n + 1 : ℕ) : ℝ) -
        capacity * (markedRenewalArrivalEpoch z n / ((n + 1 : ℕ) : ℝ)) := by
  rw [markedRenewalArrivalEpoch_eq_sum]
  simp only [markedRenewalCumulativeNetWork, markedRenewalCumulativeWork,
    Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

/-- The forward marked work empirical mean is one almost surely. -/
theorem ae_tendsto_markedRenewalCumulativeWork_div_nat_succ
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ => markedRenewalCumulativeWork z n / ((n + 1 : ℕ) : ℝ))
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
          (∑ j ∈ Finset.range (n + 1), twoSidedGap (Int.ofNat j) work) /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds 1))
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  exact ae_tendsto_twoSidedUnitExponentialFutureWorkMean

/-- The forward marked interarrival empirical mean is `1 / rate` almost surely. -/
theorem ae_tendsto_markedRenewalArrivalEpoch_div_nat_succ
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ => markedRenewalArrivalEpoch z n / ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure 1) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  refine ae_of_ae_map
    (μ := (twoSidedInterarrivalMeasure rate).prod (twoSidedInterarrivalMeasure 1))
    (f := Prod.fst) (p := fun gap : ℤ → ℝ =>
      Tendsto
        (fun n : ℕ => arrivalTime n (candidateFutureGapPath gap) /
          ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)))
    measurable_fst.aemeasurable ?_
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact ae_candidateFutureGapPath_arrivalTime_div_nat_succ_tendsto hrate

/--
At marked arrival epochs, cumulative unit work divided by elapsed interarrival
time converges almost surely to the arrival rate.  Both sums include indices
`0, ..., n`, so no unrecorded endpoint convention is used.
-/
theorem ae_tendsto_markedRenewalWork_div_arrivalEpoch
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ =>
          markedRenewalCumulativeWork z n / markedRenewalArrivalEpoch z n)
        atTop (nhds rate) := by
  have hwork := ae_tendsto_markedRenewalCumulativeWork_div_nat_succ hrate
  have hgap := ae_tendsto_markedRenewalArrivalEpoch_div_nat_succ hrate
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

/--
The empirical marked net input per arrival converges to its source drift
`1 - capacity / rate`.  This is a source-input law only; a negative value is
not by itself a queue reset or stationarity theorem.
-/
theorem ae_tendsto_markedRenewalCumulativeNetWork_div_nat_succ
    {rate capacity : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (fun n : ℕ =>
          markedRenewalCumulativeNetWork capacity z n /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 - capacity / rate)) := by
  filter_upwards [ae_tendsto_markedRenewalCumulativeWork_div_nat_succ hrate,
    ae_tendsto_markedRenewalArrivalEpoch_div_nat_succ hrate] with z hwork hgap
  rw [show (fun n : ℕ =>
      markedRenewalCumulativeNetWork capacity z n / ((n + 1 : ℕ) : ℝ)) =
        fun n : ℕ =>
          markedRenewalCumulativeWork z n / ((n + 1 : ℕ) : ℝ) -
            capacity * (markedRenewalArrivalEpoch z n / ((n + 1 : ℕ) : ℝ)) by
      funext n
      exact markedRenewalCumulativeNetWork_div_nat_succ_eq capacity z n]
  simpa [div_eq_mul_inv] using hwork.sub (hgap.const_mul capacity)

end

end AppliedModelingLib.Probability.PoissonProcess

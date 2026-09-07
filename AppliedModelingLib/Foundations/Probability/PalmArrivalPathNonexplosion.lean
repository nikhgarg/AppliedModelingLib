import AppliedModelingLib.Foundations.Probability.PalmArrivalPath
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalNonexplosion
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalStrongLaw

/-!
# Nonexplosion of the candidate two-sided Palm gap path

Both the future and past gap sequences of the candidate tagged path have the
canonical iid exponential renewal law.  Consequently, their finite-sum epochs
diverge almost surely in each direction.  This establishes local finiteness
of the candidate renewal halves, not a Campbell/Palm identity or stationary
Poisson increments for the two-sided point process.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-- The nonnegative-index gap sequence of the candidate two-sided Palm path. -/
def candidateFutureGapPath : (ℤ → ℝ) → ℕ → ℝ :=
  fun ω n => twoSidedGap (Int.ofNat n) ω

/-- The negative-index gap sequence of the candidate two-sided Palm path. -/
def candidatePastGapPath : (ℤ → ℝ) → ℕ → ℝ :=
  fun ω n => twoSidedGap (Int.negSucc n) ω

theorem iIndepFun_candidateFutureGapPath
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.iIndepFun (fun n ω => candidateFutureGapPath ω n)
      (twoSidedInterarrivalMeasure rate) := by
  simpa [candidateFutureGapPath] using
    (ProbabilityTheory.iIndepFun.precomp (g := Int.ofNat)
      (by
        intro a b hab
        exact Int.ofNat.inj hab)
      (iIndepFun_twoSidedGap hrate))

theorem candidateFutureGapPath_hasLaw
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw candidateFutureGapPath
      (exponentialInterarrivalMeasure rate) (twoSidedInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  refine ⟨(measurable_pi_iff.2 (fun n => measurable_twoSidedGap (Int.ofNat n))).aemeasurable, ?_⟩
  change Measure.map (fun ω n => twoSidedGap (Int.ofNat n) ω)
    (twoSidedInterarrivalMeasure rate) = exponentialInterarrivalMeasure rate
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun n => measurable_twoSidedGap (Int.ofNat n)) |>.mp
    (iIndepFun_candidateFutureGapPath hrate)]
  simp only [exponentialInterarrivalMeasure]
  congr 1
  funext n
  exact (twoSidedGap_hasLaw hrate (Int.ofNat n)).map_eq

theorem iIndepFun_candidatePastGapPath
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.iIndepFun (fun n ω => candidatePastGapPath ω n)
      (twoSidedInterarrivalMeasure rate) := by
  simpa [candidatePastGapPath] using
    (ProbabilityTheory.iIndepFun.precomp (g := Int.negSucc)
      (by
        intro a b hab
        exact Int.negSucc.inj hab)
      (iIndepFun_twoSidedGap hrate))

theorem candidatePastGapPath_hasLaw
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw candidatePastGapPath
      (exponentialInterarrivalMeasure rate) (twoSidedInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  refine ⟨(measurable_pi_iff.2 (fun n => measurable_twoSidedGap (Int.negSucc n))).aemeasurable, ?_⟩
  change Measure.map (fun ω n => twoSidedGap (Int.negSucc n) ω)
    (twoSidedInterarrivalMeasure rate) = exponentialInterarrivalMeasure rate
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun n => measurable_twoSidedGap (Int.negSucc n)) |>.mp
    (iIndepFun_candidatePastGapPath hrate)]
  simp only [exponentialInterarrivalMeasure]
  congr 1
  funext n
  exact (twoSidedGap_hasLaw hrate (Int.negSucc n)).map_eq

theorem candidateFutureEpoch_succ_eq_arrivalTime
    (n : ℕ) :
    (fun ω => candidateFutureEpoch ω (n + 1)) =
      fun ω => arrivalTime n (candidateFutureGapPath ω) := by
  funext ω
  simp [candidateFutureEpoch, arrivalTime, candidateFutureGapPath, interarrival]

/--
The positive-index half of the candidate two-sided tagged path has the
canonical renewal rate almost surely.  This transports only the source
interarrival law; it makes no queueing or stationarity claim.
-/
theorem ae_candidateFutureGapPath_arrivalTime_div_nat_succ_tendsto
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      Tendsto
        (fun n : ℕ => arrivalTime n (candidateFutureGapPath ω) /
          ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)) := by
  have hmap : ∀ᵐ ξ ∂Measure.map candidateFutureGapPath
      (twoSidedInterarrivalMeasure rate),
      Tendsto
        (fun n : ℕ => arrivalTime n ξ / ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)) := by
    rw [(candidateFutureGapPath_hasLaw hrate).map_eq]
    exact ae_tendsto_arrivalTime_div_nat_succ hrate
  exact Measure.tendsto_ae_map
    (candidateFutureGapPath_hasLaw hrate).aemeasurable hmap

/--
Equivalent future-epoch form of the positive-half renewal rate law.  The
index shift is explicit: epoch `n + 1` is the sum of its first `n + 1` gaps.
-/
theorem ae_candidateFutureEpoch_succ_div_nat_succ_tendsto
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      Tendsto
        (fun n : ℕ => candidateFutureEpoch ω (n + 1) /
          ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 / rate)) := by
  filter_upwards [ae_candidateFutureGapPath_arrivalTime_div_nat_succ_tendsto hrate]
    with ω hω
  simpa only [candidateFutureEpoch_succ_eq_arrivalTime] using hω

theorem candidatePastGapSum_succ_eq_arrivalTime
    (n : ℕ) :
    (fun ω => candidatePastGapSum ω (n + 1)) =
      fun ω => arrivalTime n (candidatePastGapPath ω) := by
  funext ω
  simp [candidatePastGapSum, arrivalTime, candidatePastGapPath, interarrival]

theorem ae_candidateFutureEpoch_succ_tendsto_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      Tendsto (fun n : ℕ => candidateFutureEpoch ω (n + 1)) atTop atTop := by
  have hmeas : MeasurableSet {ξ : ℕ → ℝ |
      Tendsto (fun n : ℕ => arrivalTime n ξ) atTop atTop} := by
    exact measurableSet_tendsto (l := atTop) (atTop : Filter ℝ)
      (fun n => measurable_arrivalTime n)
  have htail : ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      Tendsto (fun n : ℕ => arrivalTime n (candidateFutureGapPath ω)) atTop atTop :=
    by
      have hmap : ∀ᵐ ξ ∂Measure.map candidateFutureGapPath
          (twoSidedInterarrivalMeasure rate),
          Tendsto (fun n : ℕ => arrivalTime n ξ) atTop atTop := by
        rw [(candidateFutureGapPath_hasLaw hrate).map_eq]
        exact ae_arrivalTime_tendsto_atTop hrate
      exact (Measure.tendsto_ae_map
        (candidateFutureGapPath_hasLaw hrate).aemeasurable) hmap
  filter_upwards [htail] with ω hω
  simpa only [candidateFutureEpoch_succ_eq_arrivalTime] using hω

theorem ae_candidatePastGapSum_succ_tendsto_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      Tendsto (fun n : ℕ => candidatePastGapSum ω (n + 1)) atTop atTop := by
  have hmeas : MeasurableSet {ξ : ℕ → ℝ |
      Tendsto (fun n : ℕ => arrivalTime n ξ) atTop atTop} := by
    exact measurableSet_tendsto (l := atTop) (atTop : Filter ℝ)
      (fun n => measurable_arrivalTime n)
  have htail : ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      Tendsto (fun n : ℕ => arrivalTime n (candidatePastGapPath ω)) atTop atTop :=
    by
      have hmap : ∀ᵐ ξ ∂Measure.map candidatePastGapPath
          (twoSidedInterarrivalMeasure rate),
          Tendsto (fun n : ℕ => arrivalTime n ξ) atTop atTop := by
        rw [(candidatePastGapPath_hasLaw hrate).map_eq]
        exact ae_arrivalTime_tendsto_atTop hrate
      exact (Measure.tendsto_ae_map
        (candidatePastGapPath_hasLaw hrate).aemeasurable) hmap
  filter_upwards [htail] with ω hω
  simpa only [candidatePastGapSum_succ_eq_arrivalTime] using hω

end
end AppliedModelingLib.Probability.PoissonProcess

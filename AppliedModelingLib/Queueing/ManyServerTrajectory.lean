import AppliedModelingLib.Queueing.ManyServerUniformization
import AppliedModelingLib.Queueing.MM1.Trajectory.PoissonClock
import AppliedModelingLib.Queueing.MM1.Trajectory.FiniteDimensional
import Mathlib.Tactic

/-!
# Stationary trajectories for uniformized many-server queues

This module lifts the reversible many-server potential-event kernel to a
Mathlib Markov kernel and constructs its stationary embedded trajectory.  It
also gives fixed-time stationary marginals after an independent forward
Poisson time change.  Establishing the continuous-time semigroup and càdlàg
process properties is a separate result.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The discrete-time trajectory of the uniformized many-server queue started
from an arbitrary initial state law.  This is the embedded potential-event
chain; no stationarity assumption is made on `initial`. -/
noncomputable def manyServerUniformizedEmbeddedTrajectoryMeasure
    (initial : Measure ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) : Measure (ℕ → ℕ) :=
  stationaryTrajMeasure initial
    (countablePMFKernel (manyServerUniformizedKernel trafficIntensity servers hservers))

/-- The initial coordinate of the uniformized many-server embedded trajectory
has its specified initial law. -/
theorem manyServerUniformizedEmbeddedTrajectoryMeasure_zero_marginal
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    (manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).map (fun path => path 0) = initial := by
  exact stationaryTrajMeasure_zero_marginal

/-- At every deterministic embedded index, an arbitrary-initial-law
uniformized many-server trajectory has the corresponding iterated PMF law. -/
theorem manyServerUniformizedEmbeddedTrajectory_stateAt_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    HasLaw (fun path : ℕ → ℕ => path index)
      (initial.bind (CountableMarkovKernel.iterate
        (manyServerUniformizedKernel trafficIntensity servers hservers) index)).toMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers) := by
  have hpair := stationaryTrajMeasure_zero_n_pair_hasLaw
    (π := initial.toMeasure)
    (K := countablePMFKernel
      (manyServerUniformizedKernel trafficIntensity servers hservers)) index
  have hterminal : HasLaw Prod.snd
      (initial.bind (CountableMarkovKernel.iterate
        (manyServerUniformizedKernel trafficIntensity servers hservers) index)).toMeasure
      (initial.toMeasure ⊗ₘ ((countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ index)) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    letI : IsSFiniteKernel ((countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ index) :=
      isSFiniteKernel_pow _ index
    change (initial.toMeasure ⊗ₘ ((countablePMFKernel
      (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ index)).snd = _
    rw [Measure.snd_compProd,
      ← CountableMarkovKernel.countablePMFKernel_iterate_eq_pow,
      bind_countablePMFKernel_eq_pmf_bind_toMeasure]
  simpa [manyServerUniformizedEmbeddedTrajectoryMeasure, Function.comp_def] using
    hterminal.comp hpair

/-- Successive marginals of the uniformized many-server embedded trajectory
are related by its potential-event Markov kernel. -/
theorem manyServerUniformizedEmbeddedTrajectoryMeasure_succ_marginal
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) (step : ℕ) :
    (manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).map (fun path => path (step + 1)) =
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers)) ∘ₘ
        (manyServerUniformizedEmbeddedTrajectoryMeasure
          initial trafficIntensity servers hservers).map (fun path => path step) := by
  exact stationaryTrajMeasure_succ_marginal step

/-- The time-zero state of the independent-clock construction has the given
initial law. -/
theorem manyServerUniformizedTrajectoryAtForwardPoissonCount_zero_hasLaw
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    HasLaw
      (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H 0)
      initial
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod P) := by
  letI : IsProbabilityMeasure P := H.isProbability
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  refine ⟨?_, ?_⟩
  · exact (measurable_stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H 0).aemeasurable
  · have hzero : ∀ᵐ z : (ℕ → ℕ) × Ω ∂
        (manyServerUniformizedEmbeddedTrajectoryMeasure
          initial trafficIntensity servers hservers).prod P,
        H.count 0 z.2 = 0 := by
      refine ae_of_ae_map
        (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
          initial trafficIntensity servers hservers).prod P)
        (f := Prod.snd) (p := fun omega : Ω => H.count 0 omega = 0)
        measurable_snd.aemeasurable ?_
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact H.count_zero_ae
    calc
      Measure.map
          (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H 0)
          ((manyServerUniformizedEmbeddedTrajectoryMeasure
            initial trafficIntensity servers hservers).prod P) =
          Measure.map (fun z : (ℕ → ℕ) × Ω => z.1 0)
            ((manyServerUniformizedEmbeddedTrajectoryMeasure
              initial trafficIntensity servers hservers).prod P) := by
            apply Measure.map_congr
            filter_upwards [hzero] with z hzero
            simp [stationaryTrajectoryAtForwardPoissonCount, hzero]
      _ = Measure.map (fun path : ℕ → ℕ => path 0)
            (manyServerUniformizedEmbeddedTrajectoryMeasure
              initial trafficIntensity servers hservers) := by
            change Measure.map ((fun path : ℕ → ℕ => path 0) ∘ Prod.fst)
              ((manyServerUniformizedEmbeddedTrajectoryMeasure
                initial trafficIntensity servers hservers).prod P) = _
            rw [← Measure.map_map (measurable_pi_apply 0) measurable_fst,
              Measure.map_fst_prod, measure_univ, one_smul]
      _ = initial := manyServerUniformizedEmbeddedTrajectoryMeasure_zero_marginal
        trafficIntensity servers hservers

/-- The initial/current state pair of an arbitrary-initial-law uniformized
many-server trajectory at a forward-Poisson time is the explicit Poisson
mixture of the embedded-chain transition laws.  It is a fixed-time law only;
identifying a continuous-time semigroup and path regularity remains separate. -/
theorem manyServerUniformizedTrajectoryAtForwardPoissonCount_pair_mixture
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod P).map
        (fun z : (ℕ → ℕ) × Ω =>
          (z.1 0, stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t z)) s =
      ∫⁻ step, (initial ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ step)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t))) := by
  simpa [manyServerUniformizedEmbeddedTrajectoryMeasure,
    stationaryTrajectoryAtForwardPoissonCount] using
    (stationaryTrajMeasure_zero_forwardPoissonCount_pair_mixture
      (π := initial)
      (K := countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers)) H t s hs)

/-- The countable-kernel lift of the potential-event chain preserves the
many-server stationary PMF. -/
theorem manyServer_uniformized_kernelInvariant
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    Kernel.Invariant
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure :=
  (manyServerStationaryPMF_uniformized_stationary
    trafficIntensity servers hservers htraffic_lt_one).kernelInvariant

/-- Poissonizing the potential-event chain at any exposure preserves the
many-server stationary queue-length law. -/
theorem manyServer_uniformized_poissonizedKernelInvariant
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) (mean : ℝ≥0) :
    Kernel.Invariant
      (CountableMarkovKernel.poissonizedKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers) mean)
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure := by
  exact (manyServerStationaryPMF_uniformized_stationary
    trafficIntensity servers hservers htraffic_lt_one).poissonizedKernelInvariant mean

/-- Every member of the fixed-rate Poissonized potential-event semigroup
preserves the many-server stationary queue-length law. -/
theorem manyServer_uniformized_poissonizedKernelAtRateInvariant
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) (rate : ℝ) (hRate : 0 ≤ rate)
    (time : ℝ≥0) :
    Kernel.Invariant
      (CountableMarkovKernel.poissonizedKernelAtRate
        (manyServerUniformizedKernel trafficIntensity servers hservers) rate hRate time)
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure := by
  exact (manyServerStationaryPMF_uniformized_stationary
    trafficIntensity servers hservers htraffic_lt_one).poissonizedKernelAtRateInvariant
      rate hRate time

/-- Every coordinate of the stationary embedded trajectory has the normalized
many-server stationary PMF. -/
theorem manyServer_uniformized_stationaryTraj_marginal
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) (n : ℕ) :
    (stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).map
        (fun x => x n) =
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure := by
  exact stationaryTrajMeasure_marginal
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) n

/-- At deterministic embedded jump indices, the stationary many-server
uniformized trajectory has the exact `m`-step transition coupling.  This is a
discrete-time statement; mixing the two indices through independent Poisson
clock increments is a separate continuous-time bridge. -/
theorem manyServer_uniformized_stationaryTraj_pair_add
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) (n m : ℕ) :
    (stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).map
        (fun x => (x n, x (n + m))) =
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ m) := by
  exact stationaryTrajMeasure_pair_add
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) n m

/-- Three deterministic embedded potential-event coordinates of the
stationary many-server queue satisfy the Markov factorization through the
middle coordinate.  This is the discrete finite-dimensional component used
before an independent continuous-time clock is introduced. -/
theorem manyServer_uniformized_stationaryTraj_pair_add_succ_factor
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) (n m : ℕ) :
    (stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).map
        (fun x => ((x n, x (n + m)), x (n + m + 1))) =
      ((manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ m)) ⊗ₘ
        (countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)).prodMkLeft ℕ := by
  exact stationaryTrajMeasure_pair_add_succ_factor
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) n m

/-- At any three deterministic potential-event indices, the stationary
many-server embedded trajectory has the two successive kernel-power factors
of its homogeneous Markov law. -/
theorem manyServer_uniformized_stationaryTraj_triple_add_add
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) (n m l : ℕ) :
    (stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).map
        (fun x => ((x n, x (n + m)), x (n + m + l))) =
      ((manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ m)) ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ l).prodMkLeft ℕ := by
  exact stationaryTrajMeasure_triple_add_add
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) n m l

/-- A stationary embedded trajectory evaluated at an independent forward
Poisson count retains its stationary state law at each deterministic time. -/
theorem manyServer_uniformized_stationaryTraj_eval_forwardPoissonCount_hasLaw
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t)
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      ((stationaryTrajMeasure
        (manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
        (countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers))).prod P) := by
  exact stationaryTrajMeasure_eval_forwardPoissonCount_hasLaw
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) H t

/-- At two ordered deterministic times, the stationary uniformized many-server
queue has the exact Poisson mixture of embedded `m`-step transition couplings
over the intervening potential-event count. This is a finite-dimensional
product-space law, not yet a full continuous-time semigroup or path-space
construction. -/
theorem manyServer_uniformized_stationaryTraj_forwardPoissonCount_pair_mixture
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {sTime tTime : ℝ≥0} (hst : sTime ≤ tTime)
    (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).prod P).map
        (fun z : (ℕ → ℕ) × Ω =>
          (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H sTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H tTime z)) s =
      ∫⁻ m, (
        (manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ m)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))) := by
  exact stationaryTrajMeasure_forwardPoissonCount_pair_mixture
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) H hst s hs

/-- At three ordered deterministic times, the stationary many-server
uniformized queue has the explicit two-increment Poisson mixture of its
embedded transition powers. -/
theorem manyServer_uniformized_stationaryTraj_forwardPoissonCount_triple_mixture
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {rTime sTime tTime : ℝ≥0} (hrs : rTime ≤ sTime) (hst : sTime ≤ tTime)
    (s : Set ((ℕ × ℕ) × ℕ)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).prod P).map
        (fun z : (ℕ → ℕ) × Ω =>
          ((stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H rTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H sTime z),
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H tTime z)) s =
      ∫⁻ q : ℕ × ℕ,
        (((manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
          ((countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ q.1)) ⊗ₘ
          ((countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ q.2).prodMkLeft ℕ) s ∂
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((sTime : ℝ) - (rTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrs))))).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) := by
  exact stationaryTrajMeasure_forwardPoissonCount_triple_mixture
    (manyServer_uniformized_kernelInvariant
      trafficIntensity servers hservers htraffic_lt_one) H hrs hst s hs

/-- The total potential-event rate associated with a many-server
uniformization. -/
noncomputable def manyServerUniformizationRate
    (trafficIntensity serviceRate : ℝ) (servers : ℕ) : ℝ :=
  (servers : ℝ) * serviceRate * (1 + trafficIntensity)

/-- If the offered load is at most one, the total potential-event rate is at
most twice the full-capacity service rate. -/
theorem manyServerUniformizationRate_le_two_mul_servers_mul_serviceRate
    (trafficIntensity serviceRate : ℝ) (servers : ℕ)
    (htraffic_le_one : trafficIntensity ≤ 1) (hservice_nonneg : 0 ≤ serviceRate) :
    manyServerUniformizationRate trafficIntensity serviceRate servers ≤
      2 * (servers : ℝ) * serviceRate := by
  unfold manyServerUniformizationRate
  have hfactor_nonneg : 0 ≤ (servers : ℝ) * serviceRate := by positivity
  have hsum : 1 + trafficIntensity ≤ 2 := by linarith
  calc
    (servers : ℝ) * serviceRate * (1 + trafficIntensity) ≤
        (servers : ℝ) * serviceRate * 2 :=
      mul_le_mul_of_nonneg_left hsum hfactor_nonneg
    _ = 2 * (servers : ℝ) * serviceRate := by ring

/-- For a subcritical many-server uniformization, the chance-bound clock term
at a positive integer multiple of the server count is controlled uniformly by
the reciprocal multiplier. -/
theorem manyServerUniformizationClockOverflow_le
    (trafficIntensity serviceRate horizon : ℝ) (servers cutoffMultiplier : ℕ)
    (htraffic_le_one : trafficIntensity ≤ 1) (hservice_nonneg : 0 ≤ serviceRate)
    (hhorizon_nonneg : 0 ≤ horizon) (hservers : 0 < servers)
    (hcutoffMultiplier : 0 < cutoffMultiplier) :
    (manyServerUniformizationRate trafficIntensity serviceRate servers * horizon) /
        ((cutoffMultiplier * servers + 1 : ℕ) : ℝ) ≤
      2 * serviceRate * horizon / (cutoffMultiplier : ℝ) := by
  have hrate := manyServerUniformizationRate_le_two_mul_servers_mul_serviceRate
    trafficIntensity serviceRate servers htraffic_le_one hservice_nonneg
  have hrate_horizon :
      manyServerUniformizationRate trafficIntensity serviceRate servers * horizon ≤
        (2 * (servers : ℝ) * serviceRate) * horizon :=
    mul_le_mul_of_nonneg_right hrate hhorizon_nonneg
  have hmult_pos : 0 < (cutoffMultiplier : ℝ) := by exact_mod_cast hcutoffMultiplier
  have hden_pos : 0 < ((cutoffMultiplier * servers + 1 : ℕ) : ℝ) := by positivity
  have hcoefficient_nonneg : 0 ≤ 2 * serviceRate * horizon / (cutoffMultiplier : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) hservice_nonneg) hhorizon_nonneg)
      hmult_pos.le
  apply (div_le_iff₀ hden_pos).mpr
  calc
    manyServerUniformizationRate trafficIntensity serviceRate servers * horizon ≤
        (2 * (servers : ℝ) * serviceRate) * horizon := hrate_horizon
    _ = (2 * serviceRate * horizon / (cutoffMultiplier : ℝ)) *
        ((cutoffMultiplier : ℝ) * (servers : ℝ)) := by
          field_simp [hmult_pos.ne']
    _ ≤ (2 * serviceRate * horizon / (cutoffMultiplier : ℝ)) *
        ((cutoffMultiplier * servers + 1 : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hcoefficient_nonneg
          norm_num [Nat.cast_add, Nat.cast_mul]

/-- Multiplying the birth selection probability by the potential-event rate
recovers the many-server arrival rate. -/
theorem manyServerUniformizationRate_birth
    (trafficIntensity serviceRate : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) :
    manyServerUniformizationRate trafficIntensity serviceRate servers *
      (trafficIntensity / (1 + trafficIntensity)) =
    (servers : ℝ) * trafficIntensity * serviceRate := by
  unfold manyServerUniformizationRate
  have hdenom_ne : 1 + trafficIntensity ≠ 0 := by linarith
  field_simp [hdenom_ne]

/-- Multiplying the non-arrival selection probability by the potential-event
rate recovers the aggregate potential-service-clock rate. -/
theorem manyServerUniformizationRate_potentialService
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ) :
    manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
    (servers : ℝ) * serviceRate := by
  rw [uniformizedDeathProbability_eq]
  unfold manyServerUniformizationRate
  change ((servers : ℝ) * serviceRate * (1 + (trafficIntensity : ℝ))) *
      (1 / (1 + (trafficIntensity : ℝ))) =
    (servers : ℝ) * serviceRate
  have hdenom_ne : 1 + (trafficIntensity : ℝ) ≠ 0 := by positivity
  field_simp [hdenom_ne]

/-- Multiplying a busy-service selection probability by the potential-event
rate recovers the state-dependent total departure rate. -/
theorem manyServerUniformizationRate_death
    (trafficIntensity serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (htraffic_nonneg : 0 ≤ trafficIntensity) :
    manyServerUniformizationRate trafficIntensity serviceRate servers *
      ((1 / (1 + trafficIntensity)) *
        ((Nat.min state servers : ℝ) / servers)) =
    serviceRate * (Nat.min state servers : ℝ) := by
  unfold manyServerUniformizationRate
  have hservers_ne : (servers : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hservers
  have hdenom_ne : 1 + trafficIntensity ≠ 0 := by linarith
  field_simp [hservers_ne, hdenom_ne]

/-- The upward transition intensity of the Poissonized potential-event kernel
is the upward rate of the associated many-server birth--death family. -/
theorem manyServerUniformizedKernel_birth_intensity
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) :
    manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
      (manyServerUniformizedKernel trafficIntensity servers hservers state (state + 1)).toReal =
    (manyServerBirthDeathRates
      ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) serviceRate servers).birth state := by
  rw [manyServerUniformizedKernel_birth]
  change manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
      (uniformizedBirthProbability trafficIntensity : ℝ) =
    (servers : ℝ) * (trafficIntensity : ℝ) * serviceRate
  rw [show (uniformizedBirthProbability trafficIntensity : ℝ) =
      (trafficIntensity : ℝ) / (1 + (trafficIntensity : ℝ)) by
    simp [uniformizedBirthProbability]]
  exact manyServerUniformizationRate_birth
    (trafficIntensity : ℝ) serviceRate servers (by positivity)

/-- The downward transition intensity of the Poissonized potential-event
kernel is the downward rate of the associated many-server birth--death
family. -/
theorem manyServerUniformizedKernel_death_intensity
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) :
    manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
      (manyServerUniformizedKernel trafficIntensity servers hservers (state + 1) state).toReal =
    (manyServerBirthDeathRates
      ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) serviceRate servers).death
        (state + 1) := by
  rw [manyServerUniformizedKernel_death]
  change manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
      (((1 - uniformizedBirthProbability trafficIntensity) *
        manyServerBusyFraction servers (state + 1) : ℝ≥0) : ℝ) =
    serviceRate * (Nat.min (state + 1) servers : ℝ)
  rw [uniformizedDeathProbability_eq]
  change manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
      ((1 / (1 + (trafficIntensity : ℝ))) *
        ((Nat.min (state + 1) servers : ℝ) / servers)) =
    serviceRate * (Nat.min (state + 1) servers : ℝ)
  exact manyServerUniformizationRate_death
    (trafficIntensity : ℝ) serviceRate servers (state + 1) hservers (by positivity)

end AppliedModelingLib.Probability.Queueing

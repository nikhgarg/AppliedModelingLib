import AppliedModelingLib.Foundations.Probability.ForwardPoisson
import AppliedModelingLib.Queueing.MM1.Trajectory.TimeChange

/-!
# External forward-Poisson time changes of stationary embedded trajectories

This construction puts an invariant embedded Markov trajectory and an
external forward Poisson count path on a product probability space.  At each
fixed time the time-changed state has the invariant marginal, and its
initial/current pair is an explicit Poisson mixture of embedded transition
laws.  These are only product-space fixed-time statements: they do not
identify a CTMC semigroup, prove càdlàg paths, or construct a Palm law.  In
particular, the joint fixed-time laws below do not identify actual marked
arrival or potential-service clocks, prove marked thinning, establish PASTA,
or select a stationary/Palm-tagged arrival.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Evaluate an embedded trajectory at the count of an external forward
Poisson clock.  The product space makes the clock independent of the
trajectory by construction. -/
def stationaryTrajectoryAtForwardPoissonCount
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) : ((ℕ → α) × Ω) → α :=
  fun z => z.1 (H.count t z.2)

theorem measurable_stationaryTrajectoryAtForwardPoissonCount
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    Measurable (stationaryTrajectoryAtForwardPoissonCount (α := α) H t) := by
  simpa [stationaryTrajectoryAtForwardPoissonCount] using
    measurable_trajectoryAtIndependentRandomIndex (α := α)
      (H.count t) (H.measurable_count t)

/-- Fixed-time marginal law for an invariant embedded chain independently
time-changed by a forward Poisson counting path.  This does not assert the
continuous-time Markov semigroup or a Palm construction. -/
theorem stationaryTrajMeasure_eval_forwardPoissonCount_hasLaw
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw (stationaryTrajectoryAtForwardPoissonCount (α := α) H t) π
      ((stationaryTrajMeasure π K).prod P) := by
  letI : IsProbabilityMeasure P := H.isProbability
  simpa [stationaryTrajectoryAtForwardPoissonCount] using
    stationaryTrajMeasure_eval_independentRandomIndex_hasLaw
      hstationary (H.count t) (H.measurable_count t)

/-- At a fixed deterministic time, an invariant embedded state evaluated at
an external forward-Poisson count is jointly independent of that count.  This
uses the product-space external clock only; it does not identify a CTMC,
marked arrival/service thinning, PASTA, or a Palm-tagged arrival. -/
theorem stationaryTrajMeasure_eval_forwardPoissonCount_joint_hasLaw
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → α) × Ω =>
        (stationaryTrajectoryAtForwardPoissonCount (α := α) H t z, H.count t z.2))
      (π.prod (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam H.rate (t : ℝ)
          (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))))
      ((stationaryTrajMeasure π K).prod P) := by
  letI : IsProbabilityMeasure P := H.isProbability
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  let h := stationaryTrajMeasure_eval_independentRandomIndex_joint_hasLaw
    (π := π) (K := K) (P := P)
    hstationary (H.count t) (H.measurable_count t)
  refine ⟨?_, ?_⟩
  · simpa [stationaryTrajectoryAtForwardPoissonCount] using h.aemeasurable
  · calc
      Measure.map
          (fun z : (ℕ → α) × Ω =>
            (stationaryTrajectoryAtForwardPoissonCount (α := α) H t z, H.count t z.2))
          ((stationaryTrajMeasure π K).prod P) =
          π.prod (P.map (H.count t)) := by
            simpa [stationaryTrajectoryAtForwardPoissonCount] using h.map_eq
      _ = π.prod (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))) := by
            rw [(H.count_hasLaw t).map_eq]

/-- Under the product law of an embedded trajectory and a forward Poisson
clock, the initial/current pair is the Poisson mixture of the `n`-jump pair
laws.  The result uses external-clock independence only; it does not make the
initial state a stationary/Palm tagged arrival or identify a response-time
tail. -/
theorem stationaryTrajMeasure_zero_forwardPoissonCount_pair_mixture
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (s : Set (α × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω => (z.1 0, z.1 (H.count t z.2))) s =
      ∫⁻ n, (π ⊗ₘ (K ^ n)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t))) := by
  letI : IsProbabilityMeasure P := H.isProbability
  simpa only [(H.count_hasLaw t).map_eq] using
    (stationaryTrajMeasure_zero_externalIndex_pair_mixture
      (π := π) (K := K) (P := P) (H.count t) (H.measurable_count t) s hs)

/-- The same initial/current law expressed through the PMF iterates of the
uniformized transition rows. This makes the Poisson mixing layer explicit
without yet asserting the Chapman--Kolmogorov semigroup law. -/
theorem stationaryTrajMeasure_zero_forwardPoissonCount_pair_mixture_iterate
    {π : Measure α} [IsProbabilityMeasure π] {K : CountableMarkovKernel α}
    [Countable α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (s : Set (α × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π (countablePMFKernel K)).prod P).map
        (fun z : (ℕ → α) × Ω => (z.1 0, z.1 (H.count t z.2))) s =
      ∫⁻ step, (π ⊗ₘ countablePMFKernel (K.iterate step)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t))) := by
  simpa only [CountableMarkovKernel.countablePMFKernel_iterate_eq_pow] using
    (stationaryTrajMeasure_zero_forwardPoissonCount_pair_mixture
      (π := π) (K := countablePMFKernel K) H t s hs)

/-- Starting from an arbitrary initial law, the time-zero state and two later
forward-Poisson-clock states have the explicit two-increment mixture of the
successive embedded transition kernels.  This is the deterministic-time
finite-dimensional law of the product construction; it does not assert a
stopping-time Markov property or a functional limit. -/
theorem stationaryTrajMeasure_zero_forwardPoissonCount_triple_mixture
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {sTime tTime : ℝ≥0} (hst : sTime ≤ tTime)
    (s : Set ((α × α) × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω =>
          ((z.1 0, z.1 (H.count sTime z.2)), z.1 (H.count tTime z.2))) s =
      ∫⁻ q : ℕ × ℕ, ((π ⊗ₘ (K ^ q.1)) ⊗ₘ (K ^ q.2).prodMkLeft α) s ∂
        (P.map fun omega =>
          (H.intervalCount 0 sTime omega, H.intervalCount sTime tTime omega)) := by
  letI : IsProbabilityMeasure P := H.isProbability
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  have hzero : ∀ᵐ omega ∂P, H.count 0 omega = 0 := H.count_zero_ae
  have hmono : ∀ᵐ omega ∂P, H.count sTime omega ≤ H.count tTime omega :=
    H.count_le_ae hst
  have hlift : ∀ᵐ z : (ℕ → α) × Ω ∂(stationaryTrajMeasure π K).prod P,
      H.count 0 z.2 = 0 ∧ H.count sTime z.2 ≤ H.count tTime z.2 := by
    refine ae_of_ae_map
      (μ := (stationaryTrajMeasure π K).prod P)
      (f := Prod.snd)
      (p := fun omega : Ω => H.count 0 omega = 0 ∧
        H.count sTime omega ≤ H.count tTime omega)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    filter_upwards [hzero, hmono] with omega hzero hmono
    exact ⟨hzero, hmono⟩
  have hmixture := stationaryTrajMeasure_zero_externalIndex_add_triple_mixture
    (π := π) (K := K) (P := P)
    (H.intervalCount 0 sTime) (H.intervalCount sTime tTime)
    (H.measurable_intervalCount 0 sTime) (H.measurable_intervalCount sTime tTime) s hs
  calc
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω =>
          ((z.1 0, z.1 (H.count sTime z.2)), z.1 (H.count tTime z.2))) s =
        ((stationaryTrajMeasure π K).prod P).map
          (fun z : (ℕ → α) × Ω =>
            ((z.1 0, z.1 (H.intervalCount 0 sTime z.2)),
              z.1 (H.intervalCount 0 sTime z.2 + H.intervalCount sTime tTime z.2))) s := by
          exact congrArg (fun eta : Measure ((α × α) × α) => eta s)
            (Measure.map_congr (by
              filter_upwards [hlift] with z hz
              dsimp [PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw.intervalCount]
              rw [hz.1, Nat.sub_zero, Nat.add_sub_of_le hz.2]))
    _ = ∫⁻ q : ℕ × ℕ, ((π ⊗ₘ (K ^ q.1)) ⊗ₘ (K ^ q.2).prodMkLeft α) s ∂
        (P.map fun omega =>
          (H.intervalCount 0 sTime omega, H.intervalCount sTime tTime omega)) := by
          exact hmixture

/-- For a stationary embedded trajectory run on an independent forward
Poisson clock, the pair at two ordered deterministic times is the Poisson
mixture of embedded transition couplings over the intervening clock count.
This is an exact two-time product-space law. It does not by itself construct
a continuous-time semigroup, establish the Markov property at arbitrary
stopping times, or supply path-space diffusion convergence. -/
theorem stationaryTrajMeasure_forwardPoissonCount_pair_mixture
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {sTime tTime : ℝ≥0} (hst : sTime ≤ tTime)
    (s : Set (α × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω =>
          (stationaryTrajectoryAtForwardPoissonCount (α := α) H sTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := α) H tTime z)) s =
      ∫⁻ m, (π ⊗ₘ (K ^ m)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))) := by
  letI : IsProbabilityMeasure P := H.isProbability
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  have hclockMono : ∀ᵐ omega ∂P, H.count sTime omega ≤ H.count tTime omega :=
    H.count_le_ae hst
  have hlift : ∀ᵐ z : (ℕ → α) × Ω ∂(stationaryTrajMeasure π K).prod P,
      H.count sTime z.2 ≤ H.count tTime z.2 := by
    refine ae_of_ae_map
      (μ := (stationaryTrajMeasure π K).prod P)
      (f := Prod.snd)
      (p := fun omega : Ω => H.count sTime omega ≤ H.count tTime omega)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclockMono
  have hmix := stationaryTrajMeasure_externalIndex_add_pair_mixture
    (π := π) (K := K) (P := P) hstationary
    (H.count sTime) (H.intervalCount sTime tTime)
    (H.measurable_count sTime) (H.measurable_intervalCount sTime tTime) s hs
  calc
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω =>
          (stationaryTrajectoryAtForwardPoissonCount (α := α) H sTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := α) H tTime z)) s =
        ((stationaryTrajMeasure π K).prod P).map
          (fun z : (ℕ → α) × Ω =>
            (z.1 (H.count sTime z.2),
              z.1 (H.count sTime z.2 + H.intervalCount sTime tTime z.2))) s := by
          exact congrArg (fun η : Measure (α × α) => η s) (Measure.map_congr (by
            filter_upwards [hlift] with z hz
            dsimp [stationaryTrajectoryAtForwardPoissonCount]
            change (z.1 (H.count sTime z.2), z.1 (H.count tTime z.2)) =
              (z.1 (H.count sTime z.2),
                z.1 (H.count sTime z.2 +
                  (H.count tTime z.2 - H.count sTime z.2)))
            rw [Nat.add_sub_of_le hz]))
    _ = ∫⁻ m, (π ⊗ₘ (K ^ m)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))) := by
          simpa only [(H.intervalCount_hasLaw hst).map_eq] using hmix

/--
At three ordered deterministic times, a stationary embedded trajectory run on
an independent forward Poisson clock has the exact two-increment mixture law.
The product of Poisson interval laws is explicit, so this is the
finite-dimensional Chapman--Kolmogorov bridge for the time-changed
construction.  It remains a deterministic-time product-space result and does
not assert a stopping-time Markov property or path-space convergence.
-/
theorem stationaryTrajMeasure_forwardPoissonCount_triple_mixture
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {rTime sTime tTime : ℝ≥0} (hrs : rTime ≤ sTime) (hst : sTime ≤ tTime)
    (s : Set ((α × α) × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω =>
          ((stationaryTrajectoryAtForwardPoissonCount (α := α) H rTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := α) H sTime z),
            stationaryTrajectoryAtForwardPoissonCount (α := α) H tTime z)) s =
      ∫⁻ q : ℕ × ℕ, ((π ⊗ₘ (K ^ q.1)) ⊗ₘ (K ^ q.2).prodMkLeft α) s ∂
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((sTime : ℝ) - (rTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrs))))).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) := by
  letI : IsProbabilityMeasure P := H.isProbability
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  have hclockRS : ∀ᵐ omega ∂P, H.count rTime omega ≤ H.count sTime omega :=
    H.count_le_ae hrs
  have hclockST : ∀ᵐ omega ∂P, H.count sTime omega ≤ H.count tTime omega :=
    H.count_le_ae hst
  have hlift : ∀ᵐ z : (ℕ → α) × Ω ∂(stationaryTrajMeasure π K).prod P,
      H.count rTime z.2 ≤ H.count sTime z.2 ∧
        H.count sTime z.2 ≤ H.count tTime z.2 := by
    refine ae_of_ae_map
      (μ := (stationaryTrajMeasure π K).prod P)
      (f := Prod.snd)
      (p := fun omega : Ω => H.count rTime omega ≤ H.count sTime omega ∧
        H.count sTime omega ≤ H.count tTime omega)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    filter_upwards [hclockRS, hclockST] with omega hRS hST
    exact ⟨hRS, hST⟩
  have hmix := stationaryTrajMeasure_externalIndex_add_add_triple_mixture
    (π := π) (K := K) (P := P) hstationary
    (H.count rTime) (H.intervalCount rTime sTime) (H.intervalCount sTime tTime)
    (H.measurable_count rTime) (H.measurable_intervalCount rTime sTime)
    (H.measurable_intervalCount sTime tTime) s hs
  have hindependent := H.indepFun_intervalCount_adjacent hrs hst
  have hjoint : P.map (fun omega =>
      (H.intervalCount rTime sTime omega, H.intervalCount sTime tTime omega)) =
      (P.map (H.intervalCount rTime sTime)).prod
        (P.map (H.intervalCount sTime tTime)) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (H.measurable_intervalCount rTime sTime).aemeasurable
      (H.measurable_intervalCount sTime tTime).aemeasurable).mp hindependent
  calc
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω =>
          ((stationaryTrajectoryAtForwardPoissonCount (α := α) H rTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := α) H sTime z),
            stationaryTrajectoryAtForwardPoissonCount (α := α) H tTime z)) s =
        ((stationaryTrajMeasure π K).prod P).map
          (fun z : (ℕ → α) × Ω =>
            ((z.1 (H.count rTime z.2),
              z.1 (H.count rTime z.2 + H.intervalCount rTime sTime z.2)),
              z.1 (H.count rTime z.2 + H.intervalCount rTime sTime z.2 +
                H.intervalCount sTime tTime z.2))) s := by
          exact congrArg (fun eta : Measure ((α × α) × α) => eta s)
            (Measure.map_congr (by
              filter_upwards [hlift] with z hz
              dsimp [stationaryTrajectoryAtForwardPoissonCount]
              rw [show H.intervalCount rTime sTime z.2 =
                    H.count sTime z.2 - H.count rTime z.2 by rfl,
                show H.intervalCount sTime tTime z.2 =
                    H.count tTime z.2 - H.count sTime z.2 by rfl,
                Nat.add_sub_of_le hz.1, Nat.add_sub_of_le hz.2]))
    _ = ∫⁻ q : ℕ × ℕ, ((π ⊗ₘ (K ^ q.1)) ⊗ₘ (K ^ q.2).prodMkLeft α) s ∂
        (P.map fun omega =>
          (H.intervalCount rTime sTime omega, H.intervalCount sTime tTime omega)) := by
          exact hmix
    _ = ∫⁻ q : ℕ × ℕ, ((π ⊗ₘ (K ^ q.1)) ⊗ₘ (K ^ q.2).prodMkLeft α) s ∂
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((sTime : ℝ) - (rTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrs))))).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg H.rate_nonneg
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) := by
          rw [hjoint, (H.intervalCount_hasLaw hrs).map_eq,
            (H.intervalCount_hasLaw hst).map_eq]

/-- The rate-specialized uniformized M/M/1 embedded trajectory retains its
geometric state law after an independent external forward Poisson time change
at every fixed time.  The conclusion deliberately does not identify the
resulting process as a CTMC semigroup. -/
theorem mm1_uniformized_stationaryTraj_eval_forwardPoissonCount_hasLaw
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t)
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
      ((stationaryTrajMeasure
        (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
          (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)))).prod P) := by
  exact stationaryTrajMeasure_eval_forwardPoissonCount_hasLaw
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant H t

/-- At every deterministic time, the stationary uniformized M/M/1 state has
its geometric law jointly independently of the total external Poisson event
count.  This is a fixed-time invariance bridge only: it does not split total
events into actual arrivals and potential-service attempts, prove PASTA, or
construct a Palm-tagged arrival. -/
theorem mm1_uniformized_stationaryTraj_eval_forwardPoissonCount_joint_hasLaw
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × Ω =>
        (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t z, H.count t z.2))
      (((geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))))
      ((stationaryTrajMeasure
        (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
          (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)))).prod P) := by
  exact stationaryTrajMeasure_eval_forwardPoissonCount_joint_hasLaw
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant H t

/-- The preceding fixed-time joint law when the external event clock is
rate-aligned with uniformization.  Its count parameter is literally
`(arrivalRate + serviceRate) * t`; this still does not identify marked
arrival/service clocks, PASTA, or a Palm-tagged arrival. -/
theorem mm1_uniformized_stationaryTraj_eval_alignedForwardPoissonCount_joint_hasLaw
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (hclockRate : H.rate = ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × Ω =>
        (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t z, H.count t z.2))
      (((geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            ((arrivalRate + serviceRate : ℝ≥0) : ℝ) (t : ℝ)
            (mul_nonneg (by positivity) (NNReal.coe_nonneg t)))))
      ((stationaryTrajMeasure
        (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
          (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)))).prod P) := by
  simpa [hclockRate] using
    (mm1_uniformized_stationaryTraj_eval_forwardPoissonCount_joint_hasLaw
      arrivalRate serviceRate hstable H t)

/-- If the external clock is rate-aligned with the M/M/1 uniformization rate,
its fixed-time count has the expected Poisson parameter `(λ + μ)t`.  Together
with the preceding state-law theorem, this is the checked fixed-time
uniformization bridge; it is not a proof of a continuous-time semigroup. -/
theorem mm1_uniformization_forwardClock_count_hasLaw
    (arrivalRate serviceRate : ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (hclockRate : H.rate = ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
    (t : ℝ≥0) :
    HasLaw (H.count t)
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((arrivalRate + serviceRate : ℝ≥0) : ℝ) (t : ℝ)
          (mul_nonneg (by positivity) (NNReal.coe_nonneg t)))) P := by
  simpa [hclockRate] using H.count_hasLaw t

end

end AppliedModelingLib.Probability.Queueing

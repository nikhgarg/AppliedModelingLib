import AppliedModelingLib.Queueing.ManyServerTrajectory
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson
import AppliedModelingLib.Foundations.Probability.SkorokhodJ1

/-!
# Canonical-clock trajectories for uniformized many-server queues

This module specializes the external-clock construction for a uniformized
many-server queue to the canonical forward Poisson process built from iid
exponential interarrivals.  It gives concrete fixed-time laws on a product
probability space.  Identifying this construction with a continuous-time
Markov semigroup or establishing full càdlàg path semantics is separate.
-/

namespace AppliedModelingLib.Probability.Queueing

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The potential-event rate of a many-server uniformization is positive when
the number of servers and service rate are positive. -/
theorem manyServerUniformizationRate_pos
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    0 < manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers := by
  unfold manyServerUniformizationRate
  exact mul_pos (mul_pos (by exact_mod_cast hservers) hserviceRate) (by positivity)

/-- The canonical forward Poisson clock at the many-server potential-event
rate. -/
noncomputable def manyServerCanonicalForwardPoissonClock
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw (ℕ → ℝ)
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
  PoissonProcess.canonicalForwardHomogeneousPoissonCountingProcessByLaw
    (manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate)

/-- A trajectory evaluated at a monotone natural-valued clock has finite
range on every compact forward-time interval. -/
theorem finite_range_timeChangedTrajectory_on_Icc
    {α : Type*} (trajectory : ℕ → α) (count : ℝ≥0 → ℕ)
    (hcount : Monotone count) (horizon : ℝ≥0) :
    (Set.range fun t : Set.Icc (0 : ℝ≥0) horizon =>
      trajectory (count t.1)).Finite := by
  classical
  let values : Finset α := (Finset.range (count horizon + 1)).image trajectory
  refine values.finite_toSet.subset ?_
  rintro state ⟨t, rfl⟩
  change trajectory (count t.1) ∈ values
  exact Finset.mem_image.mpr ⟨count t.1,
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hcount t.2.2)), rfl⟩

/-- The concrete many-server potential-event clock is almost surely
right-continuous along every fixed forward-time sequence approaching a time
from above. -/
theorem ae_tendsto_manyServerCanonicalForwardPoissonClock_count_from_right
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Filter.Tendsto (fun m => (u m : ℝ)) Filter.atTop (nhds (t : ℝ)))
    (htu : ∀ m, t ≤ u m) :
    ∀ᵐ omega ∂PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers),
      Filter.Tendsto
        (fun m => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count (u m) omega)
        Filter.atTop
        (nhds ((manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count t omega)) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (PoissonProcess.ae_tendsto_canonicalRenewalCount_of_tendsto_from_right
      (manyServerUniformizationRate_pos trafficIntensity serviceRate servers
        hservers hserviceRate)
      (t : ℝ) (fun m => (u m : ℝ)) hu
      (fun m => NNReal.coe_le_coe.mpr (htu m)))

/-- The concrete many-server potential-event clock has the expected
sequential left limit along every fixed forward-time sequence approaching a
time from below. -/
theorem ae_tendsto_manyServerCanonicalForwardPoissonClock_count_from_left
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Filter.Tendsto (fun m => (u m : ℝ)) Filter.atTop (nhds (t : ℝ)))
    (htu : ∀ m, u m < t) :
    ∀ᵐ omega ∂PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers),
      Filter.Tendsto
        (fun m => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count (u m) omega)
        Filter.atTop
        (nhds (PoissonProcess.canonicalRenewalCountLE (t : ℝ) omega)) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (PoissonProcess.ae_tendsto_canonicalRenewalCount_of_tendsto_from_left
      (manyServerUniformizationRate_pos trafficIntensity serviceRate servers
        hservers hserviceRate)
      (t : ℝ) (fun m => (u m : ℝ)) hu
      (fun m => NNReal.coe_lt_coe.mpr (htu m)))

/-- The canonical-clock uniformized many-server trajectory is almost surely
right-continuous along every fixed forward-time sequence approaching a time
from above. -/
theorem ae_tendsto_manyServerUniformizedCanonicalTrajectory_from_right
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Filter.Tendsto (fun m => (u m : ℝ)) Filter.atTop (nhds (t : ℝ)))
    (htu : ∀ m, t ≤ u m) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      Filter.Tendsto
        (fun m => z.1
          ((manyServerCanonicalForwardPoissonClock
            trafficIntensity serviceRate servers hservers hserviceRate).count (u m) z.2))
        Filter.atTop
        (nhds (z.1
          ((manyServerCanonicalForwardPoissonClock
            trafficIntensity serviceRate servers hservers hserviceRate).count t z.2)) ) := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hclock := ae_tendsto_manyServerCanonicalForwardPoissonClock_count_from_right
    trafficIntensity serviceRate servers hservers hserviceRate t u hu htu
  have hlift : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      Filter.Tendsto
        (fun m => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count (u m) z.2)
        Filter.atTop
        (nhds ((manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count t z.2)) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))
      (f := Prod.snd)
      (p := fun omega : ℕ → ℝ => Filter.Tendsto
        (fun m => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count (u m) omega)
        Filter.atTop
        (nhds ((manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count t omega)))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with z hz
  exact Tendsto.comp
    (show Filter.Tendsto z.1
      (nhds ((manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate).count t z.2))
      (nhds (z.1 ((manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate).count t z.2))) from
      (continuous_of_discreteTopology : Continuous z.1).continuousAt)
    hz

/-- The canonical-clock uniformized many-server trajectory has the indicated
sequential left limit along every fixed forward-time sequence approaching a
time from below. -/
theorem ae_tendsto_manyServerUniformizedCanonicalTrajectory_from_left
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Filter.Tendsto (fun m => (u m : ℝ)) Filter.atTop (nhds (t : ℝ)))
    (htu : ∀ m, u m < t) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      Filter.Tendsto
        (fun m => z.1
          ((manyServerCanonicalForwardPoissonClock
            trafficIntensity serviceRate servers hservers hserviceRate).count (u m) z.2))
        Filter.atTop
        (nhds (z.1 (PoissonProcess.canonicalRenewalCountLE (t : ℝ) z.2))) := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hclock := ae_tendsto_manyServerCanonicalForwardPoissonClock_count_from_left
    trafficIntensity serviceRate servers hservers hserviceRate t u hu htu
  have hlift : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      Filter.Tendsto
        (fun m => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count (u m) z.2)
        Filter.atTop
        (nhds (PoissonProcess.canonicalRenewalCountLE (t : ℝ) z.2)) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))
      (f := Prod.snd)
      (p := fun omega : ℕ → ℝ => Filter.Tendsto
        (fun m => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count (u m) omega)
        Filter.atTop
        (nhds (PoissonProcess.canonicalRenewalCountLE (t : ℝ) omega)))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with z hz
  exact Tendsto.comp
    (show Filter.Tendsto z.1
      (nhds (PoissonProcess.canonicalRenewalCountLE (t : ℝ) z.2))
      (nhds (z.1 (PoissonProcess.canonicalRenewalCountLE (t : ℝ) z.2))) from
      (continuous_of_discreteTopology : Continuous z.1).continuousAt)
    hz

/-- The real-time extension of the canonical-clock uniformized many-server
trajectory is almost surely càdlàg.  On nonnegative times it agrees with the
forward-Poisson-clock trajectory. -/
theorem ae_isCadlagPath_manyServerUniformizedCanonicalTrajectory_on_real
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      IsCadlagPath (fun t : ℝ => z.1 (PoissonProcess.canonicalRenewalCount t z.2)) := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hclock := PoissonProcess.ae_isCadlagPath_canonicalRenewalCount hrate
  have hlift : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      IsCadlagPath (fun t : ℝ => PoissonProcess.canonicalRenewalCount t z.2) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))
      (f := Prod.snd)
      (p := fun omega : ℕ → ℝ =>
        IsCadlagPath (fun t : ℝ => PoissonProcess.canonicalRenewalCount t omega))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with z hz
  simpa only [Function.comp_def] using
    (IsCadlagPath.continuous_comp hz
      (continuous_of_discreteTopology : Continuous z.1))

/-- The all-real-time càdlàg extension agrees with the canonical forward
Poisson-clock trajectory at each nonnegative time. -/
theorem manyServerUniformizedCanonicalTrajectory_on_real_eq_forward
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (z : (ℕ → ℕ) × (ℕ → ℝ)) (t : ℝ≥0) :
    z.1 (PoissonProcess.canonicalRenewalCount (t : ℝ) z.2) =
      z.1 ((manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate).count t z.2) := by
  rfl

/-- The centered square-root state coordinate used for many-server heavy
traffic paths. -/
noncomputable def manyServerCenteredSqrtPath (servers : ℕ) (path : ℝ → ℕ) : ℝ → ℝ :=
  fun time => ((path time : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)

/-- The raw queue-length path obtained by running an unmarked embedded
trajectory on the canonical independent Poisson clock.  This is the
unscaled physical-time object underlying the centered many-server paths. -/
noncomputable def manyServerCanonicalQueueLengthOnReal
    (z : (ℕ → ℕ) × (ℕ → ℝ)) : ℝ → ℕ :=
  fun time => z.1 (PoissonProcess.canonicalRenewalCount time z.2)

/-- The centered square-root-scaled canonical uniformized trajectory on the
all-real-time extension. -/
noncomputable def manyServerCenteredSqrtCanonicalTrajectoryOnReal
    (servers : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) : ℝ → ℝ :=
  manyServerCenteredSqrtPath servers
    (manyServerCanonicalQueueLengthOnReal z)

/-- The centered canonical trajectory stopped after a deterministic number of
potential clock events.  On a nonexplosive clock path these finite-event
approximations eventually agree with the original trajectory on every compact
forward-time interval. -/
noncomputable def manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal
    (servers cutoff : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) : ℝ → ℝ :=
  manyServerCenteredSqrtPath servers
    (fun time : ℝ => z.1 (min (PoissonProcess.canonicalRenewalCount time z.2) cutoff))

/-- On a monotone nonexplosive renewal path, truncating a time-changed
trajectory after `cutoff` events is exactly the finite step path whose knots
are its first `cutoff` arrival epochs.  This is a deterministic path identity;
it does not use the exponential law. -/
theorem finiteStepPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
    {State : Type*} (trajectory : ℕ → State) (cutoff : ℕ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gaps)
      atTop atTop)
    (hmono : Monotone (fun index : ℕ => PoissonProcess.arrivalTime index gaps))
    (time : ℝ) :
    AppliedModelingLib.Probability.finiteStepPath
      (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val gaps)
      (fun index : Fin (cutoff + 1) => trajectory index.val)
      time = trajectory (min (PoissonProcess.canonicalRenewalCount time gaps) cutoff) := by
  have hfuture : ∃ index : ℕ, time < PoissonProcess.arrivalTime index gaps :=
    PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop gaps hdiverges time
  have hfilters : ((Finset.univ : Finset (Fin cutoff)).filter
      (fun index => PoissonProcess.arrivalTime index.val gaps ≤ time)) =
      (Finset.univ.filter fun index : Fin cutoff =>
        (index : ℕ) < PoissonProcess.canonicalRenewalCount time gaps) := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (PoissonProcess.lt_canonicalRenewalCount_iff_arrivalTime_le time gaps
      hfuture hmono index.val).symm
  have hcard : ((Finset.univ : Finset (Fin cutoff)).filter
      (fun index => PoissonProcess.arrivalTime index.val gaps ≤ time)).card =
      min cutoff (PoissonProcess.canonicalRenewalCount time gaps) := by
    rw [hfilters]
    exact Fin.card_filter_val_lt
  unfold AppliedModelingLib.Probability.finiteStepPath
  apply congrArg trajectory
  change ((Finset.univ : Finset (Fin cutoff)).filter
      (fun index => PoissonProcess.arrivalTime index.val gaps ≤ time)).card =
    min (PoissonProcess.canonicalRenewalCount time gaps) cutoff
  rw [hcard, min_comm]

/-- The first finitely many renewal epochs, when they lie strictly inside a
finite horizon, form an ordered interior knot family for the finite-horizon
Skorokhod path construction. -/
noncomputable def arrivalTimesInteriorKnotFamily (horizon : ℝ) (cutoff : ℕ)
    (gaps : ℕ → ℝ)
    (hpositive : ∀ index : Fin cutoff,
      0 < PoissonProcess.arrivalTime index.val gaps)
    (hbelow : ∀ index : Fin cutoff,
      PoissonProcess.arrivalTime index.val gaps < horizon)
    (hstrict : StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index gaps)) :
    AppliedModelingLib.Probability.OrderedInteriorKnotFamily horizon cutoff :=
  ⟨fun index => PoissonProcess.arrivalTime index.val gaps, hpositive, hbelow, by
    intro first second hfirst_second
    exact hstrict hfirst_second⟩

/-- On a strictly increasing nonexplosive renewal path, the finite-horizon
Skorokhod bundle formed from the first `cutoff` arrival times is exactly the
corresponding truncated time-changed trajectory. -/
theorem finiteStepSkorokhodPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
    {State : Type*} [TopologicalSpace State] (trajectory : ℕ → State)
    (horizon : ℝ) (cutoff : ℕ)
    (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gaps)
      atTop atTop)
    (hpositive : ∀ index : Fin cutoff,
      0 < PoissonProcess.arrivalTime index.val gaps)
    (hbelow : ∀ index : Fin cutoff,
      PoissonProcess.arrivalTime index.val gaps < horizon)
    (hstrict : StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index gaps))
    (time : ℝ) :
    AppliedModelingLib.Probability.finiteStepSkorokhodPath
      (arrivalTimesInteriorKnotFamily horizon cutoff gaps hpositive hbelow hstrict)
      (fun index : Fin (cutoff + 1) => trajectory index.val) time =
      trajectory (min (PoissonProcess.canonicalRenewalCount time gaps) cutoff) := by
  rw [AppliedModelingLib.Probability.finiteStepSkorokhodPath_apply]
  exact finiteStepPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
    trajectory cutoff gaps hdiverges hstrict.monotone time

/-- The same finite-arrival representation is an equality of local
Skorokhod-path values.  No clock regularity premise is required: strict
nonexplosion itself identifies the trajectory with a finite càdlàg step path.
-/
theorem finiteStepLocalPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
    {State : Type*} [TopologicalSpace State] (trajectory : ℕ → State)
    (cutoff : ℕ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gaps)
      atTop atTop)
    (hstrict : StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index gaps))
    (time : ℝ) :
    AppliedModelingLib.Probability.finiteStepLocalPath
      (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val gaps)
      (fun index : Fin (cutoff + 1) => trajectory index.val)
      (by
        intro first second hfirst_second
        exact hstrict hfirst_second) time =
      trajectory (min (PoissonProcess.canonicalRenewalCount time gaps) cutoff) := by
  rw [AppliedModelingLib.Probability.finiteStepLocalPath_apply]
  exact finiteStepPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
    trajectory cutoff gaps hdiverges hstrict.monotone time

/-- Strictly increasing nonexplosive renewal epochs make every finite-event
truncation càdlàg by its finite-step representation. -/
theorem isCadlagPath_truncatedCanonicalRenewalTrajectory_of_arrivalTimes
    {State : Type*} [TopologicalSpace State]
    (trajectory : ℕ → State) (cutoff : ℕ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gaps)
      atTop atTop)
    (hstrict : StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index gaps)) :
    IsCadlagPath (fun time : ℝ =>
      trajectory (min (PoissonProcess.canonicalRenewalCount time gaps) cutoff)) := by
  let jumpTimes : Fin cutoff → ℝ :=
    fun index => PoissonProcess.arrivalTime index.val gaps
  let values : Fin (cutoff + 1) → State := fun index => trajectory index.val
  have hstrictFin : StrictMono jumpTimes := by
    intro first second hfirst_second
    exact hstrict hfirst_second
  have hpath : IsCadlagPath (AppliedModelingLib.Probability.finiteStepPath jumpTimes values) :=
    AppliedModelingLib.Probability.isCadlagPath_finiteStepPath jumpTimes values hstrictFin
  rw [show (fun time : ℝ =>
      trajectory (min (PoissonProcess.canonicalRenewalCount time gaps) cutoff)) =
      AppliedModelingLib.Probability.finiteStepPath jumpTimes values by
    funext time
    symm
    exact finiteStepPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
      trajectory cutoff gaps hdiverges hstrict.monotone time]
  exact hpath

/-- Truncating the value of a càdlàg renewal clock and then reading a discrete
embedded trajectory still produces a càdlàg real-time trajectory. -/
theorem isCadlagPath_truncatedCanonicalRenewalTrajectory
    {State : Type*} [TopologicalSpace State]
    (trajectory : ℕ → State) (cutoff : ℕ) (gaps : ℕ → ℝ)
    (hclock : IsCadlagPath (fun time : ℝ =>
      PoissonProcess.canonicalRenewalCount time gaps)) :
    IsCadlagPath (fun time : ℝ =>
      trajectory (min (PoissonProcess.canonicalRenewalCount time gaps) cutoff)) := by
  simpa only [Function.comp_def] using hclock.continuous_comp
    (continuous_of_discreteTopology : Continuous (fun index : ℕ =>
      trajectory (min index cutoff)))

/-- Every fixed real-time coordinate of the concrete centered/scaled canonical
trajectory is measurable on the product input space. -/
theorem measurable_manyServerCanonicalQueueLengthOnReal_apply
    (time : ℝ) :
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCanonicalQueueLengthOnReal z time) := by
  have hindex : Measurable (fun omega : ℕ → ℝ =>
      PoissonProcess.canonicalRenewalCount time omega) :=
    PoissonProcess.measurable_canonicalRenewalCount time
  simpa [manyServerCanonicalQueueLengthOnReal] using
    (measurable_trajectoryAtIndependentRandomIndex
      (PoissonProcess.canonicalRenewalCount time) hindex)

/-- The raw canonical queue-length path is measurable for the product
σ-algebra on real-indexed queue paths. -/
theorem measurable_manyServerCanonicalQueueLengthOnReal :
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCanonicalQueueLengthOnReal z) := by
  exact measurable_pi_lambda _ fun time =>
    measurable_manyServerCanonicalQueueLengthOnReal_apply time

/-- Every fixed real-time coordinate of the concrete centered/scaled canonical
trajectory is measurable on the product input space. -/
theorem measurable_manyServerCenteredSqrtCanonicalTrajectoryOnReal_apply
    (servers : ℕ) (time : ℝ) :
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z time) := by
  have hscale : Measurable (fun state : ℕ =>
      ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)) :=
    (continuous_of_discreteTopology : Continuous
      (fun state : ℕ => ((state : ℝ) - (servers : ℝ)) /
        Real.sqrt (servers : ℝ))).measurable
  simpa [manyServerCenteredSqrtCanonicalTrajectoryOnReal,
    manyServerCenteredSqrtPath] using hscale.comp
      (measurable_manyServerCanonicalQueueLengthOnReal_apply time)

/-- The concrete centered/scaled canonical trajectory is measurable as a
real-indexed raw path with the product measurable-space structure.  Passing
from this raw path to the bundled local-`J₁` path still requires the separate
càdlàg-subtype and `J₁`-Borel bridge. -/
theorem measurable_manyServerCenteredSqrtCanonicalTrajectoryOnReal
    (servers : ℕ) :
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z) := by
  exact measurable_pi_lambda _ fun time =>
    measurable_manyServerCenteredSqrtCanonicalTrajectoryOnReal_apply servers time

/-- Each coordinate of a deterministic finite-event truncation is measurable
on the product input space. -/
theorem measurable_manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal_apply
    (servers cutoff : ℕ) (time : ℝ) :
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z time) := by
  have hindex : Measurable (fun gaps : ℕ → ℝ =>
      min (PoissonProcess.canonicalRenewalCount time gaps) cutoff) :=
    (Measurable.of_discrete : Measurable (fun index : ℕ => min index cutoff)).comp
      (PoissonProcess.measurable_canonicalRenewalCount time)
  have hevaluate : Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      z.1 (min (PoissonProcess.canonicalRenewalCount time z.2) cutoff)) :=
    measurable_trajectoryAtIndependentRandomIndex
      (fun gaps : ℕ → ℝ => min (PoissonProcess.canonicalRenewalCount time gaps) cutoff)
      hindex
  have hscale : Measurable (fun state : ℕ =>
      ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)) :=
    (continuous_of_discreteTopology : Continuous
      (fun state : ℕ => ((state : ℝ) - (servers : ℝ)) /
        Real.sqrt (servers : ℝ))).measurable
  simpa [manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal,
    manyServerCenteredSqrtPath] using hscale.comp hevaluate

/-- Every deterministic finite-event truncation is measurable as a raw
real-indexed product path.  This is weaker than local-`J₁` Borel
measurability, which remains a separate path-space result. -/
theorem measurable_manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal
    (servers cutoff : ℕ) :
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z) := by
  exact measurable_pi_lambda _ fun time =>
    measurable_manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal_apply
      servers cutoff time

/-- Centering and square-root scaling preserve càdlàg regularity of a
natural-valued queue path. -/
theorem isCadlagPath_manyServerCenteredSqrtPath
    {servers : ℕ} {path : ℝ → ℕ} (hpath : IsCadlagPath path) :
    IsCadlagPath (manyServerCenteredSqrtPath servers path) := by
  simpa only [manyServerCenteredSqrtPath, Function.comp_def] using
    (IsCadlagPath.continuous_comp hpath
      (continuous_of_discreteTopology : Continuous
        (fun state : ℕ => ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))))

/-- The concrete canonical-clock many-server path, in centered square-root
coordinates, is almost surely càdlàg on the real-time extension. -/
theorem ae_isCadlagPath_manyServerCenteredSqrtCanonicalTrajectory_on_real
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      IsCadlagPath (manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z) := by
  filter_upwards [ae_isCadlagPath_manyServerUniformizedCanonicalTrajectory_on_real
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate] with z hz
  simpa [manyServerCenteredSqrtCanonicalTrajectoryOnReal] using
    isCadlagPath_manyServerCenteredSqrtPath hz

/-- Every deterministic finite-event truncation of the centered canonical
many-server path is almost surely càdlàg. -/
theorem ae_isCadlagPath_manyServerCenteredSqrtCanonicalTruncatedTrajectory_on_real
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      IsCadlagPath
        (manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z) := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hclock := PoissonProcess.ae_isCadlagPath_canonicalRenewalCount hrate
  have hlift : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time z.2) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))
      (f := Prod.snd)
      (p := fun gaps : ℕ → ℝ => IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gaps))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with z hclock_z
  apply isCadlagPath_manyServerCenteredSqrtPath
  simpa [manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal] using
    (isCadlagPath_truncatedCanonicalRenewalTrajectory z.1 cutoff z.2 hclock_z)

/-- The scaled canonical many-server trajectory is càdlàg on the source time
domain `[0,∞)`. -/
theorem ae_isCadlagOn_manyServerCenteredSqrtCanonicalTrajectory
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      IsCadlagOn (Set.Ici (0 : ℝ))
        (manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z) := by
  filter_upwards [ae_isCadlagPath_manyServerCenteredSqrtCanonicalTrajectory_on_real
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate] with z hz
  exact IsCadlagPath.on_of_isCadlagPath hz (Set.Ici 0)

/-- A total càdlàg-path-valued version of the scaled canonical trajectory.
Outside the càdlàg event it uses the zero path; the next theorem proves that
this modification agrees almost surely with the concrete trajectory. -/
noncomputable def manyServerCenteredSqrtCanonicalCadlagPath
    (servers : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) :
    CadlagPathOn ℝ ℝ (Set.Ici (0 : ℝ)) := by
  classical
  exact if hcadlag : IsCadlagOn (Set.Ici (0 : ℝ))
      (manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z) then
    IsCadlagOn.toCadlagPathOn hcadlag
  else
    CadlagPathOn.constant (Set.Ici (0 : ℝ)) 0

/-- The total local-`J₁` version of the centered square-root canonical path.
It uses the same null-set modification as
`manyServerCenteredSqrtCanonicalCadlagPath`; measurability of this map for
the local `J₁` Borel structure is a separate result. -/
noncomputable def manyServerCenteredSqrtCanonicalSkorokhodPath
    (servers : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) : SkorokhodJ1LocalPath ℝ :=
  SkorokhodJ1LocalPath.ofCadlagPathOn
    (manyServerCenteredSqrtCanonicalCadlagPath servers z)

/-- A total local-`J₁` version of the deterministic finite-event truncation
of the centered canonical path.  Outside its càdlàg event it is the zero path,
exactly as for the untruncated canonical version. -/
noncomputable def manyServerCenteredSqrtCanonicalTruncatedCadlagPath
    (servers cutoff : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) :
    CadlagPathOn ℝ ℝ (Set.Ici (0 : ℝ)) := by
  classical
  exact if hcadlag : IsCadlagOn (Set.Ici (0 : ℝ))
      (manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z) then
    IsCadlagOn.toCadlagPathOn hcadlag
  else
    CadlagPathOn.constant (Set.Ici (0 : ℝ)) 0

/-- The local-`J₁` bundle for a deterministic finite-event truncation of the
centered canonical path. -/
noncomputable def manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath
    (servers cutoff : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) : SkorokhodJ1LocalPath ℝ :=
  SkorokhodJ1LocalPath.ofCadlagPathOn
    (manyServerCenteredSqrtCanonicalTruncatedCadlagPath servers cutoff z)

/-- The finite information needed to represent a canonical renewal path as
an ordered step path without an integer-horizon boundary jump. -/
def canonicalFiniteEventStepGood (cutoff : ℕ) (gaps : ℕ → ℝ) : Prop :=
  (∀ index : Fin cutoff, 0 < PoissonProcess.arrivalTime index.val gaps) ∧
    StrictMono (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val gaps) ∧
      (∀ index : Fin cutoff, ∀ horizon : ℕ,
        PoissonProcess.arrivalTime index.val gaps ≠ (horizon : ℝ))

/-- The cell on which exactly the first `active` finite renewal epochs lie
strictly before a specified integer horizon.  The post-prefix inequality is
vacuous when the deterministic truncation has already used every event. -/
def canonicalFiniteEventActiveCell (horizon cutoff : ℕ) (active : Fin (cutoff + 1)) :
    Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
  {z | canonicalFiniteEventStepGood cutoff z.2 ∧
    (∀ index : Fin active.val,
      PoissonProcess.arrivalTime index.val z.2 < (horizon : ℝ)) ∧
    (active.val < cutoff →
      (horizon : ℝ) < PoissonProcess.arrivalTime active.val z.2)}

/-- A finite-event input is globally good when it belongs to one strict
active-prefix cell at every integer horizon.  This countable condition gives
one coherent local path representative rather than separately chosen
finite-horizon versions. -/
def canonicalFiniteEventGlobalGood (cutoff : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) : Prop :=
  ∀ horizon : ℕ, ∃ active : Fin (cutoff + 1),
    z ∈ canonicalFiniteEventActiveCell horizon cutoff active

/-- For a finite strictly ordered renewal vector, positivity and avoidance of
integer horizons already supply the active prefix at every integer horizon. -/
theorem canonicalFiniteEventGlobalGood_iff_stepGood
    (cutoff : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) :
    canonicalFiniteEventGlobalGood cutoff z ↔ canonicalFiniteEventStepGood cutoff z.2 := by
  constructor
  · intro hglobal
    rcases hglobal 0 with ⟨active, hactive⟩
    exact hactive.1
  · intro hgood horizon
    obtain ⟨active, hbefore, hafter⟩ :=
      AppliedModelingLib.Probability.exists_activePrefix_of_strictMono_of_forall_ne
        (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
        hgood.2.1 (horizon : ℝ) (fun index => hgood.2.2 index horizon)
    refine ⟨active, hgood, ?_, ?_⟩
    · intro index
      simpa using hbefore index
    · intro hactive_lt
      let activeIndex : Fin cutoff := ⟨active.val, hactive_lt⟩
      exact hafter activeIndex le_rfl

/-- A countably indexed open unit-time slab for the finite canonical renewal
vector.  The step-good condition ensures this is also a cell of the globally
coherent finite-event local path. -/
def canonicalFiniteEventLocalUnitCell (cutoff : ℕ) (slabs : Fin cutoff → ℕ) :
    Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
  {z | canonicalFiniteEventStepGood cutoff z.2 ∧ ∀ index : Fin cutoff,
    (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
      PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1}

/-- Refine a finite renewal-time slab by a fixed finite vector of embedded
queue labels. -/
def canonicalFiniteEventLocalUnitLabelCell (cutoff : ℕ) (slabs : Fin cutoff → ℕ)
    (labels : Fin (cutoff + 1) → ℕ) : Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
  canonicalFiniteEventLocalUnitCell cutoff slabs ∩
    {z | ∀ index : Fin (cutoff + 1), z.1 index.val = labels index}

/-- The finite vector of canonical renewal epochs is measurable. -/
theorem measurable_canonicalFiniteEventArrivalVector (cutoff : ℕ) :
    Measurable (fun gaps : ℕ → ℝ =>
      fun index : Fin cutoff => PoissonProcess.arrivalTime index.val gaps) := by
  exact measurable_pi_lambda _ fun index =>
    PoissonProcess.measurable_arrivalTime index.val

/-- The finite-event strictness, positivity, and integer-boundary exclusion
condition is measurable on the canonical gap space. -/
theorem measurableSet_canonicalFiniteEventStepGood (cutoff : ℕ) :
    MeasurableSet {gaps : ℕ → ℝ | canonicalFiniteEventStepGood cutoff gaps} := by
  have htimes := measurable_canonicalFiniteEventArrivalVector cutoff
  have hpositive : MeasurableSet {gaps : ℕ → ℝ |
      ∀ index : Fin cutoff, 0 < PoissonProcess.arrivalTime index.val gaps} := by
    rw [show {gaps : ℕ → ℝ |
        ∀ index : Fin cutoff, 0 < PoissonProcess.arrivalTime index.val gaps} =
        ⋂ index : Fin cutoff,
          {gaps | 0 < PoissonProcess.arrivalTime index.val gaps} by
      ext gaps
      simp]
    exact MeasurableSet.iInter fun index =>
      measurableSet_lt measurable_const (PoissonProcess.measurable_arrivalTime index.val)
  have hstrict : MeasurableSet {gaps : ℕ → ℝ |
      StrictMono (fun index : Fin cutoff =>
        PoissonProcess.arrivalTime index.val gaps)} :=
    AppliedModelingLib.Probability.measurableSet_strictMono_fin _ htimes
  have hboundary : MeasurableSet {gaps : ℕ → ℝ |
      ∀ index : Fin cutoff, ∀ horizon : ℕ,
        PoissonProcess.arrivalTime index.val gaps ≠ (horizon : ℝ)} := by
    rw [show {gaps : ℕ → ℝ |
        ∀ index : Fin cutoff, ∀ horizon : ℕ,
          PoissonProcess.arrivalTime index.val gaps ≠ (horizon : ℝ)} =
        ⋂ index : Fin cutoff, ⋂ horizon : ℕ,
          {gaps | PoissonProcess.arrivalTime index.val gaps ≠ (horizon : ℝ)} by
      ext gaps
      simp]
    refine MeasurableSet.iInter fun index => MeasurableSet.iInter fun horizon => ?_
    exact ((measurableSet_singleton (horizon : ℝ)).preimage
      (PoissonProcess.measurable_arrivalTime index.val)).compl
  exact hpositive.inter (hstrict.inter hboundary)

/-- Every finite canonical renewal-time unit slab is measurable. -/
theorem measurableSet_canonicalFiniteEventLocalUnitCell
    (cutoff : ℕ) (slabs : Fin cutoff → ℕ) :
    MeasurableSet (canonicalFiniteEventLocalUnitCell cutoff slabs) := by
  have hgood : MeasurableSet {z : (ℕ → ℕ) × (ℕ → ℝ) |
      canonicalFiniteEventStepGood cutoff z.2} :=
    (measurableSet_canonicalFiniteEventStepGood cutoff).preimage measurable_snd
  have hslabs : MeasurableSet {z : (ℕ → ℕ) × (ℕ → ℝ) |
      ∀ index : Fin cutoff,
        (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
          PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} := by
    rw [show {z : (ℕ → ℕ) × (ℕ → ℝ) |
        ∀ index : Fin cutoff,
          (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
            PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} =
        ⋂ index : Fin cutoff,
          {z | (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
            PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} by
      ext z
      simp]
    refine MeasurableSet.iInter fun index => ?_
    exact (measurableSet_lt measurable_const
      ((PoissonProcess.measurable_arrivalTime index.val).comp measurable_snd)).inter
      (measurableSet_lt
        ((PoissonProcess.measurable_arrivalTime index.val).comp measurable_snd)
        measurable_const)
  exact hgood.inter hslabs

/-- Refining a finite canonical renewal-time slab by finitely many discrete
embedded labels preserves measurability. -/
theorem measurableSet_canonicalFiniteEventLocalUnitLabelCell
    (cutoff : ℕ) (slabs : Fin cutoff → ℕ) (labels : Fin (cutoff + 1) → ℕ) :
    MeasurableSet (canonicalFiniteEventLocalUnitLabelCell cutoff slabs labels) := by
  refine (measurableSet_canonicalFiniteEventLocalUnitCell cutoff slabs).inter ?_
  rw [show {z : (ℕ → ℕ) × (ℕ → ℝ) |
      ∀ index : Fin (cutoff + 1), z.1 index.val = labels index} =
      ⋂ index : Fin (cutoff + 1),
        {z | z.1 index.val = labels index} by
    ext z
    simp]
  refine MeasurableSet.iInter fun index => ?_
  exact (measurableSet_singleton (labels index)).preimage
    ((measurable_pi_apply index.val).comp measurable_fst)

/-- Refine a finite renewal-time slab by a finite vector of labels from an
arbitrary countable measurable carrier.  This is the label-neutral version of
the embedded-state cells used by finite-event local-path constructions. -/
def canonicalFiniteEventLocalUnitCountableLabelCell
    {Label : Type*} (cutoff : ℕ) (slabs : Fin cutoff → ℕ)
    (labels : Fin (cutoff + 1) → Label) : Set ((ℕ → Label) × (ℕ → ℝ)) :=
  {z | canonicalFiniteEventStepGood cutoff z.2 ∧ ∀ index : Fin cutoff,
      (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
        PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} ∩
    {z | ∀ index : Fin (cutoff + 1), z.1 index.val = labels index}

/-- A finite canonical renewal-time cell remains measurable after fixing a
finite vector of values from any countable measurable label carrier. -/
theorem measurableSet_canonicalFiniteEventLocalUnitCountableLabelCell
    {Label : Type*} [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (cutoff : ℕ) (slabs : Fin cutoff → ℕ) (labels : Fin (cutoff + 1) → Label) :
    MeasurableSet (canonicalFiniteEventLocalUnitCountableLabelCell cutoff slabs labels) := by
  have htiming : MeasurableSet {z : (ℕ → Label) × (ℕ → ℝ) |
      canonicalFiniteEventStepGood cutoff z.2 ∧ ∀ index : Fin cutoff,
        (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
          PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} := by
    have hgood : MeasurableSet {z : (ℕ → Label) × (ℕ → ℝ) |
        canonicalFiniteEventStepGood cutoff z.2} :=
      (measurableSet_canonicalFiniteEventStepGood cutoff).preimage measurable_snd
    have hslabs : MeasurableSet {z : (ℕ → Label) × (ℕ → ℝ) |
        ∀ index : Fin cutoff,
          (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
            PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} := by
      rw [show {z : (ℕ → Label) × (ℕ → ℝ) |
          ∀ index : Fin cutoff,
            (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
              PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} =
          ⋂ index : Fin cutoff,
            {z | (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
              PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1} by
        ext z
        simp]
      refine MeasurableSet.iInter fun index => ?_
      exact (measurableSet_lt measurable_const
        ((PoissonProcess.measurable_arrivalTime index.val).comp measurable_snd)).inter
        (measurableSet_lt
          ((PoissonProcess.measurable_arrivalTime index.val).comp measurable_snd)
          measurable_const)
    exact hgood.inter hslabs
  refine htiming.inter ?_
  rw [show {z : (ℕ → Label) × (ℕ → ℝ) |
      ∀ index : Fin (cutoff + 1), z.1 index.val = labels index} =
      ⋂ index : Fin (cutoff + 1), {z | z.1 index.val = labels index} by
    ext z
    simp]
  refine MeasurableSet.iInter fun index => ?_
  exact (measurableSet_singleton (labels index)).preimage
    ((measurable_pi_apply index.val).comp measurable_fst)

/-- A total finite-event local path whose values are selected from a finite
prefix of countable labels.  On the regular timing event it is the finite step
path through that prefix; elsewhere it is the constant zero path. -/
noncomputable def canonicalFiniteEventCellularLocalPath
    {Label State : Type*} [TopologicalSpace State] [Zero State]
    (cutoff : ℕ) (values : (Fin (cutoff + 1) → Label) → Fin (cutoff + 1) → State)
    (z : (ℕ → Label) × (ℕ → ℝ)) : SkorokhodJ1LocalPath State := by
  classical
  exact if hgood : canonicalFiniteEventStepGood cutoff z.2 then
    AppliedModelingLib.Probability.finiteStepLocalPath
      (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
      (values (fun index => z.1 index.val)) hgood.2.1
  else
    SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const

/-- The finite-event cellular local path is Borel measurable when its
embedded labels range over a countable measurable carrier.  Open unit-time
slabs make the exact local `J₁` topology stable while a countable partition of
the finite label vector fixes its path values. -/
theorem measurable_canonicalFiniteEventCellularLocalPath
    {Label State : Type*} [MeasurableSpace Label] [Countable Label]
    [MeasurableSingletonClass Label] [PseudoMetricSpace State] [Zero State]
    (cutoff : ℕ) (values : (Fin (cutoff + 1) → Label) → Fin (cutoff + 1) → State) :
    letI : UniformSpace (SkorokhodJ1LocalPath State) :=
      AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.uniformSpace (State := State)
    letI : MeasurableSpace (SkorokhodJ1LocalPath State) :=
      AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := State)
    Measurable (canonicalFiniteEventCellularLocalPath cutoff values) := by
  classical
  letI : UniformSpace (SkorokhodJ1LocalPath State) :=
    AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.uniformSpace (State := State)
  letI : MeasurableSpace (SkorokhodJ1LocalPath State) :=
    AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := State)
  let goodSet : Set ((ℕ → Label) × (ℕ → ℝ)) :=
    {z | canonicalFiniteEventStepGood cutoff z.2}
  let fallback : SkorokhodJ1LocalPath State :=
    SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const
  let cell : (Fin cutoff → ℕ) → (Fin (cutoff + 1) → Label) →
      Set ((ℕ → Label) × (ℕ → ℝ)) :=
    fun slabs labels =>
      canonicalFiniteEventLocalUnitCountableLabelCell cutoff slabs labels
  have hgoodSet : MeasurableSet goodSet := by
    exact (measurableSet_canonicalFiniteEventStepGood cutoff).preimage measurable_snd
  have hcellSet : ∀ slabs labels, MeasurableSet (cell slabs labels) := by
    intro slabs labels
    exact measurableSet_canonicalFiniteEventLocalUnitCountableLabelCell cutoff slabs labels
  have hcellBundle : ∀ slabs labels,
      Measurable (fun z : cell slabs labels =>
        AppliedModelingLib.Probability.finiteStepLocalPath
          (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.1.2)
          (values labels) z.2.1.1.2.1) := by
    intro slabs labels
    let times : cell slabs labels → AppliedModelingLib.Probability.localUnitSlab slabs :=
      fun z => ⟨⟨fun index => PoissonProcess.arrivalTime index.val z.1.2,
        ⟨z.2.1.1.1, z.2.1.1.2.1⟩⟩, z.2.1.2⟩
    have htimes : Measurable times := by
      apply Measurable.subtype_mk
      apply Measurable.subtype_mk
      exact (measurable_pi_lambda _ fun index =>
        (PoissonProcess.measurable_arrivalTime index.val).comp
          (measurable_snd.comp measurable_subtype_coe))
    have hbase :=
      AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.measurable_finiteStepLocalPath_on_localUnitSlab
        slabs (values labels)
    simpa [times] using hbase.comp htimes
  have hcellExtension : ∀ slabs labels,
      Measurable (fun z : (ℕ → Label) × (ℕ → ℝ) =>
        if hcell : z ∈ cell slabs labels then
          AppliedModelingLib.Probability.finiteStepLocalPath
            (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
            (values labels) hcell.1.1.2.1
        else fallback) := by
    intro slabs labels
    simpa only using
      (Measurable.dite (hcellBundle slabs labels) measurable_const (hcellSet slabs labels))
  refine AppliedModelingLib.Probability.measurable_of_countable_measurable_cover
    (fun choice : Option ((Fin cutoff → ℕ) × (Fin (cutoff + 1) → Label)) => match choice with
      | none => goodSetᶜ
      | some key => cell key.1 key.2)
    ?_ ?_
    (canonicalFiniteEventCellularLocalPath cutoff values)
    (fun choice z => match choice with
      | none => fallback
      | some key => if hcell : z ∈ cell key.1 key.2 then
          AppliedModelingLib.Probability.finiteStepLocalPath
            (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
            (values key.2) hcell.1.1.2.1
        else fallback)
    ?_ ?_
  · intro choice
    cases choice with
    | none => exact hgoodSet.compl
    | some key => exact hcellSet key.1 key.2
  · ext z
    constructor
    · intro _
      simp
    · intro _
      by_cases hgood : z ∈ goodSet
      · let slabs : Fin cutoff → ℕ := fun index =>
          Nat.floor (PoissonProcess.arrivalTime index.val z.2)
        let labels : Fin (cutoff + 1) → Label := fun index => z.1 index.val
        change canonicalFiniteEventStepGood cutoff z.2 at hgood
        refine Set.mem_iUnion.mpr ⟨some (slabs, labels), ?_⟩
        change z ∈ canonicalFiniteEventLocalUnitCountableLabelCell cutoff slabs labels
        refine ⟨?_, ?_⟩
        · refine ⟨hgood, ?_⟩
          intro index
          constructor
          · exact lt_of_le_of_ne (Nat.floor_le (hgood.1 index).le)
              (hgood.2.2 index (slabs index)).symm
          · simpa [slabs] using
              (Nat.lt_floor_add_one (PoissonProcess.arrivalTime index.val z.2))
        · intro index
          rfl
      · exact Set.mem_iUnion.mpr ⟨none, hgood⟩
  · intro choice
    cases choice with
    | none => exact measurable_const
    | some key => exact hcellExtension key.1 key.2
  · intro choice z hchoice
    cases choice with
    | none =>
        change ¬ canonicalFiniteEventStepGood cutoff z.2 at hchoice
        simp [canonicalFiniteEventCellularLocalPath, hchoice, fallback]
    | some key =>
        simp only at hchoice
        rcases hchoice with ⟨htiming, hlabels⟩
        have hmembership : z ∈ cell key.1 key.2 := ⟨htiming, hlabels⟩
        have hvalue : (fun index : Fin (cutoff + 1) => z.1 index.val) = key.2 := by
          funext index
          exact hlabels index
        simp [canonicalFiniteEventCellularLocalPath, htiming.1, hmembership, hvalue]

/-- The range of a finite-event cellular local path is separable in the
local `J₁` topology.  The path is either a fixed fallback or belongs to one
of countably many cells, each parametrized continuously by a finite vector
of knot times in an open unit-time slab. -/
theorem isSeparable_range_canonicalFiniteEventCellularLocalPath
    {Label State : Type*} [Countable Label] [PseudoMetricSpace State] [Zero State]
    (cutoff : ℕ) (values : (Fin (cutoff + 1) → Label) → Fin (cutoff + 1) → State) :
    letI : UniformSpace (SkorokhodJ1LocalPath State) :=
      AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.uniformSpace (State := State)
    TopologicalSpace.IsSeparable
      (Set.range (canonicalFiniteEventCellularLocalPath cutoff values)) := by
  classical
  letI : UniformSpace (SkorokhodJ1LocalPath State) :=
    AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.uniformSpace (State := State)
  let fallback : SkorokhodJ1LocalPath State :=
    SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const
  let cellRange : Option ((Fin cutoff → ℕ) × (Fin (cutoff + 1) → Label)) →
      Set (SkorokhodJ1LocalPath State) := fun choice => match choice with
    | none => {fallback}
    | some key => Set.range (fun times : AppliedModelingLib.Probability.localUnitSlab key.1 =>
        AppliedModelingLib.Probability.finiteStepLocalPath times.1.1 (values key.2) times.1.2.2)
  have hcellRange : ∀ choice, TopologicalSpace.IsSeparable (cellRange choice) := by
    intro choice
    cases choice with
    | none => exact (Set.countable_singleton fallback).isSeparable
    | some key =>
        exact TopologicalSpace.isSeparable_range
          (AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.continuous_finiteStepLocalPath_on_localUnitSlab
            key.1 (values key.2))
  refine (TopologicalSpace.IsSeparable.iUnion hcellRange).mono ?_
  rintro path ⟨z, rfl⟩
  by_cases hgood : canonicalFiniteEventStepGood cutoff z.2
  · let slabs : Fin cutoff → ℕ := fun index =>
      Nat.floor (PoissonProcess.arrivalTime index.val z.2)
    let labels : Fin (cutoff + 1) → Label := fun index => z.1 index.val
    have hslabs : ∀ index,
        (slabs index : ℝ) < PoissonProcess.arrivalTime index.val z.2 ∧
          PoissonProcess.arrivalTime index.val z.2 < (slabs index : ℝ) + 1 := by
      intro index
      constructor
      · exact lt_of_le_of_ne (Nat.floor_le (hgood.1 index).le)
          (hgood.2.2 index (slabs index)).symm
      · simpa [slabs] using
          (Nat.lt_floor_add_one (PoissonProcess.arrivalTime index.val z.2))
    let times : AppliedModelingLib.Probability.localUnitSlab slabs :=
      ⟨⟨fun index => PoissonProcess.arrivalTime index.val z.2,
        ⟨hgood.1, hgood.2.1⟩⟩, hslabs⟩
    refine Set.mem_iUnion.mpr ⟨some (slabs, labels), ?_⟩
    refine ⟨times, ?_⟩
    simp only [canonicalFiniteEventCellularLocalPath, dif_pos hgood]
    dsimp [times, labels]
  · refine Set.mem_iUnion.mpr ⟨none, ?_⟩
    simp [cellRange, canonicalFiniteEventCellularLocalPath, hgood, fallback]

/-- A finite prefix of a positive-rate canonical exponential renewal clock is
almost surely positive, strictly ordered, and disjoint from integer
restriction horizons. -/
theorem ae_canonicalFiniteEventStepGood_exponential
    (rate : ℝ) (hrate : 0 < rate) (cutoff : ℕ) :
    ∀ᵐ gaps ∂PoissonProcess.exponentialInterarrivalMeasure rate,
      canonicalFiniteEventStepGood cutoff gaps := by
  have hboundary : ∀ᵐ gaps ∂PoissonProcess.exponentialInterarrivalMeasure rate,
      ∀ index : Fin cutoff, ∀ horizon : ℕ,
        PoissonProcess.arrivalTime index.val gaps ≠ (horizon : ℝ) := by
    rw [ae_all_iff]
    intro index
    rw [ae_all_iff]
    intro horizon
    rw [ae_iff]
    simpa only [not_not] using
      (PoissonProcess.arrivalTime_measure_singleton_eq_zero hrate index.val (horizon : ℝ))
  filter_upwards [PoissonProcess.ae_all_arrivalTime_positive hrate,
    PoissonProcess.ae_arrivalTime_strictMono hrate, hboundary] with gaps hpositive hstrict hboundary
  refine ⟨?_, ?_, hboundary⟩
  · intro index
    exact hpositive index.val
  · intro first second hfirst_second
    exact hstrict (by simpa using hfirst_second)

/-- The finite renewal-prefix regularity event persists after product coupling
to any independent input carrying countable embedded labels. -/
theorem ae_canonicalFiniteEventStepGood_exponential_prod
    {Label : Type*} [MeasurableSpace Label]
    (input : Measure (ℕ → Label)) [IsProbabilityMeasure input]
    (rate : ℝ) (hrate : 0 < rate) (cutoff : ℕ) :
    ∀ᵐ z ∂input.prod (PoissonProcess.exponentialInterarrivalMeasure rate),
      canonicalFiniteEventStepGood cutoff z.2 := by
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure rate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ae_of_ae_map
    (μ := input.prod (PoissonProcess.exponentialInterarrivalMeasure rate))
    (f := Prod.snd)
    (p := fun gaps : ℕ → ℝ => canonicalFiniteEventStepGood cutoff gaps)
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  exact ae_canonicalFiniteEventStepGood_exponential rate hrate cutoff

/-- Every fixed finite active-prefix cell is measurable on the product input
space. -/
theorem measurableSet_canonicalFiniteEventActiveCell
    (horizon cutoff : ℕ) (active : Fin (cutoff + 1)) :
    MeasurableSet (canonicalFiniteEventActiveCell horizon cutoff active) := by
  have hgood : MeasurableSet {z : (ℕ → ℕ) × (ℕ → ℝ) |
      canonicalFiniteEventStepGood cutoff z.2} :=
    (measurableSet_canonicalFiniteEventStepGood cutoff).preimage measurable_snd
  have hbefore : MeasurableSet {z : (ℕ → ℕ) × (ℕ → ℝ) |
      ∀ index : Fin active.val,
        PoissonProcess.arrivalTime index.val z.2 < (horizon : ℝ)} := by
    rw [show {z : (ℕ → ℕ) × (ℕ → ℝ) |
        ∀ index : Fin active.val,
          PoissonProcess.arrivalTime index.val z.2 < (horizon : ℝ)} =
        ⋂ index : Fin active.val,
          {z | PoissonProcess.arrivalTime index.val z.2 < (horizon : ℝ)} by
      ext z
      simp]
    refine MeasurableSet.iInter fun index => ?_
    exact measurableSet_lt
      ((PoissonProcess.measurable_arrivalTime index.val).comp measurable_snd)
      measurable_const
  have hafter : MeasurableSet {z : (ℕ → ℕ) × (ℕ → ℝ) |
      active.val < cutoff →
        (horizon : ℝ) < PoissonProcess.arrivalTime active.val z.2} := by
    by_cases hactive : active.val < cutoff
    · simpa [hactive] using measurableSet_lt measurable_const
        ((PoissonProcess.measurable_arrivalTime active.val).comp measurable_snd)
    · simp [hactive]
  exact hgood.inter (hbefore.inter hafter)

/-- The countable conjunction of finite active-prefix cells is measurable. -/
theorem measurableSet_canonicalFiniteEventGlobalGood (cutoff : ℕ) :
    MeasurableSet {z : (ℕ → ℕ) × (ℕ → ℝ) |
      canonicalFiniteEventGlobalGood cutoff z} := by
  rw [show {z : (ℕ → ℕ) × (ℕ → ℝ) |
      canonicalFiniteEventGlobalGood cutoff z} =
      ⋂ horizon : ℕ, ⋃ active : Fin (cutoff + 1),
        canonicalFiniteEventActiveCell horizon cutoff active by
    ext z
    simp [canonicalFiniteEventGlobalGood]]
  exact MeasurableSet.iInter fun horizon => MeasurableSet.iUnion fun active =>
    measurableSet_canonicalFiniteEventActiveCell horizon cutoff active

/-- A local-path version built from the finite canonical step path on the
globally good event and from the zero path elsewhere.  The event is chosen
simultaneously for all integer horizons so this is one coherent local path. -/
noncomputable def manyServerCenteredSqrtCanonicalTruncatedCellularPath
    (servers cutoff : ℕ) (z : (ℕ → ℕ) × (ℕ → ℝ)) : SkorokhodJ1LocalPath ℝ := by
  classical
  exact if hgood : canonicalFiniteEventGlobalGood cutoff z then
    AppliedModelingLib.Probability.finiteStepLocalPath
      (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
      (fun index : Fin (cutoff + 1) =>
        ((z.1 index.val : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
      (by
        rcases hgood 0 with ⟨active, hactive⟩
        exact hactive.1.2.1)
  else
    SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const

/-- On an active-prefix cell, the cellular local path has precisely the
finite prefix representation on the corresponding observed interval. -/
theorem manyServerCenteredSqrtCanonicalTruncatedCellularPath_eq_prefix_on_cell
    (servers horizon cutoff : ℕ) (active : Fin (cutoff + 1))
    (z : (ℕ → ℕ) × (ℕ → ℝ))
    (hglobal : canonicalFiniteEventGlobalGood cutoff z)
    (hactive : z ∈ canonicalFiniteEventActiveCell horizon cutoff active)
    (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) (horizon : ℝ)) :
    (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict horizon time =
      AppliedModelingLib.Probability.finiteStepPath
        (fun index : Fin active.val =>
          PoissonProcess.arrivalTime
            (Fin.castLE (Nat.lt_succ_iff.mp active.isLt) index).val z.2)
        (fun index : Fin (active.val + 1) =>
          ((z.1 (Fin.castLE (Nat.succ_le_succ (Nat.lt_succ_iff.mp active.isLt)) index).val : ℝ) -
            (servers : ℝ)) / Real.sqrt (servers : ℝ)) time := by
  have hprefix : active.val ≤ cutoff := Nat.lt_succ_iff.mp active.isLt
  have hafter : ∀ index : Fin cutoff, active.val ≤ index.val →
      (horizon : ℝ) < PoissonProcess.arrivalTime index.val z.2 := by
    intro index hactive_index
    by_cases hfull : active.val = cutoff
    · exact False.elim ((not_lt_of_ge hactive_index)
        (by simpa [hfull] using index.isLt))
    · have hactive_lt : active.val < cutoff := lt_of_le_of_ne hprefix hfull
      have hfirst : (horizon : ℝ) <
          PoissonProcess.arrivalTime active.val z.2 := hactive.2.2 hactive_lt
      have hmono : Monotone (fun index : Fin cutoff =>
          PoissonProcess.arrivalTime index.val z.2) := hactive.1.2.1.monotone
      have hcast : active.val < cutoff := hactive_lt
      let activeIndex : Fin cutoff := ⟨active.val, hcast⟩
      have hactive_le : activeIndex ≤ index := by
        exact Fin.le_iff_val_le_val.mpr hactive_index
      exact hfirst.trans_le (hmono hactive_le)
  simpa [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hglobal] using
    (AppliedModelingLib.Probability.finiteStepPath_eq_prefix_of_after
      (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
      (fun index : Fin (cutoff + 1) =>
        ((z.1 index.val : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
      hprefix (horizon : ℝ) hafter htime.2)

/-- Every positive integer-horizon restriction of the cellular finite-event
local path is Borel measurable. -/
theorem measurable_manyServerCenteredSqrtCanonicalTruncatedCellularPath_restrict_pos
    (servers cutoff horizon : ℕ) (hhorizon : 0 < horizon) :
    letI : UniformSpace (SkorokhodJ1Path (horizon : ℝ) ℝ) :=
      SkorokhodJ1Entourage.uniformSpace (State := ℝ) (horizon : ℝ)
    letI : MeasurableSpace (SkorokhodJ1Path (horizon : ℝ) ℝ) :=
      SkorokhodJ1Entourage.borelMeasurableSpace (State := ℝ) (horizon : ℝ)
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict horizon) := by
  classical
  letI : UniformSpace (SkorokhodJ1Path (horizon : ℝ) ℝ) :=
    SkorokhodJ1Entourage.uniformSpace (State := ℝ) (horizon : ℝ)
  letI : MeasurableSpace (SkorokhodJ1Path (horizon : ℝ) ℝ) :=
    SkorokhodJ1Entourage.borelMeasurableSpace (State := ℝ) (horizon : ℝ)
  let globalSet : Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
    {z | canonicalFiniteEventGlobalGood cutoff z}
  let cellSet : Fin (cutoff + 1) → Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
    fun active => globalSet ∩ canonicalFiniteEventActiveCell horizon cutoff active
  let fallback : SkorokhodJ1Path (horizon : ℝ) ℝ :=
    (SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const).restrict horizon
  have hglobalSet : MeasurableSet globalSet := by
    exact measurableSet_canonicalFiniteEventGlobalGood cutoff
  have hcellSet : ∀ active, MeasurableSet (cellSet active) := by
    intro active
    exact hglobalSet.inter
      (measurableSet_canonicalFiniteEventActiveCell horizon cutoff active)
  have hcellBundle : ∀ active,
      Measurable (fun z : cellSet active =>
        (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z.1).restrict horizon) := by
    intro active
    let hprefix : active.val ≤ cutoff := Nat.lt_succ_iff.mp active.isLt
    let knots : cellSet active →
        AppliedModelingLib.Probability.OrderedInteriorKnotFamily (horizon : ℝ) active.val :=
      fun z => ⟨fun index => PoissonProcess.arrivalTime
          (Fin.castLE hprefix index).val z.1.2, by
        refine ⟨?_, ?_, ?_⟩
        · intro index
          simpa [hprefix] using z.2.2.1.1 (Fin.castLE hprefix index)
        · intro index
          simpa [hprefix] using z.2.2.2.1 index
        · intro first second hfirst_second
          exact z.2.2.1.2.1 (by simpa [hprefix] using hfirst_second)⟩
    let labels : cellSet active → Fin (active.val + 1) → ℕ :=
      fun z index => z.1.1 (Fin.castLE (Nat.succ_le_succ hprefix) index).val
    have hknots : Measurable knots := by
      apply Measurable.subtype_mk
      exact measurable_pi_lambda _ fun index =>
        (PoissonProcess.measurable_arrivalTime
          (Fin.castLE hprefix index).val).comp
          (measurable_snd.comp measurable_subtype_coe)
    have hlabels : Measurable labels := by
      refine measurable_pi_lambda _ fun index => ?_
      have hinput : Measurable (fun z : cellSet active => z.1.1) :=
        measurable_fst.comp measurable_subtype_coe
      simpa [labels] using
        hinput.eval (a := (Fin.castLE (Nat.succ_le_succ hprefix) index).val)
    refine AppliedModelingLib.Probability.measurable_finiteStepBundle_of_countable_labels
      knots labels
      (fun state : ℕ => ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
      (fun z =>
        (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z.1).restrict horizon)
      hknots hlabels ?_ (Nat.cast_nonneg horizon) (Nat.cast_pos.mpr hhorizon)
    intro z time htime
    simpa [knots, labels, hprefix] using
      (manyServerCenteredSqrtCanonicalTruncatedCellularPath_eq_prefix_on_cell
        servers horizon cutoff active z.1 z.2.1 z.2.2 time htime)
  have hcellExtension : ∀ active,
      Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        if hcell : z ∈ cellSet active then
          (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict horizon
        else fallback) := by
    intro active
    simpa only using
      (Measurable.dite (hcellBundle active) measurable_const (hcellSet active))
  refine AppliedModelingLib.Probability.measurable_of_countable_measurable_cover
    (fun choice : Option (Fin (cutoff + 1)) => match choice with
      | none => globalSetᶜ
      | some active => cellSet active)
    ?_ ?_
    (fun z =>
      (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict horizon)
    (fun choice z => match choice with
      | none => fallback
      | some active => if hcell : z ∈ cellSet active then
          (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict horizon
        else fallback)
    ?_ ?_
  · intro choice
    cases choice with
    | none => exact hglobalSet.compl
    | some active => exact hcellSet active
  · ext z
    constructor
    · intro _
      simp
    · intro _
      by_cases hglobal : z ∈ globalSet
      · change canonicalFiniteEventGlobalGood cutoff z at hglobal
        rcases hglobal horizon with ⟨active, hactive⟩
        exact Set.mem_iUnion.mpr ⟨some active, ⟨hglobal, hactive⟩⟩
      · exact Set.mem_iUnion.mpr ⟨none, hglobal⟩
  · intro choice
    cases choice with
    | none => exact measurable_const
    | some active => exact hcellExtension active
  · intro choice z hchoice
    cases choice with
    | none =>
        change ¬ canonicalFiniteEventGlobalGood cutoff z at hchoice
        change (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict horizon =
          fallback
        rw [show manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
            SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const by
          simp [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hchoice]]
    | some active =>
        simp only at hchoice
        simp [hchoice]

/-- The zero-horizon restriction of the cellular finite-event path is Borel
measurable.  On the good event, strictly positive arrival times leave only the
initial embedded state visible at time zero. -/
theorem measurable_manyServerCenteredSqrtCanonicalTruncatedCellularPath_restrict_zero
    (servers cutoff : ℕ) :
    letI : UniformSpace (SkorokhodJ1Path ((0 : ℕ) : ℝ) ℝ) :=
      SkorokhodJ1Entourage.uniformSpace (State := ℝ) ((0 : ℕ) : ℝ)
    letI : MeasurableSpace (SkorokhodJ1Path ((0 : ℕ) : ℝ) ℝ) :=
      SkorokhodJ1Entourage.borelMeasurableSpace (State := ℝ) ((0 : ℕ) : ℝ)
    Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict 0) := by
  classical
  letI : UniformSpace (SkorokhodJ1Path ((0 : ℕ) : ℝ) ℝ) :=
    SkorokhodJ1Entourage.uniformSpace (State := ℝ) ((0 : ℕ) : ℝ)
  letI : MeasurableSpace (SkorokhodJ1Path ((0 : ℕ) : ℝ) ℝ) :=
    SkorokhodJ1Entourage.borelMeasurableSpace (State := ℝ) ((0 : ℕ) : ℝ)
  let globalSet : Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
    {z | canonicalFiniteEventGlobalGood cutoff z}
  let fallback : SkorokhodJ1Path ((0 : ℕ) : ℝ) ℝ :=
    (SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const).restrict 0
  have hglobalSet : MeasurableSet globalSet := by
    exact measurableSet_canonicalFiniteEventGlobalGood cutoff
  have hlabels : Measurable (fun z : globalSet => z.1.1 0) := by
    have hinput : Measurable (fun z : globalSet => z.1.1) :=
      measurable_fst.comp measurable_subtype_coe
    simpa using hinput.eval (a := 0)
  have hglobalBundle : Measurable (fun z : globalSet =>
      (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z.1).restrict 0) := by
    refine AppliedModelingLib.Probability.measurable_zeroHorizonBundle_of_countable_labels
      (fun z : globalSet => z.1.1 0)
      (fun state : ℕ => ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
      (fun z =>
        (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z.1).restrict 0)
      hlabels ?_
    intro z
    have hgood : canonicalFiniteEventGlobalGood cutoff z.1 := z.2
    rw [SkorokhodJ1LocalPath.restrict_apply]
    rw [show manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z.1 =
        AppliedModelingLib.Probability.finiteStepLocalPath
          (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.1.2)
          (fun index : Fin (cutoff + 1) =>
            ((z.1.1 index.val : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
          (by
            rcases hgood 0 with ⟨active, hactive⟩
            exact hactive.1.2.1) by
      simp [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hgood]]
    rw [AppliedModelingLib.Probability.finiteStepLocalPath_apply]
    rw [AppliedModelingLib.Probability.finiteStepPath_zero_eq_firstValue_of_all_pos]
    · rfl
    · intro index
      rcases hgood 0 with ⟨active, hactive⟩
      exact hactive.1.1 index
  have hpiece : Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      if hgood : z ∈ globalSet then
        (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z).restrict 0
      else fallback) := by
    simpa only using (Measurable.dite hglobalBundle measurable_const hglobalSet)
  convert hpiece using 1
  funext z
  by_cases hgood : z ∈ globalSet
  · simp [hgood]
  · simp only [dif_neg hgood]
    change ¬ canonicalFiniteEventGlobalGood cutoff z at hgood
    rw [show manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
        SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const by
      simp [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hgood]]

/-- The finite-event cellular canonical path is Borel measurable for the
exact local `J₁` Borel structure.  Countably many open unit-time slabs make
the active prefix at every integer horizon locally stable. -/
theorem measurable_manyServerCenteredSqrtCanonicalTruncatedCellularPath
    (servers cutoff : ℕ) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    Measurable (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff) := by
  classical
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  let globalSet : Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
    {z | canonicalFiniteEventGlobalGood cutoff z}
  let fallback : SkorokhodJ1LocalPath ℝ :=
    SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const
  let cell : (Fin cutoff → ℕ) → (Fin (cutoff + 1) → ℕ) →
      Set ((ℕ → ℕ) × (ℕ → ℝ)) :=
    fun slabs labels => canonicalFiniteEventLocalUnitLabelCell cutoff slabs labels
  have hglobalSet : MeasurableSet globalSet := by
    exact measurableSet_canonicalFiniteEventGlobalGood cutoff
  have hcellSet : ∀ slabs labels, MeasurableSet (cell slabs labels) := by
    intro slabs labels
    exact measurableSet_canonicalFiniteEventLocalUnitLabelCell cutoff slabs labels
  have hcellBundle : ∀ slabs labels,
      Measurable (fun z : cell slabs labels =>
        AppliedModelingLib.Probability.finiteStepLocalPath
          (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.1.2)
          (fun index : Fin (cutoff + 1) =>
            ((labels index : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
          z.2.1.1.2.1) := by
    intro slabs labels
    let times : cell slabs labels →
        AppliedModelingLib.Probability.localUnitSlab slabs :=
      fun z => ⟨⟨fun index => PoissonProcess.arrivalTime index.val z.1.2,
        ⟨z.2.1.1.1, z.2.1.1.2.1⟩⟩, z.2.1.2⟩
    have htimes : Measurable times := by
      apply Measurable.subtype_mk
      apply Measurable.subtype_mk
      exact (measurable_canonicalFiniteEventArrivalVector cutoff).comp
        (measurable_snd.comp measurable_subtype_coe)
    have hbase := AppliedModelingLib.Probability.SkorokhodJ1LocalEntourage.measurable_finiteStepLocalPath_on_localUnitSlab
      slabs (fun index : Fin (cutoff + 1) =>
        ((labels index : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
    simpa [times] using hbase.comp htimes
  have hcellExtension : ∀ slabs labels,
      Measurable (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        if hcell : z ∈ cell slabs labels then
          AppliedModelingLib.Probability.finiteStepLocalPath
            (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
            (fun index : Fin (cutoff + 1) =>
              ((labels index : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
            hcell.1.1.2.1
        else fallback) := by
    intro slabs labels
    simpa only using (Measurable.dite (hcellBundle slabs labels) measurable_const
      (hcellSet slabs labels))
  refine AppliedModelingLib.Probability.measurable_of_countable_measurable_cover
    (fun choice : Option ((Fin cutoff → ℕ) × (Fin (cutoff + 1) → ℕ)) => match choice with
      | none => globalSetᶜ
      | some key => cell key.1 key.2)
    ?_ ?_
    (manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff)
    (fun choice z => match choice with
      | none => fallback
      | some key => if hcell : z ∈ cell key.1 key.2 then
          AppliedModelingLib.Probability.finiteStepLocalPath
            (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
            (fun index : Fin (cutoff + 1) =>
              ((key.2 index : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
            hcell.1.1.2.1
        else fallback)
    ?_ ?_
  · intro choice
    cases choice with
    | none => exact hglobalSet.compl
    | some key => exact hcellSet key.1 key.2
  · ext z
    constructor
    · intro _
      simp
    · intro _
      by_cases hglobal : z ∈ globalSet
      · have hgood : canonicalFiniteEventStepGood cutoff z.2 :=
          (canonicalFiniteEventGlobalGood_iff_stepGood cutoff z).mp hglobal
        let slabs : Fin cutoff → ℕ := fun index =>
          Nat.floor (PoissonProcess.arrivalTime index.val z.2)
        let labels : Fin (cutoff + 1) → ℕ := fun index => z.1 index.val
        refine Set.mem_iUnion.mpr ⟨some (slabs, labels), ?_⟩
        change z ∈ canonicalFiniteEventLocalUnitLabelCell cutoff slabs labels
        refine ⟨?_, ?_⟩
        · refine ⟨hgood, ?_⟩
          intro index
          constructor
          · exact lt_of_le_of_ne (Nat.floor_le (hgood.1 index).le)
              (hgood.2.2 index (slabs index)).symm
          · simpa [slabs] using
              (Nat.lt_floor_add_one (PoissonProcess.arrivalTime index.val z.2))
        · intro index
          rfl
      · exact Set.mem_iUnion.mpr ⟨none, hglobal⟩
  · intro choice
    cases choice with
    | none => exact measurable_const
    | some key => exact hcellExtension key.1 key.2
  · intro choice z hchoice
    cases choice with
    | none =>
        change ¬ canonicalFiniteEventGlobalGood cutoff z at hchoice
        rw [show manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
            SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const by
          simp [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hchoice]]
    | some key =>
        simp only at hchoice
        rcases hchoice with ⟨hcell, hlabels⟩
        have hmembership : z ∈ cell key.1 key.2 := ⟨hcell, hlabels⟩
        have hglobal : canonicalFiniteEventGlobalGood cutoff z :=
          (canonicalFiniteEventGlobalGood_iff_stepGood cutoff z).mpr hcell.1
        change manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
          if hcell : z ∈ cell key.1 key.2 then
            AppliedModelingLib.Probability.finiteStepLocalPath
              (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
              (fun index : Fin (cutoff + 1) =>
                ((key.2 index : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
              hcell.1.1.2.1
          else fallback
        rw [dif_pos hmembership]
        rw [show manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
            AppliedModelingLib.Probability.finiteStepLocalPath
              (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
              (fun index : Fin (cutoff + 1) =>
                ((z.1 index.val : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
              hcell.1.2.1 by
          simp [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hglobal]]
        congr 2
        funext index
        simpa [hlabels index]

/-- Under a positive canonical exponential clock, every fixed finite renewal
vector lies almost surely in one of the open unit-time slabs used by the
cellular local-`J₁` construction. -/
theorem ae_canonicalFiniteEventGlobalGood
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      canonicalFiniteEventGlobalGood cutoff z := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  let clockMeasure := PoissonProcess.exponentialInterarrivalMeasure
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
  letI : IsProbabilityMeasure clockMeasure :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hboundary : ∀ᵐ gaps ∂clockMeasure,
      ∀ index : Fin cutoff, ∀ horizon : ℕ,
        PoissonProcess.arrivalTime index.val gaps ≠ (horizon : ℝ) := by
    rw [ae_all_iff]
    intro index
    rw [ae_all_iff]
    intro horizon
    rw [ae_iff]
    simpa only [not_not] using
      (PoissonProcess.arrivalTime_measure_singleton_eq_zero hrate index.val (horizon : ℝ))
  have hgood : ∀ᵐ gaps ∂clockMeasure,
      canonicalFiniteEventStepGood cutoff gaps := by
    filter_upwards [PoissonProcess.ae_all_arrivalTime_positive hrate,
      PoissonProcess.ae_arrivalTime_strictMono hrate, hboundary] with gaps hpositive hstrict hboundary
    refine ⟨?_, ?_, hboundary⟩
    · intro index
      exact hpositive index.val
    · intro first second hfirst_second
      exact hstrict (by simpa using hfirst_second)
  refine ae_of_ae_map
    (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod clockMeasure)
    (f := Prod.snd)
    (p := fun gaps : ℕ → ℝ => canonicalFiniteEventGlobalGood cutoff (0, gaps))
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  filter_upwards [hgood] with gaps hgood_gaps
  exact (canonicalFiniteEventGlobalGood_iff_stepGood cutoff (0, gaps)).mpr hgood_gaps

/-- The càdlàg-path-valued version agrees almost surely, coordinatewise, with
the concrete centered square-root canonical trajectory. -/
theorem ae_forall_manyServerCenteredSqrtCanonicalCadlagPath_eq
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ time : ℝ, manyServerCenteredSqrtCanonicalCadlagPath servers z time =
        manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z time := by
  filter_upwards [ae_isCadlagOn_manyServerCenteredSqrtCanonicalTrajectory
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate] with z hz
  intro time
  simp [manyServerCenteredSqrtCanonicalCadlagPath, hz, IsCadlagOn.toCadlagPathOn]

/-- On its common càdlàg event, the total finite-event truncation agrees at
every time with the literal truncated canonical trajectory. -/
theorem ae_forall_manyServerCenteredSqrtCanonicalTruncatedCadlagPath_eq
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ time : ℝ,
        manyServerCenteredSqrtCanonicalTruncatedCadlagPath servers cutoff z time =
          manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z time := by
  filter_upwards [
    ae_isCadlagPath_manyServerCenteredSqrtCanonicalTruncatedTrajectory_on_real
      (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate]
    with z hcadlag
  intro time
  have hcadlagOn : IsCadlagOn (Set.Ici (0 : ℝ))
      (manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z) :=
    hcadlag.on_of_isCadlagPath (Set.Ici 0)
  simp [manyServerCenteredSqrtCanonicalTruncatedCadlagPath,
    hcadlagOn, IsCadlagOn.toCadlagPathOn]

/-- The bundled finite-event truncation agrees almost surely, at every real
time, with its literal finite-event trajectory. -/
theorem ae_forall_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath_eq
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ time : ℝ,
        manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z time =
          manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z time := by
  filter_upwards [
    ae_forall_manyServerCenteredSqrtCanonicalTruncatedCadlagPath_eq
      (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate]
    with z hvalue
  intro time
  simpa [manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath] using hvalue time

/-- The Borel cellular finite-event representative agrees almost surely with
the existing total bundled truncation. -/
theorem ae_manyServerCenteredSqrtCanonicalTruncatedCellularPath_eq
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
        manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  let clockMeasure := PoissonProcess.exponentialInterarrivalMeasure
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
  letI : IsProbabilityMeasure clockMeasure :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hdivergesGaps : ∀ᵐ gaps ∂clockMeasure,
      Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gaps) atTop atTop :=
    PoissonProcess.ae_arrivalTime_tendsto_atTop hrate
  have hstrictGaps : ∀ᵐ gaps ∂clockMeasure,
      StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index gaps) :=
    PoissonProcess.ae_arrivalTime_strictMono hrate
  have hdiverges : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod clockMeasure,
      Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index z.2) atTop atTop := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod clockMeasure)
      (f := Prod.snd)
      (p := fun gaps : ℕ → ℝ =>
        Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gaps) atTop atTop)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hdivergesGaps
  have hstrict : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod clockMeasure,
      StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index z.2) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod clockMeasure)
      (f := Prod.snd)
      (p := fun gaps : ℕ → ℝ =>
        StrictMono (fun index : ℕ => PoissonProcess.arrivalTime index gaps))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hstrictGaps
  filter_upwards [
    ae_canonicalFiniteEventGlobalGood
      (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate,
    hdiverges, hstrict,
    ae_forall_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath_eq
      (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate]
    with z hglobal hdiverges_z hstrict_z htotal
  apply SkorokhodJ1LocalPath.ext
  intro time
  have hgood : canonicalFiniteEventStepGood cutoff z.2 :=
    (canonicalFiniteEventGlobalGood_iff_stepGood cutoff z).mp hglobal
  rw [show manyServerCenteredSqrtCanonicalTruncatedCellularPath servers cutoff z =
      AppliedModelingLib.Probability.finiteStepLocalPath
        (fun index : Fin cutoff => PoissonProcess.arrivalTime index.val z.2)
        (fun index : Fin (cutoff + 1) =>
          ((z.1 index.val : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
        hgood.2.1 by
    simp [manyServerCenteredSqrtCanonicalTruncatedCellularPath, hglobal]]
  rw [finiteStepLocalPath_arrivalTimes_eq_truncatedCanonicalRenewalTrajectory
    (fun index : ℕ => ((z.1 index : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))
    cutoff z.2 hdiverges_z hstrict_z time]
  exact (htotal time).symm

/-- For each compact forward-time interval, sufficiently large finite-event
truncations agree almost surely with the full centered canonical path at every
time in that interval. -/
theorem ae_eventually_truncatedCanonicalSkorokhodPath_eq_on_Icc
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (horizon : ℕ) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ᶠ cutoff : ℕ in atTop, ∀ time ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
        manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z time =
          manyServerCenteredSqrtCanonicalSkorokhodPath servers z time := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hmono_gaps : ∀ᵐ gaps ∂PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers),
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gaps) :=
    PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  have hmono : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time z.2) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))
      (f := Prod.snd)
      (p := fun gaps : ℕ → ℝ => Monotone (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gaps))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  have htruncated : ∀ᵐ z ∂
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ cutoff : ℕ, ∀ time : ℝ,
        manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z time =
          manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal servers cutoff z time := by
    exact ae_all_iff.mpr fun cutoff =>
      ae_forall_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath_eq
        (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate
  have horiginal : ∀ᵐ z ∂
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ time : ℝ, manyServerCenteredSqrtCanonicalSkorokhodPath servers z time =
        manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z time := by
    filter_upwards [ae_forall_manyServerCenteredSqrtCanonicalCadlagPath_eq
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate]
      with z hvalue
    intro time
    simpa [manyServerCenteredSqrtCanonicalSkorokhodPath] using hvalue time
  filter_upwards [hmono, htruncated, horiginal] with z hmono_z htruncated_z horiginal_z
  filter_upwards [Filter.eventually_ge_atTop
    (PoissonProcess.canonicalRenewalCount (horizon : ℝ) z.2)] with cutoff hcutoff time htime
  have hcount : PoissonProcess.canonicalRenewalCount time z.2 ≤ cutoff :=
    (hmono_z htime.2).trans hcutoff
  rw [htruncated_z cutoff time, horiginal_z time]
  simp [manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal,
    manyServerCenteredSqrtCanonicalTrajectoryOnReal, manyServerCenteredSqrtPath,
    manyServerCanonicalQueueLengthOnReal, min_eq_left hcount]

/-- The deterministic finite-event truncations converge almost surely to the
full centered canonical path in local Skorokhod `J₁`.  This is a pathwise
nonexplosion result; it does not by itself establish Borel measurability of
the truncation maps or any weak-convergence statement. -/
theorem ae_locallyConverges_manyServerCenteredSqrtCanonicalTruncatedPaths
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      SkorokhodJ1LocallyConverges
        (fun cutoff : ℕ =>
          manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z)
        (manyServerCenteredSqrtCanonicalSkorokhodPath servers z) := by
  have hcompacts : ∀ᵐ z ∂
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ horizon : ℕ, ∀ᶠ cutoff : ℕ in atTop,
        ∀ time ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
          manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z time =
            manyServerCenteredSqrtCanonicalSkorokhodPath servers z time := by
    exact ae_all_iff.mpr fun horizon =>
      ae_eventually_truncatedCanonicalSkorokhodPath_eq_on_Icc
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate horizon
  filter_upwards [hcompacts] with z hcompacts_z
  exact SkorokhodJ1LocallyConverges.of_eventually_eq_on_compacts hcompacts_z

/-- The local-`J₁` path-valued version agrees almost surely, coordinatewise,
with the concrete centered square-root canonical trajectory. -/
theorem ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      ∀ time : ℝ, manyServerCenteredSqrtCanonicalSkorokhodPath servers z time =
        manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z time := by
  filter_upwards [ae_forall_manyServerCenteredSqrtCanonicalCadlagPath_eq
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate] with z hz
  intro time
  simpa [manyServerCenteredSqrtCanonicalSkorokhodPath] using hz time

/-- After forgetting the local-`J₁` bundle, the total canonical path is
almost-everywhere measurable as a raw real-indexed product path.  The proof
uses the common càdlàg event, so it is a pathwise equality rather than an
uncountable intersection of coordinatewise null-set statements. -/
theorem aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath_asRawPath
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    AEMeasurable
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        (fun time : ℝ => manyServerCenteredSqrtCanonicalSkorokhodPath servers z time))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  exact (measurable_manyServerCenteredSqrtCanonicalTrajectoryOnReal servers).aemeasurable.congr
    ((ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate).mono
      (fun z hz => funext fun time => (hz time).symm))

/-- After forgetting the local-`J₁` bundle, a deterministic finite-event
truncation is almost-everywhere measurable as a raw real-indexed product
path. -/
theorem aemeasurable_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath_asRawPath
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    AEMeasurable
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        (fun time : ℝ =>
          manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z time))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  exact (measurable_manyServerCenteredSqrtCanonicalTruncatedTrajectoryOnReal
    servers cutoff).aemeasurable.congr
    ((ae_forall_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath_eq
      (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate).mono
      (fun z hz => funext fun time => (hz time).symm))

/-- Every deterministic finite-event truncation is almost-everywhere Borel
measurable for the exact local `J₁` Borel structure. -/
theorem aemeasurable_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers cutoff : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    AEMeasurable
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z)
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  exact (measurable_manyServerCenteredSqrtCanonicalTruncatedCellularPath
    servers cutoff).aemeasurable.congr
    (ae_manyServerCenteredSqrtCanonicalTruncatedCellularPath_eq
      (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate)

/-- To prove local-`J₁` Borel measurability of the full canonical path, it is
enough to prove it for every deterministic finite-event truncation.  The
conclusion then follows from the checked almost-sure local-`J₁` convergence of
those truncations. -/
theorem aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath_of_truncated
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (htruncated : letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
        SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
      letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
        SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
      ∀ cutoff : ℕ,
        AEMeasurable
          (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
            manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath servers cutoff z)
          ((manyServerUniformizedEmbeddedTrajectoryMeasure
            initial trafficIntensity servers hservers).prod
            (PoissonProcess.exponentialInterarrivalMeasure
              (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    AEMeasurable
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalSkorokhodPath servers z)
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  exact SkorokhodJ1LocallyConverges.aemeasurable_of_ae_locallyConverges
    htruncated
    (ae_locallyConverges_manyServerCenteredSqrtCanonicalTruncatedPaths
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)

/-- The canonical many-server path is almost-everywhere Borel measurable for
the exact local `J₁` Borel structure. -/
theorem aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    AEMeasurable
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalSkorokhodPath servers z)
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  apply aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath_of_truncated
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  intro cutoff
  exact aemeasurable_manyServerCenteredSqrtCanonicalTruncatedSkorokhodPath
    (initial := initial) trafficIntensity serviceRate servers cutoff hservers hserviceRate

/-- The total bundled canonical path and the concrete trajectory have the
same raw product-path law.  This is an exact law equality before the separate
identification of the raw path σ-algebra with the local-`J₁` Borel structure. -/
theorem map_manyServerCenteredSqrtCanonicalSkorokhodPath_asRawPath_eq
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    Measure.map
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        (fun time : ℝ => manyServerCenteredSqrtCanonicalSkorokhodPath servers z time))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) =
    Measure.map (manyServerCenteredSqrtCanonicalTrajectoryOnReal servers)
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  apply Measure.map_congr
  filter_upwards [ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate] with z hz
  funext time
  exact hz time

/-- A fixed coordinate of the total local-`J₁` path version is almost
everywhere measurable. This follows from its almost-sure equality with the
measurable concrete coordinate; measurability of the entire path map remains
separate. -/
theorem aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath_apply
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) (time : ℝ) :
    AEMeasurable
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalSkorokhodPath servers z time)
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  exact (measurable_manyServerCenteredSqrtCanonicalTrajectoryOnReal_apply
    servers time).aemeasurable.congr
    ((ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate).mono
      (fun z hz => (hz time).symm))

/-- On every compact forward-time interval, the canonical-clock uniformized
many-server state path has finite range almost surely. -/
theorem ae_finite_range_manyServerUniformizedCanonicalTrajectory_on_Icc
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (horizon : ℝ≥0) :
    ∀ᵐ z ∂((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))),
      (Set.range fun t : Set.Icc (0 : ℝ≥0) horizon => z.1
        ((manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count t.1 z.2)).Finite := by
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers
      hservers hserviceRate
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers) := by
    unfold manyServerUniformizedEmbeddedTrajectoryMeasure stationaryTrajMeasure
    infer_instance
  have hclock : ∀ᵐ omega ∂PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers),
      Monotone (fun t => (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate).count t omega) :=
    (manyServerCanonicalForwardPoissonClock
      trafficIntensity serviceRate servers hservers hserviceRate).count_mono
  have hlift : ∀ᵐ z : (ℕ → ℕ) × (ℕ → ℝ) ∂
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      Monotone (fun t => (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate).count t z.2) := by
    refine ae_of_ae_map
      (μ := (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)))
      (f := Prod.snd) (p := fun omega : ℕ → ℝ =>
        Monotone (fun t => (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate).count t omega))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with z hmonotone
  exact finite_range_timeChangedTrajectory_on_Icc z.1
    (fun t => (manyServerCanonicalForwardPoissonClock
      trafficIntensity serviceRate servers hservers hserviceRate).count t z.2)
    hmonotone horizon

/-- At time zero, the canonical-clock uniformized many-server state has its
specified initial law. -/
theorem manyServerUniformizedCanonicalTrajectoryAt_zero_hasLaw
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    HasLaw
      (stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
        (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate) 0)
      initial
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (manyServerUniformizedTrajectoryAtForwardPoissonCount_zero_hasLaw
      (initial := initial) trafficIntensity servers hservers
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate))

/-- The centered square-root coordinate at time zero of the canonical
many-server construction has exactly the affine image of the specified
initial law.  This is the initial-condition bridge used when a sequence of
scaled initial distributions converges. -/
theorem manyServerCenteredSqrtCanonicalTrajectoryAt_zero_hasLaw
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        ((stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
          (manyServerCanonicalForwardPoissonClock
            trafficIntensity serviceRate servers hservers hserviceRate) 0 z : ℝ) -
            (servers : ℝ)) / Real.sqrt (servers : ℝ))
      (initial.map (fun state : ℕ =>
        ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  let coordinate : ℕ → ℝ := fun state =>
    ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)
  have hcoordinate : Measurable coordinate :=
    continuous_of_discreteTopology.measurable
  have hcoordinateLaw : HasLaw coordinate (initial.map coordinate) initial :=
    ⟨hcoordinate.aemeasurable, rfl⟩
  have hstate := manyServerUniformizedCanonicalTrajectoryAt_zero_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  simpa [coordinate, Function.comp_def] using
    hcoordinateLaw.comp hstate

/-- The all-real-time centered canonical path has the same exact affine
initial law at time zero.  This identifies the initial coordinate of the raw
path representation with the initial law used by the embedded construction. -/
theorem manyServerCenteredSqrtCanonicalTrajectoryOnReal_zero_hasLaw
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z 0)
      (initial.map (fun state : ℕ =>
        ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  simpa [manyServerCenteredSqrtCanonicalTrajectoryOnReal,
    manyServerCenteredSqrtPath, manyServerCanonicalQueueLengthOnReal] using
    (manyServerCenteredSqrtCanonicalTrajectoryAt_zero_hasLaw
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)

/-- The time-zero evaluation of the bundled local-`J₁` canonical path has the
same affine initial law as the concrete queue coordinate. -/
theorem manyServerCenteredSqrtCanonicalSkorokhodPath_zero_hasLaw
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalSkorokhodPath servers z 0)
      (initial.map (fun state : ℕ =>
        ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  apply (manyServerCenteredSqrtCanonicalTrajectoryOnReal_zero_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate).congr
  filter_upwards [ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate]
    with z hz
  exact hz 0

/-- Every deterministic-time marginal of the stationary canonical-clock
uniformized many-server queue is its invariant embedded-chain law. This is a
product-space marginal statement; it does not by itself identify a
continuous-time Markov semigroup. -/
theorem manyServerUniformizedCanonicalStationaryTrajectoryAt_hasLaw
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (htraffic_lt_one : trafficIntensity < 1) (time : ℝ≥0) :
    HasLaw
      (stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
        (manyServerCanonicalForwardPoissonClock
          trafficIntensity serviceRate servers hservers hserviceRate) time)
      ((manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure)
      ((stationaryTrajMeasure
        ((manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure)
        (countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers))).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (stationaryTrajMeasure_eval_forwardPoissonCount_hasLaw
      (manyServer_uniformized_kernelInvariant trafficIntensity servers hservers htraffic_lt_one)
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate) time)

/-- At a deterministic time, the initial/current pair for the canonical-clock
uniformized many-server queue is the Poisson mixture of its embedded-chain
transition laws. -/
theorem manyServerUniformizedCanonicalTrajectoryAt_pair_mixture
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          (z.1 0, stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) t z)) s =
      ∫⁻ step, (initial ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ step)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            (t : ℝ)
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (NNReal.coe_nonneg t))) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (manyServerUniformizedTrajectoryAtForwardPoissonCount_pair_mixture
      (initial := initial) trafficIntensity servers hservers
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate) t s hs)

/-- The canonical-clock initial/current law in the explicit PMF-iterate form
of uniformization. This is the transition construction used to identify the
Poissonized continuous-time transition kernel below. -/
theorem manyServerUniformizedCanonicalTrajectoryAt_pair_mixture_iterate
    {initial : Measure ℕ} [IsProbabilityMeasure initial]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          (z.1 0, stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) t z)) s =
      ∫⁻ step, (initial ⊗ₘ countablePMFKernel
        ((manyServerUniformizedKernel trafficIntensity servers hservers).iterate step)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            (t : ℝ)
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (NNReal.coe_nonneg t))) := by
  simpa [manyServerUniformizedEmbeddedTrajectoryMeasure,
    manyServerCanonicalForwardPoissonClock] using
    (stationaryTrajMeasure_zero_forwardPoissonCount_pair_mixture_iterate
      (π := initial)
      (K := manyServerUniformizedKernel trafficIntensity servers hservers)
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate) t s hs)

/-- For a countable initial PMF, the canonical-clock initial/current pair has
the composition-product law of the Poissonized many-server transition kernel.
Together with `poissonizedKernel_comp`, this identifies the finite-dimensional
continuous-time transition semigroup, while path-space process identification
and diffusion convergence remain separate. -/
theorem manyServerUniformizedCanonicalTrajectoryAt_pair_poissonizedKernel
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          (z.1 0, stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) t z)) s =
      (initial.toMeasure ⊗ₘ CountableMarkovKernel.poissonizedKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers)
        (PoissonProcess.rateExposureParam
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
          (t : ℝ)
          (mul_nonneg
            (le_of_lt (manyServerUniformizationRate_pos
              trafficIntensity serviceRate servers hservers hserviceRate))
            (NNReal.coe_nonneg t)))) s := by
  rw [manyServerUniformizedCanonicalTrajectoryAt_pair_mixture_iterate
    (initial := initial.toMeasure) trafficIntensity serviceRate servers hservers hserviceRate t s hs]
  exact (CountableMarkovKernel.compProd_poissonizedKernel_apply_eq_lintegral_iterate
    initial (manyServerUniformizedKernel trafficIntensity servers hservers)
    (PoissonProcess.rateExposureParam
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
      (t : ℝ)
      (mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos
          trafficIntensity serviceRate servers hservers hserviceRate))
        (NNReal.coe_nonneg t))) s hs).symm

/-- At every deterministic time, the arbitrary-initial canonical M/M/s
trajectory has the corresponding row of the Poissonized potential-event
semigroup.  This is the one-time continuous-time transition law of the
concrete canonical path; its proof uses the exact initial/current pair law
above rather than postulating a CTMC. -/
theorem manyServerUniformizedCanonicalTrajectoryAt_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
          (manyServerCanonicalForwardPoissonClock
            trafficIntensity serviceRate servers hservers hserviceRate) t z)
      (initial.bind (CountableMarkovKernel.poissonized
        (manyServerUniformizedKernel trafficIntensity servers hservers)
        (PoissonProcess.rateExposureParam
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
          (t : ℝ)
          (mul_nonneg
            (le_of_lt (manyServerUniformizationRate_pos
              trafficIntensity serviceRate servers hservers hserviceRate))
            (NNReal.coe_nonneg t))))).toMeasure
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  let clock := manyServerCanonicalForwardPoissonClock
    trafficIntensity serviceRate servers hservers hserviceRate
  let mean := PoissonProcess.rateExposureParam
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
    (t : ℝ)
    (mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos
        trafficIntensity serviceRate servers hservers hserviceRate))
      (NNReal.coe_nonneg t))
  let kernel := manyServerUniformizedKernel trafficIntensity servers hservers
  let input := (manyServerUniformizedEmbeddedTrajectoryMeasure
    initial.toMeasure trafficIntensity servers hservers).prod
    (PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))
  let pair : ((ℕ → ℕ) × (ℕ → ℝ)) → ℕ × ℕ := fun z =>
    (z.1 0, stationaryTrajectoryAtForwardPoissonCount (α := ℕ) clock t z)
  have hpair_measurable : Measurable pair :=
    ((measurable_pi_apply 0).comp measurable_fst).prodMk
      (measurable_stationaryTrajectoryAtForwardPoissonCount (α := ℕ) clock t)
  have hpair : Measure.map pair input =
      initial.toMeasure ⊗ₘ CountableMarkovKernel.poissonizedKernel kernel mean := by
    ext s hs
    simpa [pair, input, clock, kernel, mean] using
      (manyServerUniformizedCanonicalTrajectoryAt_pair_poissonizedKernel
        initial trafficIntensity serviceRate servers hservers hserviceRate t s hs)
  refine ⟨(measurable_stationaryTrajectoryAtForwardPoissonCount
    (α := ℕ) clock t).aemeasurable, ?_⟩
  calc
    Measure.map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          stationaryTrajectoryAtForwardPoissonCount (α := ℕ) clock t z)
        input = Measure.map Prod.snd (Measure.map pair input) := by
          change Measure.map (Prod.snd ∘ pair) input =
            Measure.map Prod.snd (Measure.map pair input)
          rw [Measure.map_map measurable_snd hpair_measurable]
    _ = Measure.map Prod.snd
        (initial.toMeasure ⊗ₘ CountableMarkovKernel.poissonizedKernel kernel mean) := by
          rw [hpair]
    _ = (initial.bind (CountableMarkovKernel.poissonized kernel mean)).toMeasure := by
          change (initial.toMeasure ⊗ₘ
            countablePMFKernel (CountableMarkovKernel.poissonized kernel mean)).snd = _
          rw [Measure.snd_compProd,
            bind_countablePMFKernel_eq_pmf_bind_toMeasure]

/-- The centered square-root coordinate of the arbitrary-initial canonical
M/M/s queue at a deterministic time is the affine image of its Poissonized
semigroup marginal.  This makes the process-level scaling compatible with
the exact one-time transition law. -/
theorem manyServerCenteredSqrtCanonicalTrajectoryAt_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        ((stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
          (manyServerCanonicalForwardPoissonClock
            trafficIntensity serviceRate servers hservers hserviceRate) t z : ℝ) -
            (servers : ℝ)) / Real.sqrt (servers : ℝ))
      ((initial.bind (CountableMarkovKernel.poissonized
        (manyServerUniformizedKernel trafficIntensity servers hservers)
        (PoissonProcess.rateExposureParam
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
          (t : ℝ)
          (mul_nonneg
            (le_of_lt (manyServerUniformizationRate_pos
              trafficIntensity serviceRate servers hservers hserviceRate))
            (NNReal.coe_nonneg t))))).map (fun state : ℕ =>
          ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))).toMeasure
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  let clock := manyServerCanonicalForwardPoissonClock
    trafficIntensity serviceRate servers hservers hserviceRate
  let mean := PoissonProcess.rateExposureParam
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
    (t : ℝ)
    (mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos
        trafficIntensity serviceRate servers hservers hserviceRate))
      (NNReal.coe_nonneg t))
  let kernel := manyServerUniformizedKernel trafficIntensity servers hservers
  let stateLaw := initial.bind (CountableMarkovKernel.poissonized kernel mean)
  let coordinate : ℕ → ℝ := fun state =>
    ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ)
  have hstate : HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        stationaryTrajectoryAtForwardPoissonCount (α := ℕ) clock t z)
      stateLaw.toMeasure
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
    simpa [clock, mean, kernel, stateLaw] using
      (manyServerUniformizedCanonicalTrajectoryAt_hasLaw
        initial trafficIntensity serviceRate servers hservers hserviceRate t)
  have hcoordinate : HasLaw coordinate (stateLaw.map coordinate).toMeasure
      stateLaw.toMeasure := by
    refine ⟨(continuous_of_discreteTopology : Continuous coordinate).measurable.aemeasurable, ?_⟩
    exact PMF.toMeasure_map coordinate stateLaw
      (continuous_of_discreteTopology : Continuous coordinate).measurable
  simpa [clock, mean, kernel, stateLaw, coordinate] using hcoordinate.fun_comp hstate

/-- The time evaluation of the bundled local-`J₁` canonical queue path has
the same centered Poissonized-semigroup law as the concrete physical-time
trajectory.  The equality is almost sure because the bundled càdlàg path is
the total modification of the literal canonical trajectory. -/
theorem manyServerCenteredSqrtCanonicalSkorokhodPath_apply_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        manyServerCenteredSqrtCanonicalSkorokhodPath servers z (t : ℝ))
      (PMF.toMeasure ((initial.bind (CountableMarkovKernel.poissonized
          (manyServerUniformizedKernel trafficIntensity servers hservers)
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            (t : ℝ)
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (NNReal.coe_nonneg t))))).map (fun state : ℕ =>
          ((state : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ))))
      ((manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  let clock := manyServerCanonicalForwardPoissonClock
    trafficIntensity serviceRate servers hservers hserviceRate
  have hcoordinate := manyServerCenteredSqrtCanonicalTrajectoryAt_hasLaw
    initial trafficIntensity serviceRate servers hservers hserviceRate t
  have heq : (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
      manyServerCenteredSqrtCanonicalSkorokhodPath servers z (t : ℝ)) =ᵐ[
        (manyServerUniformizedEmbeddedTrajectoryMeasure
          initial.toMeasure trafficIntensity servers hservers).prod
          (PoissonProcess.exponentialInterarrivalMeasure
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))]
      fun z =>
        ((stationaryTrajectoryAtForwardPoissonCount (α := ℕ) clock t z : ℝ) -
          (servers : ℝ)) / Real.sqrt (servers : ℝ) := by
    filter_upwards [ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
      (initial := initial.toMeasure) trafficIntensity serviceRate servers hservers hserviceRate]
      with z hz
    rw [hz (t : ℝ)]
    rfl
  exact hcoordinate.congr heq

/-- For every countable initial law, the canonical-clock many-server
construction has the exact time-zero/three-time finite-dimensional mixture
through two successive embedded transition powers.  This is the concrete
nonstationary process bridge required by diffusion arguments with arbitrary
initial laws; it remains a deterministic-time law statement. -/
theorem manyServerUniformizedCanonicalTrajectoryAt_triple_mixture
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {sTime tTime : ℝ≥0} (hst : sTime ≤ tTime)
    (s : Set ((ℕ × ℕ) × ℕ)) (hs : MeasurableSet s) :
    ((manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          ((z.1 0, stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) sTime z),
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
              (manyServerCanonicalForwardPoissonClock
                trafficIntensity serviceRate servers hservers hserviceRate) tTime z)) s =
      ∫⁻ q : ℕ × ℕ,
        ((initial.toMeasure ⊗ₘ
          ((countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ q.1)) ⊗ₘ
          ((countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ q.2).prodMkLeft ℕ) s ∂
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)).map
          (fun gaps =>
            ((manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate).intervalCount 0 sTime gaps,
              (manyServerCanonicalForwardPoissonClock
                trafficIntensity serviceRate servers hservers hserviceRate).intervalCount
                  sTime tTime gaps)) := by
  simpa [manyServerUniformizedEmbeddedTrajectoryMeasure,
    manyServerCanonicalForwardPoissonClock] using
    (stationaryTrajMeasure_zero_forwardPoissonCount_triple_mixture
      (π := initial.toMeasure)
      (K := countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))
      (P := PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate) hst s hs)

/-- The stationary canonical-clock M/M/s queue has the exact ordered two-time
law obtained by mixing its embedded `m`-step transition coupling over the
Poisson number of potential events in the intervening interval. This supplies
a concrete finite-dimensional continuous-time bridge, while the full CTMC and
path-space diffusion arguments remain separate. -/
theorem manyServerUniformizedCanonicalStationaryTrajectory_pair_mixture
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (htraffic_lt_one : trafficIntensity < 1)
    {sTime tTime : ℝ≥0} (hst : sTime ≤ tTime)
    (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          (stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) sTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
              (manyServerCanonicalForwardPoissonClock
                trafficIntensity serviceRate servers hservers hserviceRate) tTime z)) s =
      ∫⁻ m, (
        (manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
        ((countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ m)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (manyServer_uniformized_stationaryTraj_forwardPoissonCount_pair_mixture
      trafficIntensity servers hservers htraffic_lt_one
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate) hst s hs)

/-- The stationary canonical-clock M/M/s construction has the exact
three-time Poisson-mixture law obtained from the two intervening potential
event counts.  This supplies a concrete finite-dimensional continuous-time
bridge; functional path convergence remains a separate theorem. -/
theorem manyServerUniformizedCanonicalStationaryTrajectory_triple_mixture
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (htraffic_lt_one : trafficIntensity < 1)
    {rTime sTime tTime : ℝ≥0} (hrs : rTime ≤ sTime) (hst : sTime ≤ tTime)
    (s : Set ((ℕ × ℕ) × ℕ)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          ((stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) rTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
              (manyServerCanonicalForwardPoissonClock
                trafficIntensity serviceRate servers hservers hserviceRate) sTime z),
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
              (manyServerCanonicalForwardPoissonClock
                trafficIntensity serviceRate servers hservers hserviceRate) tTime z)) s =
      ∫⁻ q : ℕ × ℕ,
        (((manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
          ((countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ q.1)) ⊗ₘ
          ((countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers)) ^ q.2).prodMkLeft ℕ) s ∂
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            ((sTime : ℝ) - (rTime : ℝ))
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrs))))).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) := by
  simpa [manyServerCanonicalForwardPoissonClock] using
    (manyServer_uniformized_stationaryTraj_forwardPoissonCount_triple_mixture
      trafficIntensity servers hservers htraffic_lt_one
      (manyServerCanonicalForwardPoissonClock
        trafficIntensity serviceRate servers hservers hserviceRate) hrs hst s hs)

/-- At any two ordered times, the stationary canonical-clock M/M/s pair law
is the stationary measure composed with the elapsed-time Poissonized
transition kernel. -/
theorem manyServerUniformizedCanonicalStationaryTrajectory_pair_poissonizedKernel
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (htraffic_lt_one : trafficIntensity < 1)
    {sTime tTime : ℝ≥0} (hst : sTime ≤ tTime)
    (s : Set (ℕ × ℕ)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))).map
        (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
          (stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) sTime z,
            stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
              (manyServerCanonicalForwardPoissonClock
                trafficIntensity serviceRate servers hservers hserviceRate) tTime z)) s =
      ((manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure ⊗ₘ
        CountableMarkovKernel.poissonizedKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers)
          (PoissonProcess.rateExposureParam
            (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
            ((tTime : ℝ) - (sTime : ℝ))
            (mul_nonneg
              (le_of_lt (manyServerUniformizationRate_pos
                trafficIntensity serviceRate servers hservers hserviceRate))
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) s := by
  rw [manyServerUniformizedCanonicalStationaryTrajectory_pair_mixture
    trafficIntensity serviceRate servers hservers hserviceRate htraffic_lt_one hst s hs]
  simp_rw [← CountableMarkovKernel.countablePMFKernel_iterate_eq_pow]
  let initial := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let mean := PoissonProcess.rateExposureParam
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
    ((tTime : ℝ) - (sTime : ℝ))
    (mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos
        trafficIntensity serviceRate servers hservers hserviceRate))
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))
  exact (CountableMarkovKernel.compProd_poissonizedKernel_apply_eq_lintegral_iterate
    initial (manyServerUniformizedKernel trafficIntensity servers hservers) mean s hs).symm

end AppliedModelingLib.Probability.Queueing

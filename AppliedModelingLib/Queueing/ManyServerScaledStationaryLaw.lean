import AppliedModelingLib.Queueing.ManyServerStationaryTailLaw
import AppliedModelingLib.Queueing.BirthDeathDiffusionScaling
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Centered scaled stationary laws for many-server queues

This module names the pushforward of the invariant many-server queue-length
law under its centered square-root coordinate.  It is a static law-level
construction and does not assert a continuous-time process construction.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

/-- The invariant many-server queue-length law as a bundled probability
measure. -/
noncomputable def manyServerStationaryProbabilityMeasure
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    ProbabilityMeasure ℕ :=
  ⟨manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one,
    by
      unfold manyServerStationaryLaw
      exact PMF.toMeasure.isProbabilityMeasure _⟩

/-- The invariant many-server queue-length law transported to the centered
square-root queue coordinate. -/
noncomputable def manyServerCenteredScaledStationaryLaw
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    Measure ℝ :=
  (manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one).map
    (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)))

/-- The centered scaled invariant law as a bundled probability measure. -/
noncomputable def manyServerCenteredScaledStationaryProbabilityMeasure
  (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    ProbabilityMeasure ℝ :=
  (manyServerStationaryProbabilityMeasure trafficIntensity servers
    htraffic_nonneg htraffic_lt_one).map
      (f := affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)))
      (measurable_of_countable _).aemeasurable

/-- The bundled centered scaled probability measure has the named law as its
underlying measure. -/
theorem manyServerCenteredScaledStationaryProbabilityMeasure_toMeasure
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerCenteredScaledStationaryProbabilityMeasure trafficIntensity servers
      htraffic_nonneg htraffic_lt_one : Measure ℝ) =
      manyServerCenteredScaledStationaryLaw trafficIntensity servers
        htraffic_nonneg htraffic_lt_one := by
  rfl

/-- Events under the centered scaled stationary law are exactly preimage
events under the invariant queue-length law. -/
theorem manyServerCenteredScaledStationaryLaw_apply
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (event : Set ℝ) (hevent : MeasurableSet event) :
    manyServerCenteredScaledStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
      event =
      manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
        ((affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) ⁻¹' event) := by
  unfold manyServerCenteredScaledStationaryLaw
  rw [Measure.map_apply (measurable_of_countable _) hevent]

/-- The lower CDF event of a centered scaled stationary queue is exactly the
stationary probability of the associated finite natural cutoff. -/
theorem manyServerCenteredScaledStationaryLaw_Iic_apply
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (hservers : 0 < servers)
    (threshold : ℝ)
    (hthreshold_nonneg : 0 ≤ (servers : ℝ) + Real.sqrt (servers : ℝ) * threshold) :
    manyServerCenteredScaledStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
      (Set.Iic threshold) =
      manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
        (Finset.range
          (Nat.floor ((servers : ℝ) + Real.sqrt (servers : ℝ) * threshold) + 1)) := by
  rw [manyServerCenteredScaledStationaryLaw_apply _ _ _ _ _ measurableSet_Iic]
  simpa using congrArg
    (manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one)
    (affineQueueCoordinate_preimage_Iic
      (center := (servers : ℝ)) (scale := Real.sqrt (servers : ℝ))
      (threshold := threshold)
      (Real.sqrt_pos.2 (by exact_mod_cast hservers)) hthreshold_nonneg)

/-- The upper strict-tail event of a centered scaled stationary queue is
exactly the stationary probability of the associated natural upper ray. -/
theorem manyServerCenteredScaledStationaryLaw_Ioi_apply
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (hservers : 0 < servers)
    (threshold : ℝ)
    (hthreshold_nonneg : 0 ≤ (servers : ℝ) + Real.sqrt (servers : ℝ) * threshold) :
    manyServerCenteredScaledStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
      (Set.Ioi threshold) =
      manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
        (Set.Ici
          (Nat.floor ((servers : ℝ) + Real.sqrt (servers : ℝ) * threshold) + 1)) := by
  rw [manyServerCenteredScaledStationaryLaw_apply _ _ _ _ _ measurableSet_Ioi]
  simpa using congrArg
    (manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one)
    (affineQueueCoordinate_preimage_Ioi
      (center := (servers : ℝ)) (scale := Real.sqrt (servers : ℝ))
      (threshold := threshold)
      (Real.sqrt_pos.2 (by exact_mod_cast hservers)) hthreshold_nonneg)

/-- A centered scaled stationary law is a probability measure, so its lower
CDF event and strict upper-tail event are complementary in real mass. -/
theorem manyServerCenteredScaledStationaryLaw_Iic_toReal_eq_one_sub_Ioi_toReal
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (threshold : ℝ) :
    (manyServerCenteredScaledStationaryLaw
      trafficIntensity servers htraffic_nonneg htraffic_lt_one (Set.Iic threshold)).toReal =
      1 -
        (manyServerCenteredScaledStationaryLaw
          trafficIntensity servers htraffic_nonneg htraffic_lt_one (Set.Ioi threshold)).toReal := by
  letI : IsProbabilityMeasure
      (manyServerCenteredScaledStationaryLaw
        trafficIntensity servers htraffic_nonneg htraffic_lt_one) := by
    rw [← manyServerCenteredScaledStationaryProbabilityMeasure_toMeasure]
    infer_instance
  have hcompl : Set.Ioi threshold = (Set.Iic threshold)ᶜ := by
    ext point
    simp
  calc
    (manyServerCenteredScaledStationaryLaw
      trafficIntensity servers htraffic_nonneg htraffic_lt_one (Set.Iic threshold)).toReal =
        (manyServerCenteredScaledStationaryLaw
          trafficIntensity servers htraffic_nonneg htraffic_lt_one).real (Set.Iic threshold) := rfl
    _ = 1 -
        (manyServerCenteredScaledStationaryLaw
          trafficIntensity servers htraffic_nonneg htraffic_lt_one).real ((Set.Iic threshold)ᶜ) := by
      linarith [MeasureTheory.probReal_add_probReal_compl
        (μ := manyServerCenteredScaledStationaryLaw
          trafficIntensity servers htraffic_nonneg htraffic_lt_one)
        (s := Set.Iic threshold) (measurableSet_Iic : MeasurableSet (Set.Iic threshold))]
    _ = 1 -
        (manyServerCenteredScaledStationaryLaw
          trafficIntensity servers htraffic_nonneg htraffic_lt_one).real (Set.Ioi threshold) := by
      rw [hcompl]
    _ = 1 -
        (manyServerCenteredScaledStationaryLaw
          trafficIntensity servers htraffic_nonneg htraffic_lt_one (Set.Ioi threshold)).toReal := rfl

end AppliedModelingLib.Probability.Queueing

import AppliedModelingLib.Queueing.BirthDeathDiffusionScaling
import AppliedModelingLib.Queueing.ManyServerQED
import AppliedModelingLib.Queueing.ManyServerUniformization
import Mathlib.Tactic

/-!
# Diffusion coefficients for scaled many-server birth--death queues

This module rewrites the affine generator drift and second jump moment of a
many-server queue in the scaled coordinate itself.  The identities are purely
deterministic inputs to a birth--death diffusion-approximation theorem; they do
not construct a continuous-time process or assert weak convergence.
-/

namespace AppliedModelingLib.Probability.Queueing

open Filter Topology

/-- The piecewise-linear limiting drift is globally Lipschitz. -/
theorem lipschitzWith_manyServerLimitingDrift (beta serviceRate : ℝ) :
    LipschitzWith ‖serviceRate‖₊
      (fun x : ℝ => serviceRate * (-beta - min x 0)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Real.dist_eq]
  have hmin : |min x 0 - min y 0| ≤ |x - y| := by
    simpa using (abs_min_sub_min_le_max x 0 y 0)
  calc
    |serviceRate * (-beta - min x 0) - serviceRate * (-beta - min y 0)| =
        |serviceRate| * |min x 0 - min y 0| := by
      have hinner : serviceRate * (-beta - min x 0) -
          serviceRate * (-beta - min y 0) =
          -serviceRate * (min x 0 - min y 0) := by
        ring
      rw [hinner, abs_mul, abs_neg]
    _ ≤ |serviceRate| * |x - y| :=
      mul_le_mul_of_nonneg_left hmin (abs_nonneg serviceRate)
    _ = (‖serviceRate‖₊ : ℝ) * |x - y| := by
      simp [Real.norm_eq_abs]

/-- The limiting many-server drift has linear growth.  This deterministic
estimate is the coefficient-side input for compact-containment and moment
arguments in a diffusion approximation. -/
theorem abs_manyServerLimitingDrift_le_linear
    (beta serviceRate x : ℝ) :
    |serviceRate * (-beta - min x 0)| ≤ |serviceRate| * (|beta| + |x|) := by
  have hmin : |min x 0| ≤ |x| := by
    simpa using (abs_min_sub_min_le_max x 0 0 0)
  have hbody : |-beta - min x 0| ≤ |beta| + |x| := by
    calc
      |-beta - min x 0| ≤ |-beta| + |min x 0| := by
        simpa using (abs_sub_le (-beta) 0 (min x 0))
    _ = |beta| + |min x 0| := by rw [abs_neg]
    _ ≤ |beta| + |x| := add_le_add_right hmin _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hbody (abs_nonneg serviceRate)

/-- A many-server idle fraction is controlled by the absolute centered
square-root-scaled queue coordinate.  This deterministic estimate connects
the predictable variance of unused-service marks to compact containment of
the scaled queue. -/
theorem one_sub_manyServerBusyFraction_le_abs_affineQueueCoordinate_div_sqrt
    (servers state : ℕ) (hservers : 0 < servers) :
    1 - (manyServerBusyFraction servers state : ℝ) ≤
      |affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state| /
        Real.sqrt (servers : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt (servers : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hservers)
  have hsqrt_ne : Real.sqrt (servers : ℝ) ≠ 0 := hsqrt_pos.ne'
  rw [one_sub_manyServerBusyFraction_eq_unusedFraction servers state hservers]
  by_cases hstate : state ≤ servers
  · have hdiff : (state : ℝ) - (servers : ℝ) = -((servers - state : ℕ) : ℝ) := by
      rw [Nat.cast_sub hstate]
      ring
    have hunused_nonneg : 0 ≤ ((servers - state : ℕ) : ℝ) := by positivity
    rw [affineQueueCoordinate, hdiff, abs_div, abs_neg,
      abs_of_nonneg hunused_nonneg, abs_of_pos hsqrt_pos]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt (by positivity)]
  · have hservers_le : servers ≤ state := Nat.le_of_not_ge hstate
    rw [Nat.sub_eq_zero_of_le hservers_le]
    simp only [Nat.cast_zero, zero_div]
    exact div_nonneg (abs_nonneg _) hsqrt_pos.le

/-- The many-server idle fraction is exactly the negative part of the
centered square-root coordinate, divided by `sqrt servers`. -/
theorem one_sub_manyServerBusyFraction_eq_negativePart_affineQueueCoordinate_div_sqrt
    (servers state : ℕ) (hservers : 0 < servers) :
    1 - (manyServerBusyFraction servers state : ℝ) =
      (-min (affineQueueCoordinate (servers : ℝ)
        (Real.sqrt (servers : ℝ)) state) 0) / Real.sqrt (servers : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt (servers : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hservers)
  have hsqrt_ne : Real.sqrt (servers : ℝ) ≠ 0 := hsqrt_pos.ne'
  rw [one_sub_manyServerBusyFraction_eq_unusedFraction servers state hservers]
  by_cases hstate : state ≤ servers
  · have hdiff : (state : ℝ) - (servers : ℝ) = -((servers - state : ℕ) : ℝ) := by
      rw [Nat.cast_sub hstate]
      ring
    have hquotient_nonpos :
        -((servers - state : ℕ) : ℝ) / Real.sqrt (servers : ℝ) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (by positivity)) hsqrt_pos.le
    rw [affineQueueCoordinate, hdiff, min_eq_left hquotient_nonpos]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt (by positivity)]
  · have hservers_le : servers ≤ state := Nat.le_of_not_ge hstate
    rw [Nat.sub_eq_zero_of_le hservers_le]
    simp only [Nat.cast_zero, zero_div]
    have hcoordinate_nonneg :
        0 ≤ affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state := by
      unfold affineQueueCoordinate
      apply div_nonneg
      · exact sub_nonneg.mpr (by exact_mod_cast hservers_le)
      · exact hsqrt_pos.le
    rw [min_eq_right hcoordinate_nonneg]
    simp

/-- Away from the reflecting zero state, the affine many-server generator
drift is expressed through the negative part of the centered scaled state. -/
theorem manyServerBirthDeath_scaledDrift_affine_eq_coordinateMin
    (trafficIntensity serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (hstate : 0 < state) :
    birthDeathScaledDrift
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) state =
      serviceRate *
        (Real.sqrt (servers : ℝ) * (trafficIntensity - 1) -
          min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0) := by
  have hsqrt_pos : 0 < Real.sqrt (servers : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hservers)
  have hsqrt_ne : Real.sqrt (servers : ℝ) ≠ 0 := hsqrt_pos.ne'
  have hsquare : Real.sqrt (servers : ℝ) ^ 2 = (servers : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [manyServerBirthDeath_scaledDrift_affine_of_pos
    trafficIntensity serviceRate (servers : ℝ) (Real.sqrt (servers : ℝ))
    servers state hsqrt_ne hstate]
  by_cases hstate_le : state ≤ servers
  · have hmin : (Nat.min state servers : ℝ) = state := by
      exact_mod_cast Nat.min_eq_left hstate_le
    have hcoordinate_nonpos :
        affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state ≤ 0 := by
      unfold affineQueueCoordinate
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (by exact_mod_cast hstate_le)) hsqrt_pos.le
    rw [hmin, min_eq_left hcoordinate_nonpos]
    unfold affineQueueCoordinate
    field_simp [hsqrt_ne]
    rw [hsquare]
    ring
  · have hservers_le : servers ≤ state := Nat.le_of_not_ge hstate_le
    have hmin : (Nat.min state servers : ℝ) = servers := by
      exact_mod_cast Nat.min_eq_right hservers_le
    have hcoordinate_nonneg :
        0 ≤ affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state := by
      unfold affineQueueCoordinate
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hservers_le)) hsqrt_pos.le
    rw [hmin, min_eq_right hcoordinate_nonneg]
    field_simp [hsqrt_ne]
    ring_nf
    rw [hsquare]
    ring

/-- Away from the reflecting boundary, the prelimit scaled drift has a
linear-growth bound in its own affine state coordinate. -/
theorem abs_manyServerBirthDeath_scaledDrift_affine_le_linear
    (trafficIntensity serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (hstate : 0 < state) :
    |birthDeathScaledDrift
        (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
          serviceRate servers)
        (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) state| ≤
      |serviceRate| *
        (|Real.sqrt (servers : ℝ) * (trafficIntensity - 1)| +
          |affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state|) := by
  rw [manyServerBirthDeath_scaledDrift_affine_eq_coordinateMin
    trafficIntensity serviceRate servers state hservers hstate, abs_mul]
  have hmin :
      |min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0| ≤
        |affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state| := by
    simpa using (abs_min_sub_min_le_max
      (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0 0 0)
  have hbody :
      |Real.sqrt (servers : ℝ) * (trafficIntensity - 1) -
          min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0| ≤
        |Real.sqrt (servers : ℝ) * (trafficIntensity - 1)| +
          |affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state| := by
    calc
      |Real.sqrt (servers : ℝ) * (trafficIntensity - 1) -
          min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0| ≤
          |Real.sqrt (servers : ℝ) * (trafficIntensity - 1)| +
            |min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0| :=
        by
          simpa using
            (abs_sub_le (Real.sqrt (servers : ℝ) * (trafficIntensity - 1)) 0
              (min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0))
      _ ≤ |Real.sqrt (servers : ℝ) * (trafficIntensity - 1)| +
          |affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state| :=
        add_le_add_right hmin _
  exact mul_le_mul_of_nonneg_left hbody (abs_nonneg serviceRate)

/-- Along a QED sequence, the prelimit scaled drifts have one eventual
linear-growth envelope that is uniform over all positive states.  This is a
coefficient estimate for a future compact-containment argument. -/
theorem eventually_abs_manyServerBirthDeath_scaledDrift_affine_le_linear
    {trafficIntensity : ℕ → NNReal} {beta serviceRate : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ, 0 < state →
      |birthDeathScaledDrift
          (manyServerBirthDeathRates
            (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
            serviceRate (n + 1))
          (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ))) state| ≤
        |serviceRate| *
          (|beta| + 1 +
            |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
              (Real.sqrt ((n + 1 : ℕ) : ℝ)) state|) := by
  have hspare : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((trafficIntensity (n + 1) : ℝ) - 1))
      atTop (𝓝 (-beta)) := by
    refine Tendsto.congr' ?_ hscaled.neg
    filter_upwards with n
    ring
  have hnear : ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1) ∈
        Metric.ball (-beta) 1 :=
    hspare.eventually (Metric.ball_mem_nhds (-beta) (by norm_num))
  filter_upwards [hnear] with n hn state hstate
  have hspare_bound :
      |Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1)| ≤
        |beta| + 1 := by
    have htriangle :
        |Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1)| ≤
          |Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1) -
            (-beta)| + |-beta| := by
      simpa using (abs_sub_le
        (Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1))
        (-beta) 0)
    calc
      |Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1)| ≤
          |Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1) -
            (-beta)| + |-beta| := htriangle
      _ ≤ 1 + |beta| := by
        have hn' :
            |Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1) -
              (-beta)| < 1 := by
          simpa [Metric.mem_ball, Real.dist_eq] using hn
        rw [abs_neg]
        exact add_le_add hn'.le le_rfl
      _ = |beta| + 1 := by ring
  have hbound := abs_manyServerBirthDeath_scaledDrift_affine_le_linear
    (trafficIntensity (n + 1) : ℝ) serviceRate (n + 1) state
    (Nat.succ_pos n) hstate
  calc
    |birthDeathScaledDrift
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
          serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ))) state| ≤
        |serviceRate| *
          (|Real.sqrt ((n + 1 : ℕ) : ℝ) * ((trafficIntensity (n + 1) : ℝ) - 1)| +
            |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
              (Real.sqrt ((n + 1 : ℕ) : ℝ)) state|) := by
          simpa using hbound
    _ ≤ |serviceRate| *
        (|beta| + 1 + |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) state|) := by
          gcongr

/-- The scaled many-server drift differs from its limiting drift evaluated at
the same scaled coordinate only through the scalar spare-capacity error. -/
theorem manyServerBirthDeath_scaledDrift_sub_limitingCoordinateDrift
    (trafficIntensity serviceRate beta : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (hstate : 0 < state) :
    birthDeathScaledDrift
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) state -
      serviceRate * (-beta -
        min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0) =
      -serviceRate *
        (Real.sqrt (servers : ℝ) * (1 - trafficIntensity) - beta) := by
  rw [manyServerBirthDeath_scaledDrift_affine_eq_coordinateMin
    trafficIntensity serviceRate servers state hservers hstate]
  ring

/-- QED spare-capacity convergence gives a uniform drift approximation over
all positive queue states when the limiting drift is evaluated at each
state's own scaled coordinate. -/
theorem eventually_uniform_manyServerBirthDeath_scaledDrift_sub_limitingCoordinateDrift
    {trafficIntensity : ℕ → NNReal} {beta serviceRate : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ, 0 < state →
      |birthDeathScaledDrift
          (manyServerBirthDeathRates
            (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
            serviceRate (n + 1))
          (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ))) state -
        serviceRate * (-beta -
          min (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ)) state) 0)| < epsilon := by
  by_cases hservice : serviceRate = 0
  · filter_upwards with n state hstate
    rw [manyServerBirthDeath_scaledDrift_sub_limitingCoordinateDrift
      (trafficIntensity (n + 1) : ℝ) serviceRate beta (n + 1) state
      (Nat.succ_pos n) hstate, hservice]
    simpa using hepsilon
  · have habs_service_pos : 0 < |serviceRate| := abs_pos.mpr hservice
    have hball := hscaled.eventually
      (Metric.ball_mem_nhds beta (div_pos hepsilon habs_service_pos))
    filter_upwards [hball] with n hn state hstate
    have herror :
        |Real.sqrt ((n + 1 : ℕ) : ℝ) * (1 - (trafficIntensity (n + 1) : ℝ)) -
          beta| < epsilon / |serviceRate| := by
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    rw [manyServerBirthDeath_scaledDrift_sub_limitingCoordinateDrift
      (trafficIntensity (n + 1) : ℝ) serviceRate beta (n + 1) state
      (Nat.succ_pos n) hstate]
    rw [abs_mul, abs_neg]
    calc
      |serviceRate| *
          |Real.sqrt ((n + 1 : ℕ) : ℝ) * (1 - (trafficIntensity (n + 1) : ℝ)) -
            beta| < |serviceRate| * (epsilon / |serviceRate|) :=
        mul_lt_mul_of_pos_left herror habs_service_pos
      _ = epsilon := mul_div_cancel₀ _ habs_service_pos.ne'

/-- Away from the reflecting zero state, the affine many-server second jump
moment is expressed through the negative part of the centered scaled state. -/
theorem manyServerBirthDeath_scaledVariance_affine_eq_coordinateMin
    (trafficIntensity serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (hstate : 0 < state) :
    birthDeathScaledVariance
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) state =
      serviceRate *
        (trafficIntensity + 1 +
          min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0 /
            Real.sqrt (servers : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (servers : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hservers)
  have hsqrt_ne : Real.sqrt (servers : ℝ) ≠ 0 := hsqrt_pos.ne'
  have hsquare : Real.sqrt (servers : ℝ) ^ 2 = (servers : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [manyServerBirthDeath_scaledVariance_affine_of_pos
    trafficIntensity serviceRate (servers : ℝ) (Real.sqrt (servers : ℝ))
    servers state hsqrt_ne hstate]
  by_cases hstate_le : state ≤ servers
  · have hmin : (Nat.min state servers : ℝ) = state := by
      exact_mod_cast Nat.min_eq_left hstate_le
    have hcoordinate_nonpos :
        affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state ≤ 0 := by
      unfold affineQueueCoordinate
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (by exact_mod_cast hstate_le)) hsqrt_pos.le
    rw [hmin, min_eq_left hcoordinate_nonpos]
    unfold affineQueueCoordinate
    field_simp [hsqrt_ne]
    rw [hsquare]
    ring
  · have hservers_le : servers ≤ state := Nat.le_of_not_ge hstate_le
    have hmin : (Nat.min state servers : ℝ) = servers := by
      exact_mod_cast Nat.min_eq_right hservers_le
    have hcoordinate_nonneg :
        0 ≤ affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state := by
      unfold affineQueueCoordinate
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hservers_le)) hsqrt_pos.le
    rw [hmin, min_eq_right hcoordinate_nonneg]
    field_simp [hsqrt_ne]
    ring_nf
    rw [hsquare]
    ring

/-- At every positive state, the scaled second jump moment is bounded by the
arrival-plus-full-service rate after affine square-root scaling. -/
theorem manyServerBirthDeath_scaledVariance_affine_le
    (trafficIntensity serviceRate : ℝ) (servers state : ℕ)
    (hserviceRate : 0 ≤ serviceRate) (hservers : 0 < servers) (hstate : 0 < state) :
    birthDeathScaledVariance
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) state ≤
      serviceRate * (trafficIntensity + 1) := by
  rw [manyServerBirthDeath_scaledVariance_affine_eq_coordinateMin
    trafficIntensity serviceRate servers state hservers hstate]
  have hsqrt_pos : 0 < Real.sqrt (servers : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hservers)
  have hmin_nonpos :
      min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0 ≤ 0 :=
    min_le_right _ _
  have hcorrection_nonpos :
      min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0 /
          Real.sqrt (servers : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hmin_nonpos hsqrt_pos.le
  apply mul_le_mul_of_nonneg_left _ hserviceRate
  linarith

/-- Under QED scaling with positive service rate, the scaled second jump
moments have an eventual global bound over all positive queue states. -/
theorem eventually_manyServerBirthDeath_scaledVariance_affine_le_three_mul
    {trafficIntensity : ℕ → NNReal} {beta serviceRate : ℝ}
    (hserviceRate : 0 < serviceRate)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ, 0 < state →
      birthDeathScaledVariance
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
          serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ))) state ≤ 3 * serviceRate := by
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) :=
    tendsto_qed_succ_trafficIntensity hscaled
  have hnear : ∀ᶠ n : ℕ in atTop, (trafficIntensity (n + 1) : ℝ) < 2 := by
    have hball : ∀ᶠ n : ℕ in atTop, (trafficIntensity (n + 1) : ℝ) ∈
        Metric.ball 1 1 :=
      htraffic.eventually (Metric.ball_mem_nhds 1 (by norm_num))
    filter_upwards [hball] with n hn
    have hdistance : |(trafficIntensity (n + 1) : ℝ) - 1| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    linarith [(abs_lt.mp hdistance).2]
  filter_upwards [hnear] with n hn state hstate
  have hbound := manyServerBirthDeath_scaledVariance_affine_le
    (trafficIntensity (n + 1) : ℝ) serviceRate (n + 1) state
    hserviceRate.le (Nat.succ_pos n) hstate
  calc
    birthDeathScaledVariance
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
          serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ))) state ≤
        serviceRate * ((trafficIntensity (n + 1) : ℝ) + 1) := hbound
    _ ≤ 3 * serviceRate := by nlinarith

/-- The scaled many-server second jump moment differs from its limiting value
by the traffic-intensity and coordinate corrections visible in Stone's
coefficient criterion. -/
theorem manyServerBirthDeath_scaledVariance_sub_limitingVariance
    (trafficIntensity serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (hstate : 0 < state) :
    birthDeathScaledVariance
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))) state -
      2 * serviceRate =
      serviceRate *
        (trafficIntensity - 1 +
          min (affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) state) 0 /
            Real.sqrt (servers : ℝ)) := by
  rw [manyServerBirthDeath_scaledVariance_affine_eq_coordinateMin
    trafficIntensity serviceRate servers state hservers hstate]
  ring

/-- QED spare-capacity convergence gives a locally uniform second-moment
approximation on every bounded scaled-coordinate slab. -/
theorem eventually_uniform_manyServerBirthDeath_scaledVariance_sub_limitingVariance
    {trafficIntensity : ℕ → NNReal} {beta serviceRate coordinateBound : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ, 0 < state →
      |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) state| ≤ coordinateBound →
      |birthDeathScaledVariance
          (manyServerBirthDeathRates
            (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
            serviceRate (n + 1))
          (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ))) state - 2 * serviceRate| < epsilon := by
  by_cases hservice : serviceRate = 0
  · filter_upwards with n state hstate _hcoordinate
    rw [manyServerBirthDeath_scaledVariance_sub_limitingVariance
      (trafficIntensity (n + 1) : ℝ) serviceRate (n + 1) state
      (Nat.succ_pos n) hstate, hservice]
    simpa using hepsilon
  · have habs_service_pos : 0 < |serviceRate| := abs_pos.mpr hservice
    let tolerance : ℝ := epsilon / (2 * |serviceRate|)
    have htolerance : 0 < tolerance := by
      dsimp [tolerance]
      exact div_pos hepsilon (mul_pos (by norm_num) habs_service_pos)
    have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
        atTop (𝓝 1) :=
      tendsto_qed_succ_trafficIntensity hscaled
    have hsqrt : Tendsto
        (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      apply Real.tendsto_sqrt_atTop.comp
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hcoordinateCorrection : Tendsto
        (fun n : ℕ => coordinateBound / Real.sqrt ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => coordinateBound) atTop
          (𝓝 coordinateBound)).div_atTop hsqrt)
    have htrafficBall := htraffic.eventually
      (Metric.ball_mem_nhds 1 htolerance)
    have hcoordinateBall := hcoordinateCorrection.eventually
      (Metric.ball_mem_nhds 0 htolerance)
    filter_upwards [htrafficBall, hcoordinateBall] with n htrafficN hcoordinateN
      state hstate hcoordinateBound
    have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      exact Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)
    have htrafficError : |(trafficIntensity (n + 1) : ℝ) - 1| < tolerance := by
      simpa [Metric.mem_ball, Real.dist_eq] using htrafficN
    have hcoordinateError :
        |coordinateBound| / Real.sqrt ((n + 1 : ℕ) : ℝ) < tolerance := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_div,
        abs_of_pos hsqrt_pos] using hcoordinateN
    have hbound_nonneg : 0 ≤ coordinateBound :=
      le_trans (abs_nonneg _) hcoordinateBound
    have hcoordinateLower :
        -coordinateBound ≤ affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) state :=
      (abs_le.mp hcoordinateBound).1
    have hcoordinateUpper :
        affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) state ≤ coordinateBound :=
      (abs_le.mp hcoordinateBound).2
    have hminimumAbs :
        |min (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) state) 0| ≤ coordinateBound := by
      apply abs_le.2
      constructor
      · exact le_min hcoordinateLower (by linarith)
      · exact (min_le_left _ _).trans hcoordinateUpper
    have hminimumCorrection :
        |min (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ)) state) 0 /
          Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤
          |coordinateBound| / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      rw [abs_div, abs_of_pos hsqrt_pos]
      exact div_le_div_of_nonneg_right
        (hminimumAbs.trans (le_abs_self coordinateBound)) hsqrt_pos.le
    rw [manyServerBirthDeath_scaledVariance_sub_limitingVariance
      (trafficIntensity (n + 1) : ℝ) serviceRate (n + 1) state
      (Nat.succ_pos n) hstate, abs_mul]
    calc
      |serviceRate| *
          |(trafficIntensity (n + 1) : ℝ) - 1 +
            min (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
              (Real.sqrt ((n + 1 : ℕ) : ℝ)) state) 0 /
              Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤
        |serviceRate| *
          (|(trafficIntensity (n + 1) : ℝ) - 1| +
            |min (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
              (Real.sqrt ((n + 1 : ℕ) : ℝ)) state) 0 /
              Real.sqrt ((n + 1 : ℕ) : ℝ)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ |serviceRate| *
          (|(trafficIntensity (n + 1) : ℝ) - 1| +
            |coordinateBound| / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hminimumCorrection _) (abs_nonneg _)
      _ < |serviceRate| * (tolerance + tolerance) :=
        mul_lt_mul_of_pos_left (add_lt_add htrafficError hcoordinateError)
          habs_service_pos
      _ = epsilon := by
        dsimp [tolerance]
        field_simp [habs_service_pos.ne']
        ring

/-- Under QED scaling, the third absolute jump moment vanishes uniformly on
every bounded scaled-coordinate slab.  Together with the small-jump bound,
this is the Taylor/Lindeberg remainder input beyond the first two
infinitesimal coefficients. -/
theorem eventually_uniform_manyServerBirthDeath_scaledThirdAbsoluteMoment
    {trafficIntensity : ℕ → NNReal} {beta serviceRate coordinateBound : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ, 0 < state →
      |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) state| ≤ coordinateBound →
      |birthDeathScaledThirdAbsoluteMoment
          (manyServerBirthDeathRates
            (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
            serviceRate (n + 1))
          (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ))) state| < epsilon := by
  let varianceBound : ℝ := 1 + |2 * serviceRate|
  have hvarianceBound_pos : 0 < varianceBound := by
    dsimp [varianceBound]
    positivity
  have hvariance :=
    eventually_uniform_manyServerBirthDeath_scaledVariance_sub_limitingVariance
      (trafficIntensity := trafficIntensity) (beta := beta) (serviceRate := serviceRate)
      (coordinateBound := coordinateBound) hscaled (by norm_num : (0 : ℝ) < 1)
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinverse : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hinverseAbs : Tendsto
      (fun n : ℕ => |1 / Real.sqrt ((n + 1 : ℕ) : ℝ)|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, one_div, abs_zero] using
      continuous_abs.continuousAt.tendsto.comp hinverse
  have hsmall := hinverseAbs.eventually
    (Metric.ball_mem_nhds 0 (div_pos hepsilon hvarianceBound_pos))
  filter_upwards [hvariance, hsmall] with n hvarianceN hsmallN state hstate hcoordinate
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)
  have hsqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := hsqrt_pos.ne'
  have hinverse_pos : 0 < |1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| := by
    positivity
  have hinverse_small : |1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| <
      epsilon / varianceBound := by
    simpa [Metric.mem_ball, Real.dist_eq] using hsmallN
  let variance := birthDeathScaledVariance
    (manyServerBirthDeathRates
      (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
      serviceRate (n + 1))
    (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
      (Real.sqrt ((n + 1 : ℕ) : ℝ))) state
  have hvarianceError := hvarianceN state hstate hcoordinate
  change |variance - 2 * serviceRate| < 1 at hvarianceError
  have hvariance_bound : |variance| < varianceBound := by
    calc
      |variance| = |(variance - 2 * serviceRate) + 2 * serviceRate| := by ring_nf
      _ ≤ |variance - 2 * serviceRate| + |2 * serviceRate| := abs_add_le _ _
      _ < 1 + |2 * serviceRate| :=
        by simpa [add_comm] using add_lt_add_left hvarianceError |2 * serviceRate|
      _ = varianceBound := rfl
  rw [birthDeathScaledThirdAbsoluteMoment_affine _ _ _ state hsqrt_ne]
  change abs (|1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| * variance) < epsilon
  rw [abs_mul, abs_abs]
  calc
    |1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| * |variance| <
        |1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| * varianceBound :=
      mul_lt_mul_of_pos_left hvariance_bound hinverse_pos
    _ < (epsilon / varianceBound) * varianceBound :=
      mul_lt_mul_of_pos_right hinverse_small hvarianceBound_pos
    _ = epsilon := by
      field_simp [hvarianceBound_pos.ne']

/-- On every fixed bounded scaled-coordinate slab, the reflecting state zero
is eventually absent as the number of servers grows. -/
theorem eventually_manyServer_scaledCoordinate_state_pos_of_abs_le
    (coordinateBound : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ,
      |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) state| ≤ coordinateBound →
      0 < state := by
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      coordinateBound + 1 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    (tendsto_atTop.1 hsqrt) (coordinateBound + 1)
  filter_upwards [hlarge] with n hn state hcoordinate
  by_contra hstate
  have hzero : state = 0 := Nat.eq_zero_of_not_pos hstate
  subst state
  have hservers : 0 < n + 1 := Nat.succ_pos n
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  rw [affineQueueCoordinate_zero_centered_sqrt (n + 1) hservers,
    abs_neg, abs_of_nonneg hsqrt_nonneg] at hcoordinate
  linarith

/-- The scaled many-server generator drift converges locally uniformly on its
moving state grids to the piecewise-linear limiting drift. -/
theorem locallyUniformOnRealCoordinateGrids_manyServerBirthDeath_scaledDrift
    {trafficIntensity : ℕ → NNReal} {beta serviceRate : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    LocallyUniformOnRealCoordinateGrids
      (fun n state => affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) state)
      (fun n state => birthDeathScaledDrift
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
          serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ))) state)
      (fun x => serviceRate * (-beta - min x 0)) := by
  intro coordinateBound epsilon _hcoordinateBound hepsilon
  filter_upwards [
    eventually_uniform_manyServerBirthDeath_scaledDrift_sub_limitingCoordinateDrift
      (trafficIntensity := trafficIntensity) (beta := beta)
      (serviceRate := serviceRate) hscaled hepsilon,
    eventually_manyServer_scaledCoordinate_state_pos_of_abs_le coordinateBound]
    with n herror hpositive state hcoordinate
  exact herror state (hpositive state hcoordinate)

/-- The scaled many-server generator second jump moment converges locally
uniformly on its moving state grids to twice the service rate. -/
theorem locallyUniformOnRealCoordinateGrids_manyServerBirthDeath_scaledVariance
    {trafficIntensity : ℕ → NNReal} {beta serviceRate : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    LocallyUniformOnRealCoordinateGrids
      (fun n state => affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) state)
      (fun n state => birthDeathScaledVariance
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1 : ℕ) : ℝ) * serviceRate)
          serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ))) state)
      (fun _ => 2 * serviceRate) := by
  intro coordinateBound epsilon _hcoordinateBound hepsilon
  filter_upwards [
    eventually_uniform_manyServerBirthDeath_scaledVariance_sub_limitingVariance
      (trafficIntensity := trafficIntensity) (beta := beta)
      (serviceRate := serviceRate) (coordinateBound := coordinateBound)
      hscaled hepsilon,
    eventually_manyServer_scaledCoordinate_state_pos_of_abs_le coordinateBound]
    with n herror hpositive state hcoordinate
  exact herror state (hpositive state hcoordinate) hcoordinate

/-- The scaled many-server third absolute jump moment converges locally
uniformly to zero on its moving state grids. -/
theorem locallyUniformOnRealCoordinateGrids_manyServerBirthDeath_scaledThirdAbsoluteMoment
    {trafficIntensity : ℕ → NNReal} {beta serviceRate : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    LocallyUniformOnRealCoordinateGrids
      (fun n state => affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) state)
      (fun n state => birthDeathScaledThirdAbsoluteMoment
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1 : ℕ) : ℝ) * serviceRate)
          serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ))) state)
      (fun _ => 0) := by
  intro coordinateBound epsilon _hcoordinateBound hepsilon
  filter_upwards [
    eventually_uniform_manyServerBirthDeath_scaledThirdAbsoluteMoment
      (trafficIntensity := trafficIntensity) (beta := beta)
      (serviceRate := serviceRate) (coordinateBound := coordinateBound)
      hscaled hepsilon,
    eventually_manyServer_scaledCoordinate_state_pos_of_abs_le coordinateBound]
    with n hthird hpositive state hcoordinate
  simpa using hthird state (hpositive state hcoordinate) hcoordinate

/-- Along any convergent sequence of scaled positive states, the many-server
generator drift has the limiting piecewise-linear diffusion coefficient. -/
theorem tendsto_manyServerBirthDeath_scaledDrift_of_qed_succ
    {trafficIntensity : ℕ → NNReal} {state : ℕ → ℕ} {beta x serviceRate : ℝ}
    (hstate_pos : ∀ᶠ n : ℕ in atTop, 0 < state n)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (hcoordinate : Tendsto
      (fun n : ℕ => affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n))
      atTop (𝓝 x)) :
    Tendsto
      (fun n : ℕ => birthDeathScaledDrift
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
        serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)))
        (state n))
      atTop (𝓝 (serviceRate * (-beta - min x 0))) := by
  have hgap : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((trafficIntensity (n + 1) : ℝ) - 1))
      atTop (𝓝 (-beta)) := by
    refine Tendsto.congr' ?_ hscaled.neg
    filter_upwards with n
    ring
  have hminimum : Tendsto
      (fun n : ℕ => min
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n)) 0)
      atTop (𝓝 (min x 0)) :=
    hcoordinate.min tendsto_const_nhds
  have hbody := hgap.sub hminimum
  have hbody' : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((trafficIntensity (n + 1) : ℝ) - 1) - min
          (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
            (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n)) 0)
      atTop (𝓝 (-beta - min x 0)) := by
    simpa using hbody
  refine Tendsto.congr' ?_ (hbody'.const_mul serviceRate)
  filter_upwards [hstate_pos] with n hstate
  rw [manyServerBirthDeath_scaledDrift_affine_eq_coordinateMin
    (trafficIntensity (n + 1) : ℝ) serviceRate (n + 1) (state n)
    (Nat.succ_pos n) hstate]

/-- Along any convergent sequence of scaled positive states, the many-server
generator second jump moment converges to twice the service rate. -/
theorem tendsto_manyServerBirthDeath_scaledVariance_of_qed_succ
    {trafficIntensity : ℕ → NNReal} {state : ℕ → ℕ} {beta x serviceRate : ℝ}
    (hstate_pos : ∀ᶠ n : ℕ in atTop, 0 < state n)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (hcoordinate : Tendsto
      (fun n : ℕ => affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n))
      atTop (𝓝 x)) :
    Tendsto
      (fun n : ℕ => birthDeathScaledVariance
        (manyServerBirthDeathRates
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ) * serviceRate)
        serviceRate (n + 1))
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)))
        (state n))
      atTop (𝓝 (2 * serviceRate)) := by
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) :=
    tendsto_qed_succ_trafficIntensity hscaled
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hminimum : Tendsto
      (fun n : ℕ => min
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n)) 0)
      atTop (𝓝 (min x 0)) :=
    hcoordinate.min tendsto_const_nhds
  have hcorrection : Tendsto
      (fun n : ℕ => min
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n)) 0 /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    hminimum.div_atTop hsqrt
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hbody := (htraffic.add hone).add hcorrection
  have hbody' : Tendsto
      (fun n : ℕ => (trafficIntensity (n + 1) : ℝ) + 1 + min
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n)) 0 /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 2) := by
    norm_num at hbody ⊢
    exact hbody
  have hfinal : Tendsto
      (fun n : ℕ => serviceRate * ((trafficIntensity (n + 1) : ℝ) + 1 + min
        (affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state n)) 0 /
        Real.sqrt ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (2 * serviceRate)) := by
    simpa [mul_comm] using hbody'.const_mul serviceRate
  refine Tendsto.congr' ?_ hfinal
  filter_upwards [hstate_pos] with n hstate
  rw [manyServerBirthDeath_scaledVariance_affine_eq_coordinateMin
    (trafficIntensity (n + 1) : ℝ) serviceRate (n + 1) (state n)
    (Nat.succ_pos n) hstate]

end AppliedModelingLib.Probability.Queueing

import AppliedModelingLib.Queueing.ManyServerBirthDeath
import Mathlib.Tactic

/-!
# Affine scaling of birth--death generators

This module gives the infinitesimal drift and variance calculations for a
birth--death generator viewed through an affine state coordinate.  These
identities are reusable deterministic inputs to diffusion-approximation
arguments; they do not assert stochastic-process convergence.
-/

namespace AppliedModelingLib.Probability.Queueing

open Filter Topology

/-- A sequence of real-valued coefficients converges locally uniformly on
moving discrete state grids when its error is eventually uniformly small at
every state whose coordinate lies in a fixed bounded real slab. -/
def LocallyUniformOnRealCoordinateGrids
    (coordinate coefficient : ℕ → ℕ → ℝ) (limit : ℝ → ℝ) : Prop :=
  ∀ coordinateBound epsilon : ℝ, 0 < coordinateBound → 0 < epsilon →
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ,
      |coordinate n state| ≤ coordinateBound →
        |coefficient n state - limit (coordinate n state)| < epsilon

/-- Moving discrete state grids are asymptotically dense in the real line
when every real point is approached by a sequence of grid states. -/
def AsymptoticallyDenseRealCoordinateGrids
    (coordinate : ℕ → ℕ → ℝ) : Prop :=
  ∀ x : ℝ, ∃ state : ℕ → ℕ,
    Tendsto (fun n : ℕ => coordinate n (state n)) atTop (𝓝 x)

/-- An affine coordinate on nonnegative queue lengths. -/
noncomputable def affineQueueCoordinate (center scale : ℝ) (state : ℕ) : ℝ :=
  ((state : ℝ) - center) / scale

/-- Under an affine queue coordinate, an upward one-step transition changes
the coordinate by the reciprocal scale. -/
theorem affineQueueCoordinate_succ_sub
    (center scale : ℝ) (state : ℕ) (hscale : scale ≠ 0) :
    affineQueueCoordinate center scale (state + 1) -
      affineQueueCoordinate center scale state = 1 / scale := by
  unfold affineQueueCoordinate
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [hscale]
  ring

/-- A downward reflected one-step transition changes an affine queue
coordinate by at most the reciprocal scale in absolute value. -/
theorem abs_affineQueueCoordinate_pred_sub_le
    (center scale : ℝ) (state : ℕ) (hscale : scale ≠ 0) :
    |affineQueueCoordinate center scale (state - 1) -
      affineQueueCoordinate center scale state| ≤ |1 / scale| := by
  by_cases hstate : state = 0
  · subst state
    simp [affineQueueCoordinate]
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hstate
    have hdiff : affineQueueCoordinate center scale (previous.succ - 1) -
        affineQueueCoordinate center scale previous.succ = -(1 / scale) := by
      unfold affineQueueCoordinate
      norm_num [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]
      field_simp [hscale]
      ring
    rw [hdiff, abs_neg]

/-- Under square-root many-server scaling, both possible one-step coordinate
changes vanish uniformly over the queue state. This is the small-jump input
for functional diffusion approximations. -/
theorem eventually_manyServer_affineQueueCoordinate_jumps_small
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ state : ℕ,
      |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state + 1) -
        affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) state| < epsilon ∧
      |affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) (state - 1) -
        affineQueueCoordinate ((n + 1 : ℕ) : ℝ)
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) state| < epsilon := by
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hsqrt
  have hsmall := hinv.eventually (Metric.ball_mem_nhds 0 hepsilon)
  filter_upwards [hsmall] with n hn state
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)
  have hsqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := hsqrt_pos.ne'
  have hinv_small : |1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| < epsilon := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, one_div,
      abs_inv] using hn
  constructor
  · rw [affineQueueCoordinate_succ_sub _ _ _ hsqrt_ne]
    exact hinv_small
  · exact lt_of_le_of_lt
      (abs_affineQueueCoordinate_pred_sub_le _ _ _ hsqrt_ne) hinv_small

/-- Centering an empty queue at `servers` and scaling by `sqrt servers` puts
the reflecting state at `-sqrt servers`. -/
theorem affineQueueCoordinate_zero_centered_sqrt
    (servers : ℕ) (hservers : 0 < servers) :
    affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ)) 0 =
      -Real.sqrt (servers : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt (servers : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hservers)
  have hsqrt_ne : Real.sqrt (servers : ℝ) ≠ 0 := hsqrt_pos.ne'
  have hsquare : Real.sqrt (servers : ℝ) ^ 2 = (servers : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsquare' : Real.sqrt (servers : ℝ) * Real.sqrt (servers : ℝ) =
      (servers : ℝ) := by
    calc
      Real.sqrt (servers : ℝ) * Real.sqrt (servers : ℝ) =
          Real.sqrt (servers : ℝ) ^ 2 := by ring
      _ = (servers : ℝ) := hsquare
  unfold affineQueueCoordinate
  simp only [Nat.cast_zero]
  change ((0 : ℝ) - (servers : ℝ)) / Real.sqrt (servers : ℝ) =
    -Real.sqrt (servers : ℝ)
  apply (div_eq_iff hsqrt_ne).2
  calc
    (0 : ℝ) - (servers : ℝ) = -(servers : ℝ) := by ring
    _ = -(Real.sqrt (servers : ℝ) * Real.sqrt (servers : ℝ)) := by rw [hsquare']
    _ = -Real.sqrt (servers : ℝ) * Real.sqrt (servers : ℝ) := by ring

/-- Under a positive affine scale, the inverse image of a lower real ray is
the finite set of natural states up to the corresponding floor. -/
theorem affineQueueCoordinate_preimage_Iic
    {center scale threshold : ℝ} (hscale : 0 < scale)
    (hthreshold_nonneg : 0 ≤ center + scale * threshold) :
    (affineQueueCoordinate center scale) ⁻¹' Set.Iic threshold =
      (Finset.range (Nat.floor (center + scale * threshold) + 1 : ℕ) : Set ℕ) := by
  ext state
  simp only [Set.mem_preimage, Set.mem_Iic, Finset.mem_coe, Finset.mem_range]
  rw [Nat.lt_succ_iff]
  unfold affineQueueCoordinate
  rw [div_le_iff₀ hscale]
  have hcast : ((state : ℕ) : ℝ) ≤ center + scale * threshold ↔
      state ≤ Nat.floor (center + scale * threshold) :=
    (Nat.le_floor_iff hthreshold_nonneg).symm
  rw [sub_le_iff_le_add]
  convert hcast using 1
  all_goals ring_nf

/-- Under a positive affine scale, the inverse image of an upper open real
ray is the natural upper ray strictly above the corresponding floor. -/
theorem affineQueueCoordinate_preimage_Ioi
    {center scale threshold : ℝ} (hscale : 0 < scale)
    (hthreshold_nonneg : 0 ≤ center + scale * threshold) :
    (affineQueueCoordinate center scale) ⁻¹' Set.Ioi threshold =
      Set.Ici (Nat.floor (center + scale * threshold) + 1) := by
  ext state
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Ici]
  rw [← Nat.lt_iff_add_one_le]
  unfold affineQueueCoordinate
  rw [lt_div_iff₀ hscale]
  have hfloor : Nat.floor (center + scale * threshold) < state ↔
      center + scale * threshold < (state : ℝ) :=
    Nat.floor_lt hthreshold_nonneg
  rw [lt_sub_iff_add_lt]
  convert hfloor.symm using 1
  all_goals ring_nf

/-- The lower neighboring state of a real point in a positive affine queue
grid.  On the eventual compact region relevant to diffusion scaling, its
defining threshold is nonnegative and it is the literal natural floor. -/
noncomputable def affineQueueCoordinateFloor (center scale x : ℝ) : ℕ :=
  Nat.floor (center + scale * x)

/-- The affine coordinate of the floor state lies at or below the prescribed
real coordinate. -/
theorem affineQueueCoordinate_floor_le
    {center scale x : ℝ} (hscale : 0 < scale)
    (hthreshold : 0 ≤ center + scale * x) :
    affineQueueCoordinate center scale
      (affineQueueCoordinateFloor center scale x) ≤ x := by
  unfold affineQueueCoordinateFloor affineQueueCoordinate
  rw [div_le_iff₀ hscale]
  have hfloor : ((Nat.floor (center + scale * x) : ℕ) : ℝ) ≤
      center + scale * x :=
    Nat.floor_le hthreshold
  linarith

/-- The next affine-grid state lies strictly above the prescribed real
coordinate. -/
theorem lt_affineQueueCoordinate_floor_succ
    {center scale x : ℝ} (hscale : 0 < scale)
    (_hthreshold : 0 ≤ center + scale * x) :
    x < affineQueueCoordinate center scale
      (affineQueueCoordinateFloor center scale x + 1) := by
  unfold affineQueueCoordinateFloor affineQueueCoordinate
  rw [lt_div_iff₀ hscale]
  have hfloor : center + scale * x <
      ((Nat.floor (center + scale * x) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  norm_num [Nat.cast_add, Nat.cast_one]
  linarith

/-- The lower affine-grid representative is within one mesh width of the
target coordinate. -/
theorem sub_affineQueueCoordinate_floor_lt_inv_scale
    {center scale x : ℝ} (hscale : 0 < scale)
    (hthreshold : 0 ≤ center + scale * x) :
    0 ≤ x - affineQueueCoordinate center scale
      (affineQueueCoordinateFloor center scale x) ∧
    x - affineQueueCoordinate center scale
      (affineQueueCoordinateFloor center scale x) < 1 / scale := by
  constructor
  · exact sub_nonneg.mpr (affineQueueCoordinate_floor_le hscale hthreshold)
  · have hnext := lt_affineQueueCoordinate_floor_succ hscale hthreshold
    have hstep := affineQueueCoordinate_succ_sub center scale
      (affineQueueCoordinateFloor center scale x) hscale.ne'
    linarith

/-- The generator drift of a birth--death process after applying a state
coordinate. -/
noncomputable def birthDeathScaledDrift
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (state : ℕ) : ℝ :=
  rates.birth state * (coordinate (state + 1) - coordinate state) +
    rates.death state * (coordinate (state - 1) - coordinate state)

/-- The generator second jump moment of a birth--death process after applying
a state coordinate. -/
noncomputable def birthDeathScaledVariance
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (state : ℕ) : ℝ :=
  rates.birth state * (coordinate (state + 1) - coordinate state) ^ 2 +
    rates.death state * (coordinate (state - 1) - coordinate state) ^ 2

/-- The signed third jump moment per unit time after applying a state
coordinate to a birth--death process.  Together with drift and variance, this
is the exact cubic Taylor term of the generator. -/
noncomputable def birthDeathScaledThirdMoment
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (state : ℕ) : ℝ :=
  rates.birth state * (coordinate (state + 1) - coordinate state) ^ 3 +
    rates.death state * (coordinate (state - 1) - coordinate state) ^ 3

/-- The birth--death generator applied to a real test function after a state
coordinate has been chosen. -/
noncomputable def birthDeathScaledGenerator
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (test : ℝ → ℝ)
    (state : ℕ) : ℝ :=
  rates.birth state * (test (coordinate (state + 1)) - test (coordinate state)) +
    rates.death state * (test (coordinate (state - 1)) - test (coordinate state))

/-- The scaled generator on the identity test function is its drift. -/
theorem birthDeathScaledGenerator_id
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (state : ℕ) :
    birthDeathScaledGenerator rates coordinate (fun x : ℝ => x) state =
      birthDeathScaledDrift rates coordinate state := rfl

/-- The scaled generator on the square test function is determined by its
drift and second jump moment. -/
theorem birthDeathScaledGenerator_square
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (state : ℕ) :
    birthDeathScaledGenerator rates coordinate (fun x : ℝ => x ^ 2) state =
      2 * coordinate state * birthDeathScaledDrift rates coordinate state +
        birthDeathScaledVariance rates coordinate state := by
  unfold birthDeathScaledGenerator birthDeathScaledDrift birthDeathScaledVariance
  ring

/-- The scaled generator on an arbitrary quadratic test function is determined
exactly by its drift and second jump moment. -/
theorem birthDeathScaledGenerator_quadratic
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (quadratic linear constant : ℝ)
    (state : ℕ) :
    birthDeathScaledGenerator rates coordinate
      (fun x : ℝ => quadratic * x ^ 2 + linear * x + constant) state =
      quadratic *
          (2 * coordinate state * birthDeathScaledDrift rates coordinate state +
            birthDeathScaledVariance rates coordinate state) +
        linear * birthDeathScaledDrift rates coordinate state := by
  unfold birthDeathScaledGenerator birthDeathScaledDrift birthDeathScaledVariance
  ring

/-- The scaled generator on a cubic polynomial is determined exactly by the
first three signed jump moments. -/
theorem birthDeathScaledGenerator_cubic
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ)
    (cubic quadratic linear constant : ℝ) (state : ℕ) :
    birthDeathScaledGenerator rates coordinate
      (fun x : ℝ => cubic * x ^ 3 + quadratic * x ^ 2 + linear * x + constant)
      state =
      cubic *
          (3 * coordinate state ^ 2 * birthDeathScaledDrift rates coordinate state +
            3 * coordinate state * birthDeathScaledVariance rates coordinate state +
            birthDeathScaledThirdMoment rates coordinate state) +
        quadratic *
          (2 * coordinate state * birthDeathScaledDrift rates coordinate state +
            birthDeathScaledVariance rates coordinate state) +
          linear * birthDeathScaledDrift rates coordinate state := by
  unfold birthDeathScaledGenerator birthDeathScaledDrift birthDeathScaledVariance
    birthDeathScaledThirdMoment
  ring

/-- The third absolute jump moment per unit time after applying a state
coordinate to a birth--death process.  This is the Lindeberg-scale remainder
term accompanying the infinitesimal drift and variance. -/
noncomputable def birthDeathScaledThirdAbsoluteMoment
    (rates : BirthDeathRates) (coordinate : ℕ → ℝ) (state : ℕ) : ℝ :=
  rates.birth state * |coordinate (state + 1) - coordinate state| ^ 3 +
    rates.death state * |coordinate (state - 1) - coordinate state| ^ 3

/-- For an affine coordinate, the third absolute jump moment is the second
jump moment multiplied by the absolute one-step coordinate size.  The formula
also covers the reflected zero state, whose downward increment is zero. -/
theorem birthDeathScaledThirdAbsoluteMoment_affine
    (rates : BirthDeathRates) (center scale : ℝ) (state : ℕ)
    (hscale : scale ≠ 0) :
    birthDeathScaledThirdAbsoluteMoment rates (affineQueueCoordinate center scale) state =
      |1 / scale| * birthDeathScaledVariance rates
        (affineQueueCoordinate center scale) state := by
  cases state with
  | zero =>
      rw [birthDeathScaledThirdAbsoluteMoment, birthDeathScaledVariance]
      rw [rates.death_zero]
      simp only [zero_mul, add_zero]
      have hforward := affineQueueCoordinate_succ_sub center scale 0 hscale
      rw [hforward]
      have habs_cube : |1 / scale| ^ 3 = |1 / scale| * (1 / scale) ^ 2 := by
        calc
          |1 / scale| ^ 3 = |1 / scale| * |1 / scale| ^ 2 := by ring
          _ = |1 / scale| * (1 / scale) ^ 2 := by rw [sq_abs]
      rw [habs_cube]
      ring
  | succ state =>
      have hforward := affineQueueCoordinate_succ_sub center scale (state + 1) hscale
      have hbackward :
          affineQueueCoordinate center scale ((state + 1) - 1) -
            affineQueueCoordinate center scale (state + 1) = -(1 / scale) := by
        unfold affineQueueCoordinate
        norm_num [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]
        field_simp [hscale]
        ring
      have hbackward' :
          affineQueueCoordinate center scale state -
            affineQueueCoordinate center scale (state + 1) = -(1 / scale) := by
        simpa using hbackward
      have habs_cube : |1 / scale| ^ 3 = |1 / scale| * (1 / scale) ^ 2 := by
        calc
          |1 / scale| ^ 3 = |1 / scale| * |1 / scale| ^ 2 := by ring
          _ = |1 / scale| * (1 / scale) ^ 2 := by rw [sq_abs]
      rw [birthDeathScaledThirdAbsoluteMoment, birthDeathScaledVariance]
      simp only [Nat.succ_sub_one]
      rw [hforward, hbackward', abs_neg, habs_cube]
      ring

/-- For an affine coordinate, the signed third jump moment is the drift times
the square of one mesh width.  The reflected boundary is included because the
downward rate there is zero. -/
theorem birthDeathScaledThirdMoment_affine
    (rates : BirthDeathRates) (center scale : ℝ) (state : ℕ)
    (hscale : scale ≠ 0) :
    birthDeathScaledThirdMoment rates (affineQueueCoordinate center scale) state =
      (1 / scale) ^ 2 *
        birthDeathScaledDrift rates (affineQueueCoordinate center scale) state := by
  cases state with
  | zero =>
      rw [birthDeathScaledThirdMoment, birthDeathScaledDrift, rates.death_zero]
      simp only [zero_mul, add_zero]
      have hforward := affineQueueCoordinate_succ_sub center scale 0 hscale
      rw [hforward]
      ring
  | succ state =>
      have hforward := affineQueueCoordinate_succ_sub center scale (state + 1) hscale
      have hbackward :
          affineQueueCoordinate center scale ((state + 1) - 1) -
            affineQueueCoordinate center scale (state + 1) = -(1 / scale) := by
        unfold affineQueueCoordinate
        norm_num [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]
        field_simp [hscale]
        ring
      have hbackward' :
          affineQueueCoordinate center scale state -
            affineQueueCoordinate center scale (state + 1) = -(1 / scale) := by
        simpa using hbackward
      rw [birthDeathScaledThirdMoment, birthDeathScaledDrift]
      simp only [Nat.succ_sub_one]
      rw [hforward, hbackward']
      ring

/-- At a positive state, affine scaling turns generator drift into the
birth-minus-death rate divided by the scale. -/
theorem birthDeathScaledDrift_affine_of_pos
    (rates : BirthDeathRates) (center scale : ℝ) (state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) :
    birthDeathScaledDrift rates (affineQueueCoordinate center scale) state =
      (rates.birth state - rates.death state) / scale := by
  unfold birthDeathScaledDrift affineQueueCoordinate
  have hstate_one : 1 ≤ state := hstate
  norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_sub hstate_one]
  field_simp [hscale]
  ring

/-- At a positive state, affine scaling turns the generator second jump moment
into the birth-plus-death rate divided by the squared scale. -/
theorem birthDeathScaledVariance_affine_of_pos
    (rates : BirthDeathRates) (center scale : ℝ) (state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) :
    birthDeathScaledVariance rates (affineQueueCoordinate center scale) state =
      (rates.birth state + rates.death state) / scale ^ 2 := by
  unfold birthDeathScaledVariance affineQueueCoordinate
  have hstate_one : 1 ≤ state := hstate
  norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_sub hstate_one]
  field_simp [hscale]
  ring

/-- At the reflecting boundary, the downward zero rate leaves only the birth
contribution to affine generator drift. -/
theorem birthDeathScaledDrift_affine_zero
    (rates : BirthDeathRates) (center scale : ℝ) (hscale : scale ≠ 0) :
    birthDeathScaledDrift rates (affineQueueCoordinate center scale) 0 =
      rates.birth 0 / scale := by
  unfold birthDeathScaledDrift affineQueueCoordinate
  simp only [zero_add, Nat.cast_zero]
  rw [rates.death_zero]
  simp
  field_simp [hscale]
  ring

/-- At the reflecting boundary, the downward zero rate leaves only the birth
contribution to the affine generator second jump moment. -/
theorem birthDeathScaledVariance_affine_zero
    (rates : BirthDeathRates) (center scale : ℝ) (hscale : scale ≠ 0) :
    birthDeathScaledVariance rates (affineQueueCoordinate center scale) 0 =
      rates.birth 0 / scale ^ 2 := by
  unfold birthDeathScaledVariance affineQueueCoordinate
  simp only [zero_add, Nat.cast_zero]
  rw [rates.death_zero]
  simp
  field_simp [hscale]
  ring

/-- The positive-state affine drift of the many-server queue is the service
rate times offered-capacity imbalance, divided by the scale. -/
theorem manyServerBirthDeath_scaledDrift_affine_of_pos
    (trafficIntensity serviceRate center scale : ℝ) (servers state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) :
    birthDeathScaledDrift
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate center scale) state =
      (serviceRate * ((servers : ℝ) * trafficIntensity - (Nat.min state servers : ℝ))) /
        scale := by
  rw [birthDeathScaledDrift_affine_of_pos _ _ _ _ hscale hstate]
  simp only [manyServerBirthDeathRates]
  ring

/-- The positive-state affine generator second jump moment of the many-server
queue is the service rate times total offered and active capacity, divided by
the squared scale. -/
theorem manyServerBirthDeath_scaledVariance_affine_of_pos
    (trafficIntensity serviceRate center scale : ℝ) (servers state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) :
    birthDeathScaledVariance
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate center scale) state =
      (serviceRate * ((servers : ℝ) * trafficIntensity + (Nat.min state servers : ℝ))) /
        scale ^ 2 := by
  rw [birthDeathScaledVariance_affine_of_pos _ _ _ _ hscale hstate]
  simp only [manyServerBirthDeathRates]
  ring

/-- Above the full-occupancy threshold, affine many-server drift has the
constant spare-capacity form. -/
theorem manyServerBirthDeath_scaledDrift_affine_atOrAbove
    (trafficIntensity serviceRate center scale : ℝ) (servers state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) (hservers_le : servers ≤ state) :
    birthDeathScaledDrift
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate center scale) state =
      (serviceRate * (servers : ℝ) * (trafficIntensity - 1)) / scale := by
  rw [manyServerBirthDeath_scaledDrift_affine_of_pos
    trafficIntensity serviceRate center scale servers state hscale hstate]
  have hmin : (Nat.min state servers : ℝ) = servers := by
    exact_mod_cast Nat.min_eq_right hservers_le
  rw [hmin]
  ring

/-- At or below the full-occupancy threshold, affine many-server drift uses
the current queue length as the active-service multiplicity. -/
theorem manyServerBirthDeath_scaledDrift_affine_atOrBelow
    (trafficIntensity serviceRate center scale : ℝ) (servers state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) (hstate_le : state ≤ servers) :
    birthDeathScaledDrift
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate center scale) state =
      (serviceRate * ((servers : ℝ) * trafficIntensity - state)) / scale := by
  rw [manyServerBirthDeath_scaledDrift_affine_of_pos
    trafficIntensity serviceRate center scale servers state hscale hstate]
  have hmin : (Nat.min state servers : ℝ) = state := by
    exact_mod_cast Nat.min_eq_left hstate_le
  rw [hmin]

/-- Above the full-occupancy threshold, affine many-server second jump moment
has the constant full-service form. -/
theorem manyServerBirthDeath_scaledVariance_affine_atOrAbove
    (trafficIntensity serviceRate center scale : ℝ) (servers state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) (hservers_le : servers ≤ state) :
    birthDeathScaledVariance
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate center scale) state =
      (serviceRate * (servers : ℝ) * (trafficIntensity + 1)) / scale ^ 2 := by
  rw [manyServerBirthDeath_scaledVariance_affine_of_pos
    trafficIntensity serviceRate center scale servers state hscale hstate]
  have hmin : (Nat.min state servers : ℝ) = servers := by
    exact_mod_cast Nat.min_eq_right hservers_le
  rw [hmin]
  ring

/-- At or below the full-occupancy threshold, affine many-server second jump
moment uses the active-service multiplicity at the current state. -/
theorem manyServerBirthDeath_scaledVariance_affine_atOrBelow
    (trafficIntensity serviceRate center scale : ℝ) (servers state : ℕ)
    (hscale : scale ≠ 0) (hstate : 0 < state) (hstate_le : state ≤ servers) :
    birthDeathScaledVariance
      (manyServerBirthDeathRates ((servers : ℝ) * trafficIntensity * serviceRate)
        serviceRate servers)
      (affineQueueCoordinate center scale) state =
      (serviceRate * ((servers : ℝ) * trafficIntensity + state)) / scale ^ 2 := by
  rw [manyServerBirthDeath_scaledVariance_affine_of_pos
    trafficIntensity serviceRate center scale servers state hscale hstate]
  have hmin : (Nat.min state servers : ℝ) = state := by
    exact_mod_cast Nat.min_eq_left hstate_le
  rw [hmin]

end AppliedModelingLib.Probability.Queueing

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Perturbed contractive recurrences

Deterministic bounds for an iteration whose update is contractive up to a
per-round additive perturbation.  These lemmas separate the algorithmic part
of finite-sample convergence arguments from the probability estimate that
controls the perturbations.
-/

open scoped BigOperators

namespace AppliedModelingLib.Optimization

/-- Reindexing the finite geometric sum after multiplying by its common ratio. -/
theorem mul_geometric_sum_add_one (contraction : ℝ) : ∀ iteration : ℕ,
    contraction * ∑ index ∈ Finset.range iteration, contraction ^ index + 1 =
      ∑ index ∈ Finset.range (iteration + 1), contraction ^ index := by
  intro iteration
  induction iteration with
  | zero => simp
  | succ iteration ih =>
      calc
        contraction * ∑ index ∈ Finset.range (iteration + 1), contraction ^ index + 1 =
            contraction * (∑ index ∈ Finset.range iteration, contraction ^ index +
              contraction ^ iteration) + 1 := by
                rw [Finset.sum_range_succ]
        _ = (contraction * ∑ index ∈ Finset.range iteration, contraction ^ index + 1) +
              contraction ^ (iteration + 1) := by
                rw [pow_succ]
                ring
        _ = ∑ index ∈ Finset.range (iteration + 1), contraction ^ index +
              contraction ^ (iteration + 1) := by rw [ih]
        _ = ∑ index ∈ Finset.range ((iteration + 1) + 1), contraction ^ index := by
              simpa using
                (Finset.sum_range_succ (fun index => contraction ^ index) (iteration + 1)).symm

/-- An affine contractive recurrence stays inside a radius that absorbs its error. -/
theorem affine_recurrence_le_radius
    {distance : ℕ → ℝ} {contraction error radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hinitial : distance 0 ≤ radius)
    (herror : error ≤ (1 - contraction) * radius)
    (hrecur : ∀ iteration, distance (iteration + 1) ≤
      contraction * distance iteration + error) :
    ∀ iteration, distance iteration ≤ radius := by
  intro iteration
  induction iteration with
  | zero => simpa using hinitial
  | succ iteration ih =>
      calc
        distance (iteration + 1) ≤ contraction * distance iteration + error :=
          hrecur iteration
        _ ≤ contraction * radius + error := by
          gcongr
        _ ≤ radius := by linarith

/-- A finite prefix of an affine contractive recurrence stays in an absorbing radius. -/
theorem affine_recurrence_le_radius_up_to
    {distance : ℕ → ℝ} {contraction error radius : ℝ} (horizon : ℕ)
    (hcontraction_nonneg : 0 ≤ contraction)
    (hinitial : distance 0 ≤ radius)
    (herror : error ≤ (1 - contraction) * radius)
    (hrecur : ∀ iteration, iteration < horizon → distance (iteration + 1) ≤
      contraction * distance iteration + error) :
    ∀ iteration, iteration ≤ horizon → distance iteration ≤ radius := by
  intro iteration hiteration
  induction iteration with
  | zero => simpa using hinitial
  | succ iteration ih =>
      have hlt : iteration < horizon := by omega
      calc
        distance (iteration + 1) ≤ contraction * distance iteration + error :=
          hrecur iteration hlt
        _ ≤ contraction * radius + error := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hlt)) hcontraction_nonneg) le_rfl
        _ ≤ radius := by linarith

/--
If a nonnegative distance contracts whenever it is outside a target radius,
and the target radius is forward invariant once entered, then any displayed
geometric entry bound yields a permanent radius bound from that iteration on.

This is the deterministic two-region recurrence used by finite-sample
arguments that first contract toward a solution and then control the noise
floor.  It deliberately leaves selection of the entry time (for example by a
logarithmic estimate) to the caller.
-/
theorem two_phase_contraction_enters_and_stays
    {distance : ℕ → ℝ} {contraction radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (houtside : ∀ iteration, radius < distance iteration →
      distance (iteration + 1) ≤ contraction * distance iteration)
    (hinside : ∀ iteration, distance iteration ≤ radius →
      distance (iteration + 1) ≤ radius)
    (entryIteration : ℕ)
    (hentry : contraction ^ entryIteration * distance 0 ≤ radius) :
    ∀ iteration, entryIteration ≤ iteration → distance iteration ≤ radius := by
  have hbeforeEntry : ∀ iteration,
      distance iteration ≤ radius ∨ distance iteration ≤ contraction ^ iteration * distance 0 := by
    intro iteration
    induction iteration with
    | zero =>
        right
        simp
    | succ iteration ih =>
        rcases ih with hinsideradius | hgeometric
        · left
          exact hinside iteration hinsideradius
        · by_cases hcurrent : distance iteration ≤ radius
          · left
            exact hinside iteration hcurrent
          · right
            have houtside' : radius < distance iteration := lt_of_not_ge hcurrent
            calc
              distance (iteration + 1) ≤ contraction * distance iteration :=
                houtside iteration houtside'
              _ ≤ contraction * (contraction ^ iteration * distance 0) := by
                exact mul_le_mul_of_nonneg_left hgeometric hcontraction_nonneg
              _ = contraction ^ (iteration + 1) * distance 0 := by
                rw [pow_succ]
                ring
  intro iteration hiteration
  induction iteration, hiteration using Nat.le_induction with
  | base =>
      rcases hbeforeEntry entryIteration with hinsideradius | hgeometric
      · exact hinsideradius
      · exact hgeometric.trans hentry
  | succ iteration _ ih =>
      exact hinside iteration ih

/--
An affine contractive recurrence enters and stays in a radius once its
perturbation is small enough both to be absorbed inside that radius and to be
charged to a larger outside contraction factor.  This packages the usual
two-region ``contract until the noise floor, then remain there'' argument.
-/
theorem affine_recurrence_enters_and_stays
    {distance : ℕ → ℝ} {contraction outerContraction error radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_le_outer : contraction ≤ outerContraction)
    (herror_outer : error ≤ (outerContraction - contraction) * radius)
    (herror_absorbed : error ≤ (1 - contraction) * radius)
    (hrecur : ∀ iteration, distance (iteration + 1) ≤
      contraction * distance iteration + error)
    (entryIteration : ℕ)
    (hentry : outerContraction ^ entryIteration * distance 0 ≤ radius) :
    ∀ iteration, entryIteration ≤ iteration → distance iteration ≤ radius := by
  have houter_nonneg : 0 ≤ outerContraction := hcontraction_nonneg.trans hcontraction_le_outer
  have hdifference_nonneg : 0 ≤ outerContraction - contraction :=
    sub_nonneg.mpr hcontraction_le_outer
  apply two_phase_contraction_enters_and_stays houter_nonneg
  · intro iteration houtside
    calc
      distance (iteration + 1) ≤ contraction * distance iteration + error :=
        hrecur iteration
      _ ≤ contraction * distance iteration +
          (outerContraction - contraction) * radius := by
        linarith [herror_outer]
      _ ≤ contraction * distance iteration +
          (outerContraction - contraction) * distance iteration := by
        have hscale :=
          mul_le_mul_of_nonneg_left (le_of_lt houtside) hdifference_nonneg
        linarith [hscale]
      _ = outerContraction * distance iteration := by ring
  · intro iteration hinsideradius
    calc
      distance (iteration + 1) ≤ contraction * distance iteration + error :=
        hrecur iteration
      _ ≤ contraction * radius + error := by
        have hscale :=
          mul_le_mul_of_nonneg_left hinsideradius hcontraction_nonneg
        linarith [hscale]
      _ ≤ contraction * radius + (1 - contraction) * radius := by
        linarith [herror_absorbed]
      _ = radius := by ring
  · exact hentry

/--
Every nonnegative strict geometric contraction reaches a positive radius from
an arbitrary finite initial distance.

Library provenance: this directly reuses Mathlib's
`tendsto_pow_atTop_nhds_zero_of_lt_one` from
[`Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem exists_entryIteration_of_nonneg_lt_one
    {outerContraction initialDistance radius : ℝ}
    (houter_nonneg : 0 ≤ outerContraction) (houter_lt_one : outerContraction < 1)
    (hradius_pos : 0 < radius) :
    ∃ entryIteration : ℕ,
      outerContraction ^ entryIteration * initialDistance ≤ radius := by
  have htendsto : Filter.Tendsto
      (fun entryIteration : ℕ => outerContraction ^ entryIteration * initialDistance)
      Filter.atTop (nhds 0) :=
    by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one houter_nonneg houter_lt_one).mul_const
          initialDistance
  have hsmall : ∀ᶠ entryIteration : ℕ in Filter.atTop,
      outerContraction ^ entryIteration * initialDistance < radius :=
    htendsto.eventually (eventually_lt_nhds hradius_pos)
  obtain ⟨entryIteration, hentry⟩ := hsmall.exists
  exact ⟨entryIteration, hentry.le⟩

/--
An affine recurrence with a strict outer contraction eventually enters and
then stays in its absorbing radius. This is the existential-entry form of
`affine_recurrence_enters_and_stays`; the latter remains available when a
paper supplies a quantitative logarithmic entry time.
-/
theorem affine_recurrence_eventually_enters_and_stays
    {distance : ℕ → ℝ} {contraction outerContraction error radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_le_outer : contraction ≤ outerContraction)
    (houter_lt_one : outerContraction < 1)
    (hradius_pos : 0 < radius)
    (herror_outer : error ≤ (outerContraction - contraction) * radius)
    (herror_absorbed : error ≤ (1 - contraction) * radius)
    (hrecur : ∀ iteration, distance (iteration + 1) ≤
      contraction * distance iteration + error) :
    ∃ entryIteration : ℕ,
      ∀ iteration, entryIteration ≤ iteration → distance iteration ≤ radius := by
  have houter_nonneg : 0 ≤ outerContraction := hcontraction_nonneg.trans hcontraction_le_outer
  obtain ⟨entryIteration, hentry⟩ :=
    exists_entryIteration_of_nonneg_lt_one houter_nonneg houter_lt_one hradius_pos
  refine ⟨entryIteration, affine_recurrence_enters_and_stays hcontraction_nonneg
    hcontraction_le_outer herror_outer herror_absorbed hrecur entryIteration hentry⟩

/--
If an affine perturbation is at most the contraction coefficient times the
target radius, a coefficient strictly below one half gives the standard
two-region entry argument with outer factor `2 * contraction`. This is the
numerical form used by empirical risk-minimization arguments that budget one
contraction-radius of sampling error outside the ball and retain the ball
after entry.
-/
theorem affine_recurrence_eventually_enters_and_stays_of_error_le_contraction_radius
    {distance : ℕ → ℝ} {contraction error radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction) (hcontraction_lt_half : contraction < 1 / 2)
    (hradius_pos : 0 < radius) (herror : error ≤ contraction * radius)
    (hrecur : ∀ iteration, distance (iteration + 1) ≤
      contraction * distance iteration + error) :
    ∃ entryIteration : ℕ,
      ∀ iteration, entryIteration ≤ iteration → distance iteration ≤ radius := by
  apply affine_recurrence_eventually_enters_and_stays hcontraction_nonneg
    (by nlinarith : contraction ≤ 2 * contraction)
    (by nlinarith : 2 * contraction < 1) hradius_pos
  · convert herror using 1 <;> ring
  · calc
      error ≤ contraction * radius := herror
      _ ≤ (1 - contraction) * radius := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact hradius_pos.le
  · exact hrecur

/--
The common strong-convexity contraction ratio is nonnegative and strictly
smaller than one half when the sensitivity is below the corresponding
half-ratio threshold.  This isolates the numerical premise needed by a
two-region affine recurrence.
-/
theorem contraction_ratio_nonneg_lt_half_of_lt_modulus_div_two_smoothness
    {sensitivity smoothness modulus : ℝ}
    (hsensitivity_nonneg : 0 ≤ sensitivity) (hsmoothness_pos : 0 < smoothness)
    (hmodulus_pos : 0 < modulus)
    (hsensitivity_lt : sensitivity < modulus / (2 * smoothness)) :
    0 ≤ sensitivity * smoothness / modulus ∧
      sensitivity * smoothness / modulus < 1 / 2 := by
  constructor
  · positivity
  · apply (div_lt_iff₀ hmodulus_pos).mpr
    have hscaled : sensitivity * (2 * smoothness) < modulus :=
      (lt_div_iff₀ (by positivity : 0 < 2 * smoothness)).mp hsensitivity_lt
    nlinarith

/-- The exact finite-horizon bound for an affine contractive recurrence. -/
theorem affine_recurrence_le_geometric_sum
    {distance : ℕ → ℝ} {contraction error : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hrecur : ∀ iteration, distance (iteration + 1) ≤
      contraction * distance iteration + error) :
    ∀ iteration, distance iteration ≤ contraction ^ iteration * distance 0 +
      error * ∑ index ∈ Finset.range iteration, contraction ^ index := by
  intro iteration
  induction iteration with
  | zero => simp
  | succ iteration ih =>
      calc
        distance (iteration + 1) ≤ contraction * distance iteration + error :=
          hrecur iteration
        _ ≤ contraction *
            (contraction ^ iteration * distance 0 +
              error * ∑ index ∈ Finset.range iteration, contraction ^ index) + error := by
            gcongr
        _ = contraction ^ (iteration + 1) * distance 0 +
            error * (contraction * ∑ index ∈ Finset.range iteration, contraction ^ index + 1) := by
            rw [pow_succ]
            ring
        _ = contraction ^ (iteration + 1) * distance 0 +
            error * ∑ index ∈ Finset.range (iteration + 1), contraction ^ index := by
            rw [mul_geometric_sum_add_one]

/--
A trajectory that is at most `error` away from a contractive update obeys the
corresponding affine distance recurrence to any fixed point.
-/
theorem dist_le_affine_of_perturbed_contraction
    {State : Type*} [PseudoMetricSpace State]
    (update : State → State) (trajectory : ℕ → State) (fixedPoint : State)
    {contraction error : ℝ}
    (hfixed : update fixedPoint = fixedPoint)
    (hcontract : ∀ state,
      dist (update state) (update fixedPoint) ≤ contraction * dist state fixedPoint)
    (hperturb : ∀ iteration,
      dist (trajectory (iteration + 1)) (update (trajectory iteration)) ≤ error) :
    ∀ iteration, dist (trajectory (iteration + 1)) fixedPoint ≤
      contraction * dist (trajectory iteration) fixedPoint + error := by
  intro iteration
  calc
    dist (trajectory (iteration + 1)) fixedPoint ≤
        dist (trajectory (iteration + 1)) (update (trajectory iteration)) +
          dist (update (trajectory iteration)) fixedPoint := by
            simpa [hfixed] using dist_triangle (trajectory (iteration + 1))
              (update (trajectory iteration)) (update fixedPoint)
    _ ≤ error + contraction * dist (trajectory iteration) fixedPoint := by
      exact add_le_add (hperturb iteration) (by
        simpa [hfixed] using hcontract (trajectory iteration))
    _ = contraction * dist (trajectory iteration) fixedPoint + error := by ring

/--
If each perturbation is absorbed by a contractive radius, the entire trajectory
remains in that radius around the fixed point.
-/
theorem dist_le_radius_of_perturbed_contraction
    {State : Type*} [PseudoMetricSpace State]
    (update : State → State) (trajectory : ℕ → State) (fixedPoint : State)
    {contraction error radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hfixed : update fixedPoint = fixedPoint)
    (hcontract : ∀ state,
      dist (update state) (update fixedPoint) ≤ contraction * dist state fixedPoint)
    (hperturb : ∀ iteration,
      dist (trajectory (iteration + 1)) (update (trajectory iteration)) ≤ error)
    (hinitial : dist (trajectory 0) fixedPoint ≤ radius)
    (herror : error ≤ (1 - contraction) * radius) :
    ∀ iteration, dist (trajectory iteration) fixedPoint ≤ radius := by
  apply affine_recurrence_le_radius hcontraction_nonneg hinitial herror
  intro iteration
  exact dist_le_affine_of_perturbed_contraction update trajectory fixedPoint
    hfixed hcontract hperturb iteration

/--
The finite-prefix version of `dist_le_radius_of_perturbed_contraction`, used
when concentration has only been established through a prescribed horizon.
-/
theorem dist_le_radius_of_perturbed_contraction_up_to
    {State : Type*} [PseudoMetricSpace State]
    (update : State → State) (trajectory : ℕ → State) (fixedPoint : State)
    {contraction error radius : ℝ} (horizon : ℕ)
    (hcontraction_nonneg : 0 ≤ contraction)
    (hfixed : update fixedPoint = fixedPoint)
    (hcontract : ∀ state,
      dist (update state) (update fixedPoint) ≤ contraction * dist state fixedPoint)
    (hperturb : ∀ iteration, iteration < horizon →
      dist (trajectory (iteration + 1)) (update (trajectory iteration)) ≤ error)
    (hinitial : dist (trajectory 0) fixedPoint ≤ radius)
    (herror : error ≤ (1 - contraction) * radius) :
    ∀ iteration, iteration ≤ horizon → dist (trajectory iteration) fixedPoint ≤ radius := by
  apply affine_recurrence_le_radius_up_to horizon hcontraction_nonneg hinitial herror
  intro iteration hiteration
  calc
    dist (trajectory (iteration + 1)) fixedPoint ≤
        dist (trajectory (iteration + 1)) (update (trajectory iteration)) +
          dist (update (trajectory iteration)) fixedPoint := by
            simpa [hfixed] using dist_triangle (trajectory (iteration + 1))
              (update (trajectory iteration)) (update fixedPoint)
    _ ≤ error + contraction * dist (trajectory iteration) fixedPoint := by
      exact add_le_add (hperturb iteration hiteration) (by
        simpa [hfixed] using hcontract (trajectory iteration))
    _ = contraction * dist (trajectory iteration) fixedPoint + error := by ring

end AppliedModelingLib.Optimization

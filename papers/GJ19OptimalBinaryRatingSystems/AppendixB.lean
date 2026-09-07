import GJ19OptimalBinaryRatingSystems.ContinuumTheorems
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability
open Filter Topology
open MeasureTheory

/--
The quality-by-observation domain on which the Appendix B learning statements
are uniform: source quality lies in `[0,1]` and the observation coordinate is
unrestricted.
-/
def lemmaBUniformLearningDomain (Y : Type*) : Set (ℝ × Y) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.univ

/--
Equispaced interval quantile map: the interval index `floor (M θ)` normalized
by `M`.  This is the quantile map used by the Kendall/Spearman equispaced
partition branch of Corollary C.4.
-/
noncomputable def equispacedIntervalQuantile (M : ℕ) (θ : ℝ) : ℝ :=
  (Nat.floor ((M : ℝ) * θ) : ℝ) / (M : ℝ)

/--
Source endpoint selector for a binary level vector: choose the endpoint indexed
by `floor((m+2) θ)`, clamped to the last endpoint.  The clamp is only active
at the right endpoint of `[0,1]`.
-/
noncomputable def clampedFloorLevelIndex (m : ℕ) (θ : ℝ) : Fin (m + 2) :=
  ⟨min (Nat.floor (((m + 2 : ℕ) : ℝ) * θ)) (m + 1), by
    have hle :
        min (Nat.floor (((m + 2 : ℕ) : ℝ) * θ)) (m + 1) ≤ m + 1 :=
      Nat.min_le_right _ _
    omega⟩

theorem clampedFloorLevelIndex_val (m : ℕ) (θ : ℝ) :
    (clampedFloorLevelIndex m θ).1 =
      min (Nat.floor (((m + 2 : ℕ) : ℝ) * θ)) (m + 1) := by
  rfl

/--
If two source coordinates are within `B/(m+2)` in the forward direction, their
clamped endpoint-floor indices differ by at most `B`.
-/
theorem clampedFloorLevelIndex_le_add_of_le_add_div
    (m B : ℕ) {x y : ℝ} (hy0 : 0 ≤ y)
    (hxy : x ≤ y + (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    (clampedFloorLevelIndex m x).1 ≤
      (clampedFloorLevelIndex m y).1 + B := by
  let scale : ℝ := ((m + 2 : ℕ) : ℝ)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hscale_nonneg : 0 ≤ scale := le_of_lt hscale_pos
  set rawX : ℕ := Nat.floor (scale * x)
  set rawY : ℕ := Nat.floor (scale * y)
  have hmul_le : scale * x ≤ scale * y + (B : ℝ) := by
    calc
      scale * x ≤ scale * (y + (B : ℝ) / scale) := by
        exact mul_le_mul_of_nonneg_left (by simpa [scale] using hxy)
          hscale_nonneg
      _ = scale * y + (B : ℝ) := by
        field_simp [ne_of_gt hscale_pos]
  have hfloor_add :
      Nat.floor (scale * y + (B : ℝ)) = rawY + B := by
    have hbase_nonneg : 0 ≤ scale * y := mul_nonneg hscale_nonneg hy0
    simpa [rawY] using Nat.floor_add_natCast hbase_nonneg B
  have hraw : rawX ≤ rawY + B := by
    have hfloor_le :
        Nat.floor (scale * x) ≤ Nat.floor (scale * y + (B : ℝ)) :=
      Nat.floor_mono hmul_le
    simpa [rawX, hfloor_add] using hfloor_le
  simp only [clampedFloorLevelIndex_val]
  change min rawX (m + 1) ≤ min rawY (m + 1) + B
  by_cases hrawY_cap : rawY ≤ m + 1
  · have hminY : min rawY (m + 1) = rawY := Nat.min_eq_left hrawY_cap
    rw [hminY]
    exact (Nat.min_le_left rawX (m + 1)).trans hraw
  · have hminY : min rawY (m + 1) = m + 1 := Nat.min_eq_right (by omega)
    rw [hminY]
    have hcap : min rawX (m + 1) ≤ m + 1 := Nat.min_le_right rawX (m + 1)
    omega

/--
If two source coordinates are within `B/(m+2)` in metric distance, their
clamped endpoint-floor indices differ by at most `B` in the forward direction.
-/
theorem clampedFloorLevelIndex_le_add_of_dist_le_div
    (m B : ℕ) {x y : ℝ} (hy0 : 0 ≤ y)
    (hdist : dist x y ≤ (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    (clampedFloorLevelIndex m x).1 ≤
      (clampedFloorLevelIndex m y).1 + B := by
  have hdist_abs : |x - y| ≤ (B : ℝ) / (((m + 2 : ℕ) : ℝ)) := by
    simpa [Real.dist_eq] using hdist
  have hxy : x ≤ y + (B : ℝ) / (((m + 2 : ℕ) : ℝ)) := by
    have hx_sub : x - y ≤ (B : ℝ) / (((m + 2 : ℕ) : ℝ)) :=
      (le_abs_self (x - y)).trans hdist_abs
    linarith
  exact clampedFloorLevelIndex_le_add_of_le_add_div m B hy0 hxy

/--
For an equispaced source partition, the paper's quantile map
`floor ((m+2) * θ)/(m+2)` selects exactly the same endpoint as the direct
clamped floor selector. This is the formal version of the Corollary C.4
source sentence that `x_θ = θ` meets the B.1 criterion.
-/
theorem clampedFloorLevelIndex_equispacedIntervalQuantile_eq
    (m : ℕ) (θ : ℝ) :
    clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ) =
      clampedFloorLevelIndex m θ := by
  apply Fin.ext
  simp only [clampedFloorLevelIndex_val, equispacedIntervalQuantile]
  let scale : ℝ := (m : ℝ) + 2
  let raw : ℕ := Nat.floor (scale * θ)
  have hden : scale ≠ 0 := by
    dsimp [scale]
    positivity
  have hfloor :
      Nat.floor (scale * ((raw : ℝ) / scale)) = raw := by
    have hmul : scale * ((raw : ℝ) / scale) = raw := by
      field_simp [hden]
    rw [hmul, Nat.floor_natCast]
  simpa [scale, raw, Nat.cast_add, Nat.cast_ofNat] using
    congrArg (fun n : ℕ => min n (m + 1)) hfloor

/--
Source-selector normalization for Theorem B.1.  If a source interval-index
selector has the same clamped floor value as the canonical selector, then it
is definitionally the selector required by the common-floor B.1 bridge.
-/
theorem clampedFloorLevelIndex_eq_of_val_eq
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hval :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * sourceCoord θ)) (m + 1)) :
    ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
      levelIndex m θ = clampedFloorLevelIndex m (sourceCoord θ) := by
  intro m θ hθ
  apply Fin.ext
  rw [hval m θ hθ, clampedFloorLevelIndex_val]

/--
The clamped source endpoint selector supplies exactly the old/refined index
windows consumed by the five-point C.5 bridge.
-/
theorem clampedFloorLevelIndex_old_refined_five_window
    {m : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ i : Fin m,
      i.1 ≤ (clampedFloorLevelIndex m θ).1 ∧
      (clampedFloorLevelIndex m θ).1 ≤ i.1 + 2 ∧
      2 * i.1 ≤ (clampedFloorLevelIndex (2 * m + 1) θ).1 ∧
      (clampedFloorLevelIndex (2 * m + 1) θ).1 ≤ 2 * i.1 + 4 := by
  let oldRaw : ℕ := Nat.floor (((m + 2 : ℕ) : ℝ) * θ)
  let refinedRaw : ℕ :=
    Nat.floor ((((2 : ℝ) * ((m + 2 : ℕ) : ℝ)) - 1) * θ)
  have hfloor :
      refinedRaw ≤ 2 * oldRaw + 1 ∧ 2 * oldRaw ≤ refinedRaw + 2 := by
    simpa [oldRaw, refinedRaw, Nat.cast_add, Nat.cast_ofNat, mul_add,
      add_mul, two_mul] using
      AppliedModelingLib.Math.nat_floor_two_mul_sub_one_mul_window
        (M := m + 2) (by omega) hθ0 hθ1
  have hold_val :
      (clampedFloorLevelIndex m θ).1 = min oldRaw (m + 1) := by
    simp [clampedFloorLevelIndex, oldRaw]
  have href_val :
      (clampedFloorLevelIndex (2 * m + 1) θ).1 =
        min refinedRaw (2 * m + 2) := by
    simp [clampedFloorLevelIndex, refinedRaw]
    congr 2
    ring
  by_cases hzero : oldRaw = 0
  · refine ⟨⟨0, hm⟩, ?_, ?_, ?_, ?_⟩
    · rw [hold_val, hzero]
      simp
    · rw [hold_val, hzero]
      simp
    · simp
    · rw [href_val]
      have href_le : refinedRaw ≤ 1 := by
        simpa [hzero] using hfloor.1
      exact (Nat.min_le_left refinedRaw (2 * m + 2)).trans (by omega)
  · by_cases hle : oldRaw ≤ m
    · let i : Fin m := ⟨oldRaw - 1, by omega⟩
      have hold_pos : 0 < oldRaw := Nat.pos_of_ne_zero hzero
      refine ⟨i, ?_, ?_, ?_, ?_⟩
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = oldRaw := by
          exact Nat.min_eq_left (by omega)
        have htarget : oldRaw - 1 ≤ oldRaw := by omega
        simpa [i, hold_min] using htarget
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = oldRaw := by
          exact Nat.min_eq_left (by omega)
        have htarget : oldRaw ≤ oldRaw - 1 + 2 := by omega
        simpa [i, hold_min] using htarget
      · rw [href_val]
        have href_ge : 2 * (oldRaw - 1) ≤ refinedRaw := by
          omega
        have href_cap_ge : 2 * (oldRaw - 1) ≤ 2 * m + 2 := by
          omega
        exact le_min href_ge href_cap_ge
      · rw [href_val]
        have href_le : min refinedRaw (2 * m + 2) ≤ refinedRaw :=
          Nat.min_le_left refinedRaw (2 * m + 2)
        have htarget :
            min refinedRaw (2 * m + 2) ≤ 2 * (oldRaw - 1) + 4 :=
          href_le.trans (by omega)
        simpa [i] using htarget
    · let i : Fin m := ⟨m - 1, by omega⟩
      refine ⟨i, ?_, ?_, ?_, ?_⟩
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = m + 1 := by
          exact Nat.min_eq_right (by omega)
        have htarget : m - 1 ≤ m + 1 := by omega
        simpa [i, hold_min] using htarget
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = m + 1 := by
          exact Nat.min_eq_right (by omega)
        have htarget : m + 1 ≤ m - 1 + 2 := by omega
        simpa [i, hold_min] using htarget
      · rw [href_val]
        have href_ge : 2 * m ≤ refinedRaw := by
          omega
        have href_cap_ge : 2 * m ≤ 2 * m + 2 := by omega
        have hmin_ge :
            2 * m ≤ min refinedRaw (2 * m + 2) :=
          le_min href_ge href_cap_ge
        simp [i]
        omega
      · rw [href_val]
        have href_le : min refinedRaw (2 * m + 2) ≤ 2 * m + 2 :=
          Nat.min_le_right refinedRaw (2 * m + 2)
        simp [i]
        omega

/--
Q-step source selector window.  The old clamped floor index and the q-times
refined clamped floor index fit the scaled two-step window consumed by the
iterated C.5 block inclusion.
-/
theorem clampedFloorLevelIndex_iterated_old_refined_scaled_window
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ i : Fin m,
      i.1 ≤ (clampedFloorLevelIndex m θ).1 ∧
      (clampedFloorLevelIndex m θ).1 ≤ i.1 + 2 ∧
      2 ^ q * i.1 ≤
        (clampedFloorLevelIndex
          (uniformDoubledEndpointIndexIterate m q) θ).1 ∧
      (clampedFloorLevelIndex
          (uniformDoubledEndpointIndexIterate m q) θ).1 ≤
        2 ^ q * (i.1 + 2) := by
  let scale : ℕ := 2 ^ q
  let oldRaw : ℕ := Nat.floor (((m + 2 : ℕ) : ℝ) * θ)
  let refinedRaw : ℕ :=
    Nat.floor (((scale * (m + 1) + 1 : ℕ) : ℝ) * θ)
  have hfloor :
      refinedRaw ≤ scale * oldRaw + scale ∧
        scale * oldRaw ≤ refinedRaw + scale := by
    simpa [scale, oldRaw, refinedRaw] using
      AppliedModelingLib.Math.nat_floor_dyadic_pred_add_one_mul_window
        (M := m + 2) (q := q) (by omega) hθ0 hθ1
  have hold_val :
      (clampedFloorLevelIndex m θ).1 = min oldRaw (m + 1) := by
    simp [clampedFloorLevelIndex, oldRaw]
  have hiter_cap :
      uniformDoubledEndpointIndexIterate m q + 1 = scale * (m + 1) := by
    dsimp [scale]
    exact uniformDoubledEndpointIndexIterate_add_one m q
  have hiter_grid :
      uniformDoubledEndpointIndexIterate m q + 2 =
        scale * (m + 1) + 1 := by
    omega
  have href_val :
      (clampedFloorLevelIndex
          (uniformDoubledEndpointIndexIterate m q) θ).1 =
        min refinedRaw (scale * (m + 1)) := by
    simp [clampedFloorLevelIndex, refinedRaw, hiter_cap, hiter_grid]
  by_cases hzero : oldRaw = 0
  · refine ⟨⟨0, hm⟩, ?_, ?_, ?_, ?_⟩
    · rw [hold_val, hzero]
      simp
    · rw [hold_val, hzero]
      simp
    · simp
    · rw [href_val]
      have href_le : refinedRaw ≤ scale := by
        simpa [hzero] using hfloor.1
      have hcap_le : min refinedRaw (scale * (m + 1)) ≤ refinedRaw :=
        Nat.min_le_left refinedRaw (scale * (m + 1))
      have htarget : min refinedRaw (scale * (m + 1)) ≤ scale * (0 + 2) := by
        have hscale_le : scale ≤ scale * 2 :=
          Nat.le_mul_of_pos_right scale (by omega)
        exact hcap_le.trans (href_le.trans (by simpa using hscale_le))
      simpa [scale] using htarget
  · by_cases hle : oldRaw ≤ m
    · let i : Fin m := ⟨oldRaw - 1, by omega⟩
      have hold_pos : 0 < oldRaw := Nat.pos_of_ne_zero hzero
      refine ⟨i, ?_, ?_, ?_, ?_⟩
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = oldRaw := by
          exact Nat.min_eq_left (by omega)
        have htarget : oldRaw - 1 ≤ oldRaw := by omega
        simpa [i, hold_min] using htarget
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = oldRaw := by
          exact Nat.min_eq_left (by omega)
        have htarget : oldRaw ≤ oldRaw - 1 + 2 := by omega
        simpa [i, hold_min] using htarget
      · rw [href_val]
        have href_ge : scale * (oldRaw - 1) ≤ refinedRaw := by
          have hmul :
              scale * oldRaw = scale * (oldRaw - 1) + scale := by
            calc
              scale * oldRaw = scale * ((oldRaw - 1) + 1) :=
                congrArg (fun n : ℕ => scale * n) (by omega)
              _ = scale * (oldRaw - 1) + scale := by
                rw [Nat.mul_add, Nat.mul_one]
          omega
        have hcap_ge :
            scale * (oldRaw - 1) ≤ scale * (m + 1) := by
          exact Nat.mul_le_mul_left scale (by omega)
        exact le_min href_ge hcap_ge
      · rw [href_val]
        have href_le : min refinedRaw (scale * (m + 1)) ≤ refinedRaw :=
          Nat.min_le_left refinedRaw (scale * (m + 1))
        have htarget :
            min refinedRaw (scale * (m + 1)) ≤
              scale * ((oldRaw - 1) + 2) := by
          have hraw : refinedRaw ≤ scale * ((oldRaw - 1) + 2) := by
            have hmul :
                scale * oldRaw + scale =
                  scale * ((oldRaw - 1) + 2) := by
              calc
                scale * oldRaw + scale =
                    scale * ((oldRaw - 1) + 1) + scale :=
                  congrArg (fun n : ℕ => scale * n + scale) (by omega)
                _ = scale * ((oldRaw - 1) + 2) := by
                  ring_nf
            omega
          exact href_le.trans hraw
        simpa [i] using htarget
    · let i : Fin m := ⟨m - 1, by omega⟩
      refine ⟨i, ?_, ?_, ?_, ?_⟩
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = m + 1 := by
          exact Nat.min_eq_right (by omega)
        have htarget : m - 1 ≤ m + 1 := by omega
        simpa [i, hold_min] using htarget
      · rw [hold_val]
        have hold_min : min oldRaw (m + 1) = m + 1 := by
          exact Nat.min_eq_right (by omega)
        have htarget : m + 1 ≤ m - 1 + 2 := by omega
        simpa [i, hold_min] using htarget
      · rw [href_val]
        have href_ge : scale * m ≤ refinedRaw := by
          have hraw_ge : scale * (m + 1) ≤ scale * oldRaw :=
            Nat.mul_le_mul_left scale (by omega)
          have hmul : scale * (m + 1) = scale * m + scale := by
            rw [Nat.mul_add, Nat.mul_one]
          omega
        have hcap_ge : scale * m ≤ scale * (m + 1) :=
          Nat.mul_le_mul_left scale (by omega)
        have hmin_ge :
            scale * m ≤ min refinedRaw (scale * (m + 1)) :=
          le_min href_ge hcap_ge
        have htarget :
            scale * (m - 1) ≤ min refinedRaw (scale * (m + 1)) := by
          exact (Nat.mul_le_mul_left scale (by omega : m - 1 ≤ m)).trans hmin_ge
        simpa [i, scale] using htarget
      · rw [href_val]
        have href_le :
            min refinedRaw (scale * (m + 1)) ≤ scale * (m + 1) :=
          Nat.min_le_right refinedRaw (scale * (m + 1))
        have htarget :
            min refinedRaw (scale * (m + 1)) ≤ scale * ((m - 1) + 2) := by
          have hidx : (m - 1) + 2 = m + 1 := by omega
          simpa [hidx] using href_le
        simpa [i, scale] using htarget

/--
Q-step source-window package for B.1.  The old selected level and the q-times
refined selected level from the clamped floor convention lie in the same
original two-step bracket.
-/
theorem uniformDoubledEndpointLevelsIterate_clampedFloor_old_refined_mem_same_two_step_interval
    {m q : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin m,
      uniformDoubledEndpointLevelsIterate oldLevels q
          (clampedFloorLevelIndex
            (uniformDoubledEndpointIndexIterate m q) θ) ∈
          Set.Icc (oldLevels ⟨i.1, by omega⟩)
            (oldLevels ⟨i.1 + 2, by omega⟩) ∧
        oldLevels (clampedFloorLevelIndex m θ) ∈
          Set.Icc (oldLevels ⟨i.1, by omega⟩)
            (oldLevels ⟨i.1 + 2, by omega⟩) := by
  rcases clampedFloorLevelIndex_iterated_old_refined_scaled_window
      hm hθ.1 hθ.2 with
    ⟨i, hold_lo, hold_hi, href_lo, href_hi⟩
  refine ⟨i, ?_, ?_⟩
  · exact
      uniformDoubledEndpointLevelsIterate_mem_two_step_interval_of_scaled_index_between
        hm hold i
        (clampedFloorLevelIndex
          (uniformDoubledEndpointIndexIterate m q) θ)
        href_lo href_hi
  · exact
      BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
        hold i (clampedFloorLevelIndex m θ) hold_lo hold_hi

/--
Sequence-level q-step source-window package for B.1.  In any uniform equalized
endpoint-level sequence, the selected level at a repeated C.5 refinement stage
and the selected old level lie in the same old two-step bracket.
-/
theorem uniformEqualizedLevelSequence_iterated_clampedFloor_old_refined_mem_same_two_step_interval
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin m,
      levels (uniformDoubledEndpointIndexIterate m q)
          (clampedFloorLevelIndex
            (uniformDoubledEndpointIndexIterate m q) θ) ∈
          Set.Icc (levels m ⟨i.1, by omega⟩)
            (levels m ⟨i.1 + 2, by omega⟩) ∧
        levels m (clampedFloorLevelIndex m θ) ∈
          Set.Icc (levels m ⟨i.1, by omega⟩)
            (levels m ⟨i.1 + 2, by omega⟩) := by
  rcases
      uniformDoubledEndpointLevelsIterate_clampedFloor_old_refined_mem_same_two_step_interval
        hm (hlevels m) hθ with
    ⟨i, hrefined, hold_old⟩
  refine ⟨i, ?_, hold_old⟩
  have hseq :=
    uniformEqualizedLevelSequence_iterated_eq levels hlevels heq hm q
  rw [hseq]
  exact hrefined

/--
Q-step source-window package for an arbitrary selector.  If the old selected
index is in the old two-step window around `i`, and the q-times refined
selected index is in the corresponding scaled window, then the selected levels
lie in the same original two-step bracket.  This is the reusable B.1 hook for
turning the source's uniform quantile-convergence hypothesis into the
anchor-envelope argument.
-/
theorem uniformDoubledEndpointLevelsIterate_old_refined_mem_same_two_step_interval_of_scaled_index_window
    {m q : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (levelIndex : (n : ℕ) → Fin (n + 2))
    (i : Fin m)
    (hold_lo : i.1 ≤ (levelIndex m).1)
    (hold_hi : (levelIndex m).1 ≤ i.1 + 2)
    (href_lo :
      2 ^ q * i.1 ≤
        (levelIndex (uniformDoubledEndpointIndexIterate m q)).1)
    (href_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q)).1 ≤
        2 ^ q * (i.1 + 2)) :
    uniformDoubledEndpointLevelsIterate oldLevels q
        (levelIndex (uniformDoubledEndpointIndexIterate m q)) ∈
        Set.Icc (oldLevels ⟨i.1, by omega⟩)
          (oldLevels ⟨i.1 + 2, by omega⟩) ∧
      oldLevels (levelIndex m) ∈
        Set.Icc (oldLevels ⟨i.1, by omega⟩)
          (oldLevels ⟨i.1 + 2, by omega⟩) := by
  constructor
  · exact
      uniformDoubledEndpointLevelsIterate_mem_two_step_interval_of_scaled_index_between
        hm hold i
        (levelIndex (uniformDoubledEndpointIndexIterate m q))
        href_lo href_hi
  · exact
      BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
        hold i (levelIndex m) hold_lo hold_hi

/--
Sequence-level q-step source-window package for an arbitrary selector.  This
specializes the explicit repeated-C.5 window lemma to any uniform equalized
endpoint-level sequence.
-/
theorem uniformEqualizedLevelSequence_iterated_old_refined_mem_same_two_step_interval_of_scaled_index_window
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    (i : Fin m)
    (hold_lo : i.1 ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i.1 + 2)
    (href_lo :
      2 ^ q * i.1 ≤
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (href_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤
        2 ^ q * (i.1 + 2)) :
    levels (uniformDoubledEndpointIndexIterate m q)
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ) ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) ∧
      levels m (levelIndex m θ) ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) := by
  rcases
      uniformDoubledEndpointLevelsIterate_old_refined_mem_same_two_step_interval_of_scaled_index_window
        hm (hlevels m) (fun n : ℕ => levelIndex n θ) i
        hold_lo hold_hi href_lo href_hi with
    ⟨hrefined, hold_old⟩
  refine ⟨?_, hold_old⟩
  have hseq :=
    uniformEqualizedLevelSequence_iterated_eq levels hlevels heq hm q
  rw [hseq]
  exact hrefined

/--
Any endpoint whose index lies inside a fixed old block lies inside the
corresponding value block.  This is the fixed-width analogue of the two-step
index lemma used in the printed Appendix B proof.
-/
theorem BinaryEndpointLevelVector_level_mem_block_interval_of_index_between
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels) {i width : ℕ}
    (hi : i + width ≤ m + 1) (k : Fin (m + 2))
    (hlo : i ≤ k.1) (hhi : k.1 ≤ i + width) :
    levels k ∈
      Set.Icc (levels ⟨i, by omega⟩)
        (levels ⟨i + width, by omega⟩) := by
  constructor
  · exact
      BinaryEndpointLevelVector_mono
        (a := (⟨i, by omega⟩ : Fin (m + 2))) (b := k)
        hlevels hlo
  · exact
      BinaryEndpointLevelVector_mono
        (a := k) (b := (⟨i + width, by omega⟩ : Fin (m + 2)))
        hlevels hhi

/--
Fixed-width block form of the repeated C.5 inclusion.  If a refined index in
the q-times doubled chain lies in the scaled image of an old fixed-width block,
then its selected level lies in that old block.  This is the Appendix B bridge
needed when the source quantile argument gives a bounded block rather than the
exact two-step window.
-/
theorem uniformDoubledEndpointLevelsIterate_mem_block_interval_of_scaled_index_between
    {m q : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    {i width : ℕ} (hi : i + width ≤ m + 1)
    (hwidth : 2 ≤ width)
    (r : Fin ((uniformDoubledEndpointIndexIterate m q) + 2))
    (hlo : 2 ^ q * i ≤ r.1)
    (hhi : r.1 ≤ 2 ^ q * (i + width)) :
    uniformDoubledEndpointLevelsIterate oldLevels q r ∈
      Set.Icc (oldLevels ⟨i, by omega⟩)
        (oldLevels ⟨i + width, by omega⟩) := by
  induction q with
  | zero =>
      exact
        BinaryEndpointLevelVector_level_mem_block_interval_of_index_between
          hold hi r (by simpa using hlo) (by simpa using hhi)
  | succ q ih =>
      let scale : ℕ := 2 ^ q
      change
        uniformDoubledEndpointLevels
            (uniformDoubledEndpointLevelsIterate oldLevels q) r ∈
          Set.Icc (oldLevels ⟨i, by omega⟩)
            (oldLevels ⟨i + width, by omega⟩)
      have hupper :
          scale * (i + width) ≤
            uniformDoubledEndpointIndexIterate m q + 1 := by
        dsimp [scale]
        rw [uniformDoubledEndpointIndexIterate_add_one]
        exact Nat.mul_le_mul_left (2 ^ q) hi
      have hblock_nontrivial' : 2 ≤ scale * (i + width) := by
        have hscale_pos : 0 < scale := by dsimp [scale]; positivity
        have hwidth_le_scale_width : width ≤ scale * width :=
          Nat.le_mul_of_pos_left width hscale_pos
        have hscale_width_le :
            scale * width ≤ scale * (i + width) :=
          Nat.mul_le_mul_left scale (by omega)
        exact hwidth.trans (hwidth_le_scale_width.trans hscale_width_le)
      let upper : ℕ := scale * (i + width) - 2
      let jVal : ℕ := min (r.1 / 2) upper
      have hupper_plus : upper + 2 = scale * (i + width) := by
        dsimp [upper]
        omega
      have hupper_lt :
          upper < uniformDoubledEndpointIndexIterate m q := by
        have hle : upper + 2 ≤ uniformDoubledEndpointIndexIterate m q + 1 := by
          simpa [hupper_plus] using hupper
        omega
      have hleft_upper : scale * i ≤ upper := by
        dsimp [upper]
        have hmul :
            scale * (i + width) = scale * i + scale * width := by
          ring
        have htwo_le_width : 2 ≤ scale * width := by
          have hscale_pos : 0 < scale := by dsimp [scale]; positivity
          exact hwidth.trans (Nat.le_mul_of_pos_left width hscale_pos)
        omega
      have hleft_div : scale * i ≤ r.1 / 2 := by
        have hlo' : 2 * scale * i ≤ r.1 := by
          simpa [scale, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hlo
        exact (Nat.le_div_iff_mul_le Nat.zero_lt_two).2 (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hlo')
      have hj_bounds :
          scale * i ≤ jVal ∧ jVal + 2 ≤ scale * (i + width) ∧
            2 * jVal ≤ r.1 ∧ r.1 ≤ 2 * jVal + 4 := by
        by_cases hdiv_le : r.1 / 2 ≤ upper
        · refine ⟨?_, ?_, ?_, ?_⟩
          · dsimp [jVal]
            rw [min_eq_left hdiv_le]
            exact hleft_div
          · dsimp [jVal]
            rw [min_eq_left hdiv_le]
            omega
          · dsimp [jVal]
            rw [min_eq_left hdiv_le]
            have hmod := Nat.div_add_mod r.1 2
            have hmod_lt : r.1 % 2 < 2 := Nat.mod_lt r.1 (by norm_num)
            omega
          · dsimp [jVal]
            rw [min_eq_left hdiv_le]
            have hmod := Nat.div_add_mod r.1 2
            have hmod_lt : r.1 % 2 < 2 := Nat.mod_lt r.1 (by norm_num)
            omega
        · have hupper_lt_div : upper < r.1 / 2 := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · dsimp [jVal]
            rw [min_eq_right (by omega : upper ≤ r.1 / 2)]
            exact hleft_upper
          · dsimp [jVal]
            rw [min_eq_right (by omega : upper ≤ r.1 / 2)]
            exact le_of_eq hupper_plus
          · dsimp [jVal]
            rw [min_eq_right (by omega : upper ≤ r.1 / 2)]
            have hlt_mul :
                2 * upper ≤ r.1 := by
              have hsucc_le : upper + 1 ≤ r.1 / 2 :=
                Nat.succ_le_of_lt hupper_lt_div
              have hmul_le : 2 * (upper + 1) ≤ r.1 := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (Nat.le_div_iff_mul_le Nat.zero_lt_two).1 hsucc_le
              omega
            omega
          · dsimp [jVal]
            rw [min_eq_right (by omega : upper ≤ r.1 / 2)]
            have htarget :
                2 * scale * (i + width) = 2 * upper + 4 := by
              calc
                2 * scale * (i + width) =
                    2 * (scale * (i + width)) := by ring
                _ = 2 * (upper + 2) := by rw [← hupper_plus]
                _ = 2 * upper + 4 := by ring
            have hhi' : r.1 ≤ 2 * scale * (i + width) := by
              simpa [scale, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hhi
            exact hhi'.trans_eq htarget
      let j : Fin (uniformDoubledEndpointIndexIterate m q) :=
        ⟨jVal, by
          have hj_le_upper : jVal ≤ upper := by
            dsimp [jVal]
            exact Nat.min_le_right _ _
          exact lt_of_le_of_lt hj_le_upper hupper_lt⟩
      have hstep :
          uniformDoubledEndpointLevels
              (uniformDoubledEndpointLevelsIterate oldLevels q) r ∈
            Set.Icc
              (uniformDoubledEndpointLevelsIterate oldLevels q
                ⟨j.1, by omega⟩)
              (uniformDoubledEndpointLevelsIterate oldLevels q
                ⟨j.1 + 2, by omega⟩) :=
        uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_five
          (uniformDoubledEndpointIndexIterate_pos_of_pos hm q)
          (uniformDoubledEndpointLevelsIterate_isEndpointLevelVector hm hold q)
          j r hj_bounds.2.2.1 hj_bounds.2.2.2
      have hmem_lo :
          uniformDoubledEndpointLevelsIterate oldLevels q
              ⟨j.1, by omega⟩ ∈
            Set.Icc (oldLevels ⟨i, by omega⟩)
              (oldLevels ⟨i + width, by omega⟩) := by
        exact ih ⟨j.1, by omega⟩ hj_bounds.1
          (by
            have hj_hi : j.1 ≤ scale * (i + width) := by
              have hjVal_hi : jVal ≤ scale * (i + width) := by omega
              simpa [j] using hjVal_hi
            simpa [scale] using hj_hi)
      have hmem_hi :
          uniformDoubledEndpointLevelsIterate oldLevels q
              ⟨j.1 + 2, by omega⟩ ∈
            Set.Icc (oldLevels ⟨i, by omega⟩)
              (oldLevels ⟨i + width, by omega⟩) := by
        exact ih ⟨j.1 + 2, by omega⟩
          (by
            have hj_lo : scale * i ≤ j.1 := by
              simpa [j] using hj_bounds.1
            have : scale * i ≤ j.1 + 2 := by omega
            simpa [scale] using this)
          (by
            have hj_hi : j.1 + 2 ≤ scale * (i + width) := by
              simpa [j] using hj_bounds.2.1
            simpa [scale] using hj_hi)
      constructor
      · exact hmem_lo.1.trans hstep.1
      · exact hstep.2.trans hmem_hi.2

/--
Corollary C.4 preparatory fact: equispaced interval quantile maps converge
uniformly to the identity on `[0,1]`.
-/
theorem corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      (fun θ : ℝ => θ) atTop (Set.Icc (0 : ℝ) 1) := by
  simpa [equispacedIntervalQuantile] using
    AppliedModelingLib.Math.tendstoUniformlyOn_nat_floor_mul_div_Icc_zero_one

/--
The equispaced interval quantile map stays in `[0,1]` on the source interval.
-/
theorem equispacedIntervalQuantile_mem_Icc
    (M : ℕ) (hM : 0 < M) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    equispacedIntervalQuantile M θ ∈ Set.Icc (0 : ℝ) 1 := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  constructor
  · change 0 ≤ ((Nat.floor ((M : ℝ) * θ) : ℝ) / (M : ℝ))
    exact div_nonneg (Nat.cast_nonneg _) hMpos.le
  · change ((Nat.floor ((M : ℝ) * θ) : ℝ) / (M : ℝ)) ≤ 1
    rw [div_le_iff₀ hMpos]
    have hfloor_le :
        ((Nat.floor ((M : ℝ) * θ) : ℕ) : ℝ) ≤ (M : ℝ) * θ := by
      exact Nat.floor_le (mul_nonneg hMpos.le hθ.1)
    have hmul_le : (M : ℝ) * θ ≤ (M : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hθ.2 hMpos.le
    simpa [one_mul] using hfloor_le.trans hmul_le

/--
The equispaced interval quantile map tracks the identity coordinate at the
explicit `1/M` rate used by the source-facing B.1 selector bridge.
-/
theorem equispacedIntervalQuantile_dist_identity_le_inv
    (M : ℕ) (hM : 0 < M) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    dist θ (equispacedIntervalQuantile M θ) ≤ 1 / (M : ℝ) := by
  have hclose :=
    AppliedModelingLib.Math.nat_floor_mul_div_sub_abs_lt_inv
      (Q := M) hM (x := θ) hθ.1
  exact le_of_lt (by
    simpa [equispacedIntervalQuantile, Real.dist_eq, abs_sub_comm] using hclose)

/--
Two adjacent old intervals have total level width bounded by twice the maximum
adjacent width.  This is the finite mesh estimate used in the source proof of
Theorem B.1 after the C.5 doubled-chain inclusion.
-/
theorem BinaryEndpointLevelVector_two_step_width_le_two_maxWidth
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels) (i : Fin m) :
    levels ⟨i.1 + 2, by omega⟩ - levels ⟨i.1, by omega⟩ ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) levels := by
  let j0 : Fin (m + 1) := ⟨i.1, by omega⟩
  let j1 : Fin (m + 1) := ⟨i.1 + 1, by omega⟩
  have h0 :
      levels ⟨i.1 + 1, by omega⟩ - levels ⟨i.1, by omega⟩ ≤
        binaryEndpointAdjacentMaxWidth (m := m) levels := by
    simpa [binaryEndpointAdjacentMaxWidth, j0, adjacentLowIndex,
      adjacentHighIndex] using
      AppliedModelingLib.le_finiteMax
        (fun j : Fin (m + 1) =>
          levels (adjacentHighIndex j) - levels (adjacentLowIndex j)) j0
  have h1 :
      levels ⟨i.1 + 2, by omega⟩ - levels ⟨i.1 + 1, by omega⟩ ≤
        binaryEndpointAdjacentMaxWidth (m := m) levels := by
    simpa [binaryEndpointAdjacentMaxWidth, j1, adjacentLowIndex,
      adjacentHighIndex] using
      AppliedModelingLib.le_finiteMax
        (fun j : Fin (m + 1) =>
          levels (adjacentHighIndex j) - levels (adjacentLowIndex j)) j1
  calc
    levels ⟨i.1 + 2, by omega⟩ - levels ⟨i.1, by omega⟩ =
        (levels ⟨i.1 + 1, by omega⟩ - levels ⟨i.1, by omega⟩) +
          (levels ⟨i.1 + 2, by omega⟩ - levels ⟨i.1 + 1, by omega⟩) := by
          ring
    _ ≤ binaryEndpointAdjacentMaxWidth (m := m) levels +
        binaryEndpointAdjacentMaxWidth (m := m) levels := by
          exact add_le_add h0 h1
    _ = 2 * binaryEndpointAdjacentMaxWidth (m := m) levels := by ring

/--
Any fixed-width block in an endpoint-level vector has width bounded by that
many adjacent mesh widths.  This generalizes the two-step estimate used in the
printed B.1 proof and is useful when a source selector lands in a slightly
wider but still constant-size old bracket.
-/
theorem BinaryEndpointLevelVector_block_width_le_nat_mul_maxWidth
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels) :
    ∀ {i width : ℕ}, (hi : i + width ≤ m + 1) →
      levels ⟨i + width, by omega⟩ - levels ⟨i, by omega⟩ ≤
        (width : ℝ) * binaryEndpointAdjacentMaxWidth (m := m) levels := by
  intro i width
  induction width generalizing i with
  | zero =>
      intro _hi
      simp
  | succ width ih =>
      intro hi
      have hi_prev : i + width ≤ m + 1 := by omega
      have hprev := ih (i := i) hi_prev
      let j : Fin (m + 1) := ⟨i + width, by omega⟩
      have hstep :
          levels ⟨i + (width + 1), by omega⟩ -
              levels ⟨i + width, by omega⟩ ≤
            binaryEndpointAdjacentMaxWidth (m := m) levels := by
        simpa [binaryEndpointAdjacentMaxWidth, j, adjacentLowIndex,
          adjacentHighIndex, Nat.add_assoc] using
          AppliedModelingLib.le_finiteMax
            (fun j : Fin (m + 1) =>
              levels (adjacentHighIndex j) - levels (adjacentLowIndex j)) j
      calc
        levels ⟨i + (width + 1), by omega⟩ - levels ⟨i, by omega⟩ =
            (levels ⟨i + width, by omega⟩ - levels ⟨i, by omega⟩) +
              (levels ⟨i + (width + 1), by omega⟩ -
                levels ⟨i + width, by omega⟩) := by ring
        _ ≤ (width : ℝ) *
              binaryEndpointAdjacentMaxWidth (m := m) levels +
            binaryEndpointAdjacentMaxWidth (m := m) levels := by
              exact add_le_add hprev hstep
        _ = ((width + 1 : ℕ) : ℝ) *
              binaryEndpointAdjacentMaxWidth (m := m) levels := by
              norm_num [Nat.cast_add]
              ring

/--
If two real values both lie in the same two-step level bracket, their distance
is at most twice the adjacent mesh.
-/
theorem BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels) (i : Fin m)
    {x y : ℝ}
    (hx :
      x ∈ Set.Icc (levels ⟨i.1, by omega⟩)
        (levels ⟨i.1 + 2, by omega⟩))
    (hy :
      y ∈ Set.Icc (levels ⟨i.1, by omega⟩)
        (levels ⟨i.1 + 2, by omega⟩)) :
    dist x y ≤ 2 * binaryEndpointAdjacentMaxWidth (m := m) levels := by
  have hdist_le :
      dist x y ≤ levels ⟨i.1 + 2, by omega⟩ -
        levels ⟨i.1, by omega⟩ := by
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  exact hdist_le.trans
    (BinaryEndpointLevelVector_two_step_width_le_two_maxWidth hlevels i)

/--
If two real values both lie in the same fixed-width level bracket, their
distance is bounded by the bracket width times the adjacent mesh.
-/
theorem BinaryEndpointLevelVector_dist_le_nat_mul_maxWidth_of_mem_block_interval
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels) {i width : ℕ}
    (hi : i + width ≤ m + 1) {x y : ℝ}
    (hx :
      x ∈ Set.Icc (levels ⟨i, by omega⟩)
        (levels ⟨i + width, by omega⟩))
    (hy :
      y ∈ Set.Icc (levels ⟨i, by omega⟩)
        (levels ⟨i + width, by omega⟩)) :
    dist x y ≤
      (width : ℝ) * binaryEndpointAdjacentMaxWidth (m := m) levels := by
  have hdist_le :
      dist x y ≤ levels ⟨i + width, by omega⟩ -
        levels ⟨i, by omega⟩ := by
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  exact hdist_le.trans
    (BinaryEndpointLevelVector_block_width_le_nat_mul_maxWidth hlevels hi)

/--
If two real values lie in the same endpoint block, their distance is bounded
by the actual metric width of that block.  This is the non-equispaced version
of the max-mesh estimate: the number of old cells inside the block is
irrelevant once the source proof controls the real endpoint span.
-/
theorem BinaryEndpointLevelVector_dist_le_block_width_of_mem_block_interval
    {m : ℕ} {levels : Fin (m + 2) → ℝ} {i width : ℕ}
    (_hi : i + width ≤ m + 1) {x y : ℝ}
    (hx :
      x ∈ Set.Icc (levels ⟨i, by omega⟩)
        (levels ⟨i + width, by omega⟩))
    (hy :
      y ∈ Set.Icc (levels ⟨i, by omega⟩)
        (levels ⟨i + width, by omega⟩)) :
    dist x y ≤ levels ⟨i + width, by omega⟩ - levels ⟨i, by omega⟩ := by
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/--
Q-step B.1 mesh bound for an arbitrary selector satisfying the source scaled
index window.  This is the distance version of the generic selector-window
lemma above.
-/
theorem uniformEqualizedLevelSequence_iterated_beta_dist_le_two_maxWidth_of_scaled_index_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    (i : Fin m)
    (hold_lo : i.1 ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i.1 + 2)
    (href_lo :
      2 ^ q * i.1 ≤
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (href_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤
        2 ^ q * (i.1 + 2)) :
    dist
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ)
        (betaSeq m θ) ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  rcases
      uniformEqualizedLevelSequence_iterated_old_refined_mem_same_two_step_interval_of_scaled_index_window
        levels levelIndex hlevels heq hm i
        hold_lo hold_hi href_lo href_hi with
    ⟨hrefined, hold_old⟩
  rw [hrepr (uniformDoubledEndpointIndexIterate m q) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels m) i hrefined hold_old

/--
Sequence-level q-step source-window package for an arbitrary selector and a
fixed-width old block.  This is the version designed for source quantile
arguments that give a bounded old block rather than the exact two-step window.
-/
theorem uniformEqualizedLevelSequence_iterated_old_refined_mem_same_block_interval_of_scaled_index_window
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    {i width : ℕ} (hi : i + width ≤ m + 1) (hwidth : 2 ≤ width)
    (hold_lo : i ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i + width)
    (href_lo :
      2 ^ q * i ≤
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (href_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤
        2 ^ q * (i + width)) :
    levels (uniformDoubledEndpointIndexIterate m q)
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ) ∈
        Set.Icc (levels m ⟨i, by omega⟩)
          (levels m ⟨i + width, by omega⟩) ∧
      levels m (levelIndex m θ) ∈
        Set.Icc (levels m ⟨i, by omega⟩)
          (levels m ⟨i + width, by omega⟩) := by
  refine ⟨?_, ?_⟩
  · have hseq :=
      uniformEqualizedLevelSequence_iterated_eq levels hlevels heq hm q
    rw [hseq]
    exact
      uniformDoubledEndpointLevelsIterate_mem_block_interval_of_scaled_index_between
        hm (hlevels m) hi hwidth
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ)
        href_lo href_hi
  · exact
      BinaryEndpointLevelVector_level_mem_block_interval_of_index_between
        (hlevels m) hi (levelIndex m θ) hold_lo hold_hi

/--
Q-step B.1 mesh bound for an arbitrary selector satisfying a source scaled
fixed-width block window.
-/
theorem uniformEqualizedLevelSequence_iterated_beta_dist_le_nat_mul_maxWidth_of_scaled_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    {i width : ℕ} (hi : i + width ≤ m + 1) (hwidth : 2 ≤ width)
    (hold_lo : i ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i + width)
    (href_lo :
      2 ^ q * i ≤
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (href_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤
        2 ^ q * (i + width)) :
    dist
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ)
        (betaSeq m θ) ≤
      (width : ℝ) * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  rcases
      uniformEqualizedLevelSequence_iterated_old_refined_mem_same_block_interval_of_scaled_index_window
        levels levelIndex hlevels heq hm hi hwidth
        hold_lo hold_hi href_lo href_hi with
    ⟨hrefined, hold_old⟩
  rw [hrepr (uniformDoubledEndpointIndexIterate m q) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_nat_mul_maxWidth_of_mem_block_interval
      (hlevels m) hi hrefined hold_old

/--
Q-step B.1 mesh bound for an arbitrary selector satisfying a source scaled
block window, measured by the actual old endpoint span of that block.  This is
the metric non-equispaced form: it avoids converting the block to
`width * maxMesh`.
-/
theorem uniformEqualizedLevelSequence_iterated_beta_dist_le_block_width_of_scaled_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    {i width : ℕ} (hi : i + width ≤ m + 1) (hwidth : 2 ≤ width)
    (hold_lo : i ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i + width)
    (href_lo :
      2 ^ q * i ≤
        (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (href_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤
        2 ^ q * (i + width)) :
    dist
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ)
        (betaSeq m θ) ≤
      levels m ⟨i + width, by omega⟩ - levels m ⟨i, by omega⟩ := by
  rcases
      uniformEqualizedLevelSequence_iterated_old_refined_mem_same_block_interval_of_scaled_index_window
        levels levelIndex hlevels heq hm hi hwidth
        hold_lo hold_hi href_lo href_hi with
    ⟨hrefined, hold_old⟩
  rw [hrepr (uniformDoubledEndpointIndexIterate m q) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_block_width_of_mem_block_interval
      hi hrefined hold_old

/--
One-step B.1 mesh bound from source index windows.  If `β_m(θ)` and
`β_{2m+1}(θ)` are represented by selected endpoint levels whose indices fall
in the source old/refined windows around `i`, then the two beta values are
within twice the old adjacent mesh.
-/
theorem uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_index_windows
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m)
    (hold_lo : i.1 ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ (levelIndex (2 * m + 1) θ).1)
    (href_hi : (levelIndex (2 * m + 1) θ).1 ≤ 2 * i.1 + 2) :
    dist (betaSeq (2 * m + 1) θ) (betaSeq m θ) ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  have hmem :=
    uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval
      levels hlevels heq hm i (levelIndex m θ)
      (levelIndex (2 * m + 1) θ) hold_lo hold_hi href_lo href_hi
  rw [hrepr (2 * m + 1) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels m) i hmem.1 hmem.2

/--
One-step B.1 mesh bound from the four-point source floor window.  This is the
version designed to consume `nat_floor_two_mul_sub_one_mul_window` directly.
-/
theorem uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_index_windows_four
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m)
    (hold_lo : i.1 ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ (levelIndex (2 * m + 1) θ).1)
    (href_hi : (levelIndex (2 * m + 1) θ).1 ≤ 2 * i.1 + 3) :
    dist (betaSeq (2 * m + 1) θ) (betaSeq m θ) ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  have hmem :=
    uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval_four
      levels hlevels heq hm i (levelIndex m θ)
      (levelIndex (2 * m + 1) θ) hold_lo hold_hi href_lo href_hi
  rw [hrepr (2 * m + 1) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels m) i hmem.1 hmem.2

/--
One-step B.1 mesh bound from the five-point source floor window.  This variant
also covers the clamped right endpoint selected by the source level convention.
-/
theorem uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_index_windows_five
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m)
    (hold_lo : i.1 ≤ (levelIndex m θ).1)
    (hold_hi : (levelIndex m θ).1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ (levelIndex (2 * m + 1) θ).1)
    (href_hi : (levelIndex (2 * m + 1) θ).1 ≤ 2 * i.1 + 4) :
    dist (betaSeq (2 * m + 1) θ) (betaSeq m θ) ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  have hmem :=
    uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval_five
      levels hlevels heq hm i (levelIndex m θ)
      (levelIndex (2 * m + 1) θ) hold_lo hold_hi href_lo href_hi
  rw [hrepr (2 * m + 1) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels m) i hmem.1 hmem.2

/--
One-step B.1 mesh bound for the source clamped floor selector.  The dyadic
floor-window arithmetic and five-point C.5 bridge discharge the selector
window certificate.
-/
theorem uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_clampedFloorLevelIndex
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq m θ = levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    dist (betaSeq (2 * m + 1) θ) (betaSeq m θ) ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  rcases clampedFloorLevelIndex_old_refined_five_window hm hθ.1 hθ.2 with
    ⟨i, hold_lo, hold_hi, href_lo, href_hi⟩
  exact
    uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_index_windows_five
      betaSeq levels clampedFloorLevelIndex hrepr hlevels heq hm θ i
      hold_lo hold_hi href_lo href_hi

/--
Iterated-step B.1 mesh bound from source index windows.  This is the same
one-step distance estimate, stated at an arbitrary repeated C.5 stage.
-/
theorem uniformEqualizedLevelSequence_iterated_step_beta_dist_le_two_maxWidth_of_index_windows
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) (θ : ℝ)
    (i : Fin (uniformDoubledEndpointIndexIterate m q))
    (hold_lo : i.1 ≤ (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (hold_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤ i.1 + 2)
    (href_lo :
      2 * i.1 ≤
        (levelIndex
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ).1)
    (href_hi :
      (levelIndex
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ).1 ≤
        2 * i.1 + 2) :
    dist
        (betaSeq
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ)
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ) ≤
      2 * binaryEndpointAdjacentMaxWidth
        (m := uniformDoubledEndpointIndexIterate m q)
        (levels (uniformDoubledEndpointIndexIterate m q)) := by
  simpa [uniformDoubledEndpointIndex] using
    uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_index_windows
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm q) θ i
      hold_lo hold_hi href_lo href_hi

/--
Iterated-step B.1 mesh bound from the five-point source index window.  This is
the boundary-safe version for repeated C.5 stages.
-/
theorem uniformEqualizedLevelSequence_iterated_step_beta_dist_le_two_maxWidth_of_index_windows_five
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) (θ : ℝ)
    (i : Fin (uniformDoubledEndpointIndexIterate m q))
    (hold_lo : i.1 ≤ (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1)
    (hold_hi :
      (levelIndex (uniformDoubledEndpointIndexIterate m q) θ).1 ≤ i.1 + 2)
    (href_lo :
      2 * i.1 ≤
        (levelIndex
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ).1)
    (href_hi :
      (levelIndex
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ).1 ≤
        2 * i.1 + 4) :
    dist
        (betaSeq
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ)
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ) ≤
      2 * binaryEndpointAdjacentMaxWidth
        (m := uniformDoubledEndpointIndexIterate m q)
        (levels (uniformDoubledEndpointIndexIterate m q)) := by
  simpa [uniformDoubledEndpointIndex] using
    uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_index_windows_five
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm q) θ i
      hold_lo hold_hi href_lo href_hi

/--
Iterated-step B.1 mesh bound for the source clamped floor selector.
-/
theorem uniformEqualizedLevelSequence_iterated_step_beta_dist_le_two_maxWidth_of_clampedFloorLevelIndex
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq m θ = levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    dist
        (betaSeq
          (uniformDoubledEndpointIndex
            (uniformDoubledEndpointIndexIterate m q)) θ)
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ) ≤
      2 * binaryEndpointAdjacentMaxWidth
        (m := uniformDoubledEndpointIndexIterate m q)
        (levels (uniformDoubledEndpointIndexIterate m q)) := by
  simpa [uniformDoubledEndpointIndex] using
    uniformEqualizedLevelSequence_doubled_beta_dist_le_two_maxWidth_of_clampedFloorLevelIndex
      betaSeq levels hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm q) hθ

/--
Q-step B.1 mesh bound for the source clamped floor selector along an explicit
repeated C.5 refinement chain.  This is the anchor-envelope estimate once the
tail index is represented as `uniformDoubledEndpointIndexIterate m q`.
-/
theorem uniformEqualizedLevelSequence_iterated_clampedFloor_beta_dist_le_two_maxWidth
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq m θ = levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    dist
        (betaSeq (uniformDoubledEndpointIndexIterate m q) θ)
        (betaSeq m θ) ≤
      2 * binaryEndpointAdjacentMaxWidth (m := m) (levels m) := by
  rcases
      uniformEqualizedLevelSequence_iterated_clampedFloor_old_refined_mem_same_two_step_interval
        levels hlevels heq hm hθ with
    ⟨i, hrefined, hold_old⟩
  rw [hrepr (uniformDoubledEndpointIndexIterate m q) θ, hrepr m θ]
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels m) i hrefined hold_old

/--
Cauchy-completeness bridge for explicit repeated C.5 subsequences.  Once the
adjacent mesh along the repeated-refinement anchors tends to zero, the
clamped-floor beta subsequence has a uniform limit on `[0,1]`.
-/
theorem uniformDoubledEndpointIndexIterate_clampedFloor_subsequence_exists_uniform_limit
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq m θ = levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth
            (m := uniformDoubledEndpointIndexIterate m M)
            (levels (uniformDoubledEndpointIndexIterate m M)))
        atTop (nhds 0)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let mesh2 : ℕ → ℝ := fun M : ℕ =>
    2 * binaryEndpointAdjacentMaxWidth
      (m := uniformDoubledEndpointIndexIterate m M)
      (levels (uniformDoubledEndpointIndexIterate m M))
  have hmesh2 : Tendsto mesh2 atTop (nhds 0) := by
    dsimp [mesh2]
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hmesh
  have hmesh2_nonneg : ∀ M : ℕ, 0 ≤ mesh2 M := by
    intro M
    dsimp [mesh2]
    exact mul_nonneg (by norm_num)
      (binaryEndpointAdjacentMaxWidth_nonneg
        (hlevels (uniformDoubledEndpointIndexIterate m M)))
  refine
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
      (Set.Icc (0 : ℝ) 1) mesh2 hmesh2 hmesh2_nonneg ?_
  intro M
  refine ⟨M, ?_⟩
  intro N hN θ hθ
  have hdist :=
    uniformEqualizedLevelSequence_iterated_clampedFloor_beta_dist_le_two_maxWidth
      betaSeq levels hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm M)
      (m := uniformDoubledEndpointIndexIterate m M)
      (q := N - M) hθ
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  simpa [mesh2, hcomp] using hdist

/--
Cauchy-completeness bridge for arbitrary source selectors satisfying the
scaled index-window invariant used in the proof of Theorem B.1.  This is the
selector-general version of the clamped-floor subsequence bridge above.
-/
theorem uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_scaled_index_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth
            (m := uniformDoubledEndpointIndexIterate m M)
            (levels (uniformDoubledEndpointIndexIterate m M)))
        atTop (nhds 0))
    (hwindow :
      ∀ M N : ℕ, M ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (uniformDoubledEndpointIndexIterate m M),
            i.1 ≤
                (levelIndex
                  (uniformDoubledEndpointIndexIterate m M) θ).1 ∧
              (levelIndex
                  (uniformDoubledEndpointIndexIterate m M) θ).1 ≤
                i.1 + 2 ∧
              2 ^ (N - M) * i.1 ≤
                (levelIndex
                  (uniformDoubledEndpointIndexIterate m N) θ).1 ∧
              (levelIndex
                  (uniformDoubledEndpointIndexIterate m N) θ).1 ≤
                2 ^ (N - M) * (i.1 + 2)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let mesh2 : ℕ → ℝ := fun M : ℕ =>
    2 * binaryEndpointAdjacentMaxWidth
      (m := uniformDoubledEndpointIndexIterate m M)
      (levels (uniformDoubledEndpointIndexIterate m M))
  have hmesh2 : Tendsto mesh2 atTop (nhds 0) := by
    dsimp [mesh2]
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hmesh
  have hmesh2_nonneg : ∀ M : ℕ, 0 ≤ mesh2 M := by
    intro M
    dsimp [mesh2]
    exact mul_nonneg (by norm_num)
      (binaryEndpointAdjacentMaxWidth_nonneg
        (hlevels (uniformDoubledEndpointIndexIterate m M)))
  refine
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
      (Set.Icc (0 : ℝ) 1) mesh2 hmesh2 hmesh2_nonneg ?_
  intro M
  refine ⟨M, ?_⟩
  intro N hN θ hθ
  rcases hwindow M N hN θ hθ with
    ⟨i, hold_lo, hold_hi, href_lo, href_hi⟩
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have href_lo' :
      2 ^ (N - M) * i.1 ≤
        (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 := by
    rw [hcomp]
    exact href_lo
  have href_hi' :
      (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 ≤
        2 ^ (N - M) * (i.1 + 2) := by
    rw [hcomp]
    exact href_hi
  have hdist :=
    uniformEqualizedLevelSequence_iterated_beta_dist_le_two_maxWidth_of_scaled_index_window
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm M)
      (m := uniformDoubledEndpointIndexIterate m M)
      (q := N - M) (θ := θ) i
      hold_lo hold_hi href_lo' href_hi'
  simpa [mesh2, hcomp] using hdist

/--
Eventual-anchor version of the arbitrary-selector B.1 bridge.  The source
proof derives the scaled index-window only for sufficiently large anchor
indices, which is still enough for uniform subsequential convergence.
-/
theorem uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_index_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth
            (m := uniformDoubledEndpointIndexIterate m M)
            (levels (uniformDoubledEndpointIndexIterate m M)))
        atTop (nhds 0))
    (hwindow :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : Fin (uniformDoubledEndpointIndexIterate m M),
              i.1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ≤
                  i.1 + 2 ∧
                2 ^ (N - M) * i.1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ≤
                  2 ^ (N - M) * (i.1 + 2)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let mesh2 : ℕ → ℝ := fun M : ℕ =>
    2 * binaryEndpointAdjacentMaxWidth
      (m := uniformDoubledEndpointIndexIterate m M)
      (levels (uniformDoubledEndpointIndexIterate m M))
  have hmesh2 : Tendsto mesh2 atTop (nhds 0) := by
    dsimp [mesh2]
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hmesh
  have hmesh2_nonneg : ∀ M : ℕ, 0 ≤ mesh2 M := by
    intro M
    dsimp [mesh2]
    exact mul_nonneg (by norm_num)
      (binaryEndpointAdjacentMaxWidth_nonneg
        (hlevels (uniformDoubledEndpointIndexIterate m M)))
  refine
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
      (Set.Icc (0 : ℝ) 1) mesh2 hmesh2 hmesh2_nonneg ?_
  filter_upwards [hwindow] with M hMwindow
  refine ⟨M, ?_⟩
  intro N hN θ hθ
  rcases hMwindow N hN θ hθ with
    ⟨i, hold_lo, hold_hi, href_lo, href_hi⟩
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have href_lo' :
      2 ^ (N - M) * i.1 ≤
        (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 := by
    rw [hcomp]
    exact href_lo
  have href_hi' :
      (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 ≤
        2 ^ (N - M) * (i.1 + 2) := by
    rw [hcomp]
    exact href_hi
  have hdist :=
    uniformEqualizedLevelSequence_iterated_beta_dist_le_two_maxWidth_of_scaled_index_window
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm M)
      (m := uniformDoubledEndpointIndexIterate m M)
      (q := N - M) (θ := θ) i
      hold_lo hold_hi href_lo' href_hi'
  simpa [mesh2, hcomp] using hdist

/--
Eventual-anchor Cauchy bridge for source selectors satisfying a scaled
fixed-width old-block window.  This is a more tolerant version of the scaled
two-step selector bridge above and is useful for feeding approximate quantile
envelopes into Theorem B.1.
-/
theorem uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (width : ℕ) (hwidth : 2 ≤ width)
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth
            (m := uniformDoubledEndpointIndexIterate m M)
            (levels (uniformDoubledEndpointIndexIterate m M)))
        atTop (nhds 0))
    (hwindow :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + width ≤ uniformDoubledEndpointIndexIterate m M + 1,
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ≤
                  i + width ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ≤
                  2 ^ (N - M) * (i + width)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let meshWidth : ℕ → ℝ := fun M : ℕ =>
    (width : ℝ) * binaryEndpointAdjacentMaxWidth
      (m := uniformDoubledEndpointIndexIterate m M)
      (levels (uniformDoubledEndpointIndexIterate m M))
  have hmeshWidth : Tendsto meshWidth atTop (nhds 0) := by
    dsimp [meshWidth]
    simpa using (tendsto_const_nhds (x := (width : ℝ))).mul hmesh
  have hmeshWidth_nonneg : ∀ M : ℕ, 0 ≤ meshWidth M := by
    intro M
    dsimp [meshWidth]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le width)
      (binaryEndpointAdjacentMaxWidth_nonneg
        (hlevels (uniformDoubledEndpointIndexIterate m M)))
  refine
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
      (Set.Icc (0 : ℝ) 1) meshWidth hmeshWidth hmeshWidth_nonneg ?_
  filter_upwards [hwindow] with M hMwindow
  refine ⟨M, ?_⟩
  intro N hN θ hθ
  rcases hMwindow N hN θ hθ with
    ⟨i, hi, hold_lo, hold_hi, href_lo, href_hi⟩
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have href_lo' :
      2 ^ (N - M) * i ≤
        (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 := by
    rw [hcomp]
    exact href_lo
  have href_hi' :
      (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 ≤
        2 ^ (N - M) * (i + width) := by
    rw [hcomp]
    exact href_hi
  have hdist :=
    uniformEqualizedLevelSequence_iterated_beta_dist_le_nat_mul_maxWidth_of_scaled_block_window
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm M)
      (m := uniformDoubledEndpointIndexIterate m M)
      (q := N - M) (θ := θ) hi hwidth
      hold_lo hold_hi href_lo' href_hi'
  simpa [meshWidth, hcomp] using hdist

/--
Eventual-anchor Cauchy bridge for source selectors satisfying a variable-width
old-block window.  This is the non-equispaced version of the fixed-width
bridge above: the selector may drift across `widthSeq M` old cells at anchor
depth `M`, provided that drift times the old endpoint mesh still tends to zero.
-/
theorem uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_block_window_variable_width
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (widthSeq : ℕ → ℕ)
    (hmeshWidth :
      Tendsto
        (fun M : ℕ =>
          (widthSeq M : ℝ) *
            binaryEndpointAdjacentMaxWidth
              (m := uniformDoubledEndpointIndexIterate m M)
              (levels (uniformDoubledEndpointIndexIterate m M)))
        atTop (nhds 0))
    (hwidth : ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq M)
    (hwindow :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + widthSeq M ≤ uniformDoubledEndpointIndexIterate m M + 1,
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ≤
                  i + widthSeq M ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ≤
                  2 ^ (N - M) * (i + widthSeq M)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let meshWidth : ℕ → ℝ := fun M : ℕ =>
    (widthSeq M : ℝ) * binaryEndpointAdjacentMaxWidth
      (m := uniformDoubledEndpointIndexIterate m M)
      (levels (uniformDoubledEndpointIndexIterate m M))
  have hmeshWidth' : Tendsto meshWidth atTop (nhds 0) := by
    simpa [meshWidth] using hmeshWidth
  have hmeshWidth_nonneg : ∀ M : ℕ, 0 ≤ meshWidth M := by
    intro M
    dsimp [meshWidth]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (widthSeq M))
      (binaryEndpointAdjacentMaxWidth_nonneg
        (hlevels (uniformDoubledEndpointIndexIterate m M)))
  refine
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
      (Set.Icc (0 : ℝ) 1) meshWidth hmeshWidth' hmeshWidth_nonneg ?_
  filter_upwards [hwindow, hwidth] with M hMwindow hMwidth
  refine ⟨M, ?_⟩
  intro N hN θ hθ
  rcases hMwindow N hN θ hθ with
    ⟨i, hi, hold_lo, hold_hi, href_lo, href_hi⟩
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have href_lo' :
      2 ^ (N - M) * i ≤
        (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 := by
    rw [hcomp]
    exact href_lo
  have href_hi' :
      (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 ≤
        2 ^ (N - M) * (i + widthSeq M) := by
    rw [hcomp]
    exact href_hi
  have hdist :=
    uniformEqualizedLevelSequence_iterated_beta_dist_le_nat_mul_maxWidth_of_scaled_block_window
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm M)
      (m := uniformDoubledEndpointIndexIterate m M)
      (q := N - M) (θ := θ) hi hMwidth
      hold_lo hold_hi href_lo' href_hi'
  simpa [meshWidth, hcomp] using hdist

/--
Eventual-anchor Cauchy bridge for non-equispaced source selectors satisfying
a metric old-block window.  The source proof may choose blocks with many tiny
old cells; Lean only needs the actual endpoint span of the chosen block to be
bounded by `blockWidth M`, with `blockWidth M -> 0`.
-/
theorem uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_metric_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq m θ = levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (widthSeq : ℕ → ℕ) (blockWidth : ℕ → ℝ)
    (hblockWidth : Tendsto blockWidth atTop (nhds 0))
    (hblockWidth_nonneg : ∀ M : ℕ, 0 ≤ blockWidth M)
    (hwidth : ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq M)
    (hwindow :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + widthSeq M ≤ uniformDoubledEndpointIndexIterate m M + 1,
              levels (uniformDoubledEndpointIndexIterate m M)
                  ⟨i + widthSeq M, by omega⟩ -
                levels (uniformDoubledEndpointIndexIterate m M)
                  ⟨i, by omega⟩ ≤ blockWidth M ∧
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m M) θ).1 ≤
                  i + widthSeq M ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m N) θ).1 ≤
                  2 ^ (N - M) * (i + widthSeq M)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  refine
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
      (Set.Icc (0 : ℝ) 1) blockWidth hblockWidth hblockWidth_nonneg ?_
  filter_upwards [hwindow, hwidth] with M hMwindow hMwidth
  refine ⟨M, ?_⟩
  intro N hN θ hθ
  rcases hMwindow N hN θ hθ with
    ⟨i, hi, hblock, hold_lo, hold_hi, href_lo, href_hi⟩
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have href_lo' :
      2 ^ (N - M) * i ≤
        (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 := by
    rw [hcomp]
    exact href_lo
  have href_hi' :
      (levelIndex
          (uniformDoubledEndpointIndexIterate
            (uniformDoubledEndpointIndexIterate m M) (N - M)) θ).1 ≤
        2 ^ (N - M) * (i + widthSeq M) := by
    rw [hcomp]
    exact href_hi
  have hdist :=
    uniformEqualizedLevelSequence_iterated_beta_dist_le_block_width_of_scaled_block_window
      betaSeq levels levelIndex hrepr hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm M)
      (m := uniformDoubledEndpointIndexIterate m M)
      (q := N - M) (θ := θ) hi hMwidth
      hold_lo hold_hi href_lo' href_hi'
  simpa [hcomp] using hdist.trans hblock

/--
Common-coordinate selector bridge for Theorem B.1.  If the old and refined
selectors are both clamped floors of the same source coordinate along each
dyadic refinement tail, then the scaled selector-window invariant follows.
-/
theorem uniformDoubledEndpointIndexIterate_eventually_scaled_index_window_of_common_floor_coordinate
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    {m0 : ℕ} (hm0 : 0 < m0)
    (hcommon :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
              levelIndex (uniformDoubledEndpointIndexIterate m0 M) θ =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 M) x ∧
              levelIndex (uniformDoubledEndpointIndexIterate m0 N) θ =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 N) x) :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : Fin (uniformDoubledEndpointIndexIterate m0 M),
              i.1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 M) θ).1 ≤
                  i.1 + 2 ∧
                2 ^ (N - M) * i.1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 N) θ).1 ≤
                  2 ^ (N - M) * (i.1 + 2) := by
  filter_upwards [hcommon] with M hMcommon
  intro N hN θ hθ
  rcases hMcommon N hN θ hθ with ⟨x, hx, hold_eq, href_eq⟩
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m0 M) (N - M) =
        uniformDoubledEndpointIndexIterate m0 N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  rcases
      clampedFloorLevelIndex_iterated_old_refined_scaled_window
        (uniformDoubledEndpointIndexIterate_pos_of_pos hm0 M)
        (q := N - M) hx.1 hx.2 with
    ⟨i, hold_lo, hold_hi, href_lo, href_hi⟩
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · simpa [hold_eq] using hold_lo
  · simpa [hold_eq] using hold_hi
  · rw [href_eq]
    rw [← hcomp]
    exact href_lo
  · rw [href_eq]
    rw [← hcomp]
    exact href_hi

/-- Source indexing pattern from Theorem B.1's dyadic subsequence. -/
def theoremB1SubsequenceIndex (C N : ℕ) : ℕ :=
  C * 2 ^ N + 1

/--
Starting the Appendix B recurrence at `C+1` gives the dyadic subsequence
`C * 2^N + 1` used in the public B.1 bridge.
-/
theorem theoremB1SourceDoubledIndexIterate_succ_eq_theoremB1SubsequenceIndex
    (C N : ℕ) :
    theoremB1SourceDoubledIndexIterate (C + 1) N =
      theoremB1SubsequenceIndex C N := by
  rw [theoremB1SourceDoubledIndexIterate_eq (Nat.succ_pos C) N]
  dsimp [theoremB1SubsequenceIndex]
  ring

/--
Equivalently, for a positive source start `C`, Appendix B's recurrence gives
the `(C-1) * 2^N + 1` subsequence appearing before the source's final change
of variables.
-/
theorem theoremB1SourceDoubledIndexIterate_eq_theoremB1SubsequenceIndex_pred
    {C : ℕ} (hC : 0 < C) (N : ℕ) :
    theoremB1SourceDoubledIndexIterate C N =
      theoremB1SubsequenceIndex (C - 1) N := by
  rw [theoremB1SourceDoubledIndexIterate_eq hC N]
  dsimp [theoremB1SubsequenceIndex]
  ring

/-- Elementary growth bound used by the dyadic B.1 subsequence index. -/
theorem nat_le_two_pow (N : ℕ) : N ≤ 2 ^ N := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hpow_pos : 0 < 2 ^ N := by positivity
      calc
        N + 1 ≤ 2 ^ N + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ N + 2 ^ N := by
          exact Nat.add_le_add_left hpow_pos (2 ^ N)
        _ = 2 ^ (N + 1) := by
          rw [pow_succ]
          omega

/-- Positive repeated C.5 endpoint indices tend to infinity. -/
theorem uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun q : ℕ => uniformDoubledEndpointIndexIterate m q)
      atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨b, ?_⟩
  intro q hq
  have hq_le_pow : q ≤ 2 ^ q := nat_le_two_pow q
  have hpow_pos : 0 < 2 ^ q := by positivity
  have hpow_succ_le_mul : 2 ^ q + 1 ≤ 2 ^ q * (m + 1) := by
    have htwo_le : 2 ≤ m + 1 := by omega
    have hmul_ge : 2 ^ q * 2 ≤ 2 ^ q * (m + 1) :=
      Nat.mul_le_mul_left (2 ^ q) htwo_le
    have hpow_succ_le_two : 2 ^ q + 1 ≤ 2 ^ q * 2 := by
      omega
    exact hpow_succ_le_two.trans hmul_ge
  have hq_succ_le_mul : q + 1 ≤ 2 ^ q * (m + 1) := by omega
  have hiter_add := uniformDoubledEndpointIndexIterate_add_one m q
  omega

/--
Bounded-error version of the B.1 common-coordinate selector bridge.  If the
source-selected old index is within `B` cells of a common clamped-floor
coordinate, and the refined selected index is within the scaled `B`-cell
error of that same coordinate, then the fixed-width scaled block window used
by the Cauchy proof follows eventually.

The eventual clause only ensures the old grid is large enough to contain a
block of the requested fixed width.
-/
theorem uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_bounded_error
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    {m0 B width : ℕ} (hm0 : 0 < m0)
    (hwidth : 2 + 2 * B ≤ width)
    (hcommon :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
              (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 M) x).1 ≤
                (levelIndex (uniformDoubledEndpointIndexIterate m0 M) θ).1 +
                  B ∧
              (levelIndex (uniformDoubledEndpointIndexIterate m0 M) θ).1 ≤
                (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 M) x).1 + B ∧
              (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 N) x).1 ≤
                (levelIndex (uniformDoubledEndpointIndexIterate m0 N) θ).1 +
                  2 ^ (N - M) * B ∧
              (levelIndex (uniformDoubledEndpointIndexIterate m0 N) θ).1 ≤
                (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 N) x).1 +
                  2 ^ (N - M) * B) :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + width ≤ uniformDoubledEndpointIndexIterate m0 M + 1,
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 M) θ).1 ≤
                  i + width ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 N) θ).1 ≤
                  2 ^ (N - M) * (i + width) := by
  have hlarge0 :
      ∀ᶠ M : ℕ in atTop,
        width ≤ uniformDoubledEndpointIndexIterate m0 M := by
    have htend := uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos hm0
    rw [Filter.tendsto_atTop] at htend
    exact htend width
  filter_upwards [hcommon, hlarge0] with M hMcommon hMlarge
  intro N hN θ hθ
  let mOld : ℕ := uniformDoubledEndpointIndexIterate m0 M
  let mRef : ℕ := uniformDoubledEndpointIndexIterate m0 N
  let scale : ℕ := 2 ^ (N - M)
  have hmOld : 0 < mOld := by
    dsimp [mOld]
    exact uniformDoubledEndpointIndexIterate_pos_of_pos hm0 M
  have hcomp :
      uniformDoubledEndpointIndexIterate mOld (N - M) = mRef := by
    dsimp [mOld, mRef]
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  rcases hMcommon N hN θ hθ with
    ⟨x, hx, hold_err_lo, hold_err_hi, href_err_lo, href_err_hi⟩
  rcases
      clampedFloorLevelIndex_iterated_old_refined_scaled_window
        (m := mOld) (q := N - M) hmOld hx.1 hx.2 with
    ⟨oldBlock, hold_lo, hold_hi, href_lo, href_hi⟩
  have href_lo' :
      scale * oldBlock.1 ≤
        (clampedFloorLevelIndex mRef x).1 := by
    dsimp [scale]
    rw [← hcomp]
    exact href_lo
  have href_hi' :
      (clampedFloorLevelIndex mRef x).1 ≤
        scale * (oldBlock.1 + 2) := by
    dsimp [scale]
    rw [← hcomp]
    exact href_hi
  let i : ℕ := min (oldBlock.1 - B) (mOld + 1 - width)
  have hi_right : i ≤ mOld + 1 - width := by
    dsimp [i]
    exact Nat.min_le_right _ _
  have hi_left : i ≤ oldBlock.1 - B := by
    dsimp [i]
    exact Nat.min_le_left _ _
  have hi_width : i + width ≤ mOld + 1 := by
    omega
  refine ⟨i, hi_width, ?_, ?_, ?_, ?_⟩
  · have hblock_le_sel :
        oldBlock.1 ≤
          (levelIndex mOld θ).1 + B :=
      hold_lo.trans (by simpa [mOld] using hold_err_lo)
    by_cases hB_le : B ≤ oldBlock.1
    · have hi_add_B_le_old : i + B ≤ oldBlock.1 := by
        omega
      have hi_add_B_le_sel_add :
          i + B ≤ (levelIndex mOld θ).1 + B :=
        hi_add_B_le_old.trans hblock_le_sel
      exact (Nat.add_le_add_iff_right).mp hi_add_B_le_sel_add
    · have hsub_zero : oldBlock.1 - B = 0 :=
        Nat.sub_eq_zero_of_le (le_of_not_ge hB_le)
      have hi_zero : i = 0 := by
        dsimp [i]
        rw [hsub_zero]
        simp
      rw [hi_zero]
      exact Nat.zero_le _
  · have hsel_le_block :
        (levelIndex mOld θ).1 ≤ oldBlock.1 + 2 + B := by
      have htmp :
          (levelIndex mOld θ).1 ≤
            (clampedFloorLevelIndex mOld x).1 + B := by
        simpa [mOld] using hold_err_hi
      exact htmp.trans (Nat.add_le_add_right hold_hi B)
    by_cases hleft_case : oldBlock.1 - B ≤ mOld + 1 - width
    · have hi_eq : i = oldBlock.1 - B := by
        dsimp [i]
        exact Nat.min_eq_left hleft_case
      have hidx_le : oldBlock.1 + 2 + B ≤ i + width := by
        rw [hi_eq]
        by_cases hB_le : B ≤ oldBlock.1
        · omega
        · omega
      exact hsel_le_block.trans hidx_le
    · have hi_eq : i = mOld + 1 - width := by
        dsimp [i]
        exact Nat.min_eq_right (by omega)
      have hsel_cap : (levelIndex mOld θ).1 ≤ mOld + 1 := by
        have hlt := (levelIndex mOld θ).isLt
        omega
      rw [hi_eq]
      omega
  · have hscale_block_le_sel :
        scale * oldBlock.1 ≤
          (levelIndex mRef θ).1 + scale * B :=
      href_lo'.trans (by simpa [mRef, scale] using href_err_lo)
    by_cases hB_le : B ≤ oldBlock.1
    · have hi_add_B_le : i + B ≤ oldBlock.1 := by
        omega
      have hscaled_i_add :
          scale * i + scale * B ≤
            (levelIndex mRef θ).1 + scale * B := by
        rw [← Nat.mul_add]
        exact (Nat.mul_le_mul_left scale hi_add_B_le).trans hscale_block_le_sel
      exact (Nat.add_le_add_iff_right).mp hscaled_i_add
    · have hsub_zero : oldBlock.1 - B = 0 :=
        Nat.sub_eq_zero_of_le (le_of_not_ge hB_le)
      have hi_zero : i = 0 := by
        dsimp [i]
        rw [hsub_zero]
        simp
      rw [hi_zero]
      simp
  · have hsel_le_scaled_block :
        (levelIndex mRef θ).1 ≤ scale * (oldBlock.1 + 2) + scale * B := by
      have htmp :
          (levelIndex mRef θ).1 ≤
            (clampedFloorLevelIndex mRef x).1 + scale * B := by
        simpa [mRef, scale] using href_err_hi
      exact htmp.trans (Nat.add_le_add_right href_hi' (scale * B))
    have hmRef_add_one : mRef + 1 = scale * (mOld + 1) := by
      have hadd := uniformDoubledEndpointIndexIterate_add_one mOld (N - M)
      rw [hcomp] at hadd
      simpa [scale] using hadd
    have hsel_ref_cap :
        (levelIndex mRef θ).1 ≤ scale * (mOld + 1) := by
      have hlt := (levelIndex mRef θ).isLt
      have hle : (levelIndex mRef θ).1 ≤ mRef + 1 := by omega
      simpa [hmRef_add_one] using hle
    by_cases hleft_case : oldBlock.1 - B ≤ mOld + 1 - width
    · have hi_eq : i = oldBlock.1 - B := by
        dsimp [i]
        exact Nat.min_eq_left hleft_case
      have hidx_le : oldBlock.1 + 2 + B ≤ i + width := by
        rw [hi_eq]
        omega
      have hscaled_target :
          scale * (oldBlock.1 + 2) + scale * B ≤
            scale * (i + width) := by
        have hmul :
            scale * ((oldBlock.1 + 2) + B) ≤
              scale * (i + width) :=
          Nat.mul_le_mul_left scale (by omega)
        simpa [Nat.mul_add, Nat.add_assoc] using hmul
      exact hsel_le_scaled_block.trans hscaled_target
    · have hi_eq : i = mOld + 1 - width := by
        dsimp [i]
        exact Nat.min_eq_right (by omega)
      have hi_add_width : i + width = mOld + 1 := by
        rw [hi_eq]
        omega
      rw [hi_add_width]
      exact hsel_ref_cap

/--
Variable-error version of
`uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_bounded_error`.
The old selector may be within `BSeq M` cells of a common source coordinate at
anchor depth `M`, and the refined selector may be within the dyadically scaled
error.  A variable block width absorbing `2 + 2 * BSeq M` then gives the
scaled block-window invariant.
-/
theorem uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_variable_bounded_error
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    {m0 : ℕ} (hm0 : 0 < m0)
    (BSeq widthSeq : ℕ → ℕ)
    (hwidth :
      ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq M ≤ widthSeq M)
    (hlarge :
      ∀ᶠ M : ℕ in atTop,
        widthSeq M ≤ uniformDoubledEndpointIndexIterate m0 M + 1)
    (hcommon :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
              (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 M) x).1 ≤
                (levelIndex (uniformDoubledEndpointIndexIterate m0 M) θ).1 +
                  BSeq M ∧
              (levelIndex (uniformDoubledEndpointIndexIterate m0 M) θ).1 ≤
                (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 M) x).1 + BSeq M ∧
              (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 N) x).1 ≤
                (levelIndex (uniformDoubledEndpointIndexIterate m0 N) θ).1 +
                  2 ^ (N - M) * BSeq M ∧
              (levelIndex (uniformDoubledEndpointIndexIterate m0 N) θ).1 ≤
                (clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate m0 N) x).1 +
                  2 ^ (N - M) * BSeq M) :
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + widthSeq M ≤ uniformDoubledEndpointIndexIterate m0 M + 1,
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 M) θ).1 ≤
                  i + widthSeq M ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate m0 N) θ).1 ≤
                  2 ^ (N - M) * (i + widthSeq M) := by
  filter_upwards [hcommon, hwidth, hlarge] with M hMcommon hMwidth hMlarge
  intro N hN θ hθ
  let mOld : ℕ := uniformDoubledEndpointIndexIterate m0 M
  let mRef : ℕ := uniformDoubledEndpointIndexIterate m0 N
  let scale : ℕ := 2 ^ (N - M)
  let B : ℕ := BSeq M
  let width : ℕ := widthSeq M
  have hmOld : 0 < mOld := by
    dsimp [mOld]
    exact uniformDoubledEndpointIndexIterate_pos_of_pos hm0 M
  have hcomp :
      uniformDoubledEndpointIndexIterate mOld (N - M) = mRef := by
    dsimp [mOld, mRef]
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have hwidth_absorb : 2 + 2 * B ≤ width := by
    dsimp [B, width]
    exact hMwidth
  have hlarge_width : width ≤ mOld + 1 := by
    dsimp [width, mOld]
    exact hMlarge
  rcases hMcommon N hN θ hθ with
    ⟨x, hx, hold_err_lo, hold_err_hi, href_err_lo, href_err_hi⟩
  rcases
      clampedFloorLevelIndex_iterated_old_refined_scaled_window
        (m := mOld) (q := N - M) hmOld hx.1 hx.2 with
    ⟨oldBlock, hold_lo, hold_hi, href_lo, href_hi⟩
  have href_lo' :
      scale * oldBlock.1 ≤
        (clampedFloorLevelIndex mRef x).1 := by
    dsimp [scale]
    rw [← hcomp]
    exact href_lo
  have href_hi' :
      (clampedFloorLevelIndex mRef x).1 ≤
        scale * (oldBlock.1 + 2) := by
    dsimp [scale]
    rw [← hcomp]
    exact href_hi
  let i : ℕ := min (oldBlock.1 - B) (mOld + 1 - width)
  have hi_width : i + width ≤ mOld + 1 := by
    dsimp [i]
    omega
  refine ⟨i, by simpa [width, mOld] using hi_width, ?_, ?_, ?_, ?_⟩
  · have hblock_le_sel :
        oldBlock.1 ≤
          (levelIndex mOld θ).1 + B :=
      hold_lo.trans (by simpa [mOld, B] using hold_err_lo)
    by_cases hB_le : B ≤ oldBlock.1
    · have hi_add_B_le_old : i + B ≤ oldBlock.1 := by
        dsimp [i]
        omega
      have hi_add_B_le_sel_add :
          i + B ≤ (levelIndex mOld θ).1 + B :=
        hi_add_B_le_old.trans hblock_le_sel
      have hi_le_sel : i ≤ (levelIndex mOld θ).1 :=
        (Nat.add_le_add_iff_right).mp hi_add_B_le_sel_add
      simpa [mOld] using hi_le_sel
    · have hsub_zero : oldBlock.1 - B = 0 :=
        Nat.sub_eq_zero_of_le (le_of_not_ge hB_le)
      have hi_zero : i = 0 := by
        dsimp [i]
        rw [hsub_zero]
        simp
      rw [hi_zero]
      exact Nat.zero_le _
  · have hsel_le_block :
        (levelIndex mOld θ).1 ≤ oldBlock.1 + 2 + B := by
      have htmp :
          (levelIndex mOld θ).1 ≤
            (clampedFloorLevelIndex mOld x).1 + B := by
        simpa [mOld, B] using hold_err_hi
      exact htmp.trans (Nat.add_le_add_right hold_hi B)
    by_cases hleft_case : oldBlock.1 - B ≤ mOld + 1 - width
    · have hi_eq : i = oldBlock.1 - B := by
        dsimp [i]
        exact Nat.min_eq_left hleft_case
      have hidx_le : oldBlock.1 + 2 + B ≤ i + width := by
        rw [hi_eq]
        omega
      have hsel_le : (levelIndex mOld θ).1 ≤ i + width :=
        hsel_le_block.trans hidx_le
      simpa [mOld, width] using hsel_le
    · have hi_eq : i = mOld + 1 - width := by
        dsimp [i]
        exact Nat.min_eq_right (by omega)
      have hsel_cap : (levelIndex mOld θ).1 ≤ mOld + 1 := by
        have hlt := (levelIndex mOld θ).isLt
        omega
      rw [hi_eq]
      omega
  · have hscale_block_le_sel :
        scale * oldBlock.1 ≤
          (levelIndex mRef θ).1 + scale * B :=
      href_lo'.trans (by simpa [mRef, scale, B] using href_err_lo)
    by_cases hB_le : B ≤ oldBlock.1
    · have hi_add_B_le : i + B ≤ oldBlock.1 := by
        dsimp [i]
        omega
      have hscaled_i_add :
          scale * i + scale * B ≤
            (levelIndex mRef θ).1 + scale * B := by
        rw [← Nat.mul_add]
        exact (Nat.mul_le_mul_left scale hi_add_B_le).trans hscale_block_le_sel
      have hscaled_i_le : scale * i ≤ (levelIndex mRef θ).1 :=
        (Nat.add_le_add_iff_right).mp hscaled_i_add
      simpa [mRef, scale] using hscaled_i_le
    · have hsub_zero : oldBlock.1 - B = 0 :=
        Nat.sub_eq_zero_of_le (le_of_not_ge hB_le)
      have hi_zero : i = 0 := by
        dsimp [i]
        rw [hsub_zero]
        simp
      rw [hi_zero]
      simp
  · have hsel_le_scaled_block :
        (levelIndex mRef θ).1 ≤ scale * (oldBlock.1 + 2) + scale * B := by
      have htmp :
          (levelIndex mRef θ).1 ≤
            (clampedFloorLevelIndex mRef x).1 + scale * B := by
        simpa [mRef, scale, B] using href_err_hi
      exact htmp.trans (Nat.add_le_add_right href_hi' (scale * B))
    have hmRef_add_one : mRef + 1 = scale * (mOld + 1) := by
      have hadd := uniformDoubledEndpointIndexIterate_add_one mOld (N - M)
      rw [hcomp] at hadd
      simpa [scale] using hadd
    have hsel_ref_cap :
        (levelIndex mRef θ).1 ≤ scale * (mOld + 1) := by
      have hlt := (levelIndex mRef θ).isLt
      have hle : (levelIndex mRef θ).1 ≤ mRef + 1 := by omega
      simpa [hmRef_add_one] using hle
    by_cases hleft_case : oldBlock.1 - B ≤ mOld + 1 - width
    · have hi_eq : i = oldBlock.1 - B := by
        dsimp [i]
        exact Nat.min_eq_left hleft_case
      have hidx_le : oldBlock.1 + 2 + B ≤ i + width := by
        rw [hi_eq]
        omega
      have hscaled_target :
          scale * (oldBlock.1 + 2) + scale * B ≤
            scale * (i + width) := by
        have hmul :
            scale * ((oldBlock.1 + 2) + B) ≤
              scale * (i + width) :=
          Nat.mul_le_mul_left scale (by omega)
        simpa [Nat.mul_add, Nat.add_assoc] using hmul
      have hsel_le : (levelIndex mRef θ).1 ≤ scale * (i + width) :=
        hsel_le_scaled_block.trans hscaled_target
      simpa [mRef, scale, width] using hsel_le
    · have hi_eq : i = mOld + 1 - width := by
        dsimp [i]
        exact Nat.min_eq_right (by omega)
      have hi_add_width : i + width = mOld + 1 := by
        rw [hi_eq]
        omega
      rw [hi_add_width]
      simpa [mRef, scale] using hsel_ref_cap

/--
Uniform equalized repeated C.5 subsequences with clamped-floor representation
have a uniform limit; Corollary C.2 supplies the mesh convergence required by
the repeated-refinement Cauchy bridge.
-/
theorem uniformDoubledEndpointIndexIterate_clampedFloor_subsequence_exists_uniform_limit_of_uniform_equalized
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq m θ = levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (uniformDoubledEndpointIndexIterate m N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  refine
    uniformDoubledEndpointIndexIterate_clampedFloor_subsequence_exists_uniform_limit
      betaSeq levels hrepr hlevels heq hm ?_
  let shiftedLevels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ :=
    fun N => levels (N + 1)
  have hshift_levels :
      ∀ N : ℕ, BinaryEndpointLevelVector (shiftedLevels N) := by
    intro N
    exact hlevels (N + 1)
  have hshift_eq :
      ∀ N : ℕ,
        BinaryEndpointAwareAdjacentRatesEqualize (shiftedLevels N)
          (fun _ : Fin ((N + 1) + 2) => (1 : ℝ)) := by
    intro N
    exact heq (N + 1)
  have hmesh_shift :
      Tendsto
        (fun N : ℕ =>
          binaryEndpointAdjacentMaxWidth (m := N + 1) (shiftedLevels N))
        atTop (nhds 0) :=
    corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
      shiftedLevels hshift_levels hshift_eq
  have hpred_tendsto :
      Tendsto
        (fun M : ℕ => uniformDoubledEndpointIndexIterate m M - 1)
        atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp
      (uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos hm)
  have hmesh_comp := hmesh_shift.comp hpred_tendsto
  refine Tendsto.congr' ?_ hmesh_comp
  filter_upwards with M
  have hpos := uniformDoubledEndpointIndexIterate_pos_of_pos hm M
  have hidx :
      (uniformDoubledEndpointIndexIterate m M - 1) + 1 =
        uniformDoubledEndpointIndexIterate m M :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
  exact congrArg
    (fun n : ℕ => binaryEndpointAdjacentMaxWidth (m := n) (levels n)) hidx

/--
The positive dyadic B.1 subsequence is a one-term shift of a repeated C.5
endpoint-index refinement, after translating source indices to endpoint counts.
-/
theorem theoremB1SubsequenceIndex_succ_eq_uniformDoubledEndpointIndexIterate_add_two
    {C : ℕ} (hC : 0 < C) (N : ℕ) :
    theoremB1SubsequenceIndex C (N + 1) =
      uniformDoubledEndpointIndexIterate (2 * C - 1) N + 2 := by
  have htwoc_pos : 0 < 2 * C := by omega
  have htwoc_pred : 2 * C - 1 + 1 = 2 * C :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr htwoc_pos)
  have hright :
      uniformDoubledEndpointIndexIterate (2 * C - 1) N + 2 =
        2 ^ N * (2 * C) + 1 := by
    have hiter :=
      uniformDoubledEndpointIndexIterate_add_one (2 * C - 1) N
    rw [htwoc_pred] at hiter
    omega
  rw [theoremB1SubsequenceIndex, hright, pow_succ]
  ring

/--
Theorem B.1 positive-dyadic source-index bridge for the clamped-floor endpoint
selector.  If the source beta sequence at index `m+2` is represented by the
endpoint vector with C.5/clamped-floor convention, every positive dyadic
subsequence `C * 2^N + 1` has a uniform limit on `[0,1]`.
-/
theorem theoremB1SubsequenceIndex_clampedFloor_subsequence_exists_uniform_limit_of_uniform_equalized
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {C : ℕ} (hC : 0 < C) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  obtain ⟨betaLimit, htail_internal⟩ :=
    uniformDoubledEndpointIndexIterate_clampedFloor_subsequence_exists_uniform_limit_of_uniform_equalized
      (fun m : ℕ => fun θ : ℝ => betaSeq (m + 2) θ)
      levels hrepr hlevels heq hendpointStart
  refine ⟨betaLimit, ?_⟩
  refine AppliedModelingLib.Math.TendstoUniformlyOn.of_succ ?_
  refine htail_internal.congr ?_
  filter_upwards with N
  intro θ _hθ
  rw [theoremB1SubsequenceIndex_succ_eq_uniformDoubledEndpointIndexIterate_add_two
    hC N]

/--
Theorem B.1 positive-dyadic source-index bridge for arbitrary source
selectors.  The only source-specific selector input is the eventual scaled
index-window invariant along the corresponding repeated C.5 chain.
-/
theorem theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_index_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {C : ℕ} (hC : 0 < C)
    (hwindow :
      let endpointStart : ℕ := 2 * C - 1
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : Fin (uniformDoubledEndpointIndexIterate endpointStart M),
              i.1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                  i.1 + 2 ∧
                2 ^ (N - M) * i.1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                  2 ^ (N - M) * (i.1 + 2)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  obtain ⟨betaLimit, htail_internal⟩ :=
    uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_index_window
      (fun m : ℕ => fun θ : ℝ => betaSeq (m + 2) θ)
      levels levelIndex hrepr hlevels heq hendpointStart
      (hmesh := by
        let shiftedLevels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ :=
          fun N => levels (N + 1)
        have hshift_levels :
            ∀ N : ℕ, BinaryEndpointLevelVector (shiftedLevels N) := by
          intro N
          exact hlevels (N + 1)
        have hshift_eq :
            ∀ N : ℕ,
              BinaryEndpointAwareAdjacentRatesEqualize (shiftedLevels N)
                (fun _ : Fin ((N + 1) + 2) => (1 : ℝ)) := by
          intro N
          exact heq (N + 1)
        have hmesh_shift :
            Tendsto
              (fun N : ℕ =>
                binaryEndpointAdjacentMaxWidth (m := N + 1) (shiftedLevels N))
              atTop (nhds 0) :=
          corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
            shiftedLevels hshift_levels hshift_eq
        have hpred_tendsto :
            Tendsto
              (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M - 1)
              atTop atTop :=
          (tendsto_sub_atTop_nat 1).comp
            (uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
              hendpointStart)
        have hmesh_comp := hmesh_shift.comp hpred_tendsto
        refine Tendsto.congr' ?_ hmesh_comp
        filter_upwards with M
        have hpos :=
          uniformDoubledEndpointIndexIterate_pos_of_pos hendpointStart M
        have hidx :
            (uniformDoubledEndpointIndexIterate endpointStart M - 1) + 1 =
              uniformDoubledEndpointIndexIterate endpointStart M :=
          Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
        exact congrArg
          (fun n : ℕ => binaryEndpointAdjacentMaxWidth (m := n) (levels n))
          hidx)
      (by simpa [endpointStart] using hwindow)
  refine ⟨betaLimit, ?_⟩
  refine AppliedModelingLib.Math.TendstoUniformlyOn.of_succ ?_
  refine htail_internal.congr ?_
  filter_upwards with N
  intro θ _hθ
  rw [theoremB1SubsequenceIndex_succ_eq_uniformDoubledEndpointIndexIterate_add_two
    hC N]

/--
Theorem B.1 positive-dyadic source-index bridge for arbitrary source
selectors satisfying a fixed-width scaled block window.  This is the
source-quantile-tolerant version of the scaled selector-window bridge above.
-/
theorem theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {C : ℕ} (hC : 0 < C)
    (width : ℕ) (hwidth : 2 ≤ width)
    (hwindow :
      let endpointStart : ℕ := 2 * C - 1
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + width ≤ uniformDoubledEndpointIndexIterate endpointStart M + 1,
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                  i + width ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                  2 ^ (N - M) * (i + width)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  obtain ⟨betaLimit, htail_internal⟩ :=
    uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_block_window
      (fun m : ℕ => fun θ : ℝ => betaSeq (m + 2) θ)
      levels levelIndex hrepr hlevels heq hendpointStart
      width hwidth
      (hmesh := by
        let shiftedLevels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ :=
          fun N => levels (N + 1)
        have hshift_levels :
            ∀ N : ℕ, BinaryEndpointLevelVector (shiftedLevels N) := by
          intro N
          exact hlevels (N + 1)
        have hshift_eq :
            ∀ N : ℕ,
              BinaryEndpointAwareAdjacentRatesEqualize (shiftedLevels N)
                (fun _ : Fin ((N + 1) + 2) => (1 : ℝ)) := by
          intro N
          exact heq (N + 1)
        have hmesh_shift :
            Tendsto
              (fun N : ℕ =>
                binaryEndpointAdjacentMaxWidth (m := N + 1) (shiftedLevels N))
              atTop (nhds 0) :=
          corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
            shiftedLevels hshift_levels hshift_eq
        have hpred_tendsto :
            Tendsto
              (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M - 1)
              atTop atTop :=
          (tendsto_sub_atTop_nat 1).comp
            (uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
              hendpointStart)
        have hmesh_comp := hmesh_shift.comp hpred_tendsto
        refine Tendsto.congr' ?_ hmesh_comp
        filter_upwards with M
        have hpos :=
          uniformDoubledEndpointIndexIterate_pos_of_pos hendpointStart M
        have hidx :
            (uniformDoubledEndpointIndexIterate endpointStart M - 1) + 1 =
              uniformDoubledEndpointIndexIterate endpointStart M :=
          Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
        exact congrArg
          (fun n : ℕ => binaryEndpointAdjacentMaxWidth (m := n) (levels n))
          hidx)
      (by simpa [endpointStart] using hwindow)
  refine ⟨betaLimit, ?_⟩
  refine AppliedModelingLib.Math.TendstoUniformlyOn.of_succ ?_
  refine htail_internal.congr ?_
  filter_upwards with N
  intro θ _hθ
  rw [theoremB1SubsequenceIndex_succ_eq_uniformDoubledEndpointIndexIterate_add_two
    hC N]

/--
Theorem B.1 positive-dyadic source-index bridge for arbitrary source
selectors satisfying a variable-width scaled block window.  This is the
non-equispaced selector version: the window width may grow with the anchor
depth, as long as width times the anchor endpoint mesh goes to zero.
-/
theorem theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_block_window_variable_width
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {C : ℕ} (hC : 0 < C)
    (widthSeq : ℕ → ℕ)
    (hmeshWidth :
      let endpointStart : ℕ := 2 * C - 1
      Tendsto
        (fun M : ℕ =>
          (widthSeq M : ℝ) *
            binaryEndpointAdjacentMaxWidth
              (m := uniformDoubledEndpointIndexIterate endpointStart M)
              (levels (uniformDoubledEndpointIndexIterate endpointStart M)))
        atTop (nhds 0))
    (hwidth : ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq M)
    (hwindow :
      let endpointStart : ℕ := 2 * C - 1
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + widthSeq M ≤
                uniformDoubledEndpointIndexIterate endpointStart M + 1,
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                  i + widthSeq M ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                  2 ^ (N - M) * (i + widthSeq M)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  obtain ⟨betaLimit, htail_internal⟩ :=
    uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_block_window_variable_width
      (fun m : ℕ => fun θ : ℝ => betaSeq (m + 2) θ)
      levels levelIndex hrepr hlevels heq hendpointStart widthSeq
      (hmeshWidth := by
        simpa [endpointStart] using hmeshWidth)
      hwidth
      (by simpa [endpointStart] using hwindow)
  refine ⟨betaLimit, ?_⟩
  refine AppliedModelingLib.Math.TendstoUniformlyOn.of_succ ?_
  refine htail_internal.congr ?_
  filter_upwards with N
  intro θ _hθ
  rw [theoremB1SubsequenceIndex_succ_eq_uniformDoubledEndpointIndexIterate_add_two
    hC N]

/--
Theorem B.1 positive-dyadic source-index bridge for arbitrary source
selectors satisfying a non-equispaced metric scaled block window.  The source
controls the actual old endpoint span of the selected block, not the number of
old cells in that block.
-/
theorem theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_metric_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {C : ℕ} (hC : 0 < C)
    (widthSeq : ℕ → ℕ) (blockWidth : ℕ → ℝ)
    (hblockWidth :
      Tendsto blockWidth atTop (nhds 0))
    (hblockWidth_nonneg : ∀ M : ℕ, 0 ≤ blockWidth M)
    (hwidth : ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq M)
    (hwindow :
      let endpointStart : ℕ := 2 * C - 1
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ i : ℕ, ∃ hi :
              i + widthSeq M ≤
                uniformDoubledEndpointIndexIterate endpointStart M + 1,
              levels (uniformDoubledEndpointIndexIterate endpointStart M)
                  ⟨i + widthSeq M, by omega⟩ -
                levels (uniformDoubledEndpointIndexIterate endpointStart M)
                  ⟨i, by omega⟩ ≤ blockWidth M ∧
              i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                  i + widthSeq M ∧
                2 ^ (N - M) * i ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                  2 ^ (N - M) * (i + widthSeq M)) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  obtain ⟨betaLimit, htail_internal⟩ :=
    uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_metric_block_window
      (fun m : ℕ => fun θ : ℝ => betaSeq (m + 2) θ)
      levels levelIndex hrepr hlevels heq hendpointStart widthSeq blockWidth
      hblockWidth hblockWidth_nonneg hwidth
      (by simpa [endpointStart] using hwindow)
  refine ⟨betaLimit, ?_⟩
  refine AppliedModelingLib.Math.TendstoUniformlyOn.of_succ ?_
  refine htail_internal.congr ?_
  filter_upwards with N
  intro θ _hθ
  rw [theoremB1SubsequenceIndex_succ_eq_uniformDoubledEndpointIndexIterate_add_two
    hC N]

/-- Positive dyadic B.1 subsequence indices tend to infinity. -/
theorem theoremB1SubsequenceIndex_tendsto_atTop_of_pos
    {C : ℕ} (hC : 0 < C) :
    Tendsto (fun N : ℕ => theoremB1SubsequenceIndex C N) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨b, ?_⟩
  intro N hN
  have hN_le_pow : N ≤ 2 ^ N := nat_le_two_pow N
  have hpow_le_mul : 2 ^ N ≤ C * 2 ^ N :=
    Nat.le_mul_of_pos_left (2 ^ N) hC
  calc
    b ≤ N := hN
    _ ≤ 2 ^ N := hN_le_pow
    _ ≤ C * 2 ^ N := hpow_le_mul
    _ ≤ theoremB1SubsequenceIndex C N := by
      dsimp [theoremB1SubsequenceIndex]
      omega

/--
Theorem B.1 as a reusable source-shaped convergence principle.  If the
interval-quantile maps converge uniformly to the identity, then every dyadic
subsequence `C * 2^N + 1` of optimal binary rules has a uniform limit.

This definition intentionally isolates the still-hard B.1 compactness/Cauchy
argument from the Kendall/Spearman equispaced-interval algebra.
-/
def theoremB1UniformOptimalSubsequencePrinciple
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) : Prop :=
  TendstoUniformlyOn quantileSeq
      (fun θ : ℝ => θ) atTop (Set.Icc (0 : ℝ) 1) →
    ∀ C : ℕ, ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1)

/--
Source-facing B.1 conclusion without naming a quantile limit: every dyadic
subsequence `C * 2^N + 1` has a uniform limit on `[0,1]`.  Several selector
bridges prove this conclusion directly; the printed theorem's quantile
convergence hypothesis is one source-side route to the selector hypotheses.
-/
def theoremB1DyadicSubsequenceUniformConvergence
    (betaSeq : ℕ → ℝ → ℝ) : Prop :=
  ∀ C : ℕ, ∃ betaLimit : ℝ → ℝ,
    TendstoUniformlyOn
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      betaLimit atTop (Set.Icc (0 : ℝ) 1)

/--
General-limit version of Theorem B.1.  The source theorem assumes only that
the interval-quantile maps converge uniformly; the equispaced
Kendall/Spearman specialization instantiates the limit as the identity.
-/
def theoremB1UniformOptimalSubsequencePrincipleTo
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ) : Prop :=
  TendstoUniformlyOn quantileSeq quantileLimit atTop (Set.Icc (0 : ℝ) 1) →
    theoremB1DyadicSubsequenceUniformConvergence betaSeq

theorem theoremB1UniformOptimalSubsequencePrinciple_iff_to_identity
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq ↔
      theoremB1UniformOptimalSubsequencePrincipleTo
        betaSeq quantileSeq (fun θ : ℝ => θ) := by
  rfl

/--
Uniform limits of quantile maps with values in `[0,1]` still take values in
`[0,1]`.  The range hypothesis is stated on the shifted paper index
`m + 2`, matching the endpoint-chain convention used in B.1.
-/
theorem theoremB1_quantileLimit_mem_Icc_of_tendstoUniformlyOn_shift
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (hquantile :
      TendstoUniformlyOn quantileSeq quantileLimit atTop
        (Set.Icc (0 : ℝ) 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      quantileLimit θ ∈ Set.Icc (0 : ℝ) 1 := by
  intro θ hθ
  have hshift :
      Tendsto (fun m : ℕ => m + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have hquantile_shift :
      TendstoUniformlyOn
        (fun m : ℕ => fun θ : ℝ => quantileSeq (m + 2) θ)
        quantileLimit atTop (Set.Icc (0 : ℝ) 1) :=
    AppliedModelingLib.Math.TendstoUniformlyOn.comp_tendsto_index
      hquantile hshift
  exact
    isClosed_Icc.mem_of_tendsto
      (hquantile_shift.tendsto_at hθ)
      (Eventually.of_forall (fun m : ℕ => hquantile_range m θ hθ))

/--
Theorem B.1 source-index bridge from the explicit clamped-floor C.5 model.
The positive dyadic subsequences are handled by the shifted repeated-C.5
wrapper above, while the `C = 0` subsequence is the constant index `1`.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_clampedFloor
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_clampedFloor_subsequence_exists_uniform_limit_of_uniform_equalized
        betaSeq levels hrepr hlevels heq hC
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
Theorem B.1 clamped-floor bridge with finite optimal endpoint chains.  Finite
uniform optimality supplies both endpoint-vector feasibility and the equalized
adjacent-rate condition consumed by the clamped-floor source selector proof.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_clampedFloor
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_clampedFloor
    betaSeq quantileSeq levels hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))

/--
Theorem B.1 source-index bridge for arbitrary source selectors.  Uniform
equalized endpoint levels plus an eventual scaled selector-window invariant
for each positive dyadic source subsequence imply the full B.1 subsequence
principle.  The `C = 0` branch is the constant source index `1`.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_scaled_index_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (uniformDoubledEndpointIndexIterate endpointStart M),
                i.1 ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i.1 + 2 ∧
                  2 ^ (N - M) * i.1 ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i.1 + 2)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_index_window
        betaSeq levels levelIndex hrepr hlevels heq hC
        (hwindow C hC)
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
Source-facing B.1 conclusion from an eventual scaled selector-window invariant.
This is the same Cauchy-completeness argument as the theorem above, stated
without an artificial identity-quantile hypothesis.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_index_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (uniformDoubledEndpointIndexIterate endpointStart M),
                i.1 ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i.1 + 2 ∧
                  2 ^ (N - M) * i.1 ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i.1 + 2)) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_index_window
        betaSeq levels levelIndex hrepr hlevels heq hC
        (hwindow C hC)
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
General-limit Theorem B.1 bridge from an eventual scaled selector-window
invariant.  The quantile limit is accepted as an arbitrary uniform limit,
matching the source theorem's statement; the selector-window proof itself
already gives the dyadic subsequence conclusion.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_index_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (uniformDoubledEndpointIndexIterate endpointStart M),
                i.1 ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i.1 + 2 ∧
                  2 ^ (N - M) * i.1 ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i.1 + 2)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_index_window
      betaSeq levels levelIndex hrepr hlevels heq hwindow

/--
Theorem B.1 source-index bridge for arbitrary source selectors satisfying a
fixed-width scaled block window.  This bridges the paper's approximate
quantile-window reasoning to the dyadic subsequence conclusion.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_scaled_block_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (width : ℕ) (hwidth : 2 ≤ width)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + width ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + width ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + width)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_block_window
        betaSeq levels levelIndex hrepr hlevels heq hC width hwidth
        (hwindow C hC)
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
Source-facing B.1 conclusion from an eventual fixed-width scaled
selector-window invariant, stated without choosing a quantile limit.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (width : ℕ) (hwidth : 2 ≤ width)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + width ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + width ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + width)) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_block_window
        betaSeq levels levelIndex hrepr hlevels heq hC width hwidth
        (hwindow C hC)
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
General-limit B.1 bridge from an eventual fixed-width scaled selector-window
invariant.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (width : ℕ) (hwidth : 2 ≤ width)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + width ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + width ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + width)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window
      betaSeq levels levelIndex hrepr hlevels heq width hwidth hwindow

/--
Source-facing B.1 conclusion from an eventual variable-width scaled
selector-window invariant.  The variable width is indexed by the dyadic
subsequence parameter `C` and anchor depth `M`; the required mesh condition is
that this width times the old endpoint adjacent mesh tends to zero for every
positive `C`.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window_variable_width
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (widthSeq : ℕ → ℕ → ℕ)
    (hmeshWidth :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (widthSeq C M : ℝ) *
              binaryEndpointAdjacentMaxWidth
                (m := uniformDoubledEndpointIndexIterate endpointStart M)
                (levels (uniformDoubledEndpointIndexIterate endpointStart M)))
          atTop (nhds 0))
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_block_window_variable_width
        betaSeq levels levelIndex hrepr hlevels heq hC (widthSeq C)
        (hmeshWidth C hC) (hwidth C hC) (hwindow C hC)
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
General-limit B.1 bridge from an eventual variable-width scaled
selector-window invariant.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window_variable_width
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (widthSeq : ℕ → ℕ → ℕ)
    (hmeshWidth :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (widthSeq C M : ℝ) *
              binaryEndpointAdjacentMaxWidth
                (m := uniformDoubledEndpointIndexIterate endpointStart M)
                (levels (uniformDoubledEndpointIndexIterate endpointStart M)))
          atTop (nhds 0))
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window_variable_width
      betaSeq levels levelIndex hrepr hlevels heq widthSeq hmeshWidth
      hwidth hwindow

/--
Source-facing B.1 conclusion from a variable-width scaled selector window whose
width grows slower than the square-root endpoint resolution available for
uniform equalized endpoint chains.  The quantitative C.2 max-gap bound derives
the mesh-product premise of the previous theorem internally.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window_subsqrt
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (widthSeq : ℕ → ℕ → ℕ)
    (hwidthSqRate :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            ((widthSeq C M : ℝ) ^ 2) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
          atTop (nhds 0))
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  refine
    theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window_variable_width
      betaSeq levels levelIndex hrepr hlevels heq widthSeq ?_ hwidth hwindow
  intro C hC
  let endpointStart : ℕ := 2 * C - 1
  let meshProd : ℕ → ℝ := fun M : ℕ =>
    (widthSeq C M : ℝ) *
      binaryEndpointAdjacentMaxWidth
        (m := uniformDoubledEndpointIndexIterate endpointStart M)
        (levels (uniformDoubledEndpointIndexIterate endpointStart M))
  let sqBound : ℕ → ℝ := fun M : ℕ =>
    ((widthSeq C M : ℝ) ^ 2) /
      (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ))
  have hsqBound_zero : Tendsto sqBound atTop (nhds 0) := by
    simpa [sqBound, endpointStart] using hwidthSqRate C hC
  have hsqrt_zero :
      Tendsto (fun M : ℕ => Real.sqrt (sqBound M)) atTop (nhds 0) := by
    simpa [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsqBound_zero
  have hendpointStart : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  have habs_bound :
      ∀ᶠ M : ℕ in atTop, |meshProd M| ≤ Real.sqrt (sqBound M) := by
    filter_upwards with M
    let mM : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    let maxW : ℝ := binaryEndpointAdjacentMaxWidth (m := mM) (levels mM)
    have hmM_pos : 0 < mM := by
      dsimp [mM]
      exact uniformDoubledEndpointIndexIterate_pos_of_pos hendpointStart M
    have hmaxW_nonneg : 0 ≤ maxW := by
      dsimp [maxW]
      exact binaryEndpointAdjacentMaxWidth_nonneg (hlevels mM)
    have hprod_nonneg : 0 ≤ meshProd M := by
      dsimp [meshProd, maxW, mM]
      exact mul_nonneg (by exact_mod_cast Nat.zero_le (widthSeq C M))
        hmaxW_nonneg
    have hmaxW_sq :
        maxW ^ 2 ≤ 1 / (((mM + 1 : ℕ) : ℝ)) := by
      dsimp [maxW]
      exact
        binaryEndpointAdjacentMaxWidth_sq_le_inv_of_uniform_equalized
          hmM_pos (hlevels mM) (heq mM)
    have hprod_sq :
        (meshProd M) ^ 2 ≤ sqBound M := by
      have hmul :
          ((widthSeq C M : ℝ) ^ 2) * maxW ^ 2 ≤
            ((widthSeq C M : ℝ) ^ 2) *
              (1 / (((mM + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hmaxW_sq (sq_nonneg _)
      simpa [meshProd, sqBound, maxW, mM, div_eq_mul_inv, mul_pow] using hmul
    simpa [abs_of_nonneg hprod_nonneg] using Real.le_sqrt_of_sq_le hprod_sq
  have hzero :=
    AppliedModelingLib.Math.TendsToZero_of_eventually_abs_le_tendsto_zero
      meshProd (fun M : ℕ => Real.sqrt (sqBound M)) hsqrt_zero habs_bound
  simpa [AppliedModelingLib.Math.TendsToZero, meshProd, endpointStart] using hzero

/--
General-limit B.1 bridge from a sub-square-root variable-width scaled selector
window.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window_subsqrt
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (widthSeq : ℕ → ℕ → ℕ)
    (hwidthSqRate :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            ((widthSeq C M : ℝ) ^ 2) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
          atTop (nhds 0))
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_block_window_subsqrt
      betaSeq levels levelIndex hrepr hlevels heq widthSeq hwidthSqRate
      hwidth hwindow

/--
Source-facing B.1 conclusion from an eventual non-equispaced metric
selector-window invariant.  Unlike the max-mesh variable-width bridge, this
assumption controls the actual endpoint span of the selected old block.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_metric_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (widthSeq : ℕ → ℕ → ℕ) (blockWidth : ℕ → ℕ → ℝ)
    (hblockWidth :
      ∀ C : ℕ, 0 < C →
        Tendsto (blockWidth C) atTop (nhds 0))
    (hblockWidth_nonneg :
      ∀ C : ℕ, 0 < C → ∀ M : ℕ, 0 ≤ blockWidth C M)
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                levels (uniformDoubledEndpointIndexIterate endpointStart M)
                    ⟨i + widthSeq C M, by omega⟩ -
                  levels (uniformDoubledEndpointIndexIterate endpointStart M)
                    ⟨i, by omega⟩ ≤ blockWidth C M ∧
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  by_cases hC : 0 < C
  · exact
      theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_metric_block_window
        betaSeq levels levelIndex hrepr hlevels heq hC (widthSeq C)
        (blockWidth C) (hblockWidth C hC) (hblockWidth_nonneg C hC)
        (hwidth C hC) (hwindow C hC)
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
General-limit B.1 bridge from an eventual non-equispaced metric
selector-window invariant.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_metric_block_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (widthSeq : ℕ → ℕ → ℕ) (blockWidth : ℕ → ℕ → ℝ)
    (hblockWidth :
      ∀ C : ℕ, 0 < C →
        Tendsto (blockWidth C) atTop (nhds 0))
    (hblockWidth_nonneg :
      ∀ C : ℕ, 0 < C → ∀ M : ℕ, 0 ≤ blockWidth C M)
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                levels (uniformDoubledEndpointIndexIterate endpointStart M)
                    ⟨i + widthSeq C M, by omega⟩ -
                  levels (uniformDoubledEndpointIndexIterate endpointStart M)
                    ⟨i, by omega⟩ ≤ blockWidth C M ∧
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_uniform_equalized_eventually_scaled_metric_block_window
      betaSeq levels levelIndex hrepr hlevels heq widthSeq blockWidth
      hblockWidth hblockWidth_nonneg hwidth hwindow

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains and a
fixed-width scaled block window.  Finite optimality supplies equalized rates;
the remaining source work is the approximate selector-window invariant.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_scaled_block_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (width : ℕ) (hwidth : 2 ≤ width)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + width ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + width ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + width)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_scaled_block_window
    betaSeq quantileSeq levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    width hwidth hwindow

/--
General-limit B.1 source-index bridge for optimal uniform endpoint chains and
a variable-width scaled block window.  This is the non-equispaced selector
bridge: finite optimality supplies equalized rates, while the source must
provide a selector-window width whose product with the old endpoint mesh tends
to zero along every dyadic tail.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_block_window_variable_width
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (widthSeq : ℕ → ℕ → ℕ)
    (hmeshWidth :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (widthSeq C M : ℝ) *
              binaryEndpointAdjacentMaxWidth
                (m := uniformDoubledEndpointIndexIterate endpointStart M)
                (levels (uniformDoubledEndpointIndexIterate endpointStart M)))
          atTop (nhds 0))
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window_variable_width
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    widthSeq hmeshWidth hwidth hwindow

/--
General-limit B.1 source-index bridge for optimal uniform endpoint chains and
a sub-square-root variable-width scaled block window.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_block_window_subsqrt
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (widthSeq : ℕ → ℕ → ℕ)
    (hwidthSqRate :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            ((widthSeq C M : ℝ) ^ 2) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
          atTop (nhds 0))
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window_subsqrt
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    widthSeq hwidthSqRate hwidth hwindow

/--
If a natural-valued block width has square negligible relative to an endpoint
count, then eventually the block fits inside that endpoint grid.
-/
theorem eventually_width_le_endpoint_add_one_of_sq_div_tendsto_zero
    (mSeq widthSeq : ℕ → ℕ)
    (hzero :
      Tendsto
        (fun M : ℕ =>
          ((widthSeq M : ℝ) ^ 2) / (((mSeq M + 1 : ℕ) : ℝ)))
        atTop (nhds 0)) :
    ∀ᶠ M : ℕ in atTop, widthSeq M ≤ mSeq M + 1 := by
  have hlt_one :
      ∀ᶠ M : ℕ in atTop,
        ((widthSeq M : ℝ) ^ 2) / (((mSeq M + 1 : ℕ) : ℝ)) < 1 :=
    hzero.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hlt_one] with M hM
  by_contra hnot
  have hden_pos : 0 < (((mSeq M + 1 : ℕ) : ℝ)) := by
    positivity
  have hden_ge_one : (1 : ℝ) ≤ (((mSeq M + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (mSeq M))
  have hgt_nat : mSeq M + 1 < widthSeq M := Nat.lt_of_not_ge hnot
  have hden_le_width : (((mSeq M + 1 : ℕ) : ℝ)) ≤ (widthSeq M : ℝ) := by
    exact_mod_cast hgt_nat.le
  have hsq_le :
      (((mSeq M + 1 : ℕ) : ℝ)) ^ 2 ≤ (widthSeq M : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hden_le_width
  have hquot_ge_den :
      (((mSeq M + 1 : ℕ) : ℝ)) ≤
        ((widthSeq M : ℝ) ^ 2) / (((mSeq M + 1 : ℕ) : ℝ)) := by
    rw [le_div_iff₀ hden_pos]
    simpa [pow_two] using hsq_le
  have hquot_ge_one :
      (1 : ℝ) ≤
        ((widthSeq M : ℝ) ^ 2) / (((mSeq M + 1 : ℕ) : ℝ)) :=
    hden_ge_one.trans hquot_ge_den
  linarith

/--
If a natural-valued block width is `o(mSeq M)`, then eventually it fits in the
endpoint grid of size `mSeq M + 1`.
-/
theorem eventually_width_le_endpoint_add_one_of_div_tendsto_zero
    (mSeq widthSeq : ℕ → ℕ)
    (hzero :
      Tendsto
        (fun M : ℕ =>
          (widthSeq M : ℝ) / (((mSeq M + 1 : ℕ) : ℝ)))
        atTop (nhds 0)) :
    ∀ᶠ M : ℕ in atTop, widthSeq M ≤ mSeq M + 1 := by
  have hlt_one :
      ∀ᶠ M : ℕ in atTop,
        (widthSeq M : ℝ) / (((mSeq M + 1 : ℕ) : ℝ)) < 1 :=
    hzero.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hlt_one] with M hM
  by_contra hnot
  have hden_pos : 0 < (((mSeq M + 1 : ℕ) : ℝ)) := by
    positivity
  have hgt_nat : mSeq M + 1 < widthSeq M := Nat.lt_of_not_ge hnot
  have hden_le_width : (((mSeq M + 1 : ℕ) : ℝ)) ≤ (widthSeq M : ℝ) := by
    exact_mod_cast hgt_nat.le
  have hquot_ge_one :
      (1 : ℝ) ≤
        (widthSeq M : ℝ) / (((mSeq M + 1 : ℕ) : ℝ)) := by
    rw [le_div_iff₀ hden_pos]
    simpa using hden_le_width
  linarith

/--
General-limit B.1 bridge from the paper's quantile-floor selector convention
and a variable dyadic tracking envelope, using the direct mesh-product
condition.  This is the source-faithful endpoint-span route: if the selected
old block width induced by quantile drift has vanishing product with the old
endpoint mesh, the B.1 Cauchy proof goes through without requiring the
sub-square-root specialization below.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_mesh_width
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (BSeq widthSeq : ℕ → ℕ → ℕ)
    (hmeshWidth :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (widthSeq C M : ℝ) *
              binaryEndpointAdjacentMaxWidth
                (m := uniformDoubledEndpointIndexIterate endpointStart M)
                (levels (uniformDoubledEndpointIndexIterate endpointStart M)))
          atTop (nhds 0))
    (hwidth_absorb :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M)
    (hlarge :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          widthSeq C M ≤
            uniformDoubledEndpointIndexIterate endpointStart M + 1)
    (hdist_track :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_block_window_variable_width
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      widthSeq hmeshWidth ?_ ?_
  · intro C hC
    filter_upwards [hwidth_absorb C hC] with M hM
    omega
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    refine
      uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_variable_bounded_error
        levelIndex hendpointStart (BSeq C) (widthSeq C)
        (hwidth_absorb C hC)
        (by simpa [endpointStart] using hlarge C hC)
        ?_
    filter_upwards [hdist_track C hC] with M hM
    intro N hN θ hθ
    let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
    let scale : ℕ := 2 ^ (N - M)
    have hold_eq :
        levelIndex mOld θ =
          clampedFloorLevelIndex mOld (quantileSeq (mOld + 2) θ) := by
      apply Fin.ext
      rw [hlevelIndex_val mOld θ hθ, clampedFloorLevelIndex_val]
    have href_eq :
        levelIndex mRef θ =
          clampedFloorLevelIndex mRef (quantileSeq (mRef + 2) θ) := by
      apply Fin.ext
      rw [hlevelIndex_val mRef θ hθ, clampedFloorLevelIndex_val]
    rcases hM N hN θ hθ with ⟨hold_dist, href_dist⟩
    refine ⟨quantileLimit θ, hlimit_range θ hθ, ?_, ?_, ?_, ?_⟩
    · have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mOld (BSeq C M) (hquantile_range mOld θ hθ).1 hold_dist
      simpa [mOld, hold_eq] using hfloor
    · have hold_dist_sym :
          dist (quantileSeq (mOld + 2) θ) (quantileLimit θ) ≤
            (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
        simpa [dist_comm, mOld] using hold_dist
      have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mOld (BSeq C M) (hlimit_range θ hθ).1 hold_dist_sym
      simpa [mOld, hold_eq] using hfloor
    · have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mRef (scale * BSeq C M) (hquantile_range mRef θ hθ).1
          (by simpa [mRef, scale] using href_dist)
      simpa [mRef, scale, href_eq] using hfloor
    · have href_dist_sym :
          dist (quantileSeq (mRef + 2) θ) (quantileLimit θ) ≤
            ((scale * BSeq C M : ℕ) : ℝ) / (((mRef + 2 : ℕ) : ℝ)) := by
        simpa [dist_comm, mRef, scale] using href_dist
      have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mRef (scale * BSeq C M) (hlimit_range θ hθ).1 href_dist_sym
      simpa [mRef, scale, href_eq] using hfloor

/--
Linear-endpoint-mesh version of the quantile-floor B.1 bridge.  If the
selected quantile-error window is sublinear in the old endpoint count and the
uniform equalized endpoint mesh has a linear max-gap bound, then the direct
mesh-product premise above follows.

This theorem isolates the shortest remaining endpoint-geometry route for the
printed arbitrary-weight B.1 statement: prove the displayed linear mesh bound
for the uniform optimal endpoint levels, then derive the sublinear window from
uniform convergence of the interval-quantile maps.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_linear_mesh
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (BSeq widthSeq : ℕ → ℕ → ℕ) (K : ℝ)
    (hwidth_ratio :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (widthSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
                ℝ)))
          atTop (nhds 0))
    (hlinearMesh :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          binaryEndpointAdjacentMaxWidth
              (m := uniformDoubledEndpointIndexIterate endpointStart M)
              (levels (uniformDoubledEndpointIndexIterate endpointStart M)) ≤
            K /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
                ℝ)))
    (hwidth_absorb :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M)
    (hdist_track :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_mesh_width
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hquantile_range hlimit_range BSeq widthSeq ?_
      hwidth_absorb ?_ hdist_track
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    let meshProd : ℕ → ℝ := fun M : ℕ =>
      (widthSeq C M : ℝ) *
        binaryEndpointAdjacentMaxWidth
          (m := uniformDoubledEndpointIndexIterate endpointStart M)
          (levels (uniformDoubledEndpointIndexIterate endpointStart M))
    let scaledRatio : ℕ → ℝ := fun M : ℕ =>
      K *
        ((widthSeq C M : ℝ) /
          (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
    have hscaled_zero :
        Tendsto scaledRatio atTop (nhds 0) := by
      dsimp [scaledRatio]
      simpa [endpointStart] using
        (tendsto_const_nhds (x := K)).mul (hwidth_ratio C hC)
    have habs_bound :
        ∀ᶠ M : ℕ in atTop, |meshProd M| ≤ scaledRatio M := by
      filter_upwards [hlinearMesh C hC] with M hmesh
      let mM : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
      let maxW : ℝ := binaryEndpointAdjacentMaxWidth (m := mM) (levels mM)
      have hwidth_nonneg : 0 ≤ (widthSeq C M : ℝ) := by
        exact_mod_cast Nat.zero_le (widthSeq C M)
      have hmaxW_nonneg : 0 ≤ maxW := by
        dsimp [maxW]
        exact binaryEndpointAdjacentMaxWidth_nonneg
          ((hoptimal mM).1)
      have hprod_nonneg : 0 ≤ meshProd M := by
        dsimp [meshProd, maxW, mM]
        exact mul_nonneg hwidth_nonneg hmaxW_nonneg
      have hmul :
          (widthSeq C M : ℝ) * maxW ≤
            (widthSeq C M : ℝ) *
              (K / (((mM + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (by simpa [endpointStart, mM, maxW] using hmesh)
          hwidth_nonneg
      have htarget :
          meshProd M ≤ scaledRatio M := by
        dsimp [meshProd, scaledRatio, maxW, mM]
        calc
          (widthSeq C M : ℝ) *
              binaryEndpointAdjacentMaxWidth (m := mM) (levels mM)
              ≤ (widthSeq C M : ℝ) *
                  (K / (((mM + 1 : ℕ) : ℝ))) := by
                simpa [maxW] using hmul
          _ = K * ((widthSeq C M : ℝ) / (((mM + 1 : ℕ) : ℝ))) := by
                ring
      simpa [abs_of_nonneg hprod_nonneg] using htarget
    have hzero :=
      AppliedModelingLib.Math.TendsToZero_of_eventually_abs_le_tendsto_zero
        meshProd scaledRatio hscaled_zero habs_bound
    simpa [AppliedModelingLib.Math.TendsToZero, meshProd, endpointStart] using hzero
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    exact
      (eventually_width_le_endpoint_add_one_of_div_tendsto_zero
        (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
        (widthSeq C)
        (by simpa [endpointStart] using hwidth_ratio C hC))

/--
Geometric-mesh version of the quantile-floor B.1 bridge.  The C.5 refinement
recurrence gives a per-dyadic-subsequence linear mesh bound for uniform
optimal endpoint levels, so the source only needs a selected old-grid window
whose width is sublinear in the old endpoint count.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_geometric_mesh
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (BSeq widthSeq : ℕ → ℕ → ℕ)
    (hwidth_ratio :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (widthSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
                ℝ)))
          atTop (nhds 0))
    (hwidth_absorb :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M)
    (hdist_track :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_mesh_width
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hquantile_range hlimit_range BSeq widthSeq ?_
      hwidth_absorb ?_ hdist_track
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    let anchorObjective : ℝ :=
      binaryEndpointAwareAdjacentRateObjective
        (levels endpointStart) (fun _ : Fin (endpointStart + 2) => (1 : ℝ))
    let anchorConstant : ℝ :=
      (((endpointStart + 1 : ℕ) : ℝ)) * (anchorObjective + 1)
    let meshProd : ℕ → ℝ := fun M : ℕ =>
      (widthSeq C M : ℝ) *
        binaryEndpointAdjacentMaxWidth
          (m := uniformDoubledEndpointIndexIterate endpointStart M)
          (levels (uniformDoubledEndpointIndexIterate endpointStart M))
    let scaledRatio : ℕ → ℝ := fun M : ℕ =>
      anchorConstant *
        ((widthSeq C M : ℝ) /
          (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
    have hscaled_zero :
        Tendsto scaledRatio atTop (nhds 0) := by
      dsimp [scaledRatio]
      simpa [endpointStart] using
        (tendsto_const_nhds (x := anchorConstant)).mul
          (hwidth_ratio C hC)
    have habs_bound :
        ∀ᶠ M : ℕ in atTop, |meshProd M| ≤ scaledRatio M := by
      filter_upwards with M
      let mM : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
      let maxW : ℝ := binaryEndpointAdjacentMaxWidth (m := mM) (levels mM)
      have hwidth_nonneg : 0 ≤ (widthSeq C M : ℝ) := by
        exact_mod_cast Nat.zero_le (widthSeq C M)
      have hmaxW_nonneg : 0 ≤ maxW := by
        dsimp [maxW]
        exact binaryEndpointAdjacentMaxWidth_nonneg ((hoptimal mM).1)
      have hprod_nonneg : 0 ≤ meshProd M := by
        dsimp [meshProd, maxW, mM]
        exact mul_nonneg hwidth_nonneg hmaxW_nonneg
      have hmesh :
          maxW ≤
            anchorConstant /
              (((mM + 1 : ℕ) : ℝ)) := by
        dsimp [maxW, anchorConstant, anchorObjective, mM]
        simpa [endpointStart] using
          uniformEqualizedLevelSequence_iterated_maxWidth_le_start_objective_add_one_div
            levels
            (fun m => (hoptimal m).1)
            (fun m =>
              binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
                (hoptimal m))
            hendpointStart_pos M
      have hmul :
          (widthSeq C M : ℝ) * maxW ≤
            (widthSeq C M : ℝ) *
              (anchorConstant / (((mM + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hmesh hwidth_nonneg
      have htarget :
          meshProd M ≤ scaledRatio M := by
        dsimp [meshProd, scaledRatio, maxW, mM]
        calc
          (widthSeq C M : ℝ) *
              binaryEndpointAdjacentMaxWidth (m := mM) (levels mM)
              ≤ (widthSeq C M : ℝ) *
                  (anchorConstant / (((mM + 1 : ℕ) : ℝ))) := by
                simpa [maxW] using hmul
          _ =
              anchorConstant *
                ((widthSeq C M : ℝ) / (((mM + 1 : ℕ) : ℝ))) := by
                ring
      simpa [abs_of_nonneg hprod_nonneg] using htarget
    have hzero :=
      AppliedModelingLib.Math.TendsToZero_of_eventually_abs_le_tendsto_zero
        meshProd scaledRatio hscaled_zero habs_bound
    simpa [AppliedModelingLib.Math.TendsToZero, meshProd, endpointStart] using hzero
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    exact
      (eventually_width_le_endpoint_add_one_of_div_tendsto_zero
        (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
        (widthSeq C)
        (by simpa [endpointStart] using hwidth_ratio C hC))

/--
General-limit B.1 bridge from the paper's quantile-floor selector convention
and a variable dyadic tracking envelope.  The envelope supplies the common
source-coordinate window, while the sub-square-root block-width rate supplies
the Cauchy mesh condition through the quantitative C.2 max-gap bound.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_subsqrt
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (BSeq widthSeq : ℕ → ℕ → ℕ)
    (hwidthSqRate :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            ((widthSeq C M : ℝ) ^ 2) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
          atTop (nhds 0))
    (hwidth_absorb :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M)
    (hdist_track :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_block_window_subsqrt
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      widthSeq hwidthSqRate ?_ ?_
  · intro C hC
    filter_upwards [hwidth_absorb C hC] with M hM
    omega
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    refine
      uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_variable_bounded_error
        levelIndex hendpointStart (BSeq C) (widthSeq C)
        (hwidth_absorb C hC)
        (by
          have hlarge :=
            eventually_width_le_endpoint_add_one_of_sq_div_tendsto_zero
              (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
              (widthSeq C)
              (by simpa [endpointStart] using hwidthSqRate C hC)
          simpa [endpointStart] using hlarge)
        ?_
    filter_upwards [hdist_track C hC] with M hM
    intro N hN θ hθ
    let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
    let scale : ℕ := 2 ^ (N - M)
    have hold_eq :
        levelIndex mOld θ =
          clampedFloorLevelIndex mOld (quantileSeq (mOld + 2) θ) := by
      apply Fin.ext
      rw [hlevelIndex_val mOld θ hθ, clampedFloorLevelIndex_val]
    have href_eq :
        levelIndex mRef θ =
          clampedFloorLevelIndex mRef (quantileSeq (mRef + 2) θ) := by
      apply Fin.ext
      rw [hlevelIndex_val mRef θ hθ, clampedFloorLevelIndex_val]
    rcases hM N hN θ hθ with ⟨hold_dist, href_dist⟩
    refine ⟨quantileLimit θ, hlimit_range θ hθ, ?_, ?_, ?_, ?_⟩
    · have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mOld (BSeq C M) (hquantile_range mOld θ hθ).1 hold_dist
      simpa [mOld, hold_eq] using hfloor
    · have hold_dist_sym :
          dist (quantileSeq (mOld + 2) θ) (quantileLimit θ) ≤
            (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
        simpa [dist_comm, mOld] using hold_dist
      have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mOld (BSeq C M) (hlimit_range θ hθ).1 hold_dist_sym
      simpa [mOld, hold_eq] using hfloor
    · have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mRef (scale * BSeq C M) (hquantile_range mRef θ hθ).1
          (by simpa [mRef, scale] using href_dist)
      simpa [mRef, scale, href_eq] using hfloor
    · have href_dist_sym :
          dist (quantileSeq (mRef + 2) θ) (quantileLimit θ) ≤
            ((scale * BSeq C M : ℕ) : ℝ) / (((mRef + 2 : ℕ) : ℝ)) := by
        simpa [dist_comm, mRef, scale] using href_dist
      have hfloor :=
        clampedFloorLevelIndex_le_add_of_dist_le_div
          mRef (scale * BSeq C M) (hlimit_range θ hθ).1 href_dist_sym
      simpa [mRef, scale, href_eq] using hfloor

/--
General-limit B.1 source-index bridge for optimal uniform endpoint chains and
a non-equispaced metric scaled block window.  Finite optimality supplies
equalized rates; the source supplies shrinking actual endpoint spans for the
old blocks that contain the old and refined selectors.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_metric_block_window
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (widthSeq : ℕ → ℕ → ℕ) (blockWidth : ℕ → ℕ → ℝ)
    (hblockWidth :
      ∀ C : ℕ, 0 < C →
        Tendsto (blockWidth C) atTop (nhds 0))
    (hblockWidth_nonneg :
      ∀ C : ℕ, 0 < C → ∀ M : ℕ, 0 ≤ blockWidth C M)
    (hwidth :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 ≤ widthSeq C M)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                levels (uniformDoubledEndpointIndexIterate endpointStart M)
                    ⟨i + widthSeq C M, by omega⟩ -
                  levels (uniformDoubledEndpointIndexIterate endpointStart M)
                    ⟨i, by omega⟩ ≤ blockWidth C M ∧
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_metric_block_window
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    widthSeq blockWidth hblockWidth hblockWidth_nonneg hwidth hwindow

/--
Theorem B.1 source-index bridge from a common floor-coordinate convention.
This is the form closest to the source proof: once each positive dyadic tail
shares a coordinate whose clamped floor selects both the anchor and refined
levels, the scaled-window bridge above supplies the full B.1 subsequence
principle.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart M) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart N) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_scaled_index_window
    betaSeq quantileSeq levels levelIndex hrepr hlevels heq
    (fun C hC =>
      uniformDoubledEndpointIndexIterate_eventually_scaled_index_window_of_common_floor_coordinate
        levelIndex (by omega : 0 < 2 * C - 1)
        (by simpa using hcommon C hC))

/--
General-limit B.1 bridge from the source common floor-coordinate convention.
The conclusion is independent of the identity limit used in the equispaced
special case.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_common_floor_coordinate
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart M) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart N) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_index_window
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr hlevels heq
    (fun C hC =>
      uniformDoubledEndpointIndexIterate_eventually_scaled_index_window_of_common_floor_coordinate
        levelIndex (by omega : 0 < 2 * C - 1)
        (by simpa using hcommon C hC))

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains.  Finite
optimality supplies equalized adjacent rates, while the source common
floor-coordinate invariant supplies the dyadic selector tracking used by the
Cauchy proof.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart M) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart N) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate
    betaSeq quantileSeq levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hcommon

/--
General-limit B.1 bridge for optimal uniform endpoint chains.  Finite
optimality supplies equalized adjacent rates, and the common floor-coordinate
invariant gives the dyadic selector tracking; the quantile maps may converge
uniformly to an arbitrary limit.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_common_floor_coordinate
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart M) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart N) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_common_floor_coordinate
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hcommon

/--
Theorem B.1 source-index bridge from a bounded-error common floor-coordinate
convention.  This weakens the exact common-coordinate selector above: the source
selector may be within `B` old cells of a common clamped-floor coordinate, and
within the dyadically scaled error at the refined level.  The fixed block width
`width` absorbs the two exact clamped-floor cells and the two error margins.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 + B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 + 2 ^ (N - M) * B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_scaled_block_window
    betaSeq quantileSeq levels levelIndex hrepr hlevels heq width (by omega)
    (fun C hC =>
      uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_bounded_error
        levelIndex (by omega : 0 < 2 * C - 1) hwidth
        (by simpa using hcommon C hC))

/--
General-limit B.1 bridge from a bounded-error common floor-coordinate
convention.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_common_floor_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 + B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 + 2 ^ (N - M) * B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr hlevels heq
    width (by omega)
    (fun C hC =>
      uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_bounded_error
        levelIndex (by omega : 0 < 2 * C - 1) hwidth
        (by simpa using hcommon C hC))

/--
Optimal-endpoint version of the bounded-error common floor-coordinate bridge.
Finite uniform optimality supplies the equalized adjacent-rate hypothesis.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 + B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 + 2 ^ (N - M) * B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_bounded_error
    betaSeq quantileSeq levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    B width hwidth hcommon

/--
Theorem B.1 source-index bridge from a global source-coordinate selector.
This packages the common floor-coordinate convention in the form used by
piecewise-constant source models: for every source type, one coordinate
selects the same clamped floor endpoint at every dyadic refinement depth.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_map
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hlevelIndex :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        levelIndex m θ = clampedFloorLevelIndex m (sourceCoord θ)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate
      betaSeq quantileSeq levels levelIndex hrepr hlevels heq ?_
  intro C _hC
  filter_upwards with M
  intro N _hN θ hθ
  refine ⟨sourceCoord θ, hcoord_range θ hθ, ?_, ?_⟩
  · exact hlevelIndex (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ hθ
  · exact hlevelIndex (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ hθ

/--
Theorem B.1 source floor-selector convention.  The source proof follows one
coordinate `x_θ` through the dyadic refinement tail; in Lean this is represented
by saying that every source level selector is the clamped floor selector of a
single source-coordinate map.
-/
def theoremB1SourceFloorSelectorConvention
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ) : Prop :=
  ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    levelIndex m θ = clampedFloorLevelIndex m (sourceCoord θ)

/--
Value-form normalization for the B.1 source floor-selector convention.  This is
the form closest to the paper's interval-index notation: the selected source
interval has index `floor((m+2) x_θ)`, clamped at the right endpoint.
-/
theorem theoremB1SourceFloorSelectorConvention_of_floor_value
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * sourceCoord θ)) (m + 1)) :
    theoremB1SourceFloorSelectorConvention levelIndex sourceCoord :=
  clampedFloorLevelIndex_eq_of_val_eq levelIndex sourceCoord hlevelIndex_val

/--
Theorem B.1 source-convention bridge.  Once the source floor-selector convention
is named explicitly, the common-coordinate proof above gives the full B.1
dyadic subsequence principle under uniform equalized endpoint levels.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_source_floor_selector_convention
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hsource :
      theoremB1SourceFloorSelectorConvention levelIndex sourceCoord) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_map
    betaSeq quantileSeq levels levelIndex sourceCoord hrepr hlevels heq
    hcoord_range hsource

/--
Theorem B.1 source-convention bridge for optimal endpoint chains.  Finite
optimality gives the equalized-rate hypothesis; the named source floor-selector
convention supplies the dyadic selector tracking used by the source proof.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_source_floor_selector_convention
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hsource :
      theoremB1SourceFloorSelectorConvention levelIndex sourceCoord) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_source_floor_selector_convention
    betaSeq quantileSeq levels levelIndex sourceCoord hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hcoord_range hsource

/--
Theorem B.1 bridge from a source floor-value selector formula.  This is the
same common-coordinate theorem as above, but callers can provide the natural
source statement for the selected interval index as a value equality.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_floor_value_selector
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * sourceCoord θ)) (m + 1)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  exact
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_map
      betaSeq quantileSeq levels levelIndex sourceCoord hrepr hlevels heq
      hcoord_range
      (theoremB1SourceFloorSelectorConvention_of_floor_value levelIndex sourceCoord
        hlevelIndex_val)

/--
Theorem B.1 bridge for the equispaced source convention `x_θ = θ`.  The
source selector only needs to expose the clamped floor-index value formula.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_identity_floor_value_selector
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * θ)) (m + 1)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  exact
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_floor_value_selector
      betaSeq quantileSeq levels levelIndex (fun θ : ℝ => θ) hrepr
      hlevels heq (fun _θ hθ => hθ) hlevelIndex_val

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains.  If the
source beta sequence is represented by endpoint levels that maximize the
finite uniform adjacent-rate objective, and if the source selector follows one
global clamped floor coordinate through all dyadic refinements, then the B.1
dyadic subsequence principle follows.  The finite Lemma 3.1 optimizer theorem
derives the equalized-rate input consumed by the common-floor bridge.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate_map
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hlevelIndex :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        levelIndex m θ = clampedFloorLevelIndex m (sourceCoord θ)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_map
      betaSeq quantileSeq levels levelIndex sourceCoord hrepr
      (fun m => (hoptimal m).1) ?_ hcoord_range hlevelIndex
  intro m
  exact binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
    (hoptimal m)

/--
Theorem B.1 bridge from source optimal endpoint chains and a source
floor-value selector formula.  Finite optimality gives equalized adjacent
rates, and the value formula normalizes the source interval selector to the
canonical common-floor selector.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_floor_value_selector
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * sourceCoord θ)) (m + 1)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  exact
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate_map
      betaSeq quantileSeq levels levelIndex sourceCoord hrepr hoptimal
      hcoord_range
      (theoremB1SourceFloorSelectorConvention_of_floor_value levelIndex sourceCoord
        hlevelIndex_val)

/--
Theorem B.1 bridge for source-optimal endpoint chains under the equispaced
source convention `x_θ = θ`.  Finite optimality supplies equalized rates, and
the source selector only needs to expose its floor-index value formula.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_identity_floor_value_selector
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * θ)) (m + 1)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  exact
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_floor_value_selector
      betaSeq quantileSeq levels levelIndex (fun θ : ℝ => θ) hrepr
      hoptimal (fun _θ hθ => hθ) hlevelIndex_val

/--
Theorem B.1 bridge with the source's quantile-index selector convention.  The
selector for `β_M(θ)` is the clamped floor of the paper quantile map `q_M(θ)`.
The remaining hypothesis is the source proof's dyadic envelope: along every
positive dyadic tail, the anchor and refined quantile floors are eventually
the floors of one common coordinate `x_θ`.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_selector_common_coordinate
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ) =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ) =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate
      betaSeq quantileSeq levels levelIndex hrepr hlevels heq ?_
  intro C hC
  filter_upwards [hquantile_common C hC] with M hM
  intro N hN θ hθ
  rcases hM N hN θ hθ with ⟨x, hx, hold, href⟩
  refine ⟨x, hx, ?_, ?_⟩
  · apply Fin.ext
    rw [hlevelIndex_val
      (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ hθ]
    rw [clampedFloorLevelIndex_val]
    exact congrArg Fin.val hold
  · apply Fin.ext
    rw [hlevelIndex_val
      (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ hθ]
    rw [clampedFloorLevelIndex_val]
    exact congrArg Fin.val href

/--
Optimal-endpoint version of the B.1 quantile-floor selector bridge.  Finite
uniform optimality supplies the equalized-rate hypothesis; the remaining
source-specific work is the quantile common-coordinate envelope.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_selector_common_coordinate
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ) =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ) =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_selector_common_coordinate
    betaSeq quantileSeq levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val hquantile_common

/--
Theorem B.1 bridge with the paper's quantile-index selector convention and a
bounded-error common-coordinate envelope.  This is the rate-free form of the
source proof once the required dyadic cell-width Cauchy estimate has been made
explicit: the quantile floors at the anchor and refined depths track one common
coordinate up to bounded old-grid error and its dyadic scaling.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 + 2 ^ (N - M) * B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_bounded_error
      betaSeq quantileSeq levels levelIndex hrepr hlevels heq B width hwidth ?_
  intro C hC
  filter_upwards [hquantile_common C hC] with M hM
  intro N hN θ hθ
  rcases hM N hN θ hθ with
    ⟨x, hx, hold_lo, hold_hi, href_lo, href_hi⟩
  refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ hθ]
      using hold_lo
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ hθ]
      using hold_hi
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ hθ]
      using href_lo
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ hθ]
      using href_hi

/--
General-limit B.1 bridge with the paper's quantile-index selector convention
and a bounded-error common-coordinate envelope.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 + 2 ^ (N - M) * B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_common_floor_coordinate_bounded_error
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hlevels heq
      B width hwidth ?_
  intro C hC
  filter_upwards [hquantile_common C hC] with M hM
  intro N hN θ hθ
  rcases hM N hN θ hθ with
    ⟨x, hx, hold_lo, hold_hi, href_lo, href_hi⟩
  refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ hθ]
      using hold_lo
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ hθ]
      using hold_hi
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ hθ]
      using href_lo
  · simpa [clampedFloorLevelIndex_val,
      hlevelIndex_val (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ hθ]
      using href_hi

/--
Optimal-endpoint version of the quantile-floor bounded-error B.1 bridge.
Finite uniform optimality supplies the equalized-rate hypothesis.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 + 2 ^ (N - M) * B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
    betaSeq quantileSeq levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val B width hwidth hquantile_common

/--
General-limit optimal-endpoint version of the quantile-floor bounded-error
B.1 bridge.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 + 2 ^ (N - M) * B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (quantileSeq
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val B width hwidth hquantile_common

/--
General-limit B.1 bridge from a finite coarse-cell uniqueness premise.  If,
eventually along every dyadic tail, the refined quantile and anchor quantile
fall in the same old clamped-floor cell, the bounded common-coordinate bridge
applies with zero error.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_finite_coarse_cell
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hcoarse_cell :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart M)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart M)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val 0 2 (by omega) ?_
  intro C hC
  filter_upwards [hcoarse_cell C hC] with M hM
  intro N hN θ hθ
  let endpointStart : ℕ := 2 * C - 1
  let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
  let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
  let x : ℝ := quantileSeq (mRef + 2) θ
  have hx_range : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [x, mRef] using hquantile_range mRef θ hθ
  have hsame :
      (clampedFloorLevelIndex mOld x).1 =
        (clampedFloorLevelIndex mOld (quantileSeq (mOld + 2) θ)).1 := by
    simpa [endpointStart, mOld, mRef, x] using
      congrArg Fin.val (hM N hN θ hθ)
  refine ⟨x, hx_range, ?_, ?_, ?_, ?_⟩
  · have hle :
        (clampedFloorLevelIndex mOld x).1 ≤
          (clampedFloorLevelIndex mOld (quantileSeq (mOld + 2) θ)).1 + 0 := by
        rw [hsame]
        omega
    simpa [endpointStart, mOld, x] using hle
  · have hle :
        (clampedFloorLevelIndex mOld (quantileSeq (mOld + 2) θ)).1 ≤
          (clampedFloorLevelIndex mOld x).1 + 0 := by
        rw [hsame]
        omega
    simpa [endpointStart, mOld, x] using hle
  · have hle :
        (clampedFloorLevelIndex mRef x).1 ≤
          (clampedFloorLevelIndex mRef (quantileSeq (mRef + 2) θ)).1 +
            2 ^ (N - M) * 0 := by
        dsimp [x]
        omega
    simpa [endpointStart, mRef, x] using hle
  · have hle :
        (clampedFloorLevelIndex mRef (quantileSeq (mRef + 2) θ)).1 ≤
          (clampedFloorLevelIndex mRef x).1 + 2 ^ (N - M) * 0 := by
        dsimp [x]
        omega
    simpa [endpointStart, mRef, x] using hle

/--
General-limit B.1 bridge from raw anchor/tail quantile-distance control.  For
each dyadic source tail, if the tail quantile coordinate is eventually close
to the anchor quantile coordinate at the refined floor-selector scale, then
the bounded-error C.5 bridge supplies the B.1 subsequential limit.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_eventual_anchor_dist
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hanchor_dist :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (quantileSeq
                  (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                  θ)
                (quantileSeq
                  (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                  θ) ≤
                ((2 ^ (N - M) * B : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) :
                    ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hlevels heq
      hlevelIndex_val B width hwidth ?_
  intro C hC
  filter_upwards [hanchor_dist C hC] with M hM
  intro N hN θ hθ
  let endpointStart : ℕ := 2 * C - 1
  let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
  let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
  let x : ℝ := quantileSeq (mOld + 2) θ
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [x, mOld, endpointStart] using hquantile_range mOld θ hθ
  have href_range :
      quantileSeq (mRef + 2) θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [mRef, endpointStart] using hquantile_range mRef θ hθ
  have hdist :
      dist x (quantileSeq (mRef + 2) θ) ≤
        ((2 ^ (N - M) * B : ℕ) : ℝ) / (((mRef + 2 : ℕ) : ℝ)) := by
    simpa [x, mOld, mRef, endpointStart] using hM N hN θ hθ
  refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _
  · exact
      clampedFloorLevelIndex_le_add_of_dist_le_div mRef
        (2 ^ (N - M) * B) href_range.1 hdist
  · have hdist_sym :
        dist (quantileSeq (mRef + 2) θ) x ≤
          ((2 ^ (N - M) * B : ℕ) : ℝ) /
            (((mRef + 2 : ℕ) : ℝ)) := by
      simpa [dist_comm] using hdist
    exact
      clampedFloorLevelIndex_le_add_of_dist_le_div mRef
        (2 ^ (N - M) * B) hx.1 hdist_sym

/--
Optimal-endpoint version of the anchor/tail quantile-distance B.1 bridge.
Finite uniform optimality supplies the equalized-rate hypothesis.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_eventual_anchor_dist
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hanchor_dist :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (quantileSeq
                  (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                  θ)
                (quantileSeq
                  (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                  θ) ≤
                ((2 ^ (N - M) * B : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) :
                    ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_eventual_anchor_dist
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val hquantile_range B width hwidth hanchor_dist

/--
Theorem B.1 bridge with the paper's quantile-index selector convention and a
global bounded floor-tracking premise.  A single eventual source-coordinate
estimate supplies the dyadic bounded-error common-coordinate envelope used by
the preceding bridge.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_global_floor_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hfloor_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          (clampedFloorLevelIndex m (sourceCoord θ)).1 ≤
            (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 + B ∧
          (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 ≤
            (clampedFloorLevelIndex m (sourceCoord θ)).1 + B) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
      betaSeq quantileSeq levels levelIndex hrepr hlevels heq
      hlevelIndex_val B width hwidth ?_
  rw [Filter.eventually_atTop] at hfloor_track
  rcases hfloor_track with ⟨threshold, htrack⟩
  intro C hC
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart_pos : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  have htend :=
    uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
      hendpointStart_pos
  rw [Filter.tendsto_atTop] at htend
  have hlarge :
      ∀ᶠ M : ℕ in atTop,
        threshold ≤ uniformDoubledEndpointIndexIterate endpointStart M :=
    htend threshold
  filter_upwards [hlarge] with M hM
  intro N hN θ hθ
  let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
  let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
  have hmOld_ge : threshold ≤ mOld := by
    exact hM
  have hcomp :
      uniformDoubledEndpointIndexIterate mOld (N - M) = mRef := by
    dsimp [mOld, mRef]
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have hmOld_le_ref : mOld ≤ mRef := by
    rw [← hcomp]
    exact uniformDoubledEndpointIndexIterate_self_le mOld (N - M)
  have hmRef_ge : threshold ≤ mRef := hmOld_ge.trans hmOld_le_ref
  rcases htrack mOld hmOld_ge θ hθ with ⟨hold_lo, hold_hi⟩
  rcases htrack mRef hmRef_ge θ hθ with ⟨href_lo, href_hi⟩
  have hpow_pos : 0 < 2 ^ (N - M) :=
    Nat.pow_pos (by norm_num : 0 < (2 : ℕ))
  have hB_le_scaled : B ≤ 2 ^ (N - M) * B :=
    Nat.le_mul_of_pos_left B hpow_pos
  refine ⟨sourceCoord θ, hcoord_range θ hθ, ?_, ?_, ?_, ?_⟩
  · simpa [endpointStart, mOld] using hold_lo
  · simpa [endpointStart, mOld] using hold_hi
  · exact href_lo.trans (Nat.add_le_add_left hB_le_scaled _)
  · exact href_hi.trans (Nat.add_le_add_left hB_le_scaled _)

/--
General-limit B.1 bridge with the paper's quantile-index selector convention
and a global bounded floor-tracking premise.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_global_floor_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hfloor_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          (clampedFloorLevelIndex m (sourceCoord θ)).1 ≤
            (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 + B ∧
          (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 ≤
            (clampedFloorLevelIndex m (sourceCoord θ)).1 + B) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_selector_common_coordinate_bounded_error
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hlevels heq
      hlevelIndex_val B width hwidth ?_
  rw [Filter.eventually_atTop] at hfloor_track
  rcases hfloor_track with ⟨threshold, htrack⟩
  intro C hC
  let endpointStart : ℕ := 2 * C - 1
  have hendpointStart_pos : 0 < endpointStart := by
    dsimp [endpointStart]
    omega
  have htend :=
    uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
      hendpointStart_pos
  rw [Filter.tendsto_atTop] at htend
  have hlarge :
      ∀ᶠ M : ℕ in atTop,
        threshold ≤ uniformDoubledEndpointIndexIterate endpointStart M :=
    htend threshold
  filter_upwards [hlarge] with M hM
  intro N hN θ hθ
  let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
  let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
  have hmOld_ge : threshold ≤ mOld := by
    exact hM
  have hcomp :
      uniformDoubledEndpointIndexIterate mOld (N - M) = mRef := by
    dsimp [mOld, mRef]
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hN]
  have hmOld_le_ref : mOld ≤ mRef := by
    rw [← hcomp]
    exact uniformDoubledEndpointIndexIterate_self_le mOld (N - M)
  have hmRef_ge : threshold ≤ mRef := hmOld_ge.trans hmOld_le_ref
  rcases htrack mOld hmOld_ge θ hθ with ⟨hold_lo, hold_hi⟩
  rcases htrack mRef hmRef_ge θ hθ with ⟨href_lo, href_hi⟩
  have hpow_pos : 0 < 2 ^ (N - M) :=
    Nat.pow_pos (by norm_num : 0 < (2 : ℕ))
  have hB_le_scaled : B ≤ 2 ^ (N - M) * B :=
    Nat.le_mul_of_pos_left B hpow_pos
  refine ⟨sourceCoord θ, hcoord_range θ hθ, ?_, ?_, ?_, ?_⟩
  · simpa [endpointStart, mOld] using hold_lo
  · simpa [endpointStart, mOld] using hold_hi
  · exact href_lo.trans (Nat.add_le_add_left hB_le_scaled _)
  · exact href_hi.trans (Nat.add_le_add_left hB_le_scaled _)

/--
Optimal-endpoint version of the global floor-tracking B.1 bridge.  Finite
uniform optimality supplies the equalized-rate hypothesis; the remaining input
is the source-coordinate floor-tracking estimate.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_global_floor_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hfloor_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          (clampedFloorLevelIndex m (sourceCoord θ)).1 ≤
            (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 + B ∧
          (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 ≤
            (clampedFloorLevelIndex m (sourceCoord θ)).1 + B) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_global_floor_tracking
    betaSeq quantileSeq levels levelIndex sourceCoord hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val hcoord_range B width hwidth hfloor_track

/--
General-limit optimal-endpoint version of the global floor-tracking B.1
bridge.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_global_floor_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hfloor_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          (clampedFloorLevelIndex m (sourceCoord θ)).1 ≤
            (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 + B ∧
          (clampedFloorLevelIndex m (quantileSeq (m + 2) θ)).1 ≤
            (clampedFloorLevelIndex m (sourceCoord θ)).1 + B) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_global_floor_tracking
    betaSeq quantileSeq quantileLimit levels levelIndex sourceCoord hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val hcoord_range B width hwidth hfloor_track

/--
Theorem B.1 bridge with the paper's quantile-index selector convention and a
real-valued global tracking premise.  If the source coordinate and quantile
coordinate are eventually within `B/(m+2)`, the clamped floor selector
condition follows from floor-index stability.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_global_dist_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (sourceCoord θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_global_floor_tracking
      betaSeq quantileSeq levels levelIndex sourceCoord hrepr hlevels heq
      hlevelIndex_val hcoord_range B width hwidth ?_
  filter_upwards [hdist_track] with m hm
  intro θ hθ
  have hdist := hm θ hθ
  constructor
  · exact
      clampedFloorLevelIndex_le_add_of_dist_le_div m B
        (hquantile_range m θ hθ).1 hdist
  · have hdist_sym :
        dist (quantileSeq (m + 2) θ) (sourceCoord θ) ≤
          (B : ℝ) / (((m + 2 : ℕ) : ℝ)) := by
      simpa [dist_comm] using hdist
    exact
      clampedFloorLevelIndex_le_add_of_dist_le_div m B
        (hcoord_range θ hθ).1 hdist_sym

/--
Optimal-endpoint version of the real-valued global tracking B.1 bridge.
Finite uniform optimality supplies the equalized-rate hypothesis.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_global_dist_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (sourceCoord θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_quantile_floor_global_dist_tracking
    betaSeq quantileSeq levels levelIndex sourceCoord hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val hcoord_range hquantile_range B width hwidth hdist_track

/--
General-limit B.1 bridge with the paper's quantile-index selector convention
and a real-valued global tracking premise.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_global_dist_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (sourceCoord θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_global_floor_tracking
      betaSeq quantileSeq quantileLimit levels levelIndex sourceCoord hrepr
      hlevels heq hlevelIndex_val hcoord_range B width hwidth ?_
  filter_upwards [hdist_track] with m hm
  intro θ hθ
  have hdist := hm θ hθ
  constructor
  · exact
      clampedFloorLevelIndex_le_add_of_dist_le_div m B
        (hquantile_range m θ hθ).1 hdist
  · have hdist_sym :
        dist (quantileSeq (m + 2) θ) (sourceCoord θ) ≤
          (B : ℝ) / (((m + 2 : ℕ) : ℝ)) := by
      simpa [dist_comm] using hdist
    exact
      clampedFloorLevelIndex_le_add_of_dist_le_div m B
        (hcoord_range θ hθ).1 hdist_sym

/--
General-limit optimal-endpoint version of the real-valued global tracking B.1
bridge.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_global_dist_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (sourceCoord θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_quantile_floor_global_dist_tracking
    betaSeq quantileSeq quantileLimit levels levelIndex sourceCoord hrepr
    (fun m => (hoptimal m).1)
    (fun m =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal m))
    hlevelIndex_val hcoord_range hquantile_range B width hwidth hdist_track

/--
General-limit optimal-endpoint B.1 bridge from quantitative convergence of the
paper quantile maps to their limiting source coordinate.  This is the
source-natural specialization of the global-distance tracking theorem: the
source coordinate used by the selector proof is exactly `quantileLimit`, and
the additional source regularity is the explicit `O(1/m)` tracking estimate
needed to keep the clamped floor selectors in a bounded dyadic envelope.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_global_dist_tracking
    betaSeq quantileSeq quantileLimit levels levelIndex quantileLimit hrepr
    hoptimal hlevelIndex_val hlimit_range hquantile_range B width hwidth
    hdist_track

/--
Same B.1 limit-tracking bridge, but with the limiting-coordinate range derived
from the theorem's uniform convergence hypothesis and the finite quantile-map
range.  Thus the remaining quantitative source input is the actual `O(1/m)`
selector-tracking estimate.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking_of_quantile_range
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro hquantile
  have hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1 :=
    theoremB1_quantileLimit_mem_Icc_of_tendstoUniformlyOn_shift
      quantileSeq quantileLimit hquantile hquantile_range
  exact
    (theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hlimit_range hquantile_range B width hwidth
      hdist_track) hquantile

/--
B.1 limit-tracking bridge with both auxiliary range and width bookkeeping
discharged.  The source-facing inputs are the finite quantile-map range and a
single bounded `O(1/m)` selector-tracking constant.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking_clean
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B : ℕ)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking_of_quantile_range
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
    hlevelIndex_val hquantile_range B (2 + 2 * B) le_rfl hdist_track

/--
Source convention that makes the arbitrary-selector B.1 bridge source-facing:
finite optimal endpoint levels are represented by a quantile-floor selector,
and a single source coordinate tracks the interval-quantile coordinate to
`O(1/m)`.  This is the formal version of the paper proof's common
`x_θ`/selector-coherence assumption.
-/
structure TheoremB1OptimalQuantileFloorGlobalDistTrackingConvention
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2)) : Type where
  sourceCoord : ℝ → ℝ
  hrepr : ∀ m θ, betaSeq (m + 2) θ =
    levels m (levelIndex m θ)
  hoptimal : ∀ m : ℕ,
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun xs : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective xs
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      (levels m)
  hlevelIndex_val :
    ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
      (levelIndex m θ).1 =
        min
          (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
          (m + 1)
  hcoord_range :
    ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      sourceCoord θ ∈ Set.Icc (0 : ℝ) 1
  hquantile_range :
    ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
      quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1
  B : ℕ
  width : ℕ
  hwidth : 2 + 2 * B ≤ width
  hdist_track :
    ∀ᶠ m : ℕ in atTop,
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        dist (sourceCoord θ) (quantileSeq (m + 2) θ) ≤
          (B : ℝ) / (((m + 2 : ℕ) : ℝ))

/--
Build the named B.1 selector convention from quantitative convergence of the
paper quantile maps to their limiting coordinate.  This packages the source
assumption in the strongest currently checked form: the selector source
coordinate is the limiting quantile coordinate itself.
-/
def theoremB1OptimalQuantileFloorGlobalDistTrackingConvention_of_limit_dist_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hdist_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ) (quantileSeq (m + 2) θ) ≤
            (B : ℝ) / (((m + 2 : ℕ) : ℝ))) :
    TheoremB1OptimalQuantileFloorGlobalDistTrackingConvention
      betaSeq quantileSeq levels levelIndex where
  sourceCoord := quantileLimit
  hrepr := hrepr
  hoptimal := hoptimal
  hlevelIndex_val := hlevelIndex_val
  hcoord_range := hlimit_range
  hquantile_range := hquantile_range
  B := B
  width := width
  hwidth := hwidth
  hdist_track := hdist_track

/--
B.1 under the named global source-coordinate tracking convention.  The
quantile maps may converge uniformly to any limit; the convention supplies
the selector coherence used by the Cauchy proof.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_optimal_quantile_floor_global_dist_tracking_convention
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (H : TheoremB1OptimalQuantileFloorGlobalDistTrackingConvention
      betaSeq quantileSeq levels levelIndex) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_global_dist_tracking
    betaSeq quantileSeq quantileLimit levels levelIndex H.sourceCoord
    H.hrepr H.hoptimal H.hlevelIndex_val H.hcoord_range H.hquantile_range
    H.B H.width H.hwidth H.hdist_track

/--
Canonical source-indexed binary rule for the uniform equalized clamped-floor
convention.  The paper's source index `M` has endpoint-chain parameter
`M - 2`; for `M < 2` the definition falls back to the tiny endpoint vector and
only affects the constant `C = 0` subsequence.
-/
noncomputable def canonicalUniformEqualizedClampedFloorBetaSeq
    (M : ℕ) (θ : ℝ) : ℝ :=
  canonicalUniformEqualizedEndpointLevels (M - 2)
    (clampedFloorLevelIndex (M - 2) θ)

theorem canonicalUniformEqualizedClampedFloorBetaSeq_repr
    (m : ℕ) (θ : ℝ) :
    canonicalUniformEqualizedClampedFloorBetaSeq (m + 2) θ =
      canonicalUniformEqualizedEndpointLevels m
        (clampedFloorLevelIndex m θ) := by
  unfold canonicalUniformEqualizedClampedFloorBetaSeq
  have hidx : m + 2 - 2 = m := by omega
  cases hidx
  rfl

/--
Theorem B.1 with the uniform equalized clamped-floor source convention
discharged: the canonical sequence has uniformly convergent dyadic
subsequences.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_equalized_clampedFloor :
    theoremB1UniformOptimalSubsequencePrinciple
      canonicalUniformEqualizedClampedFloorBetaSeq
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ) :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_clampedFloor
    canonicalUniformEqualizedClampedFloorBetaSeq
    (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
    canonicalUniformEqualizedEndpointLevels
    canonicalUniformEqualizedClampedFloorBetaSeq_repr
    canonicalUniformEqualizedEndpointLevels_levelVector
    canonicalUniformEqualizedEndpointLevels_equalizes_uniform

/--
Theorem B.1 representative-transfer bridge. If a reference representative
already has uniformly convergent dyadic subsequences, then any beta sequence
that is eventually pointwise equal to it on `[0,1]` has the same B.1 dyadic
compactness conclusion. This applies equally to equispaced and non-equispaced
reference representatives; it is still stronger than an a.e. equality because
B.1 is a uniform source-coordinate statement.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq
    (betaSeq referenceSeq : ℕ → ℝ → ℝ)
    (href : theoremB1DyadicSubsequenceUniformConvergence referenceSeq)
    (heq :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          betaSeq M θ = referenceSeq M θ) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  by_cases hC : 0 < C
  · rcases href C with ⟨betaLimit, hreference⟩
    refine ⟨betaLimit, ?_⟩
    refine
      AppliedModelingLib.Math.tendstoUniformlyOn_of_tendstoUniformlyOn_of_eventual_dist_le
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        (fun N : ℕ => fun θ : ℝ =>
          referenceSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit (Set.Icc (0 : ℝ) 1) (fun _ : ℕ => (0 : ℝ))
        hreference tendsto_const_nhds ?_
    have hsubseq_eq :
        ∀ᶠ N : ℕ in atTop,
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            betaSeq (theoremB1SubsequenceIndex C N) θ =
              referenceSeq (theoremB1SubsequenceIndex C N) θ :=
      (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC).eventually heq
    filter_upwards [hsubseq_eq] with N hN θ hθ
    rw [hN θ hθ]
    simp
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
General-limit B.1 representative-transfer bridge. Once a reference
representative satisfies the source-facing B.1 principle for a quantile limit,
any eventually pointwise equal source representative satisfies the same
principle.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_eq
    (betaSeq referenceSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (href :
      theoremB1UniformOptimalSubsequencePrincipleTo
        referenceSeq quantileSeq quantileLimit)
    (heq :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          betaSeq M θ = referenceSeq M θ) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq
      betaSeq referenceSeq (href hquantile) heq

/--
Identity-limit B.1 representative-transfer bridge, specialized to the paper's
main `theoremB1UniformOptimalSubsequencePrinciple` wrapper.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq
    (betaSeq referenceSeq quantileSeq : ℕ → ℝ → ℝ)
    (href : theoremB1UniformOptimalSubsequencePrinciple referenceSeq quantileSeq)
    (heq :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          betaSeq M θ = referenceSeq M θ) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq
      betaSeq referenceSeq (href hquantile) heq

/--
Theorem B.1 transfer from the canonical uniform equalized clamped-floor
representative. If a source representative is eventually pointwise equal to
the canonical representative on `[0,1]`, then every dyadic source subsequence
has a uniform limit. This is stronger than an a.e. representative statement:
the B.1 conclusion is uniform in the source coordinate.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq_canonical_uniform_equalized_clampedFloor
    (betaSeq : ℕ → ℝ → ℝ)
    (heq :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          betaSeq M θ = canonicalUniformEqualizedClampedFloorBetaSeq M θ) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq
      betaSeq canonicalUniformEqualizedClampedFloorBetaSeq
      (theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_equalized_clampedFloor
        corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity)
      heq

/--
Theorem B.1 source-facing principle from eventual equality with the canonical
uniform equalized clamped-floor representative. The quantile hypothesis is
irrelevant once the beta representatives themselves have the canonical dyadic
limits.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq_canonical_uniform_equalized_clampedFloor
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (heq :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          betaSeq M θ = canonicalUniformEqualizedClampedFloorBetaSeq M θ) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  exact
    theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq
      betaSeq canonicalUniformEqualizedClampedFloorBetaSeq quantileSeq
      (fun _hquantile =>
        theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_equalized_clampedFloor
          corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity)
      heq

/--
Theorem B.1 Cauchy-completeness bridge.  Once the paper-specific dyadic
argument supplies an anchor envelope saying every tail of each subsequence is
uniformly within `mesh M` of the `M`-th anchor function, and `mesh M -> 0`,
the subsequence has a uniform limit on `[0,1]`.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_anchor_bound
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile C
  exact
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (Set.Icc (0 : ℝ) 1) mesh hmesh hmesh_nonneg
      (fun M => hanchor C M)

/--
Source-facing B.1 Cauchy-completeness bridge: an anchor envelope with mesh
going to zero gives dyadic subsequence convergence, independently of how the
quantile maps are named.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_anchor_bound
    (betaSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  exact
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (Set.Icc (0 : ℝ) 1) mesh hmesh hmesh_nonneg
      (fun M => hanchor C M)

/--
General-limit B.1 Cauchy-completeness bridge from an anchor envelope.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_anchor_bound
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_anchor_bound
      betaSeq mesh hmesh hmesh_nonneg hanchor

/--
Theorem B.1 Cauchy-completeness bridge with eventual anchors.  The source
proof only needs to provide the anchor envelope for all sufficiently large
anchors along each dyadic subsequence.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_eventually_anchor_bound
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (betaSeq (theoremB1SubsequenceIndex C N) θ)
                (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile C
  exact
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (Set.Icc (0 : ℝ) 1) mesh hmesh hmesh_nonneg
      (hanchor C)

/--
Source-facing B.1 Cauchy-completeness bridge with eventual anchors.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound
    (betaSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (betaSeq (theoremB1SubsequenceIndex C N) θ)
                (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  exact
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (Set.Icc (0 : ℝ) 1) mesh hmesh hmesh_nonneg
      (hanchor C)

/--
General-limit B.1 Cauchy-completeness bridge with eventual anchors.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_anchor_bound
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (betaSeq (theoremB1SubsequenceIndex C N) θ)
                (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound
      betaSeq mesh hmesh hmesh_nonneg hanchor

/--
Source-facing B.1 Cauchy-completeness bridge with subsequence-dependent
eventual anchors.  This is the clean value-level route for non-equispaced
selectors: for each dyadic subsequence `C`, the source proof may supply its
own shrinking bound `mesh C M`.
-/
theorem theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound_by_subsequence
    (betaSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℕ → ℝ)
    (hmesh : ∀ C : ℕ, Tendsto (mesh C) atTop (nhds 0))
    (hmesh_nonneg : ∀ C M : ℕ, 0 ≤ mesh C M)
    (hanchor :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (betaSeq (theoremB1SubsequenceIndex C N) θ)
                (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh C M) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq := by
  intro C
  exact
    AppliedModelingLib.Math.exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (Set.Icc (0 : ℝ) 1) (mesh C) (hmesh C) (hmesh_nonneg C)
      (hanchor C)

/--
Theorem B.1 with subsequence-dependent eventual anchors.  The quantile maps
are only used to match the paper's theorem statement; the convergence proof
uses the value-level anchor bounds.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_eventually_anchor_bound_by_subsequence
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℕ → ℝ)
    (hmesh : ∀ C : ℕ, Tendsto (mesh C) atTop (nhds 0))
    (hmesh_nonneg : ∀ C M : ℕ, 0 ≤ mesh C M)
    (hanchor :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (betaSeq (theoremB1SubsequenceIndex C N) θ)
                (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh C M) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound_by_subsequence
      betaSeq mesh hmesh hmesh_nonneg hanchor

/--
General-limit B.1 with subsequence-dependent eventual anchors.  This is the
minimal source-facing statement needed when the non-equispaced selector proof
can show value-level Cauchy tails directly.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_anchor_bound_by_subsequence
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (mesh : ℕ → ℕ → ℝ)
    (hmesh : ∀ C : ℕ, Tendsto (mesh C) atTop (nhds 0))
    (hmesh_nonneg : ∀ C M : ℕ, 0 ≤ mesh C M)
    (hanchor :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist
                (betaSeq (theoremB1SubsequenceIndex C N) θ)
                (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh C M) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro _hquantile
  exact
    theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound_by_subsequence
      betaSeq mesh hmesh hmesh_nonneg hanchor

/--
Theorem B.1 two-step-bracket bridge.  The source proof shows that sufficiently
far along each dyadic subsequence, `β_N(θ)` and the anchor `β_M(θ)` lie in the
same old two-step level bracket.  Together with vanishing old adjacent mesh,
that bracket inclusion supplies the anchor envelope required by the Cauchy
bridge above.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_two_step_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth (m := M + 1) (levels M))
        atTop (nhds 0))
    (hbracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  let mesh2 : ℕ → ℝ := fun M : ℕ =>
    2 * binaryEndpointAdjacentMaxWidth (m := M + 1) (levels M)
  have hmesh2 : Tendsto mesh2 atTop (nhds 0) := by
    dsimp [mesh2]
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hmesh
  have hmesh2_nonneg : ∀ M : ℕ, 0 ≤ mesh2 M := by
    intro M
    dsimp [mesh2]
    exact mul_nonneg (by norm_num)
      (binaryEndpointAdjacentMaxWidth_nonneg (hlevels M))
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_anchor_bound
      betaSeq quantileSeq mesh2 hmesh2 hmesh2_nonneg ?_
  intro C M
  obtain ⟨K, hK⟩ := hbracket C M
  refine ⟨K, ?_⟩
  intro N hN θ hθ
  rcases hK N hN θ hθ with ⟨i, htail, hanchor⟩
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels M) i htail hanchor

/--
Theorem B.1 eventual two-step-bracket bridge.  It is enough for the source
two-step bracket condition to hold for all sufficiently large anchors.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_eventually_two_step_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth (m := M + 1) (levels M))
        atTop (nhds 0))
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  let mesh2 : ℕ → ℝ := fun M : ℕ =>
    2 * binaryEndpointAdjacentMaxWidth (m := M + 1) (levels M)
  have hmesh2 : Tendsto mesh2 atTop (nhds 0) := by
    dsimp [mesh2]
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hmesh
  have hmesh2_nonneg : ∀ M : ℕ, 0 ≤ mesh2 M := by
    intro M
    dsimp [mesh2]
    exact mul_nonneg (by norm_num)
      (binaryEndpointAdjacentMaxWidth_nonneg (hlevels M))
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_eventually_anchor_bound
      betaSeq quantileSeq mesh2 hmesh2 hmesh2_nonneg ?_
  intro C
  filter_upwards [hbracket C] with M hM
  rcases hM with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro N hN θ hθ
  rcases hK N hN θ hθ with ⟨i, htail, hanchor⟩
  exact
    BinaryEndpointLevelVector_dist_le_two_maxWidth_of_mem_two_step_interval
      (hlevels M) i htail hanchor

/--
Theorem B.1 fixed-width bracket bridge.  The Cauchy argument does not depend
on the source bracket having exactly two adjacent old intervals: any
source-derived bracket whose endpoint-index width is bounded by a fixed
constant gives the same subsequential convergence conclusion, because the old
adjacent mesh tends to zero.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_eventually_fixed_width_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (hmesh :
      Tendsto
        (fun M : ℕ =>
          binaryEndpointAdjacentMaxWidth (m := M + 1) (levels M))
        atTop (nhds 0))
    (width : ℕ)
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi : i + width ≤ (M + 1) + 1,
                  betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  let meshWidth : ℕ → ℝ := fun M : ℕ =>
    (width : ℝ) *
      binaryEndpointAdjacentMaxWidth (m := M + 1) (levels M)
  have hmeshWidth : Tendsto meshWidth atTop (nhds 0) := by
    dsimp [meshWidth]
    simpa using (tendsto_const_nhds (x := (width : ℝ))).mul hmesh
  have hmeshWidth_nonneg : ∀ M : ℕ, 0 ≤ meshWidth M := by
    intro M
    dsimp [meshWidth]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le width)
      (binaryEndpointAdjacentMaxWidth_nonneg (hlevels M))
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_eventually_anchor_bound
      betaSeq quantileSeq meshWidth hmeshWidth hmeshWidth_nonneg ?_
  intro C
  filter_upwards [hbracket C] with M hM
  rcases hM with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro N hN θ hθ
  rcases hK N hN θ hθ with ⟨i, hi, htail, hanchor⟩
  exact
    BinaryEndpointLevelVector_dist_le_nat_mul_maxWidth_of_mem_block_interval
      (hlevels M) (m := M + 1) (i := i) (width := width) hi
      htail hanchor

/--
Theorem B.1 two-step-bracket bridge with C.2 discharged.  For uniform
equalized old level vectors, Corollary C.2 supplies the vanishing mesh; the
only remaining paper-specific input is the C.5-style two-step bracket
inclusion for the optimal dyadic subsequence.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_two_step_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (heq : ∀ M : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels M)
        (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
    (hbracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_two_step_bracket
    betaSeq quantileSeq levels hlevels
    (corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
      levels hlevels heq)
    hbracket

/--
Theorem B.1 eventual two-step-bracket bridge with Corollary C.2 discharged by
uniform equalized old level vectors.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_two_step_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (heq : ∀ M : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels M)
        (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_eventually_two_step_bracket
    betaSeq quantileSeq levels hlevels
    (corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
      levels hlevels heq)
    hbracket

/--
Theorem B.1 fixed-width bracket bridge with Corollary C.2 discharged by
uniform equalized old level vectors.  This is the source-facing hook for
proving B.1 from any dyadic selector argument that places the anchor and tail
selected levels in a common old bracket of fixed index width.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_fixed_width_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (heq : ∀ M : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels M)
        (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
    (width : ℕ)
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi : i + width ≤ (M + 1) + 1,
                  betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_eventually_fixed_width_bracket
    betaSeq quantileSeq levels hlevels
    (corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
      levels hlevels heq)
    width hbracket

/--
Theorem B.1 two-step-bracket bridge with equalized rates derived from finite
uniform optimality.  This is the source-facing C.5 route: the paper-specific
work is the two-step bracket inclusion, while Lemma 3.1 supplies the
equalized-rate structure from optimality.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_two_step_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hbracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_two_step_bracket
    betaSeq quantileSeq levels
    (fun M => (hoptimal M).1)
    (fun M =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal M))
    hbracket

/--
Theorem B.1 eventual two-step-bracket bridge with equalized rates derived
from finite uniform optimality.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_two_step_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_two_step_bracket
    betaSeq quantileSeq levels
    (fun M => (hoptimal M).1)
    (fun M =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal M))
    hbracket

/--
Theorem B.1 eventual fixed-width bracket bridge with equalized rates derived
from finite uniform optimality.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_fixed_width_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (width : ℕ)
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi : i + width ≤ (M + 1) + 1,
                  betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_fixed_width_bracket
    betaSeq quantileSeq levels
    (fun M => (hoptimal M).1)
    (fun M =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal M))
    width hbracket

/--
A beta sequence is represented by endpoint levels and a level selector when
each value `β_M(θ)` is exactly the selected endpoint level.  This is the
source convention for piecewise-constant binary rating rules.
-/
def BetaSeqRepresentedByLevelIndex
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2)) : Prop :=
  ∀ M θ, betaSeq M θ = levels M (levelIndex M θ)

/--
Theorem B.1 level-selector bridge.  If the source beta rules are represented by
level selectors, then it is enough to prove the two-step bracket condition for
the selected levels.  Corollary C.2 still supplies the vanishing mesh from the
uniform equalized-rate hypotheses.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_levelIndex_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2))
    (hrepr : BetaSeqRepresentedByLevelIndex betaSeq levels levelIndex)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (heq : ∀ M : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels M)
        (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
    (hidxBracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            levels (theoremB1SubsequenceIndex C N)
                (levelIndex (theoremB1SubsequenceIndex C N) θ) ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              levels (theoremB1SubsequenceIndex C M)
                (levelIndex (theoremB1SubsequenceIndex C M) θ) ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_two_step_bracket
      betaSeq quantileSeq levels hlevels heq ?_
  intro C M
  rcases hidxBracket C M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro N hN θ hθ
  rcases hK N hN θ hθ with ⟨i, htail, hanchor⟩
  refine ⟨i, ?_, ?_⟩
  · rw [hrepr (theoremB1SubsequenceIndex C N) θ]
    exact htail
  · rw [hrepr (theoremB1SubsequenceIndex C M) θ]
    exact hanchor

/--
Theorem B.1 eventual level-selector bridge.  The selected-level two-step
bracket condition only needs to hold for all sufficiently large anchor
indices, matching the source proof's eventual anchor-envelope argument.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_levelIndex_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2))
    (hrepr : BetaSeqRepresentedByLevelIndex betaSeq levels levelIndex)
    (hlevels : ∀ M : ℕ, BinaryEndpointLevelVector (levels M))
    (heq : ∀ M : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels M)
        (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
    (hidxBracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                levels (theoremB1SubsequenceIndex C N)
                    (levelIndex (theoremB1SubsequenceIndex C N) θ) ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  levels (theoremB1SubsequenceIndex C M)
                    (levelIndex (theoremB1SubsequenceIndex C M) θ) ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_two_step_bracket
      betaSeq quantileSeq levels hlevels heq ?_
  intro C
  filter_upwards [hidxBracket C] with M hM
  rcases hM with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro N hN θ hθ
  rcases hK N hN θ hθ with ⟨i, htail, hanchor⟩
  refine ⟨i, ?_, ?_⟩
  · rw [hrepr (theoremB1SubsequenceIndex C N) θ]
    exact htail
  · rw [hrepr (theoremB1SubsequenceIndex C M) θ]
    exact hanchor

/--
Theorem B.1 level-selector bridge with equalized rates derived from finite
uniform optimality.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_levelIndex_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2))
    (hrepr : BetaSeqRepresentedByLevelIndex betaSeq levels levelIndex)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hidxBracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            levels (theoremB1SubsequenceIndex C N)
                (levelIndex (theoremB1SubsequenceIndex C N) θ) ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              levels (theoremB1SubsequenceIndex C M)
                (levelIndex (theoremB1SubsequenceIndex C M) θ) ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_levelIndex_bracket
    betaSeq quantileSeq levels levelIndex hrepr
    (fun M => (hoptimal M).1)
    (fun M =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal M))
    hidxBracket

/--
Theorem B.1 eventual level-selector bridge with equalized rates derived from
finite uniform optimality.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_levelIndex_bracket
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2))
    (hrepr : BetaSeqRepresentedByLevelIndex betaSeq levels levelIndex)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hidxBracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                levels (theoremB1SubsequenceIndex C N)
                    (levelIndex (theoremB1SubsequenceIndex C N) θ) ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  levels (theoremB1SubsequenceIndex C M)
                    (levelIndex (theoremB1SubsequenceIndex C M) θ) ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_levelIndex_bracket
    betaSeq quantileSeq levels levelIndex hrepr
    (fun M => (hoptimal M).1)
    (fun M =>
      binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
        (hoptimal M))
    hidxBracket

/--
Theorem B.1 tracking bridge.  If a fixed dyadic subsequence of `β_M` uniformly
tracks a dyadic quantile subsequence up to a vanishing error, then that
subsequence has a uniform limit.  This isolates a common grid-convergence
route to the B.1 conclusion from the source-specific optimality argument that
must supply the tracking estimate.
-/
theorem theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℝ) (C : ℕ)
    (hquantile :
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          quantileSeq (theoremB1SubsequenceIndex C N) θ)
        (fun θ : ℝ => θ) atTop (Set.Icc (0 : ℝ) 1))
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htracking :
      ∀ᶠ N : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (quantileSeq (theoremB1SubsequenceIndex C N) θ) ≤ mesh N) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  refine ⟨fun θ : ℝ => θ, ?_⟩
  exact
    AppliedModelingLib.Math.tendstoUniformlyOn_of_tendstoUniformlyOn_of_eventual_dist_le
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (fun N : ℕ => fun θ : ℝ =>
        quantileSeq (theoremB1SubsequenceIndex C N) θ)
      (fun θ : ℝ => θ) (Set.Icc (0 : ℝ) 1) mesh hquantile hmesh
      htracking

/--
General-limit B.1 tracking bridge.  If a fixed dyadic subsequence of `β_M`
uniformly tracks a quantile subsequence and that quantile subsequence has an
arbitrary uniform limit, then the beta subsequence has the same uniform limit.
-/
theorem theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking_to
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (mesh : ℕ → ℝ) (C : ℕ)
    (hquantile :
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          quantileSeq (theoremB1SubsequenceIndex C N) θ)
        quantileLimit atTop (Set.Icc (0 : ℝ) 1))
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htracking :
      ∀ᶠ N : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (quantileSeq (theoremB1SubsequenceIndex C N) θ) ≤ mesh N) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  refine ⟨quantileLimit, ?_⟩
  exact
    AppliedModelingLib.Math.tendstoUniformlyOn_of_tendstoUniformlyOn_of_eventual_dist_le
      (fun N : ℕ => fun θ : ℝ =>
        betaSeq (theoremB1SubsequenceIndex C N) θ)
      (fun N : ℕ => fun θ : ℝ =>
        quantileSeq (theoremB1SubsequenceIndex C N) θ)
      quantileLimit (Set.Icc (0 : ℝ) 1) mesh hquantile hmesh
      htracking

/--
Theorem B.1 tracking principle.  If every positive dyadic subsequence of the
source `β_M` rules uniformly tracks the corresponding quantile maps up to a
vanishing error, then the full B.1 subsequential convergence conclusion
follows from the paper's quantile-convergence hypothesis.  The `C = 0`
subsequence is constant at source index `1`.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_dyadic_quantile_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (htracking :
      ∀ C : ℕ, 0 < C →
        ∃ mesh : ℕ → ℝ,
          Tendsto mesh atTop (nhds 0) ∧
            ∀ᶠ N : ℕ in atTop,
              ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
                dist
                  (betaSeq (theoremB1SubsequenceIndex C N) θ)
                  (quantileSeq (theoremB1SubsequenceIndex C N) θ) ≤
                    mesh N) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro hquantile C
  by_cases hC : 0 < C
  · rcases htracking C hC with ⟨mesh, hmesh, htrack⟩
    exact
      theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking
        betaSeq quantileSeq mesh C
        (AppliedModelingLib.Math.TendstoUniformlyOn.comp_tendsto_index hquantile
          (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC))
        hmesh htrack
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
General-limit B.1 tracking principle.  This is the source theorem's natural
form: the quantile maps may converge uniformly to any limiting coordinate
function, and beta inherits dyadic subsequential uniform limits when it tracks
those quantiles up to a vanishing error.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_dyadic_quantile_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (htracking :
      ∀ C : ℕ, 0 < C →
        ∃ mesh : ℕ → ℝ,
          Tendsto mesh atTop (nhds 0) ∧
            ∀ᶠ N : ℕ in atTop,
              ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
                dist
                  (betaSeq (theoremB1SubsequenceIndex C N) θ)
                  (quantileSeq (theoremB1SubsequenceIndex C N) θ) ≤
                    mesh N) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  intro hquantile C
  by_cases hC : 0 < C
  · rcases htracking C hC with ⟨mesh, hmesh, htrack⟩
    exact
      theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking_to
        betaSeq quantileSeq quantileLimit mesh C
        (AppliedModelingLib.Math.TendstoUniformlyOn.comp_tendsto_index hquantile
          (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC))
        hmesh htrack
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
Theorem B.1 direct convergence bridge.  If the source `β_M` rules themselves
converge uniformly on `[0,1]`, then every positive dyadic subsequence has that
same limit; the `C = 0` subsequence is constant at source index `1`.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_beta_tendstoUniformlyOn
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (betaLimit : ℝ → ℝ)
    (hbeta :
      TendstoUniformlyOn betaSeq betaLimit atTop (Set.Icc (0 : ℝ) 1)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  intro _hquantile C
  by_cases hC : 0 < C
  · exact
      ⟨betaLimit,
        AppliedModelingLib.Math.TendstoUniformlyOn.comp_tendsto_index hbeta
          (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC)⟩
  · have hC0 : C = 0 := by omega
    subst C
    refine ⟨fun θ : ℝ => betaSeq 1 θ, ?_⟩
    intro u hu
    filter_upwards with N
    intro θ _hθ
    simpa [theoremB1SubsequenceIndex] using
      (refl_mem_uniformity (x := betaSeq 1 θ) hu)

/--
Theorem B.1 global tracking bridge.  A single eventual uniform tracking
estimate for all source sizes implies the dyadic tracking hypotheses required
by the B.1 principle.  This is the source-facing form used when the paper's
optimality argument supplies one mesh bound for the full sequence rather than
separate bounds for each dyadic subsequence.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_global_quantile_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htracking :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (betaSeq M θ) (quantileSeq M θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_dyadic_quantile_tracking
      betaSeq quantileSeq ?_
  intro C hC
  refine ⟨fun N : ℕ => mesh (theoremB1SubsequenceIndex C N), ?_, ?_⟩
  · exact hmesh.comp (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC)
  · exact (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC).eventually htracking

/--
General-limit global tracking bridge.  A single eventual uniform tracking
estimate for all source sizes implies the dyadic tracking hypotheses required
by the arbitrary-quantile-limit B.1 principle.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_global_quantile_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htracking :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (betaSeq M θ) (quantileSeq M θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_dyadic_quantile_tracking
      betaSeq quantileSeq quantileLimit ?_
  intro C hC
  refine ⟨fun N : ℕ => mesh (theoremB1SubsequenceIndex C N), ?_, ?_⟩
  · exact hmesh.comp (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC)
  · exact (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC).eventually htracking

/--
Theorem B.1 global tracking bridge for an explicit `O(1/M)` source-selector
bound.  This is the common floor/quantile form: if `β_M` is uniformly within
`B/(M+1)` of the interval quantile map, then the B.1 dyadic subsequential
convergence conclusion follows.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_global_quantile_tracking_inv_succ
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (B : ℝ)
    (htracking :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (betaSeq M θ) (quantileSeq M θ) ≤
            B / (((M + 1 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_global_quantile_tracking
      betaSeq quantileSeq
      (fun M : ℕ => B / (((M + 1 : ℕ) : ℝ))) ?_ htracking
  simpa using
    (Filter.Tendsto.const_div_atTop
      AppliedModelingLib.Math.tendsto_nat_succ_cast_atTop B)

/--
General-limit global tracking bridge for an explicit `O(1/M)` source-selector
bound.
-/
theorem theoremB1UniformOptimalSubsequencePrincipleTo_of_global_quantile_tracking_inv_succ
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ) (B : ℝ)
    (htracking :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (betaSeq M θ) (quantileSeq M θ) ≤
            B / (((M + 1 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_global_quantile_tracking
      betaSeq quantileSeq quantileLimit
      (fun M : ℕ => B / (((M + 1 : ℕ) : ℝ))) ?_ htracking
  simpa using
    (Filter.Tendsto.const_div_atTop
      AppliedModelingLib.Math.tendsto_nat_succ_cast_atTop B)

/--
Corollary C.4 dyadic quantile specialization: along every positive dyadic B.1
subsequence, the equispaced interval quantile maps still converge uniformly to
the identity.
-/
theorem corollaryC4_equispaced_dyadic_quantile_tendstoUniformlyOn_identity
    {C : ℕ} (hC : 0 < C) :
    TendstoUniformlyOn
      (fun N : ℕ => fun θ : ℝ =>
        equispacedIntervalQuantile (theoremB1SubsequenceIndex C N) θ)
      (fun θ : ℝ => θ) atTop (Set.Icc (0 : ℝ) 1) :=
  AppliedModelingLib.Math.TendstoUniformlyOn.comp_tendsto_index
    corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity
    (theoremB1SubsequenceIndex_tendsto_atTop_of_pos hC)

/--
Corollary C.4 tracking bridge specialized to equispaced Kendall/Spearman
interval quantiles.  The remaining source-specific input is a uniform
vanishing-error estimate showing that the optimal `β_M` subsequence tracks the
equispaced interval quantile map.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_tracking
    (betaSeq : ℕ → ℝ → ℝ) (mesh : ℕ → ℝ)
    {C : ℕ} (hC : 0 < C)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htracking :
      ∀ᶠ N : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (equispacedIntervalQuantile
              (theoremB1SubsequenceIndex C N) θ) ≤ mesh N) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking
    betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
    mesh C
    (corollaryC4_equispaced_dyadic_quantile_tendstoUniformlyOn_identity hC)
    hmesh htracking

/--
Corollary C.4 global tracking bridge specialized to the equispaced
Kendall/Spearman quantile convention.  It packages the source proof pattern
where the same vanishing mesh tracks every finite rating rule.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_global_uniform_tracking
    (betaSeq : ℕ → ℝ → ℝ) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htracking :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (betaSeq M θ) (equispacedIntervalQuantile M θ) ≤ mesh M)
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  (theoremB1UniformOptimalSubsequencePrinciple_of_global_quantile_tracking
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      mesh hmesh htracking)
    corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity
    C

/--
Corollary C.4 global tracking bridge for the explicit `O(1/M)` floor-selector
bound.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_global_uniform_tracking_inv_succ
    (betaSeq : ℕ → ℝ → ℝ) (B : ℝ)
    (htracking :
      ∀ᶠ M : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (betaSeq M θ) (equispacedIntervalQuantile M θ) ≤
            B / (((M + 1 : ℕ) : ℝ)))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  (theoremB1UniformOptimalSubsequencePrinciple_of_global_quantile_tracking_inv_succ
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      B htracking)
    corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity
    C

/--
Corollary C.4 source bridge: for the equispaced Kendall/Spearman interval
quantiles, Theorem B.1's quantile-convergence hypothesis is automatic.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    (betaSeq : ℕ → ℝ → ℝ)
    (hB1 :
      theoremB1UniformOptimalSubsequencePrinciple
        betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  hB1 corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity C

/--
Corollary C.4 equispaced source bridge with B.1 discharged by the explicit
clamped-floor, uniform-equalized endpoint model.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_equalized_clampedFloor
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_clampedFloor
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels hrepr hlevels heq)
    C

/--
Corollary C.4 equispaced source bridge with B.1 discharged by finite optimal
uniform endpoint chains and the clamped-floor source selector convention.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_clampedFloor
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_clampedFloor
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels hrepr hoptimal)
    C

/--
Corollary C.4 equispaced source bridge for optimal endpoint chains and the
common floor-coordinate invariant.  This is the selector-tracking form of the
remaining arbitrary-source-model B.1 assumption.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_common_floor_coordinate
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart M) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                levelIndex (uniformDoubledEndpointIndexIterate endpointStart N) θ =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x)
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal hcommon)
    C

/--
Corollary C.4 equispaced source bridge for optimal uniform endpoint chains.
The source selector is given by the floor-index value formula with
`x_θ = θ`, so B.1 is discharged by the identity-coordinate optimal selector
wrapper.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_identity_floor_value_selector
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min (Nat.floor (((m + 2 : ℕ) : ℝ) * θ)) (m + 1))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_identity_floor_value_selector
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal hlevelIndex_val)
    C

/--
Corollary C.4 equispaced source bridge using the named B.1 source floor-selector
convention with `x_θ = θ`, matching the source proof's Kendall/Spearman
sentence.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_source_floor_selector_convention
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hsource :
      theoremB1SourceFloorSelectorConvention levelIndex (fun θ : ℝ => θ))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_source_floor_selector_convention
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex (fun θ : ℝ => θ) hrepr hoptimal
      (fun _θ hθ => hθ) hsource)
    C

/--
Corollary C.4 equispaced source bridge using the paper's quantile-index
selector convention.  The selector for `β_M(θ)` is the clamped floor of the
equispaced quantile map, and the remaining source input is the common
coordinate envelope from the proof of Theorem B.1.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector_common_coordinate
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) *
              equispacedIntervalQuantile (m + 2) θ))
            (m + 1))
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (equispacedIntervalQuantile
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ) =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
                clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (equispacedIntervalQuantile
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ) =
                  clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x)
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_selector_common_coordinate
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal hlevelIndex_val hquantile_common)
    C

/--
Corollary C.4 equispaced selector convention.  For Kendall/Spearman
equispaced intervals, the quantile floor selector has the common-coordinate
witness required by the B.1 bridge, with `x_θ = θ`.
-/
theorem corollaryC4_equispaced_quantile_common_floor_coordinate :
    ∀ C : ℕ, 0 < C →
      let endpointStart : ℕ := 2 * C - 1
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
              clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart M)
                  (equispacedIntervalQuantile
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
              clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart N)
                  (equispacedIntervalQuantile
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart N) x := by
  intro C hC
  filter_upwards with M
  intro N _hN θ hθ
  refine ⟨θ, hθ, ?_, ?_⟩
  · exact
      clampedFloorLevelIndex_equispacedIntervalQuantile_eq
        (uniformDoubledEndpointIndexIterate (2 * C - 1) M) θ
  · exact
      clampedFloorLevelIndex_equispacedIntervalQuantile_eq
        (uniformDoubledEndpointIndexIterate (2 * C - 1) N) θ

/--
Theorem B.1 equispaced source bridge with the quantile-floor selector built
in.  For Kendall/Spearman equispaced intervals, finite uniform optimality and
the source convention `x_θ = θ` give the full dyadic subsequence principle.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_equispaced_floor_selector
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m
        (clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ)))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m)) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ) := by
  exact
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_selector_common_coordinate
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels
      (fun m : ℕ => fun θ : ℝ =>
        clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ))
      hrepr hoptimal
      (by
        intro m θ _hθ
        rw [clampedFloorLevelIndex_val])
      corollaryC4_equispaced_quantile_common_floor_coordinate

/--
Theorem B.1 with the canonical uniform optimal equispaced source convention
discharged: the canonical sequence is represented by the equispaced
quantile-floor selector, and the canonical endpoint levels are finite-rate
optimal.
-/
theorem theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_optimal_equispaced_floor_selector :
    theoremB1UniformOptimalSubsequencePrinciple
      canonicalUniformEqualizedClampedFloorBetaSeq
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ) := by
  refine
    theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_equispaced_floor_selector
      canonicalUniformEqualizedClampedFloorBetaSeq
      canonicalUniformEqualizedEndpointLevels ?_ ?_
  · intro m θ
    rw [canonicalUniformEqualizedClampedFloorBetaSeq_repr]
    rw [clampedFloorLevelIndex_equispacedIntervalQuantile_eq]
  · intro m
    exact canonicalUniformEqualizedEndpointLevels_isMaximizerOn m

/--
Corollary C.4 equispaced source bridge with the quantile-floor selector
premise discharged.  This is the Kendall/Spearman branch of the source proof:
finite uniform optimality supplies the equalized endpoint levels, and
equispaced intervals make the common B.1 coordinate simply `x_θ = θ`.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) *
              equispacedIntervalQuantile (m + 2) θ))
            (m + 1))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector_common_coordinate
    betaSeq levels levelIndex hrepr hoptimal hlevelIndex_val
    corollaryC4_equispaced_quantile_common_floor_coordinate C

/--
Corollary C.4 equispaced source bridge with the paper's quantile-floor
selector built in.  This removes the separate selector-normalization premise
from the Kendall/Spearman branch: the selected endpoint is definitionally the
clamped floor of the equispaced interval quantile.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_equispaced_floor_selector
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m
        (clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ)))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector
    betaSeq levels
    (fun m θ => clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ))
    hrepr hoptimal
    (by
      intro m θ _hθ
      rw [clampedFloorLevelIndex_val])
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and the source two-step bracket condition.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_two_step_bracket
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hbracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_two_step_bracket
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels hoptimal hbracket)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and an eventual source two-step bracket condition.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_two_step_bracket
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_two_step_bracket
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels hoptimal hbracket)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and an eventual fixed-width old-grid bracket condition.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_fixed_width_bracket
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (width : ℕ)
    (hbracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi : i + width ≤ (M + 1) + 1,
                  betaSeq (theoremB1SubsequenceIndex C N) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩) ∧
                  betaSeq (theoremB1SubsequenceIndex C M) θ ∈
                    Set.Icc (levels M ⟨i, by omega⟩)
                      (levels M ⟨i + width, by omega⟩))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_fixed_width_bracket
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels hoptimal width hbracket)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and an eventual scaled fixed-width selector-window condition.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_scaled_block_window
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (width : ℕ) (hwidth : 2 ≤ width)
    (hwindow :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + width ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M) θ).1 ≤
                    i + width ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N) θ).1 ≤
                    2 ^ (N - M) * (i + width))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_scaled_block_window
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal width hwidth hwindow)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and a bounded-error common floor-coordinate convention.  This is the
fixed-width source-selector form: the source may choose an endpoint within a
bounded number of cells of a common dyadic floor coordinate.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_common_floor_coordinate_bounded_error
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hcommon :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 + B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 + 2 ^ (N - M) * B ∧
                (levelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    θ).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B)
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate_bounded_error
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal B width hwidth hcommon)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality, the quantile-floor selector convention, and one global
floor-tracking premise.  This is the source-facing bounded-selector form:
the selected source coordinate may stay within a fixed number of endpoint
floor cells from the equispaced interval quantile at every large source size.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_global_floor_tracking
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (sourceCoord : ℝ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) *
              equispacedIntervalQuantile (m + 2) θ))
            (m + 1))
    (hcoord_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        sourceCoord θ ∈ Set.Icc (0 : ℝ) 1)
    (B : ℕ)
    (hfloor_track :
      ∀ᶠ m : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          (clampedFloorLevelIndex m (sourceCoord θ)).1 ≤
            (clampedFloorLevelIndex m
              (equispacedIntervalQuantile (m + 2) θ)).1 + B ∧
          (clampedFloorLevelIndex m
              (equispacedIntervalQuantile (m + 2) θ)).1 ≤
            (clampedFloorLevelIndex m (sourceCoord θ)).1 + B)
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_global_floor_tracking
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex sourceCoord hrepr hoptimal hlevelIndex_val
      hcoord_range B (2 + 2 * B) (by omega) hfloor_track)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged through the quantitative
limit-tracking selector route.  For equispaced interval quantiles, the limiting
source coordinate is `θ` and the `O(1/m)` tracking premise holds with `B = 1`.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_limit_dist_tracking
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) *
              equispacedIntervalQuantile (m + 2) θ))
            (m + 1))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  (theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      (fun θ : ℝ => θ) levels levelIndex hrepr hoptimal hlevelIndex_val
      (fun _θ hθ => hθ)
      (fun m θ hθ =>
        equispacedIntervalQuantile_mem_Icc (m + 2) (by omega) hθ)
      1 4 (by norm_num)
      (by
        filter_upwards with m θ hθ
        simpa [Nat.cast_one] using
          (equispacedIntervalQuantile_dist_identity_le_inv
            (m + 2) (by omega) hθ))
    corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity
    C)

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and the paper's quantile-floor selector, allowing a bounded dyadic
floor-envelope error.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * equispacedIntervalQuantile (m + 2) θ))
            (m + 1))
    (B width : ℕ) (hwidth : 2 + 2 * B ≤ width)
    (hquantile_common :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (equispacedIntervalQuantile
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M)
                    (equispacedIntervalQuantile
                      (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart M) x).1 + B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (equispacedIntervalQuantile
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 + 2 ^ (N - M) * B ∧
                (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N)
                    (equispacedIntervalQuantile
                      (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                      θ)).1 ≤
                  (clampedFloorLevelIndex
                    (uniformDoubledEndpointIndexIterate endpointStart N) x).1 +
                    2 ^ (N - M) * B)
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal hlevelIndex_val B width hwidth
      hquantile_common)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and a selected-level two-step bracket condition.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_levelIndex_bracket
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2))
    (hrepr : BetaSeqRepresentedByLevelIndex betaSeq levels levelIndex)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hidxBracket :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          ∃ i : Fin (M + 1),
            levels (theoremB1SubsequenceIndex C N)
                (levelIndex (theoremB1SubsequenceIndex C N) θ) ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩) ∧
              levels (theoremB1SubsequenceIndex C M)
                (levelIndex (theoremB1SubsequenceIndex C M) θ) ∈
                Set.Icc (levels M ⟨i.1, by omega⟩)
                  (levels M ⟨i.1 + 2, by omega⟩))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_levelIndex_bracket
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal hidxBracket)
    C

/--
Corollary C.4 equispaced bridge with B.1 discharged by finite uniform
optimality and an eventual selected-level two-step bracket condition.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_levelIndex_bracket
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (M : ℕ) → Fin ((M + 1) + 2) → ℝ)
    (levelIndex : (M : ℕ) → ℝ → Fin ((M + 1) + 2))
    (hrepr : BetaSeqRepresentedByLevelIndex betaSeq levels levelIndex)
    (hoptimal : ∀ M : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin ((M + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((M + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin ((M + 1) + 2) => (1 : ℝ)))
        (levels M))
    (hidxBracket :
      ∀ C : ℕ,
        ∀ᶠ M : ℕ in atTop,
          ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : Fin (M + 1),
                levels (theoremB1SubsequenceIndex C N)
                    (levelIndex (theoremB1SubsequenceIndex C N) θ) ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩) ∧
                  levels (theoremB1SubsequenceIndex C M)
                    (levelIndex (theoremB1SubsequenceIndex C M) θ) ∈
                    Set.Icc (levels M ⟨i.1, by omega⟩)
                      (levels M ⟨i.1 + 2, by omega⟩))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq
    (theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_levelIndex_bracket
      betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      levels levelIndex hrepr hoptimal hidxBracket)
    C

/--
Corollary C.4 for the canonical uniform equalized clamped-floor sequence:
every dyadic source subsequence has a uniform limit on `[0,1]`.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_equalized_clampedFloor
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          canonicalUniformEqualizedClampedFloorBetaSeq
            (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    canonicalUniformEqualizedClampedFloorBetaSeq
    theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_equalized_clampedFloor
    C

/--
Corollary C.4 with the canonical uniform optimal equispaced selector
discharged: the canonical optimal beta sequence has uniformly convergent
dyadic subsequences.
-/
theorem corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          canonicalUniformEqualizedClampedFloorBetaSeq
            (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    canonicalUniformEqualizedClampedFloorBetaSeq
    theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_optimal_equispaced_floor_selector
    C

/--
Lemma C.10 Spearman source objective in finite interval form.  The summand is
the integral of the linear distance weight over an ordered pair of intervals,
written as midpoint distance times the two interval lengths.
-/
noncomputable def spearmanLinearWeightOrderedPairIntervalObjective
    (M : ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if i < j then
      (((s (j + 1) + s j) / 2) - ((s (i + 1) + s i) / 2)) *
        (s (i + 1) - s i) * (s (j + 1) - s j)
    else 0

/--
Source ordered-pair objective with a continuous weight evaluated at cell
midpoints.  This is the finite cell-midpoint convention used by the
paper-local finite-level source certificates.
-/
noncomputable def midpointWeightedOrderedPairIntervalObjective
    (M : ℕ) (weight : ℝ × ℝ → ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if i < j then
      weight (((s (i + 1) + s i) / 2), ((s (j + 1) + s j) / 2)) *
        (s (i + 1) - s i) * (s (j + 1) - s j)
    else 0

/--
Theorem 3.1 equation-(20) limiting-value objective for a fixed finite
cutpoint chain: sum the true weighted measure of each selected ordered pair
cell.  Unlike the midpoint objective above, this is the paper's exact
cell-integral convention for the primary `S*` objective.
-/
noncomputable def theorem31CellIntegralLimitingValueObjective
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (weight : ℝ × ℝ → ℝ) : ℝ :=
  let P :=
    theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
  ∑ component : theorem31OrderedNontrivialPairComponent m,
    P.componentIntegral weight component

/--
The equation-(20) finite cell sum is the integral of the objective weight over
the selected ordered-pair support of the cutpoint partition.
-/
theorem theorem31CellIntegralLimitingValueObjective_eq_support_integral
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet
              component)
          (μ.prod μ)) :
    theorem31CellIntegralLimitingValueObjective μ (m := m) cut hmono weight =
      ∫ q in
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).support,
        weight q ∂(μ.prod μ) := by
  let P :=
    theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
  have h :=
    P.setIntegral_eq_sum_componentIntegral weight (by
      intro component
      simpa [P] using hweight_int component)
  simpa [theorem31CellIntegralLimitingValueObjective, P] using h.symm

/-- Spearman's interval objective is the midpoint-weighted objective with linear distance weight. -/
theorem midpointWeightedOrderedPairIntervalObjective_linearDistance_eq_spearman
    (M : ℕ) :
    midpointWeightedOrderedPairIntervalObjective M
        (fun q : ℝ × ℝ => q.2 - q.1) =
      spearmanLinearWeightOrderedPairIntervalObjective M := by
  funext s
  unfold midpointWeightedOrderedPairIntervalObjective
    spearmanLinearWeightOrderedPairIntervalObjective
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]

/--
Lemma C.11 constant-weight interval objective in gap-vector form.  For
Kendall's tau, the source objective is equivalent to
`(1 - ∑ gap_i^2) / 2`; this expression is maximized by the uniform gap vector.
-/
def kendallConstantWeightGapObjective {M : ℕ} (gap : Fin M → ℝ) : ℝ :=
  (1 - ∑ i : Fin M, (gap i) ^ 2) / 2

/-- Lemma C.11 interval objective written from endpoint cutpoints. -/
def kendallConstantWeightIntervalObjective (M : ℕ) (s : ℕ → ℝ) : ℝ :=
  kendallConstantWeightGapObjective
    (M := M) (fun i : Fin M => s (i.1 + 1) - s i.1)

/-- Lemma C.11 source ordered-pair objective written from endpoint cutpoints. -/
noncomputable def kendallConstantWeightOrderedPairIntervalObjective
    (M : ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin M,
    if i < j then
      (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
    else 0

/-- Equispaced interval cutpoints `s_i = i / M` on `[0,1]`. -/
noncomputable def equispacedIntervalCutpoint (M : ℕ) (i : ℕ) : ℝ :=
  (i : ℝ) / (M : ℝ)

theorem equispacedIntervalCutpoint_zero (M : ℕ) :
    equispacedIntervalCutpoint M 0 = 0 := by
  simp [equispacedIntervalCutpoint]

theorem equispacedIntervalCutpoint_self {M : ℕ} (hM : 0 < M) :
    equispacedIntervalCutpoint M M = 1 := by
  have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  rw [equispacedIntervalCutpoint]
  exact div_self hM_ne

theorem monotone_equispacedIntervalCutpoint (M : ℕ) :
    Monotone (equispacedIntervalCutpoint M) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg M)

theorem equispacedIntervalCutpoint_gap {M : ℕ} (hM : 0 < M) (i : Fin M) :
    equispacedIntervalCutpoint M (i.1 + 1) -
        equispacedIntervalCutpoint M i.1 =
      (M : ℝ)⁻¹ := by
  have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  unfold equispacedIntervalCutpoint
  field_simp [hM_ne]
  norm_num

/-- Adjacent equispaced cutpoints are strictly ordered. -/
theorem equispacedIntervalCutpoint_strict_adjacent
    {M : ℕ} (hM : 0 < M) (i : ℕ) :
    equispacedIntervalCutpoint M i <
      equispacedIntervalCutpoint M (i + 1) := by
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
  unfold equispacedIntervalCutpoint
  exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hM_pos

/--
Lemma C.4/Theorem 3.1 equispaced source-rate certificate.  For equispaced
cutpoints, constant weight, uniform sampling, and the canonical equalized
endpoint levels, the source-defined `Wbar_k` has a positive exponential-rate
certificate.
-/
theorem theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_equispacedIntervalCutpoint
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ
          (equispacedIntervalCutpoint (m + 2))
          (monotone_equispacedIntervalCutpoint (m + 2))
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          (fun _ : ℝ × ℝ => (1 : ℝ)))
        c := by
  exact
    theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_of_cell_midpoints
      μ hm (equispacedIntervalCutpoint (m + 2))
      (monotone_equispacedIntervalCutpoint (m + 2))
      (by
        intro i _hi
        exact
          equispacedIntervalCutpoint_strict_adjacent
            (M := m + 2) (by omega) i)

/--
Theorem 3.1 equispaced fixed-discretization source branch: for the normalized
constant-weight, uniform-sampling convention, equispaced cutpoints admit
endpoint levels that both carry a source-defined positive rate certificate and
are lexicographically optimal among endpoint vectors once the primary
partition value is fixed.
-/
theorem theorem31_sourceDefinedWbar_const_weight_uniform_sampleRate_fixed_value_lexicographic_certificate_equispacedIntervalCutpoint
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (limitingValue : ℝ) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ
              (equispacedIntervalCutpoint (m + 2))
              (monotone_equispacedIntervalCutpoint (m + 2))
              (fun _ : Fin (m + 2) => (1 : ℝ)) levels hlevels
              (fun _ : ℝ × ℝ => (1 : ℝ)))
            (binaryEndpointAwareAdjacentRateObjective levels
              (fun _ : Fin (m + 2) => (1 : ℝ))) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun _candidate : Fin (m + 2) → ℝ => limitingValue)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate
                (fun _ : Fin (m + 2) => (1 : ℝ)))
            levels := by
  refine
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate_const_weight_of_cell_midpoints
      μ hm (equispacedIntervalCutpoint (m + 2))
      (monotone_equispacedIntervalCutpoint (m + 2)) ?_
      (fun _ : Fin (m + 2) => (1 : ℝ)) ?_ ?_ limitingValue
  · intro i _hi
    exact equispacedIntervalCutpoint_strict_adjacent (M := m + 2) (by omega) i
  · intro k hk
    rw [binaryEndpointSampleRateNat_of_lt (fun _ : Fin (m + 2) => (1 : ℝ)) hk]
    norm_num
  · intro _a _b _hab
    norm_num

/--
Uniform adjacent gaps determine the equispaced cutpoints on the finite
partition range.
-/
theorem intervalCutpoints_eq_equispacedIntervalCutpoint_of_uniform_gap
    {M : ℕ} (s : ℕ → ℝ) (h0 : s 0 = 0)
    (hgap : ∀ i : Fin M, s (i.1 + 1) - s i.1 = (M : ℝ)⁻¹) :
    ∀ k : ℕ, k ≤ M → s k = equispacedIntervalCutpoint M k := by
  intro k hk
  have hsum :
      (∑ r ∈ Finset.range k, (s (r + 1) - s r)) =
        ∑ _r ∈ Finset.range k, (M : ℝ)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hr_lt_M : r < M := (Finset.mem_range.mp hr).trans_le hk
    simpa using hgap ⟨r, hr_lt_M⟩
  have htel :
      (∑ r ∈ Finset.range k, (s (r + 1) - s r)) = s k := by
    simpa [h0] using AppliedModelingLib.sum_range_adjacent_sub s k
  calc
    s k = ∑ r ∈ Finset.range k, (s (r + 1) - s r) := htel.symm
    _ = ∑ _r ∈ Finset.range k, (M : ℝ)⁻¹ := hsum
    _ = equispacedIntervalCutpoint M k := by
      simp [equispacedIntervalCutpoint, div_eq_mul_inv, mul_comm]

/-- Endpoint feasibility for interval cutpoints on `[0,1]`. -/
def intervalCutpointsEndpointFeasible (M : ℕ) (s : ℕ → ℝ) : Prop :=
  s 0 = 0 ∧ s M = 1

/-- Monotone endpoint feasibility for interval cutpoints on `[0,1]`. -/
def monotoneIntervalCutpointsEndpointFeasible (M : ℕ) (s : ℕ → ℝ) : Prop :=
  Monotone s ∧ intervalCutpointsEndpointFeasible M s

/-- Adjacent gap vector induced by a finite cutpoint chain. -/
def intervalCutpointAdjacentGap (M : ℕ) (s : ℕ → ℝ) : Fin M → ℝ :=
  AppliedModelingLib.finiteAdjacentGap M s

/--
Every monotone endpoint-feasible cutpoint chain induces a finite probability
simplex of adjacent gaps.
-/
theorem finiteProbabilitySimplex_intervalCutpointAdjacentGap_of_monotoneIntervalCutpointsEndpointFeasible
    {M : ℕ} (s : ℕ → ℝ)
    (hs : monotoneIntervalCutpointsEndpointFeasible M s) :
    AppliedModelingLib.FiniteProbabilitySimplex
      (intervalCutpointAdjacentGap M s) := by
  exact
    AppliedModelingLib.finiteProbabilitySimplex_finiteAdjacentGap_of_monotone_endpoint
      s hs.1 hs.2.1 hs.2.2

/--
The prefix cutpoints induced by the adjacent gaps of a finite cutpoint chain
recover the original cutpoints on the finite source range.
-/
theorem finiteGapCutpoint_intervalCutpointAdjacentGap_eq
    {M : ℕ} (s : ℕ → ℝ) (h0 : s 0 = 0) :
    ∀ k : ℕ, k ≤ M →
      AppliedModelingLib.FiniteSum.finiteGapCutpoint
          (intervalCutpointAdjacentGap M s) k = s k :=
  AppliedModelingLib.finiteGapCutpoint_finiteAdjacentGap_eq s h0

/--
Finite simplex gap vectors induce monotone interval cutpoints with endpoints
`0` and `1`.  This is the gap-domain adapter used to turn compact simplex
optimizers into the paper's interval-cutpoint convention.
-/
theorem monotoneIntervalCutpointsEndpointFeasible_finiteGapCutpoint_of_finiteProbabilitySimplex
    {M : ℕ} (gap : Fin M → ℝ)
    (hgap : AppliedModelingLib.FiniteProbabilitySimplex gap) :
    monotoneIntervalCutpointsEndpointFeasible M
      (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) := by
  refine ⟨?_, ?_⟩
  · exact
      AppliedModelingLib.FiniteSum.finiteGapCutpoint_monotone_of_nonneg gap hgap.1
  · refine ⟨?_, ?_⟩
    · exact AppliedModelingLib.FiniteSum.finiteGapCutpoint_zero gap
    · rw [AppliedModelingLib.FiniteSum.finiteGapCutpoint_self_eq_sum gap]
      exact hgap.2

/--
Positive simplex gap vectors give the paper's monotone cutpoint convention and
strictly positive adjacent cells.  This is the finite-gap representation used by
the C.3/C.4 endpoint-partition arguments.
-/
theorem monotoneIntervalCutpointsEndpointFeasible_finiteGapCutpoint_strict_adjacent_of_pos
    {M : ℕ} (gap : Fin M → ℝ)
    (hgap : AppliedModelingLib.FiniteProbabilitySimplex gap)
    (hgap_pos : ∀ i : Fin M, 0 < gap i) :
    monotoneIntervalCutpointsEndpointFeasible M
        (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) ∧
      ∀ i : Fin M,
        AppliedModelingLib.FiniteSum.finiteGapCutpoint gap i.1 <
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap (i.1 + 1) := by
  refine ⟨?_, ?_⟩
  · exact
      monotoneIntervalCutpointsEndpointFeasible_finiteGapCutpoint_of_finiteProbabilitySimplex
        gap hgap
  · intro i
    exact
      AppliedModelingLib.FiniteSum.finiteGapCutpoint_strict_adjacent_of_pos
        gap hgap_pos i.2

/--
A cutpoint functional is source-finite if it only depends on the displayed
finite cutpoint range `0, ..., M`.  This is the source-shaped extensionality
condition for limiting-value objectives written from interval cutpoints.
-/
def cutpointFunctionalDependsOnlyOnRange
    (M : ℕ) (functional : (ℕ → ℝ) → ℝ) : Prop :=
  ∀ S T : ℕ → ℝ,
    (∀ k : ℕ, k ≤ M → S k = T k) → functional S = functional T

/--
Range-dependence supplies the finite-gap extensionality hypothesis used by the
compact-simplex cutpoint optimizer.
-/
theorem cutpointFunctionalDependsOnlyOnRange.value_extensional
    {M : ℕ} {functional : (ℕ → ℝ) → ℝ}
    (hdepends : cutpointFunctionalDependsOnlyOnRange M functional) :
    ∀ (S : ℕ → ℝ) (gap : Fin M → ℝ),
      monotoneIntervalCutpointsEndpointFeasible M S →
      (∀ k : ℕ, k ≤ M →
        AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k = S k) →
      functional (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) =
        functional S := by
  intro S gap _hS hrecover
  exact hdepends (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) S hrecover

/--
Lift a finite-vector objective on the displayed cutpoints `0, ..., M` to a
source-shaped cutpoint functional on `ℕ → ℝ`.  This is the direct interface for
paper objectives that are written as finite sums or finite-vector formulas in
the cutpoints.
-/
def cutpointRangeFunctional
    (M : ℕ) (finiteFunctional : (Fin (M + 1) → ℝ) → ℝ)
    (S : ℕ → ℝ) : ℝ :=
  finiteFunctional (fun i : Fin (M + 1) => S i.1)

/-- Read a displayed cutpoint from a finite cutpoint vector, defaulting to `0`
outside the displayed source range. -/
def finiteCutpointVectorEval
    (M : ℕ) (v : Fin (M + 1) → ℝ) (i : ℕ) : ℝ :=
  if h : i ≤ M then v ⟨i, Nat.lt_succ_of_le h⟩ else 0

/--
Finite-vector Kendall ordered-pair objective.  This is the continuous
finite-dimensional version of
`kendallConstantWeightOrderedPairIntervalObjective` used by the `S*`
compact-simplex bridge.
-/
noncomputable def kendallConstantWeightOrderedPairFiniteObjective
    (M : ℕ) (v : Fin (M + 1) → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin M,
    if i < j then
      (finiteCutpointVectorEval M v (i.1 + 1) -
          finiteCutpointVectorEval M v i.1) *
        (finiteCutpointVectorEval M v (j.1 + 1) -
          finiteCutpointVectorEval M v j.1)
    else 0

/--
Finite-vector Spearman ordered-pair objective.  This is the continuous
finite-dimensional version of
`spearmanLinearWeightOrderedPairIntervalObjective` used by the `S*`
compact-simplex bridge.
-/
noncomputable def spearmanLinearWeightOrderedPairFiniteObjective
    (M : ℕ) (v : Fin (M + 1) → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if i < j then
      (((finiteCutpointVectorEval M v (j + 1) +
            finiteCutpointVectorEval M v j) / 2) -
          ((finiteCutpointVectorEval M v (i + 1) +
            finiteCutpointVectorEval M v i) / 2)) *
        (finiteCutpointVectorEval M v (i + 1) -
          finiteCutpointVectorEval M v i) *
        (finiteCutpointVectorEval M v (j + 1) -
          finiteCutpointVectorEval M v j)
    else 0

/--
Finite-vector midpoint-weighted ordered-pair objective.  This is the
continuous finite-dimensional version of
`midpointWeightedOrderedPairIntervalObjective`.
-/
noncomputable def midpointWeightedOrderedPairFiniteObjective
    (M : ℕ) (weight : ℝ × ℝ → ℝ) (v : Fin (M + 1) → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if i < j then
      weight
          (((finiteCutpointVectorEval M v (i + 1) +
              finiteCutpointVectorEval M v i) / 2),
            ((finiteCutpointVectorEval M v (j + 1) +
              finiteCutpointVectorEval M v j) / 2)) *
        (finiteCutpointVectorEval M v (i + 1) -
          finiteCutpointVectorEval M v i) *
        (finiteCutpointVectorEval M v (j + 1) -
          finiteCutpointVectorEval M v j)
    else 0

/-- Spearman's finite-vector objective is the midpoint-weighted objective with linear distance weight. -/
theorem midpointWeightedOrderedPairFiniteObjective_linearDistance_eq_spearman
    (M : ℕ) :
    midpointWeightedOrderedPairFiniteObjective M
        (fun q : ℝ × ℝ => q.2 - q.1) =
      spearmanLinearWeightOrderedPairFiniteObjective M := by
  funext v
  unfold midpointWeightedOrderedPairFiniteObjective
    spearmanLinearWeightOrderedPairFiniteObjective
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]

/--
Generic finite ordered-pair cutpoint objective.  Each ordered-pair summand is
allowed to be any continuous finite-vector expression in the displayed
cutpoints.
-/
noncomputable def finiteOrderedPairCutpointObjective
    (M : ℕ)
    (term : Fin M → Fin M → (Fin (M + 1) → ℝ) → ℝ)
    (v : Fin (M + 1) → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin M,
    if i < j then term i j v else 0

/-- Kendall's finite-vector objective is an instance of the generic ordered-pair wrapper. -/
theorem finiteOrderedPairCutpointObjective_kendallGapTerm
    (M : ℕ) :
    finiteOrderedPairCutpointObjective M
        (fun i j : Fin M => fun v : Fin (M + 1) → ℝ =>
          (finiteCutpointVectorEval M v (i.1 + 1) -
              finiteCutpointVectorEval M v i.1) *
            (finiteCutpointVectorEval M v (j.1 + 1) -
              finiteCutpointVectorEval M v j.1)) =
      kendallConstantWeightOrderedPairFiniteObjective M := by
  funext v
  unfold finiteOrderedPairCutpointObjective
    kendallConstantWeightOrderedPairFiniteObjective
  rfl

/-- The generic ordered-pair wrapper specializes to the finite midpoint-weighted objective. -/
theorem finiteOrderedPairCutpointObjective_midpointWeightedTerm
    (M : ℕ) (weight : ℝ × ℝ → ℝ) :
    finiteOrderedPairCutpointObjective M
        (fun i j : Fin M => fun v : Fin (M + 1) → ℝ =>
          weight
            (((finiteCutpointVectorEval M v (i.1 + 1) +
                finiteCutpointVectorEval M v i.1) / 2),
              ((finiteCutpointVectorEval M v (j.1 + 1) +
                finiteCutpointVectorEval M v j.1) / 2)) *
            (finiteCutpointVectorEval M v (i.1 + 1) -
              finiteCutpointVectorEval M v i.1) *
            (finiteCutpointVectorEval M v (j.1 + 1) -
              finiteCutpointVectorEval M v j.1)) =
      midpointWeightedOrderedPairFiniteObjective M weight := by
  funext v
  unfold finiteOrderedPairCutpointObjective
    midpointWeightedOrderedPairFiniteObjective
  change
    (∑ i : Fin M, ∑ j : Fin M,
      if i.1 < j.1 then
        weight
          (((finiteCutpointVectorEval M v (i.1 + 1) +
              finiteCutpointVectorEval M v i.1) / 2),
            ((finiteCutpointVectorEval M v (j.1 + 1) +
              finiteCutpointVectorEval M v j.1) / 2)) *
          (finiteCutpointVectorEval M v (i.1 + 1) -
            finiteCutpointVectorEval M v i.1) *
          (finiteCutpointVectorEval M v (j.1 + 1) -
            finiteCutpointVectorEval M v j.1)
      else 0) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        if i < j then
          weight
            (((finiteCutpointVectorEval M v (i + 1) +
                finiteCutpointVectorEval M v i) / 2),
              ((finiteCutpointVectorEval M v (j + 1) +
                finiteCutpointVectorEval M v j) / 2)) *
            (finiteCutpointVectorEval M v (i + 1) -
              finiteCutpointVectorEval M v i) *
            (finiteCutpointVectorEval M v (j + 1) -
              finiteCutpointVectorEval M v j)
        else 0
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      ∑ j : Fin M,
        if i < j.1 then
          weight
            (((finiteCutpointVectorEval M v (i + 1) +
                finiteCutpointVectorEval M v i) / 2),
              ((finiteCutpointVectorEval M v (j.1 + 1) +
                finiteCutpointVectorEval M v j.1) / 2)) *
            (finiteCutpointVectorEval M v (i + 1) -
              finiteCutpointVectorEval M v i) *
            (finiteCutpointVectorEval M v (j.1 + 1) -
              finiteCutpointVectorEval M v j.1)
        else 0) M]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ =>
      if i < j then
        weight
          (((finiteCutpointVectorEval M v (i + 1) +
              finiteCutpointVectorEval M v i) / 2),
            ((finiteCutpointVectorEval M v (j + 1) +
              finiteCutpointVectorEval M v j) / 2)) *
          (finiteCutpointVectorEval M v (i + 1) -
            finiteCutpointVectorEval M v i) *
          (finiteCutpointVectorEval M v (j + 1) -
            finiteCutpointVectorEval M v j)
      else 0) M]

/--
A functional lifted from the finite displayed cutpoint vector automatically
has the source-finite dependence property needed by the compact-simplex bridge.
-/
theorem cutpointFunctionalDependsOnlyOnRange_cutpointRangeFunctional
    (M : ℕ) (finiteFunctional : (Fin (M + 1) → ℝ) → ℝ) :
    cutpointFunctionalDependsOnlyOnRange M
      (cutpointRangeFunctional M finiteFunctional) := by
  intro S T hsame
  unfold cutpointRangeFunctional
  congr
  funext i
  exact hsame i.1 (Nat.le_of_lt_succ i.2)

/-- Evaluating a fixed displayed coordinate of a finite cutpoint vector is continuous. -/
theorem continuous_finiteCutpointVectorEval
    (M i : ℕ) :
    Continuous
      (fun v : Fin (M + 1) → ℝ => finiteCutpointVectorEval M v i) := by
  unfold finiteCutpointVectorEval
  by_cases h : i ≤ M
  · simpa [h] using
      (continuous_apply (⟨i, Nat.lt_succ_of_le h⟩ : Fin (M + 1)) :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            v ⟨i, Nat.lt_succ_of_le h⟩))
  · simpa [h] using
      (continuous_const :
        Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))

/-- The finite-vector Kendall ordered-pair objective is continuous. -/
theorem continuous_kendallConstantWeightOrderedPairFiniteObjective
    (M : ℕ) :
    Continuous (kendallConstantWeightOrderedPairFiniteObjective M) := by
  unfold kendallConstantWeightOrderedPairFiniteObjective
  refine continuous_finset_sum Finset.univ ?_
  intro i _hi
  refine continuous_finset_sum Finset.univ ?_
  intro j _hj
  by_cases hij : i < j
  · have hi :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            finiteCutpointVectorEval M v (i.1 + 1) -
              finiteCutpointVectorEval M v i.1) :=
      (continuous_finiteCutpointVectorEval M (i.1 + 1)).sub
        (continuous_finiteCutpointVectorEval M i.1)
    have hj :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            finiteCutpointVectorEval M v (j.1 + 1) -
              finiteCutpointVectorEval M v j.1) :=
      (continuous_finiteCutpointVectorEval M (j.1 + 1)).sub
        (continuous_finiteCutpointVectorEval M j.1)
    simpa [hij] using hi.mul hj
  · simpa [hij] using
      (continuous_const :
        Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))

/-- The finite-vector Spearman ordered-pair objective is continuous. -/
theorem continuous_spearmanLinearWeightOrderedPairFiniteObjective
    (M : ℕ) :
    Continuous (spearmanLinearWeightOrderedPairFiniteObjective M) := by
  unfold spearmanLinearWeightOrderedPairFiniteObjective
  refine continuous_finset_sum (Finset.range M) ?_
  intro i _hi
  refine continuous_finset_sum (Finset.range M) ?_
  intro j _hj
  by_cases hij : i < j
  · have hleft :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            (finiteCutpointVectorEval M v (j + 1) +
                finiteCutpointVectorEval M v j) / 2 -
              (finiteCutpointVectorEval M v (i + 1) +
                finiteCutpointVectorEval M v i) / 2) := by
      exact
        (((continuous_finiteCutpointVectorEval M (j + 1)).add
            (continuous_finiteCutpointVectorEval M j)).div_const 2).sub
          (((continuous_finiteCutpointVectorEval M (i + 1)).add
              (continuous_finiteCutpointVectorEval M i)).div_const 2)
    have hi :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            finiteCutpointVectorEval M v (i + 1) -
              finiteCutpointVectorEval M v i) :=
      (continuous_finiteCutpointVectorEval M (i + 1)).sub
        (continuous_finiteCutpointVectorEval M i)
    have hj :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            finiteCutpointVectorEval M v (j + 1) -
              finiteCutpointVectorEval M v j) :=
      (continuous_finiteCutpointVectorEval M (j + 1)).sub
        (continuous_finiteCutpointVectorEval M j)
    simpa [hij, mul_assoc] using (hleft.mul hi).mul hj
  · simpa [hij] using
      (continuous_const :
        Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))

/-- The finite-vector midpoint-weighted ordered-pair objective is continuous. -/
theorem continuous_midpointWeightedOrderedPairFiniteObjective
    (M : ℕ) {weight : ℝ × ℝ → ℝ} (hweight : Continuous weight) :
    Continuous (midpointWeightedOrderedPairFiniteObjective M weight) := by
  unfold midpointWeightedOrderedPairFiniteObjective
  refine continuous_finset_sum (Finset.range M) ?_
  intro i _hi
  refine continuous_finset_sum (Finset.range M) ?_
  intro j _hj
  by_cases hij : i < j
  · have hmid_i :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            (finiteCutpointVectorEval M v (i + 1) +
                finiteCutpointVectorEval M v i) / 2) :=
      ((continuous_finiteCutpointVectorEval M (i + 1)).add
        (continuous_finiteCutpointVectorEval M i)).div_const 2
    have hmid_j :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            (finiteCutpointVectorEval M v (j + 1) +
                finiteCutpointVectorEval M v j) / 2) :=
      ((continuous_finiteCutpointVectorEval M (j + 1)).add
        (continuous_finiteCutpointVectorEval M j)).div_const 2
    have hweight_eval :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            weight
              (((finiteCutpointVectorEval M v (i + 1) +
                    finiteCutpointVectorEval M v i) / 2),
                ((finiteCutpointVectorEval M v (j + 1) +
                    finiteCutpointVectorEval M v j) / 2))) :=
      hweight.comp (hmid_i.prodMk hmid_j)
    have hi :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            finiteCutpointVectorEval M v (i + 1) -
              finiteCutpointVectorEval M v i) :=
      (continuous_finiteCutpointVectorEval M (i + 1)).sub
        (continuous_finiteCutpointVectorEval M i)
    have hj :
        Continuous
          (fun v : Fin (M + 1) → ℝ =>
            finiteCutpointVectorEval M v (j + 1) -
              finiteCutpointVectorEval M v j) :=
      (continuous_finiteCutpointVectorEval M (j + 1)).sub
        (continuous_finiteCutpointVectorEval M j)
    simpa [hij, mul_assoc] using (hweight_eval.mul hi).mul hj
  · simpa [hij] using
      (continuous_const :
        Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))

/-- A finite ordered-pair objective is continuous when every displayed summand is continuous. -/
theorem continuous_finiteOrderedPairCutpointObjective
    (M : ℕ)
    {term : Fin M → Fin M → (Fin (M + 1) → ℝ) → ℝ}
    (hterm : ∀ i j : Fin M, Continuous (term i j)) :
    Continuous (finiteOrderedPairCutpointObjective M term) := by
  unfold finiteOrderedPairCutpointObjective
  refine continuous_finset_sum Finset.univ ?_
  intro i _hi
  refine continuous_finset_sum Finset.univ ?_
  intro j _hj
  by_cases hij : i < j
  · simpa [hij] using hterm i j
  · simpa [hij] using
      (continuous_const :
        Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))

/--
The finite-vector Kendall objective agrees with the source cutpoint objective
after lifting through `cutpointRangeFunctional`.
-/
theorem cutpointRangeFunctional_kendallConstantWeightOrderedPairFiniteObjective
    (M : ℕ) :
    cutpointRangeFunctional M
        (kendallConstantWeightOrderedPairFiniteObjective M) =
      kendallConstantWeightOrderedPairIntervalObjective M := by
  funext S
  unfold cutpointRangeFunctional
    kendallConstantWeightOrderedPairFiniteObjective
    kendallConstantWeightOrderedPairIntervalObjective
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hi0 : i.1 ≤ M := Nat.le_of_lt i.2
  have hi1 : i.1 + 1 ≤ M := Nat.succ_le_iff.mpr i.2
  have hj0 : j.1 ≤ M := Nat.le_of_lt j.2
  have hj1 : j.1 + 1 ≤ M := Nat.succ_le_iff.mpr j.2
  simp [finiteCutpointVectorEval, hi0, hi1, hj0, hj1]

/--
The finite-vector Spearman objective agrees with the source cutpoint objective
after lifting through `cutpointRangeFunctional`.
-/
theorem cutpointRangeFunctional_spearmanLinearWeightOrderedPairFiniteObjective
    (M : ℕ) :
    cutpointRangeFunctional M
        (spearmanLinearWeightOrderedPairFiniteObjective M) =
      spearmanLinearWeightOrderedPairIntervalObjective M := by
  funext S
  unfold cutpointRangeFunctional
    spearmanLinearWeightOrderedPairFiniteObjective
    spearmanLinearWeightOrderedPairIntervalObjective
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hi0 : i ≤ M := Nat.le_of_lt (Finset.mem_range.mp hi)
  have hi1 : i + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
  have hj0 : j ≤ M := Nat.le_of_lt (Finset.mem_range.mp hj)
  have hj1 : j + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
  simp [finiteCutpointVectorEval, hi0, hi1, hj0, hj1]

/--
The finite-vector midpoint-weighted objective agrees with the source
cutpoint objective after lifting through `cutpointRangeFunctional`.
-/
theorem cutpointRangeFunctional_midpointWeightedOrderedPairFiniteObjective
    (M : ℕ) (weight : ℝ × ℝ → ℝ) :
    cutpointRangeFunctional M
        (midpointWeightedOrderedPairFiniteObjective M weight) =
      midpointWeightedOrderedPairIntervalObjective M weight := by
  funext S
  unfold cutpointRangeFunctional
    midpointWeightedOrderedPairFiniteObjective
    midpointWeightedOrderedPairIntervalObjective
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hi0 : i ≤ M := Nat.le_of_lt (Finset.mem_range.mp hi)
  have hi1 : i + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
  have hj0 : j ≤ M := Nat.le_of_lt (Finset.mem_range.mp hj)
  have hj1 : j + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
  simp [finiteCutpointVectorEval, hi0, hi1, hj0, hj1]

/--
The generic finite ordered-pair wrapper, once lifted back to the source
cutpoint convention, is exactly the midpoint-weighted ordered-pair interval
objective for the corresponding midpoint summand.  This composes the generic
finite wrapper with the source-range lift used in the `S*` optimizer layer.
-/
theorem cutpointRangeFunctional_finiteOrderedPairCutpointObjective_midpointWeightedTerm
    (M : ℕ) (weight : ℝ × ℝ → ℝ) :
    cutpointRangeFunctional M
        (finiteOrderedPairCutpointObjective M
          (fun i j : Fin M => fun v : Fin (M + 1) → ℝ =>
            weight
              (((finiteCutpointVectorEval M v (i.1 + 1) +
                  finiteCutpointVectorEval M v i.1) / 2),
                ((finiteCutpointVectorEval M v (j.1 + 1) +
                  finiteCutpointVectorEval M v j.1) / 2)) *
              (finiteCutpointVectorEval M v (i.1 + 1) -
                finiteCutpointVectorEval M v i.1) *
              (finiteCutpointVectorEval M v (j.1 + 1) -
                finiteCutpointVectorEval M v j.1))) =
      midpointWeightedOrderedPairIntervalObjective M weight := by
  rw [finiteOrderedPairCutpointObjective_midpointWeightedTerm,
    cutpointRangeFunctional_midpointWeightedOrderedPairFiniteObjective]

/--
Each displayed finite-gap cutpoint is a continuous function of the finite gap
vector.  This is the analytic bridge from a continuous finite-vector source
objective to the finite-simplex continuity hypothesis used by compactness.
-/
theorem continuous_finiteGapCutpoint_eval
    {M : ℕ} (i : ℕ) :
    Continuous
      (fun gap : Fin M → ℝ =>
        AppliedModelingLib.FiniteSum.finiteGapCutpoint gap i) := by
  unfold AppliedModelingLib.FiniteSum.finiteGapCutpoint
    AppliedModelingLib.FiniteSum.finitePartitionPrefix
  exact continuous_finset_sum (Finset.range i) (fun k _hk => by
    by_cases hkM : k < M
    · simpa [AppliedModelingLib.FiniteSum.finiteGapExtend, hkM] using
        (continuous_apply (⟨k, hkM⟩ : Fin M) :
          Continuous (fun gap : Fin M → ℝ => gap ⟨k, hkM⟩))
    · simpa [AppliedModelingLib.FiniteSum.finiteGapExtend, hkM] using
        (continuous_const :
          Continuous (fun _gap : Fin M → ℝ => (0 : ℝ))))

/--
The finite vector of displayed cutpoints `0, ..., M` is continuous as a
function of the finite gap vector.
-/
theorem continuous_finiteGapCutpoint_vector
    {M : ℕ} :
    Continuous
      (fun gap : Fin M → ℝ =>
        fun i : Fin (M + 1) =>
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap i.1) :=
  continuous_pi (fun i => continuous_finiteGapCutpoint_eval i.1)

/--
Theorem 3.1 finite-gap image form.  The compact finite-simplex optimizer can be
read directly as an optimizer over cutpoints induced by finite gaps.
-/
theorem theorem31_exists_finiteGapCutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
    {M : ℕ} [Nonempty (Fin M)] {Endpoint : Type*}
    (endpointFeasible : (ℕ → ℝ) → Endpoint → Prop)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → Endpoint → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin M → ℝ =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hendpoint :
      ∀ gap : Fin M → ℝ, AppliedModelingLib.FiniteProbabilitySimplex gap →
        ∃ tstar : Endpoint,
          endpointFeasible (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap)
            tstar ∧
            ∀ (otherGap : Fin M → ℝ) (t : Endpoint),
              AppliedModelingLib.FiniteProbabilitySimplex otherGap →
              endpointFeasible
                (AppliedModelingLib.FiniteSum.finiteGapCutpoint otherGap) t →
              limitingValue
                  (AppliedModelingLib.FiniteSum.finiteGapCutpoint otherGap) =
                  limitingValue
                    (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) →
                  rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint otherGap) t ≤
                    rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) tstar) :
    ∃ design : (Fin M → ℝ) × Endpoint,
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin M → ℝ) × Endpoint =>
          AppliedModelingLib.FiniteProbabilitySimplex design.1 ∧
            endpointFeasible
              (AppliedModelingLib.FiniteSum.finiteGapCutpoint design.1) design.2)
        (fun design : (Fin M → ℝ) × Endpoint =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint design.1))
        (fun design : (Fin M → ℝ) × Endpoint =>
          rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint design.1) design.2)
        design :=
  theorem31_exists_gap_partition_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
    (fun gap t =>
      endpointFeasible (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) t)
    (fun gap =>
      limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
    (fun gap t =>
      rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) t)
    hcontinuous hendpoint

/--
Theorem 3.1 cutpoint argmax existence bridge.  A continuous limiting-value
objective on the finite probability simplex attains an optimizer, and finite
range extensionality transports that optimizer to the paper's cutpoint-chain
feasible region.  This supplies the `S* = arg max ...` source convention used
by the staged Theorem 3.1 wrappers.
-/
theorem theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex
    {M : ℕ} [Nonempty (Fin M)]
    (limitingValue : (ℕ → ℝ) → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin M → ℝ =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hvalue_extensional :
      ∀ (S : ℕ → ℝ) (gap : Fin M → ℝ),
        monotoneIntervalCutpointsEndpointFeasible M S →
        (∀ k : ℕ, k ≤ M →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k = S k) →
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) =
          limitingValue S) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        limitingValue Sstar := by
  rcases
    AppliedModelingLib.Optimization.exists_isMaximizerOn_of_isCompact_continuousOn
      AppliedModelingLib.finiteProbabilitySimplex_isCompact
      AppliedModelingLib.finiteProbabilitySimplex_nonempty
      (fun gap : Fin M → ℝ =>
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
      hcontinuous with
    ⟨gapstar, hgapstar⟩
  let Sstar : ℕ → ℝ :=
    AppliedModelingLib.FiniteSum.finiteGapCutpoint gapstar
  refine ⟨Sstar, ?_⟩
  constructor
  · exact
      monotoneIntervalCutpointsEndpointFeasible_finiteGapCutpoint_of_finiteProbabilitySimplex
        gapstar hgapstar.1
  · intro S hS
    let altGap : Fin M → ℝ :=
      intervalCutpointAdjacentGap M S
    have haltGap :
        AppliedModelingLib.FiniteProbabilitySimplex altGap :=
      finiteProbabilitySimplex_intervalCutpointAdjacentGap_of_monotoneIntervalCutpointsEndpointFeasible
        S hS
    have hrecover :
        ∀ k : ℕ, k ≤ M →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap k = S k :=
      finiteGapCutpoint_intervalCutpointAdjacentGap_eq S hS.2.1
    have hvalue :
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap) =
          limitingValue S :=
      hvalue_extensional S altGap hS hrecover
    have hle :
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap) ≤
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gapstar) :=
      hgapstar.2 altGap haltGap
    calc
      limitingValue S =
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap) :=
        hvalue.symm
      _ ≤ limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gapstar) :=
        hle
      _ = limitingValue Sstar := rfl

/--
Theorem 3.1 cutpoint argmax existence with source-shaped finite-range
extensionality.  A continuous limiting-value objective on the finite simplex
attains an optimizer whenever the source objective depends only on the finite
cutpoint range `0, ..., M`.
-/
theorem theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange
    {M : ℕ} [Nonempty (Fin M)]
    (limitingValue : (ℕ → ℝ) → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin M → ℝ =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hdepends :
      cutpointFunctionalDependsOnlyOnRange M limitingValue) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        limitingValue Sstar :=
  theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex
    limitingValue hcontinuous
    (cutpointFunctionalDependsOnlyOnRange.value_extensional hdepends)

/--
Theorem 3.1 cutpoint argmax existence for a finite-vector objective.  This
specializes the source-finite bridge to objectives expressed directly as a
function of the displayed cutpoints `0, ..., M`.
-/
theorem theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
    {M : ℕ} [Nonempty (Fin M)]
    (finiteFunctional : (Fin (M + 1) → ℝ) → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin M → ℝ =>
          cutpointRangeFunctional M finiteFunctional
            (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap}) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (cutpointRangeFunctional M finiteFunctional) Sstar :=
  theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange
    (cutpointRangeFunctional M finiteFunctional) hcontinuous
    (cutpointFunctionalDependsOnlyOnRange_cutpointRangeFunctional M
      finiteFunctional)

/--
Theorem 3.1 cutpoint argmax existence for a continuous finite-vector
objective.  Continuity of the finite objective itself implies the composed
finite-simplex continuity premise because finite-gap cutpoints are continuous
in the gap vector.
-/
theorem theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
    {M : ℕ} [Nonempty (Fin M)]
    (finiteFunctional : (Fin (M + 1) → ℝ) → ℝ)
    (hcontinuous : Continuous finiteFunctional) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (cutpointRangeFunctional M finiteFunctional) Sstar := by
  have hcontinuousOn :
      ContinuousOn
        (fun gap : Fin M → ℝ =>
          cutpointRangeFunctional M finiteFunctional
            (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap} := by
    simpa [cutpointRangeFunctional] using
      (hcontinuous.comp (continuous_finiteGapCutpoint_vector (M := M))).continuousOn
  exact
    theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
      finiteFunctional hcontinuousOn

/-- Weight integral over ordered cell pairs excluding the bottom-to-top pair. This is the nontrivial-error component weight, not the full cross-cell primary value. -/
noncomputable def nontrivialCellWeightFiniteObjective
    (μ : Measure ℝ) (m : ℕ) (weight : ℝ × ℝ → ℝ)
    (v : Fin ((m + 2) + 1) → ℝ) : ℝ :=
  ∑ component : theorem31OrderedNontrivialPairComponent m,
    ∫ q in
      (Set.Ioc
          (finiteCutpointVectorEval (m + 2) v component.val.1.val)
          (finiteCutpointVectorEval (m + 2) v (component.val.1.val + 1)) ×ˢ
        Set.Ioc
          (finiteCutpointVectorEval (m + 2) v component.val.2.val)
          (finiteCutpointVectorEval (m + 2) v (component.val.2.val + 1))),
      weight q ∂(μ.prod μ)

/-- For constant Lebesgue weight, the nontrivial-cell weight equals the sum of its rectangle areas. -/
theorem nontrivialCellWeightFiniteObjective_volume_const_eq_gapProduct
    (m : ℕ) :
    nontrivialCellWeightFiniteObjective volume m
        (fun _q : ℝ × ℝ => (1 : ℝ)) =
      fun v : Fin ((m + 2) + 1) → ℝ =>
        ∑ component : theorem31OrderedNontrivialPairComponent m,
          max
              (finiteCutpointVectorEval (m + 2) v
                  (component.val.1.val + 1) -
                finiteCutpointVectorEval (m + 2) v component.val.1.val)
              0 *
            max
              (finiteCutpointVectorEval (m + 2) v
                  (component.val.2.val + 1) -
                finiteCutpointVectorEval (m + 2) v component.val.2.val)
              0 := by
  funext v
  unfold nontrivialCellWeightFiniteObjective
  simp [MeasureTheory.measureReal_prod_prod]

/-- The constant-weight nontrivial-cell objective is continuous. -/
theorem continuous_nontrivialCellWeightFiniteObjective_volume_const
    (m : ℕ) :
    Continuous
      (nontrivialCellWeightFiniteObjective volume m
        (fun _q : ℝ × ℝ => (1 : ℝ))) := by
  rw [nontrivialCellWeightFiniteObjective_volume_const_eq_gapProduct]
  refine continuous_finset_sum Finset.univ ?_
  intro component _hcomponent
  have hfirst :
      Continuous
        (fun v : Fin ((m + 2) + 1) → ℝ =>
          max
            (finiteCutpointVectorEval (m + 2) v
                (component.val.1.val + 1) -
              finiteCutpointVectorEval (m + 2) v component.val.1.val)
            0) :=
    ((continuous_finiteCutpointVectorEval (m + 2)
        (component.val.1.val + 1)).sub
      (continuous_finiteCutpointVectorEval (m + 2)
        component.val.1.val)).max continuous_const
  have hsecond :
      Continuous
        (fun v : Fin ((m + 2) + 1) → ℝ =>
          max
            (finiteCutpointVectorEval (m + 2) v
                (component.val.2.val + 1) -
              finiteCutpointVectorEval (m + 2) v component.val.2.val)
            0) :=
    ((continuous_finiteCutpointVectorEval (m + 2)
        (component.val.2.val + 1)).sub
      (continuous_finiteCutpointVectorEval (m + 2)
        component.val.2.val)).max continuous_const
  exact hfirst.mul hsecond

/--
If a moving lower endpoint tends to `a₀`, then away from the boundary point
`a₀` the strict lower-membership test is eventually constant.
-/
theorem eventually_lt_const_iff_of_tendsto_of_ne
    {ι : Type*} {l : Filter ι} {a : ι → ℝ} {a₀ x : ℝ}
    (ha : Tendsto a l (𝓝 a₀)) (hne : x ≠ a₀) :
    ∀ᶠ i in l, (a i < x ↔ a₀ < x) := by
  by_cases hlt : a₀ < x
  · exact (ha.eventually (Iio_mem_nhds hlt)).mono fun _ hi =>
      ⟨fun _ => hlt, fun _ => hi⟩
  · have hxlt : x < a₀ := lt_of_le_of_ne (le_of_not_gt hlt) hne
    exact
      (ha.eventually (Ioi_mem_nhds hxlt)).mono fun _ hi =>
        ⟨fun h => (lt_asymm hi h).elim,
          fun h => (hlt h).elim⟩

/--
If a moving upper endpoint tends to `b₀`, then away from the boundary point
`b₀` the closed upper-membership test is eventually constant.
-/
theorem eventually_const_le_iff_of_tendsto_of_ne
    {ι : Type*} {l : Filter ι} {b : ι → ℝ} {b₀ x : ℝ}
    (hb : Tendsto b l (𝓝 b₀)) (hne : x ≠ b₀) :
    ∀ᶠ i in l, (x ≤ b i ↔ x ≤ b₀) := by
  by_cases hlt : x < b₀
  · exact
      (hb.eventually (Ioi_mem_nhds hlt)).mono fun _ hi =>
        ⟨fun _ => hlt.le, fun _ => hi.le⟩
  · have hblt : b₀ < x := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    exact
      (hb.eventually (Iio_mem_nhds hblt)).mono fun _ hi =>
        ⟨fun h => (not_le_of_gt hi h).elim,
          fun h => (not_le_of_gt hblt h).elim⟩

/--
For endpoints converging to `(a₀,b₀)`, membership in the moving half-open
interval is eventually the same as membership in the limiting interval at all
non-boundary points.
-/
theorem eventually_mem_Ioc_iff_of_tendsto_of_ne
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {a₀ b₀ x : ℝ}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hne_left : x ≠ a₀) (hne_right : x ≠ b₀) :
    ∀ᶠ i in l, (x ∈ Set.Ioc (a i) (b i) ↔ x ∈ Set.Ioc a₀ b₀) := by
  filter_upwards
    [eventually_lt_const_iff_of_tendsto_of_ne ha hne_left,
      eventually_const_le_iff_of_tendsto_of_ne hb hne_right] with i hleft hright
  simp [Set.mem_Ioc, hleft, hright]

/--
The moving rectangle membership test for products of half-open intervals is
eventually constant away from the four limiting boundary lines.
-/
theorem eventually_mem_Ioc_prod_iff_of_tendsto_of_ne
    {ι : Type*} {l : Filter ι}
    {a b c d : ι → ℝ} {a₀ b₀ c₀ d₀ : ℝ} {q : ℝ × ℝ}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀))
    (hne_a : q.1 ≠ a₀) (hne_b : q.1 ≠ b₀)
    (hne_c : q.2 ≠ c₀) (hne_d : q.2 ≠ d₀) :
    ∀ᶠ i in l,
      (q ∈ Set.Ioc (a i) (b i) ×ˢ Set.Ioc (c i) (d i) ↔
        q ∈ Set.Ioc a₀ b₀ ×ˢ Set.Ioc c₀ d₀) := by
  filter_upwards
    [eventually_mem_Ioc_iff_of_tendsto_of_ne ha hb hne_a hne_b,
      eventually_mem_Ioc_iff_of_tendsto_of_ne hc hd hne_c hne_d] with i hfirst hsecond
  simp [Set.mem_prod, hfirst, hsecond]

/--
Displayed finite-gap cutpoints from a simplex gap vector lie in the source
unit interval.
-/
theorem finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex
    {M : ℕ} (gap : Fin M → ℝ)
    (hgap : AppliedModelingLib.FiniteProbabilitySimplex gap)
    {k : ℕ} (hk : k ≤ M) :
    AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k ∈ Set.Icc (0 : ℝ) 1 := by
  have hfeasible :=
    monotoneIntervalCutpointsEndpointFeasible_finiteGapCutpoint_of_finiteProbabilitySimplex
      gap hgap
  constructor
  · calc
      0 = AppliedModelingLib.FiniteSum.finiteGapCutpoint gap 0 := by
        exact (AppliedModelingLib.FiniteSum.finiteGapCutpoint_zero gap).symm
      _ ≤ AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k := hfeasible.1 (Nat.zero_le k)
  · calc
      AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k ≤
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap M := hfeasible.1 hk
      _ = 1 := hfeasible.2.2

/--
Displayed entries of the finite cutpoint vector induced by simplex gaps lie in
the unit interval, with the out-of-range default also equal to `0`.
-/
theorem finiteCutpointVectorEval_finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex
    {M : ℕ} (gap : Fin M → ℝ)
    (hgap : AppliedModelingLib.FiniteProbabilitySimplex gap)
    (k : ℕ) :
    finiteCutpointVectorEval M
        (fun j : Fin (M + 1) =>
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1) k ∈
      Set.Icc (0 : ℝ) 1 := by
  unfold finiteCutpointVectorEval
  by_cases hk : k ≤ M
  · simpa [hk] using
      finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex gap hgap hk
  · simp [hk]

/--
Each finite-vector cell induced by a simplex gap vector is contained in the
source unit square.
-/
theorem finiteCutpointVectorEval_finiteGapCutpoint_Ioc_prod_subset_unit_square
    {M : ℕ} (gap : Fin M → ℝ)
    (hgap : AppliedModelingLib.FiniteProbabilitySimplex gap) (i j : ℕ) :
    Set.Ioc
        (finiteCutpointVectorEval M
          (fun k : Fin (M + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k.1) i)
        (finiteCutpointVectorEval M
          (fun k : Fin (M + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k.1) (i + 1)) ×ˢ
      Set.Ioc
        (finiteCutpointVectorEval M
          (fun k : Fin (M + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k.1) j)
        (finiteCutpointVectorEval M
          (fun k : Fin (M + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k.1) (j + 1)) ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  intro q hq
  constructor
  · have hleft :=
      finiteCutpointVectorEval_finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex
        gap hgap i
    have hright :=
      finiteCutpointVectorEval_finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex
        gap hgap (i + 1)
    exact ⟨le_trans hleft.1 hq.1.1.le, le_trans hq.1.2 hright.2⟩
  · have hleft :=
      finiteCutpointVectorEval_finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex
        gap hgap j
    have hright :=
      finiteCutpointVectorEval_finiteGapCutpoint_mem_Icc_of_finiteProbabilitySimplex
        gap hgap (j + 1)
    exact ⟨le_trans hleft.1 hq.2.1.le, le_trans hq.2.2 hright.2⟩

/--
Dominated-convergence continuity for one selected cell in equation (20).
The moving half-open rectangle is allowed to vary with a filter, provided all
moving rectangles eventually stay in the unit square and the limiting
rectangle itself is in the unit square.  The only regularity assumption on the
paper weight is integrability on `[0,1]^2`.
-/
theorem tendsto_integral_Ioc_prod_of_tendsto_of_integrableOn_Icc
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {a b c d : ι → ℝ} {a₀ b₀ c₀ d₀ : ℝ}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀))
    {weight : ℝ × ℝ → ℝ}
    (hweight_int :
      IntegrableOn weight
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
        (volume.prod volume))
    (hrect_subset :
      ∀ᶠ i in l,
        Set.Ioc (a i) (b i) ×ˢ Set.Ioc (c i) (d i) ⊆
          Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hrect0_subset :
      Set.Ioc a₀ b₀ ×ˢ Set.Ioc c₀ d₀ ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    Tendsto
      (fun i =>
        ∫ q in Set.Ioc (a i) (b i) ×ˢ Set.Ioc (c i) (d i),
          weight q ∂(volume.prod volume))
      l
      (𝓝 (∫ q in Set.Ioc a₀ b₀ ×ˢ Set.Ioc c₀ d₀,
          weight q ∂(volume.prod volume))) := by
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  let square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  let rect : ι → Set (ℝ × ℝ) :=
    fun i => Set.Ioc (a i) (b i) ×ˢ Set.Ioc (c i) (d i)
  let rect₀ : Set (ℝ × ℝ) := Set.Ioc a₀ b₀ ×ˢ Set.Ioc c₀ d₀
  have hsquare : MeasurableSet square := measurableSet_Icc.prod measurableSet_Icc
  have hrect_meas : ∀ i, MeasurableSet (rect i) := by
    intro i
    exact measurableSet_Ioc.prod measurableSet_Ioc
  have hrect₀_meas : MeasurableSet rect₀ := measurableSet_Ioc.prod measurableSet_Ioc
  have hweight_int_square : IntegrableOn weight square μ := by
    simpa [μ, square] using hweight_int
  have hweight_norm_int :
      IntegrableOn (fun q : ℝ × ℝ => ‖weight q‖) square μ :=
    hweight_int_square.norm
  have hbound_integrable :
      Integrable (square.indicator (fun q : ℝ × ℝ => ‖weight q‖)) μ :=
    hweight_norm_int.integrable_indicator hsquare
  have hmeas :
      ∀ᶠ i in l, AEStronglyMeasurable (fun q => (rect i).indicator weight q) μ := by
    filter_upwards [hrect_subset] with i hsub
    rw [aestronglyMeasurable_indicator_iff (hrect_meas i)]
    exact (hweight_int_square.mono_set hsub).aestronglyMeasurable
  have hbound :
      ∀ᶠ i in l,
        ∀ᵐ q ∂μ,
          ‖(rect i).indicator weight q‖ ≤
            square.indicator (fun q : ℝ × ℝ => ‖weight q‖) q := by
    filter_upwards [hrect_subset] with i hsub
    exact ae_of_all μ fun q => by
      rw [norm_indicator_eq_indicator_norm]
      by_cases hqrect : q ∈ rect i
      · have hqsquare : q ∈ square := hsub hqrect
        simp [Set.indicator_of_mem, hqrect, hqsquare]
      · by_cases hqsquare : q ∈ square
        · simp [Set.indicator_of_notMem, hqrect, Set.indicator_of_mem, hqsquare]
        · simp [Set.indicator_of_notMem, hqrect, hqsquare]
  have hline_a :
      μ {q : ℝ × ℝ | q.1 = a₀} = 0 := by
    change (volume.prod volume) {q : ℝ × ℝ | q.1 = a₀} = 0
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact AppliedModelingLib.volume_prod_vertical_line a₀
  have hline_b :
      μ {q : ℝ × ℝ | q.1 = b₀} = 0 := by
    change (volume.prod volume) {q : ℝ × ℝ | q.1 = b₀} = 0
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact AppliedModelingLib.volume_prod_vertical_line b₀
  have hline_c :
      μ {q : ℝ × ℝ | q.2 = c₀} = 0 := by
    change (volume.prod volume) {q : ℝ × ℝ | q.2 = c₀} = 0
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact AppliedModelingLib.volume_prod_horizontal_line c₀
  have hline_d :
      μ {q : ℝ × ℝ | q.2 = d₀} = 0 := by
    change (volume.prod volume) {q : ℝ × ℝ | q.2 = d₀} = 0
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact AppliedModelingLib.volume_prod_horizontal_line d₀
  have hne_a : ∀ᵐ q ∂μ, q.1 ≠ a₀ := by
    rw [ae_iff]
    simpa using hline_a
  have hne_b : ∀ᵐ q ∂μ, q.1 ≠ b₀ := by
    rw [ae_iff]
    simpa using hline_b
  have hne_c : ∀ᵐ q ∂μ, q.2 ≠ c₀ := by
    rw [ae_iff]
    simpa using hline_c
  have hne_d : ∀ᵐ q ∂μ, q.2 ≠ d₀ := by
    rw [ae_iff]
    simpa using hline_d
  have hlim :
      ∀ᵐ q ∂μ,
        Tendsto (fun i => (rect i).indicator weight q) l
          (𝓝 ((rect₀).indicator weight q)) := by
    filter_upwards [hne_a, hne_b, hne_c, hne_d] with q hqa hqb hqc hqd
    refine tendsto_const_nhds.congr' ?_
    exact
      (eventually_mem_Ioc_prod_iff_of_tendsto_of_ne
        (q := q) ha hb hc hd hqa hqb hqc hqd).mono fun i hmem => by
        by_cases hi : q ∈ rect i
        · have h₀ : q ∈ rect₀ := hmem.mp hi
          simp [Set.indicator_of_mem, hi, h₀]
        · have h₀ : q ∉ rect₀ := fun h => hi (hmem.mpr h)
          simp [Set.indicator_of_notMem, hi, h₀]
  have hdct :
      Tendsto
        (fun i => ∫ q, (rect i).indicator weight q ∂μ)
        l
        (𝓝 (∫ q, (rect₀).indicator weight q ∂μ)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ)
      (bound := square.indicator (fun q : ℝ × ℝ => ‖weight q‖))
      hmeas hbound hbound_integrable hlim
  simpa [μ, rect, rect₀, MeasureTheory.integral_indicator,
    hrect_meas, hrect₀_meas] using hdct

/-- An integrable weight gives a continuous nontrivial-cell objective on the finite-gap simplex. -/
theorem continuousOn_nontrivialCellWeightFiniteObjective_volume_of_integrableOn_Icc
    (m : ℕ) {weight : ℝ × ℝ → ℝ}
    (hweight_int :
      IntegrableOn weight
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
        (volume.prod volume)) :
    ContinuousOn
      (fun gap : Fin (m + 2) → ℝ =>
        cutpointRangeFunctional (m + 2)
          (nontrivialCellWeightFiniteObjective volume m weight)
          (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
      {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap} := by
  let simplex : Set (Fin (m + 2) → ℝ) :=
    {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap}
  have hsum :
      ContinuousOn
        (fun gap : Fin (m + 2) → ℝ =>
          ∑ component : theorem31OrderedNontrivialPairComponent m,
            ∫ q in
              (Set.Ioc
                  (finiteCutpointVectorEval (m + 2)
                    (fun j : Fin ((m + 2) + 1) =>
                      AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
                    component.val.1.val)
                  (finiteCutpointVectorEval (m + 2)
                    (fun j : Fin ((m + 2) + 1) =>
                      AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
                    (component.val.1.val + 1)) ×ˢ
                Set.Ioc
                  (finiteCutpointVectorEval (m + 2)
                    (fun j : Fin ((m + 2) + 1) =>
                      AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
                    component.val.2.val)
                  (finiteCutpointVectorEval (m + 2)
                    (fun j : Fin ((m + 2) + 1) =>
                      AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
                    (component.val.2.val + 1))),
              weight q ∂(volume.prod volume))
        simplex := by
    refine continuousOn_finset_sum Finset.univ ?_
    intro component _hcomponent gap₀ hgap₀
    let a : (Fin (m + 2) → ℝ) → ℝ :=
      fun gap =>
        finiteCutpointVectorEval (m + 2)
          (fun j : Fin ((m + 2) + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
          component.val.1.val
    let b : (Fin (m + 2) → ℝ) → ℝ :=
      fun gap =>
        finiteCutpointVectorEval (m + 2)
          (fun j : Fin ((m + 2) + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
          (component.val.1.val + 1)
    let c : (Fin (m + 2) → ℝ) → ℝ :=
      fun gap =>
        finiteCutpointVectorEval (m + 2)
          (fun j : Fin ((m + 2) + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
          component.val.2.val
    let d : (Fin (m + 2) → ℝ) → ℝ :=
      fun gap =>
        finiteCutpointVectorEval (m + 2)
          (fun j : Fin ((m + 2) + 1) =>
            AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
          (component.val.2.val + 1)
    have ha : Tendsto a (𝓝[simplex] gap₀) (𝓝 (a gap₀)) := by
      simpa [a] using
        ((continuous_finiteCutpointVectorEval (m + 2)
          component.val.1.val).comp
          (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
    have hb : Tendsto b (𝓝[simplex] gap₀) (𝓝 (b gap₀)) := by
      simpa [b] using
        ((continuous_finiteCutpointVectorEval (m + 2)
          (component.val.1.val + 1)).comp
          (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
    have hc : Tendsto c (𝓝[simplex] gap₀) (𝓝 (c gap₀)) := by
      simpa [c] using
        ((continuous_finiteCutpointVectorEval (m + 2)
          component.val.2.val).comp
          (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
    have hd : Tendsto d (𝓝[simplex] gap₀) (𝓝 (d gap₀)) := by
      simpa [d] using
        ((continuous_finiteCutpointVectorEval (m + 2)
          (component.val.2.val + 1)).comp
          (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
    have hrect_subset :
        ∀ᶠ gap in 𝓝[simplex] gap₀,
          Set.Ioc (a gap) (b gap) ×ˢ Set.Ioc (c gap) (d gap) ⊆
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin] with gap hgap
      simpa [a, b, c, d] using
        finiteCutpointVectorEval_finiteGapCutpoint_Ioc_prod_subset_unit_square
          gap hgap component.val.1.val component.val.2.val
    have hrect₀_subset :
        Set.Ioc (a gap₀) (b gap₀) ×ˢ Set.Ioc (c gap₀) (d gap₀) ⊆
          Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
      simpa [a, b, c, d] using
        finiteCutpointVectorEval_finiteGapCutpoint_Ioc_prod_subset_unit_square
          gap₀ hgap₀ component.val.1.val component.val.2.val
    simpa [a, b, c, d] using
      tendsto_integral_Ioc_prod_of_tendsto_of_integrableOn_Icc
        (l := 𝓝[simplex] gap₀)
        ha hb hc hd hweight_int hrect_subset hrect₀_subset
  simpa [simplex, nontrivialCellWeightFiniteObjective, cutpointRangeFunctional]
    using hsum

/--
Spearman's linear weight integrates exactly to the midpoint value times the
rectangle area on monotone Lebesgue cells.
-/
theorem spearmanLinearWeight_rectangleIntegral_eq_midpoint_area_of_le
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ q in Set.Ioc a b ×ˢ Set.Ioc c d,
        (q.2 - q.1) ∂(volume.prod volume) =
      (((c + d) / 2) - ((a + b) / 2)) * (b - a) * (d - c) := by
  let A : Set ℝ := Set.Ioc a b
  let B : Set ℝ := Set.Ioc c d
  have hmeas : MeasurableSet (A ×ˢ B) := by
    exact measurableSet_Ioc.prod measurableSet_Ioc
  have hsub :
      A ×ˢ B ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    isCompact_Icc.prod isCompact_Icc
  have hfinite :
      (volume.prod volume) (A ×ˢ B) ≠ ⊤ := by
    exact
      ((measure_mono hsub).trans_lt
        (lt_top_iff_ne_top.mpr hcompact.measure_ne_top)).ne
  have hsnd_int :
      IntegrableOn (fun q : ℝ × ℝ => q.2) (A ×ˢ B)
        (volume.prod volume) := by
    exact
      continuous_snd.continuousOn.integrableOn_of_subset_isCompact
        hcompact hmeas hsub hfinite
  have hfst_int :
      IntegrableOn (fun q : ℝ × ℝ => q.1) (A ×ˢ B)
        (volume.prod volume) := by
    exact
      continuous_fst.continuousOn.integrableOn_of_subset_isCompact
        hcompact hmeas hsub hfinite
  have h_snd :
      ∫ q in A ×ˢ B, q.2 ∂(volume.prod volume) =
        (∫ x in A, (1 : ℝ) ∂volume) * ∫ y in B, y ∂volume := by
    simpa [A, B, one_mul] using
      (MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
        (f := fun _x : ℝ => (1 : ℝ)) (g := fun y : ℝ => y) A B)
  have h_fst :
      ∫ q in A ×ˢ B, q.1 ∂(volume.prod volume) =
        (∫ x in A, x ∂volume) * ∫ y in B, (1 : ℝ) ∂volume := by
    simpa [A, B, mul_one] using
      (MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
        (f := fun x : ℝ => x) (g := fun _y : ℝ => (1 : ℝ)) A B)
  have hA_one : ∫ x in A, (1 : ℝ) ∂volume = b - a := by
    simp [A, Real.volume_real_Ioc_of_le hab]
  have hB_one : ∫ y in B, (1 : ℝ) ∂volume = d - c := by
    simp [B, Real.volume_real_Ioc_of_le hcd]
  have hA_id : ∫ x in A, x ∂volume = (b ^ 2 - a ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hab]
    exact integral_id
  have hB_id : ∫ y in B, y ∂volume = (d ^ 2 - c ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hcd]
    exact integral_id
  calc
    ∫ q in Set.Ioc a b ×ˢ Set.Ioc c d,
        (q.2 - q.1) ∂(volume.prod volume)
        = ∫ q in A ×ˢ B, (q.2 - q.1) ∂(volume.prod volume) := by
          rfl
    _ = (∫ q in A ×ˢ B, q.2 ∂(volume.prod volume)) -
          ∫ q in A ×ˢ B, q.1 ∂(volume.prod volume) := by
          rw [MeasureTheory.integral_sub hsnd_int hfst_int]
    _ = (((c + d) / 2) - ((a + b) / 2)) * (b - a) * (d - c) := by
          rw [h_snd, h_fst, hA_one, hB_one, hA_id, hB_id]
          ring

/-- Midpoint formula for linear weights on ordered cell pairs excluding the bottom-to-top pair. -/
noncomputable def nontrivialCellSpearmanMidpointFiniteObjective
    (m : ℕ) (v : Fin ((m + 2) + 1) → ℝ) : ℝ :=
  ∑ component : theorem31OrderedNontrivialPairComponent m,
    (((finiteCutpointVectorEval (m + 2) v component.val.2.val +
        finiteCutpointVectorEval (m + 2) v
          (component.val.2.val + 1)) / 2) -
      ((finiteCutpointVectorEval (m + 2) v component.val.1.val +
          finiteCutpointVectorEval (m + 2) v
            (component.val.1.val + 1)) / 2)) *
      (finiteCutpointVectorEval (m + 2) v
          (component.val.1.val + 1) -
        finiteCutpointVectorEval (m + 2) v component.val.1.val) *
      (finiteCutpointVectorEval (m + 2) v
          (component.val.2.val + 1) -
        finiteCutpointVectorEval (m + 2) v component.val.2.val)

/-- The nontrivial-cell linear-weight midpoint formula is continuous. -/
theorem continuous_nontrivialCellSpearmanMidpointFiniteObjective
    (m : ℕ) :
    Continuous (nontrivialCellSpearmanMidpointFiniteObjective m) := by
  unfold nontrivialCellSpearmanMidpointFiniteObjective
  refine continuous_finset_sum Finset.univ ?_
  intro component _hcomponent
  have hmid :
      Continuous
        (fun v : Fin ((m + 2) + 1) → ℝ =>
          (finiteCutpointVectorEval (m + 2) v component.val.2.val +
              finiteCutpointVectorEval (m + 2) v
                (component.val.2.val + 1)) / 2 -
            (finiteCutpointVectorEval (m + 2) v component.val.1.val +
                finiteCutpointVectorEval (m + 2) v
                  (component.val.1.val + 1)) / 2) :=
    (((continuous_finiteCutpointVectorEval (m + 2)
        component.val.2.val).add
      (continuous_finiteCutpointVectorEval (m + 2)
        (component.val.2.val + 1))).div_const 2).sub
      (((continuous_finiteCutpointVectorEval (m + 2)
          component.val.1.val).add
        (continuous_finiteCutpointVectorEval (m + 2)
          (component.val.1.val + 1))).div_const 2)
  have hlow :
      Continuous
        (fun v : Fin ((m + 2) + 1) → ℝ =>
          finiteCutpointVectorEval (m + 2) v
              (component.val.1.val + 1) -
            finiteCutpointVectorEval (m + 2) v component.val.1.val) :=
    (continuous_finiteCutpointVectorEval (m + 2)
      (component.val.1.val + 1)).sub
      (continuous_finiteCutpointVectorEval (m + 2)
        component.val.1.val)
  have hhigh :
      Continuous
        (fun v : Fin ((m + 2) + 1) → ℝ =>
          finiteCutpointVectorEval (m + 2) v
              (component.val.2.val + 1) -
            finiteCutpointVectorEval (m + 2) v component.val.2.val) :=
    (continuous_finiteCutpointVectorEval (m + 2)
      (component.val.2.val + 1)).sub
      (continuous_finiteCutpointVectorEval (m + 2)
        component.val.2.val)
  exact (hmid.mul hlow).mul hhigh

/-- For ordered cells, the nontrivial-cell linear-weight integral equals its midpoint formula. -/
theorem nontrivialCellWeightFiniteObjective_volume_spearman_eq_midpoint_sum_of_monotone
    (m : ℕ) (v : Fin ((m + 2) + 1) → ℝ)
    (hmono :
      ∀ i : ℕ, i + 1 ≤ m + 2 →
        finiteCutpointVectorEval (m + 2) v i ≤
          finiteCutpointVectorEval (m + 2) v (i + 1)) :
    nontrivialCellWeightFiniteObjective volume m
        (fun q : ℝ × ℝ => q.2 - q.1) v =
      nontrivialCellSpearmanMidpointFiniteObjective m v := by
  unfold nontrivialCellWeightFiniteObjective
    nontrivialCellSpearmanMidpointFiniteObjective
  refine Finset.sum_congr rfl ?_
  intro component _hcomponent
  have hlow :
      finiteCutpointVectorEval (m + 2) v component.val.1.val ≤
        finiteCutpointVectorEval (m + 2) v (component.val.1.val + 1) := by
    exact hmono component.val.1.val (Nat.succ_le_iff.mpr component.val.1.2)
  have hhigh :
      finiteCutpointVectorEval (m + 2) v component.val.2.val ≤
        finiteCutpointVectorEval (m + 2) v (component.val.2.val + 1) := by
    exact hmono component.val.2.val (Nat.succ_le_iff.mpr component.val.2.2)
  simpa using
    spearmanLinearWeight_rectangleIntegral_eq_midpoint_area_of_le
      (a := finiteCutpointVectorEval (m + 2) v component.val.1.val)
      (b := finiteCutpointVectorEval (m + 2) v (component.val.1.val + 1))
      (c := finiteCutpointVectorEval (m + 2) v component.val.2.val)
      (d := finiteCutpointVectorEval (m + 2) v (component.val.2.val + 1))
      hlow hhigh

/-- The nontrivial-cell linear-weight objective is continuous on the finite-gap simplex. -/
theorem continuousOn_nontrivialCellWeightFiniteObjective_volume_spearman_finiteGapCutpoint
    (m : ℕ) :
    ContinuousOn
      (fun gap : Fin (m + 2) → ℝ =>
        cutpointRangeFunctional (m + 2)
          (nontrivialCellWeightFiniteObjective volume m
            (fun q : ℝ × ℝ => q.2 - q.1))
          (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
      {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap} := by
  have hpoly :
      Continuous
        (fun gap : Fin (m + 2) → ℝ =>
          cutpointRangeFunctional (m + 2)
            (nontrivialCellSpearmanMidpointFiniteObjective m)
            (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap)) := by
    simpa [cutpointRangeFunctional] using
      (continuous_nontrivialCellSpearmanMidpointFiniteObjective m).comp
        (continuous_finiteGapCutpoint_vector (M := m + 2))
  refine hpoly.continuousOn.congr ?_
  intro gap hgap
  unfold cutpointRangeFunctional
  have hcut_mono :
      Monotone (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) :=
    AppliedModelingLib.FiniteSum.finiteGapCutpoint_monotone_of_nonneg gap hgap.1
  have hmono_eval :
      ∀ i : ℕ, i + 1 ≤ m + 2 →
        finiteCutpointVectorEval (m + 2)
            (fun j : Fin ((m + 2) + 1) =>
              AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1) i ≤
          finiteCutpointVectorEval (m + 2)
            (fun j : Fin ((m + 2) + 1) =>
              AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1) (i + 1) := by
    intro i hi
    have hi0 : i ≤ m + 2 := Nat.le_of_succ_le hi
    simp [finiteCutpointVectorEval, hi0, hi]
    exact hcut_mono (Nat.le_succ i)
  simpa using
    nontrivialCellWeightFiniteObjective_volume_spearman_eq_midpoint_sum_of_monotone
      m
      (fun j : Fin ((m + 2) + 1) =>
        AppliedModelingLib.FiniteSum.finiteGapCutpoint gap j.1)
      hmono_eval

/-- The nontrivial-cell linear-weight objective attains a maximum. -/
theorem exists_nontrivialCellWeight_volume_spearman_cutpoint_value_argmax
    (m : ℕ) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        (cutpointRangeFunctional (m + 2)
          (nontrivialCellWeightFiniteObjective volume m
            (fun q : ℝ × ℝ => q.2 - q.1))) Sstar := by
  haveI : Nonempty (Fin (m + 2)) := ⟨⟨0, by omega⟩⟩
  exact
    theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
      (M := m + 2)
      (nontrivialCellWeightFiniteObjective volume m
        (fun q : ℝ × ℝ => q.2 - q.1))
      (continuousOn_nontrivialCellWeightFiniteObjective_volume_spearman_finiteGapCutpoint m)

/-- The nontrivial-cell integrable-weight objective attains a maximum. -/
theorem exists_nontrivialCellWeight_volume_weighted_cutpoint_value_argmax_of_integrableOn_Icc
    (m : ℕ) {weight : ℝ × ℝ → ℝ}
    (hweight_int :
      IntegrableOn weight
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
        (volume.prod volume)) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        (cutpointRangeFunctional (m + 2)
          (nontrivialCellWeightFiniteObjective volume m weight)) Sstar := by
  haveI : Nonempty (Fin (m + 2)) := ⟨⟨0, by omega⟩⟩
  exact
    theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
      (M := m + 2)
      (nontrivialCellWeightFiniteObjective volume m weight)
      (continuousOn_nontrivialCellWeightFiniteObjective_volume_of_integrableOn_Icc
        m hweight_int)

/-- A continuous nontrivial-cell objective attains a maximum. -/
theorem exists_nontrivialCellWeight_cutpoint_value_argmax_of_continuous
    (μ : Measure ℝ) (m : ℕ) (weight : ℝ × ℝ → ℝ)
    (hcontinuous :
      Continuous (nontrivialCellWeightFiniteObjective μ m weight)) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        (cutpointRangeFunctional (m + 2)
          (nontrivialCellWeightFiniteObjective μ m weight)) Sstar := by
  haveI : Nonempty (Fin (m + 2)) := ⟨⟨0, by omega⟩⟩
  exact
    theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
      (M := m + 2)
      (nontrivialCellWeightFiniteObjective μ m weight)
      hcontinuous

/-- The constant-weight nontrivial-cell objective attains a maximum. -/
theorem exists_nontrivialCellWeight_volume_const_cutpoint_value_argmax
    (m : ℕ) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        (cutpointRangeFunctional (m + 2)
          (nontrivialCellWeightFiniteObjective volume m
            (fun _q : ℝ × ℝ => (1 : ℝ)))) Sstar := by
  exact
    exists_nontrivialCellWeight_cutpoint_value_argmax_of_continuous
      volume m (fun _q : ℝ × ℝ => (1 : ℝ))
      (continuous_nontrivialCellWeightFiniteObjective_volume_const m)

/--
Theorem 3.1 Kendall source objective: the constant-weight ordered-pair
cutpoint objective has a value-maximizing `S*` over endpoint-feasible cutpoint
chains.  The finite-vector continuity and source equality are discharged
internally.
-/
theorem theorem31_exists_kendall_constant_weight_ordered_pair_cutpoint_value_argmax
    {M : ℕ} [Nonempty (Fin M)] :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (kendallConstantWeightOrderedPairIntervalObjective M) Sstar := by
  rcases
      theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
        (M := M)
        (kendallConstantWeightOrderedPairFiniteObjective M)
        (continuous_kendallConstantWeightOrderedPairFiniteObjective M) with
    ⟨Sstar, hSstar⟩
  refine ⟨Sstar, ?_⟩
  simpa [cutpointRangeFunctional_kendallConstantWeightOrderedPairFiniteObjective]
    using hSstar

/--
Theorem 3.1 Spearman source objective: the linear-weight ordered-pair
cutpoint objective has a value-maximizing `S*` over endpoint-feasible cutpoint
chains.  The finite-vector continuity and source equality are discharged
internally.
-/
theorem theorem31_exists_spearman_linear_weight_ordered_pair_cutpoint_value_argmax
    {M : ℕ} [Nonempty (Fin M)] :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (spearmanLinearWeightOrderedPairIntervalObjective M) Sstar := by
  rcases
      theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
        (M := M)
        (spearmanLinearWeightOrderedPairFiniteObjective M)
        (continuous_spearmanLinearWeightOrderedPairFiniteObjective M) with
    ⟨Sstar, hSstar⟩
  refine ⟨Sstar, ?_⟩
  simpa [cutpointRangeFunctional_spearmanLinearWeightOrderedPairFiniteObjective]
    using hSstar

/--
Theorem 3.1 midpoint-weighted source objective: every continuous
midpoint-weighted ordered-pair cutpoint objective has a value-maximizing `S*`
over endpoint-feasible cutpoint chains.
-/
theorem theorem31_exists_midpoint_weighted_ordered_pair_cutpoint_value_argmax
    {M : ℕ} [Nonempty (Fin M)]
    (weight : ℝ × ℝ → ℝ) (hweight : Continuous weight) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (midpointWeightedOrderedPairIntervalObjective M weight) Sstar := by
  rcases
      theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
        (M := M)
        (midpointWeightedOrderedPairFiniteObjective M weight)
        (continuous_midpointWeightedOrderedPairFiniteObjective M hweight) with
    ⟨Sstar, hSstar⟩
  refine ⟨Sstar, ?_⟩
  simpa [cutpointRangeFunctional_midpointWeightedOrderedPairFiniteObjective]
    using hSstar

/--
Theorem 3.1 generic finite ordered-pair source objective: any objective whose
ordered-pair summands are continuous finite-vector expressions in the
displayed cutpoints has a value-maximizing `S*`.
-/
theorem theorem31_exists_finite_ordered_pair_cutpoint_value_argmax
    {M : ℕ} [Nonempty (Fin M)]
    (term : Fin M → Fin M → (Fin (M + 1) → ℝ) → ℝ)
    (hterm : ∀ i j : Fin M, Continuous (term i j)) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (cutpointRangeFunctional M
          (finiteOrderedPairCutpointObjective M term)) Sstar :=
  theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
    (M := M)
    (finiteOrderedPairCutpointObjective M term)
    (continuous_finiteOrderedPairCutpointObjective M hterm)

/--
Theorem 3.1 cutpoint form.  If the paper's endpoint feasibility, limiting
value, and rate only depend on the finite cutpoint range, the finite-simplex
optimizer is lexicographically optimal among all monotone endpoint-feasible
cutpoint chains.
-/
theorem theorem31_exists_cutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
    {M : ℕ} [Nonempty (Fin M)] {Endpoint : Type*}
    (endpointFeasible : (ℕ → ℝ) → Endpoint → Prop)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → Endpoint → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin M → ℝ =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hendpoint :
      ∀ gap : Fin M → ℝ, AppliedModelingLib.FiniteProbabilitySimplex gap →
        ∃ tstar : Endpoint,
          endpointFeasible (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap)
            tstar ∧
            ∀ (otherGap : Fin M → ℝ) (t : Endpoint),
              AppliedModelingLib.FiniteProbabilitySimplex otherGap →
              endpointFeasible
                (AppliedModelingLib.FiniteSum.finiteGapCutpoint otherGap) t →
              limitingValue
                  (AppliedModelingLib.FiniteSum.finiteGapCutpoint otherGap) =
                  limitingValue
                    (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) →
                  rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint otherGap) t ≤
                    rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) tstar)
    (hendpoint_extensional :
      ∀ (S : ℕ → ℝ) (gap : Fin M → ℝ) (t : Endpoint),
        monotoneIntervalCutpointsEndpointFeasible M S →
        (∀ k : ℕ, k ≤ M →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k = S k) →
        endpointFeasible S t →
          endpointFeasible (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) t)
    (hvalue_extensional :
      ∀ (S : ℕ → ℝ) (gap : Fin M → ℝ),
        monotoneIntervalCutpointsEndpointFeasible M S →
        (∀ k : ℕ, k ≤ M →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k = S k) →
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) =
          limitingValue S)
    (hrate_extensional :
      ∀ (S : ℕ → ℝ) (gap : Fin M → ℝ) (t : Endpoint),
        monotoneIntervalCutpointsEndpointFeasible M S →
        (∀ k : ℕ, k ≤ M →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k = S k) →
        rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) t = rate S t) :
    ∃ design : (ℕ → ℝ) × Endpoint,
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × Endpoint =>
          monotoneIntervalCutpointsEndpointFeasible M design.1 ∧
            endpointFeasible design.1 design.2)
        (fun design : (ℕ → ℝ) × Endpoint => limitingValue design.1)
        (fun design : (ℕ → ℝ) × Endpoint => rate design.1 design.2)
        design := by
  rcases
    theorem31_exists_finiteGapCutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
      (M := M) endpointFeasible limitingValue rate hcontinuous hendpoint with
    ⟨designGap, hlexGap⟩
  let Sstar : ℕ → ℝ :=
    AppliedModelingLib.FiniteSum.finiteGapCutpoint designGap.1
  refine ⟨(Sstar, designGap.2), ?_⟩
  constructor
  · exact
      ⟨monotoneIntervalCutpointsEndpointFeasible_finiteGapCutpoint_of_finiteProbabilitySimplex
          designGap.1 hlexGap.1.1,
        hlexGap.1.2⟩
  · intro design hdesign
    let altGap : Fin M → ℝ :=
      intervalCutpointAdjacentGap M design.1
    have haltGap :
        AppliedModelingLib.FiniteProbabilitySimplex altGap :=
      finiteProbabilitySimplex_intervalCutpointAdjacentGap_of_monotoneIntervalCutpointsEndpointFeasible
        design.1 hdesign.1
    have hrecover :
        ∀ k : ℕ, k ≤ M →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap k = design.1 k :=
      finiteGapCutpoint_intervalCutpointAdjacentGap_eq design.1 hdesign.1.2.1
    have haltEndpoint :
        endpointFeasible (AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap)
          design.2 :=
      hendpoint_extensional design.1 altGap design.2 hdesign.1 hrecover
        hdesign.2
    have hlexAlt :=
      hlexGap.2 (altGap, design.2) ⟨haltGap, haltEndpoint⟩
    have hvalue :
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap) =
          limitingValue design.1 :=
      hvalue_extensional design.1 altGap hdesign.1 hrecover
    have hrate :
        rate (AppliedModelingLib.FiniteSum.finiteGapCutpoint altGap) design.2 =
          rate design.1 design.2 :=
      hrate_extensional design.1 altGap design.2 hdesign.1 hrecover
    rcases hlexAlt with hlt | ⟨heq, hle⟩
    · left
      simpa [Sstar, hvalue] using hlt
    · right
      constructor
      · simpa [Sstar, hvalue] using heq
      · simpa [Sstar, hrate] using hle

/--
Theorem 3.1 uniform-matching cutpoint optimizer.  When the endpoint-rate
objective is the source's uniform-matching adjacent-rate objective, the
secondary endpoint optimizer is derived internally from the canonical
equalized endpoint levels.  Thus a continuous finite-simplex limiting-value
objective produces a lexicographically optimal cutpoint/endpoint design
without carrying an endpoint certificate as a premise.
-/
theorem theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
    {m : ℕ}
    (limitingValue : (ℕ → ℝ) → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin (m + 2) → ℝ =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hvalue_extensional :
      ∀ (S : ℕ → ℝ) (gap : Fin (m + 2) → ℝ),
        monotoneIntervalCutpointsEndpointFeasible (m + 2) S →
        (∀ k : ℕ, k ≤ m + 2 →
          AppliedModelingLib.FiniteSum.finiteGapCutpoint gap k = S k) →
        limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap) =
          limitingValue S) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          limitingValue design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  classical
  refine
    theorem31_exists_cutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
      (M := m + 2)
      (Endpoint := Fin (m + 2) → ℝ)
      (fun _S levels => BinaryEndpointLevelVector levels)
      limitingValue
      (fun _S levels =>
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      hcontinuous ?_ ?_ hvalue_extensional ?_
  · intro gap _hgap
    refine
      ⟨canonicalUniformEqualizedEndpointLevels m,
        canonicalUniformEqualizedEndpointLevels_levelVector m, ?_⟩
    intro _otherGap levels _hotherGap hlevels _hvalue_eq
    exact (canonicalUniformEqualizedEndpointLevels_isMaximizerOn m).le hlevels
  · intro _S _gap _levels _hS _hrecover hlevels
    exact hlevels
  · intro _S _gap _levels _hS _hrecover
    rfl

/--
Theorem 3.1 uniform-matching cutpoint optimizer with source-shaped
finite-range extensionality.  This replaces the low-level finite-gap
extensionality premise by the natural statement that the limiting-value
objective only depends on the finite cutpoint range.
-/
theorem theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange
    {m : ℕ}
    (limitingValue : (ℕ → ℝ) → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin (m + 2) → ℝ =>
          limitingValue (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hdepends :
      cutpointFunctionalDependsOnlyOnRange (m + 2) limitingValue) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          limitingValue design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design :=
  theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
    limitingValue hcontinuous
    (cutpointFunctionalDependsOnlyOnRange.value_extensional hdepends)

/--
Theorem 3.1 uniform-matching optimizer for a finite-vector objective.  This is
the staged S* optimizer interface for source objectives expressed as finite
formulas in the displayed cutpoints.
-/
theorem theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
    {m : ℕ}
    (finiteFunctional : (Fin ((m + 2) + 1) → ℝ) → ℝ)
    (hcontinuous :
      ContinuousOn
        (fun gap : Fin (m + 2) → ℝ =>
          cutpointRangeFunctional (m + 2) finiteFunctional
            (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap}) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2) finiteFunctional design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design :=
  theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange
    (cutpointRangeFunctional (m + 2) finiteFunctional) hcontinuous
    (cutpointFunctionalDependsOnlyOnRange_cutpointRangeFunctional (m + 2)
      finiteFunctional)

/-- Lexicographic optimization of nontrivial-cell linear weight and the uniform-matching adjacent-rate formula. -/
theorem exists_nontrivialCellWeight_volume_spearman_uniform_endpoint_two_stage_lexicographic_optimality
    (m : ℕ) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2)
            (nontrivialCellWeightFiniteObjective volume m
              (fun q : ℝ × ℝ => q.2 - q.1)) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  exact
    theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
      (m := m)
      (nontrivialCellWeightFiniteObjective volume m
        (fun q : ℝ × ℝ => q.2 - q.1))
      (continuousOn_nontrivialCellWeightFiniteObjective_volume_spearman_finiteGapCutpoint m)

/-- Lexicographic optimization of nontrivial-cell integrable weight and the uniform-matching adjacent-rate formula. -/
theorem exists_nontrivialCellWeight_volume_weighted_uniform_endpoint_two_stage_lexicographic_optimality_of_integrableOn_Icc
    (m : ℕ) {weight : ℝ × ℝ → ℝ}
    (hweight_int :
      IntegrableOn weight
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
        (volume.prod volume)) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2)
            (nontrivialCellWeightFiniteObjective volume m weight) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  exact
    theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
      (m := m)
      (nontrivialCellWeightFiniteObjective volume m weight)
      (continuousOn_nontrivialCellWeightFiniteObjective_volume_of_integrableOn_Icc
        m hweight_int)

/--
Theorem 3.1 uniform-matching optimizer for a continuous finite-vector
objective.  This removes the composed-continuity premise from the finite-vector
`S*` bridge.
-/
theorem theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
    {m : ℕ}
    (finiteFunctional : (Fin ((m + 2) + 1) → ℝ) → ℝ)
    (hcontinuous : Continuous finiteFunctional) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2) finiteFunctional design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  have hcontinuousOn :
      ContinuousOn
        (fun gap : Fin (m + 2) → ℝ =>
          cutpointRangeFunctional (m + 2) finiteFunctional
            (AppliedModelingLib.FiniteSum.finiteGapCutpoint gap))
        {gap : Fin (m + 2) → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap} := by
    simpa [cutpointRangeFunctional] using
      (hcontinuous.comp
        (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousOn
  exact
    theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
      finiteFunctional hcontinuousOn

/-- A continuous nontrivial-cell objective and the uniform-matching adjacent-rate formula admit a lexicographic optimizer. -/
theorem exists_nontrivialCellWeight_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous
    (μ : Measure ℝ) (m : ℕ) (weight : ℝ × ℝ → ℝ)
    (hcontinuous :
      Continuous (nontrivialCellWeightFiniteObjective μ m weight)) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2)
            (nontrivialCellWeightFiniteObjective μ m weight) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  exact
    theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
      (m := m)
      (nontrivialCellWeightFiniteObjective μ m weight)
      hcontinuous

/-- Lexicographic optimization of constant nontrivial-cell weight and the uniform-matching adjacent-rate formula. -/
theorem exists_nontrivialCellWeight_volume_const_uniform_endpoint_two_stage_lexicographic_optimality
    (m : ℕ) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2)
            (nontrivialCellWeightFiniteObjective volume m
              (fun _q : ℝ × ℝ => (1 : ℝ))) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  exact
    exists_nontrivialCellWeight_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous
      volume m (fun _q : ℝ × ℝ => (1 : ℝ))
      (continuous_nontrivialCellWeightFiniteObjective_volume_const m)

/--
Theorem 3.1 Kendall source objective with uniform matching: the concrete
constant-weight ordered-pair value objective and canonical equalized endpoint
rate objective admit a lexicographically optimal design.  No `S*`
continuity or argmax certificate is exposed to the caller.
-/
theorem theorem31_exists_kendall_constant_weight_ordered_pair_uniform_endpoint_two_stage_lexicographic_optimality
    (m : ℕ) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          kendallConstantWeightOrderedPairIntervalObjective (m + 2) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  rcases
      theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
        (m := m)
        (kendallConstantWeightOrderedPairFiniteObjective (m + 2))
        (continuous_kendallConstantWeightOrderedPairFiniteObjective
          (m + 2)) with
    ⟨design, hdesign⟩
  refine ⟨design, ?_⟩
  simpa [cutpointRangeFunctional_kendallConstantWeightOrderedPairFiniteObjective]
    using hdesign

/--
Theorem 3.1 Spearman source objective with uniform matching: the concrete
linear-weight ordered-pair value objective and canonical equalized endpoint
rate objective admit a lexicographically optimal design.  No `S*`
continuity or argmax certificate is exposed to the caller.
-/
theorem theorem31_exists_spearman_linear_weight_ordered_pair_uniform_endpoint_two_stage_lexicographic_optimality
    (m : ℕ) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          spearmanLinearWeightOrderedPairIntervalObjective (m + 2) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  rcases
      theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
        (m := m)
        (spearmanLinearWeightOrderedPairFiniteObjective (m + 2))
        (continuous_spearmanLinearWeightOrderedPairFiniteObjective
          (m + 2)) with
    ⟨design, hdesign⟩
  refine ⟨design, ?_⟩
  simpa [cutpointRangeFunctional_spearmanLinearWeightOrderedPairFiniteObjective]
    using hdesign

/--
Theorem 3.1 midpoint-weighted source objective with uniform matching:
continuous midpoint weights admit a lexicographically optimal
cutpoint/endpoint design.  The `S*` existence and endpoint-rate optimization
are derived internally from the finite-vector objective.
-/
theorem theorem31_exists_midpoint_weighted_ordered_pair_uniform_endpoint_two_stage_lexicographic_optimality
    (m : ℕ) (weight : ℝ × ℝ → ℝ) (hweight : Continuous weight) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          midpointWeightedOrderedPairIntervalObjective (m + 2) weight
            design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design := by
  rcases
      theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
        (m := m)
        (midpointWeightedOrderedPairFiniteObjective (m + 2) weight)
        (continuous_midpointWeightedOrderedPairFiniteObjective
          (m + 2) hweight) with
    ⟨design, hdesign⟩
  refine ⟨design, ?_⟩
  simpa [cutpointRangeFunctional_midpointWeightedOrderedPairFiniteObjective]
    using hdesign

/--
Theorem 3.1 generic finite ordered-pair source objective with uniform
matching: continuous finite-vector ordered-pair summands produce a
lexicographically optimal cutpoint/endpoint design.
-/
theorem theorem31_exists_finite_ordered_pair_uniform_endpoint_two_stage_lexicographic_optimality
    (m : ℕ)
    (term :
      Fin (m + 2) → Fin (m + 2) →
        (Fin ((m + 2) + 1) → ℝ) → ℝ)
    (hterm :
      ∀ i j : Fin (m + 2), Continuous (term i j)) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2)
            (finiteOrderedPairCutpointObjective (m + 2) term) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design :=
  theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
    (m := m)
    (finiteOrderedPairCutpointObjective (m + 2) term)
    (continuous_finiteOrderedPairCutpointObjective (m + 2) hterm)

/--
Theorem 3.1 staged source certificate for a fixed value-maximizing
discretization.  This is the paper's printed decomposition form: once `S*` is
represented by a cutpoint chain that maximizes the limiting-value objective,
the forward-clipped endpoint construction supplies the optimal endpoint levels
for that `S*`, and the source-defined `Wbar_k` has the corresponding adjacent
large-deviation rate certificate.  No endpoint-rate certificate is assumed.
-/
theorem theorem31_strict_cutpoint_value_argmax_forward_clipped_endpoint_source_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (hcut_value :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        limitingValue cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (monotoneIntervalCutpointsEndpointFeasible (m + 2))
            limitingValue cut := by
  rcases
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
      μ hm cut hmono hcut_strict sampleRate hsample_pos hsample_mono
      weight hweight_int hweight_nonneg hweight_cont hweight_midpoint_pos with
    ⟨levels, hlevels, heq, hrate_opt, _hpos, hcert⟩
  exact ⟨levels, hlevels, heq, hrate_opt, hcert, hcut_value⟩

/--
Theorem 3.1 staged source theorem with the nonunique value-tie obligation
made explicit.  The fixed-`S*` endpoint levels and the `Wbar_k` exponential
rate certificate are still derived from the weighted finite-level source
model.  When another discretization has the same primary limiting value, the
only remaining source obligation is that its displayed secondary rate is no
larger than the derived equalized endpoint rate for `S*`.
-/
theorem theorem31_strict_cutpoint_value_tie_forward_clipped_endpoint_lexicographic_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → (Fin (m + 2) → ℝ) → ℝ)
    (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (hcut_value :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        limitingValue cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hrate_cut :
      ∀ levels : Fin (m + 2) → ℝ, BinaryEndpointLevelVector levels →
        rate cut levels =
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
    (hrate_value_tie :
      ∀ levels : Fin (m + 2) → ℝ,
        BinaryEndpointLevelVector levels →
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate →
          ∀ S : ℕ → ℝ, ∀ candidate : Fin (m + 2) → ℝ,
            monotoneIntervalCutpointsEndpointFeasible (m + 2) S →
            BinaryEndpointLevelVector candidate →
            limitingValue S = limitingValue cut →
            S ≠ cut →
              rate S candidate ≤
                binaryEndpointAwareAdjacentRateObjective levels sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
                BinaryEndpointLevelVector design.2)
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              limitingValue design.1)
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              rate design.1 design.2)
            (cut, levels) := by
  rcases
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
      μ hm cut hmono hcut_strict sampleRate hsample_pos hsample_mono
      weight hweight_int hweight_nonneg hweight_cont hweight_midpoint_pos with
    ⟨levels, hlevels, heq, hrate_opt, _hpos, hcert⟩
  refine ⟨levels, hlevels, heq, hcert, ?_⟩
  refine
    theorem31_partition_endpoint_two_stage_lexicographic_optimality
      (fun S : ℕ → ℝ =>
        monotoneIntervalCutpointsEndpointFeasible (m + 2) S)
      (fun _S levels => BinaryEndpointLevelVector levels)
      limitingValue rate cut levels hcut_value hlevels ?_
  intro S candidate hS hcandidate hvalue_eq
  by_cases hS_eq : S = cut
  · subst S
    rw [hrate_cut candidate hcandidate, hrate_cut levels hlevels]
    exact hrate_opt.le hcandidate
  · rw [hrate_cut levels hlevels]
    exact
      hrate_value_tie levels hlevels heq S candidate hS hcandidate
        hvalue_eq hS_eq

/--
Weighted finite-level source-model version of the nonunique value-tie
Theorem 3.1 wrapper.  The model supplies the source regularity and Lean
constructs the equalized endpoint vector and its `Wbar_k` rate certificate;
the remaining premise is exactly the secondary-rate comparison across
primary-value ties.
-/
theorem theorem31_appropriate_finite_levels_weighted_value_tie_lexicographic_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → (Fin (S.m + 2) → ℝ) → ℝ)
    (hcut_value :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (S.m + 2))
        limitingValue S.cut)
    (hrate_cut :
      ∀ levels : Fin (S.m + 2) → ℝ, BinaryEndpointLevelVector levels →
        rate S.cut levels =
          binaryEndpointAwareAdjacentRateObjective levels S.sampleRate)
    (hrate_value_tie :
      ∀ levels : Fin (S.m + 2) → ℝ,
        BinaryEndpointLevelVector levels →
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          ∀ T : ℕ → ℝ, ∀ candidate : Fin (S.m + 2) → ℝ,
            monotoneIntervalCutpointsEndpointFeasible (S.m + 2) T →
            BinaryEndpointLevelVector candidate →
            limitingValue T = limitingValue S.cut →
            T ≠ S.cut →
              rate T candidate ≤
                binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
              S.weight)
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              monotoneIntervalCutpointsEndpointFeasible (S.m + 2) design.1 ∧
                BinaryEndpointLevelVector design.2)
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              limitingValue design.1)
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              rate design.1 design.2)
            (S.cut, levels) :=
  theorem31_strict_cutpoint_value_tie_forward_clipped_endpoint_lexicographic_certificate
    μ S.hm limitingValue rate S.cut S.hmono S.hcut_strict hcut_value
    S.sampleRate S.hsample_pos S.hsample_mono hrate_cut hrate_value_tie
    S.weight S.hweight_int S.hweight_nonneg S.hweight_cont
    S.hweight_midpoint_pos

/--
Theorem 3.1 staged source theorem with the nonunique value-tie convention
written as an ordinary secondary maximization certificate on the
primary-value fiber.  This is the paper's value-then-rate selection rule:
first choose a limiting-value maximizer, then choose endpoint levels whose
secondary rate maximizes the displayed rate among all limiting-value ties.
-/
theorem theorem31_strict_cutpoint_value_fiber_rate_max_forward_clipped_endpoint_lexicographic_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → (Fin (m + 2) → ℝ) → ℝ)
    (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (hcut_value :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (m + 2))
        limitingValue cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hrate_cut :
      ∀ levels : Fin (m + 2) → ℝ, BinaryEndpointLevelVector levels →
        rate cut levels =
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
    (hrate_value_fiber :
      ∀ levels : Fin (m + 2) → ℝ,
        BinaryEndpointLevelVector levels →
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate →
          AppliedModelingLib.Optimization.IsMaximizerOn
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
                BinaryEndpointLevelVector design.2 ∧
                limitingValue design.1 = limitingValue cut)
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              rate design.1 design.2)
            (cut, levels))
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
                BinaryEndpointLevelVector design.2)
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              limitingValue design.1)
            (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
              rate design.1 design.2)
            (cut, levels) :=
  theorem31_strict_cutpoint_value_tie_forward_clipped_endpoint_lexicographic_certificate
    μ hm limitingValue rate cut hmono hcut_strict hcut_value sampleRate
    hsample_pos hsample_mono hrate_cut
    (fun levels hlevels heq T candidate hT hcandidate hvalue_eq _hT_ne =>
      calc
        rate T candidate ≤ rate cut levels :=
          (hrate_value_fiber levels hlevels heq).le
            (y := (T, candidate)) ⟨hT, hcandidate, hvalue_eq⟩
        _ = binaryEndpointAwareAdjacentRateObjective levels sampleRate :=
          hrate_cut levels hlevels)
    weight hweight_int hweight_nonneg hweight_cont hweight_midpoint_pos

/--
Weighted finite-level source-model version of the value-fiber Theorem 3.1
wrapper.  This replaces the pointwise value-tie inequality by a standard
secondary `IsMaximizerOn` certificate over the tied limiting-value fiber.
-/
theorem theorem31_appropriate_finite_levels_weighted_value_fiber_rate_max_lexicographic_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → (Fin (S.m + 2) → ℝ) → ℝ)
    (hcut_value :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (S.m + 2))
        limitingValue S.cut)
    (hrate_cut :
      ∀ levels : Fin (S.m + 2) → ℝ, BinaryEndpointLevelVector levels →
        rate S.cut levels =
          binaryEndpointAwareAdjacentRateObjective levels S.sampleRate)
    (hrate_value_fiber :
      ∀ levels : Fin (S.m + 2) → ℝ,
        BinaryEndpointLevelVector levels →
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          AppliedModelingLib.Optimization.IsMaximizerOn
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              monotoneIntervalCutpointsEndpointFeasible (S.m + 2) design.1 ∧
                BinaryEndpointLevelVector design.2 ∧
                limitingValue design.1 = limitingValue S.cut)
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              rate design.1 design.2)
            (S.cut, levels)) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
              S.weight)
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              monotoneIntervalCutpointsEndpointFeasible (S.m + 2) design.1 ∧
                BinaryEndpointLevelVector design.2)
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              limitingValue design.1)
            (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
              rate design.1 design.2)
            (S.cut, levels) :=
  theorem31_strict_cutpoint_value_fiber_rate_max_forward_clipped_endpoint_lexicographic_certificate
    μ S.hm limitingValue rate S.cut S.hmono S.hcut_strict hcut_value
    S.sampleRate S.hsample_pos S.hsample_mono hrate_cut hrate_value_fiber
    S.weight S.hweight_int S.hweight_nonneg S.hweight_cont
    S.hweight_midpoint_pos

/--
The equispaced cutpoints attain the Kendall constant-weight interval objective
value used in Lemma C.11.
-/
theorem lemmaC11_kendall_constant_weight_interval_objective_equispaced_eq
    {M : ℕ} (hM : 0 < M) :
    kendallConstantWeightIntervalObjective M (equispacedIntervalCutpoint M) =
      (1 - (M : ℝ)⁻¹) / 2 := by
  have hsum :
      (∑ i : Fin M,
          (equispacedIntervalCutpoint M (i.1 + 1) -
            equispacedIntervalCutpoint M i.1) ^ 2) =
        (M : ℝ)⁻¹ := by
    calc
      (∑ i : Fin M,
          (equispacedIntervalCutpoint M (i.1 + 1) -
            equispacedIntervalCutpoint M i.1) ^ 2)
          = ∑ _i : Fin M, ((M : ℝ)⁻¹) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [equispacedIntervalCutpoint_gap hM i]
      _ = (M : ℝ)⁻¹ := by
            have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
            calc
              (∑ _i : Fin M, ((M : ℝ)⁻¹) ^ 2)
                  = (M : ℝ) * ((M : ℝ)⁻¹) ^ 2 := by
                    simp
              _ = (M : ℝ)⁻¹ := by
                    field_simp [hM_ne]
  simp [kendallConstantWeightIntervalObjective,
    kendallConstantWeightGapObjective, hsum]

/--
Lemma C.11 finite-simplex optimizer: among interval gaps summing to one, the
constant-weight Kendall objective is at most its uniform-gap value.
-/
theorem lemmaC11_kendall_constant_weight_gap_objective_le_uniform
    {M : ℕ} [Nonempty (Fin M)]
    (gap : Fin M → ℝ)
    (hgap_sum : (∑ i : Fin M, gap i) = 1) :
    kendallConstantWeightGapObjective gap ≤
      (1 - (M : ℝ)⁻¹) / 2 := by
  have h :=
    AppliedModelingLib.simplex_one_sub_sum_sq_div_two_le_uniform gap hgap_sum
  simpa [kendallConstantWeightGapObjective] using h

/--
Lemma C.11 source-sum form: the constant-weight ordered interval-pair
objective is at most the equispaced value whenever the interval gaps sum to
one.
-/
theorem lemmaC11_kendall_constant_weight_ordered_pair_gap_objective_le_uniform
    {M : ℕ} [Nonempty (Fin M)]
    (gap : Fin M → ℝ)
    (hgap_sum : (∑ i : Fin M, gap i) = 1) :
    (∑ i : Fin M, ∑ j : Fin M,
        if i < j then gap i * gap j else 0) ≤
      (1 - (M : ℝ)⁻¹) / 2 := by
  rw [AppliedModelingLib.FiniteSum.ordered_pair_mul_sum_eq_one_sub_sum_sq_div_two
    gap hgap_sum]
  exact lemmaC11_kendall_constant_weight_gap_objective_le_uniform gap hgap_sum

/--
Lemma C.11 endpoint-cutpoint form: any interval partition with endpoints
`0` and `1` has Kendall constant-weight objective at most the equispaced
partition value.
-/
theorem lemmaC11_kendall_constant_weight_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    kendallConstantWeightIntervalObjective M s ≤
      (1 - (M : ℝ)⁻¹) / 2 := by
  have hgap_sum :
      (∑ i : Fin M, (s (i.1 + 1) - s i.1)) = 1 := by
    calc
      (∑ i : Fin M, (s (i.1 + 1) - s i.1))
          = ∑ k ∈ Finset.range M, (s (k + 1) - s k) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ => s (k + 1) - s k) M]
      _ = 1 := by
            simpa [h0, hM] using AppliedModelingLib.sum_range_adjacent_sub s M
  exact
    lemmaC11_kendall_constant_weight_gap_objective_le_uniform
      (M := M) (fun i : Fin M => s (i.1 + 1) - s i.1) hgap_sum

/--
Lemma C.11 optimizer form: the equispaced cutpoints maximize the equivalent
constant-weight Kendall gap objective among endpoint-feasible interval
cutpoints.
-/
theorem lemmaC11_kendall_constant_weight_interval_objective_equispaced_isMaximizerOn
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (intervalCutpointsEndpointFeasible M)
      (kendallConstantWeightIntervalObjective M)
      (equispacedIntervalCutpoint M) := by
  refine ⟨?_, ?_⟩
  · exact ⟨equispacedIntervalCutpoint_zero M,
      equispacedIntervalCutpoint_self hM⟩
  · intro s hs
    calc
      kendallConstantWeightIntervalObjective M s
          ≤ (1 - (M : ℝ)⁻¹) / 2 :=
            lemmaC11_kendall_constant_weight_interval_objective_le_equispaced
              s hs.1 hs.2
      _ = kendallConstantWeightIntervalObjective M
            (equispacedIntervalCutpoint M) := by
            rw [lemmaC11_kendall_constant_weight_interval_objective_equispaced_eq hM]

/--
Lemma C.11 endpoint-cutpoint source-sum form: the ordered constant-weight
interval-pair sum in equation (27) is maximized by equispaced intervals.
-/
theorem lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    (∑ i : Fin M, ∑ j : Fin M,
        if i < j then
          (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
        else 0) ≤
      (1 - (M : ℝ)⁻¹) / 2 := by
  have hgap_sum :
      (∑ i : Fin M, (s (i.1 + 1) - s i.1)) = 1 := by
    calc
      (∑ i : Fin M, (s (i.1 + 1) - s i.1))
          = ∑ k ∈ Finset.range M, (s (k + 1) - s k) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ => s (k + 1) - s k) M]
      _ = 1 := by
            simpa [h0, hM] using AppliedModelingLib.sum_range_adjacent_sub s M
  exact
    lemmaC11_kendall_constant_weight_ordered_pair_gap_objective_le_uniform
      (M := M) (fun i : Fin M => s (i.1 + 1) - s i.1) hgap_sum

/--
Lemma C.11 attainment in the source ordered-pair objective: equispaced
cutpoints attain the constant-weight Kendall value.
-/
theorem lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_eq
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    (∑ i : Fin M, ∑ j : Fin M,
        if i < j then
          (equispacedIntervalCutpoint M (i.1 + 1) -
              equispacedIntervalCutpoint M i.1) *
            (equispacedIntervalCutpoint M (j.1 + 1) -
              equispacedIntervalCutpoint M j.1)
        else 0) =
      (1 - (M : ℝ)⁻¹) / 2 := by
  have hgap_sum :
      (∑ i : Fin M,
          (equispacedIntervalCutpoint M (i.1 + 1) -
            equispacedIntervalCutpoint M i.1)) = 1 := by
    calc
      (∑ i : Fin M,
          (equispacedIntervalCutpoint M (i.1 + 1) -
            equispacedIntervalCutpoint M i.1))
          = ∑ k ∈ Finset.range M,
              (equispacedIntervalCutpoint M (k + 1) -
                equispacedIntervalCutpoint M k) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ =>
                equispacedIntervalCutpoint M (k + 1) -
                  equispacedIntervalCutpoint M k) M]
      _ = 1 := by
            simpa [equispacedIntervalCutpoint_zero M,
              equispacedIntervalCutpoint_self hM]
              using
                AppliedModelingLib.sum_range_adjacent_sub
                  (equispacedIntervalCutpoint M) M
  rw [AppliedModelingLib.FiniteSum.ordered_pair_mul_sum_eq_one_sub_sum_sq_div_two
    (fun i : Fin M =>
      equispacedIntervalCutpoint M (i.1 + 1) -
        equispacedIntervalCutpoint M i.1) hgap_sum]
  exact lemmaC11_kendall_constant_weight_interval_objective_equispaced_eq hM

/--
Lemma C.11 source optimizer form: the equispaced cutpoints maximize the
constant-weight Kendall ordered-pair interval objective.
-/
theorem lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (intervalCutpointsEndpointFeasible M)
      (fun s : ℕ → ℝ =>
        ∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
          else 0)
      (equispacedIntervalCutpoint M) := by
  refine ⟨?_, ?_⟩
  · exact ⟨equispacedIntervalCutpoint_zero M,
      equispacedIntervalCutpoint_self hM⟩
  · intro s hs
    calc
      (∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
          else 0)
          ≤ (1 - (M : ℝ)⁻¹) / 2 :=
            lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
              s hs.1 hs.2
      _ = (∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (equispacedIntervalCutpoint M (i.1 + 1) -
                equispacedIntervalCutpoint M i.1) *
              (equispacedIntervalCutpoint M (j.1 + 1) -
                equispacedIntervalCutpoint M j.1)
          else 0) := by
            rw [lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_eq hM]

/--
Lemma C.11 value-tie rigidity: if an endpoint-feasible interval partition ties
the equispaced value in the source ordered-pair Kendall objective, then all
its adjacent gaps are uniform.
-/
theorem lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_eq_equispaced_uniform_gap
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M)
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hsM : s M = 1)
    (heq :
      (∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
          else 0) =
        (∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (equispacedIntervalCutpoint M (i.1 + 1) -
                equispacedIntervalCutpoint M i.1) *
              (equispacedIntervalCutpoint M (j.1 + 1) -
                equispacedIntervalCutpoint M j.1)
          else 0)) :
    ∀ i : Fin M, s (i.1 + 1) - s i.1 = (M : ℝ)⁻¹ := by
  let gap : Fin M → ℝ := fun i => s (i.1 + 1) - s i.1
  have hgap_sum : (∑ i : Fin M, gap i) = 1 := by
    calc
      (∑ i : Fin M, gap i)
          = ∑ k ∈ Finset.range M, (s (k + 1) - s k) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ => s (k + 1) - s k) M]
      _ = 1 := by
            simpa [gap, h0, hsM] using AppliedModelingLib.sum_range_adjacent_sub s M
  have hsource :
      (∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
          else 0) =
        (1 - ∑ i : Fin M, (gap i) ^ 2) / 2 := by
    simpa [gap] using
      AppliedModelingLib.FiniteSum.ordered_pair_mul_sum_eq_one_sub_sum_sq_div_two
        gap hgap_sum
  have hequi :
      (∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (equispacedIntervalCutpoint M (i.1 + 1) -
                equispacedIntervalCutpoint M i.1) *
              (equispacedIntervalCutpoint M (j.1 + 1) -
                equispacedIntervalCutpoint M j.1)
          else 0) =
        (1 - (M : ℝ)⁻¹) / 2 :=
    lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_eq
      hM
  have hsq : (∑ i : Fin M, (gap i) ^ 2) = (M : ℝ)⁻¹ := by
    rw [hsource, hequi] at heq
    linarith
  have huniform :=
    AppliedModelingLib.simplex_eq_inv_card_of_sum_sq_eq_inv_card
      gap hgap_sum (by simpa using hsq)
  intro i
  simpa [gap] using huniform i

/--
Theorem 3.1 Kendall branch, finite value-then-rate composition.  For the
constant-weight Kendall value objective, the equispaced cutpoints maximize the
primary value.  The secondary-rate comparison therefore only needs to be
checked on endpoint-feasible partitions whose adjacent gaps are all uniform.
-/
theorem theorem31_kendall_constant_weight_equispaced_two_stage_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M)
    {Endpoint : Type*}
    (endpointFeasible : (ℕ → ℝ) → Endpoint → Prop)
    (rate : (ℕ → ℝ) → Endpoint → ℝ)
    (tstar : Endpoint)
    (htstar : endpointFeasible (equispacedIntervalCutpoint M) tstar)
    (hrate_uniform :
      ∀ S t, intervalCutpointsEndpointFeasible M S →
        endpointFeasible S t →
        (∀ i : Fin M, S (i.1 + 1) - S i.1 = (M : ℝ)⁻¹) →
          rate S t ≤ rate (equispacedIntervalCutpoint M) tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × Endpoint =>
        intervalCutpointsEndpointFeasible M design.1 ∧
          endpointFeasible design.1 design.2)
      (fun design : (ℕ → ℝ) × Endpoint =>
        kendallConstantWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × Endpoint => rate design.1 design.2)
      (equispacedIntervalCutpoint M, tstar) := by
  refine
    theorem31_partition_endpoint_two_stage_lexicographic_optimality
      (Partition := ℕ → ℝ) (Endpoint := Endpoint)
      (intervalCutpointsEndpointFeasible M)
      endpointFeasible
      (kendallConstantWeightOrderedPairIntervalObjective M)
      rate
      (equispacedIntervalCutpoint M)
      tstar
      ?hvalue htstar ?hrate
  · simpa [kendallConstantWeightOrderedPairIntervalObjective] using
      lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
        (M := M) hM
  · intro S t hS ht hvalue_eq
    have huniform :
        ∀ i : Fin M, S (i.1 + 1) - S i.1 = (M : ℝ)⁻¹ :=
      lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_eq_equispaced_uniform_gap
        (M := M) hM S hS.1 hS.2
        (by
          simpa [kendallConstantWeightOrderedPairIntervalObjective] using
            hvalue_eq)
    exact hrate_uniform S t hS ht huniform

/--
Theorem 3.1 Kendall branch in finite source-cutpoint form.  It is enough to
compare the secondary rate on alternatives whose finite cutpoint range agrees
with the equispaced source partition.
-/
theorem theorem31_kendall_constant_weight_equispaced_two_stage_lexicographic_optimality_of_rate_on_equispaced_range
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M)
    {Endpoint : Type*}
    (endpointFeasible : (ℕ → ℝ) → Endpoint → Prop)
    (rate : (ℕ → ℝ) → Endpoint → ℝ)
    (tstar : Endpoint)
    (htstar : endpointFeasible (equispacedIntervalCutpoint M) tstar)
    (hrate_equispaced_range :
      ∀ S t, intervalCutpointsEndpointFeasible M S →
        endpointFeasible S t →
        (∀ k : ℕ, k ≤ M → S k = equispacedIntervalCutpoint M k) →
          rate S t ≤ rate (equispacedIntervalCutpoint M) tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × Endpoint =>
        intervalCutpointsEndpointFeasible M design.1 ∧
          endpointFeasible design.1 design.2)
      (fun design : (ℕ → ℝ) × Endpoint =>
        kendallConstantWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × Endpoint => rate design.1 design.2)
      (equispacedIntervalCutpoint M, tstar) :=
  theorem31_kendall_constant_weight_equispaced_two_stage_lexicographic_optimality
    (M := M) hM endpointFeasible rate tstar htstar
    (by
      intro S t hS ht huniform
      exact hrate_equispaced_range S t hS ht
        (intervalCutpoints_eq_equispacedIntervalCutpoint_of_uniform_gap
          S hS.1 huniform))

/--
Lemma C.12 Spearman interval objective in gap-vector form.  For linear
distance weights, the source objective is equivalent to
`(1 - ∑ gap_i^3) / 6`; this expression is maximized by the uniform gap vector.
-/
def spearmanLinearWeightGapObjective {M : ℕ} (gap : Fin M → ℝ) : ℝ :=
  (1 - ∑ i : Fin M, (gap i) ^ 3) / 6

/-- Lemma C.12 interval objective written from endpoint cutpoints. -/
def spearmanLinearWeightIntervalObjective (M : ℕ) (s : ℕ → ℝ) : ℝ :=
  spearmanLinearWeightGapObjective
    (M := M) (fun i : Fin M => s (i.1 + 1) - s i.1)

/--
The equispaced cutpoints attain the Spearman linear-weight interval objective
value used in Lemma C.12.
-/
theorem lemmaC12_spearman_linear_weight_interval_objective_equispaced_eq
    {M : ℕ} (hM : 0 < M) :
    spearmanLinearWeightIntervalObjective M (equispacedIntervalCutpoint M) =
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 := by
  have hsum :
      (∑ i : Fin M,
          (equispacedIntervalCutpoint M (i.1 + 1) -
            equispacedIntervalCutpoint M i.1) ^ 3) =
        ((M : ℝ)⁻¹) ^ 2 := by
    calc
      (∑ i : Fin M,
          (equispacedIntervalCutpoint M (i.1 + 1) -
            equispacedIntervalCutpoint M i.1) ^ 3)
          = ∑ _i : Fin M, ((M : ℝ)⁻¹) ^ 3 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [equispacedIntervalCutpoint_gap hM i]
      _ = ((M : ℝ)⁻¹) ^ 2 := by
            have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
            calc
              (∑ _i : Fin M, ((M : ℝ)⁻¹) ^ 3)
                  = (M : ℝ) * ((M : ℝ)⁻¹) ^ 3 := by
                    simp
              _ = ((M : ℝ)⁻¹) ^ 2 := by
                    field_simp [hM_ne]
  simp [spearmanLinearWeightIntervalObjective,
    spearmanLinearWeightGapObjective, hsum]

/--
Lemma C.10 source-integral reduction for Spearman's rho: for a partition of
`[0,1]`, the ordered interval-pair linear-distance objective is exactly the
cubic gap objective used in Lemma C.12.
-/
theorem lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    (M : ℕ) (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightOrderedPairIntervalObjective M s =
      spearmanLinearWeightIntervalObjective M s := by
  let gap : ℕ → ℝ := fun i => s (i + 1) - s i
  have hmid :
      ∀ i : ℕ,
        AppliedModelingLib.FiniteSum.finitePartitionMidpoint gap i =
          (s (i + 1) + s i) / 2 := by
    intro i
    have hprefix :
        AppliedModelingLib.FiniteSum.finitePartitionPrefix gap i = s i := by
      have htel := AppliedModelingLib.sum_range_adjacent_sub s i
      simpa [gap, AppliedModelingLib.FiniteSum.finitePartitionPrefix, h0] using htel
    rw [AppliedModelingLib.FiniteSum.finitePartitionMidpoint, hprefix]
    simp [gap]
    ring
  have hsource :
      spearmanLinearWeightOrderedPairIntervalObjective M s =
        AppliedModelingLib.FiniteSum.orderedPairLinearGapObjectiveRange gap M := by
    unfold spearmanLinearWeightOrderedPairIntervalObjective
    unfold AppliedModelingLib.FiniteSum.orderedPairLinearGapObjectiveRange
    refine Finset.sum_congr rfl ?_
    intro i _hi
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hij : i < j
    · simp [hij, gap, hmid i, hmid j]
    · simp [hij]
  have hprefixM :
      AppliedModelingLib.FiniteSum.finitePartitionPrefix gap M = 1 := by
    have htel := AppliedModelingLib.sum_range_adjacent_sub s M
    simpa [gap, AppliedModelingLib.FiniteSum.finitePartitionPrefix, h0, hM] using htel
  rw [hsource,
    AppliedModelingLib.FiniteSum.orderedPairLinearGapObjectiveRange_eq_cube_sub_sum_cube_div_six,
    hprefixM]
  unfold spearmanLinearWeightIntervalObjective spearmanLinearWeightGapObjective
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (s (i + 1) - s i) ^ 3) M]
  simp [gap]

/--
Lemma C.12 finite-simplex optimizer: among nonnegative interval gaps summing
to one, the Spearman linear-weight objective is at most its uniform-gap value.
-/
theorem lemmaC12_spearman_linear_weight_gap_objective_le_uniform
    {M : ℕ} [Nonempty (Fin M)]
    (gap : Fin M → ℝ)
    (hgap_nonneg : ∀ i : Fin M, 0 ≤ gap i)
    (hgap_sum : (∑ i : Fin M, gap i) = 1) :
    spearmanLinearWeightGapObjective gap ≤
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 := by
  have h :=
    AppliedModelingLib.simplex_one_sub_sum_cube_div_six_le_uniform
      gap hgap_nonneg hgap_sum
  simpa [spearmanLinearWeightGapObjective] using h

/--
Lemma C.12 endpoint-cutpoint form: any monotone interval partition with
endpoints `0` and `1` has Spearman linear-weight objective at most the
equispaced partition value.
-/
theorem lemmaC12_spearman_linear_weight_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightIntervalObjective M s ≤
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 := by
  have hgap_nonneg :
      ∀ i : Fin M, 0 ≤ s (i.1 + 1) - s i.1 := by
    intro i
    exact sub_nonneg.mpr (hmono (Nat.le_succ i.1))
  have hgap_sum :
      (∑ i : Fin M, (s (i.1 + 1) - s i.1)) = 1 := by
    calc
      (∑ i : Fin M, (s (i.1 + 1) - s i.1))
          = ∑ k ∈ Finset.range M, (s (k + 1) - s k) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ => s (k + 1) - s k) M]
      _ = 1 := by
            simpa [h0, hM] using AppliedModelingLib.sum_range_adjacent_sub s M
  exact
    lemmaC12_spearman_linear_weight_gap_objective_le_uniform
      (M := M) (fun i : Fin M => s (i.1 + 1) - s i.1)
      hgap_nonneg hgap_sum

/--
Lemma C.12 optimizer form: the equispaced cutpoints maximize the equivalent
Spearman linear-weight gap objective among monotone endpoint-feasible interval
cutpoints.
-/
theorem lemmaC12_spearman_linear_weight_interval_objective_equispaced_isMaximizerOn
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (monotoneIntervalCutpointsEndpointFeasible M)
      (spearmanLinearWeightIntervalObjective M)
      (equispacedIntervalCutpoint M) := by
  refine ⟨?_, ?_⟩
  · exact ⟨monotone_equispacedIntervalCutpoint M,
      equispacedIntervalCutpoint_zero M,
      equispacedIntervalCutpoint_self hM⟩
  · intro s hs
    calc
      spearmanLinearWeightIntervalObjective M s
          ≤ (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
            lemmaC12_spearman_linear_weight_interval_objective_le_equispaced
              s hs.1 hs.2.1 hs.2.2
      _ = spearmanLinearWeightIntervalObjective M
            (equispacedIntervalCutpoint M) := by
            rw [lemmaC12_spearman_linear_weight_interval_objective_equispaced_eq hM]

/--
Lemma C.12 source-sum form: using Lemma C.10's source reduction, the ordered
linear-distance interval-pair objective is maximized by equispaced intervals.
-/
theorem lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightOrderedPairIntervalObjective M s ≤
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 := by
  rw [lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    M s h0 hM]
  exact lemmaC12_spearman_linear_weight_interval_objective_le_equispaced
    s hmono h0 hM

/--
Lemma C.12 attainment in the source ordered-pair objective: equispaced
cutpoints attain the Spearman linear-weight value.
-/
theorem lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_eq
    {M : ℕ} (hM : 0 < M) :
    spearmanLinearWeightOrderedPairIntervalObjective M
        (equispacedIntervalCutpoint M) =
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 := by
  rw [lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    M (equispacedIntervalCutpoint M)
    (equispacedIntervalCutpoint_zero M)
    (equispacedIntervalCutpoint_self hM)]
  exact lemmaC12_spearman_linear_weight_interval_objective_equispaced_eq hM

/--
Lemma C.12 source optimizer form: the equispaced cutpoints maximize the
Spearman ordered-pair interval objective among monotone endpoint-feasible
cutpoints.
-/
theorem lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (monotoneIntervalCutpointsEndpointFeasible M)
      (spearmanLinearWeightOrderedPairIntervalObjective M)
      (equispacedIntervalCutpoint M) := by
  refine ⟨?_, ?_⟩
  · exact ⟨monotone_equispacedIntervalCutpoint M,
      equispacedIntervalCutpoint_zero M,
      equispacedIntervalCutpoint_self hM⟩
  · intro s hs
    calc
      spearmanLinearWeightOrderedPairIntervalObjective M s
          ≤ (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
            lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
              s hs.1 hs.2.1 hs.2.2
      _ = spearmanLinearWeightOrderedPairIntervalObjective M
            (equispacedIntervalCutpoint M) := by
            rw [lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_eq hM]

/--
Lemma C.12 value-tie rigidity: if a monotone endpoint-feasible interval
partition ties the equispaced value in the source ordered-pair Spearman
objective, then all adjacent gaps are uniform.
-/
theorem lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_eq_equispaced_uniform_gap
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M)
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hsM : s M = 1)
    (heq :
      spearmanLinearWeightOrderedPairIntervalObjective M s =
        spearmanLinearWeightOrderedPairIntervalObjective M
          (equispacedIntervalCutpoint M)) :
    ∀ i : Fin M, s (i.1 + 1) - s i.1 = (M : ℝ)⁻¹ := by
  let gap : Fin M → ℝ := fun i => s (i.1 + 1) - s i.1
  have hgap_nonneg : ∀ i : Fin M, 0 ≤ gap i := by
    intro i
    exact sub_nonneg.mpr (hmono (Nat.le_succ i.1))
  have hgap_sum : (∑ i : Fin M, gap i) = 1 := by
    calc
      (∑ i : Fin M, gap i)
          = ∑ k ∈ Finset.range M, (s (k + 1) - s k) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ => s (k + 1) - s k) M]
      _ = 1 := by
            simpa [gap, h0, hsM] using AppliedModelingLib.sum_range_adjacent_sub s M
  have hsource :
      spearmanLinearWeightOrderedPairIntervalObjective M s =
        (1 - ∑ i : Fin M, (gap i) ^ 3) / 6 := by
    rw [lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
      M s h0 hsM]
    simp [spearmanLinearWeightIntervalObjective,
      spearmanLinearWeightGapObjective, gap]
  have hequi :
      spearmanLinearWeightOrderedPairIntervalObjective M
          (equispacedIntervalCutpoint M) =
        (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
    lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_eq
      hM
  have hcube : (∑ i : Fin M, (gap i) ^ 3) = ((M : ℝ)⁻¹) ^ 2 := by
    rw [hsource, hequi] at heq
    linarith
  have huniform :=
    AppliedModelingLib.simplex_eq_inv_card_of_sum_cube_eq_inv_card_sq
      gap hgap_nonneg hgap_sum (by simpa using hcube)
  intro i
  simpa [gap] using huniform i

/--
Theorem 3.1 Spearman branch, finite value-then-rate composition.  For the
linear-weight Spearman value objective, the equispaced cutpoints maximize the
primary value, and the secondary-rate comparison only has to be checked on
monotone endpoint-feasible partitions with uniform adjacent gaps.
-/
theorem theorem31_spearman_linear_weight_equispaced_two_stage_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M)
    {Endpoint : Type*}
    (endpointFeasible : (ℕ → ℝ) → Endpoint → Prop)
    (rate : (ℕ → ℝ) → Endpoint → ℝ)
    (tstar : Endpoint)
    (htstar : endpointFeasible (equispacedIntervalCutpoint M) tstar)
    (hrate_uniform :
      ∀ S t, monotoneIntervalCutpointsEndpointFeasible M S →
        endpointFeasible S t →
        (∀ i : Fin M, S (i.1 + 1) - S i.1 = (M : ℝ)⁻¹) →
          rate S t ≤ rate (equispacedIntervalCutpoint M) tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × Endpoint =>
        monotoneIntervalCutpointsEndpointFeasible M design.1 ∧
          endpointFeasible design.1 design.2)
      (fun design : (ℕ → ℝ) × Endpoint =>
        spearmanLinearWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × Endpoint => rate design.1 design.2)
      (equispacedIntervalCutpoint M, tstar) := by
  refine
    theorem31_partition_endpoint_two_stage_lexicographic_optimality
      (Partition := ℕ → ℝ) (Endpoint := Endpoint)
      (monotoneIntervalCutpointsEndpointFeasible M)
      endpointFeasible
      (spearmanLinearWeightOrderedPairIntervalObjective M)
      rate
      (equispacedIntervalCutpoint M)
      tstar
      ?hvalue htstar ?hrate
  · exact
      lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
        (M := M) hM
  · intro S t hS ht hvalue_eq
    have huniform :
        ∀ i : Fin M, S (i.1 + 1) - S i.1 = (M : ℝ)⁻¹ :=
      lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_eq_equispaced_uniform_gap
        (M := M) hM S hS.1 hS.2.1 hS.2.2
        hvalue_eq
    exact hrate_uniform S t hS ht huniform

/--
Theorem 3.1 Spearman branch in finite source-cutpoint form.  It is enough to
compare the secondary rate on monotone alternatives whose finite cutpoint
range agrees with the equispaced source partition.
-/
theorem theorem31_spearman_linear_weight_equispaced_two_stage_lexicographic_optimality_of_rate_on_equispaced_range
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M)
    {Endpoint : Type*}
    (endpointFeasible : (ℕ → ℝ) → Endpoint → Prop)
    (rate : (ℕ → ℝ) → Endpoint → ℝ)
    (tstar : Endpoint)
    (htstar : endpointFeasible (equispacedIntervalCutpoint M) tstar)
    (hrate_equispaced_range :
      ∀ S t, monotoneIntervalCutpointsEndpointFeasible M S →
        endpointFeasible S t →
        (∀ k : ℕ, k ≤ M → S k = equispacedIntervalCutpoint M k) →
          rate S t ≤ rate (equispacedIntervalCutpoint M) tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × Endpoint =>
        monotoneIntervalCutpointsEndpointFeasible M design.1 ∧
          endpointFeasible design.1 design.2)
      (fun design : (ℕ → ℝ) × Endpoint =>
        spearmanLinearWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × Endpoint => rate design.1 design.2)
      (equispacedIntervalCutpoint M, tstar) :=
  theorem31_spearman_linear_weight_equispaced_two_stage_lexicographic_optimality
    (M := M) hM endpointFeasible rate tstar htstar
    (by
      intro S t hS ht huniform
      exact hrate_equispaced_range S t hS ht
        (intervalCutpoints_eq_equispacedIntervalCutpoint_of_uniform_gap
          S hS.2.1 huniform))

/--
Theorem 3.1 Kendall example branch with the canonical endpoint-rate optimizer.
Equispaced cutpoints maximize the constant-weight Kendall primary value, and
the canonical uniform equalized endpoint levels maximize the finite
large-deviation rate objective on the value-tie fiber.
-/
theorem theorem31_kendall_constant_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        intervalCutpointsEndpointFeasible M design.1 ∧
          BinaryEndpointLevelVector design.2)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        kendallConstantWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        binaryEndpointAwareAdjacentRateObjective design.2
          (fun _ : Fin (M + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint M,
        canonicalUniformEqualizedEndpointLevels M) :=
  theorem31_kendall_constant_weight_equispaced_two_stage_lexicographic_optimality
    (M := M) hM
    (fun _ t => BinaryEndpointLevelVector t)
    (fun _ t =>
      binaryEndpointAwareAdjacentRateObjective t
        (fun _ : Fin (M + 2) => (1 : ℝ)))
    (canonicalUniformEqualizedEndpointLevels M)
    (canonicalUniformEqualizedEndpointLevels_levelVector M)
    (by
      intro _S t _hS ht _huniform
      exact (canonicalUniformEqualizedEndpointLevels_isMaximizerOn M).2 t ht)

/--
Theorem 3.1 Spearman example branch with the canonical endpoint-rate
optimizer.  Equispaced cutpoints maximize the linear-weight Spearman primary
value, and the canonical uniform equalized endpoint levels maximize the finite
large-deviation rate objective on the value-tie fiber.
-/
theorem theorem31_spearman_linear_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        monotoneIntervalCutpointsEndpointFeasible M design.1 ∧
          BinaryEndpointLevelVector design.2)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        spearmanLinearWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        binaryEndpointAwareAdjacentRateObjective design.2
          (fun _ : Fin (M + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint M,
        canonicalUniformEqualizedEndpointLevels M) :=
  theorem31_spearman_linear_weight_equispaced_two_stage_lexicographic_optimality
    (M := M) hM
    (fun _ t => BinaryEndpointLevelVector t)
    (fun _ t =>
      binaryEndpointAwareAdjacentRateObjective t
        (fun _ : Fin (M + 2) => (1 : ℝ)))
    (canonicalUniformEqualizedEndpointLevels M)
    (canonicalUniformEqualizedEndpointLevels_levelVector M)
    (by
      intro _S t _hS ht _huniform
      exact (canonicalUniformEqualizedEndpointLevels_isMaximizerOn M).2 t ht)

/--
Theorem 3.1 Kendall branch in the same source-normalized indexing convention
used by `theorem31SourceWbar`.  Equispaced cutpoints maximize the
constant-weight Kendall primary objective over the `m + 2` source cells, while
the canonical uniform endpoint chain maximizes the adjacent-rate secondary
objective over endpoint vectors of length `m + 2`.
-/
theorem theorem31_kendall_constant_weight_equispaced_source_endpoint_lexicographic_optimality
    (m : ℕ) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
        intervalCutpointsEndpointFeasible (m + 2) design.1 ∧
          BinaryEndpointLevelVector design.2)
      (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
        kendallConstantWeightOrderedPairIntervalObjective (m + 2) design.1)
      (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
        binaryEndpointAwareAdjacentRateObjective design.2
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint (m + 2),
        canonicalUniformEqualizedEndpointLevels m) := by
  classical
  have hM : 0 < m + 2 := by omega
  haveI : Nonempty (Fin (m + 2)) := ⟨⟨0, hM⟩⟩
  refine
    theorem31_partition_endpoint_two_stage_lexicographic_optimality
      (Partition := ℕ → ℝ) (Endpoint := Fin (m + 2) → ℝ)
      (intervalCutpointsEndpointFeasible (m + 2))
      (fun _S levels => BinaryEndpointLevelVector levels)
      (kendallConstantWeightOrderedPairIntervalObjective (m + 2))
      (fun _S levels =>
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint (m + 2))
      (canonicalUniformEqualizedEndpointLevels m)
      ?hvalue ?hlevels ?hrate
  · exact
      lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
        (M := m + 2) hM
  · exact canonicalUniformEqualizedEndpointLevels_levelVector m
  · intro _S levels _hS hlevels _hvalue_eq
    exact (canonicalUniformEqualizedEndpointLevels_isMaximizerOn m).le hlevels

/--
Theorem 3.1 Kendall source branch with both pieces needed by the paper's
decomposition: the source-normalized equispaced/canonical design is
lexicographically optimal for the Kendall primary value and adjacent-rate
secondary criterion, and the corresponding source-defined `Wbar_k` sequence
has a positive exponential-rate certificate.
-/
theorem theorem31_kendall_constant_weight_equispaced_source_endpoint_lexicographic_optimality_and_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ
          (equispacedIntervalCutpoint (m + 2))
          (monotone_equispacedIntervalCutpoint (m + 2))
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          (fun _ : ℝ × ℝ => (1 : ℝ)))
        c ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          intervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          kendallConstantWeightOrderedPairIntervalObjective (m + 2) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (equispacedIntervalCutpoint (m + 2),
          canonicalUniformEqualizedEndpointLevels m) := by
  rcases
    theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_equispacedIntervalCutpoint
      μ hm with
    ⟨c, hc, hcert⟩
  exact
    ⟨c, hc, hcert,
      theorem31_kendall_constant_weight_equispaced_source_endpoint_lexicographic_optimality
        m⟩

/--
Theorem 3.1 Spearman branch in the same source-normalized indexing convention
used by `theorem31SourceWbar`.  Equispaced cutpoints maximize the linear
Spearman primary objective over the `m + 2` source cells, while the canonical
uniform endpoint chain maximizes the adjacent-rate secondary objective over
endpoint vectors of length `m + 2`.
-/
theorem theorem31_spearman_linear_weight_equispaced_source_endpoint_lexicographic_optimality
    (m : ℕ) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
        monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
          BinaryEndpointLevelVector design.2)
      (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
        spearmanLinearWeightOrderedPairIntervalObjective (m + 2) design.1)
      (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
        binaryEndpointAwareAdjacentRateObjective design.2
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint (m + 2),
        canonicalUniformEqualizedEndpointLevels m) := by
  classical
  have hM : 0 < m + 2 := by omega
  haveI : Nonempty (Fin (m + 2)) := ⟨⟨0, hM⟩⟩
  refine
    theorem31_partition_endpoint_two_stage_lexicographic_optimality
      (Partition := ℕ → ℝ) (Endpoint := Fin (m + 2) → ℝ)
      (monotoneIntervalCutpointsEndpointFeasible (m + 2))
      (fun _S levels => BinaryEndpointLevelVector levels)
      (spearmanLinearWeightOrderedPairIntervalObjective (m + 2))
      (fun _S levels =>
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint (m + 2))
      (canonicalUniformEqualizedEndpointLevels m)
      ?hvalue ?hlevels ?hrate
  · exact
      lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
        (M := m + 2) hM
  · exact canonicalUniformEqualizedEndpointLevels_levelVector m
  · intro _S levels _hS hlevels _hvalue_eq
    exact (canonicalUniformEqualizedEndpointLevels_isMaximizerOn m).le hlevels

/--
Theorem 3.1 Spearman source branch with both pieces needed by the paper's
decomposition: the source-normalized equispaced/canonical design is
lexicographically optimal for the Spearman primary value and adjacent-rate
secondary criterion, and the corresponding source-defined `Wbar_k` sequence
has a positive exponential-rate certificate.
-/
theorem theorem31_spearman_linear_weight_equispaced_source_endpoint_lexicographic_optimality_and_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ
          (equispacedIntervalCutpoint (m + 2))
          (monotone_equispacedIntervalCutpoint (m + 2))
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          (fun _ : ℝ × ℝ => (1 : ℝ)))
        c ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          spearmanLinearWeightOrderedPairIntervalObjective (m + 2) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (equispacedIntervalCutpoint (m + 2),
          canonicalUniformEqualizedEndpointLevels m) := by
  rcases
    theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_equispacedIntervalCutpoint
      μ hm with
    ⟨c, hc, hcert⟩
  exact
    ⟨c, hc, hcert,
      theorem31_spearman_linear_weight_equispaced_source_endpoint_lexicographic_optimality
        m⟩

/--
Lemma B.2 finite-coordinate learning step.  For a fixed finite set of
representative items and a finite question set, coordinatewise convergence of
the empirical responses is uniform over item-question pairs.  This is the
finite-uniformization step following the Strong Law of Large Numbers in the
source proof.
-/
theorem lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise
    {Item Y : Type*} [Fintype Item] [Fintype Y]
    (psiHat : ℕ → Item → Y → ℝ) (psiAt : Item → Y → ℝ)
    (hpoint :
      ∀ i : Item, ∀ y : Y,
        Tendsto (fun N : ℕ => psiHat N i y) atTop (nhds (psiAt i y))) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : Item × Y => psiHat N p.1 p.2)
      (fun p : Item × Y => psiAt p.1 p.2) atTop Set.univ := by
  exact
    AppliedModelingLib.Math.tendstoUniformlyOn_univ_of_fintype
      (fun N : ℕ => fun p : Item × Y => psiHat N p.1 p.2)
      (fun p : Item × Y => psiAt p.1 p.2)
      (by
        intro p
        exact hpoint p.1 p.2)

/--
Lemma B.3 fixed-finite learning step.  Once the unknown-type experiment has a
fixed finite set of ranked items, coordinatewise convergence of the empirical
responses is uniform over ranked item-question pairs.  The separate ranking
consistency step is handled by the representative-tracking lemma below.
-/
theorem lemmaB3_unknownTypeExperiment_fixed_finite_uniform_of_pointwise
    {RankedItem Y : Type*} [Fintype RankedItem] [Fintype Y]
    (psiHat : ℕ → RankedItem → Y → ℝ) (psiAt : RankedItem → Y → ℝ)
    (hpoint :
      ∀ i : RankedItem, ∀ y : Y,
        Tendsto (fun N : ℕ => psiHat N i y) atTop (nhds (psiAt i y))) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : RankedItem × Y => psiHat N p.1 p.2)
      (fun p : RankedItem × Y => psiAt p.1 p.2) atTop Set.univ := by
  exact
    lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise
      psiHat psiAt hpoint

/--
Lemma B.2 finite-question product step.  If every question coordinate of the
known-type estimator converges uniformly on `[0,1]`, then the estimator
converges uniformly on the quality-question product when the question set is
finite.
-/
theorem lemmaB2_knownTypeExperiment_uniform_over_finite_questions_of_each_question
    {Y : Type*} [Finite Y]
    (psiHat : ℕ → ℝ → Y → ℝ) (psi : ℝ → Y → ℝ)
    (hquestion :
      ∀ y : Y,
        TendstoUniformlyOn (fun N : ℕ => fun θ : ℝ => psiHat N θ y)
          (fun θ : ℝ => psi θ y) atTop (Set.Icc (0 : ℝ) 1)) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × Y => psiHat N p.1 p.2)
      (fun p : ℝ × Y => psi p.1 p.2) atTop
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  exact
    AppliedModelingLib.Math.tendstoUniformlyOn_prod_right_of_finite hquestion

/--
Lemma B.3 finite-question product step.  The same finite-coordinate product
lift applies after the unknown-type ranking stage supplies per-question
uniform convergence on `[0,1]`.
-/
theorem lemmaB3_unknownTypeExperiment_uniform_over_finite_questions_of_each_question
    {Y : Type*} [Finite Y]
    (psiHat : ℕ → ℝ → Y → ℝ) (psi : ℝ → Y → ℝ)
    (hquestion :
      ∀ y : Y,
        TendstoUniformlyOn (fun N : ℕ => fun θ : ℝ => psiHat N θ y)
          (fun θ : ℝ => psi θ y) atTop (Set.Icc (0 : ℝ) 1)) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × Y => psiHat N p.1 p.2)
      (fun p : ℝ × Y => psi p.1 p.2) atTop
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  exact
    lemmaB2_knownTypeExperiment_uniform_over_finite_questions_of_each_question
      psiHat psi hquestion

/--
Lemma B.2 deterministic learning core for `KnownTypeExperiment`.  Once the
empirical response estimates track the true response at the representative
item qualities, and those representative qualities form a vanishing mesh of
`[0,1]`, Lipschitz continuity in quality gives uniform convergence of the
piecewise estimator.

The probabilistic strong-law step is isolated in `htrack`; this theorem proves
the source's deterministic Lipschitz/mesh conclusion.
-/
theorem lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking
    {Y : Type*}
    (psiHat : ℕ → ℝ → Y → ℝ) (psi : ℝ → Y → ℝ)
    (representative : ℕ → ℝ → ℝ)
    (noise mesh : ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hnoise : Tendsto noise atTop (nhds 0))
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htrack :
      ∀ᶠ n : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 → ∀ y : Y,
          dist (psiHat n θ y) (psi (representative n θ) y) ≤ noise n)
    (hrepresentative :
      ∀ᶠ n : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (representative n θ) θ ≤ mesh n)
    (hlipschitz :
      ∀ θ θ' : ℝ, ∀ y : Y,
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × Y => psiHat n p.1 p.2)
      (fun p : ℝ × Y => psi p.1 p.2) atTop
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  exact
    AppliedModelingLib.Math.tendstoUniformlyOn_prod_of_lipschitz_tracking_rep
      psiHat psi representative (Set.Icc (0 : ℝ) 1) noise mesh K hK
      hnoise hmesh htrack hrepresentative hlipschitz

/--
Lemma B.3 deterministic learning core for `UnknownTypeExperiment`.  If the
experiment's ranking stage supplies representatives whose quality percentiles
approach the target quality uniformly, and the empirical response estimates
track the true response at those representatives, then Lipschitz continuity
again gives uniform learning.

The source's probabilistic ranking-consistency and strong-law inputs are the
two visible hypotheses `hranking` and `htrack`.
-/
theorem lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking
    {Y : Type*}
    (psiHat : ℕ → ℝ → Y → ℝ) (psi : ℝ → Y → ℝ)
    (rankRepresentative : ℕ → ℝ → ℝ)
    (noise mesh : ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hnoise : Tendsto noise atTop (nhds 0))
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htrack :
      ∀ᶠ n : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 → ∀ y : Y,
          dist (psiHat n θ y) (psi (rankRepresentative n θ) y) ≤ noise n)
    (hranking :
      ∀ᶠ n : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (rankRepresentative n θ) θ ≤ mesh n)
    (hlipschitz :
      ∀ θ θ' : ℝ, ∀ y : Y,
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × Y => psiHat n p.1 p.2)
      (fun p : ℝ × Y => psi p.1 p.2) atTop
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  exact
    lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking
      psiHat psi rankRepresentative noise mesh hK hnoise hmesh htrack
      hranking hlipschitz

end

end GJ19OptimalBinaryRatingSystems

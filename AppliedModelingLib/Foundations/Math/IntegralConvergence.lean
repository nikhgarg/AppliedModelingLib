import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Finite

/-!
# Integral Convergence Helpers

Reusable measure-theoretic convergence wrappers for continuous EconCS proofs.
These statements keep paper proofs from repeatedly unpacking dominated
convergence when the source argument only uses bounded convergence on a finite
measure space.
-/

open Filter Topology
open MeasureTheory
open Set

namespace AppliedModelingLib
namespace Math

noncomputable section

/--
Continuity at a point gives an open neighborhood on which a real-valued
function differs from its value at that point by at most `ε`.
-/
theorem exists_open_abs_sub_le_of_continuousAt
    {α : Type*} [TopologicalSpace α] {f : α → ℝ} {x : α}
    (hf : ContinuousAt f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧
      ∀ y : α, y ∈ U → |f y - f x| ≤ ε := by
  have htarget : Metric.ball (f x) ε ∈ 𝓝 (f x) :=
    Metric.ball_mem_nhds (f x) hε
  have hpre : {y : α | f y ∈ Metric.ball (f x) ε} ∈ 𝓝 x :=
    hf htarget
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  have hball := hUsub hy
  have hlt : |f y - f x| < ε := by
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  exact le_of_lt hlt

/--
An eventual Lipschitz bound on a parameter set gives the local eventual
oscillation bound used by compact-uniform convergence arguments.
-/
theorem eventually_local_abs_sub_le_of_eventually_lipschitz_on
    {α : Type*} [PseudoMetricSpace α] {K : Set α}
    {F : ℕ → α → ℝ} {L : ℝ} (hL : 0 < L)
    (hLip :
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ K → ∀ y : α, y ∈ K →
          |F n y - F n x| ≤ L * dist y x) :
    ∀ x : α, x ∈ K → ∀ ε > 0,
      ∃ U : Set α,
        IsOpen U ∧ x ∈ U ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ y : α, y ∈ K → y ∈ U → |F n y - F n x| ≤ ε := by
  intro x hx ε hε
  let δ : ℝ := ε / L
  have hδ : 0 < δ := div_pos hε hL
  refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
  filter_upwards [hLip] with n hn y hy hyU
  have hdist_lt : dist y x < δ := by
    simpa [Metric.mem_ball, dist_comm] using hyU
  have hdist_le : dist y x ≤ δ := le_of_lt hdist_lt
  calc
    |F n y - F n x| ≤ L * dist y x := hn x hx y hy
    _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist_le hL.le
    _ = ε := by
      change L * (ε / L) = ε
      exact mul_div_cancel₀ ε hL.ne'

/--
Compactness upgrades local eventual bounds to a uniform eventual bound on the
compact set.  The local hypotheses may use different neighborhoods and
different burn-in indices at different points; compactness supplies a finite
subcover and the filter supplies the maximum burn-in.
-/
theorem eventually_uniform_on_compact_of_eventually_local_uniform
    {α : Type*} [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {P : ℕ → α → Prop}
    (hlocal :
      ∀ x ∈ s, ∃ U : Set α,
        IsOpen U ∧ x ∈ U ∧
          ∀ᶠ n : ℕ in atTop, ∀ y, y ∈ s → y ∈ U → P n y) :
    ∀ᶠ n : ℕ in atTop, ∀ y, y ∈ s → P n y := by
  classical
  have hlocal_sub :
      ∀ x : s, ∃ U : Set α,
        IsOpen U ∧ (x : α) ∈ U ∧
          ∀ᶠ n : ℕ in atTop, ∀ y, y ∈ s → y ∈ U → P n y := by
    intro x
    exact hlocal x x.property
  choose U hUopen hxU hUevent using hlocal_sub
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩
  rcases hs.elim_finite_subcover U hUopen hcover with ⟨t, ht⟩
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ t, ∀ y, y ∈ s → y ∈ U x → P n y := by
    exact (Finset.eventually_all t).2 (fun x _hx => hUevent x)
  filter_upwards [hevent] with n hn y hy
  have hycover := ht hy
  rcases mem_iUnion.1 hycover with ⟨x, hxcover⟩
  rcases mem_iUnion.1 hxcover with ⟨hxt, hyU⟩
  exact hn x hxt y hy hyU

/--
Real-valued specialization of
`eventually_uniform_on_compact_of_eventually_local_uniform`: local uniform
eventual `ε`-bounds on neighborhoods imply uniform eventual convergence on a
compact set.
-/
theorem eventually_uniform_abs_sub_le_on_compact_of_eventually_local_uniform
    {α : Type*} [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {F : ℕ → α → ℝ} {f : α → ℝ}
    (hlocal :
      ∀ x ∈ s, ∀ ε > 0, ∃ U : Set α,
        IsOpen U ∧ x ∈ U ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ y, y ∈ s → y ∈ U → |F n y - f y| ≤ ε) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ y, y ∈ s → |F n y - f y| ≤ ε := by
  intro ε hε
  exact
    eventually_uniform_on_compact_of_eventually_local_uniform
      (s := s) hs (P := fun n y => |F n y - f y| ≤ ε)
      (fun x hx => hlocal x hx ε hε)

/--
Compact-superset version of local-to-uniform convergence.  This is convenient
for half-open partition cells: prove local uniform estimates on a compact
ambient rectangle `K`, then restrict the resulting uniform bound to the cell
`s ⊆ K`.
-/
theorem eventually_uniform_on_subset_of_eventually_local_uniform_on_compact
    {α : Type*} [TopologicalSpace α] {s K : Set α} (hK : IsCompact K)
    (hsub : s ⊆ K) {P : ℕ → α → Prop}
    (hlocal :
      ∀ x ∈ K, ∃ U : Set α,
        IsOpen U ∧ x ∈ U ∧
          ∀ᶠ n : ℕ in atTop, ∀ y, y ∈ K → y ∈ U → P n y) :
    ∀ᶠ n : ℕ in atTop, ∀ y, y ∈ s → P n y := by
  exact
    (eventually_uniform_on_compact_of_eventually_local_uniform
      (s := K) hK hlocal).mono
      (fun _n hn y hy => hn y (hsub hy))

/--
Real-valued compact-superset version of local-to-uniform convergence.
-/
theorem eventually_uniform_abs_sub_le_on_subset_of_eventually_local_uniform_on_compact
    {α : Type*} [TopologicalSpace α] {s K : Set α} (hK : IsCompact K)
    (hsub : s ⊆ K) {F : ℕ → α → ℝ} {f : α → ℝ}
    (hlocal :
      ∀ x ∈ K, ∀ ε > 0, ∃ U : Set α,
        IsOpen U ∧ x ∈ U ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ y, y ∈ K → y ∈ U → |F n y - f y| ≤ ε) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ y, y ∈ s → |F n y - f y| ≤ ε := by
  intro ε hε
  exact
    eventually_uniform_on_subset_of_eventually_local_uniform_on_compact
      (s := s) (K := K) hK hsub
      (P := fun n y => |F n y - f y| ≤ ε)
      (fun x hx => hlocal x hx ε hε)

/--
Bounded-convergence wrapper for real-valued integrals over a finite measure:
if `F n` is uniformly bounded in norm by a constant `B` and converges almost
everywhere to `f`, then the integrals converge to the integral of `f`.
-/
theorem tendsto_integral_of_uniform_norm_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {f : α → ℝ} {B : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  exact
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := μ) (F := F) (f := f) (fun _x : α => B)
      hF_meas (MeasureTheory.integrable_const B) hbound hlim

/--
Source-shaped dominated-convergence wrapper: if `P n x` converges pointwise
almost everywhere to `1`, and the products `w x * P n x` are uniformly
bounded in norm by a constant, then the weighted integrals converge to the
integral of `w`.
-/
theorem tendsto_integral_mul_tendsto_one_of_uniform_norm_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (P : ℕ → α → ℝ) {B : ℝ}
    (hprod_meas :
      ∀ n, AEStronglyMeasurable (fun x => w x * P n x) μ)
    (hprod_bound :
      ∀ n, ∀ᵐ x ∂μ, ‖w x * P n x‖ ≤ B)
    (hP_lim : ∀ᵐ x ∂μ, Tendsto (fun n => P n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, w x * P n x ∂μ)
      atTop (𝓝 (∫ x, w x ∂μ)) := by
  have hlim :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => w x * P n x) atTop (𝓝 (w x)) := by
    filter_upwards [hP_lim] with x hx
    simpa [mul_one] using (tendsto_const_nhds.mul hx)
  exact
    tendsto_integral_of_uniform_norm_bound μ hprod_meas hprod_bound hlim

/--
Source-shaped dominated-convergence wrapper for bounded weights and factors:
if `‖w x‖ ≤ B`, `‖P n x‖ ≤ 1`, and `P n x → 1` almost everywhere, then
`∫ w * P n` converges to `∫ w`.
-/
theorem tendsto_integral_mul_tendsto_one_of_weight_norm_bound_of_factor_norm_le_one
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (P : ℕ → α → ℝ) {B : ℝ}
    (hprod_meas :
      ∀ n, AEStronglyMeasurable (fun x => w x * P n x) μ)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ B)
    (hP_bound : ∀ n, ∀ᵐ x ∂μ, ‖P n x‖ ≤ 1)
    (hP_lim : ∀ᵐ x ∂μ, Tendsto (fun n => P n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, w x * P n x ∂μ)
      atTop (𝓝 (∫ x, w x ∂μ)) := by
  refine
    tendsto_integral_mul_tendsto_one_of_uniform_norm_bound
      (B := B) μ w P hprod_meas ?_ hP_lim
  intro n
  filter_upwards [hw_bound, hP_bound n] with x hw hP
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg (w x)) hP).trans hw

/--
Nonnegative bounded-convergence wrapper: the common case where each integrand
lies between `0` and a finite constant.
-/
theorem tendsto_integral_of_nonneg_le_const
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {f : α → ℝ} {B : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x ∧ F n x ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_uniform_norm_bound (B := B) μ hF_meas ?_ hlim
  intro n
  filter_upwards [hbound n] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/--
Source-shaped bounded-convergence wrapper: if `P n x` converges pointwise
almost everywhere to `1`, and the products `w x * P n x` are uniformly
bounded between `0` and a constant, then the weighted integrals converge to
the integral of `w`.
-/
theorem tendsto_integral_mul_tendsto_one_of_nonneg_le_const
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (P : ℕ → α → ℝ) {B : ℝ}
    (hprod_meas :
      ∀ n, AEStronglyMeasurable (fun x => w x * P n x) μ)
    (hprod_bound :
      ∀ n, ∀ᵐ x ∂μ, 0 ≤ w x * P n x ∧ w x * P n x ≤ B)
    (hP_lim : ∀ᵐ x ∂μ, Tendsto (fun n => P n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, w x * P n x ∂μ)
      atTop (𝓝 (∫ x, w x ∂μ)) := by
  have hlim :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => w x * P n x) atTop (𝓝 (w x)) := by
    filter_upwards [hP_lim] with x hx
    simpa [mul_one] using (tendsto_const_nhds.mul hx)
  exact
    tendsto_integral_of_nonneg_le_const μ hprod_meas hprod_bound hlim

end

end Math
end AppliedModelingLib

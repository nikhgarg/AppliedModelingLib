import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform local Lipschitz bounds on convex sets

A Lipschitz estimate with one fixed positive distance threshold extends, with
the same constant, to every pair in a convex set.  The proof subdivides the
line segment into equal pieces and applies the polygonal triangle inequality.

We also record the elementary geometry of inner-offset sets used to obtain
such a uniform threshold inside an open convex parameter domain.
-/

namespace PZMH20PerformativePrediction.DomainGradient

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F]

/-- A uniform Lipschitz bound for sufficiently close pairs in a convex set is
a global Lipschitz bound on that set, with no differentiability assumption. -/
theorem norm_image_sub_le_of_uniform_local_on_convex
    (map : E → F) (domain : Set E) (hconvex : Convex ℝ domain)
    {constant threshold : ℝ} (hthreshold : 0 < threshold)
    (hlocal : ∀ first ∈ domain, ∀ second ∈ domain,
      ‖first - second‖ ≤ threshold →
        ‖map first - map second‖ ≤ constant * ‖first - second‖) :
    ∀ first ∈ domain, ∀ second ∈ domain,
      ‖map first - map second‖ ≤ constant * ‖first - second‖ := by
  intro first hfirst second hsecond
  obtain ⟨pieces, hpieces⟩ := exists_nat_gt (‖first - second‖ / threshold)
  have hratio_nonneg : 0 ≤ ‖first - second‖ / threshold :=
    div_nonneg (norm_nonneg _) hthreshold.le
  have hpieces_real_pos : 0 < (pieces : ℝ) :=
    lt_of_le_of_lt hratio_nonneg hpieces
  let point : ℕ → E := fun index ↦
    first + ((index : ℝ) / (pieces : ℝ)) • (second - first)
  have point_zero : point 0 = first := by simp [point]
  have point_pieces : point pieces = second := by
    simp [point, ne_of_gt hpieces_real_pos]
  have point_mem (index : ℕ) (hindex : index ≤ pieces) : point index ∈ domain := by
    apply hconvex.add_smul_sub_mem hfirst hsecond
    constructor
    · positivity
    · exact (div_le_one hpieces_real_pos).2 (Nat.cast_le.mpr hindex)
  have step_norm (index : ℕ) :
      ‖point index - point (index + 1)‖ = ‖first - second‖ / (pieces : ℝ) := by
    have hpoint_sub : point (index + 1) - point index =
        (1 / (pieces : ℝ)) • (second - first) := by
      dsimp only [point]
      module
    rw [norm_sub_rev, hpoint_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hpieces_real_pos), norm_sub_rev]
    ring
  have hstep_threshold : ‖first - second‖ / (pieces : ℝ) ≤ threshold := by
    have hscaled : ‖first - second‖ < (pieces : ℝ) * threshold :=
      (div_lt_iff₀ hthreshold).mp hpieces
    exact le_of_lt ((div_lt_iff₀ hpieces_real_pos).2 (by nlinarith))
  have step_bound (index : ℕ) (hindex : index < pieces) :
      dist (map (point index)) (map (point (index + 1))) ≤
        constant * (‖first - second‖ / (pieces : ℝ)) := by
    have hbound := hlocal (point index) (point_mem index hindex.le)
      (point (index + 1)) (point_mem (index + 1) hindex) (by
        rw [step_norm]
        exact hstep_threshold)
    simpa only [dist_eq_norm, step_norm] using hbound
  have hchain := dist_le_range_sum_of_dist_le
    (f := fun index ↦ map (point index)) pieces
    (d := fun _ ↦ constant * (‖first - second‖ / (pieces : ℝ)))
    (fun hindex ↦ step_bound _ hindex)
  change dist (map (point 0)) (map (point pieces)) ≤
    ∑ _index ∈ Finset.range pieces,
      constant * (‖first - second‖ / (pieces : ℝ)) at hchain
  rw [point_zero, point_pieces, dist_eq_norm] at hchain
  calc
    ‖map first - map second‖ ≤
        ∑ _index ∈ Finset.range pieces,
          constant * (‖first - second‖ / (pieces : ℝ)) := hchain
    _ = constant * ‖first - second‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hpieces_real_pos]

/-- `LipschitzOnWith` form of the uniform-local-to-global result. -/
theorem lipschitzOnWith_of_uniform_local_on_convex
    (map : E → F) (domain : Set E) (hconvex : Convex ℝ domain)
    {constant threshold : ℝ} (hconstant : 0 ≤ constant) (hthreshold : 0 < threshold)
    (hlocal : ∀ first ∈ domain, ∀ second ∈ domain,
      ‖first - second‖ ≤ threshold →
        ‖map first - map second‖ ≤ constant * ‖first - second‖) :
    LipschitzOnWith ⟨constant, hconstant⟩ map domain := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first hfirst second hsecond
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    norm_image_sub_le_of_uniform_local_on_convex map domain hconvex hthreshold
      hlocal first hfirst second hsecond

/-- Existential-threshold form: one positive radius on which the estimate is
uniform suffices for the global estimate. -/
theorem norm_image_sub_le_of_exists_uniform_local_on_convex
    (map : E → F) (domain : Set E) (hconvex : Convex ℝ domain)
    {constant : ℝ}
    (hlocal : ∃ threshold > 0, ∀ first ∈ domain, ∀ second ∈ domain,
      ‖first - second‖ ≤ threshold →
        ‖map first - map second‖ ≤ constant * ‖first - second‖) :
    ∀ first ∈ domain, ∀ second ∈ domain,
      ‖map first - map second‖ ≤ constant * ‖first - second‖ := by
  obtain ⟨threshold, hthreshold, hlocal⟩ := hlocal
  exact norm_image_sub_le_of_uniform_local_on_convex map domain hconvex hthreshold hlocal

/-- Points at whose closed `radius`-ball remains in `domain`. -/
def innerOffset (domain : Set E) (radius : ℝ) : Set E :=
  {point | ∀ shift : E, ‖shift‖ ≤ radius → point + shift ∈ domain}

/-- A fixed-radius inner offset of a convex set is convex. -/
theorem convex_innerOffset (domain : Set E) (radius : ℝ) (hconvex : Convex ℝ domain) :
    Convex ℝ (innerOffset domain radius) := by
  intro first hfirst second hsecond left right hleft hright hsum shift hshift
  have hfirst_shift := hfirst shift hshift
  have hsecond_shift := hsecond shift hshift
  have heq : left • first + right • second + shift =
      left • (first + shift) + right • (second + shift) := by
    calc
      left • first + right • second + shift =
          left • first + right • second + (left + right) • shift := by
            rw [hsum, one_smul]
      _ = left • (first + shift) + right • (second + shift) := by module
  rw [heq]
  exact hconvex hfirst_shift hsecond_shift hleft hright hsum

omit [NormedSpace ℝ E] in
/-- Any two points of an open set lie in a common positive-radius inner
offset.  Convexity is not needed for this fact. -/
theorem exists_common_innerOffset_of_isOpen
    (domain : Set E) (hopen : IsOpen domain) {first second : E}
    (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    ∃ radius > 0,
      first ∈ innerOffset domain radius ∧ second ∈ innerOffset domain radius := by
  obtain ⟨firstRadius, hfirstRadius, hfirstBall⟩ :=
    Metric.isOpen_iff.mp hopen first hfirst
  obtain ⟨secondRadius, hsecondRadius, hsecondBall⟩ :=
    Metric.isOpen_iff.mp hopen second hsecond
  let radius := min firstRadius secondRadius / 2
  have hradius : 0 < radius := by dsimp [radius]; positivity
  have hradius_first : radius < firstRadius := by
    dsimp [radius]
    have hmin : min firstRadius secondRadius ≤ firstRadius := min_le_left _ _
    nlinarith
  have hradius_second : radius < secondRadius := by
    dsimp [radius]
    have hmin : min firstRadius secondRadius ≤ secondRadius := min_le_right _ _
    nlinarith
  refine ⟨radius, hradius, ?_, ?_⟩
  · intro shift hshift
    apply hfirstBall
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using lt_of_le_of_lt hshift hradius_first
  · intro shift hshift
    apply hsecondBall
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using lt_of_le_of_lt hshift hradius_second

end PZMH20PerformativePrediction.DomainGradient

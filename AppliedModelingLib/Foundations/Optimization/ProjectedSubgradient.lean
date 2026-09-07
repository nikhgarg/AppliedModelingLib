import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNormsDerivative

/-!
# Projected Subgradient Methods in Finite Coordinates

Reusable vocabulary for (stochastic) projected subgradient iterations on a
finite coordinate space `Coord → ℝ`.

These definitions are paper-independent: an iteration is described by a
projection map, a trajectory, a step-size schedule, and a decomposition of the
observed step direction into a true subgradient, a zero-mean noise term, and a
bias term.

- `FiniteSubgradientAt`: the defining subgradient inequality.
- `ProjectionOnto`: a map lands in the feasible set.
- `FiniteProjectedSSGMUpdateAt` and `FollowsFiniteProjectedSSGM`: one step and
  the whole trajectory of the projected update rule.
- `FollowsFiniteProjectedSampleSubgradientMethod`: the trajectory follows the
  update rule and each direction is a subgradient of the sampled cost.
- `SSGMStepSizeConditions`: the Robbins-Monro step-size hypotheses.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Optimization

/--
`g` is a subgradient of `cost` at `x`, written with the finite-coordinate
linear functional `h ↦ ∑ i, g i * h i`.
-/
def FiniteSubgradientAt {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (x g : Coord → ℝ) : Prop :=
  ∀ y,
    cost x +
      FiniteDimensionalNorms.coordinateLinearFunctional g
        (fun i => y i - x i) ≤ cost y

theorem finiteSubgradientAt_formula {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (x g : Coord → ℝ) :
    FiniteSubgradientAt cost x g ↔
      ∀ y,
        cost x +
          FiniteDimensionalNorms.coordinateLinearFunctional g
            (fun i => y i - x i) ≤ cost y := by
  rfl

/-- The finite-coordinate linear functional as an explicit sum. -/
theorem coordinateLinearFunctional_apply {Coord : Type*} [Fintype Coord]
    (g h : Coord → ℝ) :
    FiniteDimensionalNorms.coordinateLinearFunctional g h =
      ∑ i : Coord, g i * h i := by
  simp [FiniteDimensionalNorms.coordinateLinearFunctional]

/-- A subgradient inequality restricted to a feasible set. -/
def FiniteSubgradientOn {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (X : Set (Coord → ℝ))
    (x g : Coord → ℝ) : Prop :=
  ∀ y, y ∈ X →
    cost x +
      FiniteDimensionalNorms.coordinateLinearFunctional g
        (fun i => y i - x i) ≤ cost y

/-- Reversing a displacement reverses its finite-coordinate linear functional. -/
theorem coordinateLinearFunctional_sub_rev {Coord : Type*} [Fintype Coord]
    (g x y : Coord → ℝ) :
    FiniteDimensionalNorms.coordinateLinearFunctional g (fun i => x i - y i) =
      -FiniteDimensionalNorms.coordinateLinearFunctional g (fun i => y i - x i) := by
  simp only [coordinateLinearFunctional_apply]
  calc
    ∑ i, g i * (x i - y i) = ∑ i, -(g i * (y i - x i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = -∑ i, g i * (y i - x i) := by
      simpa using (Finset.sum_neg_distrib
        (s := Finset.univ) (f := fun i => g i * (y i - x i)))

/-- A restricted subgradient controls the objective gap by its forward pairing. -/
theorem finiteSubgradientOn_objective_gap_le
    {Coord : Type*} [Fintype Coord]
    {cost : (Coord → ℝ) → ℝ} {X : Set (Coord → ℝ)} {x g y : Coord → ℝ}
    (hg : FiniteSubgradientOn cost X x g) (hy : y ∈ X) :
    cost x - cost y ≤
      FiniteDimensionalNorms.coordinateLinearFunctional g (fun i => x i - y i) := by
  have h := hg y hy
  rw [coordinateLinearFunctional_sub_rev] at ⊢
  linarith

/--
Uniformly bounded feasible-set subgradients make the objective Lipschitz on
the feasible set.  The hypothesis includes existence at every feasible point;
without it, a boundedness statement quantified only over existing
subgradients can be vacuous at a boundary point.
-/
theorem abs_sub_objective_le_l2_of_exists_bounded_subgradientOn
    {Coord : Type*} [Fintype Coord]
    {cost : (Coord → ℝ) → ℝ} {X : Set (Coord → ℝ)} {C : ℝ}
    (hC : 0 ≤ C)
    (hsub : ∀ x, x ∈ X → ∃ g,
      FiniteSubgradientOn cost X x g ∧
        FiniteDimensionalNorms.l2 g ≤ C)
    {x y : Coord → ℝ} (hx : x ∈ X) (hy : y ∈ X) :
    |cost x - cost y| ≤
      C * FiniteDimensionalNorms.l2 (fun i => x i - y i) := by
  rcases hsub x hx with ⟨gx, hgx, hgx_bound⟩
  rcases hsub y hy with ⟨gy, hgy, hgy_bound⟩
  have hxy : cost x - cost y ≤
      FiniteDimensionalNorms.dot gx (fun i => x i - y i) := by
    simpa [FiniteDimensionalNorms.dot,
      FiniteDimensionalNorms.coordinateLinearFunctional] using
      finiteSubgradientOn_objective_gap_le hgx hy
  have hxy_bound : cost x - cost y ≤
      C * FiniteDimensionalNorms.l2 (fun i => x i - y i) := by
    calc
      cost x - cost y ≤ FiniteDimensionalNorms.dot gx (fun i => x i - y i) := hxy
      _ ≤ |FiniteDimensionalNorms.dot gx (fun i => x i - y i)| := le_abs_self _
      _ ≤ FiniteDimensionalNorms.l2 gx *
          FiniteDimensionalNorms.l2 (fun i => x i - y i) :=
        FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 _ _
      _ ≤ C * FiniteDimensionalNorms.l2 (fun i => x i - y i) :=
        mul_le_mul_of_nonneg_right hgx_bound
          (FiniteDimensionalNorms.normL2_nonneg _)
  have hyx : cost y - cost x ≤
      FiniteDimensionalNorms.dot gy (fun i => y i - x i) := by
    simpa [FiniteDimensionalNorms.dot,
      FiniteDimensionalNorms.coordinateLinearFunctional] using
      finiteSubgradientOn_objective_gap_le hgy hx
  have hyx_bound : cost y - cost x ≤
      C * FiniteDimensionalNorms.l2 (fun i => x i - y i) := by
    calc
      cost y - cost x ≤ FiniteDimensionalNorms.dot gy (fun i => y i - x i) := hyx
      _ ≤ |FiniteDimensionalNorms.dot gy (fun i => y i - x i)| := le_abs_self _
      _ ≤ FiniteDimensionalNorms.l2 gy *
          FiniteDimensionalNorms.l2 (fun i => y i - x i) :=
        FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 _ _
      _ ≤ C * FiniteDimensionalNorms.l2 (fun i => y i - x i) :=
        mul_le_mul_of_nonneg_right hgy_bound
          (FiniteDimensionalNorms.normL2_nonneg _)
      _ = C * FiniteDimensionalNorms.l2 (fun i => x i - y i) := by
        rw [FiniteDimensionalNorms.normL2_sub_rev]
  apply abs_le.mpr
  constructor
  · linarith
  · exact hxy_bound

/--
A finite-dimensional objective with uniformly bounded feasible-set
subgradients at every feasible point is continuous on that set.
-/
theorem continuousOn_of_exists_bounded_subgradientOn
    {Coord : Type*} [Fintype Coord]
    {cost : (Coord → ℝ) → ℝ} {X : Set (Coord → ℝ)} {C : ℝ}
    (hC : 0 ≤ C)
    (hsub : ∀ x, x ∈ X → ∃ g,
      FiniteSubgradientOn cost X x g ∧
        FiniteDimensionalNorms.l2 g ≤ C) :
    ContinuousOn cost X := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro epsilon hepsilon
  let displacement : (Coord → ℝ) → ℝ :=
    fun y => FiniteDimensionalNorms.l2 (fun i => y i - x i)
  have hdisplacement_continuous : Continuous displacement := by
    exact FiniteDimensionalNorms.continuous_l2.comp
      (continuous_id.sub continuous_const)
  have hdenom_pos : 0 < C + 1 := by linarith
  rcases (Metric.continuousAt_iff.mp
      hdisplacement_continuous.continuousAt)
      (epsilon / (C + 1)) (div_pos hepsilon hdenom_pos) with
    ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨delta, hdelta_pos, ?_⟩
  intro y hy hy_delta
  have hsmall : displacement y < epsilon / (C + 1) := by
    have h := hdelta hy_delta
    rw [Real.dist_eq] at h
    simpa only [displacement, FiniteDimensionalNorms.normL2_sub_self, sub_zero,
      abs_of_nonneg (FiniteDimensionalNorms.normL2_nonneg _)] using h
  have hscaled : C * displacement y < epsilon := by
    have hC_step : C ≤ C + 1 := by linarith
    calc
      C * displacement y ≤ (C + 1) * displacement y := by
        exact mul_le_mul_of_nonneg_right hC_step
          (FiniteDimensionalNorms.normL2_nonneg _)
      _ < (C + 1) * (epsilon / (C + 1)) :=
        mul_lt_mul_of_pos_left hsmall hdenom_pos
      _ = epsilon := by field_simp
  have hgap := abs_sub_objective_le_l2_of_exists_bounded_subgradientOn
    hC hsub hy hx
  simpa [Real.dist_eq, displacement] using hgap.trans_lt hscaled

/-- A map that always lands in the feasible set `X`. -/
def ProjectionOnto {Point : Type*} (X : Set Point) (project : Point → Point) :
  Prop :=
  ∀ y, project y ∈ X

/-- A map selects a Euclidean closest feasible point for every input. -/
def EuclideanProjectionOnto {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (project : (Coord → ℝ) → Coord → ℝ) : Prop :=
  ∀ y,
    project y ∈ X ∧
      IsMinOn
        (fun x => FiniteDimensionalNorms.l2 (fun i => x i - y i))
        X (project y)

/--
The pointwise Euclidean nearest-point projection onto a nonempty compact set.
For a convex feasible set, `euclideanProjectionOnto` below records the usual
projection property used by projected first-order methods.
-/
noncomputable def euclideanProjection
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ))
    (hcompact : IsCompact X) (hnonempty : X.Nonempty) :
    (Coord → ℝ) → Coord → ℝ :=
  fun y : Coord → ℝ => Classical.choose (hcompact.exists_isMinOn
    (f := fun x : Coord → ℝ => FiniteDimensionalNorms.l2 (fun i => x i - y i)) hnonempty
    ((FiniteDimensionalNorms.continuous_l2.comp
      (continuous_id.sub
        (continuous_const : Continuous fun _ : Coord → ℝ => y))).continuousOn))

/-- The chosen Euclidean projection lies in the feasible set and minimizes distance. -/
theorem euclideanProjection_spec
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ))
    (hcompact : IsCompact X) (hnonempty : X.Nonempty) (y : Coord → ℝ) :
    euclideanProjection X hcompact hnonempty y ∈ X ∧
      IsMinOn
        (fun x => FiniteDimensionalNorms.l2 (fun i => x i - y i))
        X (euclideanProjection X hcompact hnonempty y) := by
  exact Classical.choose_spec (hcompact.exists_isMinOn
    (f := fun x : Coord → ℝ => FiniteDimensionalNorms.l2 (fun i => x i - y i)) hnonempty
    ((FiniteDimensionalNorms.continuous_l2.comp
      (continuous_id.sub
        (continuous_const : Continuous fun _ : Coord → ℝ => y))).continuousOn))

/-- A nonempty compact feasible set has its pointwise Euclidean projection. -/
theorem euclideanProjection_onto
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ))
    (hcompact : IsCompact X) (hnonempty : X.Nonempty) :
    EuclideanProjectionOnto X (euclideanProjection X hcompact hnonempty) := by
  intro y
  exact euclideanProjection_spec X hcompact hnonempty y

set_option maxHeartbeats 1000000 in
-- The finite-coordinate/PiLp transport expands several nested norm conversions.
/--
The residual from a Euclidean closest-point projection has nonpositive inner
product with every feasible displacement away from the projection.  This is
the variational characterization of projection onto a convex set.
-/
theorem euclideanProjection_inner_le_zero
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hX : Convex ℝ X) (hproject : EuclideanProjectionOnto X project)
    (z x : Coord → ℝ) (hx : x ∈ X) :
    FiniteDimensionalNorms.dot (fun i => z i - project z i)
      (fun i => x i - project z i) ≤ 0 := by
  let E : Type _ := @PiLp (2 : ENNReal) Coord (fun _ => ℝ)
  let toE : (Coord → ℝ) → E := WithLp.toLp 2
  let K : Set E := toE '' X
  let u : E := toE z
  let v : E := toE (project z)
  have hKconvex : Convex ℝ K := by
    simpa [K, toE, WithLp.coe_symm_linearEquiv] using
      hX.linear_image
        ((WithLp.linearEquiv (2 : ENNReal) ℝ (Coord → ℝ)).symm.toLinearMap)
  have hvK : v ∈ K := ⟨project z, (hproject z).1, rfl⟩
  have hmin : ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖ := by
    rintro w ⟨a, ha, rfl⟩
    have h : FiniteDimensionalNorms.l2 (fun i => project z i - z i) ≤
        FiniteDimensionalNorms.l2 (fun i => a i - z i) :=
      (hproject z).2 ha
    calc
      ‖u - v‖ = FiniteDimensionalNorms.l2 (fun i => z i - project z i) := by
        change ‖WithLp.toLp 2 z - WithLp.toLp 2 (project z)‖ = _
        rw [← WithLp.toLp_sub]
        exact (FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _).symm
      _ = FiniteDimensionalNorms.l2 (fun i => project z i - z i) :=
        FiniteDimensionalNorms.normL2_sub_rev _ _
      _ ≤ FiniteDimensionalNorms.l2 (fun i => a i - z i) := h
      _ = FiniteDimensionalNorms.l2 (fun i => z i - a i) :=
        FiniteDimensionalNorms.normL2_sub_rev _ _
      _ = ‖u - toE a‖ := by
        change FiniteDimensionalNorms.l2 (fun i => z i - a i) =
          ‖WithLp.toLp 2 z - WithLp.toLp 2 a‖
        rw [← WithLp.toLp_sub]
        exact FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _
  letI : Nonempty K := ⟨⟨v, hvK⟩⟩
  have hnorm_eq_iInf : ‖u - v‖ = ⨅ w : K, ‖u - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      exact hmin w w.2
    · change (⨅ w : K, ‖u - w‖) ≤
        (fun w : K => ‖u - w‖) ⟨v, hvK⟩
      apply ciInf_le
      use 0
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
  have hinner : ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hKconvex hvK).mp hnorm_eq_iInf
  have hinner_x := hinner (toE x) ⟨x, hx, rfl⟩
  change inner ℝ
      ((WithLp.toLp 2 z : E) - WithLp.toLp 2 (project z))
      ((WithLp.toLp 2 x : E) - WithLp.toLp 2 (project z)) ≤ 0 at hinner_x
  rw [← FiniteDimensionalNorms.piLp_inner_eq_dot]
  simpa only [WithLp.toLp_sub] using hinner_x

set_option maxHeartbeats 1000000 in
-- Expanding the projection characterization twice requires a larger elaboration budget.
/--
A Euclidean closest-point projection onto a convex finite-dimensional set is
nonexpansive in squared Euclidean distance.
-/
theorem euclideanProjection_l2Sq_nonexpansive
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hX : Convex ℝ X) (hproject : EuclideanProjectionOnto X project)
    (z w : Coord → ℝ) :
    FiniteDimensionalNorms.l2Sq (fun i => project z i - project w i) ≤
      FiniteDimensionalNorms.l2Sq (fun i => z i - w i) := by
  have hz := euclideanProjection_inner_le_zero hX hproject z (project w)
    (hproject w).1
  have hw := euclideanProjection_inner_le_zero hX hproject w (project z)
    (hproject z).1
  have hz_rewritten :
      FiniteDimensionalNorms.dot (fun i => z i - project z i)
        (fun i => project w i - project z i) =
        -FiniteDimensionalNorms.dot (fun i => z i - project z i)
          (fun i => project z i - project w i) := by
    simp only [FiniteDimensionalNorms.dot]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hz_nonneg : 0 ≤ FiniteDimensionalNorms.dot (fun i => z i - project z i)
      (fun i => project z i - project w i) := by
    rw [hz_rewritten] at hz
    linarith
  have hdot_expand :
      FiniteDimensionalNorms.dot (fun i => z i - w i)
          (fun i => project z i - project w i) =
        FiniteDimensionalNorms.dot (fun i => z i - project z i)
          (fun i => project z i - project w i) +
          FiniteDimensionalNorms.l2Sq (fun i => project z i - project w i) -
          FiniteDimensionalNorms.dot (fun i => w i - project w i)
            (fun i => project z i - project w i) := by
    simp only [FiniteDimensionalNorms.dot, FiniteDimensionalNorms.l2Sq]
    calc
      ∑ i, (z i - w i) * (project z i - project w i) =
          ∑ i, ((z i - project z i) * (project z i - project w i) +
            (project z i - project w i) ^ 2 -
              (w i - project w i) * (project z i - project w i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hdot_lower :
      FiniteDimensionalNorms.l2Sq (fun i => project z i - project w i) ≤
        FiniteDimensionalNorms.dot (fun i => z i - w i)
          (fun i => project z i - project w i) := by
    rw [hdot_expand]
    linarith
  have hdot_upper :
      FiniteDimensionalNorms.dot (fun i => z i - w i)
        (fun i => project z i - project w i) ≤
        FiniteDimensionalNorms.l2 (fun i => z i - w i) *
          FiniteDimensionalNorms.l2 (fun i => project z i - project w i) :=
    (le_abs_self _).trans
      (FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 _ _)
  have hscaled :
      FiniteDimensionalNorms.l2Sq (fun i => project z i - project w i) ≤
        FiniteDimensionalNorms.l2 (fun i => z i - w i) *
          FiniteDimensionalNorms.l2 (fun i => project z i - project w i) :=
    hdot_lower.trans hdot_upper
  have hproject_nonneg := FiniteDimensionalNorms.normL2_nonneg
    (fun i => project z i - project w i)
  have hinput_nonneg := FiniteDimensionalNorms.normL2_nonneg (fun i => z i - w i)
  have hproject_sq := FiniteDimensionalNorms.normL2_sq_eq_normL2Sq
    (fun i => project z i - project w i)
  have hinput_sq := FiniteDimensionalNorms.normL2_sq_eq_normL2Sq (fun i => z i - w i)
  have hnorm : FiniteDimensionalNorms.l2 (fun i => project z i - project w i) ≤
      FiniteDimensionalNorms.l2 (fun i => z i - w i) := by
    nlinarith
  nlinarith

/-- A Euclidean closest-point projection onto a convex finite-dimensional set is 1-Lipschitz. -/
theorem euclideanProjection_l2_nonexpansive
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hX : Convex ℝ X) (hproject : EuclideanProjectionOnto X project)
    (z w : Coord → ℝ) :
    FiniteDimensionalNorms.l2 (fun i => project z i - project w i) ≤
      FiniteDimensionalNorms.l2 (fun i => z i - w i) := by
  unfold FiniteDimensionalNorms.l2
  exact Real.sqrt_le_sqrt (euclideanProjection_l2Sq_nonexpansive hX hproject z w)

/--
After identifying a finite coordinate product with its `L2` normed-space
copy, a Euclidean closest-point projection is 1-Lipschitz.
-/
theorem euclideanProjection_lipschitz
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hX : Convex ℝ X) (hproject : EuclideanProjectionOnto X project) :
    LipschitzWith 1 (fun u : @PiLp (2 : ENNReal) Coord (fun _ => ℝ) =>
      WithLp.toLp 2 (project (WithLp.ofLp u))) := by
  apply LipschitzWith.of_edist_le
  intro u v
  rw [edist_dist, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  calc
    dist (WithLp.toLp 2 (project (WithLp.ofLp u)))
        (WithLp.toLp 2 (project (WithLp.ofLp v))) =
        FiniteDimensionalNorms.l2
          (fun i => project (WithLp.ofLp u) i - project (WithLp.ofLp v) i) := by
      rw [dist_eq_norm_sub, ← WithLp.toLp_sub]
      exact (FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _).symm
    _ ≤ FiniteDimensionalNorms.l2
          (fun i => WithLp.ofLp u i - WithLp.ofLp v i) :=
      euclideanProjection_l2_nonexpansive hX hproject _ _
    _ = dist u v := by
      rw [dist_eq_norm_sub]
      calc
        FiniteDimensionalNorms.l2
            (fun i => WithLp.ofLp u i - WithLp.ofLp v i) =
            ‖WithLp.toLp 2 (fun i => WithLp.ofLp u i - WithLp.ofLp v i)‖ :=
          FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _
        _ = ‖WithLp.toLp 2 (WithLp.ofLp u) - WithLp.toLp 2 (WithLp.ofLp v)‖ := by
          rw [← WithLp.toLp_sub]
          congr 1
        _ = ‖u - v‖ := by simp

/-- A Euclidean closest-point projection onto a convex finite-dimensional set is continuous. -/
theorem euclideanProjection_continuous
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hX : Convex ℝ X) (hproject : EuclideanProjectionOnto X project) :
    Continuous project := by
  let P : @PiLp (2 : ENNReal) Coord (fun _ => ℝ) →
      @PiLp (2 : ENNReal) Coord (fun _ => ℝ) := fun u =>
        WithLp.toLp 2 (project (WithLp.ofLp u))
  have hP : Continuous P := (euclideanProjection_lipschitz hX hproject).continuous
  have hrewrite : project = fun x => WithLp.ofLp (P (WithLp.toLp 2 x)) := by
    funext x
    simp only [P]
  rw [hrewrite]
  exact (PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Coord => ℝ)).comp
    (hP.comp (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Coord => ℝ)))

/--
A projection is nonexpansive with respect to every feasible comparison point.
For a closest-point projection onto a closed convex set in Euclidean space,
this is the standard projection theorem; keeping the property separate makes
the deterministic descent API applicable to other nonexpansive retractions.
-/
def SquaredDistanceNonexpansiveOn {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (project : (Coord → ℝ) → Coord → ℝ) : Prop :=
  ∀ z x, x ∈ X →
    FiniteDimensionalNorms.l2Sq (fun i => project z i - x i) ≤
      FiniteDimensionalNorms.l2Sq (fun i => z i - x i)

set_option maxHeartbeats 1000000 in
-- The finite-coordinate `PiLp` conversion below expands several nested Hilbert-space identities.
/--
A closest-point projection onto a convex subset of a finite Euclidean space is
nonexpansive with respect to every feasible comparison point.  This is the
finite-coordinate form of the Hilbert projection theorem.
-/
theorem euclideanProjection_squaredDistanceNonexpansive
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hX : Convex ℝ X) (hproject : EuclideanProjectionOnto X project) :
    SquaredDistanceNonexpansiveOn X project := by
  intro z x hx
  let E : Type _ := @PiLp (2 : ENNReal) Coord (fun _ => ℝ)
  let toE : (Coord → ℝ) → E := WithLp.toLp 2
  let K : Set E := toE '' X
  let u : E := toE z
  let v : E := toE (project z)
  have hKconvex : Convex ℝ K := by
    simpa [K, toE, WithLp.coe_symm_linearEquiv] using
      hX.linear_image
        ((WithLp.linearEquiv (2 : ENNReal) ℝ (Coord → ℝ)).symm.toLinearMap)
  have hvK : v ∈ K := ⟨project z, (hproject z).1, rfl⟩
  have hmin : ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖ := by
    rintro w ⟨a, ha, rfl⟩
    have h : FiniteDimensionalNorms.l2 (fun i => project z i - z i) ≤
        FiniteDimensionalNorms.l2 (fun i => a i - z i) :=
      (hproject z).2 ha
    calc
      ‖u - v‖ = FiniteDimensionalNorms.l2 (fun i => z i - project z i) := by
        change ‖WithLp.toLp 2 z - WithLp.toLp 2 (project z)‖ = _
        rw [← WithLp.toLp_sub]
        exact (FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _).symm
      _ = FiniteDimensionalNorms.l2 (fun i => project z i - z i) :=
        FiniteDimensionalNorms.normL2_sub_rev _ _
      _ ≤ FiniteDimensionalNorms.l2 (fun i => a i - z i) := h
      _ = FiniteDimensionalNorms.l2 (fun i => z i - a i) :=
        FiniteDimensionalNorms.normL2_sub_rev _ _
      _ = ‖u - toE a‖ := by
        change FiniteDimensionalNorms.l2 (fun i => z i - a i) =
          ‖WithLp.toLp 2 z - WithLp.toLp 2 a‖
        rw [← WithLp.toLp_sub]
        exact FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _
  letI : Nonempty K := ⟨⟨v, hvK⟩⟩
  have hnorm_eq_iInf : ‖u - v‖ = ⨅ w : K, ‖u - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      exact hmin w w.2
    · change (⨅ w : K, ‖u - w‖) ≤
        (fun w : K => ‖u - w‖) ⟨v, hvK⟩
      apply ciInf_le
      use 0
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
  have hinner : ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hKconvex hvK).mp hnorm_eq_iInf
  have hinner_x := hinner (toE x) ⟨x, hx, rfl⟩
  have hinner_coord :
      FiniteDimensionalNorms.dot (fun i => z i - project z i)
        (fun i => x i - project z i) ≤ 0 := by
    change inner ℝ
        ((WithLp.toLp 2 z : E) - WithLp.toLp 2 (project z))
        ((WithLp.toLp 2 x : E) - WithLp.toLp 2 (project z)) ≤ 0 at hinner_x
    rw [← FiniteDimensionalNorms.piLp_inner_eq_dot]
    simpa only [WithLp.toLp_sub] using hinner_x
  have hsq :
      FiniteDimensionalNorms.l2Sq (fun i => project z i - x i) ≤
        FiniteDimensionalNorms.l2Sq (fun i => z i - x i) := by
    simp only [FiniteDimensionalNorms.l2Sq, FiniteDimensionalNorms.dot] at hinner_coord ⊢
    have hsum_nonneg : 0 ≤ ∑ i, (z i - project z i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hexpand :
        ∑ i, (z i - x i) ^ 2 =
          (∑ i, (project z i - x i) ^ 2) +
            (∑ i, (z i - project z i) ^ 2) -
              2 * (∑ i, (z i - project z i) * (x i - project z i)) := by
      calc
        ∑ i, (z i - x i) ^ 2 =
            ∑ i, ((project z i - x i) ^ 2 +
              (z i - project z i) ^ 2 -
                2 * ((z i - project z i) * (x i - project z i))) := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexpand]
    nlinarith
  exact hsq

/-- The defining squared-distance estimate for a nonexpansive retraction. -/
theorem l2Sq_project_sub_le
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn X project)
    {z x : Coord → ℝ} (hx : x ∈ X) :
    FiniteDimensionalNorms.l2Sq (fun i => project z i - x i) ≤
      FiniteDimensionalNorms.l2Sq (fun i => z i - x i) := by
  exact hproject z x hx

/-- Exact one-step expansion of squared Euclidean distance. -/
theorem l2Sq_sub_smul_sub_eq
    {Coord : Type*} [Fintype Coord]
    (previous direction target : Coord → ℝ) (radius : ℝ) :
    FiniteDimensionalNorms.l2Sq
        (fun i => previous i - radius * direction i - target i) =
      FiniteDimensionalNorms.l2Sq (fun i => previous i - target i) -
        2 * radius *
          FiniteDimensionalNorms.dot direction (fun i => previous i - target i) +
        radius ^ 2 * FiniteDimensionalNorms.l2Sq direction := by
  simp only [FiniteDimensionalNorms.l2Sq, FiniteDimensionalNorms.dot]
  calc
    ∑ i, (previous i - radius * direction i - target i) ^ 2 =
        ∑ i, ((previous i - target i) ^ 2 -
          (2 * radius) * (direction i * (previous i - target i)) +
          radius ^ 2 * direction i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = (∑ i, (previous i - target i) ^ 2) -
          2 * radius * (∑ i, direction i * (previous i - target i)) +
          radius ^ 2 * (∑ i, direction i ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]

/--
Projection followed by an arbitrary finite-coordinate direction satisfies the
standard deterministic squared-distance descent inequality.
-/
theorem l2Sq_projected_step_sub_le
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn X project)
    (previous direction target : Coord → ℝ) (radius : ℝ) (htarget : target ∈ X) :
    FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous j - radius * direction j) i - target i) ≤
      FiniteDimensionalNorms.l2Sq (fun i => previous i - target i) -
        2 * radius *
          FiniteDimensionalNorms.dot direction (fun i => previous i - target i) +
        radius ^ 2 * FiniteDimensionalNorms.l2Sq direction := by
  calc
    FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous j - radius * direction j) i - target i) ≤
        FiniteDimensionalNorms.l2Sq
          (fun i => (previous i - radius * direction i) - target i) :=
      l2Sq_project_sub_le hproject htarget
    _ = _ := l2Sq_sub_smul_sub_eq previous direction target radius

/-- The explicit coordinate pairing agrees with the finite Euclidean dot product. -/
theorem dot_eq_coordinateLinearFunctional {Coord : Type*} [Fintype Coord]
    (g h : Coord → ℝ) :
    FiniteDimensionalNorms.dot g h =
      FiniteDimensionalNorms.coordinateLinearFunctional g h := by
  simp [FiniteDimensionalNorms.dot,
    FiniteDimensionalNorms.coordinateLinearFunctional]

/-- The finite Euclidean dot product is additive in its first argument. -/
theorem dot_add_left {Coord : Type*} [Fintype Coord]
    (g h d : Coord → ℝ) :
    FiniteDimensionalNorms.dot (fun i => g i + h i) d =
      FiniteDimensionalNorms.dot g d + FiniteDimensionalNorms.dot h d := by
  simp only [FiniteDimensionalNorms.dot]
  calc
    ∑ i, (g i + h i) * d i = ∑ i, (g i * d i + h i * d i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = _ := by rw [Finset.sum_add_distrib]

/--
One projected stochastic-subgradient step is bounded by objective descent plus
the explicitly isolated noise-and-bias pairing.  This is the deterministic
inequality used before conditional expectation and martingale arguments.
-/
theorem l2Sq_projected_subgradient_noise_bias_step_le
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    {cost : (Coord → ℝ) → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn X project)
    {previous gradient noise bias target : Coord → ℝ} {radius : ℝ}
    (hsubgradient : FiniteSubgradientOn cost X previous gradient)
    (htarget : target ∈ X) (hradius : 0 ≤ radius) :
    FiniteDimensionalNorms.l2Sq
        (fun i =>
          project (fun j => previous j - radius *
            (gradient j + noise j + bias j)) i - target i) ≤
      FiniteDimensionalNorms.l2Sq (fun i => previous i - target i) -
        2 * radius * (cost previous - cost target) -
        2 * radius *
          FiniteDimensionalNorms.dot (fun i => noise i + bias i)
            (fun i => previous i - target i) +
        radius ^ 2 *
          FiniteDimensionalNorms.l2Sq
            (fun i => gradient i + noise i + bias i) := by
  let direction : Coord → ℝ := fun i => gradient i + noise i + bias i
  have hstep := l2Sq_projected_step_sub_le hproject previous direction target radius htarget
  have hgap := finiteSubgradientOn_objective_gap_le hsubgradient htarget
  have hdot_gradient :
      FiniteDimensionalNorms.dot gradient (fun i => previous i - target i) =
        FiniteDimensionalNorms.coordinateLinearFunctional gradient
          (fun i => previous i - target i) :=
    dot_eq_coordinateLinearFunctional gradient _
  have hdot_direction :
      FiniteDimensionalNorms.dot direction (fun i => previous i - target i) =
        FiniteDimensionalNorms.dot gradient (fun i => previous i - target i) +
          FiniteDimensionalNorms.dot (fun i => noise i + bias i)
            (fun i => previous i - target i) := by
    simpa [direction, add_assoc] using
      dot_add_left gradient (fun i => noise i + bias i)
        (fun i => previous i - target i)
  rw [hdot_direction, hdot_gradient] at hstep
  have hscaled := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * radius by nlinarith)
  change _ ≤ _
  dsimp [direction] at hstep
  nlinarith

/--
The one-step projected stochastic-subgradient estimate with the bias pairing
and squared direction norm bounded by Euclidean norms.  It isolates the sole
martingale term `dot noise (previous - target)` for conditional-expectation
arguments, while keeping the bias contribution in a deterministic summable
form.
-/
theorem l2Sq_projected_subgradient_noise_bias_step_le_bounded
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    {cost : (Coord → ℝ) → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn X project)
    {previous gradient noise bias target : Coord → ℝ}
    {radius C distanceBound : ℝ}
    (hsubgradient : FiniteSubgradientOn cost X previous gradient)
    (htarget : target ∈ X) (hradius : 0 ≤ radius)
    (hgradient_bound : FiniteDimensionalNorms.l2 gradient ≤ C)
    (hdistance_bound :
      FiniteDimensionalNorms.l2 (fun i => previous i - target i) ≤ distanceBound) :
    FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous j - radius *
          (gradient j + noise j + bias j)) i - target i) ≤
      FiniteDimensionalNorms.l2Sq (fun i => previous i - target i) -
        2 * radius * (cost previous - cost target) -
        2 * radius *
          FiniteDimensionalNorms.dot noise (fun i => previous i - target i) +
        2 * radius * distanceBound * FiniteDimensionalNorms.l2 bias +
        3 * radius ^ 2 *
          (C ^ 2 + FiniteDimensionalNorms.l2Sq noise +
            FiniteDimensionalNorms.l2Sq bias) := by
  have hstep := l2Sq_projected_subgradient_noise_bias_step_le
    (noise := noise) (bias := bias) hproject hsubgradient htarget hradius
  have hdot_split :
      FiniteDimensionalNorms.dot (fun i => noise i + bias i)
          (fun i => previous i - target i) =
        FiniteDimensionalNorms.dot noise (fun i => previous i - target i) +
          FiniteDimensionalNorms.dot bias (fun i => previous i - target i) := by
    simpa using dot_add_left noise bias (fun i => previous i - target i)
  have hbias_dot :
      FiniteDimensionalNorms.dot bias (fun i => previous i - target i) ≤
        FiniteDimensionalNorms.l2 bias *
          FiniteDimensionalNorms.l2 (fun i => previous i - target i) := by
    exact le_trans (le_abs_self _)
      (FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 _ _)
  have hbias_scaled :
      -2 * radius *
          FiniteDimensionalNorms.dot bias (fun i => previous i - target i) ≤
        2 * radius * distanceBound * FiniteDimensionalNorms.l2 bias := by
    have hdot_lower :
        -(FiniteDimensionalNorms.l2 bias *
          FiniteDimensionalNorms.l2 (fun i => previous i - target i)) ≤
          FiniteDimensionalNorms.dot bias (fun i => previous i - target i) := by
      have habs := FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 bias
        (fun i => previous i - target i)
      exact (abs_le.mp habs).1
    have hscaled := mul_le_mul_of_nonneg_left hdot_lower
      (show 0 ≤ 2 * radius by linarith)
    have hdist_scaled := mul_le_mul_of_nonneg_left hdistance_bound
      (FiniteDimensionalNorms.normL2_nonneg bias)
    nlinarith
  have hdirection_sq :
      FiniteDimensionalNorms.l2Sq (fun i => gradient i + noise i + bias i) ≤
        3 * (FiniteDimensionalNorms.l2Sq gradient +
          FiniteDimensionalNorms.l2Sq noise +
          FiniteDimensionalNorms.l2Sq bias) :=
    FiniteDimensionalNorms.normL2Sq_add_three_le gradient noise bias
  have hgradient_sq : FiniteDimensionalNorms.l2Sq gradient ≤ C ^ 2 := by
    rw [← FiniteDimensionalNorms.normL2_sq_eq_normL2Sq]
    have hC_nonneg : 0 ≤ C :=
      (FiniteDimensionalNorms.normL2_nonneg gradient).trans hgradient_bound
    exact (sq_le_sq₀ (FiniteDimensionalNorms.normL2_nonneg gradient) hC_nonneg).mpr
      hgradient_bound
  have hdirection_scaled :
      radius ^ 2 * FiniteDimensionalNorms.l2Sq
          (fun i => gradient i + noise i + bias i) ≤
        3 * radius ^ 2 *
          (C ^ 2 + FiniteDimensionalNorms.l2Sq noise +
            FiniteDimensionalNorms.l2Sq bias) := by
    calc
      radius ^ 2 * FiniteDimensionalNorms.l2Sq
          (fun i => gradient i + noise i + bias i) ≤
        radius ^ 2 *
          (3 * (FiniteDimensionalNorms.l2Sq gradient +
            FiniteDimensionalNorms.l2Sq noise +
            FiniteDimensionalNorms.l2Sq bias)) :=
          mul_le_mul_of_nonneg_left hdirection_sq (sq_nonneg _)
      _ ≤ radius ^ 2 *
          (3 * (C ^ 2 + FiniteDimensionalNorms.l2Sq noise +
            FiniteDimensionalNorms.l2Sq bias)) := by
          gcongr
      _ = 3 * radius ^ 2 *
          (C ^ 2 + FiniteDimensionalNorms.l2Sq noise +
            FiniteDimensionalNorms.l2Sq bias) := by ring
  rw [hdot_split] at hstep
  nlinarith

/--
One projected stochastic subgradient step: move from `previous` along the
negative of `subgradient + noise + bias` scaled by `radius`, then project.
-/
def FiniteProjectedSSGMUpdateAt {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (previous : Coord → ℝ) (radius : ℝ)
    (subgradient noise bias next : Coord → ℝ) : Prop :=
  next =
    project
      (fun i => previous i -
        radius * (subgradient i + noise i + bias i))

/-- The trajectory follows the projected update rule at every step. -/
def FollowsFiniteProjectedSSGM {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  ∀ t : ℕ,
    FiniteProjectedSSGMUpdateAt project (trajectory t) (radius (t + 1))
      (subgradient t) (noise t) (bias t) (trajectory (t + 1))

/--
The trajectory follows the projected update rule and each step direction is a
genuine subgradient of that step's sampled cost.
-/
def FollowsFiniteProjectedSampleSubgradientMethod {Coord : Type*} [Fintype Coord]
    (sampleCost : ℕ → (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
    ∀ t : ℕ, FiniteSubgradientAt (sampleCost t) (trajectory t) (subgradient t)

/--
Robbins-Monro step-size hypotheses: positive steps, square-summable, with
divergent partial sums.  The shifted indices reflect that Lean's naturals start
at zero while the schedule starts at one.
-/
def SSGMStepSizeConditions (radius : ℕ → ℝ) : Prop :=
  (∀ t : ℕ, 0 < t → 0 < radius t) ∧
    Summable (fun t : ℕ => (radius (t + 1)) ^ 2) ∧
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1))
        Filter.atTop Filter.atTop

end Optimization
end AppliedModelingLib

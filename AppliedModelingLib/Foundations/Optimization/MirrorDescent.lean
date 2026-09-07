import AppliedModelingLib.Foundations.Optimization.Certificate
import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNormsDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Abstract Bregman mirror-descent estimate

This module isolates the algebraic estimate behind a Bregman mirror update.
It is deliberately phrased with explicit three-point, strong-convexity, and
dual-norm certificates, so that finite entropy/KL applications can discharge
each analytic ingredient independently.  In particular, no existence or
first-order optimality result for an abstract argmax is assumed silently.

## Main declaration

- `bregmanMirrorStep_bound_of_certificates`
-/

namespace AppliedModelingLib
namespace Optimization

/-- Finite-coordinate pairing of two real vectors. -/
def finiteVectorPairing {Coordinate : Type*} [Fintype Coordinate]
    (first second : Coordinate → ℝ) : ℝ :=
  ∑ coordinate, first coordinate * second coordinate

/-- The finite Bregman divergence associated with an explicit gradient field. -/
def finiteBregmanDivergence {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (first second : Coordinate → ℝ) : ℝ :=
  potential first - potential second -
    finiteVectorPairing (gradient second) (first - second)

theorem finiteVectorPairing_comm {Coordinate : Type*} [Fintype Coordinate]
    (first second : Coordinate → ℝ) :
    finiteVectorPairing first second = finiteVectorPairing second first := by
  unfold finiteVectorPairing
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

theorem finiteVectorPairing_sub_left {Coordinate : Type*} [Fintype Coordinate]
    (first second third : Coordinate → ℝ) :
    finiteVectorPairing (first - second) third =
      finiteVectorPairing first third - finiteVectorPairing second third := by
  unfold finiteVectorPairing
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem finiteVectorPairing_sub_right {Coordinate : Type*} [Fintype Coordinate]
    (first second third : Coordinate → ℝ) :
    finiteVectorPairing first (second - third) =
      finiteVectorPairing first second - finiteVectorPairing first third := by
  unfold finiteVectorPairing
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem coordinateLinearFunctional_apply_pairing {Coordinate : Type*} [Fintype Coordinate]
    (vector argument : Coordinate → ℝ) :
    FiniteDimensionalNorms.coordinateLinearFunctional vector argument =
      finiteVectorPairing vector argument := by
  unfold FiniteDimensionalNorms.coordinateLinearFunctional finiteVectorPairing
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/--
Exact finite Bregman three-point identity.  This is algebraic: it needs only
the displayed potential and gradient field, not a differentiability theorem.
-/
theorem finiteBregmanDivergence_three_point {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (target update previous : Coordinate → ℝ) :
    finiteBregmanDivergence potential gradient target update =
    finiteBregmanDivergence potential gradient target previous -
        finiteBregmanDivergence potential gradient update previous +
          finiteVectorPairing (gradient update - gradient previous) (update - target) := by
  unfold finiteBregmanDivergence finiteVectorPairing
  simp only [Pi.sub_apply]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The finite-coordinate objective maximized by a Bregman mirror update. -/
def finiteBregmanMirrorObjective {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (previous direction policy : Coordinate → ℝ) : ℝ :=
  finiteVectorPairing policy direction -
    finiteBregmanDivergence potential gradient policy previous

/--
The derivative of the finite Bregman mirror objective.  The potential's
derivative is kept as an explicit continuous linear map, avoiding a hidden
identification between a coordinate gradient and a Fréchet derivative.
-/
theorem finiteBregmanMirrorObjective_hasFDerivAt
    {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (update previous direction : Coordinate → ℝ)
    (potentialDerivative : (Coordinate → ℝ) →L[ℝ] ℝ)
    (hpotential : HasFDerivAt potential potentialDerivative update) :
    HasFDerivAt
      (finiteBregmanMirrorObjective potential gradient previous direction)
      (FiniteDimensionalNorms.coordinateLinearFunctional direction -
        (potentialDerivative -
          FiniteDimensionalNorms.coordinateLinearFunctional (gradient previous))) update := by
  have hshift : HasFDerivAt
      (fun policy => finiteVectorPairing (gradient previous) (policy - previous))
      (FiniteDimensionalNorms.coordinateLinearFunctional (gradient previous)) update := by
    simpa only [coordinateLinearFunctional_apply_pairing, finiteVectorPairing_sub_right] using
      (FiniteDimensionalNorms.coordinateLinearFunctional (gradient previous)).hasFDerivAt
        |>.sub_const (finiteVectorPairing (gradient previous) previous)
  have hdiv : HasFDerivAt
      (finiteBregmanDivergence potential gradient · previous)
      (potentialDerivative -
        FiniteDimensionalNorms.coordinateLinearFunctional (gradient previous)) update := by
    simpa only [finiteBregmanDivergence, sub_zero] using
      ((hpotential.sub (hasFDerivAt_const (potential previous) update)).sub hshift)
  have hlinear : HasFDerivAt
      (fun policy => finiteVectorPairing policy direction)
      (FiniteDimensionalNorms.coordinateLinearFunctional direction) update := by
    convert (FiniteDimensionalNorms.coordinateLinearFunctional direction).hasFDerivAt using 1
    ext policy
    rw [← finiteVectorPairing_comm direction policy]
    exact (coordinateLinearFunctional_apply_pairing direction policy).symm
  simpa only [finiteBregmanMirrorObjective] using
    (hlinear.sub hdiv)

/--
An actual maximizer of the finite Bregman objective supplies the variational
first-order inequality whenever its objective has the displayed derivative
within a feasible set and the target direction is feasible to first order.

This is the raw `arg max`-to-first-order portion of the Appendix-D route.  It
leaves only the ordinary differentiability calculation for a chosen potential
and the convex-simplex tangent witness to a concrete application.
-/
theorem finiteBregmanMirror_firstOrder_of_maximizer
    {Coordinate : Type*} [Fintype Coordinate]
    (feasible : Set (Coordinate → ℝ))
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (target update previous direction : Coordinate → ℝ)
    (derivative : (Coordinate → ℝ) →L[ℝ] ℝ)
    (hmax : IsMaximizerOn (fun policy => policy ∈ feasible)
      (finiteBregmanMirrorObjective potential gradient previous direction) update)
    (hderiv : HasFDerivWithinAt
      (finiteBregmanMirrorObjective potential gradient previous direction)
      derivative feasible update)
    (hderivative : derivative (target - update) =
      finiteVectorPairing (direction - (gradient update - gradient previous)) (target - update))
    (hsegment : segment ℝ update (update + (target - update)) ⊆ feasible) :
    0 ≤ finiteVectorPairing
      (gradient update - gradient previous - direction) (target - update) := by
  have hmaxOn : IsMaxOn
      (finiteBregmanMirrorObjective potential gradient previous direction) feasible update := by
    intro policy hpolicy
    exact hmax.2 policy hpolicy
  have htangent : target - update ∈ posTangentConeAt feasible update := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnonpos := hmaxOn.localize.hasFDerivWithinAt_nonpos hderiv htangent
  rw [hderivative] at hnonpos
  have hnegate :
      finiteVectorPairing (direction - (gradient update - gradient previous)) (target - update) =
        -finiteVectorPairing
          (gradient update - gradient previous - direction) (target - update) := by
    unfold finiteVectorPairing
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _
    simp only [Pi.sub_apply]
    ring
  rw [hnegate] at hnonpos
  linarith

/--
Derivative-explicit version of `finiteBregmanMirror_firstOrder_of_maximizer`.
It computes the mirror objective derivative from the potential derivative and
only asks that this derivative agree with the displayed coordinate gradient in
the target direction.
-/
theorem finiteBregmanMirror_firstOrder_of_differentiableMaximizer
    {Coordinate : Type*} [Fintype Coordinate]
    (feasible : Set (Coordinate → ℝ))
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (target update previous direction : Coordinate → ℝ)
    (potentialDerivative : (Coordinate → ℝ) →L[ℝ] ℝ)
    (hmax : IsMaximizerOn (fun policy => policy ∈ feasible)
      (finiteBregmanMirrorObjective potential gradient previous direction) update)
    (hpotential : HasFDerivAt potential potentialDerivative update)
    (hgradient : potentialDerivative (target - update) =
      finiteVectorPairing (gradient update) (target - update))
    (hsegment : segment ℝ update (update + (target - update)) ⊆ feasible) :
    0 ≤ finiteVectorPairing
      (gradient update - gradient previous - direction) (target - update) := by
  apply finiteBregmanMirror_firstOrder_of_maximizer feasible potential gradient
    target update previous direction
    (FiniteDimensionalNorms.coordinateLinearFunctional direction -
      (potentialDerivative -
        FiniteDimensionalNorms.coordinateLinearFunctional (gradient previous)))
    hmax
    (finiteBregmanMirrorObjective_hasFDerivAt potential gradient update previous direction
      potentialDerivative hpotential).hasFDerivWithinAt
  · simp only [ContinuousLinearMap.sub_apply, coordinateLinearFunctional_apply_pairing]
    rw [hgradient, finiteVectorPairing_sub_left, finiteVectorPairing_sub_left]
  · exact hsegment

/--
Simplex-specialized version of the mirror `arg max`-to-first-order bridge.
The feasible-direction condition is discharged by the convexity of the finite
probability simplex.
-/
theorem finiteBregmanMirror_firstOrder_of_differentiableSimplexMaximizer
    {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (target update previous direction : Coordinate → ℝ)
    (potentialDerivative : (Coordinate → ℝ) →L[ℝ] ℝ)
    (hmax : IsMaximizerOn FiniteProbabilitySimplex
      (finiteBregmanMirrorObjective potential gradient previous direction) update)
    (hupdate : FiniteProbabilitySimplex update)
    (htarget : FiniteProbabilitySimplex target)
    (hpotential : HasFDerivAt potential potentialDerivative update)
    (hgradient : potentialDerivative (target - update) =
      finiteVectorPairing (gradient update) (target - update)) :
    0 ≤ finiteVectorPairing
      (gradient update - gradient previous - direction) (target - update) := by
  exact finiteBregmanMirror_firstOrder_of_differentiableMaximizer
    {mass | FiniteProbabilitySimplex mass} potential gradient target update previous direction
    potentialDerivative hmax hpotential hgradient
    (finiteProbabilitySimplex_segment_update_add_sub update target hupdate htarget)

/--
The variational first-order inequality for a finite Bregman mirror update
turns the exact three-point identity into the three-point certificate consumed
by `bregmanMirrorStep_bound_of_certificates`.

The feasible-set/argmax-to-first-order derivation is intentionally separate:
on a simplex it is a boundary-sensitive calculus fact, whereas this theorem
checks the resulting algebra with no hidden regularity assumption.
-/
theorem finiteBregmanMirror_threePoint_of_firstOrder
    {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (target update previous direction : Coordinate → ℝ)
    (hfirstOrder : 0 ≤ finiteVectorPairing
      (gradient update - gradient previous - direction) (target - update)) :
    finiteBregmanDivergence potential gradient target update ≤
      finiteBregmanDivergence potential gradient target previous -
        finiteBregmanDivergence potential gradient update previous +
          finiteVectorPairing (update - target) direction := by
  have hthree := finiteBregmanDivergence_three_point potential gradient target update previous
  have hfirstOrder_rewrite :
      finiteVectorPairing (gradient update - gradient previous - direction) (target - update) =
        finiteVectorPairing (update - target) direction -
          finiteVectorPairing (gradient update - gradient previous) (update - target) := by
    unfold finiteVectorPairing
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _
    simp only [Pi.sub_apply]
    ring
  have hbound :
      finiteVectorPairing (gradient update - gradient previous) (update - target) ≤
        finiteVectorPairing (update - target) direction := by
    rw [hfirstOrder_rewrite] at hfirstOrder
    exact sub_nonneg.mp hfirstOrder
  rw [hthree]
  linarith

/--
The standard one-step Bregman mirror-descent bound, factored into its three
mathematical inputs:

* the Bregman three-point/first-order inequality for the mirror update;
* strong convexity, giving a quadratic lower bound on its divergence; and
* the dual-norm (Hölder) bound on the update direction.

For `ℓ_p` and its Hölder-dual `ℓ_q`, these are exactly the analytic facts used
in NLHF Appendix D, Lemma 2.  The conclusion uses the source's (deliberately
loose) constant `2 / σ`; the same hypotheses in fact yield the sharper
`1 / (2σ)` quadratic term.
-/
theorem bregmanMirrorStep_bound_of_certificates
    {State Action : Type*} [AddCommGroup Action]
    (divergence : State → State → ℝ)
    (displacement : State → State → Action)
    (pairing : Action → Action → ℝ)
    (primalNorm dualNorm : Action → ℝ)
    (target update previous : State) (direction : Action) (modulus : ℝ)
    (hmodulus : 0 < modulus)
    (hdisplacement : displacement update target =
      displacement update previous + displacement previous target)
    (hpairing_add : pairing (displacement update previous + displacement previous target)
      direction = pairing (displacement update previous) direction +
        pairing (displacement previous target) direction)
    (hthreePoint : divergence target update ≤ divergence target previous -
      divergence update previous + pairing (displacement update target) direction)
    (hstrongConvex : modulus / 2 * primalNorm (displacement update previous) ^ 2 ≤
      divergence update previous)
    (hholder : pairing (displacement update previous) direction ≤
      primalNorm (displacement update previous) * dualNorm direction) :
    divergence target update ≤ divergence target previous +
      pairing (displacement previous target) direction +
        (2 / modulus) * dualNorm direction ^ 2 := by
  have hlocal :
      pairing (displacement update previous) direction - divergence update previous ≤
        primalNorm (displacement update previous) * dualNorm direction -
          modulus / 2 * primalNorm (displacement update previous) ^ 2 := by
    linarith
  have hquadratic :
      primalNorm (displacement update previous) * dualNorm direction -
          modulus / 2 * primalNorm (displacement update previous) ^ 2 ≤
        (2 / modulus) * dualNorm direction ^ 2 := by
    rw [show (2 / modulus) * dualNorm direction ^ 2 =
      (2 * dualNorm direction ^ 2) / modulus by ring]
    apply (le_div_iff₀ hmodulus).mpr
    nlinarith [sq_nonneg
      (modulus * primalNorm (displacement update previous) - dualNorm direction),
      sq_nonneg (dualNorm direction)]
  calc
    divergence target update ≤ divergence target previous - divergence update previous +
        pairing (displacement update target) direction := hthreePoint
    _ = divergence target previous + pairing (displacement previous target) direction +
        (pairing (displacement update previous) direction - divergence update previous) := by
      rw [hdisplacement, hpairing_add]
      ring
    _ ≤ divergence target previous + pairing (displacement previous target) direction +
        (primalNorm (displacement update previous) * dualNorm direction -
          modulus / 2 * primalNorm (displacement update previous) ^ 2) := by
      linarith
    _ ≤ divergence target previous + pairing (displacement previous target) direction +
        (2 / modulus) * dualNorm direction ^ 2 := by
      linarith

/--
Finite-simplex Bregman mirror-step bound in the notation of NLHF Appendix D,
Lemma 2.  The potential derivative, strong-convexity inequality, and Hölder
bound are exposed as their literal mathematical premises; all argmax,
simplex-feasibility, three-point, and quadratic-remainder algebra is proved.
-/
theorem finiteBregmanMirror_simplex_bound_of_differentiableMaximizer
    {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (primalNorm dualNorm : (Coordinate → ℝ) → ℝ)
    (target update previous direction : Coordinate → ℝ)
    (modulus : ℝ) (potentialDerivative : (Coordinate → ℝ) →L[ℝ] ℝ)
    (hmodulus : 0 < modulus)
    (hmax : IsMaximizerOn FiniteProbabilitySimplex
      (finiteBregmanMirrorObjective potential gradient previous direction) update)
    (hupdate : FiniteProbabilitySimplex update)
    (htarget : FiniteProbabilitySimplex target)
    (hpotential : HasFDerivAt potential potentialDerivative update)
    (hgradient : potentialDerivative (target - update) =
      finiteVectorPairing (gradient update) (target - update))
    (hstrongConvex : modulus / 2 * primalNorm (update - previous) ^ 2 ≤
      finiteBregmanDivergence potential gradient update previous)
    (hholder : finiteVectorPairing (update - previous) direction ≤
      primalNorm (update - previous) * dualNorm direction) :
    finiteBregmanDivergence potential gradient target update ≤
      finiteBregmanDivergence potential gradient target previous +
        finiteVectorPairing (previous - target) direction +
          (2 / modulus) * dualNorm direction ^ 2 := by
  apply bregmanMirrorStep_bound_of_certificates
    (finiteBregmanDivergence potential gradient) (fun first second => first - second)
    finiteVectorPairing primalNorm dualNorm target update previous direction modulus hmodulus
  · ext coordinate
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  · unfold finiteVectorPairing
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · exact finiteBregmanMirror_threePoint_of_firstOrder potential gradient
      target update previous direction
      (finiteBregmanMirror_firstOrder_of_differentiableSimplexMaximizer
        potential gradient target update previous direction potentialDerivative hmax hupdate htarget
        hpotential hgradient)
  · exact hstrongConvex
  · exact hholder

/--
The finite-simplex form of Appendix-D Lemma 2 with the source's `ℓ_p` and
Hölder-dual `ℓ_q` analytic premise instantiated from the reusable finite
Hölder theorem.  Thus the only potential-specific analytic input left is the
source strong-convexity inequality.
-/
theorem finiteBregmanMirror_simplex_lp_bound_of_differentiableMaximizer
    {Coordinate : Type*} [Fintype Coordinate]
    (potential : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (target update previous direction : Coordinate → ℝ)
    (p q modulus : ℝ) (potentialDerivative : (Coordinate → ℝ) →L[ℝ] ℝ)
    (hpq : p.HolderConjugate q)
    (hmodulus : 0 < modulus)
    (hmax : IsMaximizerOn FiniteProbabilitySimplex
      (finiteBregmanMirrorObjective potential gradient previous direction) update)
    (hupdate : FiniteProbabilitySimplex update)
    (htarget : FiniteProbabilitySimplex target)
    (hpotential : HasFDerivAt potential potentialDerivative update)
    (hgradient : potentialDerivative (target - update) =
      finiteVectorPairing (gradient update) (target - update))
    (hstrongConvex : modulus / 2 * FiniteDimensionalNorms.lp p (update - previous) ^ 2 ≤
      finiteBregmanDivergence potential gradient update previous) :
    finiteBregmanDivergence potential gradient target update ≤
      finiteBregmanDivergence potential gradient target previous +
        finiteVectorPairing (previous - target) direction +
          (2 / modulus) * FiniteDimensionalNorms.lp q direction ^ 2 := by
  apply finiteBregmanMirror_simplex_bound_of_differentiableMaximizer
    potential gradient (FiniteDimensionalNorms.lp p) (FiniteDimensionalNorms.lp q)
    target update previous direction modulus potentialDerivative hmodulus hmax hupdate htarget
    hpotential hgradient hstrongConvex
  exact FiniteDimensionalNorms.dot_le_lp_mul_lp (update - previous) direction hpq

end Optimization
end AppliedModelingLib

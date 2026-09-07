import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Euclidean projection onto a closed convex set

This module gives the reusable selected Euclidean projection needed by
projected first-order algorithms.  It directly reuses Mathlib's Hilbert
projection theorem and its variational characterization:

* https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.html
* https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean

In particular, the existence/minimizer proof is upstream Mathlib work, not a
local reimplementation.  This module packages that result in AppliedModelingLib's
`IsVariationalEuclideanProjectionOn` interface and proves the standard
nonexpansiveness consequence used by projected gradient methods.
-/

namespace AppliedModelingLib

open scoped InnerProductSpace

section

variable {Parameter : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]

/--
A selected nearest point in a nonempty closed convex subset of a real Hilbert
space.  Existence is supplied by Mathlib's Hilbert projection theorem.
-/
noncomputable def hilbertProjection (domain : Set Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) : Parameter → Parameter :=
  fun input => Classical.choose
    (exists_norm_eq_iInf_of_complete_convex hnonempty hclosed.isComplete hconvex input)

/-- The selected Hilbert projection is feasible. -/
theorem hilbertProjection_mem (domain : Set Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) (input : Parameter) :
    hilbertProjection domain hnonempty hclosed hconvex input ∈ domain := by
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hnonempty hclosed.isComplete hconvex input)).1

/-- The selected Hilbert projection attains the distance infimum. -/
theorem hilbertProjection_norm_eq_iInf (domain : Set Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) (input : Parameter) :
    ‖input - hilbertProjection domain hnonempty hclosed hconvex input‖ =
      ⨅ candidate : domain, ‖input - (candidate : Parameter)‖ := by
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hnonempty hclosed.isComplete hconvex input)).2

/-- The selected projection satisfies AppliedModelingLib's variational projection interface. -/
theorem isVariationalEuclideanProjectionOn_hilbertProjection (domain : Set Parameter)
    (hnonempty : domain.Nonempty) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) :
    IsVariationalEuclideanProjectionOn domain (hilbertProjection domain hnonempty hclosed hconvex) := by
  constructor
  · intro input
    exact hilbertProjection_mem domain hnonempty hclosed hconvex input
  · intro input candidate hcandidate
    exact (norm_eq_iInf_iff_real_inner_le_zero hconvex
      (hilbertProjection_mem domain hnonempty hclosed hconvex input)).mp
      (hilbertProjection_norm_eq_iInf domain hnonempty hclosed hconvex input) candidate hcandidate

/--
The Hilbert projection onto a nonempty closed convex set is nonexpansive.
This derives the usual two-variational-inequality proof from Mathlib's
projection theorem, so callers do not need to assume a separate certificate.
-/
theorem hilbertProjection_lipschitzWith_one (domain : Set Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) :
    LipschitzWith 1 (hilbertProjection domain hnonempty hclosed hconvex) := by
  apply LipschitzWith.of_dist_le_mul
  intro input first
  let projectedInput := hilbertProjection domain hnonempty hclosed hconvex input
  let projectedFirst := hilbertProjection domain hnonempty hclosed hconvex first
  have hprojectedInput : projectedInput ∈ domain :=
    hilbertProjection_mem domain hnonempty hclosed hconvex input
  have hprojectedFirst : projectedFirst ∈ domain :=
    hilbertProjection_mem domain hnonempty hclosed hconvex first
  have hinput := (isVariationalEuclideanProjectionOn_hilbertProjection domain hnonempty hclosed hconvex).2
    input projectedFirst hprojectedFirst
  have hfirst := (isVariationalEuclideanProjectionOn_hilbertProjection domain hnonempty hclosed hconvex).2
    first projectedInput hprojectedInput
  have hinput_nonneg : 0 ≤ ⟪input - projectedInput, projectedInput - projectedFirst⟫_ℝ := by
    rw [show projectedFirst - projectedInput = -(projectedInput - projectedFirst) by abel,
      inner_neg_right] at hinput
    linarith
  have hfirst_nonneg : 0 ≤ ⟪projectedFirst - first, projectedInput - projectedFirst⟫_ℝ := by
    rw [show projectedFirst - first = -(first - projectedFirst) by abel,
      inner_neg_left]
    linarith
  have hsquared : ‖projectedInput - projectedFirst‖ ^ 2 ≤
      ⟪input - first, projectedInput - projectedFirst⟫_ℝ := by
    rw [show input - first = (input - projectedInput) + (projectedInput - projectedFirst) +
        (projectedFirst - first) by abel, inner_add_left, inner_add_left,
      real_inner_self_eq_norm_sq]
    linarith
  have hproduct : ‖projectedInput - projectedFirst‖ ^ 2 ≤
      ‖input - first‖ * ‖projectedInput - projectedFirst‖ :=
    hsquared.trans (real_inner_le_norm _ _)
  have hnorm : ‖projectedInput - projectedFirst‖ ≤ ‖input - first‖ := by
    nlinarith [norm_nonneg (input - first), norm_nonneg (projectedInput - projectedFirst)]
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hnorm

end

end AppliedModelingLib

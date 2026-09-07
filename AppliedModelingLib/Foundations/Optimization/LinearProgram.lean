import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Optimization.Certificate

open scoped BigOperators

namespace AppliedModelingLib
namespace Optimization

/-!
# Finite Linear-Program Certificates

Lightweight finite LP records for paper proofs that use explicit primal/dual
witnesses rather than a generic solver.

## Main declarations

- `StandardMaxLP`: nonnegative-variable maximization LPs with `Ax <= b`.
- `StandardMaxLP.PrimalFeasible`, `StandardMaxLP.DualFeasible`.
- `StandardMaxLP.weak_duality`.
- `StandardMaxLPCertificate`: matching feasible primal/dual witnesses with the
  same value.
- `StandardMaxLPCertificate.toUpperBoundCertificate`.

This is intentionally below a full basic-feasible-solution API.  It handles the
common EC proof step "closed-form primal witness plus matching dual bound proves
optimality"; BFS support/rank theorems can be layered on top later.
-/

/--
A finite maximization LP in standard inequality form:

maximize `c · x` subject to `A x <= b` and `x >= 0`.
-/
structure StandardMaxLP (ι κ : Type*) where
  A : κ → ι → ℝ
  b : κ → ℝ
  c : ι → ℝ

namespace StandardMaxLP

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The primal objective `c · x`. -/
noncomputable def primalObjective (P : StandardMaxLP ι κ)
    (x : ι → ℝ) : ℝ :=
  ∑ i : ι, P.c i * x i

/-- The dual objective `y · b`. -/
noncomputable def dualObjective (P : StandardMaxLP ι κ)
    (y : κ → ℝ) : ℝ :=
  ∑ k : κ, y k * P.b k

/-- Primal feasibility: `x >= 0` and `A x <= b`. -/
def PrimalFeasible (P : StandardMaxLP ι κ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ k, (∑ i : ι, P.A k i * x i) ≤ P.b k

/-- Dual feasibility: `y >= 0` and `A^T y >= c`. -/
def DualFeasible (P : StandardMaxLP ι κ) (y : κ → ℝ) : Prop :=
  (∀ k, 0 ≤ y k) ∧ ∀ i, P.c i ≤ ∑ k : κ, P.A k i * y k

/-- Variables with nonzero value. Useful as a lightweight support scaffold. -/
noncomputable def support (x : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

/-- Constraints that bind at `x`. Useful as a lightweight BFS scaffold. -/
noncomputable def activeConstraints (P : StandardMaxLP ι κ)
    (x : ι → ℝ) : Finset κ := by
  classical
  exact Finset.univ.filter
    (fun k => (∑ i : ι, P.A k i * x i) = P.b k)

/-- Finite LP weak duality for standard nonnegative-variable maximization LPs. -/
theorem weak_duality (P : StandardMaxLP ι κ)
    {x : ι → ℝ} {y : κ → ℝ}
    (hx : P.PrimalFeasible x) (hy : P.DualFeasible y) :
    P.primalObjective x ≤ P.dualObjective y := by
  classical
  have hcoef :
      (∑ i : ι, P.c i * x i) ≤
        ∑ i : ι, (∑ k : κ, P.A k i * y k) * x i := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact mul_le_mul_of_nonneg_right (hy.2 i) (hx.1 i)
  have hswap :
      (∑ i : ι, (∑ k : κ, P.A k i * y k) * x i) =
        ∑ k : κ, y k * ∑ i : ι, P.A k i * x i := by
    calc
      (∑ i : ι, (∑ k : κ, P.A k i * y k) * x i)
          = ∑ i : ι, ∑ k : κ, (P.A k i * y k) * x i := by
              simp [Finset.sum_mul]
      _ = ∑ k : κ, ∑ i : ι, (P.A k i * y k) * x i := by
              rw [Finset.sum_comm]
      _ = ∑ k : κ, y k * ∑ i : ι, P.A k i * x i := by
              refine Finset.sum_congr rfl ?_
              intro k _
              calc
                (∑ i : ι, (P.A k i * y k) * x i)
                    = ∑ i : ι, y k * (P.A k i * x i) := by
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ring
                _ = y k * ∑ i : ι, P.A k i * x i := by
                        rw [Finset.mul_sum]
  have hbound :
      (∑ k : κ, y k * ∑ i : ι, P.A k i * x i) ≤
        ∑ k : κ, y k * P.b k := by
    refine Finset.sum_le_sum ?_
    intro k _
    exact mul_le_mul_of_nonneg_left (hx.2 k) (hy.1 k)
  calc
    P.primalObjective x = ∑ i : ι, P.c i * x i := rfl
    _ ≤ ∑ i : ι, (∑ k : κ, P.A k i * y k) * x i := hcoef
    _ = ∑ k : κ, y k * ∑ i : ι, P.A k i * x i := hswap
    _ ≤ ∑ k : κ, y k * P.b k := hbound
    _ = P.dualObjective y := rfl

end StandardMaxLP

/--
A primal/dual certificate for a standard finite maximization LP.

The certificate is intentionally constructive: it stores the primal witness,
the dual witness, feasibility proofs, and the common value.
-/
structure StandardMaxLPCertificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : StandardMaxLP ι κ) (value : ℝ) where
  primal : ι → ℝ
  dual : κ → ℝ
  primal_feasible : P.PrimalFeasible primal
  dual_feasible : P.DualFeasible dual
  primal_value : P.primalObjective primal = value
  dual_value : P.dualObjective dual = value

namespace StandardMaxLPCertificate

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {P : StandardMaxLP ι κ} {value : ℝ}

/-- A matching primal/dual LP certificate gives an upper-bound certificate. -/
def toUpperBoundCertificate
    (cert : StandardMaxLPCertificate P value) :
    UpperBoundCertificate P.PrimalFeasible P.primalObjective value where
  candidate := cert.primal
  candidate_feasible := cert.primal_feasible
  candidate_value := cert.primal_value
  upper_bound := by
    intro x hx
    rw [← cert.dual_value]
    exact P.weak_duality hx cert.dual_feasible

/-- A matching primal/dual LP certificate proves primal optimality. -/
theorem isMaximizerOn
    (cert : StandardMaxLPCertificate P value) :
    IsMaximizerOn P.PrimalFeasible P.primalObjective cert.primal :=
  cert.toUpperBoundCertificate.isMaximizerOn

end StandardMaxLPCertificate

end Optimization
end AppliedModelingLib

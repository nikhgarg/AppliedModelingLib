/-
Copyright (c) 2026 Alexander Quispe and Kevin Xu. All rights reserved.
Released under Apache 2.0 license.
Authors: Alexander Quispe, Kevin Xu
-/
import EconCSLib.Foundations.Optimization.Argmax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Quispe–Xu 2026: model primitives

Paper-local definitions for agentic delegation (arXiv 2605.25438v2, §4 and
Appendix A). Subscripts \((i,k,t)\) are suppressed as in the source.

## Main declarations

- `TaskParams`, `TaskParams.WellFormed`
- `caraUtility`, `caraExpectedUtility`, `certaintyEquivalent` (Eqs. 14–15)
- `V_S`, `V_C`, `V_D` (Eqs. 1–3)
- `Mode`, `Menu1`, `Menu2`, `V1`, `V2` (Eq. 21)
- `T_S`, `T_C`, `T_1`, `T_D`, `T_2`, `B` (Eqs. 4–7)
- `Z`, `LanguageActive`, `languageCount`
- `Assumption1_foothold`, `Assumption2Hypotheses`, `Assumption3_exchangeable`
-/

open scoped BigOperators
set_option linter.style.openClassical false

namespace QX26AgenticDelegation

noncomputable section

/-! ## P0. Environment -/

/-- Language-task primitives with subscripts \((i,k,t)\) suppressed.
`zA` is agent competence \(z(A)\); `kappa` is verification cost
\(\kappa(a,s)\); `sigmaD2` is residual agent-error variance
\(\sigma_D^2(a,s,A)\). -/
structure TaskParams where
  omega : ℝ
  s : ℝ
  mu : ℝ
  pi : ℝ
  b : ℝ
  rho : ℝ
  gamma : ℝ
  rC : ℝ
  lambda : ℝ
  a : ℝ
  zA : ℝ
  kappa : ℝ
  rD : ℝ
  sigmaD2 : ℝ

namespace TaskParams

/-- Well-formedness: \(s\in[0,1]\), \(\pi>0\), \(\rho>0\),
\(\lambda\in(0,1]\), \(a\ge 0\), \(\sigma_D^2\ge 0\). -/
structure WellFormed (p : TaskParams) : Prop where
  s_nonneg : 0 ≤ p.s
  s_le_one : p.s ≤ 1
  pi_pos : 0 < p.pi
  rho_pos : 0 < p.rho
  lambda_pos : 0 < p.lambda
  lambda_le_one : p.lambda ≤ 1
  a_nonneg : 0 ≤ p.a
  sigmaD2_nonneg : 0 ≤ p.sigmaD2

lemma WellFormed.pi_ne_zero {p : TaskParams} (hp : p.WellFormed) : p.pi ≠ 0 :=
  hp.pi_pos.ne'

lemma WellFormed.rho_ne_zero {p : TaskParams} (hp : p.WellFormed) : p.rho ≠ 0 :=
  hp.rho_pos.ne'

end TaskParams

/-! ## Eqs. (14)–(15): CARA–Normal closed forms

Closed-form MGF / CE evaluations (Eqs. 14–15), not a measure-theoretic
integral against `gaussianReal`. `EconCSLib.Foundations.Probability.Gaussian`
is conjugate-precision / CDF-API and does not supply this CARA identity
without a new bridge, so the paper-local closed form is kept.
-/

/-- CARA utility \(u(y)=-\exp(-\rho y)\). -/
def caraUtility (rho y : ℝ) : ℝ :=
  -Real.exp (-(rho * y))

/-- Expected CARA utility of \(Y\sim\mathcal{N}(m,\sigma^2)\) (Eq. 14). -/
def caraExpectedUtility (m sigma2 rho : ℝ) : ℝ :=
  -Real.exp (-(rho * m) + (rho ^ 2 * sigma2) / 2)

/-- Certainty equivalent \(\mathrm{CE}=m-\rho\sigma^2/2\) (Eq. 15). -/
def certaintyEquivalent (m sigma2 rho : ℝ) : ℝ :=
  m - (rho * sigma2) / 2

/-! ## Eqs. (1)–(3): mode surpluses -/

/-- Solo net CE surplus (Eq. 1).
\(V^S=\omega+s\mu-\rho s^2/(2\pi)-b\). -/
def V_S (p : TaskParams) : ℝ :=
  p.omega + p.s * p.mu - (p.rho * p.s ^ 2) / (2 * p.pi) - p.b

/-- Copilot / Gen-1 surplus (Eq. 2).
\(V^C=V^S+\gamma s-r_C\). -/
def V_C (p : TaskParams) : ℝ :=
  V_S p + p.gamma * p.s - p.rC

/-- Delegation / Gen-2 surplus (Eq. 3). -/
def V_D (p : TaskParams) : ℝ :=
  p.omega + (1 - p.lambda) * p.s * p.mu + p.lambda * p.a * p.zA
    - p.kappa - p.rD - p.b
    - (p.rho / 2)
        * (((1 - p.lambda) ^ 2 * p.s ^ 2) / p.pi + p.sigmaD2)

/-! ## P1. Menus, best surplus, activation -/

/-- Production modes \(S,C,D\). -/
inductive Mode where
  | solo
  | copilot
  | delegate
deriving DecidableEq, Repr

/-- Surplus of a named mode. -/
def surplus : Mode → TaskParams → ℝ
  | .solo => V_S
  | .copilot => V_C
  | .delegate => V_D

/-- Pre-agent menu \(\mathcal{M}_1=\{S,C\}\). -/
def Menu1 : Finset Mode := {Mode.solo, Mode.copilot}

/-- Post-agent menu \(\mathcal{M}_2=\{S,C,D\}\). -/
def Menu2 : Finset Mode := {Mode.solo, Mode.copilot, Mode.delegate}

/-- Reuse `EconCSLib.Decision.IsPointwiseMax` (same statement). -/
abbrev IsPointwiseMax {ι α : Type*} (score : ι → α → ℝ) (choose : ι → α) : Prop :=
  EconCSLib.Decision.IsPointwiseMax score choose

/-- Generation index \(g\in\{1,2\}\). -/
inductive Generation where
  | gen1
  | gen2
deriving DecidableEq, Repr

/-- Best surplus under \(\mathcal{M}_1\): \(V^1=\max\{V^S,V^C\}\). -/
def V1 (p : TaskParams) : ℝ :=
  max (V_S p) (V_C p)

/-- Best surplus under \(\mathcal{M}_2\): \(V^2=\max\{V^S,V^C,V^D\}\)
(Eq. 21). -/
def V2 (p : TaskParams) : ℝ :=
  max (V1 p) (V_D p)

/-- Generation-indexed best surplus. -/
def V_g : Generation → TaskParams → ℝ
  | .gen1 => V1
  | .gen2 => V2

/--
Language activity is a **production** frontier, not a skill frontier
(Remark 1). A language is active when some mode delivers nonnegative CE
surplus, including delegation (agent executes share \(\lambda\); the
developer specifies and verifies). Activity does not claim that adoption
raises \(s\).
-/
def LanguageActive (V : ℝ) : Prop :=
  0 ≤ V

/-- \(\{0,1\}\) activity indicator \(Z=\mathbf{1}[V\ge 0]\). -/
def Z (V : ℝ) : ℝ :=
  if 0 ≤ V then (1 : ℝ) else 0

/-- Generation-indexed activity indicator \(Z^g\). -/
def Z_g (g : Generation) (p : TaskParams) : ℝ :=
  Z (V_g g p)

/-- Monthly language count \(N^g=\sum_k Z^g_k\) on a finite language set. -/
def languageCount {n : ℕ} (Vfun : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, Z (Vfun k)

open Classical

/-- Active-language set \(\{k:V_k\ge 0\}\). -/
def activeSet {n : ℕ} (Vfun : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => 0 ≤ Vfun k)

/-! ## Eqs. (4)–(7): thresholds and agentic advantage -/

/-- Solo activation threshold (Eq. 4).
\(T^S=b-s\mu+\rho s^2/(2\pi)\). -/
def T_S (p : TaskParams) : ℝ :=
  p.b - p.s * p.mu + (p.rho * p.s ^ 2) / (2 * p.pi)

/-- Copilot threshold (inline after Eq. 4; appendix Eq. 17).
\(T^C=T^S-(\gamma s-r_C)\). -/
def T_C (p : TaskParams) : ℝ :=
  T_S p - (p.gamma * p.s - p.rC)

/-- Generation-1 threshold (Eq. 5).
\(T^1=\min\{T^S,T^C\}\). -/
def T_1 (p : TaskParams) : ℝ :=
  min (T_S p) (T_C p)

/-- Delegation threshold (Eq. 6). -/
def T_D (p : TaskParams) : ℝ :=
  p.b - (1 - p.lambda) * p.s * p.mu - p.lambda * p.a * p.zA
    + p.kappa + p.rD
    + (p.rho / 2)
        * (((1 - p.lambda) ^ 2 * p.s ^ 2) / p.pi + p.sigmaD2)

/-- Post-agent threshold \(T^2=\min\{T^1,T^D\}\). -/
def T_2 (p : TaskParams) : ℝ :=
  min (T_1 p) (T_D p)

/-- Generation-indexed entry threshold. -/
def T_g : Generation → TaskParams → ℝ
  | .gen1 => T_1
  | .gen2 => T_2

/-- Agentic threshold reduction (Eq. 7).
\(B=\lambda[az(A)-s\mu]-\kappa-r_D+(\rho/2)[((2\lambda-\lambda^2)s^2)/\pi-\sigma_D^2]\). -/
def B (p : TaskParams) : ℝ :=
  p.lambda * (p.a * p.zA - p.s * p.mu) - p.kappa - p.rD
    + (p.rho / 2)
        * (((2 * p.lambda - p.lambda ^ 2) * p.s ^ 2) / p.pi - p.sigmaD2)

/-! ## Assumptions -/

/-- Assumption 1 (augmentation requires a foothold), unfamiliar-language
clause: \(\gamma s-r_C\le 0\). -/
def Assumption1_foothold (p : TaskParams) : Prop :=
  p.gamma * p.s - p.rC ≤ 0

/-- Familiar-language dual of Assumption 1: \(\gamma\bar s-r_C>0\). -/
def Assumption1_foothold_familiar (p : TaskParams) : Prop :=
  0 < p.gamma * p.s - p.rC

/--
Assumption 2 (verification technology). The source states
\(\kappa_a<0\), \(\kappa_s\le 0\), and
\(\partial\sigma_D^2/\partial a,\partial\sigma_D^2/\partial s,\partial\sigma_D^2/\partial A\le 0\).
This isolated package does **not** invent derivatives: the five signed
quantities are finite-difference representatives supplied as data, and
the inequalities are hypotheses (not axioms).
-/
structure Assumption2Hypotheses where
  kappa_a_neg : ℝ
  kappa_s_nonpos : ℝ
  sigmaD2_da : ℝ
  sigmaD2_ds : ℝ
  sigmaD2_dA : ℝ
  h_kappa_a : kappa_a_neg < 0
  h_kappa_s : kappa_s_nonpos ≤ 0
  h_sigma_a : sigmaD2_da ≤ 0
  h_sigma_s : sigmaD2_ds ≤ 0
  h_sigma_A : sigmaD2_dA ≤ 0

/-- Conjunction of Assumption 2's five signed comparisons. -/
def Assumption2_verification (H : Assumption2Hypotheses) : Prop :=
  H.kappa_a_neg < 0 ∧ H.kappa_s_nonpos ≤ 0 ∧ H.sigmaD2_da ≤ 0 ∧
    H.sigmaD2_ds ≤ 0 ∧ H.sigmaD2_dA ≤ 0

/-- Assumption 3: unfamiliar languages are exchangeable given developer
characteristics, with a common per-language activation increment \(p\ge 0\). -/
def Assumption3_exchangeable {K : Type*} (U : Finset K) (pInc : K → ℝ) : Prop :=
  (∀ k ∈ U, 0 ≤ pInc k) ∧ ∃ p : ℝ, ∀ k ∈ U, pInc k = p

/-! ## Cumulative-language gap (Eq. 10) and Bayes update (Eqs. 28–29) -/

/-- One-horizon cumulative-language gap \(\Delta C\) (Eq. 10) on a finite
unfamiliar set. -/
def cumulativeGap {K : Type*} (U : Finset K) (p1 p2 : K → ℝ) (s : ℕ) : ℝ :=
  ∑ k ∈ U, ((1 - p1 k) ^ (s + 1) - (1 - p2 k) ^ (s + 1))

/-- Posterior precision \(\pi'=\pi+q\) (Eq. 29). -/
def posteriorPrecision (pi q : ℝ) : ℝ :=
  pi + q

/-- Posterior mean \(\mu'=(\pi\mu+q\bar x_q)/(\pi+q)\) (Eq. 29). -/
def posteriorMean (pi mu q xbar : ℝ) : ℝ :=
  (pi * mu + q * xbar) / (pi + q)

/-- Total precision of \(L\) independent signals (Eq. 28). -/
def totalPrecision {L : ℕ} (sigma2 : Fin L → ℝ) : ℝ :=
  ∑ ℓ : Fin L, 1 / sigma2 ℓ

end

end QX26AgenticDelegation

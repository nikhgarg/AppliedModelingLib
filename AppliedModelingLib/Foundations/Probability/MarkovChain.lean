import AppliedModelingLib.Foundations.Probability.PMFKernel
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AppliedModelingLib

/--
A finite-state Markov transition kernel, represented as a probability mass
function over next states for each current state.
-/
abbrev FiniteMarkovKernel (σ : Type*) [Fintype σ] [DecidableEq σ] :=
  PMFKernel σ σ

namespace FiniteMarkovKernel

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Real-valued transition probability from `x` to `y`. -/
noncomputable def transitionProb (K : FiniteMarkovKernel σ) (x y : σ) : ℝ :=
  (K x y).toReal

theorem transitionProb_nonneg (K : FiniteMarkovKernel σ) (x y : σ) :
    0 ≤ transitionProb K x y := by
  exact ENNReal.toReal_nonneg

/-- Every row of a finite Markov kernel has total real mass one. -/
theorem transitionProb_sum_eq_one (K : FiniteMarkovKernel σ) (x : σ) :
    ∑ y : σ, transitionProb K x y = 1 := by
  simpa [transitionProb] using pmfToRealSum (K x)

/-- One-step push-forward of a distribution through a Markov kernel. -/
noncomputable def step (K : FiniteMarkovKernel σ) (μ : PMF σ) : PMF σ :=
  μ.bind K

/-- Distribution after `n` Markov transitions. -/
noncomputable def iterate (K : FiniteMarkovKernel σ) : ℕ → PMF σ → PMF σ
  | 0, μ => μ
  | n + 1, μ => step K (iterate K n μ)

@[simp] theorem iterate_zero (K : FiniteMarkovKernel σ) (μ : PMF σ) :
    iterate K 0 μ = μ := by
  rfl

@[simp] theorem iterate_succ (K : FiniteMarkovKernel σ) (n : ℕ) (μ : PMF σ) :
    iterate K (n + 1) μ = step K (iterate K n μ) := by
  rfl

/-- Expected value of a state observable after one transition from `x`. -/
noncomputable def expectedNext (K : FiniteMarkovKernel σ) (f : σ → ℝ) (x : σ) : ℝ :=
  pmfExp (K x) f

theorem expectedNext_eq_sum (K : FiniteMarkovKernel σ) (f : σ → ℝ) (x : σ) :
    expectedNext K f x = ∑ y : σ, transitionProb K x y * f y := by
  rfl

@[simp] theorem expectedNext_const (K : FiniteMarkovKernel σ) (c : ℝ) (x : σ) :
    expectedNext K (fun _ => c) x = c := by
  simp [expectedNext]

/-- One-step drift of a potential/Lyapunov function. -/
noncomputable def drift (K : FiniteMarkovKernel σ) (V : σ → ℝ) (x : σ) : ℝ :=
  expectedNext K V x - V x

@[simp] theorem drift_const (K : FiniteMarkovKernel σ) (c : ℝ) (x : σ) :
    drift K (fun _ => c) x = 0 := by
  simp [drift]

theorem drift_nonpos_iff (K : FiniteMarkovKernel σ) (V : σ → ℝ) (x : σ) :
    drift K V x ≤ 0 ↔ expectedNext K V x ≤ V x := by
  unfold drift
  constructor <;> intro h <;> linarith

theorem drift_nonpos_of_expectedNext_le
    (K : FiniteMarkovKernel σ) (V : σ → ℝ) (x : σ)
    (h : expectedNext K V x ≤ V x) :
    drift K V x ≤ 0 := by
  exact (drift_nonpos_iff K V x).2 h

theorem pmfExp_mono (μ : PMF σ) {f g : σ → ℝ}
    (h : ∀ x, f x ≤ g x) :
    pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  exact Finset.sum_le_sum (fun x _ =>
    mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg)

theorem expectedNext_mono (K : FiniteMarkovKernel σ) {f g : σ → ℝ} (x : σ)
    (h : ∀ y, f y ≤ g y) :
    expectedNext K f x ≤ expectedNext K g x := by
  exact pmfExp_mono (K x) h

/-- `π` is stationary for `K` if one transition leaves it unchanged. -/
def Stationary (K : FiniteMarkovKernel σ) (π : PMF σ) : Prop :=
  step K π = π

theorem stationary_step {K : FiniteMarkovKernel σ} {π : PMF σ}
    (hπ : Stationary K π) :
    step K π = π :=
  hπ

theorem iterate_stationary (K : FiniteMarkovKernel σ) {π : PMF σ}
    (hπ : Stationary K π) :
    ∀ n : ℕ, iterate K n π = π := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      calc
        iterate K (n + 1) π = step K (iterate K n π) := by
          rfl
        _ = step K π := by
          rw [ih]
        _ = π := hπ

theorem stationary_expectation {K : FiniteMarkovKernel σ} {π : PMF σ}
    (hπ : Stationary K π) (f : σ → ℝ) :
    pmfExp (step K π) f = pmfExp π f := by
  rw [hπ]

theorem iterate_stationary_expectation (K : FiniteMarkovKernel σ) {π : PMF σ}
    (hπ : Stationary K π) (n : ℕ) (f : σ → ℝ) :
    pmfExp (iterate K n π) f = pmfExp π f := by
  rw [iterate_stationary K hπ n]

/-- A state is absorbing if its next-state law is the point mass at itself. -/
def Absorbing (K : FiniteMarkovKernel σ) (x : σ) : Prop :=
  K x = PMF.pure x

theorem expectedNext_of_absorbing {K : FiniteMarkovKernel σ} {x : σ}
    (hx : Absorbing K x) (f : σ → ℝ) :
    expectedNext K f x = f x := by
  rw [expectedNext, hx]
  unfold pmfExp
  calc
    ∑ y : σ, ((PMF.pure x : PMF σ) y).toReal * f y =
        ((PMF.pure x : PMF σ) x).toReal * f x := by
          refine Finset.sum_eq_single x ?_ ?_
          · intro y _ hyx
            simp [hyx]
          · intro hxnot
            simp at hxnot
    _ = f x := by
      simp

theorem drift_of_absorbing {K : FiniteMarkovKernel σ} {x : σ}
    (hx : Absorbing K x) (V : σ → ℝ) :
    drift K V x = 0 := by
  simp [drift, expectedNext_of_absorbing hx V]

/--
Pointwise comparison of two kernels under a fixed observable. This is useful
when comparing two policies, such as two surge rules, using the same state
space and same value/potential function.
-/
def ExpectedLe (K L : FiniteMarkovKernel σ) (f : σ → ℝ) : Prop :=
  ∀ x, expectedNext K f x ≤ expectedNext L f x

theorem drift_le_of_expectedLe {K L : FiniteMarkovKernel σ} {V : σ → ℝ}
    (h : ExpectedLe K L V) (x : σ) :
    drift K V x ≤ drift L V x := by
  unfold drift
  linarith [h x]

/--
A kernel is stochastically monotone if larger states have larger one-step
expectations for every monotone real observable.
-/
def StochasticallyMonotone [Preorder σ] (K : FiniteMarkovKernel σ) : Prop :=
  ∀ ⦃x y : σ⦄, x ≤ y → ∀ f : σ → ℝ, Monotone f →
    expectedNext K f x ≤ expectedNext K f y

theorem expectedNext_le_of_stochasticallyMonotone [Preorder σ]
    {K : FiniteMarkovKernel σ} (hK : StochasticallyMonotone K)
    {x y : σ} (hxy : x ≤ y) {f : σ → ℝ} (hf : Monotone f) :
    expectedNext K f x ≤ expectedNext K f y :=
  hK hxy f hf

end FiniteMarkovKernel

end AppliedModelingLib

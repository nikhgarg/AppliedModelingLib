import AppliedModelingLib.Foundations.Probability.MarkovChain

open scoped BigOperators

namespace AppliedModelingLib

/-!
# Finite controlled Markov chains and MDPs

This module provides a small reusable interface for finite Markov decision
processes. It is designed for dynamic platform, pricing, bandit, and surge-style
papers that need controlled transition kernels before they need a full
discounted or average-reward theory.

## Main declarations

- `FiniteMDP`: finite-state/action transition model with one-step rewards.
- `FiniteMDP.Policy`: randomized Markov policy.
- `FiniteMDP.controlledKernel`: Markov kernel induced by an MDP and policy.
- `FiniteMDP.horizonValue`: finite-horizon value of a fixed policy.
- `FiniteMDP.optimalValue`: finite-horizon optimal value by Bellman recursion.
- `FiniteMDP.occupancyMass`: finite-horizon state occupancy mass.
-/

/--
A finite Markov decision process with state type `σ` and action type `α`.
The reward may depend on the current state, action, and realized next state.
-/
structure FiniteMDP (σ α : Type*) where
  transition : σ → α → PMF σ
  reward : σ → α → σ → ℝ

namespace FiniteMDP

variable {σ α β : Type*}
variable [Fintype σ] [DecidableEq σ] [Fintype α] [DecidableEq α]

/-- A randomized Markov policy assigning an action distribution to each state. -/
abbrev Policy (σ α : Type*) := PMFKernel σ α

/-- A deterministic Markov policy as a special randomized policy. -/
noncomputable def deterministicPolicy (choose : σ → α) : Policy σ α :=
  PMFKernel.pure choose

/-- Real-valued transition probability for a fixed state-action pair. -/
noncomputable def transitionProb (M : FiniteMDP σ α) (x : σ) (a : α) (y : σ) : ℝ :=
  ((M.transition x a) y).toReal

theorem transitionProb_nonneg (M : FiniteMDP σ α) (x : σ) (a : α) (y : σ) :
    0 ≤ transitionProb M x a y := by
  exact ENNReal.toReal_nonneg

/-- Real-valued action probability under a randomized policy. -/
noncomputable def actionProb (π : Policy σ α) (x : σ) (a : α) : ℝ :=
  ((π x) a).toReal

theorem actionProb_nonneg (π : Policy σ α) (x : σ) (a : α) :
    0 ≤ actionProb π x a := by
  exact ENNReal.toReal_nonneg

/-- Markov transition kernel induced by an MDP and a randomized policy. -/
noncomputable def controlledKernel (M : FiniteMDP σ α) (π : Policy σ α) :
    FiniteMarkovKernel σ :=
  fun x => (π x).bind (fun a => M.transition x a)

@[simp] theorem controlledKernel_deterministic
    (M : FiniteMDP σ α) (choose : σ → α) (x : σ) :
    controlledKernel M (deterministicPolicy choose) x = M.transition x (choose x) := by
  simp [controlledKernel, deterministicPolicy]

/--
One-step value of choosing action `a` in state `x`, receiving the realized
one-step reward, and then continuing with terminal/continuation value `V`.
-/
noncomputable def actionValue (M : FiniteMDP σ α) (V : σ → ℝ) (x : σ) (a : α) :
    ℝ :=
  pmfExp (M.transition x a) (fun y => M.reward x a y + V y)

theorem actionValue_mono (M : FiniteMDP σ α) {V W : σ → ℝ}
    (hVW : ∀ x, V x ≤ W x) (x : σ) (a : α) :
    actionValue M V x a ≤ actionValue M W x a := by
  unfold actionValue
  exact FiniteMarkovKernel.pmfExp_mono (M.transition x a) (fun y =>
    add_le_add_right (hVW y) (M.reward x a y))

/-- One Bellman step for a fixed randomized policy. -/
noncomputable def policyValueStep
    (M : FiniteMDP σ α) (π : Policy σ α) (V : σ → ℝ) (x : σ) : ℝ :=
  pmfExp (π x) (fun a => actionValue M V x a)

theorem policyValueStep_mono (M : FiniteMDP σ α) (π : Policy σ α)
    {V W : σ → ℝ} (hVW : ∀ x, V x ≤ W x) (x : σ) :
    policyValueStep M π V x ≤ policyValueStep M π W x := by
  unfold policyValueStep
  exact FiniteMarkovKernel.pmfExp_mono (π x) (fun a =>
    actionValue_mono M hVW x a)

/-- Expectation under a point mass. -/
theorem pmfExp_pure [Fintype β] [DecidableEq β] (b : β) (f : β → ℝ) :
    pmfExp (PMF.pure b) f = f b := by
  unfold pmfExp
  calc
    ∑ y : β, ((PMF.pure b : PMF β) y).toReal * f y =
        ((PMF.pure b : PMF β) b).toReal * f b := by
          refine Finset.sum_eq_single b ?_ ?_
          · intro y _ hy
            simp [hy]
          · intro hb
            simp at hb
    _ = f b := by
      simp

@[simp] theorem policyValueStep_deterministic
    (M : FiniteMDP σ α) (choose : σ → α) (V : σ → ℝ) (x : σ) :
  policyValueStep M (deterministicPolicy choose) V x =
      actionValue M V x (choose x) := by
  rw [policyValueStep, deterministicPolicy, PMFKernel.pure_apply, pmfExp_pure]

/-- Finite-horizon value for a fixed policy, with zero terminal value. -/
noncomputable def horizonValue
    (M : FiniteMDP σ α) (π : Policy σ α) : ℕ → σ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => policyValueStep M π (horizonValue M π n) x

@[simp] theorem horizonValue_zero
    (M : FiniteMDP σ α) (π : Policy σ α) (x : σ) :
    horizonValue M π 0 x = 0 := by
  rfl

@[simp] theorem horizonValue_succ
    (M : FiniteMDP σ α) (π : Policy σ α) (n : ℕ) (x : σ) :
    horizonValue M π (n + 1) x =
      policyValueStep M π (horizonValue M π n) x := by
  rfl

/-- Finite maximum Bellman step over actions. -/
noncomputable def optimalStep [Nonempty α]
    (M : FiniteMDP σ α) (V : σ → ℝ) (x : σ) : ℝ :=
  (Finset.univ : Finset α).sup' Finset.univ_nonempty (fun a => actionValue M V x a)

theorem actionValue_le_optimalStep [Nonempty α]
    (M : FiniteMDP σ α) (V : σ → ℝ) (x : σ) (a : α) :
    actionValue M V x a ≤ optimalStep M V x := by
  unfold optimalStep
  exact Finset.le_sup' (s := (Finset.univ : Finset α))
    (f := fun a => actionValue M V x a) (by simp)

theorem exists_action_optimalStep [Nonempty α]
    (M : FiniteMDP σ α) (V : σ → ℝ) (x : σ) :
    ∃ a : α, optimalStep M V x = actionValue M V x a := by
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset α))
      (H := Finset.univ_nonempty)
      (f := fun a => actionValue M V x a)
  exact ⟨a, by simpa [optimalStep] using ha⟩

/-- Expectation bounded above by a constant pointwise upper bound. -/
theorem pmfExp_le_const [Fintype β] [DecidableEq β]
    (μ : PMF β) {f : β → ℝ} {c : ℝ} (h : ∀ b, f b ≤ c) :
    pmfExp μ f ≤ c := by
  unfold pmfExp
  calc
    ∑ b : β, (μ b).toReal * f b ≤ ∑ b : β, (μ b).toReal * c := by
      exact Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (h b) ENNReal.toReal_nonneg)
    _ = (∑ b : β, (μ b).toReal) * c := by
      rw [Finset.sum_mul]
    _ = c := by
      rw [pmfToRealSum μ]
      simp

theorem policyValueStep_le_optimalStep [Nonempty α]
    (M : FiniteMDP σ α) (π : Policy σ α) (V : σ → ℝ) (x : σ) :
    policyValueStep M π V x ≤ optimalStep M V x := by
  unfold policyValueStep
  exact pmfExp_le_const (π x) (c := optimalStep M V x)
    (fun a => actionValue_le_optimalStep M V x a)

/-- Finite-horizon optimal value, with zero terminal value. -/
noncomputable def optimalValue [Nonempty α]
    (M : FiniteMDP σ α) : ℕ → σ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => optimalStep M (optimalValue M n) x

@[simp] theorem optimalValue_zero [Nonempty α]
    (M : FiniteMDP σ α) (x : σ) :
    optimalValue M 0 x = 0 := by
  rfl

@[simp] theorem optimalValue_succ [Nonempty α]
    (M : FiniteMDP σ α) (n : ℕ) (x : σ) :
    optimalValue M (n + 1) x = optimalStep M (optimalValue M n) x := by
  rfl

/-- Bellman optimality: the finite-horizon value is the maximum Bellman step. -/
theorem bellman_optimality [Nonempty α]
    (M : FiniteMDP σ α) (n : ℕ) (x : σ) :
    optimalValue M (n + 1) x = optimalStep M (optimalValue M n) x := by
  rfl

theorem actionValue_le_optimalValue_succ [Nonempty α]
    (M : FiniteMDP σ α) (n : ℕ) (x : σ) (a : α) :
    actionValue M (optimalValue M n) x a ≤ optimalValue M (n + 1) x := by
  simpa using actionValue_le_optimalStep M (optimalValue M n) x a

theorem exists_action_optimalValue_succ [Nonempty α]
    (M : FiniteMDP σ α) (n : ℕ) (x : σ) :
    ∃ a : α, optimalValue M (n + 1) x =
      actionValue M (optimalValue M n) x a := by
  simpa using exists_action_optimalStep M (optimalValue M n) x

/-- A deterministic action rule is greedy for a continuation value. -/
def Greedy [Nonempty α] (M : FiniteMDP σ α) (choose : σ → α) (V : σ → ℝ) : Prop :=
  ∀ x, actionValue M V x (choose x) = optimalStep M V x

theorem policyValueStep_eq_optimalStep_of_greedy [Nonempty α]
    (M : FiniteMDP σ α) {choose : σ → α} {V : σ → ℝ}
    (hchoose : Greedy M choose V) (x : σ) :
    policyValueStep M (deterministicPolicy choose) V x = optimalStep M V x := by
  rw [policyValueStep_deterministic]
  exact hchoose x

theorem horizonValue_le_optimalValue [Nonempty α]
    (M : FiniteMDP σ α) (π : Policy σ α) :
    ∀ n x, horizonValue M π n x ≤ optimalValue M n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        horizonValue M π (n + 1) x =
            policyValueStep M π (horizonValue M π n) x := by
              rfl
        _ ≤ policyValueStep M π (optimalValue M n) x :=
            policyValueStep_mono M π (fun y => ih y) x
        _ ≤ optimalStep M (optimalValue M n) x :=
            policyValueStep_le_optimalStep M π (optimalValue M n) x
        _ = optimalValue M (n + 1) x := by
            rfl

/-!
## Finite-horizon policy optimality and incentive compatibility

Dynamic pricing and platform papers often phrase the driver-side result as
"truthful" or "accept-all" behavior being a best response.  The generic finite
MDP form is: a policy is incentive compatible at a horizon if no alternative
policy has larger value from any state.
-/

/-- Policy `π` weakly dominates policy `ρ` at a finite horizon. -/
def PolicyWeaklyDominatesAtHorizon
    (M : FiniteMDP σ α) (π ρ : Policy σ α) (n : ℕ) : Prop :=
  ∀ x, horizonValue M ρ n x ≤ horizonValue M π n x

/-- Finite-horizon incentive compatibility: no policy deviation improves value. -/
def IncentiveCompatibleAtHorizon
    (M : FiniteMDP σ α) (π : Policy σ α) (n : ℕ) : Prop :=
  ∀ ρ : Policy σ α, PolicyWeaklyDominatesAtHorizon M π ρ n

/-- A concrete finite-horizon profitable deviation from policy `π` to policy `ρ`. -/
def ProfitableDeviationAtHorizon
    (M : FiniteMDP σ α) (π ρ : Policy σ α) (n : ℕ) (x : σ) : Prop :=
  horizonValue M π n x < horizonValue M ρ n x

/-- A concrete profitable deviation refutes finite-horizon incentive compatibility. -/
theorem not_incentiveCompatibleAtHorizon_of_profitableDeviation
    (M : FiniteMDP σ α) (π ρ : Policy σ α) (n : ℕ) (x : σ)
    (hdev : ProfitableDeviationAtHorizon M π ρ n x) :
    ¬ IncentiveCompatibleAtHorizon M π n := by
  intro hIC
  exact not_le_of_gt hdev (hIC ρ x)

/-- A policy that attains the Bellman optimal value is finite-horizon IC. -/
theorem incentiveCompatibleAtHorizon_of_horizonValue_eq_optimalValue [Nonempty α]
    (M : FiniteMDP σ α) (π : Policy σ α) (n : ℕ)
    (hπ : ∀ x, horizonValue M π n x = optimalValue M n x) :
    IncentiveCompatibleAtHorizon M π n := by
  intro ρ x
  rw [hπ x]
  exact horizonValue_le_optimalValue M ρ n x

/--
If a deterministic policy is greedy with respect to the optimal continuation
value at every remaining horizon, then its finite-horizon value equals the
Bellman optimal value.
-/
theorem horizonValue_eq_optimalValue_of_greedy_optimalValue [Nonempty α]
    (M : FiniteMDP σ α) (choose : σ → α)
    (hgreedy : ∀ n, Greedy M choose (optimalValue M n)) :
    ∀ n x, horizonValue M (deterministicPolicy choose) n x = optimalValue M n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      have hfun : horizonValue M (deterministicPolicy choose) n = optimalValue M n := by
        exact funext ih
      calc
        horizonValue M (deterministicPolicy choose) (n + 1) x
            = policyValueStep M (deterministicPolicy choose)
                (horizonValue M (deterministicPolicy choose) n) x := by
              rfl
        _ = actionValue M (horizonValue M (deterministicPolicy choose) n) x (choose x) := by
              rw [policyValueStep_deterministic]
        _ = actionValue M (optimalValue M n) x (choose x) := by
              rw [hfun]
        _ = optimalStep M (optimalValue M n) x := hgreedy n x
        _ = optimalValue M (n + 1) x := by
              rfl

/-- A deterministic policy that is Bellman-greedy at every horizon is finite-horizon IC. -/
theorem incentiveCompatibleAtHorizon_of_greedy_optimalValue [Nonempty α]
    (M : FiniteMDP σ α) (choose : σ → α)
    (hgreedy : ∀ n, Greedy M choose (optimalValue M n)) (n : ℕ) :
    IncentiveCompatibleAtHorizon M (deterministicPolicy choose) n :=
  incentiveCompatibleAtHorizon_of_horizonValue_eq_optimalValue M
    (deterministicPolicy choose) n
    (horizonValue_eq_optimalValue_of_greedy_optimalValue M choose hgreedy n)

/-- State distribution at time `t` under initial law `μ0` and policy `π`. -/
noncomputable def stateDistribution
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (t : ℕ) : PMF σ :=
  FiniteMarkovKernel.iterate (controlledKernel M π) t μ0

@[simp] theorem stateDistribution_zero
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) :
    stateDistribution M π μ0 0 = μ0 := by
  rfl

@[simp] theorem stateDistribution_succ
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (t : ℕ) :
    stateDistribution M π μ0 (t + 1) =
      FiniteMarkovKernel.step (controlledKernel M π) (stateDistribution M π μ0 t) := by
  rfl

/-- Real mass of state `x` at time `t`. -/
noncomputable def stateMass
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (t : ℕ) (x : σ) : ℝ :=
  ((stateDistribution M π μ0 t) x).toReal

theorem stateMass_nonneg
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (t : ℕ) (x : σ) :
    0 ≤ stateMass M π μ0 t x := by
  exact ENNReal.toReal_nonneg

/-- Finite-horizon state occupancy mass, summed over `t : Fin T`. -/
noncomputable def occupancyMass
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (T : ℕ) (x : σ) : ℝ :=
  ∑ t : Fin T, stateMass M π μ0 t x

theorem occupancyMass_nonneg
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (T : ℕ) (x : σ) :
    0 ≤ occupancyMass M π μ0 T x := by
  unfold occupancyMass
  exact Finset.sum_nonneg (fun t _ => stateMass_nonneg M π μ0 t x)

/-- Finite-horizon state-action occupancy mass. -/
noncomputable def stateActionOccupancyMass
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (T : ℕ) (x : σ) (a : α) :
    ℝ :=
  ∑ t : Fin T, stateMass M π μ0 t x * actionProb π x a

theorem stateActionOccupancyMass_nonneg
    (M : FiniteMDP σ α) (π : Policy σ α) (μ0 : PMF σ) (T : ℕ) (x : σ) (a : α) :
    0 ≤ stateActionOccupancyMass M π μ0 T x a := by
  unfold stateActionOccupancyMass
  exact Finset.sum_nonneg (fun t _ =>
    mul_nonneg (stateMass_nonneg M π μ0 t x) (actionProb_nonneg π x a))

/-- Probability of a finite state path under the policy-induced kernel. -/
noncomputable def statePathProb
    (M : FiniteMDP σ α) (π : Policy σ α) : σ → List σ → ℝ
  | _, [] => 1
  | x, y :: rest =>
      FiniteMarkovKernel.transitionProb (controlledKernel M π) x y *
        statePathProb M π y rest

theorem statePathProb_nonneg
    (M : FiniteMDP σ α) (π : Policy σ α) :
    ∀ x path, 0 ≤ statePathProb M π x path
  | _, [] => by
      simp [statePathProb]
  | x, y :: rest => by
      simp [statePathProb]
      exact mul_nonneg
        (FiniteMarkovKernel.transitionProb_nonneg (controlledKernel M π) x y)
        (statePathProb_nonneg M π y rest)

end FiniteMDP

end AppliedModelingLib

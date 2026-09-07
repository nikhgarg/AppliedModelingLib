import AppliedModelingLib.Foundations.Probability.MDP

/-!
# Finite Support for Driver Surge Pricing

Auxiliary finite-MDP declarations for discrete dynamic-pricing sanity checks.
The source GN21 paper is continuous-time; these declarations are intentionally
kept separate from the continuous CTMC theorem ledger.
-/

open AppliedModelingLib

namespace GN21DriverSurgePricing

section FiniteSupport

variable {State Action : Type*}
variable [Fintype State] [DecidableEq State]
variable [Fintype Action] [DecidableEq Action]

/-- Finite approximation of a dynamic driver decision model. -/
abbrev FiniteDriverModel (State Action : Type*) := FiniteMDP State Action

/-- Finite-horizon driver IC in a discrete MDP approximation. -/
abbrev finiteHorizonDriverIC
    (M : FiniteDriverModel State Action) (π : FiniteMDP.Policy State Action)
    (n : ℕ) : Prop := FiniteMDP.IncentiveCompatibleAtHorizon M π n

/--
Auxiliary finite dynamic-pricing theorem: a deterministic policy that is
Bellman-greedy at every remaining horizon is finite-horizon IC.
-/
theorem paper_aux_finite_dynamic_pricing_ic_of_greedy
    [Nonempty Action]
    (M : FiniteDriverModel State Action) (choose : State → Action)
    (hgreedy : ∀ n, FiniteMDP.Greedy M choose (FiniteMDP.optimalValue M n))
    (n : ℕ) :
    finiteHorizonDriverIC M (FiniteMDP.deterministicPolicy choose) n :=
   FiniteMDP.incentiveCompatibleAtHorizon_of_greedy_optimalValue M choose
    hgreedy n

/--
Auxiliary finite dynamic-pricing theorem: an explicit better deviation refutes
finite-horizon IC.
-/
theorem paper_aux_finite_dynamic_pricing_not_ic_of_profitable_deviation
    (M : FiniteDriverModel State Action) (π ρ : FiniteMDP.Policy State Action)
    (n : ℕ) (x : State)
    (hdev : FiniteMDP.ProfitableDeviationAtHorizon M π ρ n x) :
    ¬ finiteHorizonDriverIC M π n :=
   FiniteMDP.not_incentiveCompatibleAtHorizon_of_profitableDeviation
    M π ρ n x hdev

end FiniteSupport

end GN21DriverSurgePricing

import AppliedModelingLib.Foundations.Probability.MDP

/-!
# Occupancy-weighted preference features

Occupancy-weighted state-action features are the finite-MDP bridge from policy
rollouts to trajectory scores used by linear preference models.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- The state-action occupancy-weighted total of a finite-horizon feature. -/
noncomputable def preferenceOccupancyFeatureMass
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    (initial : PMF State) (horizon : ℕ) (feature : State → Action → ℝ) : ℝ :=
  ∑ state : State, ∑ action : Action,
    M.stateActionOccupancyMass policy initial horizon state action * feature state action

/-- Nonnegative features have nonnegative occupancy-weighted total mass. -/
theorem preferenceOccupancyFeatureMass_nonneg
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    (initial : PMF State) (horizon : ℕ) (feature : State → Action → ℝ)
    (hfeature : ∀ state action, 0 ≤ feature state action) :
    0 ≤ preferenceOccupancyFeatureMass M policy initial horizon feature := by
  unfold preferenceOccupancyFeatureMass
  refine Finset.sum_nonneg fun state _ => ?_
  refine Finset.sum_nonneg fun action _ => ?_
  exact mul_nonneg
    (FiniteMDP.stateActionOccupancyMass_nonneg M policy initial horizon state action)
    (hfeature state action)

/--
Occupancy evaluation is linear in a scalar reward parameter. This is the
one-dimensional specialization of linear reward parametrization.
-/
theorem preferenceOccupancyFeatureMass_scale
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    (initial : PMF State) (horizon : ℕ) (feature : State → Action → ℝ) (parameter : ℝ) :
    preferenceOccupancyFeatureMass M policy initial horizon
        (fun state action => parameter * feature state action) =
      parameter * preferenceOccupancyFeatureMass M policy initial horizon feature := by
  unfold preferenceOccupancyFeatureMass
  calc
    ∑ state : State, ∑ action : Action,
        M.stateActionOccupancyMass policy initial horizon state action *
          (parameter * feature state action) =
      ∑ state : State, ∑ action : Action,
        parameter *
          (M.stateActionOccupancyMass policy initial horizon state action * feature state action) := by
        apply Finset.sum_congr rfl
        intro state _
        apply Finset.sum_congr rfl
        intro action _
        ring
    _ = ∑ state : State,
        parameter * ∑ action : Action,
          M.stateActionOccupancyMass policy initial horizon state action * feature state action := by
        apply Finset.sum_congr rfl
        intro state _
        rw [Finset.mul_sum]
    _ = parameter * ∑ state : State, ∑ action : Action,
          M.stateActionOccupancyMass policy initial horizon state action * feature state action := by
        rw [Finset.mul_sum]

/-- Occupancy evaluation commutes with a finite sum of state-action features. -/
theorem preferenceOccupancyFeatureMass_sum
    {State Action Feature : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Fintype Feature]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    (initial : PMF State) (horizon : ℕ)
    (feature : Feature → State → Action → ℝ) :
    preferenceOccupancyFeatureMass M policy initial horizon
        (fun state action => ∑ index : Feature, feature index state action) =
      ∑ index : Feature,
        preferenceOccupancyFeatureMass M policy initial horizon (feature index) := by
  unfold preferenceOccupancyFeatureMass
  calc
    ∑ state : State, ∑ action : Action,
        M.stateActionOccupancyMass policy initial horizon state action *
          (∑ index : Feature, feature index state action) =
      ∑ state : State, ∑ action : Action, ∑ index : Feature,
        M.stateActionOccupancyMass policy initial horizon state action *
          feature index state action := by
        apply Finset.sum_congr rfl
        intro state _
        apply Finset.sum_congr rfl
        intro action _
        rw [Finset.mul_sum]
    _ = ∑ state : State, ∑ index : Feature, ∑ action : Action,
        M.stateActionOccupancyMass policy initial horizon state action *
          feature index state action := by
        apply Finset.sum_congr rfl
        intro state _
        rw [Finset.sum_comm]
    _ = ∑ index : Feature, ∑ state : State, ∑ action : Action,
        M.stateActionOccupancyMass policy initial horizon state action *
          feature index state action := by
        rw [Finset.sum_comm]

/--
Finite-coordinate linear reward evaluation is the parameter-weighted sum of
the corresponding occupancy feature masses.
-/
theorem preferenceOccupancyFeatureMass_linear
    {State Action Feature : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Fintype Feature]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    (initial : PMF State) (horizon : ℕ)
    (feature : State → Action → Feature → ℝ) (parameter : Feature → ℝ) :
    preferenceOccupancyFeatureMass M policy initial horizon
        (fun state action => ∑ index : Feature,
          parameter index * feature state action index) =
      ∑ index : Feature, parameter index *
        preferenceOccupancyFeatureMass M policy initial horizon
          (fun state action => feature state action index) := by
  calc
    preferenceOccupancyFeatureMass M policy initial horizon
        (fun state action => ∑ index : Feature,
          parameter index * feature state action index) =
      ∑ index : Feature,
        preferenceOccupancyFeatureMass M policy initial horizon
          (fun state action => parameter index * feature state action index) :=
      preferenceOccupancyFeatureMass_sum M policy initial horizon
        (fun index state action => parameter index * feature state action index)
    _ = ∑ index : Feature, parameter index *
        preferenceOccupancyFeatureMass M policy initial horizon
          (fun state action => feature state action index) := by
      apply Finset.sum_congr rfl
      intro index _
      exact preferenceOccupancyFeatureMass_scale M policy initial horizon
        (fun state action => feature state action index) (parameter index)

end PreferenceRL

end AppliedModelingLib

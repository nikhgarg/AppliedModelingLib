import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

namespace AppliedModelingLib

open scoped BigOperators

/-!
# Finite-class marginal-externality pricing for queues

This module records the calculus identity behind a Pigouvian price in a finite
collection of congestible classes.  The result is deliberately independent of
any particular queue: a queueing model supplies its class waiting-time map and
the required differentiability facts.
-/

/-- Net value at a finite vector of class flow levels: gross value less than
class delay cost times Little's-law population `xᵢ Wᵢ(x)`. -/
noncomputable def finiteDelayNetValue
    {Class : Type*} [Fintype Class]
    (value : Class → ℝ → ℝ) (delayCost : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ) (x : Class → ℝ) : ℝ :=
  ∑ j, (value j (x j) - delayCost j * x j * waitingTime j x)

/-- The delay externality caused by an infinitesimal increase in the flow of
one class, given the partial derivatives of every class's waiting time. -/
noncomputable def finiteMarginalExternalityPrice
    {Class : Type*} [Fintype Class]
    (delayCost flow partialWaiting : Class → ℝ) : ℝ :=
  ∑ j, delayCost j * flow j * partialWaiting j

/-- The directional derivative of finite-class net value when only the flow of
one class is varied.  This calculation is useful independently of whether the
flow vector is optimal. -/
theorem hasDerivAt_finiteDelayNetValue_update
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (value : Class → ℝ → ℝ) (delayCost : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ)
    (flow : Class → ℝ) (i : Class) (marginalValue : ℝ)
    (partialWaiting : Class → ℝ)
    (hvalue : HasDerivAt (value i) marginalValue (flow i))
    (hwaiting : ∀ j,
      HasDerivAt
        (fun t => waitingTime j (Function.update flow i t))
        (partialWaiting j) (flow i)) :
    HasDerivAt
      (fun t => finiteDelayNetValue value delayCost waitingTime
        (Function.update flow i t))
      (∑ j : Class,
        ((if j = i then marginalValue else 0) -
          delayCost j *
            ((if j = i then 1 else 0) * waitingTime j flow +
              flow j * partialWaiting j)))
      (flow i) := by
  classical
  have hvalueAll : ∀ j : Class,
      HasDerivAt
        (fun t => value j (Function.update flow i t j))
        (if j = i then marginalValue else 0) (flow i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hvalue
    · simpa [hji, Function.update_of_ne hji] using
        (hasDerivAt_const (x := flow i) (c := value j (flow j)))
  have hflow : ∀ j : Class,
      HasDerivAt
        (fun t => Function.update flow i t j)
        (if j = i then 1 else 0) (flow i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (hasDerivAt_id (x := flow i))
    · simpa [hji, Function.update_of_ne hji] using
        (hasDerivAt_const (x := flow i) (c := flow j))
  have hdelay : ∀ j : Class,
      HasDerivAt
        (fun t =>
          delayCost j * Function.update flow i t j *
            waitingTime j (Function.update flow i t))
        (delayCost j *
          ((if j = i then 1 else 0) * waitingTime j flow +
            flow j * partialWaiting j))
        (flow i) := by
    intro j
    simpa [Function.update_eq_self, mul_assoc, mul_left_comm, mul_comm] using
      ((hflow j).mul (hwaiting j)).const_mul (delayCost j)
  have hterm : ∀ j : Class,
      HasDerivAt
        (fun t =>
          value j (Function.update flow i t j) -
            delayCost j * Function.update flow i t j *
              waitingTime j (Function.update flow i t))
        ((if j = i then marginalValue else 0) -
          delayCost j *
            ((if j = i then 1 else 0) * waitingTime j flow +
              flow j * partialWaiting j))
        (flow i) := by
    intro j
    exact (hvalueAll j).sub (hdelay j)
  change HasDerivAt
    (fun t => ∑ j : Class,
      (value j (Function.update flow i t j) -
        delayCost j * Function.update flow i t j *
          waitingTime j (Function.update flow i t)))
    _ (flow i)
  convert (HasDerivAt.sum (u := Finset.univ) fun j _ => hterm j) using 1
  ext t
  simp only [Finset.sum_apply]

/--
At an interior stationary point of finite-class net value, the marginal value
of class `i` equals its private delay cost plus the marginal delay externality
on every class.  This is a purely differential identity; no queueing dynamics
or priority discipline is built into the statement.
-/
theorem marginalValue_eq_privateDelay_add_externality
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (value : Class → ℝ → ℝ) (delayCost : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ)
    (flow : Class → ℝ) (i : Class) (marginalValue : ℝ)
    (partialWaiting : Class → ℝ)
    (hvalue : HasDerivAt (value i) marginalValue (flow i))
    (hwaiting : ∀ j,
      HasDerivAt
        (fun t => waitingTime j (Function.update flow i t))
        (partialWaiting j) (flow i))
    (hstationary :
      HasDerivAt
        (fun t => finiteDelayNetValue value delayCost waitingTime
          (Function.update flow i t))
        0 (flow i)) :
    marginalValue =
      delayCost i * waitingTime i flow +
        finiteMarginalExternalityPrice delayCost flow partialWaiting := by
  classical
  have hvalueAll : ∀ j : Class,
      HasDerivAt
        (fun t => value j (Function.update flow i t j))
        (if j = i then marginalValue else 0) (flow i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hvalue
    · simpa [hji, Function.update_of_ne hji] using
        (hasDerivAt_const (x := flow i) (c := value j (flow j)))
  have hflow : ∀ j : Class,
      HasDerivAt
        (fun t => Function.update flow i t j)
        (if j = i then 1 else 0) (flow i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (hasDerivAt_id (x := flow i))
    · simpa [hji, Function.update_of_ne hji] using
        (hasDerivAt_const (x := flow i) (c := flow j))
  have hdelay : ∀ j : Class,
      HasDerivAt
        (fun t =>
          delayCost j * Function.update flow i t j *
            waitingTime j (Function.update flow i t))
        (delayCost j *
          ((if j = i then 1 else 0) * waitingTime j flow +
            flow j * partialWaiting j))
        (flow i) := by
    intro j
    simpa [Function.update_eq_self, mul_assoc, mul_left_comm, mul_comm] using
      ((hflow j).mul (hwaiting j)).const_mul (delayCost j)
  have hterm : ∀ j : Class,
      HasDerivAt
        (fun t =>
          value j (Function.update flow i t j) -
            delayCost j * Function.update flow i t j *
              waitingTime j (Function.update flow i t))
        ((if j = i then marginalValue else 0) -
          delayCost j *
            ((if j = i then 1 else 0) * waitingTime j flow +
              flow j * partialWaiting j))
        (flow i) := by
    intro j
    exact (hvalueAll j).sub (hdelay j)
  have hobjective :
      HasDerivAt
        (fun t => finiteDelayNetValue value delayCost waitingTime
          (Function.update flow i t))
        (∑ j : Class,
          ((if j = i then marginalValue else 0) -
            delayCost j *
              ((if j = i then 1 else 0) * waitingTime j flow +
                flow j * partialWaiting j)))
        (flow i) := by
    change HasDerivAt
      (fun t => ∑ j : Class,
        (value j (Function.update flow i t j) -
          delayCost j * Function.update flow i t j *
            waitingTime j (Function.update flow i t)))
      _ (flow i)
    convert (HasDerivAt.sum (u := Finset.univ) fun j _ => hterm j) using 1
    ext t
    simp only [Finset.sum_apply]
  have hsum :
      (∑ j : Class,
        ((if j = i then marginalValue else 0) -
          delayCost j *
            ((if j = i then 1 else 0) * waitingTime j flow +
              flow j * partialWaiting j))) = 0 := by
    calc
      _ = deriv
          (fun t => finiteDelayNetValue value delayCost waitingTime
            (Function.update flow i t)) (flow i) := hobjective.deriv.symm
      _ = 0 := hstationary.deriv
  have hfirst :
      marginalValue =
        ∑ j : Class,
          delayCost j *
            ((if j = i then 1 else 0) * waitingTime j flow +
              flow j * partialWaiting j) := by
    rw [Finset.sum_sub_distrib] at hsum
    have hvalueSum : (∑ j : Class, if j = i then marginalValue else 0) =
        marginalValue := by simp
    rw [hvalueSum] at hsum
    linarith
  have hprivate :
      (∑ j : Class,
        delayCost j * (if j = i then 1 else 0) * waitingTime j flow) =
        delayCost i * waitingTime i flow := by
    calc
      _ = ∑ j : Class,
          if j = i then delayCost i * waitingTime i flow else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp
            · simp [hji]
      _ = delayCost i * waitingTime i flow := by simp
  calc
    marginalValue =
        ∑ j : Class,
          delayCost j *
            ((if j = i then 1 else 0) * waitingTime j flow +
              flow j * partialWaiting j) := hfirst
    _ = (∑ j : Class,
          delayCost j * (if j = i then 1 else 0) * waitingTime j flow) +
          ∑ j : Class, delayCost j * flow j * partialWaiting j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = delayCost i * waitingTime i flow +
        finiteMarginalExternalityPrice delayCost flow partialWaiting := by
      rw [hprivate]
      rfl

/-- A local optimum supplies the zero directional derivative required by
`marginalValue_eq_privateDelay_add_externality`. -/
theorem marginalValue_eq_privateDelay_add_externality_of_isLocalMax
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (value : Class → ℝ → ℝ) (delayCost : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ)
    (flow : Class → ℝ) (i : Class) (marginalValue : ℝ)
    (partialWaiting : Class → ℝ)
    (hvalue : HasDerivAt (value i) marginalValue (flow i))
    (hwaiting : ∀ j,
      HasDerivAt
        (fun t => waitingTime j (Function.update flow i t))
        (partialWaiting j) (flow i))
    (hmax : IsLocalMax
      (fun t => finiteDelayNetValue value delayCost waitingTime
        (Function.update flow i t))
      (flow i)) :
    marginalValue =
      delayCost i * waitingTime i flow +
        finiteMarginalExternalityPrice delayCost flow partialWaiting := by
  let directionalDerivative : ℝ :=
    ∑ j : Class,
      ((if j = i then marginalValue else 0) -
        delayCost j *
          ((if j = i then 1 else 0) * waitingTime j flow +
            flow j * partialWaiting j))
  have hobjective :
      HasDerivAt
        (fun t => finiteDelayNetValue value delayCost waitingTime
          (Function.update flow i t))
        directionalDerivative (flow i) := by
    exact hasDerivAt_finiteDelayNetValue_update
      value delayCost waitingTime flow i marginalValue partialWaiting
      hvalue hwaiting
  have hzero : directionalDerivative = 0 :=
    hmax.hasDerivAt_eq_zero hobjective
  have hstationary :
      HasDerivAt
        (fun t => finiteDelayNetValue value delayCost waitingTime
          (Function.update flow i t))
        0 (flow i) := by
    simpa [hzero] using hobjective
  exact marginalValue_eq_privateDelay_add_externality
    value delayCost waitingTime flow i marginalValue partialWaiting
    hvalue hwaiting hstationary

end AppliedModelingLib

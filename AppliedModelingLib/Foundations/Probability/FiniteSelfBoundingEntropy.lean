import AppliedModelingLib.Foundations.Probability.FiniteEntropy
import AppliedModelingLib.Foundations.Probability.FiniteSelfBounding

/-!
# Entropy bounds from finite self-bounding replacement drops

This is the local bridge in Maurer's self-bounding argument.  It turns the
literal finite replacement infimum into the one-coordinate entropy estimate;
finite-product tensorization is deliberately left to the subsequent layer.
-/

namespace AppliedModelingLib

/-- At one coordinate, the exponential-weight entropy is controlled by the
square of the literal replacement drop.  The replacement infimum is invariant
under first changing that same coordinate, so the bound is expressed at the
resampled vector itself. -/
theorem pmfFunctionalEntropy_exp_update_le_half_sq_replacementDrop
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (objective : (Fin n → α) → ℝ)
    (sample : Fin n → α) (coordinate : Fin n) (parameter : ℝ)
    (hparameter : 0 ≤ parameter) :
    pmfFunctionalEntropy law (fun value =>
      Real.exp (parameter * objective (Function.update sample coordinate value))) ≤
      (parameter ^ 2 / 2) *
        pmfExp law (fun value =>
          Real.exp (parameter * objective (Function.update sample coordinate value)) *
            (finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) ^ 2) := by
  let lower : ℝ := finiteCoordinateReplacementInf objective sample coordinate
  have hlower : ∀ value : α,
      lower ≤ objective (Function.update sample coordinate value) := by
    intro value
    exact finiteCoordinateReplacementInf_le_replacement objective sample coordinate value
  calc
    pmfFunctionalEntropy law (fun value =>
        Real.exp (parameter * objective (Function.update sample coordinate value))) ≤
        (parameter ^ 2 / 2) *
          pmfExp law (fun value =>
            Real.exp (parameter * objective (Function.update sample coordinate value)) *
              (objective (Function.update sample coordinate value) - lower) ^ 2) :=
        pmfFunctionalEntropy_exp_le_half_sq_drop law
          (fun value => objective (Function.update sample coordinate value)) parameter lower
          hparameter hlower
    _ = (parameter ^ 2 / 2) *
          pmfExp law (fun value =>
            Real.exp (parameter * objective (Function.update sample coordinate value)) *
              (finiteCoordinateReplacementDrop objective
                (Function.update sample coordinate value) coordinate) ^ 2) := by
          congr 1
          apply pmfExp_congr
          intro value
          unfold finiteCoordinateReplacementDrop
          rw [finiteCoordinateReplacementInf_update]

/-- Averaging the one-coordinate entropy bound over an iid product and then
resampling that coordinate produces the corresponding product expectation.
This is the exact local contribution used in a product-tensorization proof. -/
theorem pmfExp_pmfProduct_coordinateEntropy_exp_le_half_sq_replacementDrop
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (objective : (Fin n → α) → ℝ)
    (coordinate : Fin n) (parameter : ℝ) (hparameter : 0 ≤ parameter) :
    pmfExp (pmfProduct (Fin n) α law) (fun sample =>
      pmfFunctionalEntropy law (fun value =>
        Real.exp (parameter * objective (Function.update sample coordinate value)))) ≤
      (parameter ^ 2 / 2) *
        pmfExp (pmfProduct (Fin n) α law) (fun sample =>
          Real.exp (parameter * objective sample) *
            (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) := by
  let resampledIntegrand : (Fin n → α) → α → ℝ := fun sample value =>
    Real.exp (parameter * objective (Function.update sample coordinate value)) *
      (finiteCoordinateReplacementDrop objective
        (Function.update sample coordinate value) coordinate) ^ 2
  have hpoint : ∀ sample : Fin n → α,
      pmfFunctionalEntropy law (fun value =>
        Real.exp (parameter * objective (Function.update sample coordinate value))) ≤
        (parameter ^ 2 / 2) * pmfExp law (resampledIntegrand sample) := by
    intro sample
    exact pmfFunctionalEntropy_exp_update_le_half_sq_replacementDrop
      law objective sample coordinate parameter hparameter
  calc
    pmfExp (pmfProduct (Fin n) α law) (fun sample =>
        pmfFunctionalEntropy law (fun value =>
          Real.exp (parameter * objective (Function.update sample coordinate value)))) ≤
        pmfExp (pmfProduct (Fin n) α law) (fun sample =>
          (parameter ^ 2 / 2) * pmfExp law (resampledIntegrand sample)) := by
          apply pmfExp_le_pmfExp_of_forall_le
          exact hpoint
    _ = (parameter ^ 2 / 2) *
          pmfPairExp (pmfProduct (Fin n) α law) law resampledIntegrand := by
          unfold pmfPairExp
          rw [pmfExp_const_mul]
    _ = (parameter ^ 2 / 2) *
          pmfExp (pmfProduct (Fin n) α law) (fun sample =>
            Real.exp (parameter * objective sample) *
              (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) := by
          congr 1
          change pmfPairExp (pmfProduct (Fin n) α law) law
            (fun sample value =>
              Real.exp (parameter * objective (Function.update sample coordinate value)) *
                (finiteCoordinateReplacementDrop objective
                  (Function.update sample coordinate value) coordinate) ^ 2) = _
          exact pmfPairExp_pmfProduct_update_eq_pmfExp law
            (fun sample =>
              Real.exp (parameter * objective sample) *
                (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) coordinate

end AppliedModelingLib

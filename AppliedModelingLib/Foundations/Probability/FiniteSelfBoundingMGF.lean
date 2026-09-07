import AppliedModelingLib.Foundations.Probability.FiniteEntropyTensorization
import AppliedModelingLib.Foundations.Probability.FiniteSelfBoundingEntropy

/-!
# Product entropy and finite self-bounding exponential moments

Maurer's self-bounding proof has two logically distinct ingredients: a
finite-product entropy tensorization theorem and the local replacement-drop
bound.  This file combines the checked finite tensorization theorem for
exponential weights with the literal replacement-drop argument.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The finite-product entropy tensorization inequality for an iid PMF.
Its right side is the sum of literal one-coordinate conditional entropies. -/
def FiniteProductEntropyTensorizes
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) (n : ℕ) : Prop :=
  ∀ weight : (Fin n → α) → ℝ,
    pmfFunctionalEntropy (pmfProduct (Fin n) α law) weight ≤
      pmfExp (pmfProduct (Fin n) α law) (fun sample =>
        ∑ coordinate : Fin n,
          pmfFunctionalEntropy law (fun value =>
            weight (Function.update sample coordinate value)))

/-- The empty finite product has zero functional entropy and therefore
satisfies tensorization. -/
theorem finiteProductEntropyTensorizes_zero
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) :
    FiniteProductEntropyTensorizes law 0 := by
  intro weight
  let emptySample : Fin 0 → α := Fin.elim0
  have hconstant : ∀ sample : Fin 0 → α, weight sample = weight emptySample := by
    intro sample
    congr
    exact Subsingleton.elim _ _
  have hfirst :
      pmfExp (pmfProduct (Fin 0) α law)
        (fun sample => weight sample * Real.log (weight sample)) =
        weight emptySample * Real.log (weight emptySample) := by
    calc
      pmfExp (pmfProduct (Fin 0) α law)
          (fun sample => weight sample * Real.log (weight sample)) =
          pmfExp (pmfProduct (Fin 0) α law)
            (fun _sample => weight emptySample * Real.log (weight emptySample)) := by
            apply pmfExp_congr
            intro sample
            rw [hconstant sample]
      _ = weight emptySample * Real.log (weight emptySample) := pmfExp_const _ _
  have hmean :
      pmfExp (pmfProduct (Fin 0) α law) weight = weight emptySample := by
    calc
      pmfExp (pmfProduct (Fin 0) α law) weight =
          pmfExp (pmfProduct (Fin 0) α law) (fun _sample => weight emptySample) := by
            apply pmfExp_congr
            intro sample
            exact hconstant sample
      _ = weight emptySample := pmfExp_const _ _
  unfold pmfFunctionalEntropy
  rw [hfirst, hmean]
  simp

/-- A one-coordinate iid product satisfies tensorization exactly: every
function on `Fin 1 → α` is determined by its only coordinate. -/
theorem finiteProductEntropyTensorizes_one
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) :
    FiniteProductEntropyTensorizes law 1 := by
  intro weight
  let scalarWeight : α → ℝ := fun value => weight (fun _index : Fin 1 => value)
  have hweight (sample : Fin 1 → α) : weight sample = scalarWeight (sample 0) := by
    unfold scalarWeight
    congr
    funext index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    rfl
  have hupdate (sample : Fin 1 → α) (value : α) :
      weight (Function.update sample 0 value) = scalarWeight value := by
    unfold scalarWeight
    congr
    funext index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    simp
  have hfirst :
      pmfExp (pmfProduct (Fin 1) α law)
        (fun sample => weight sample * Real.log (weight sample)) =
        pmfExp law (fun value => scalarWeight value * Real.log (scalarWeight value)) := by
    calc
      pmfExp (pmfProduct (Fin 1) α law)
          (fun sample => weight sample * Real.log (weight sample)) =
          pmfExp (pmfProduct (Fin 1) α law)
            (fun sample => scalarWeight (sample 0) * Real.log (scalarWeight (sample 0))) := by
            apply pmfExp_congr
            intro sample
            rw [hweight sample]
      _ = pmfExp law (fun value => scalarWeight value * Real.log (scalarWeight value)) :=
          pmfExp_pmfProduct_eval law 0
            (fun value => scalarWeight value * Real.log (scalarWeight value))
  have hmean :
      pmfExp (pmfProduct (Fin 1) α law) weight = pmfExp law scalarWeight := by
    calc
      pmfExp (pmfProduct (Fin 1) α law) weight =
          pmfExp (pmfProduct (Fin 1) α law) (fun sample => scalarWeight (sample 0)) := by
            apply pmfExp_congr
            intro sample
            exact hweight sample
      _ = pmfExp law scalarWeight := pmfExp_pmfProduct_eval law 0 scalarWeight
  have hright :
      pmfExp (pmfProduct (Fin 1) α law) (fun sample =>
        ∑ coordinate : Fin 1,
          pmfFunctionalEntropy law (fun value =>
            weight (Function.update sample coordinate value))) =
        pmfFunctionalEntropy law scalarWeight := by
    calc
      pmfExp (pmfProduct (Fin 1) α law) (fun sample =>
          ∑ coordinate : Fin 1,
            pmfFunctionalEntropy law (fun value =>
              weight (Function.update sample coordinate value))) =
          pmfExp (pmfProduct (Fin 1) α law) (fun sample =>
            pmfFunctionalEntropy law (fun value =>
              weight (Function.update sample 0 value))) := by
            apply pmfExp_congr
            intro sample
            rw [Fin.sum_univ_one]
      _ = pmfExp (pmfProduct (Fin 1) α law) (fun _sample =>
            pmfFunctionalEntropy law scalarWeight) := by
            apply pmfExp_congr
            intro sample
            congr 1
            funext value
            rw [hupdate sample value]
      _ = pmfFunctionalEntropy law scalarWeight := pmfExp_const _ _
  change pmfFunctionalEntropy (pmfProduct (Fin 1) α law) weight ≤ _
  rw [hright]
  unfold pmfFunctionalEntropy
  rw [hfirst, hmean]

/-- Given the finite-product entropy tensorization inequality, the literal
self-bounding replacement conditions control the entropy of the exponential
weight.  This is the source's entropy inequality before its one-dimensional
Herbst integration step. -/
theorem FiniteSelfBounding.entropy_exp_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hparameter : 0 ≤ parameter) :
    pmfFunctionalEntropy (pmfProduct (Fin n) α law)
        (fun sample => Real.exp (parameter * objective sample)) ≤
      (parameter ^ 2 / 2) * scale *
        pmfExp (pmfProduct (Fin n) α law)
          (fun sample => Real.exp (parameter * objective sample) * objective sample) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let coordinateContribution : Fin n → (Fin n → α) → ℝ := fun coordinate sample =>
    pmfFunctionalEntropy law (fun value =>
      Real.exp (parameter * objective (Function.update sample coordinate value)))
  let resampledEnergy : Fin n → (Fin n → α) → ℝ := fun coordinate sample =>
    Real.exp (parameter * objective sample) *
      (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2
  have hcoordinate (coordinate : Fin n) :
      pmfExp productLaw (coordinateContribution coordinate) ≤
        (parameter ^ 2 / 2) * pmfExp productLaw (resampledEnergy coordinate) := by
    exact pmfExp_pmfProduct_coordinateEntropy_exp_le_half_sq_replacementDrop
      law objective coordinate parameter hparameter
  have hsum_coordinate :
      (∑ coordinate : Fin n, pmfExp productLaw (coordinateContribution coordinate)) ≤
        ∑ coordinate : Fin n,
          (parameter ^ 2 / 2) * pmfExp productLaw (resampledEnergy coordinate) := by
    exact Finset.sum_le_sum fun coordinate _ => hcoordinate coordinate
  have henergy_point (sample : Fin n → α) :
      (∑ coordinate : Fin n, resampledEnergy coordinate sample) ≤
        Real.exp (parameter * objective sample) * (scale * objective sample) := by
    dsimp [resampledEnergy]
    calc
      (∑ coordinate : Fin n,
          Real.exp (parameter * objective sample) *
            (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) =
          Real.exp (parameter * objective sample) *
            ∑ coordinate : Fin n,
              (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (parameter * objective sample) * (scale * objective sample) := by
            gcongr
            exact hself.sum_sq_drop_le sample
  have henergy_mean :
      pmfExp productLaw (fun sample => ∑ coordinate : Fin n,
          resampledEnergy coordinate sample) ≤
        pmfExp productLaw (fun sample =>
          Real.exp (parameter * objective sample) * (scale * objective sample)) := by
    apply pmfExp_le_pmfExp_of_forall_le
    exact henergy_point
  have hsum_resampled :
      (∑ coordinate : Fin n, pmfExp productLaw (resampledEnergy coordinate)) ≤
        pmfExp productLaw (fun sample =>
          Real.exp (parameter * objective sample) * (scale * objective sample)) := by
    rw [← pmfExp_univ_sum]
    exact henergy_mean
  have hparameter_sq_nonneg : 0 ≤ parameter ^ 2 / 2 := by positivity
  calc
    pmfFunctionalEntropy productLaw
        (fun sample => Real.exp (parameter * objective sample)) ≤
        pmfExp productLaw (fun sample =>
          ∑ coordinate : Fin n, coordinateContribution coordinate sample) := by
          exact finiteProductEntropyTensorizesExp_fin law n
            (fun sample => parameter * objective sample)
    _ = ∑ coordinate : Fin n,
          pmfExp productLaw (coordinateContribution coordinate) :=
        pmfExp_univ_sum productLaw coordinateContribution
    _ ≤ ∑ coordinate : Fin n,
          (parameter ^ 2 / 2) * pmfExp productLaw (resampledEnergy coordinate) :=
        hsum_coordinate
    _ = (parameter ^ 2 / 2) *
          ∑ coordinate : Fin n, pmfExp productLaw (resampledEnergy coordinate) := by
          rw [Finset.mul_sum]
    _ ≤ (parameter ^ 2 / 2) *
          pmfExp productLaw (fun sample =>
            Real.exp (parameter * objective sample) * (scale * objective sample)) := by
          gcongr
    _ = (parameter ^ 2 / 2) * scale *
          pmfExp productLaw (fun sample =>
            Real.exp (parameter * objective sample) * objective sample) := by
          rw [← pmfExp_const_mul]
          calc
            pmfExp productLaw (fun sample =>
                (parameter ^ 2 / 2) *
                  (Real.exp (parameter * objective sample) * (scale * objective sample))) =
                pmfExp productLaw (fun sample =>
                  ((parameter ^ 2 / 2) * scale) *
                    (Real.exp (parameter * objective sample) * objective sample)) := by
                    apply pmfExp_congr
                    intro sample
                    ring
            _ = ((parameter ^ 2 / 2) * scale) *
                  pmfExp productLaw (fun sample =>
                    Real.exp (parameter * objective sample) * objective sample) := by
                    rw [pmfExp_const_mul]
            _ = (parameter ^ 2 / 2) * scale *
                  pmfExp productLaw (fun sample =>
                    Real.exp (parameter * objective sample) * objective sample) := by
                    ring

/-- The functional entropy of an exponential finite-PMF weight is the
standard log-MGF differential numerator. -/
theorem pmfFunctionalEntropy_exp_eq_finiteLogMGF_numerator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (objective : Ω → ℝ) (parameter : ℝ) :
    pmfFunctionalEntropy law (fun outcome => Real.exp (parameter * objective outcome)) =
      parameter * (∑ outcome : Ω,
        (law outcome).toReal *
          (Real.exp (parameter * objective outcome) * objective outcome)) -
        Probability.finiteMGF law objective parameter *
          Probability.finiteLogMGF law objective parameter := by
  unfold pmfFunctionalEntropy pmfExp Probability.finiteMGF Probability.finiteLogMGF
  simp_rw [Real.log_exp]
  simp only [Probability.finiteMGF]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

/-- The checked product entropy inequality yields the exact differential
inequality for the finite log-MGF used in Maurer's Herbst step.  This is an
analytic bridge, not yet the integrated tail bound. -/
theorem FiniteSelfBounding.finiteLogMGF_differential_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hparameter : 0 ≤ parameter) :
    (parameter - parameter ^ 2 / 2 * scale) *
        ((∑ sample : Fin n → α,
          (pmfProduct (Fin n) α law sample).toReal *
            (Real.exp (parameter * objective sample) * objective sample)) /
          Probability.finiteMGF (pmfProduct (Fin n) α law) objective parameter) ≤
      Probability.finiteLogMGF (pmfProduct (Fin n) α law) objective parameter := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let numerator : ℝ := ∑ sample : Fin n → α,
    (productLaw sample).toReal *
      (Real.exp (parameter * objective sample) * objective sample)
  let partition : ℝ := Probability.finiteMGF productLaw objective parameter
  have hpartition_pos : 0 < partition :=
    Probability.finiteMGF_pos productLaw objective parameter
  have hentropy :
      pmfFunctionalEntropy productLaw
          (fun sample => Real.exp (parameter * objective sample)) ≤
        (parameter ^ 2 / 2) * scale * numerator := by
    simpa only [productLaw, numerator, pmfExp] using
      hself.entropy_exp_le (law := law) hparameter
  rw [pmfFunctionalEntropy_exp_eq_finiteLogMGF_numerator] at hentropy
  change (parameter - parameter ^ 2 / 2 * scale) * (numerator / partition) ≤
    Probability.finiteLogMGF productLaw objective parameter
  calc
    (parameter - parameter ^ 2 / 2 * scale) * (numerator / partition) =
        ((parameter - parameter ^ 2 / 2 * scale) * numerator) / partition := by ring
    _ ≤ Probability.finiteLogMGF productLaw objective parameter := by
      apply (div_le_iff₀ hpartition_pos).2
      have hbound :
          (parameter - parameter ^ 2 / 2 * scale) * numerator ≤
            partition * Probability.finiteLogMGF productLaw objective parameter := by
        nlinarith [hentropy]
      simpa [mul_comm] using hbound

end AppliedModelingLib

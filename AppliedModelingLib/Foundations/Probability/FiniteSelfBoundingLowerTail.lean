import AppliedModelingLib.Foundations.Probability.FiniteEntropy
import AppliedModelingLib.Foundations.Probability.FiniteSelfBounding
import AppliedModelingLib.Foundations.Probability.FiniteEntropyTensorization
import AppliedModelingLib.Foundations.Probability.FiniteSelfBoundingMGF
import AppliedModelingLib.Foundations.Probability.FiniteHerbst
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Negative-parameter finite entropy bounds for self-bounding functions

This is the lower-tail counterpart to the positive-parameter entropy route.
It starts with the one-variable remainder comparison required when a unit
replacement drop is tilted by a negative exponential parameter.
-/

namespace AppliedModelingLib

open scoped Topology
open Filter Set

/-- On the unit interval, the positive exponential remainder is quadratically
dominated by its endpoint remainder.  This is the elementary estimate used
for the negative-parameter self-bounding entropy calculation. -/
theorem exp_mul_sub_mul_sub_one_le_sq_mul_exp_sub
    {parameter drop : ℝ} (hparameter : 0 ≤ parameter)
    (hdrop : 0 ≤ drop) (hdrop_one : drop ≤ 1) :
    Real.exp (parameter * drop) - parameter * drop - 1 ≤
      drop ^ 2 * (Real.exp parameter - parameter - 1) := by
  by_cases hparameter_zero : parameter = 0
  · simp [hparameter_zero]
  by_cases hdrop_zero : drop = 0
  · simp [hdrop_zero]
  let numerator : ℝ → ℝ := fun value =>
    Real.exp value * (value - 2) + value + 2
  have hnumerator_deriv (value : ℝ) :
      HasDerivAt numerator (Real.exp value * (value - 1) + 1) value := by
    unfold numerator
    convert
      ((Real.hasDerivAt_exp value).mul
        ((hasDerivAt_id value).sub (hasDerivAt_const value (2 : ℝ)))).add
        ((hasDerivAt_id value).add (hasDerivAt_const value (2 : ℝ))) using 1 <;>
      first | (ext x <;> simp [id_eq] <;> ring) | (simp [id_eq] <;> ring)
  let slope : ℝ → ℝ := fun value => Real.exp value * (value - 1) + 1
  have hslope_deriv (value : ℝ) :
      HasDerivAt slope (Real.exp value * value) value := by
    unfold slope
    convert
      ((Real.hasDerivAt_exp value).mul
        ((hasDerivAt_id value).sub (hasDerivAt_const value (1 : ℝ)))).add
        (hasDerivAt_const value (1 : ℝ)) using 1 <;>
      first | (ext x <;> simp [id_eq] <;> ring) | (simp [id_eq] <;> ring)
  have hslope_nonneg : ∀ value, 0 ≤ value → 0 ≤ slope value := by
    intro value hvalue
    have hslope_mono : MonotoneOn slope (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · intro value _
        exact (hslope_deriv value).continuousAt.continuousWithinAt
      · intro value _
        exact (hslope_deriv value).differentiableAt.differentiableWithinAt
      · intro value hvalue
        rw [(hslope_deriv value).deriv]
        exact mul_nonneg (Real.exp_nonneg _) (mem_Ici.mp (interior_subset hvalue))
    have hcompare := hslope_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hvalue) hvalue
    simpa [slope] using hcompare
  have hnumerator_nonneg : ∀ value, 0 ≤ value → 0 ≤ numerator value := by
    intro value hvalue
    have hnumerator_mono : MonotoneOn numerator (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · intro value _
        exact (hnumerator_deriv value).continuousAt.continuousWithinAt
      · intro value _
        exact (hnumerator_deriv value).differentiableAt.differentiableWithinAt
      · intro value hvalue
        rw [(hnumerator_deriv value).deriv]
        exact hslope_nonneg value (mem_Ici.mp (interior_subset hvalue))
    have hcompare := hnumerator_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hvalue) hvalue
    simpa [numerator] using hcompare
  let quotient : ℝ → ℝ := fun value =>
    (Real.exp value - value - 1) / value ^ 2
  have hquotient_deriv (value : ℝ) (hvalue : value ≠ 0) :
      HasDerivAt quotient (numerator value / value ^ 3) value := by
    unfold quotient numerator
    convert
      (((Real.hasDerivAt_exp value).sub (hasDerivAt_id value)).sub
        (hasDerivAt_const value (1 : ℝ))).div
        ((hasDerivAt_pow 2 value)) (pow_ne_zero 2 hvalue) using 1 <;>
      first | (ext x <;> simp [id_eq] <;> field_simp [hvalue] <;> ring) |
        (simp [id_eq] <;> field_simp [hvalue] <;> ring)
  have hquotient_mono : MonotoneOn quotient (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro value hvalue
      exact (hquotient_deriv value (mem_Ioi.mp hvalue).ne').continuousAt.continuousWithinAt
    · intro value hvalue
      exact (hquotient_deriv value (mem_Ioi.mp (interior_subset hvalue)).ne').differentiableAt
        |>.differentiableWithinAt
    · intro value hvalue
      rw [(hquotient_deriv value (mem_Ioi.mp (interior_subset hvalue)).ne').deriv]
      exact div_nonneg
        (hnumerator_nonneg value (mem_Ioi.mp (interior_subset hvalue)).le)
        (pow_nonneg (mem_Ioi.mp (interior_subset hvalue)).le _)
  have hparameter_pos : 0 < parameter := lt_of_le_of_ne hparameter (Ne.symm hparameter_zero)
  have hdrop_pos : 0 < drop := lt_of_le_of_ne hdrop (Ne.symm hdrop_zero)
  have hscaled_pos : 0 < parameter * drop := mul_pos hparameter_pos hdrop_pos
  have hscaled_le : parameter * drop ≤ parameter := by
    nlinarith
  have hratio := hquotient_mono (mem_Ioi.mpr hscaled_pos)
    (mem_Ioi.mpr hparameter_pos) hscaled_le
  unfold quotient at hratio
  field_simp [hparameter_pos.ne', hdrop_pos.ne'] at hratio
  nlinarith

/-- The negative-parameter one-coordinate entropy bound.  A unit replacement
drop turns the positive exponential remainder into the squared-drop term
needed for the lower self-bounding tail. -/
theorem pmfFunctionalEntropy_negExp_update_le_exp_remainder_sq_drop
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ} {scale : ℝ}
    (law : PMF α) (objective : (Fin n → α) → ℝ)
    (sample : Fin n → α) (coordinate : Fin n) (parameter : ℝ)
    (hself : FiniteSelfBounding objective scale) (hparameter : 0 ≤ parameter) :
    pmfFunctionalEntropy law (fun value =>
      Real.exp (-parameter * objective (Function.update sample coordinate value))) ≤
      (Real.exp parameter - parameter - 1) *
        pmfExp law (fun value =>
          Real.exp (-parameter * objective (Function.update sample coordinate value)) *
            (finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) ^ 2) := by
  let lower : ℝ := finiteCoordinateReplacementInf objective sample coordinate
  have hlower : ∀ value : α,
      lower ≤ objective (Function.update sample coordinate value) := by
    intro value
    exact finiteCoordinateReplacementInf_le_replacement objective sample coordinate value
  have hbase := pmfFunctionalEntropy_exp_le_expNegDrop
    law (fun value => objective (Function.update sample coordinate value)) (-parameter) lower
  have hpoint (value : α) :
      Real.exp (-parameter * objective (Function.update sample coordinate value)) *
          (Real.exp (parameter *
            finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) -
            parameter * finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate - 1) ≤
        Real.exp (-parameter * objective (Function.update sample coordinate value)) *
          ((finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) ^ 2 *
            (Real.exp parameter - parameter - 1)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    apply exp_mul_sub_mul_sub_one_le_sq_mul_exp_sub hparameter
    · exact finiteCoordinateReplacementDrop_nonneg objective
        (Function.update sample coordinate value) coordinate
    · exact hself.drop_le_one (Function.update sample coordinate value) coordinate
  calc
    pmfFunctionalEntropy law (fun value =>
        Real.exp (-parameter * objective (Function.update sample coordinate value))) =
      pmfFunctionalEntropy law (fun value =>
        Real.exp ((-parameter) * objective (Function.update sample coordinate value))) := by
          rfl
    _ ≤ pmfExp law (fun value =>
        Real.exp ((-parameter) * objective (Function.update sample coordinate value)) *
          (Real.exp (-(-parameter) *
            (objective (Function.update sample coordinate value) - lower)) +
            (-parameter) *
              (objective (Function.update sample coordinate value) - lower) - 1)) := hbase
    _ = pmfExp law (fun value =>
        Real.exp (-parameter * objective (Function.update sample coordinate value)) *
          (Real.exp (parameter *
            finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) -
            parameter * finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate - 1)) := by
          apply pmfExp_congr
          intro value
          unfold finiteCoordinateReplacementDrop
          rw [finiteCoordinateReplacementInf_update]
          simp only [lower]
          ring
    _ ≤ pmfExp law (fun value =>
        Real.exp (-parameter * objective (Function.update sample coordinate value)) *
          ((finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) ^ 2 *
            (Real.exp parameter - parameter - 1))) := by
          apply pmfExp_le_pmfExp_of_forall_le
          exact hpoint
    _ = (Real.exp parameter - parameter - 1) *
        pmfExp law (fun value =>
          Real.exp (-parameter * objective (Function.update sample coordinate value)) *
            (finiteCoordinateReplacementDrop objective
              (Function.update sample coordinate value) coordinate) ^ 2) := by
          rw [← pmfExp_const_mul]
          apply pmfExp_congr
          intro value
          ring

/-- Averaging the negative-parameter coordinate entropy estimate over a
resampled iid coordinate gives the corresponding literal product energy. -/
theorem pmfExp_pmfProduct_coordinateEntropy_negExp_le_exp_remainder_sq_drop
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (objective : (Fin n → α) → ℝ)
    (coordinate : Fin n) (parameter scale : ℝ)
    (hself : FiniteSelfBounding objective scale) (hparameter : 0 ≤ parameter) :
    pmfExp (pmfProduct (Fin n) α law) (fun sample =>
      pmfFunctionalEntropy law (fun value =>
        Real.exp (-parameter * objective (Function.update sample coordinate value)))) ≤
      (Real.exp parameter - parameter - 1) *
        pmfExp (pmfProduct (Fin n) α law) (fun sample =>
          Real.exp (-parameter * objective sample) *
            (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) := by
  let resampledEnergy : (Fin n → α) → α → ℝ := fun sample value =>
    Real.exp (-parameter * objective (Function.update sample coordinate value)) *
      (finiteCoordinateReplacementDrop objective
        (Function.update sample coordinate value) coordinate) ^ 2
  have hpoint : ∀ sample : Fin n → α,
      pmfFunctionalEntropy law (fun value =>
        Real.exp (-parameter * objective (Function.update sample coordinate value))) ≤
        (Real.exp parameter - parameter - 1) * pmfExp law (resampledEnergy sample) := by
    intro sample
    exact pmfFunctionalEntropy_negExp_update_le_exp_remainder_sq_drop
      law objective sample coordinate parameter hself hparameter
  calc
    pmfExp (pmfProduct (Fin n) α law) (fun sample =>
        pmfFunctionalEntropy law (fun value =>
          Real.exp (-parameter * objective (Function.update sample coordinate value)))) ≤
        pmfExp (pmfProduct (Fin n) α law) (fun sample =>
          (Real.exp parameter - parameter - 1) * pmfExp law (resampledEnergy sample)) := by
          apply pmfExp_le_pmfExp_of_forall_le
          exact hpoint
    _ = (Real.exp parameter - parameter - 1) *
        pmfPairExp (pmfProduct (Fin n) α law) law resampledEnergy := by
          unfold pmfPairExp
          rw [pmfExp_const_mul]
    _ = (Real.exp parameter - parameter - 1) *
        pmfExp (pmfProduct (Fin n) α law) (fun sample =>
          Real.exp (-parameter * objective sample) *
            (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) := by
          congr 1
          change pmfPairExp (pmfProduct (Fin n) α law) law
            (fun sample value =>
              Real.exp (-parameter * objective (Function.update sample coordinate value)) *
                (finiteCoordinateReplacementDrop objective
                  (Function.update sample coordinate value) coordinate) ^ 2) = _
          exact pmfPairExp_pmfProduct_update_eq_pmfExp law
            (fun sample =>
              Real.exp (-parameter * objective sample) *
                (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) coordinate

/-- Tensorizing the negative-parameter coordinate estimate gives the finite
entropy inequality for the lower self-bounding tail. -/
theorem FiniteSelfBounding.entropy_negExp_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hparameter : 0 ≤ parameter) :
    pmfFunctionalEntropy (pmfProduct (Fin n) α law)
        (fun sample => Real.exp (-parameter * objective sample)) ≤
      (Real.exp parameter - parameter - 1) * scale *
        pmfExp (pmfProduct (Fin n) α law)
          (fun sample => Real.exp (-parameter * objective sample) * objective sample) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let coefficient : ℝ := Real.exp parameter - parameter - 1
  let coordinateContribution : Fin n → (Fin n → α) → ℝ := fun coordinate sample =>
    pmfFunctionalEntropy law (fun value =>
      Real.exp (-parameter * objective (Function.update sample coordinate value)))
  let resampledEnergy : Fin n → (Fin n → α) → ℝ := fun coordinate sample =>
    Real.exp (-parameter * objective sample) *
      (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2
  have hcoefficient_nonneg : 0 ≤ coefficient := by
    unfold coefficient
    linarith [Real.add_one_le_exp parameter]
  have hcoordinate (coordinate : Fin n) :
      pmfExp productLaw (coordinateContribution coordinate) ≤
        coefficient * pmfExp productLaw (resampledEnergy coordinate) := by
    simpa only [productLaw, coordinateContribution, coefficient] using
      pmfExp_pmfProduct_coordinateEntropy_negExp_le_exp_remainder_sq_drop
        law objective coordinate parameter scale hself hparameter
  have hsum_coordinate :
      (∑ coordinate : Fin n, pmfExp productLaw (coordinateContribution coordinate)) ≤
        ∑ coordinate : Fin n,
          coefficient * pmfExp productLaw (resampledEnergy coordinate) := by
    exact Finset.sum_le_sum fun coordinate _ => hcoordinate coordinate
  have henergy_point (sample : Fin n → α) :
      (∑ coordinate : Fin n, resampledEnergy coordinate sample) ≤
        Real.exp (-parameter * objective sample) * (scale * objective sample) := by
    dsimp [resampledEnergy]
    calc
      (∑ coordinate : Fin n,
          Real.exp (-parameter * objective sample) *
            (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) =
          Real.exp (-parameter * objective sample) *
            ∑ coordinate : Fin n,
              (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (-parameter * objective sample) * (scale * objective sample) := by
            gcongr
            exact hself.sum_sq_drop_le sample
  have henergy_mean :
      pmfExp productLaw (fun sample => ∑ coordinate : Fin n,
          resampledEnergy coordinate sample) ≤
        pmfExp productLaw (fun sample =>
          Real.exp (-parameter * objective sample) * (scale * objective sample)) := by
    apply pmfExp_le_pmfExp_of_forall_le
    exact henergy_point
  have hsum_resampled :
      (∑ coordinate : Fin n, pmfExp productLaw (resampledEnergy coordinate)) ≤
        pmfExp productLaw (fun sample =>
          Real.exp (-parameter * objective sample) * (scale * objective sample)) := by
    rw [← pmfExp_univ_sum]
    exact henergy_mean
  calc
    pmfFunctionalEntropy productLaw
        (fun sample => Real.exp (-parameter * objective sample)) ≤
        pmfExp productLaw (fun sample =>
          ∑ coordinate : Fin n, coordinateContribution coordinate sample) := by
          exact finiteProductEntropyTensorizesExp_fin law n
            (fun sample => -parameter * objective sample)
    _ = ∑ coordinate : Fin n,
          pmfExp productLaw (coordinateContribution coordinate) :=
        pmfExp_univ_sum productLaw coordinateContribution
    _ ≤ ∑ coordinate : Fin n,
          coefficient * pmfExp productLaw (resampledEnergy coordinate) :=
        hsum_coordinate
    _ = coefficient *
          ∑ coordinate : Fin n, pmfExp productLaw (resampledEnergy coordinate) := by
          rw [Finset.mul_sum]
    _ ≤ coefficient *
          pmfExp productLaw (fun sample =>
            Real.exp (-parameter * objective sample) * (scale * objective sample)) := by
          gcongr
    _ = coefficient * scale *
        pmfExp productLaw (fun sample =>
          Real.exp (-parameter * objective sample) * objective sample) := by
          rw [← pmfExp_const_mul]
          calc
            pmfExp productLaw (fun sample =>
                coefficient *
                  (Real.exp (-parameter * objective sample) *
                    (scale * objective sample))) =
                pmfExp productLaw (fun sample =>
                  (coefficient * scale) *
                    (Real.exp (-parameter * objective sample) * objective sample)) := by
                    apply pmfExp_congr
                    intro sample
                    ring
            _ = (coefficient * scale) *
                pmfExp productLaw (fun sample =>
                  Real.exp (-parameter * objective sample) * objective sample) := by
                    rw [pmfExp_const_mul]
            _ = coefficient * scale *
                pmfExp productLaw (fun sample =>
                  Real.exp (-parameter * objective sample) * objective sample) := by
                    ring

/-- The negative-parameter product entropy inequality gives the exact
log-MGF differential inequality for the lower self-bounding tail. -/
theorem FiniteSelfBounding.finiteLogMGF_neg_differential_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hparameter : 0 ≤ parameter) :
    (parameter + scale * (Real.exp parameter - parameter - 1)) *
        (-((∑ sample : Fin n → α,
          (pmfProduct (Fin n) α law sample).toReal *
            (Real.exp ((-parameter) * objective sample) * objective sample)) /
          Probability.finiteMGF (pmfProduct (Fin n) α law) objective (-parameter))) ≤
      Probability.finiteLogMGF (pmfProduct (Fin n) α law) objective (-parameter) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let numerator : ℝ := ∑ sample : Fin n → α,
    (productLaw sample).toReal *
      (Real.exp ((-parameter) * objective sample) * objective sample)
  let partition : ℝ := Probability.finiteMGF productLaw objective (-parameter)
  have hpartition_pos : 0 < partition :=
    Probability.finiteMGF_pos productLaw objective (-parameter)
  have hentropy :
      pmfFunctionalEntropy productLaw
          (fun sample => Real.exp (-parameter * objective sample)) ≤
        (Real.exp parameter - parameter - 1) * scale * numerator := by
    simpa only [productLaw, numerator] using
      hself.entropy_negExp_le (law := law) hparameter
  have hidentity := pmfFunctionalEntropy_exp_eq_finiteLogMGF_numerator
    productLaw objective (-parameter)
  have hentropy' :
      (-parameter) * numerator -
        partition * Probability.finiteLogMGF productLaw objective (-parameter) ≤
        (Real.exp parameter - parameter - 1) * scale * numerator := by
    rw [← hidentity]
    simpa only [partition, numerator] using hentropy
  change (parameter + scale * (Real.exp parameter - parameter - 1)) *
      (-(numerator / partition)) ≤
    Probability.finiteLogMGF productLaw objective (-parameter)
  have hnumerator :
      -(parameter + scale * (Real.exp parameter - parameter - 1)) * numerator ≤
        partition * Probability.finiteLogMGF productLaw objective (-parameter) := by
    nlinarith [hentropy']
  calc
    (parameter + scale * (Real.exp parameter - parameter - 1)) *
        (-(numerator / partition)) =
        (-(parameter + scale * (Real.exp parameter - parameter - 1)) * numerator) /
          partition := by
            field_simp [hpartition_pos.ne']
    _ ≤ Probability.finiteLogMGF productLaw objective (-parameter) :=
      (div_le_iff₀ hpartition_pos).2 (by simpa [mul_comm] using hnumerator)

/-- The lower-tail entropy denominator is bounded by the explicit comparison
denominator whose homogeneous solution is `(1 - exp(-a λ)) / a`. -/
theorem selfBoundingNegEntropyDenominator_le_expComparison
    {scale parameter : ℝ} (hscale : 1 ≤ scale) (hparameter : 0 ≤ parameter) :
    parameter + scale * (Real.exp parameter - parameter - 1) ≤
      (Real.exp (scale * parameter) - 1) / scale := by
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  let inner : ℝ → ℝ := fun value =>
    Real.exp (scale * value) - 1 - scale * (Real.exp value - 1)
  have hinner_deriv (value : ℝ) :
      HasDerivAt inner (scale * (Real.exp (scale * value) - Real.exp value)) value := by
    unfold inner
    convert
      ((((hasDerivAt_const value scale).mul (hasDerivAt_id value)).exp.sub_const 1).sub
        ((hasDerivAt_const value scale).mul
          ((Real.hasDerivAt_exp value).sub (hasDerivAt_const value (1 : ℝ))))) using 1 <;>
      simp [id_eq] <;> ring
  have hinner_nonneg : ∀ value, 0 ≤ value → 0 ≤ inner value := by
    intro value hvalue
    have hinner_mono : MonotoneOn inner (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · intro point _
        exact (hinner_deriv point).continuousAt.continuousWithinAt
      · intro point _
        exact (hinner_deriv point).differentiableAt.differentiableWithinAt
      · intro point hpoint
        rw [(hinner_deriv point).deriv]
        apply mul_nonneg hscale_pos.le
        apply sub_nonneg.mpr
        apply Real.exp_le_exp.mpr
        have hpoint_nonneg : 0 ≤ point := mem_Ici.mp (interior_subset hpoint)
        nlinarith
    have hcompare := hinner_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hvalue) hvalue
    simpa [inner] using hcompare
  let difference : ℝ → ℝ := fun value =>
    Real.exp (scale * value) - 1 - scale * value -
      scale ^ 2 * (Real.exp value - value - 1)
  have hdifference_deriv (value : ℝ) :
      HasDerivAt difference (scale * inner value) value := by
    unfold difference inner
    convert
      (((((hasDerivAt_const value scale).mul (hasDerivAt_id value)).exp.sub_const 1).sub
        ((hasDerivAt_const value scale).mul (hasDerivAt_id value))).sub
        ((hasDerivAt_const value (scale ^ 2)).mul
          (((Real.hasDerivAt_exp value).sub (hasDerivAt_id value)).sub
            (hasDerivAt_const value (1 : ℝ))))) using 1 <;>
      simp [id_eq] <;> ring
  have hdifference_nonneg : 0 ≤ difference parameter := by
    have hdifference_mono : MonotoneOn difference (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · intro value _
        exact (hdifference_deriv value).continuousAt.continuousWithinAt
      · intro value _
        exact (hdifference_deriv value).differentiableAt.differentiableWithinAt
      · intro value hvalue
        rw [(hdifference_deriv value).deriv]
        exact mul_nonneg hscale_pos.le
          (hinner_nonneg value (mem_Ici.mp (interior_subset hvalue)))
    have hcompare := hdifference_mono (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr hparameter) hparameter
    simpa [difference] using hcompare
  apply (le_div_iff₀ hscale_pos).2
  nlinarith [hdifference_nonneg]

/-- The negative-parameter self-bounding differential inequality integrates
against its exponential comparison solution.  This is the lower-tail Herbst
step before centering and Chernoff optimization. -/
theorem negLogMGF_le_of_selfBounding_differential
    {logMGF derivative : ℝ → ℝ} {mean scale endpoint : ℝ}
    (hscale : 1 ≤ scale)
    (hcontinuous : Continuous logMGF)
    (hderiv : ∀ parameter, HasDerivAt logMGF (derivative parameter) parameter)
    (hzero : logMGF 0 = 0)
    (hderiv_zero : derivative 0 = -mean)
    (hdiff : ∀ parameter, 0 < parameter → parameter ≤ endpoint →
      (parameter + scale * (Real.exp parameter - parameter - 1)) *
        derivative parameter ≤ logMGF parameter)
    (hderiv_nonpos : ∀ parameter, 0 < parameter → parameter ≤ endpoint →
      derivative parameter ≤ 0) :
    ∀ parameter, 0 < parameter → parameter ≤ endpoint →
      logMGF parameter ≤
        -mean * ((1 - Real.exp (-scale * parameter)) / scale) := by
  intro parameter hparameter hparameter_endpoint
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  let comparison : ℝ → ℝ := fun value =>
    (1 - Real.exp (-scale * value)) / scale
  have hcomparison_deriv (value : ℝ) :
      HasDerivAt comparison (Real.exp (-scale * value)) value := by
    unfold comparison
    convert ((hasDerivAt_const value (1 : ℝ)).sub
      (((hasDerivAt_const value (-scale)).mul (hasDerivAt_id value)).exp)).div_const scale using 1 <;>
      simp [id_eq] <;> field_simp [hscale_pos.ne'] <;> ring
  have hcomparison_pos (value : ℝ) (hvalue : 0 < value) : 0 < comparison value := by
    unfold comparison
    apply div_pos
    · rw [sub_pos]
      apply Real.exp_lt_one_iff.mpr
      nlinarith
    · exact hscale_pos
  let quotient : ℝ → ℝ := fun value => logMGF value / comparison value
  have hquotient_continuous : ContinuousOn quotient (Ioc 0 endpoint) := by
    intro value hvalue
    exact (hcontinuous.continuousAt.div
      (hcomparison_deriv value).continuousAt (hcomparison_pos value hvalue.1).ne').continuousWithinAt
  have hquotient_deriv (value : ℝ) (hvalue : 0 < value) :
      HasDerivAt quotient
        ((comparison value * derivative value -
          logMGF value * Real.exp (-scale * value)) / comparison value ^ 2) value := by
    unfold quotient
    simpa [mul_comm] using (hderiv value).div
      (hcomparison_deriv value) (hcomparison_pos value hvalue).ne'
  have hcomparison_times_deriv_le (value : ℝ) (hvalue : 0 < value)
      (hvalue_endpoint : value ≤ endpoint) :
      comparison value * derivative value ≤
        logMGF value * Real.exp (-scale * value) := by
    have hdenominator := selfBoundingNegEntropyDenominator_le_expComparison
      hscale hvalue.le
    have hscaled :
        ((Real.exp (scale * value) - 1) / scale) * derivative value ≤
          (value + scale * (Real.exp value - value - 1)) * derivative value :=
      mul_le_mul_of_nonpos_right hdenominator
        (hderiv_nonpos value hvalue hvalue_endpoint)
    have hsource := hdiff value hvalue hvalue_endpoint
    have hcomparison_eq :
        comparison value = (Real.exp (scale * value) - 1) / scale *
          Real.exp (-scale * value) := by
      unfold comparison
      have hnegative : -scale * value = -(scale * value) := by ring
      rw [hnegative, Real.exp_neg]
      field_simp [hscale_pos.ne', Real.exp_ne_zero]
    calc
      comparison value * derivative value =
          Real.exp (-scale * value) *
            (((Real.exp (scale * value) - 1) / scale) * derivative value) := by
              rw [hcomparison_eq]
              ring
      _ ≤ Real.exp (-scale * value) *
          ((value + scale * (Real.exp value - value - 1)) * derivative value) := by
              gcongr
      _ ≤ Real.exp (-scale * value) * logMGF value := by
              gcongr
      _ = logMGF value * Real.exp (-scale * value) := by ring
  have hquotient_antitone : AntitoneOn quotient (Ioc 0 endpoint) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 endpoint) hquotient_continuous
    · intro value hvalue
      have hvalue_pos : 0 < value := (mem_Ioc.mp (interior_subset hvalue)).1
      exact (hquotient_deriv value hvalue_pos).differentiableAt.differentiableWithinAt
    · intro value hvalue
      have hvalue_mem : value ∈ Ioc 0 endpoint := interior_subset hvalue
      have hvalue_pos : 0 < value := hvalue_mem.1
      have hvalue_endpoint : value ≤ endpoint := hvalue_mem.2
      rw [(hquotient_deriv value hvalue_pos).deriv]
      apply div_nonpos_of_nonpos_of_nonneg
      · exact sub_nonpos.mpr
          (hcomparison_times_deriv_le value hvalue_pos hvalue_endpoint)
      · positivity
  have hquotient_limit : Tendsto quotient (𝓝[>] 0) (𝓝 (-mean)) := by
    have hslope := (hderiv 0).tendsto_slope_zero_right
    have hratio : Tendsto (fun value : ℝ => logMGF value / value)
        (𝓝[>] 0) (𝓝 (-mean)) := by
      rw [← hderiv_zero]
      simpa [div_eq_mul_inv, mul_comm, hzero] using hslope
    have hcomparison_ratio : Tendsto (fun value : ℝ => comparison value / value)
        (𝓝[>] 0) (𝓝 1) := by
      have hderiv_limit := (hcomparison_deriv 0).tendsto_slope_zero_right
      simpa [comparison, div_eq_mul_inv, mul_comm] using hderiv_limit
    have hratio' : Tendsto (fun value : ℝ =>
        (logMGF value / value) / (comparison value / value))
        (𝓝[>] 0) (𝓝 (-mean / 1)) :=
      hratio.div hcomparison_ratio (by norm_num)
    have hquotient_eq : (fun value : ℝ => quotient value) =ᶠ[𝓝[>] 0]
        (fun value => (logMGF value / value) / (comparison value / value)) := by
      filter_upwards [Ioc_mem_nhdsGT hparameter] with value hvalue
      unfold quotient
      field_simp [hvalue.1.ne', (hcomparison_pos value hvalue.1).ne']
    convert hratio'.congr' hquotient_eq.symm using 1 <;> ring
  have hquotient_le : quotient parameter ≤ -mean := by
    apply ge_of_tendsto hquotient_limit
    filter_upwards [Ioc_mem_nhdsGT hparameter] with value hvalue
    exact hquotient_antitone
      (mem_Ioc.mpr ⟨hvalue.1, le_trans hvalue.2 hparameter_endpoint⟩)
      (mem_Ioc.mpr ⟨hparameter, hparameter_endpoint⟩) hvalue.2
  have hcomparison_parameter_pos : 0 < comparison parameter :=
    hcomparison_pos parameter hparameter
  calc
    logMGF parameter = comparison parameter * quotient parameter := by
      unfold quotient
      field_simp [hcomparison_parameter_pos.ne']
    _ ≤ comparison parameter * (-mean) := by gcongr
    _ = -mean * ((1 - Real.exp (-scale * parameter)) / scale) := by
      unfold comparison
      ring

/-- The finite negative log-MGF of a self-bounding objective is controlled by
the exponential comparison solution.  The scale hypothesis is Maurer's
`a ≥ 1` lower-tail regime. -/
theorem FiniteSelfBounding.finiteLogMGF_neg_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 1 ≤ scale) (hparameter : 0 < parameter) :
    Probability.finiteLogMGF (pmfProduct (Fin n) α law) objective (-parameter) ≤
      -pmfExp (pmfProduct (Fin n) α law) objective *
        ((1 - Real.exp (-scale * parameter)) / scale) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let derivative : ℝ → ℝ := fun value =>
    -((∑ sample : Fin n → α,
      (productLaw sample).toReal *
        (Real.exp ((-value) * objective sample) * objective sample)) /
      Probability.finiteMGF productLaw objective (-value))
  let mean : ℝ := pmfExp productLaw objective
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hobjective_nonneg (sample : Fin n → α) : 0 ≤ objective sample := by
    exact hself.objective_nonneg_of_pos_scale hscale_pos sample
  have hderiv (value : ℝ) :
      HasDerivAt (fun argument =>
        Probability.finiteLogMGF productLaw objective (-argument))
        (derivative value) value := by
    unfold derivative
    simpa [mul_comm] using
      (Probability.finiteLogMGF_hasDerivAt productLaw objective (-value)).comp value
        (hasDerivAt_neg value)
  have hderiv_zero : derivative 0 = -mean := by
    exact (hderiv 0).unique (by
      simpa [mean, Probability.finiteMGF_zero, pmfExp, mul_comm] using
        (Probability.finiteLogMGF_hasDerivAt productLaw objective (-(0 : ℝ))).comp (0 : ℝ)
          (hasDerivAt_neg (0 : ℝ)))
  have hderiv_nonpos (value : ℝ) (hvalue : 0 < value)
      (hvalue_endpoint : value ≤ parameter) : derivative value ≤ 0 := by
    unfold derivative
    apply neg_nonpos.mpr
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro sample _
      exact mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (Real.exp_nonneg _) (hobjective_nonneg sample))
    · exact (Probability.finiteMGF_pos productLaw objective (-value)).le
  have hdiff (value : ℝ) (hvalue : 0 < value)
      (hvalue_endpoint : value ≤ parameter) :
      (value + scale * (Real.exp value - value - 1)) * derivative value ≤
        Probability.finiteLogMGF productLaw objective (-value) := by
    unfold derivative
    simpa [productLaw] using
      hself.finiteLogMGF_neg_differential_le (law := law) (parameter := value) hvalue.le
  have hsource := negLogMGF_le_of_selfBounding_differential
    (logMGF := fun value => Probability.finiteLogMGF productLaw objective (-value))
    (derivative := derivative) (mean := mean) (scale := scale) (endpoint := parameter)
    hscale (by
      exact (Probability.finiteLogMGF_continuous productLaw objective).comp
        (continuous_neg)) hderiv
    (by simp [Probability.finiteLogMGF, Probability.finiteMGF_zero]) hderiv_zero
    hdiff hderiv_nonpos parameter hparameter le_rfl
  simpa only [productLaw, mean] using hsource

/-- The centered lower-direction log-MGF is subgaussian with variance proxy
`scale * E[Z]`.  This is the form used by the Chernoff lower-tail step. -/
theorem FiniteSelfBounding.finiteLogMGF_const_sub_le_half_sq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 1 ≤ scale) (hparameter : 0 < parameter) :
    Probability.finiteLogMGF (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law) objective - objective sample) parameter ≤
      scale * pmfExp (pmfProduct (Fin n) α law) objective * parameter ^ 2 / 2 := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let mean : ℝ := pmfExp productLaw objective
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hmean_nonneg : 0 ≤ mean :=
    pmfExp_nonneg_of_forall_nonneg productLaw objective
      (hself.objective_nonneg_of_pos_scale hscale_pos)
  have hcomparison :
      parameter - ((1 - Real.exp (-scale * parameter)) / scale) ≤
        scale * parameter ^ 2 / 2 := by
    have hquadratic := exp_neg_add_sub_one_le_half_sq
      (mul_nonneg hscale_pos.le hparameter.le)
    calc
      parameter - ((1 - Real.exp (-scale * parameter)) / scale) =
          (Real.exp (-scale * parameter) + scale * parameter - 1) / scale := by
            field_simp [hscale_pos.ne']
            ring
      _ ≤ (scale * parameter) ^ 2 / 2 / scale := by
            apply div_le_div_of_nonneg_right _ hscale_pos.le
            convert hquadratic using 1 <;> ring
      _ = scale * parameter ^ 2 / 2 := by
            field_simp [hscale_pos.ne']
  have hnegative := hself.finiteLogMGF_neg_le (law := law) hscale hparameter
  rw [Probability.finiteLogMGF_const_sub]
  calc
    parameter * mean + Probability.finiteLogMGF productLaw objective (-parameter) ≤
        parameter * mean +
          (-mean * ((1 - Real.exp (-scale * parameter)) / scale)) := by
            gcongr
    _ = mean *
        (parameter - ((1 - Real.exp (-scale * parameter)) / scale)) := by ring
    _ ≤ mean * (scale * parameter ^ 2 / 2) := by gcongr
    _ = scale * mean * parameter ^ 2 / 2 := by ring

/-- Maurer's finite self-bounding lower tail.  The literal lower event is
`E[Z] - Z > t`, and the `scale ≥ 1` hypothesis is retained exactly from the
source theorem. -/
theorem FiniteSelfBounding.pmfProb_lowerTail_le_exp
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale threshold : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 1 ≤ scale) (hthreshold : 0 < threshold) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          objective sample <
            pmfExp (pmfProduct (Fin n) α law) objective - threshold) ≤
      Real.exp (-threshold ^ 2 /
        (2 * scale * pmfExp (pmfProduct (Fin n) α law) objective)) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let mean : ℝ := pmfExp productLaw objective
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hmean_nonneg : 0 ≤ mean :=
    pmfExp_nonneg_of_forall_nonneg productLaw objective
      (hself.objective_nonneg_of_pos_scale hscale_pos)
  rcases eq_or_lt_of_le hmean_nonneg with hmean_zero | hmean_pos
  · calc
      pmfProb (pmfProduct (Fin n) α law)
          (fun sample =>
            objective sample < pmfExp (pmfProduct (Fin n) α law) objective - threshold) ≤ 1 :=
          pmfProb_le_one _ _
      _ = Real.exp (-threshold ^ 2 /
          (2 * scale * pmfExp (pmfProduct (Fin n) α law) objective)) := by
            rw [show pmfExp (pmfProduct (Fin n) α law) objective = 0 by
              simpa [mean, productLaw] using hmean_zero.symm]
            simp
  · let parameter : ℝ := threshold / (scale * mean)
    have hdenominator_pos : 0 < scale * mean := mul_pos hscale_pos hmean_pos
    have hparameter : 0 < parameter := div_pos hthreshold hdenominator_pos
    have hlog := hself.finiteLogMGF_const_sub_le_half_sq (law := law)
      hscale hparameter
    have hchernoff := pmfProb_upperTail_le_exp_neg_mul_add_finiteLogMGF
      productLaw (fun sample => mean - objective sample) threshold parameter hparameter
    have hevent : ∀ sample,
        threshold < mean - objective sample ↔ objective sample < mean - threshold := by
      intro sample
      constructor <;> intro h <;> linarith
    rw [pmfProb_congr productLaw hevent] at hchernoff
    calc
      pmfProb (pmfProduct (Fin n) α law)
          (fun sample =>
            objective sample < pmfExp (pmfProduct (Fin n) α law) objective - threshold) =
          pmfProb productLaw (fun sample => objective sample < mean - threshold) := by
            rfl
      _ ≤ Real.exp (-parameter * threshold +
          Probability.finiteLogMGF productLaw (fun sample => mean - objective sample) parameter) :=
            hchernoff
      _ ≤ Real.exp (-parameter * threshold +
          scale * mean * parameter ^ 2 / 2) := by
            apply Real.exp_monotone
            gcongr
      _ = Real.exp (-threshold ^ 2 / (2 * scale * mean)) := by
            congr 1
            dsimp [parameter]
            field_simp [hscale_pos.ne', hmean_pos.ne']
            ring
      _ = Real.exp (-threshold ^ 2 /
          (2 * scale * pmfExp (pmfProduct (Fin n) α law) objective)) := by
            rfl

end AppliedModelingLib

import AppliedModelingLib.Foundations.Probability.FiniteSelfBoundingMGF
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A one-dimensional finite Herbst lemma

This file isolates the real-analysis integration step after the finite
product entropy calculation.  The hypothesis is the exact differential
inequality obtained from a self-bounding entropy bound.
-/

namespace AppliedModelingLib

open scoped Topology
open Filter Set

/-- A log-MGF differential inequality integrates to the standard finite
Herbst bound on any positive interval where its denominator remains positive. -/
theorem logMGF_le_of_selfBounding_differential
    {logMGF derivative : ℝ → ℝ} {mean scale endpoint : ℝ}
    (hcontinuous : Continuous logMGF)
    (hderiv : ∀ parameter, HasDerivAt logMGF (derivative parameter) parameter)
    (hzero : logMGF 0 = 0)
    (hderiv_zero : derivative 0 = mean)
    (hdiff : ∀ parameter, 0 < parameter → parameter ≤ endpoint →
      (parameter - parameter ^ 2 / 2 * scale) * derivative parameter ≤
        logMGF parameter)
    (hfactor : ∀ parameter, 0 < parameter → parameter ≤ endpoint →
      0 < 1 - scale * parameter / 2) :
    ∀ parameter, 0 < parameter → parameter ≤ endpoint →
      logMGF parameter ≤
        parameter * mean / (1 - scale * parameter / 2) := by
  intro parameter hparameter hparameter_endpoint
  let quotient : ℝ → ℝ := fun value =>
    (1 - scale * value / 2) * (logMGF value / value)
  have hquotient_continuous : ContinuousOn quotient (Ioc 0 endpoint) := by
    intro value hvalue
    exact (
      ((continuous_const.sub
        ((continuous_const.mul continuous_id).div_const (2 : ℝ))).continuousAt).mul
        (hcontinuous.continuousAt.div continuousAt_id hvalue.1.ne')).continuousWithinAt
  have hquotient_deriv (value : ℝ) (hvalue : value ≠ 0) :
      HasDerivAt quotient
        (((value - value ^ 2 / 2 * scale) * derivative value - logMGF value) /
          value ^ 2) value := by
    unfold quotient
    have hfactor_deriv :
        HasDerivAt (fun argument : ℝ => 1 - scale * argument / 2) (-scale / 2) value := by
      convert (hasDerivAt_const value (1 : ℝ)).sub
        (((hasDerivAt_const value scale).mul (hasDerivAt_id value)).div_const (2 : ℝ)) using 1 <;>
        ring
    have hratio_deriv :
        HasDerivAt (fun argument : ℝ => logMGF argument / argument)
          ((derivative value * value - logMGF value) / value ^ 2) value := by
      change HasDerivAt (logMGF / id)
        ((derivative value * value - logMGF value) / value ^ 2) value
      simpa using (hderiv value).div (hasDerivAt_id value) hvalue
    convert hfactor_deriv.mul hratio_deriv using 1 <;>
      field_simp [hvalue] <;> ring
  have hquotient_antitone : AntitoneOn quotient (Ioc 0 endpoint) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 endpoint) hquotient_continuous
    · intro value hvalue
      have hvalue_pos : 0 < value := (mem_Ioc.mp (interior_subset hvalue)).1
      exact (hquotient_deriv value hvalue_pos.ne').differentiableAt.differentiableWithinAt
    · intro value hvalue
      have hvalue_mem : value ∈ Ioc 0 endpoint := interior_subset hvalue
      have hvalue_pos : 0 < value := (mem_Ioc.mp hvalue_mem).1
      have hvalue_endpoint : value ≤ endpoint := (mem_Ioc.mp hvalue_mem).2
      rw [(hquotient_deriv value hvalue_pos.ne').deriv]
      apply div_nonpos_of_nonpos_of_nonneg
      · have hsource := hdiff value hvalue_pos hvalue_endpoint
        nlinarith
      · positivity
  have hquotient_limit : Tendsto quotient (𝓝[>] 0) (𝓝 mean) := by
    have hslope := (hderiv 0).tendsto_slope_zero_right
    have hratio : Tendsto (fun value : ℝ => logMGF value / value) (𝓝[>] 0) (𝓝 mean) := by
      rw [← hderiv_zero]
      simpa [div_eq_mul_inv, mul_comm, hzero] using hslope
    have hfactor_limit :
        Tendsto (fun value : ℝ => 1 - scale * value / 2) (𝓝[>] 0) (𝓝 1) := by
      have hfactor_continuous : Continuous (fun value : ℝ => 1 - scale * value / 2) :=
        continuous_const.sub
          ((continuous_const.mul continuous_id).div_const (2 : ℝ))
      simpa using Tendsto.mono_left
        ((hfactor_continuous.continuousAt :
          ContinuousAt (fun value : ℝ => 1 - scale * value / 2) 0).tendsto)
        nhdsWithin_le_nhds
    simpa only [quotient, one_mul] using hfactor_limit.mul hratio
  have hquotient_le : quotient parameter ≤ mean := by
    apply ge_of_tendsto hquotient_limit
    filter_upwards [Ioc_mem_nhdsGT hparameter] with value hvalue
    exact hquotient_antitone
      (mem_Ioc.mpr ⟨hvalue.1, le_trans hvalue.2 hparameter_endpoint⟩)
      (mem_Ioc.mpr ⟨hparameter, hparameter_endpoint⟩) hvalue.2
  have hfactor_pos : 0 < 1 - scale * parameter / 2 :=
    hfactor parameter hparameter hparameter_endpoint
  have hratio_le : logMGF parameter / parameter ≤
      mean / (1 - scale * parameter / 2) := by
    apply (le_div_iff₀ hfactor_pos).2
    simpa [quotient, mul_comm, mul_left_comm, mul_assoc] using hquotient_le
  calc
    logMGF parameter = parameter * (logMGF parameter / parameter) := by
      field_simp [hparameter.ne']
    _ ≤ parameter * (mean / (1 - scale * parameter / 2)) := by
      gcongr
    _ = parameter * mean / (1 - scale * parameter / 2) := by ring

/-- The finite self-bounding entropy argument yields Maurer's positive-
parameter log-MGF bound.  The remaining Chernoff optimization is separate
from this analytic integration step. -/
theorem FiniteSelfBounding.finiteLogMGF_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale parameter : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 0 ≤ scale) (hparameter : 0 < parameter)
    (hfactor : 0 < 1 - scale * parameter / 2) :
    Probability.finiteLogMGF (pmfProduct (Fin n) α law) objective parameter ≤
      parameter * pmfExp (pmfProduct (Fin n) α law) objective /
        (1 - scale * parameter / 2) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let derivative : ℝ → ℝ := fun value =>
    (∑ sample : Fin n → α,
      (productLaw sample).toReal *
        (Real.exp (value * objective sample) * objective sample)) /
      Probability.finiteMGF productLaw objective value
  let mean : ℝ := pmfExp productLaw objective
  have hderiv (value : ℝ) :
      HasDerivAt (fun argument => Probability.finiteLogMGF productLaw objective argument)
        (derivative value) value := by
    unfold derivative
    simpa [mul_comm] using Probability.finiteLogMGF_hasDerivAt productLaw objective value
  have hderiv_zero : derivative 0 = mean := by
    exact (hderiv 0).unique
      (Probability.finiteLogMGF_hasDerivAt_zero productLaw objective)
  have hdiff (value : ℝ) (hvalue : 0 < value) (hvalue_endpoint : value ≤ parameter) :
      (value - value ^ 2 / 2 * scale) * derivative value ≤
        Probability.finiteLogMGF productLaw objective value := by
    unfold derivative
    simpa [productLaw] using
      hself.finiteLogMGF_differential_le (law := law) (parameter := value) hvalue.le
  have hfactor_all (value : ℝ) (hvalue : 0 < value) (hvalue_endpoint : value ≤ parameter) :
      0 < 1 - scale * value / 2 := by
    have hproduct_le : scale * value ≤ scale * parameter :=
      mul_le_mul_of_nonneg_left hvalue_endpoint hscale
    linarith
  have hsource := logMGF_le_of_selfBounding_differential
    (logMGF := fun value => Probability.finiteLogMGF productLaw objective value)
    (derivative := derivative) (mean := mean) (scale := scale) (endpoint := parameter)
    (Probability.finiteLogMGF_continuous productLaw objective) hderiv
    (by simp [Probability.finiteLogMGF, Probability.finiteMGF_zero]) hderiv_zero
    hdiff hfactor_all parameter hparameter le_rfl
  simpa only [productLaw, mean] using hsource

/-- Finite-PMF Chernoff's inequality, stated with the finite log-MGF.  This is
the direct Markov step for a strict upper-tail event. -/
theorem pmfProb_upperTail_le_exp_neg_mul_add_finiteLogMGF
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (score : α → ℝ) (threshold parameter : ℝ)
    (hparameter : 0 < parameter) :
    pmfProb law (fun outcome => threshold < score outcome) ≤
      Real.exp (-parameter * threshold +
        Probability.finiteLogMGF law score parameter) := by
  let exponentialScore : α → ℝ := fun outcome =>
    Real.exp (parameter * score outcome)
  have htail := pmfExp_ge_of_nonneg_of_tail law exponentialScore
    (Real.exp (parameter * threshold)) (fun outcome => Real.exp_nonneg _)
    (Real.exp_nonneg _)
  have hevent : ∀ outcome,
      Real.exp (parameter * threshold) < exponentialScore outcome ↔
        threshold < score outcome := by
    intro outcome
    change Real.exp (parameter * threshold) <
      Real.exp (parameter * score outcome) ↔ threshold < score outcome
    rw [Real.exp_lt_exp]
    constructor <;> intro h <;> nlinarith
  rw [pmfProb_congr law hevent] at htail
  have hmgf : pmfExp law exponentialScore =
      Probability.finiteMGF law score parameter := by
    unfold exponentialScore Probability.finiteMGF pmfExp
    congr with outcome
  rw [hmgf] at htail
  have hdivide :
      pmfProb law (fun outcome => threshold < score outcome) ≤
        Probability.finiteMGF law score parameter /
          Real.exp (parameter * threshold) := by
    exact (le_div_iff₀ (Real.exp_pos _)).2 (by
      simpa [mul_comm] using htail)
  rw [← Probability.exp_finiteLogMGF] at hdivide
  calc
    pmfProb law (fun outcome => threshold < score outcome) ≤
        Real.exp (Probability.finiteLogMGF law score parameter) /
          Real.exp (parameter * threshold) := hdivide
    _ = Real.exp (-parameter * threshold +
          Probability.finiteLogMGF law score parameter) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- The positive-mean upper-tail form of Maurer's self-bounding inequality on
a finite iid product.  The zero-mean boundary is separated because the
optimizing exponential parameter lies at the endpoint of the Herbst domain. -/
theorem FiniteSelfBounding.pmfProb_upperTail_le_exp
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale threshold : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 0 < scale) (hthreshold : 0 < threshold)
    (hmean : 0 < pmfExp (pmfProduct (Fin n) α law) objective) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law) objective + threshold < objective sample) ≤
      Real.exp (-threshold ^ 2 /
        (2 * scale * pmfExp (pmfProduct (Fin n) α law) objective + scale * threshold)) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let mean : ℝ := pmfExp productLaw objective
  let parameter : ℝ := threshold / (scale * (mean + threshold / 2))
  have hbase_pos : 0 < mean + threshold / 2 := by
    dsimp [mean]
    linarith
  have hbase_two_pos : 0 < mean * 2 + threshold := by
    linarith
  have hmean_pos : 0 < mean := by
    simpa [mean, productLaw] using hmean
  have hdenominator_pos : 0 < scale * (mean + threshold / 2) :=
    mul_pos hscale hbase_pos
  have hparameter : 0 < parameter := div_pos hthreshold hdenominator_pos
  have hfactor_eq : 1 - scale * parameter / 2 = mean / (mean + threshold / 2) := by
    apply (eq_div_iff hbase_pos.ne').2
    dsimp [parameter]
    field_simp [hscale.ne', hbase_two_pos.ne']
    ring
  have hfactor : 0 < 1 - scale * parameter / 2 := by
    rw [hfactor_eq]
    exact div_pos hmean_pos hbase_pos
  have hlog :
      Probability.finiteLogMGF productLaw (fun sample => objective sample - mean) parameter ≤
        scale * mean * parameter ^ 2 / (2 * (1 - scale * parameter / 2)) := by
    rw [Probability.finiteLogMGF_sub_const]
    calc
      Probability.finiteLogMGF productLaw objective parameter - parameter * mean ≤
          parameter * mean / (1 - scale * parameter / 2) - parameter * mean := by
        exact sub_le_sub_right
          (hself.finiteLogMGF_le hscale.le hparameter hfactor) _
      _ = scale * mean * parameter ^ 2 / (2 * (1 - scale * parameter / 2)) := by
        have hfactor_alt : 0 < 2 - parameter * scale := by
          nlinarith [hfactor]
        field_simp [hfactor_alt.ne']
        ring
  have hchernoff := pmfProb_upperTail_le_exp_neg_mul_add_finiteLogMGF
    productLaw (fun sample => objective sample - mean) threshold parameter hparameter
  have hevent : ∀ sample,
      threshold < objective sample - mean ↔ mean + threshold < objective sample := by
    intro sample
    constructor <;> intro h <;> linarith
  rw [pmfProb_congr productLaw hevent] at hchernoff
  calc
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample => pmfExp (pmfProduct (Fin n) α law) objective + threshold < objective sample) =
        pmfProb productLaw (fun sample => mean + threshold < objective sample) := by
      rfl
    _ ≤ Real.exp (-parameter * threshold +
        Probability.finiteLogMGF productLaw (fun sample => objective sample - mean) parameter) :=
      hchernoff
    _ ≤ Real.exp (-parameter * threshold +
        scale * mean * parameter ^ 2 / (2 * (1 - scale * parameter / 2))) := by
      apply Real.exp_monotone
      linarith
    _ = Real.exp (-threshold ^ 2 / (2 * scale * mean + scale * threshold)) := by
      congr 1
      rw [hfactor_eq]
      dsimp [parameter]
      have htail_denom_pos : 0 < 2 * scale * mean + scale * threshold := by
        nlinarith
      apply (eq_div_iff htail_denom_pos.ne').2
      field_simp [hscale.ne', hbase_two_pos.ne', hmean_pos.ne']
      ring
    _ = Real.exp (-threshold ^ 2 /
        (2 * scale * pmfExp (pmfProduct (Fin n) α law) objective + scale * threshold)) := by
      rfl

/-- At the zero-mean endpoint, a nonnegative self-bounding objective vanishes
on every positive-mass atom.  Thus every strictly positive upper-tail event
has probability zero. -/
theorem FiniteSelfBounding.pmfProb_upperTail_eq_zero_of_mean_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale threshold : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 0 < scale) (hthreshold : 0 < threshold)
    (hmean : pmfExp (pmfProduct (Fin n) α law) objective = 0) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law) objective + threshold < objective sample) = 0 := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  have hobjective_nonneg (sample : Fin n → α) : 0 ≤ objective sample :=
    hself.objective_nonneg_of_pos_scale hscale sample
  apply pmfProb_eq_zero_of_no_mass productLaw
  intro sample htail
  by_contra hmass_zero
  have hmass : 0 < (productLaw sample).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmass_zero)
  have hobjective_pos : 0 < objective sample := by
    change pmfExp productLaw objective + threshold < objective sample at htail
    rw [show pmfExp productLaw objective = 0 by simpa [productLaw] using hmean] at htail
    linarith
  have hterm_nonneg (outcome : Fin n → α) :
      0 ≤ (productLaw outcome).toReal * objective outcome :=
    mul_nonneg ENNReal.toReal_nonneg (hobjective_nonneg outcome)
  have hterm_pos :
      0 < (productLaw sample).toReal * objective sample :=
    mul_pos hmass hobjective_pos
  have hsum_pos :
      0 < ∑ outcome : Fin n → α,
        (productLaw outcome).toReal * objective outcome :=
    lt_of_lt_of_le hterm_pos
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin n → α)))
        (f := fun outcome => (productLaw outcome).toReal * objective outcome)
        (fun outcome _ => hterm_nonneg outcome) (Finset.mem_univ sample))
  have : 0 < pmfExp productLaw objective := by
    simpa [pmfExp] using hsum_pos
  rw [show pmfExp productLaw objective = 0 by simpa [productLaw] using hmean] at this
  exact (lt_irrefl 0 this)

/-- The finite self-bounding upper-tail theorem, including the zero-mean
boundary.  This is Maurer's `exp(-t²/(2a EZ + a t))` form for finite iid
products; no probabilistic certificate is assumed. -/
theorem FiniteSelfBounding.pmfProb_upperTail_le_exp_all
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {law : PMF α} {objective : (Fin n → α) → ℝ} {scale threshold : ℝ}
    (hself : FiniteSelfBounding objective scale)
    (hscale : 0 < scale) (hthreshold : 0 < threshold) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law) objective + threshold < objective sample) ≤
      Real.exp (-threshold ^ 2 /
        (2 * scale * pmfExp (pmfProduct (Fin n) α law) objective + scale * threshold)) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let mean : ℝ := pmfExp productLaw objective
  have hmean_nonneg : 0 ≤ mean :=
    pmfExp_nonneg_of_forall_nonneg productLaw objective
      (hself.objective_nonneg_of_pos_scale hscale)
  rcases eq_or_lt_of_le hmean_nonneg with hmean_zero | hmean_pos
  · have htail_zero := hself.pmfProb_upperTail_eq_zero_of_mean_eq_zero
      (law := law) hscale hthreshold
      (by simpa [mean, productLaw] using hmean_zero.symm)
    rw [htail_zero]
    exact Real.exp_nonneg _
  · exact hself.pmfProb_upperTail_le_exp hscale hthreshold
      (by simpa [mean, productLaw] using hmean_pos)

end AppliedModelingLib

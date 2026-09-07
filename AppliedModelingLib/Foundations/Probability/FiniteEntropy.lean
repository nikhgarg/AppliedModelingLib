import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Elementary finite entropy inequalities

The finite-product self-bounding concentration argument uses the elementary
function `exp (-t) + t - 1`.  This module records its quadratic upper bound
with an explicit real-calculus proof, so later entropy and product arguments
do not need to hide that analytic step behind a tail certificate.
-/

namespace AppliedModelingLib

/-- The finite entropy of a real-valued weight with respect to a PMF.  The
definition is used below only for nonnegative exponential weights, but keeping
the finite-sum expression total makes its product identities algebraic. -/
noncomputable def pmfFunctionalEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (weight : α → ℝ) : ℝ :=
  pmfExp law (fun outcome => weight outcome * Real.log (weight outcome)) -
    pmfExp law weight * Real.log (pmfExp law weight)

/-- For nonnegative `t`, the entropy-method remainder
`exp (-t) + t - 1` is at most `t^2 / 2`. -/
theorem exp_neg_add_sub_one_le_half_sq {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) + t - 1 ≤ t ^ 2 / 2 := by
  let remainder : ℝ → ℝ := fun x => x ^ 2 / 2 - (Real.exp (-x) + x - 1)
  have hderiv (x : ℝ) :
      HasDerivAt remainder (x + Real.exp (-x) - 1) x := by
    unfold remainder
    convert
      ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).sub
        (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).add
          (hasDerivAt_id x) |>.sub (hasDerivAt_const x 1)) using 1 <;> ring
  have hdiff : Differentiable ℝ remainder := fun x => (hderiv x).differentiableAt
  have hmono : MonotoneOn remainder (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      hdiff.continuous.continuousOn hdiff.differentiableOn (by
        intro x hx
        have hx0 : 0 ≤ x := Set.mem_Ici.mp (interior_subset hx)
        rw [(hderiv x).deriv]
        have hlinear := Real.one_sub_le_exp_neg x
        linarith)
  have hzero : 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have ht_mem : t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ht
  have hcompare := hmono hzero ht_mem ht
  simpa [remainder] using hcompare

/-- A one-coordinate entropy bound before the quadratic estimate.  It is the
finite PMF form of the elementary entropy inequality used in the upper-tail
half of the self-bounding argument. -/
theorem pmfFunctionalEntropy_exp_le_expNegDrop
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (score : α → ℝ) (parameter lower : ℝ) :
    pmfFunctionalEntropy law (fun outcome => Real.exp (parameter * score outcome)) ≤
      pmfExp law (fun outcome =>
        Real.exp (parameter * score outcome) *
          (Real.exp (-parameter * (score outcome - lower)) +
            parameter * (score outcome - lower) - 1)) := by
  let partition : ℝ := pmfExp law (fun outcome => Real.exp (parameter * score outcome))
  have hpartition_nonneg : 0 ≤ partition := by
    exact pmfExp_nonneg_of_forall_nonneg law _ (fun outcome => (Real.exp_pos _).le)
  have hlower_exp_pos : 0 < Real.exp (parameter * lower) := Real.exp_pos _
  have hlog_tangent := mass_sub_le_mul_log_mass_ratio
    hpartition_nonneg hlower_exp_pos
  change partition - Real.exp (parameter * lower) ≤
    partition * (Real.log partition - Real.log (Real.exp (parameter * lower))) at hlog_tangent
  rw [Real.log_exp] at hlog_tangent
  have hfirst :
      pmfExp law (fun outcome =>
        Real.exp (parameter * score outcome) *
          Real.exp (-parameter * (score outcome - lower))) =
        Real.exp (parameter * lower) := by
    calc
      pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) *
            Real.exp (-parameter * (score outcome - lower))) =
          pmfExp law (fun _outcome => Real.exp (parameter * lower)) := by
            apply pmfExp_congr
            intro outcome
            rw [← Real.exp_add]
            congr 1
            ring
      _ = Real.exp (parameter * lower) := pmfExp_const _ _
  have hsecond :
      pmfExp law (fun outcome =>
        Real.exp (parameter * score outcome) *
          (parameter * score outcome - parameter * lower - 1)) =
        pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) * (parameter * score outcome)) -
          partition * (parameter * lower) - partition := by
    calc
      pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) *
            (parameter * score outcome - parameter * lower - 1)) =
          pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) * (parameter * score outcome) -
              Real.exp (parameter * score outcome) * (parameter * lower) -
                Real.exp (parameter * score outcome)) := by
            apply pmfExp_congr
            intro outcome
            ring
      _ = pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) * (parameter * score outcome)) -
            pmfExp law (fun outcome =>
              Real.exp (parameter * score outcome) * (parameter * lower)) -
              pmfExp law (fun outcome => Real.exp (parameter * score outcome)) := by
            rw [pmfExp_sub, pmfExp_sub]
      _ = pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) * (parameter * score outcome)) -
            partition * (parameter * lower) - partition := by
            rw [pmfExp_mul_const]
  have hright :
      pmfExp law (fun outcome =>
        Real.exp (parameter * score outcome) *
          (Real.exp (-parameter * (score outcome - lower)) +
            parameter * (score outcome - lower) - 1)) =
        Real.exp (parameter * lower) +
          (pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) * (parameter * score outcome)) -
            partition * (parameter * lower) - partition) := by
    calc
      pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) *
            (Real.exp (-parameter * (score outcome - lower)) +
              parameter * (score outcome - lower) - 1)) =
          pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) *
              Real.exp (-parameter * (score outcome - lower)) +
            Real.exp (parameter * score outcome) *
              (parameter * score outcome - parameter * lower - 1)) := by
            apply pmfExp_congr
            intro outcome
            ring
      _ = pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) *
              Real.exp (-parameter * (score outcome - lower))) +
            pmfExp law (fun outcome =>
              Real.exp (parameter * score outcome) *
                (parameter * score outcome - parameter * lower - 1)) := by
            rw [pmfExp_add]
      _ = Real.exp (parameter * lower) +
          (pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) * (parameter * score outcome)) -
            partition * (parameter * lower) - partition) := by
            rw [hfirst, hsecond]
  unfold pmfFunctionalEntropy
  simp_rw [Real.log_exp]
  change
    pmfExp law (fun outcome =>
      Real.exp (parameter * score outcome) * (parameter * score outcome)) -
        partition * Real.log partition ≤ _
  rw [hright]
  nlinarith

/-- The preceding entropy bound combined with the quadratic control of the
entropy remainder. -/
theorem pmfFunctionalEntropy_exp_le_half_sq_drop
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (score : α → ℝ) (parameter lower : ℝ)
    (hparameter : 0 ≤ parameter) (hlower : ∀ outcome, lower ≤ score outcome) :
    pmfFunctionalEntropy law (fun outcome => Real.exp (parameter * score outcome)) ≤
      (parameter ^ 2 / 2) *
        pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) * (score outcome - lower) ^ 2) := by
  calc
    pmfFunctionalEntropy law (fun outcome => Real.exp (parameter * score outcome)) ≤
        pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) *
            (Real.exp (-parameter * (score outcome - lower)) +
              parameter * (score outcome - lower) - 1)) :=
        pmfFunctionalEntropy_exp_le_expNegDrop law score parameter lower
    _ ≤ pmfExp law (fun outcome =>
          Real.exp (parameter * score outcome) *
            ((parameter * (score outcome - lower)) ^ 2 / 2)) := by
          apply pmfExp_le_pmfExp_of_forall_le
          intro outcome
          have hdrop : 0 ≤ parameter * (score outcome - lower) :=
            mul_nonneg hparameter (sub_nonneg.mpr (hlower outcome))
          gcongr
          convert exp_neg_add_sub_one_le_half_sq hdrop using 1 <;> ring
    _ = (parameter ^ 2 / 2) *
          pmfExp law (fun outcome =>
            Real.exp (parameter * score outcome) * (score outcome - lower) ^ 2) := by
          rw [← pmfExp_const_mul]
          apply pmfExp_congr
          intro outcome
          ring

/-- Entropy under a two-coordinate independent product decomposes into the
entropy of the first conditional mean plus the mean conditional entropy. -/
theorem pmfFunctionalEntropy_pmfProd_decompose
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (first : PMF α) (second : PMF β) (weight : α → β → ℝ) :
    pmfFunctionalEntropy (pmfProd first second) (fun pair => weight pair.1 pair.2) =
      pmfFunctionalEntropy first (fun left => pmfExp second (fun right => weight left right)) +
        pmfExp first (fun left =>
          pmfFunctionalEntropy second (fun right => weight left right)) := by
  unfold pmfFunctionalEntropy
  rw [pmfExp_pmfProd_eq_pairExp, pmfExp_pmfProd_eq_pairExp]
  unfold pmfPairExp
  rw [pmfExp_sub]
  ring

/-- The entropy decomposition when one iid coordinate is exposed from a
finite product.  It is the recursive form needed for product tensorization. -/
theorem pmfFunctionalEntropy_pmfProduct_option_decompose
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (law : PMF α) (weight : (Option ι → α) → ℝ) :
    pmfFunctionalEntropy (pmfProduct (Option ι) α law) weight =
      pmfFunctionalEntropy (pmfProduct ι α law)
        (fun oldSample => pmfExp law (fun newValue =>
          weight (extendDraw oldSample newValue))) +
        pmfExp (pmfProduct ι α law) (fun oldSample =>
          pmfFunctionalEntropy law (fun newValue =>
            weight (extendDraw oldSample newValue))) := by
  unfold pmfFunctionalEntropy
  rw [pmfExp_pmfProduct_option_eq_pairExp,
    pmfExp_pmfProduct_option_eq_pairExp]
  unfold pmfPairExp
  rw [pmfExp_sub]
  ring

end AppliedModelingLib

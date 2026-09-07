import PRPKG24AccuracyDiversity.MainTheorems

/-!
# Appendix D.1 source-model route

The printed generic Lemma D.1 is not used as a black-box theorem here.  Its
part (i) has inconsistent displayed signs and its proof relies on stronger
interiority facts than its statement supplies.  This module instead records
the direct finite-discrete iid source-model route used by Theorem 1(i): the
literal fixed-total integer optimizer is compared through the finite binomial
top-support marginal bounds.

This is intentionally *not* a formalization of generic Lemma D.1(i).  It is a
checked downstream application under explicit finite-support assumptions.
-/

namespace PRPKG24AccuracyDiversity

/--
The finite-discrete iid source-model application of Appendix D.1(i).

`itemLaw` is a literal finite conditional item-value law.  The top-support
split makes `xTop` the strictly better top value, with positive top and
non-top mass.  The conclusion is obtained from the actual separable integer
optimization problem, not from an assumed limiting objective or an optimizer
convergence certificate.
-/
theorem lemmaD1_i_finiteDiscrete_iid_source_uniform_homogeneity
    {T : ℕ} [NeZero T] {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (itemLaw : PMF Omega) (value : Omega -> ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T -> ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
              likelihood k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ omega, value omega ≤ xTop)
    (hvalue_split : ∀ omega, value omega = xTop ∨ value omega ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => value omega = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => ¬ value omega = xTop))
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
  paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_top_split
    itemLaw value likelihood k seq hk_pos hxTop_pos hxSecond_nonneg
    hsecond_le_top hsecond_lt_top hvalue_le hvalue_split htop_mass_pos
    hnontop_mass_pos hlike_pos

/--
Equation-(6) form of the direct finite-discrete iid Appendix-D.1 application.
The target is the source's `0`-homogeneity profile: each positive-likelihood
type receives asymptotic representation `1 / T`.
-/
theorem lemmaD1_i_finiteDiscrete_iid_source_uniform_formula
    {T : ℕ} [NeZero T] {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (itemLaw : PMF Omega) (value : Omega -> ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T -> ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
              likelihood k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ omega, value omega ≤ xTop)
    (hvalue_split : ∀ omega, value omega = xTop ∨ value omega ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => value omega = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => ¬ value omega = xTop))
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    lemmaD1_i_finiteDiscrete_iid_source_uniform_homogeneity
      itemLaw value likelihood k seq hk_pos hxTop_pos hxSecond_nonneg
      hsecond_le_top hsecond_lt_top hvalue_le hvalue_split htop_mass_pos
      hnontop_mass_pos hlike_pos
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using hconv t

end PRPKG24AccuracyDiversity

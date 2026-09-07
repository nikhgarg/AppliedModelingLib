import Mathlib.Analysis.SpecialFunctions.Pow.Real
import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.FiniteSupportMGF

/-!
# Finite geometric mixtures

The geometric mixture of two full-support finite PMFs assigns mass
proportional to `first(a)^(1 - mixWeight) * second(a)^mixWeight`.  It is the
regularized opponent policy used by Nash-MD.  Full-support assumptions are
explicit because real powers and log identities need positive base masses.

## Main declarations

- `geometricMixturePartition`
- `geometricMixture`
- `geometricMixture_fullSupport`
- `geometricMixture_zero`
- `geometricMixture_one`
- `geometricMixture_log_mass`
-/

open scoped BigOperators

namespace AppliedModelingLib

/-- Normalizing partition function for a finite geometric mixture. -/
noncomputable def geometricMixturePartition
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ) : ℝ :=
  ∑ outcome : Outcome,
    (first outcome).toReal ^ (1 - mixWeight) * (second outcome).toReal ^ mixWeight

/-- The geometric-mixture partition function is positive for full-support inputs. -/
theorem geometricMixturePartition_pos
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) :
    0 < geometricMixturePartition first second mixWeight := by
  unfold geometricMixturePartition
  rcases Probability.exists_pmf_toReal_pos first with ⟨outcome, houtcome⟩
  refine Finset.sum_pos' ?_ ?_
  · intro outcome _
    exact mul_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  · refine ⟨outcome, Finset.mem_univ outcome, ?_⟩
    exact mul_pos
      (Real.rpow_pos_of_pos (hfirst outcome) _)
      (Real.rpow_pos_of_pos (hsecond outcome) _)

/-- A normalized geometric mixture of two full-support finite PMFs. -/
noncomputable def geometricMixture
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) : PMF Outcome :=
  PMF.ofFintype
    (fun outcome : Outcome =>
      ENNReal.ofReal
        ((first outcome).toReal ^ (1 - mixWeight) *
          (second outcome).toReal ^ mixWeight /
          geometricMixturePartition first second mixWeight))
    (by
      classical
      have hterm_nonneg : ∀ outcome : Outcome,
          0 ≤ (first outcome).toReal ^ (1 - mixWeight) *
            (second outcome).toReal ^ mixWeight /
            geometricMixturePartition first second mixWeight := by
        intro outcome
        exact div_nonneg
          (mul_nonneg
            (Real.rpow_nonneg ENNReal.toReal_nonneg _)
            (Real.rpow_nonneg ENNReal.toReal_nonneg _))
          (geometricMixturePartition_pos first second mixWeight hfirst hsecond).le
      have hsum_real :
          (∑ outcome : Outcome,
            (first outcome).toReal ^ (1 - mixWeight) *
              (second outcome).toReal ^ mixWeight /
              geometricMixturePartition first second mixWeight) = 1 := by
        rw [← Finset.sum_div]
        simpa [geometricMixturePartition] using
          div_self (geometricMixturePartition_pos first second mixWeight hfirst hsecond).ne'
      calc
        (∑ outcome : Outcome,
          ENNReal.ofReal
            ((first outcome).toReal ^ (1 - mixWeight) *
              (second outcome).toReal ^ mixWeight /
              geometricMixturePartition first second mixWeight)) =
            ENNReal.ofReal
              (∑ outcome : Outcome,
                (first outcome).toReal ^ (1 - mixWeight) *
                  (second outcome).toReal ^ mixWeight /
                  geometricMixturePartition first second mixWeight) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset Outcome))
                (f := fun outcome : Outcome =>
                  (first outcome).toReal ^ (1 - mixWeight) *
                    (second outcome).toReal ^ mixWeight /
                    geometricMixturePartition first second mixWeight)
                (by intro outcome _; exact hterm_nonneg outcome)
        _ = 1 := by rw [hsum_real]; norm_num)

/-- Real mass formula for the finite geometric mixture. -/
@[simp] theorem geometricMixture_apply_toReal
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second)
    (outcome : Outcome) :
    (geometricMixture first second mixWeight hfirst hsecond outcome).toReal =
      (first outcome).toReal ^ (1 - mixWeight) *
        (second outcome).toReal ^ mixWeight /
        geometricMixturePartition first second mixWeight := by
  unfold geometricMixture
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg
      (mul_nonneg
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (geometricMixturePartition_pos first second mixWeight hfirst hsecond).le)

/-- A geometric mixture of full-support PMFs has full support. -/
theorem geometricMixture_fullSupport
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) :
    PMFFullSupport (geometricMixture first second mixWeight hfirst hsecond) := by
  intro outcome
  rw [geometricMixture_apply_toReal]
  exact div_pos
    (mul_pos
      (Real.rpow_pos_of_pos (hfirst outcome) _)
      (Real.rpow_pos_of_pos (hsecond outcome) _))
    (geometricMixturePartition_pos first second mixWeight hfirst hsecond)

/-- The zero-weight geometric mixture is its first input. -/
theorem geometricMixture_zero
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) :
    geometricMixture first second 0 hfirst hsecond = first := by
  have hpartition : geometricMixturePartition first second 0 = 1 := by
    unfold geometricMixturePartition
    simpa using pmfToRealSum first
  apply PMF.ext
  intro outcome
  apply (ENNReal.toReal_eq_toReal_iff'
    ((geometricMixture first second 0 hfirst hsecond).apply_ne_top outcome)
    (first.apply_ne_top outcome)).mp
  rw [geometricMixture_apply_toReal, hpartition]
  simp

/-- The unit-weight geometric mixture is its second input. -/
theorem geometricMixture_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) :
    geometricMixture first second 1 hfirst hsecond = second := by
  have hpartition : geometricMixturePartition first second 1 = 1 := by
    unfold geometricMixturePartition
    simpa using pmfToRealSum second
  apply PMF.ext
  intro outcome
  apply (ENNReal.toReal_eq_toReal_iff'
    ((geometricMixture first second 1 hfirst hsecond).apply_ne_top outcome)
    (second.apply_ne_top outcome)).mp
  rw [geometricMixture_apply_toReal, hpartition]
  simp

/-- Log mass of a geometric mixture equals the weighted log masses minus log partition. -/
theorem geometricMixture_log_mass
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second)
    (outcome : Outcome) :
    Real.log (geometricMixture first second mixWeight hfirst hsecond outcome).toReal =
      (1 - mixWeight) * Real.log (first outcome).toReal +
        mixWeight * Real.log (second outcome).toReal -
          Real.log (geometricMixturePartition first second mixWeight) := by
  rw [geometricMixture_apply_toReal]
  have hfirst_pos : 0 < (first outcome).toReal := hfirst outcome
  have hsecond_pos : 0 < (second outcome).toReal := hsecond outcome
  have hpartition_pos : 0 < geometricMixturePartition first second mixWeight :=
    geometricMixturePartition_pos first second mixWeight hfirst hsecond
  rw [Real.log_div
    (mul_ne_zero
      (Real.rpow_pos_of_pos hfirst_pos _).ne'
      (Real.rpow_pos_of_pos hsecond_pos _).ne')
    hpartition_pos.ne']
  rw [Real.log_mul
    (Real.rpow_pos_of_pos hfirst_pos _).ne'
    (Real.rpow_pos_of_pos hsecond_pos _).ne']
  rw [Real.log_rpow hfirst_pos, Real.log_rpow hsecond_pos]

/--
KL divergence against a full-support geometric mixture decomposes into the two
reference KL divergences plus the mixture's log partition.  This is the
finite identity underlying the geometric-opponent estimate in Appendix D of
Munos et al. (2024).
-/
theorem finiteKLDivergence_geometricMixture
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (target first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) :
    finiteKLDivergence target (geometricMixture first second mixWeight hfirst hsecond) =
      (1 - mixWeight) * finiteKLDivergence target first +
        mixWeight * finiteKLDivergence target second +
          Real.log (geometricMixturePartition first second mixWeight) := by
  classical
  unfold finiteKLDivergence
  calc
    ∑ outcome : Outcome,
        (target outcome).toReal *
          (Real.log (target outcome).toReal -
            Real.log (geometricMixture first second mixWeight hfirst hsecond outcome).toReal) =
        ∑ outcome : Outcome,
          ((1 - mixWeight) *
              ((target outcome).toReal *
                (Real.log (target outcome).toReal - Real.log (first outcome).toReal)) +
            mixWeight *
              ((target outcome).toReal *
                (Real.log (target outcome).toReal - Real.log (second outcome).toReal)) +
            (target outcome).toReal *
              Real.log (geometricMixturePartition first second mixWeight)) := by
          refine Finset.sum_congr rfl ?_
          intro outcome _
          rw [geometricMixture_log_mass first second mixWeight hfirst hsecond outcome]
          ring
    _ = (1 - mixWeight) *
          ∑ outcome : Outcome,
            (target outcome).toReal *
              (Real.log (target outcome).toReal - Real.log (first outcome).toReal) +
        mixWeight *
          ∑ outcome : Outcome,
            (target outcome).toReal *
              (Real.log (target outcome).toReal - Real.log (second outcome).toReal) +
          (∑ outcome : Outcome, (target outcome).toReal) *
            Real.log (geometricMixturePartition first second mixWeight) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = (1 - mixWeight) *
          ∑ outcome : Outcome,
            (target outcome).toReal *
              (Real.log (target outcome).toReal - Real.log (first outcome).toReal) +
        mixWeight *
          ∑ outcome : Outcome,
            (target outcome).toReal *
              (Real.log (target outcome).toReal - Real.log (second outcome).toReal) +
          Real.log (geometricMixturePartition first second mixWeight) := by
          rw [pmfToRealSum]
          ring

/--
The log partition of a geometric mixture is at most negative the mixture
weight times its KL divergence to the second reference law.  The upper bound
uses only the finite Gibbs inequality and a mix weight at most one.
-/
theorem geometricMixture_logPartition_le_neg_mul_finiteKLDivergence
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second)
    (hmixWeight_one : mixWeight ≤ 1) :
    Real.log (geometricMixturePartition first second mixWeight) ≤
      -mixWeight *
        finiteKLDivergence (geometricMixture first second mixWeight hfirst hsecond) second := by
  have hidentity := finiteKLDivergence_geometricMixture
    (geometricMixture first second mixWeight hfirst hsecond) first second mixWeight hfirst hsecond
  rw [finiteKLDivergence_self] at hidentity
  have hkl_nonneg := finiteKLDivergence_nonneg
    (geometricMixture first second mixWeight hfirst hsecond) first hfirst
  have hcoefficient_nonneg : 0 ≤ 1 - mixWeight := by linarith
  nlinarith [mul_nonneg hcoefficient_nonneg hkl_nonneg]

/--
Finite geometric-mixture KL inequality.  For a mix weight in `[0, 1]`, the
KL divergence to the geometric mixture is bounded by the corresponding
weighted KL divergences minus the mixture's second-reference KL term.  This
is the exact finite form of Appendix D, Lemma 1 of Munos et al. (2024).
-/
theorem finiteKLDivergence_geometricMixture_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (target first second : PMF Outcome) (mixWeight : ℝ)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second)
    (hmixWeight_nonneg : 0 ≤ mixWeight) (hmixWeight_one : mixWeight ≤ 1) :
    finiteKLDivergence target (geometricMixture first second mixWeight hfirst hsecond) ≤
      mixWeight * finiteKLDivergence target second +
        (1 - mixWeight) * finiteKLDivergence target first -
          mixWeight *
            finiteKLDivergence (geometricMixture first second mixWeight hfirst hsecond) second := by
  have hidentity := finiteKLDivergence_geometricMixture target first second mixWeight
    hfirst hsecond
  have hpartition := geometricMixture_logPartition_le_neg_mul_finiteKLDivergence
    first second mixWeight hfirst hsecond hmixWeight_one
  rw [hidentity]
  linarith [hmixWeight_nonneg]

end AppliedModelingLib

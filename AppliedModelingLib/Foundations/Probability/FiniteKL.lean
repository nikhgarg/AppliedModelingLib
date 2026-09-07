import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite Kullback--Leibler divergence

This module supplies the finite real-valued KL expression used by the
learning-and-alignment core.  Mathlib's `InformationTheory.klDiv` remains the
general measure-theoretic definition; this finite API is for transparent
finite-sum arguments over `PMF`s.

The first law need not have full support.  A zero first-law mass contributes
zero, using Mathlib's `Real.log 0 = 0` convention.  The second law's full
support is an explicit hypothesis of every theorem that interprets the sum as
a finite divergence.

## Main declarations

- `PMFFullSupport`
- `PMFAbsoluteContinuous`
- `finiteKLDivergence`
- `finiteKLDivergence_self`
- `finiteKLDivergence_nonneg`
- `finiteKLDivergence_pos_of_ne`
- `finiteKLDivergence_eq_zero_iff`
-/

open scoped BigOperators

namespace AppliedModelingLib

/-- Every atom of a finite probability mass function has strictly positive real mass. -/
def PMFFullSupport {α : Type*} (law : PMF α) : Prop :=
  ∀ outcome, 0 < (law outcome).toReal

/-- Every positive-mass atom of the first PMF also has positive mass under the second PMF. -/
def PMFAbsoluteContinuous {α : Type*} (first second : PMF α) : Prop :=
  ∀ outcome, 0 < (first outcome).toReal → 0 < (second outcome).toReal

/-- A full-support reference PMF is absolutely continuous with respect to every PMF. -/
theorem pmfAbsoluteContinuous_of_fullSupport {α : Type*} (first second : PMF α)
    (hsecond : PMFFullSupport second) :
    PMFAbsoluteContinuous first second := fun outcome _ => hsecond outcome

/-- The finite real-valued KL expression between two probability mass functions. -/
noncomputable def finiteKLDivergence {α : Type*} [Fintype α] [DecidableEq α]
    (first second : PMF α) : ℝ :=
  ∑ outcome : α,
    (first outcome).toReal *
      (Real.log (first outcome).toReal - Real.log (second outcome).toReal)

/-- The finite Shannon entropy, with the standard zero-mass contribution
given by Mathlib's `Real.log 0 = 0` convention. -/
noncomputable def finiteEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) : ℝ :=
  -∑ outcome : α, (law outcome).toReal * Real.log (law outcome).toReal

/-- Cross entropy of a finite law against a reference law.  The definition is
real-valued for every PMF; results interpreting it through KL make the
reference's full support explicit. -/
noncomputable def finiteCrossEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (law reference : PMF α) : ℝ :=
  -∑ outcome : α, (law outcome).toReal * Real.log (reference outcome).toReal

/-- Extended-real cross entropy with the usual information-theoretic boundary
convention: a reference assigning zero mass to a positive-mass data atom has
cost `⊤`.  On absolutely continuous pairs this agrees with the finite real
sum `finiteCrossEntropy`. -/
noncomputable def finiteCrossEntropyExtended {α : Type*} [Fintype α] [DecidableEq α]
    (law reference : PMF α) : WithTop ℝ := by
  classical
  exact if PMFAbsoluteContinuous law reference then finiteCrossEntropy law reference else ⊤

/-- The finite cross-entropy identity: cross entropy is entropy plus KL. -/
theorem finiteCrossEntropy_eq_entropy_add_kl {α : Type*} [Fintype α] [DecidableEq α]
    (law reference : PMF α) :
    finiteCrossEntropy law reference =
      finiteEntropy law + finiteKLDivergence law reference := by
  unfold finiteCrossEntropy finiteEntropy finiteKLDivergence
  calc
    -(∑ outcome : α, (law outcome).toReal * Real.log (reference outcome).toReal) =
        ∑ outcome : α,
          -((law outcome).toReal * Real.log (reference outcome).toReal) := by
            rw [← Finset.sum_neg_distrib]
    _ = ∑ outcome : α,
        (-((law outcome).toReal * Real.log (law outcome).toReal) +
          (law outcome).toReal *
            (Real.log (law outcome).toReal - Real.log (reference outcome).toReal)) := by
            refine Finset.sum_congr rfl fun outcome _ => ?_
            ring
    _ = -(∑ outcome : α, (law outcome).toReal * Real.log (law outcome).toReal) +
          ∑ outcome : α, (law outcome).toReal *
            (Real.log (law outcome).toReal - Real.log (reference outcome).toReal) := by
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

/--
The pointwise tangent lower bound underlying finite Gibbs inequalities.  It is
stated separately because event- and clone-mass KL estimates use the same
one-line bound on the complement of their distinguished event.
-/
theorem mass_sub_le_mul_log_mass_ratio {firstMass referenceMass : ℝ}
    (hfirst_nonneg : 0 ≤ firstMass) (href_pos : 0 < referenceMass) :
    firstMass - referenceMass ≤
      firstMass * (Real.log firstMass - Real.log referenceMass) := by
  by_cases hfirst_zero : firstMass = 0
  · simp [hfirst_zero, href_pos.le]
  · have hfirst_pos : 0 < firstMass := lt_of_le_of_ne hfirst_nonneg (Ne.symm hfirst_zero)
    have hlog := Real.one_sub_inv_le_log_of_pos
      (div_pos hfirst_pos href_pos)
    have hmul := mul_le_mul_of_nonneg_left hlog hfirst_nonneg
    calc
      firstMass - referenceMass =
          firstMass * (1 - (firstMass / referenceMass)⁻¹) := by
            field_simp [hfirst_pos.ne', href_pos.ne']
      _ ≤ firstMass * Real.log (firstMass / referenceMass) := hmul
      _ = firstMass * (Real.log firstMass - Real.log referenceMass) := by
            rw [Real.log_div hfirst_pos.ne' href_pos.ne']

/-- KL divergence from a deterministic finite policy is the negative log mass
that its reference policy assigns to the selected outcome. -/
@[simp] theorem finiteKLDivergence_pure {α : Type*} [Fintype α] [DecidableEq α]
    (reference : PMF α) (outcome : α) :
    finiteKLDivergence (PMF.pure outcome) reference =
      -Real.log (reference outcome).toReal := by
  change pmfExp (PMF.pure outcome) (fun other : α =>
    Real.log ((PMF.pure outcome other).toReal) - Real.log (reference other).toReal) = _
  rw [pmfExp_pure]
  simp [PMF.pure_apply]

/-- KL divergence from a finite law to itself is zero. -/
@[simp] theorem finiteKLDivergence_self {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) :
    finiteKLDivergence law law = 0 := by
  unfold finiteKLDivergence
  refine Finset.sum_eq_zero fun outcome _ => ?_
  ring

/-- The KL divergence of any finite law from the uniform reference is at most
the logarithm of the finite support size.  Thus a KL ball of radius
`log |α|` around a uniform reference contains every policy on `α`. -/
theorem finiteKLDivergence_uniform_le_log_card
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (law : PMF α) :
    finiteKLDivergence law (uniformPMF α) ≤ Real.log (Fintype.card α : ℝ) := by
  have hsum : ∑ outcome : α, (law outcome).toReal = 1 := pmfToRealSum law
  have hentropy : ∑ outcome : α,
      (law outcome).toReal * Real.log (law outcome).toReal ≤ 0 := by
    apply Finset.sum_nonpos
    intro outcome _
    exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
      (Real.log_nonpos ENNReal.toReal_nonneg (pmf_apply_toReal_le_one law outcome))
  have huniform_log : ∀ outcome : α,
      Real.log ((uniformPMF α outcome).toReal) = -Real.log (Fintype.card α : ℝ) := by
    intro outcome
    rw [uniformPMF_apply_toReal, Real.log_inv]
  unfold finiteKLDivergence
  simp_rw [huniform_log]
  calc
    (∑ outcome : α, (law outcome).toReal *
        (Real.log (law outcome).toReal - -Real.log (Fintype.card α : ℝ))) =
        ∑ outcome : α, ((law outcome).toReal * Real.log (law outcome).toReal +
          (law outcome).toReal * Real.log (Fintype.card α : ℝ)) := by
            refine Finset.sum_congr rfl fun outcome _ => ?_
            ring
    _ =
        (∑ outcome : α, (law outcome).toReal * Real.log (law outcome).toReal) +
          (∑ outcome : α, (law outcome).toReal) * Real.log (Fintype.card α : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = (∑ outcome : α, (law outcome).toReal * Real.log (law outcome).toReal) +
          Real.log (Fintype.card α : ℝ) := by rw [hsum]; ring
    _ ≤ Real.log (Fintype.card α : ℝ) := by linarith

/--
The finite KL expression is nonnegative when its reference PMF has full
support.  This is the finite-sum Gibbs inequality; no probability-space
assumption is used.
-/
theorem finiteKLDivergence_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (first second : PMF α) (hsecond : PMFFullSupport second) :
    0 ≤ finiteKLDivergence first second := by
  classical
  unfold finiteKLDivergence
  have hterm : ∀ outcome : α,
      (first outcome).toReal - (second outcome).toReal ≤
        (first outcome).toReal *
          (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
    intro outcome
    by_cases hfirst_zero : (first outcome).toReal = 0
    · have hsecond_nonneg : 0 ≤ (second outcome).toReal := (hsecond outcome).le
      simp [hfirst_zero, hsecond_nonneg]
    · have hfirst_pos : 0 < (first outcome).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirst_zero)
      have hsecond_pos : 0 < (second outcome).toReal := hsecond outcome
      have hlog := Real.one_sub_inv_le_log_of_pos
        (div_pos hfirst_pos hsecond_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hfirst_pos.le
      calc
        (first outcome).toReal - (second outcome).toReal
            = (first outcome).toReal *
                (1 - ((first outcome).toReal / (second outcome).toReal)⁻¹) := by
                field_simp [hfirst_pos.ne', hsecond_pos.ne']
        _ ≤ (first outcome).toReal *
              Real.log ((first outcome).toReal / (second outcome).toReal) := hmul
        _ = (first outcome).toReal *
              (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
                rw [Real.log_div hfirst_pos.ne' hsecond_pos.ne']
  calc
    0 = (∑ outcome : α, (first outcome).toReal) -
          ∑ outcome : α, (second outcome).toReal := by
          rw [pmfToRealSum, pmfToRealSum]
          norm_num
    _ = ∑ outcome : α, ((first outcome).toReal - (second outcome).toReal) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ outcome : α,
          (first outcome).toReal *
            (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
          exact Finset.sum_le_sum fun outcome _ => hterm outcome

/-- The finite KL expression is nonnegative whenever the first PMF is
absolutely continuous with respect to the second.  Unlike
`finiteKLDivergence_nonneg`, the reference may vanish away from the support
of the first PMF. -/
theorem finiteKLDivergence_nonneg_of_absoluteContinuous
    {α : Type*} [Fintype α] [DecidableEq α]
    (first second : PMF α) (hcontinuous : PMFAbsoluteContinuous first second) :
    0 ≤ finiteKLDivergence first second := by
  classical
  unfold finiteKLDivergence
  have hterm : ∀ outcome : α,
      (first outcome).toReal - (second outcome).toReal ≤
        (first outcome).toReal *
          (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
    intro outcome
    by_cases hsecond_zero : (second outcome).toReal = 0
    · have hfirst_not_pos : ¬ 0 < (first outcome).toReal := by
        intro hfirst_pos
        have hsecond_pos := hcontinuous outcome hfirst_pos
        rw [hsecond_zero] at hsecond_pos
        exact lt_irrefl _ hsecond_pos
      have hfirst_zero : (first outcome).toReal = 0 :=
        le_antisymm (le_of_not_gt hfirst_not_pos) ENNReal.toReal_nonneg
      simp [hfirst_zero, hsecond_zero]
    · have hsecond_pos : 0 < (second outcome).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hsecond_zero)
      exact mass_sub_le_mul_log_mass_ratio ENNReal.toReal_nonneg hsecond_pos
  calc
    0 = (∑ outcome : α, (first outcome).toReal) -
          ∑ outcome : α, (second outcome).toReal := by
          rw [pmfToRealSum, pmfToRealSum]
          norm_num
    _ = ∑ outcome : α, ((first outcome).toReal - (second outcome).toReal) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ outcome : α,
          (first outcome).toReal *
            (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
          exact Finset.sum_le_sum fun outcome _ => hterm outcome

/-- Cross entropy is at least entropy when the data law is absolutely
continuous with respect to the reference law. -/
theorem finiteEntropy_le_finiteCrossEntropy_of_absoluteContinuous
    {α : Type*} [Fintype α] [DecidableEq α]
    (law reference : PMF α) (hcontinuous : PMFAbsoluteContinuous law reference) :
    finiteEntropy law ≤ finiteCrossEntropy law reference := by
  rw [finiteCrossEntropy_eq_entropy_add_kl]
  linarith [finiteKLDivergence_nonneg_of_absoluteContinuous law reference hcontinuous]

/-- Extended cross entropy is at least entropy, including when the reference
misses a positive-mass data atom (where its value is `⊤`). -/
theorem coe_finiteEntropy_le_finiteCrossEntropyExtended
    {α : Type*} [Fintype α] [DecidableEq α]
    (law reference : PMF α) :
    (finiteEntropy law : WithTop ℝ) ≤ finiteCrossEntropyExtended law reference := by
  classical
  by_cases hcontinuous : PMFAbsoluteContinuous law reference
  · rw [finiteCrossEntropyExtended, if_pos hcontinuous]
    exact WithTop.coe_le_coe.mpr
      (finiteEntropy_le_finiteCrossEntropy_of_absoluteContinuous law reference hcontinuous)
  · rw [finiteCrossEntropyExtended, if_neg hcontinuous]
    exact le_top

@[simp] theorem finiteCrossEntropyExtended_self {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) : finiteCrossEntropyExtended law law = finiteEntropy law := by
  classical
  have hcontinuous : PMFAbsoluteContinuous law law := fun _ hpositive => hpositive
  rw [finiteCrossEntropyExtended, if_pos hcontinuous]
  exact congrArg (fun value : ℝ => (value : WithTop ℝ)) (by
    rw [finiteCrossEntropy_eq_entropy_add_kl, finiteKLDivergence_self, add_zero])

/-- The range of extended-real cross entropy as the reference ranges over all
finite probability mass functions. -/
noncomputable def finiteCrossEntropyExtendedRange
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) : Set (WithTop ℝ) :=
  { value | ∃ reference : PMF α, value = finiteCrossEntropyExtended law reference }

/-- The source-faithful closed-simplex entropy variational identity.  This is
Appendix Fact 5's finite statement: the infimum is over all reference PMFs,
and zero reference mass at a positive-mass data atom has extended-real cost.
-/
theorem sInf_finiteCrossEntropyExtendedRange_eq_entropy
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) :
    sInf (finiteCrossEntropyExtendedRange law) = finiteEntropy law := by
  have hself : (finiteEntropy law : WithTop ℝ) ∈ finiteCrossEntropyExtendedRange law := by
    exact ⟨law, finiteCrossEntropyExtended_self law |>.symm⟩
  have hnonempty : (finiteCrossEntropyExtendedRange law).Nonempty := ⟨_, hself⟩
  have hlower : ∀ value ∈ finiteCrossEntropyExtendedRange law,
      (finiteEntropy law : WithTop ℝ) ≤ value := by
    intro value hvalue
    rcases hvalue with ⟨reference, rfl⟩
    exact coe_finiteEntropy_le_finiteCrossEntropyExtended law reference
  have hbdd : BddBelow (finiteCrossEntropyExtendedRange law) :=
    ⟨finiteEntropy law, hlower⟩
  apply le_antisymm
  · exact csInf_le hbdd hself
  · exact le_csInf hnonempty hlower

/-- A full-support law minimizes finite cross entropy over full-support
references. This is the finite real form of the entropy variational identity. -/
theorem finiteEntropy_le_finiteCrossEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (law reference : PMF α) (hreference : PMFFullSupport reference) :
    finiteEntropy law ≤ finiteCrossEntropy law reference := by
  rw [finiteCrossEntropy_eq_entropy_add_kl]
  linarith [finiteKLDivergence_nonneg law reference hreference]

@[simp] theorem finiteCrossEntropy_self {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) : finiteCrossEntropy law law = finiteEntropy law := by
  rw [finiteCrossEntropy_eq_entropy_add_kl, finiteKLDivergence_self, add_zero]

/-- The range of finite cross entropy as the reference ranges over
full-support finite probability mass functions. -/
noncomputable def finiteCrossEntropyFullSupportRange
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) : Set ℝ :=
  { value | ∃ reference : PMF α,
    PMFFullSupport reference ∧ value = finiteCrossEntropy law reference }

/-- If the law has full support, its entropy is the infimum of its cross
entropy against full-support reference laws.  This is the finite real-valued
version of the entropy variational identity. -/
theorem sInf_finiteCrossEntropyFullSupportRange_eq_entropy
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α)
    (hlaw : PMFFullSupport law) :
    sInf (finiteCrossEntropyFullSupportRange law) = finiteEntropy law := by
  have hself : finiteEntropy law ∈ finiteCrossEntropyFullSupportRange law := by
    exact ⟨law, hlaw, (finiteCrossEntropy_self law).symm⟩
  have hnonempty : (finiteCrossEntropyFullSupportRange law).Nonempty := ⟨_, hself⟩
  have hlower : ∀ value ∈ finiteCrossEntropyFullSupportRange law,
      finiteEntropy law ≤ value := by
    intro value hvalue
    rcases hvalue with ⟨reference, hreference, rfl⟩
    exact finiteEntropy_le_finiteCrossEntropy law reference hreference
  have hbdd : BddBelow (finiteCrossEntropyFullSupportRange law) :=
    ⟨finiteEntropy law, hlower⟩
  apply le_antisymm
  · exact csInf_le hbdd hself
  · exact le_csInf hnonempty hlower

/-- Strict tangent inequality for `log` away from its equality point. -/
theorem log_lt_sub_one_of_pos_of_ne_one {x : ℝ}
    (hx : 0 < x) (hx_one : x ≠ 1) :
    Real.log x < x - 1 := by
  have hlog_ne_zero : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx_one
  have hexp : Real.log x + 1 < Real.exp (Real.log x) :=
    Real.add_one_lt_exp hlog_ne_zero
  rw [Real.exp_log hx] at hexp
  linarith

/-- The strict form of `Real.one_sub_inv_le_log_of_pos` away from `x = 1`. -/
theorem one_sub_inv_lt_log_of_pos_of_ne_one {x : ℝ}
    (hx : 0 < x) (hx_one : x ≠ 1) :
    1 - x⁻¹ < Real.log x := by
  have hinv_pos : 0 < x⁻¹ := inv_pos.mpr hx
  have hinv_ne_one : x⁻¹ ≠ 1 := by
    intro hinv
    apply hx_one
    exact inv_eq_one.mp hinv
  have hlog_inv : Real.log x⁻¹ < x⁻¹ - 1 :=
    log_lt_sub_one_of_pos_of_ne_one hinv_pos hinv_ne_one
  rw [Real.log_inv x] at hlog_inv
  linarith

/--
With a full-support reference PMF, the finite KL expression is strictly
positive whenever its two PMF arguments differ.
-/
theorem finiteKLDivergence_pos_of_ne {α : Type*} [Fintype α] [DecidableEq α]
    (first second : PMF α) (hsecond : PMFFullSupport second) (hne : first ≠ second) :
    0 < finiteKLDivergence first second := by
  classical
  have hterm_le : ∀ outcome : α,
      (first outcome).toReal - (second outcome).toReal ≤
        (first outcome).toReal *
          (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
    intro outcome
    by_cases hfirst_zero : (first outcome).toReal = 0
    · have hsecond_nonneg : 0 ≤ (second outcome).toReal := (hsecond outcome).le
      simp [hfirst_zero, hsecond_nonneg]
    · have hfirst_pos : 0 < (first outcome).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirst_zero)
      have hsecond_pos : 0 < (second outcome).toReal := hsecond outcome
      have hlog := Real.one_sub_inv_le_log_of_pos
        (div_pos hfirst_pos hsecond_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hfirst_pos.le
      calc
        (first outcome).toReal - (second outcome).toReal
            = (first outcome).toReal *
                (1 - ((first outcome).toReal / (second outcome).toReal)⁻¹) := by
                field_simp [hfirst_pos.ne', hsecond_pos.ne']
        _ ≤ (first outcome).toReal *
              Real.log ((first outcome).toReal / (second outcome).toReal) := hmul
        _ = (first outcome).toReal *
              (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := by
                rw [Real.log_div hfirst_pos.ne' hsecond_pos.ne']
  have hmass_ne : ∃ outcome : α,
      (first outcome).toReal ≠ (second outcome).toReal := by
    by_contra hnot
    push Not at hnot
    apply hne
    apply PMF.ext
    intro outcome
    exact (ENNReal.toReal_eq_toReal_iff'
      (ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one first outcome) ENNReal.one_lt_top))
      (ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one second outcome) ENNReal.one_lt_top))).mp
      (hnot outcome)
  obtain ⟨witness, hwitness⟩ := hmass_ne
  have hterm_lt :
      (first witness).toReal - (second witness).toReal <
        (first witness).toReal *
          (Real.log (first witness).toReal - Real.log (second witness).toReal) := by
    by_cases hfirst_zero : (first witness).toReal = 0
    · have hsecond_pos : 0 < (second witness).toReal := hsecond witness
      simp [hfirst_zero]
      linarith
    · have hfirst_pos : 0 < (first witness).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirst_zero)
      have hsecond_pos : 0 < (second witness).toReal := hsecond witness
      have hratio_ne : (first witness).toReal / (second witness).toReal ≠ 1 := by
        intro hratio
        apply hwitness
        exact (div_eq_one_iff_eq hsecond_pos.ne').mp hratio
      have hlog := one_sub_inv_lt_log_of_pos_of_ne_one
        (div_pos hfirst_pos hsecond_pos) hratio_ne
      have hmul := mul_lt_mul_of_pos_left hlog hfirst_pos
      calc
        (first witness).toReal - (second witness).toReal
            = (first witness).toReal *
                (1 - ((first witness).toReal / (second witness).toReal)⁻¹) := by
                field_simp [hfirst_pos.ne', hsecond_pos.ne']
        _ < (first witness).toReal *
              Real.log ((first witness).toReal / (second witness).toReal) := hmul
        _ = (first witness).toReal *
              (Real.log (first witness).toReal - Real.log (second witness).toReal) := by
                rw [Real.log_div hfirst_pos.ne' hsecond_pos.ne']
  have hsum_lt :
      (∑ outcome : α, ((first outcome).toReal - (second outcome).toReal)) <
        (∑ outcome : α, ((first outcome).toReal *
          (Real.log (first outcome).toReal - Real.log (second outcome).toReal))) := by
    refine Finset.sum_lt_sum (fun outcome _ => hterm_le outcome) ?_
    exact ⟨witness, Finset.mem_univ _, hterm_lt⟩
  unfold finiteKLDivergence
  calc
    0 = (∑ outcome : α, (first outcome).toReal) -
          ∑ outcome : α, (second outcome).toReal := by
          rw [pmfToRealSum, pmfToRealSum]
          norm_num
    _ = ∑ outcome : α, ((first outcome).toReal - (second outcome).toReal) := by
          rw [Finset.sum_sub_distrib]
    _ < ∑ outcome : α, (first outcome).toReal *
          (Real.log (first outcome).toReal - Real.log (second outcome).toReal) := hsum_lt

/--
For a full-support reference PMF, finite KL divergence vanishes exactly when
the two PMFs coincide.
-/
theorem finiteKLDivergence_eq_zero_iff {α : Type*} [Fintype α] [DecidableEq α]
    (first second : PMF α) (hsecond : PMFFullSupport second) :
    finiteKLDivergence first second = 0 ↔ first = second := by
  constructor
  · intro hzero
    by_contra hne
    have hpositive := finiteKLDivergence_pos_of_ne first second hsecond hne
    linarith
  · intro heq
    subst second
    exact finiteKLDivergence_self first

/--
Against a full-support reference PMF, the finite KL divergence is at most zero
exactly for the reference PMF itself.  This is the zero-radius boundary of a
finite KL ball and the finite-policy meaning of an infinite KL penalty.
-/
theorem finiteKLDivergence_le_zero_iff_eq {α : Type*} [Fintype α] [DecidableEq α]
    (first reference : PMF α) (hreference : PMFFullSupport reference) :
    finiteKLDivergence first reference ≤ 0 ↔ first = reference := by
  constructor
  · intro hle
    apply (finiteKLDivergence_eq_zero_iff first reference hreference).mp
    apply le_antisymm hle
    exact finiteKLDivergence_nonneg first reference hreference
  · intro heq
    subst reference
    rw [finiteKLDivergence_self]

/--
For a score in the unit interval, changing a finite PMF changes its expected
score by at most the finite `ℓ₁` difference of its real mass vectors.
-/
theorem pmfExp_sub_le_l1_mass_difference
    {α : Type*} [Fintype α] [DecidableEq α]
    (first second : PMF α) (score : α → ℝ)
    (hscore_nonneg : ∀ outcome, 0 ≤ score outcome)
    (hscore_le_one : ∀ outcome, score outcome ≤ 1) :
    pmfExp first score - pmfExp second score ≤
      FiniteDimensionalNorms.l1
        (fun outcome => (first outcome).toReal - (second outcome).toReal) := by
  unfold pmfExp FiniteDimensionalNorms.l1
  calc
    (∑ outcome : α, (first outcome).toReal * score outcome) -
        ∑ outcome : α, (second outcome).toReal * score outcome =
        ∑ outcome : α,
          ((first outcome).toReal - (second outcome).toReal) * score outcome := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun outcome _ => ?_
            ring
    _ ≤ |∑ outcome : α,
          ((first outcome).toReal - (second outcome).toReal) * score outcome| :=
        le_abs_self _
    _ ≤ ∑ outcome : α,
        |((first outcome).toReal - (second outcome).toReal) * score outcome| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ outcome : α, |(first outcome).toReal - (second outcome).toReal| := by
      refine Finset.sum_le_sum fun outcome _ => ?_
      rw [abs_mul, abs_of_nonneg (hscore_nonneg outcome)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hscore_le_one outcome)

/--
Jensen's lower bound for the unnormalized entropy sum of a finite nonnegative
mass vector.  In particular, spreading a fixed total mass uniformly over a
finite set minimizes `∑ xᵢ log xᵢ`.

The empty index type is included: both sides then use the library convention
`log 0 = 0` and are zero.
-/
theorem sum_mul_log_ge_mass_mul_log_div_card
    {α : Type*} [Fintype α] (mass : α → ℝ)
    (hmass_nonneg : ∀ outcome, 0 ≤ mass outcome) :
    (∑ outcome : α, mass outcome) *
        Real.log ((∑ outcome : α, mass outcome) / (Fintype.card α : ℝ)) ≤
      ∑ outcome : α, mass outcome * Real.log (mass outcome) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl hempty =>
      simp
  | inr hnonempty =>
      let n : ℝ := Fintype.card α
      change (∑ outcome : α, mass outcome) *
          Real.log ((∑ outcome : α, mass outcome) / n) ≤
        ∑ outcome : α, mass outcome * Real.log (mass outcome)
      have hn_pos : 0 < n := by
        dsimp [n]
        exact_mod_cast Fintype.card_pos
      have hn_ne : n ≠ 0 := hn_pos.ne'
      let w : α → ℝ := fun _ => n⁻¹
      let point : α → ℝ := fun outcome => n * mass outcome
      have hw_nonneg : ∀ outcome ∈ (Finset.univ : Finset α), 0 ≤ w outcome := by
        intro outcome _
        exact inv_nonneg.mpr hn_pos.le
      have hw_sum : ∑ outcome ∈ (Finset.univ : Finset α), w outcome = 1 := by
        change (∑ _ : α, n⁻¹) = 1
        calc
          (∑ _ : α, n⁻¹) = (Fintype.card α : ℝ) * n⁻¹ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = n * n⁻¹ := by rfl
          _ = 1 := mul_inv_cancel₀ hn_ne
      have hpoint_mem : ∀ outcome ∈ (Finset.univ : Finset α),
          point outcome ∈ Set.Ici (0 : ℝ) := by
        intro outcome _
        exact mul_nonneg hn_pos.le (hmass_nonneg outcome)
      have hjensen :
          (fun x : ℝ => x * Real.log x) (∑ outcome : α, w outcome * point outcome) ≤
            ∑ outcome : α, w outcome *
              ((fun x : ℝ => x * Real.log x) (point outcome)) :=
        Real.convexOn_mul_log.map_sum_le hw_nonneg hw_sum hpoint_mem
      have hmean :
          (∑ outcome : α, w outcome * point outcome) =
            ∑ outcome : α, mass outcome := by
        simp only [w, point]
        refine Finset.sum_congr rfl fun outcome _ => ?_
        field_simp [hn_ne]
      rw [hmean] at hjensen
      have hlog_div :
          (∑ outcome : α, mass outcome) *
              Real.log ((∑ outcome : α, mass outcome) / n) =
            (∑ outcome : α, mass outcome) * Real.log (∑ outcome : α, mass outcome) -
              (∑ outcome : α, mass outcome) * Real.log n := by
        by_cases htotal_zero : (∑ outcome : α, mass outcome) = 0
        · simp [htotal_zero]
        · rw [Real.log_div htotal_zero hn_ne]
          ring
      calc
        (∑ outcome : α, mass outcome) *
            Real.log ((∑ outcome : α, mass outcome) / n) =
            (∑ outcome : α, mass outcome) * Real.log (∑ outcome : α, mass outcome) -
              (∑ outcome : α, mass outcome) * Real.log n := hlog_div
        _ ≤ (∑ outcome : α, w outcome *
              (point outcome * Real.log (point outcome))) -
              (∑ outcome : α, mass outcome) * Real.log n := by
              linarith
        _ = ∑ outcome : α, mass outcome * Real.log (mass outcome) := by
              rw [Finset.sum_mul]
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun outcome _ => ?_
              simp only [w, point]
              by_cases hzero : mass outcome = 0
              · simp [hzero]
              · rw [Real.log_mul hn_ne hzero]
                field_simp [hn_ne]
                ring

/--
A finite KL ball around a reference distribution that gives total mass
`epsilon` uniformly to a nonempty clone class cannot place much mass on that
class.  The bound is the elementary source-friendly form
`p(clones) log (1 / epsilon) - 1 ≤ KL`.

Unlike a Pinsker bound, this captures the logarithmic protection obtained by
making the reference clone mass small.  The result is stated for a sum type so
the clone class and its complement remain explicit in applications.
-/
theorem finiteKLDivergence_right_uniform_mass_lower
    {Left Right : Type*} [Fintype Left] [DecidableEq Left]
    [Fintype Right] [DecidableEq Right] [Nonempty Right]
    (first reference : PMF (Left ⊕ Right)) (epsilon : ℝ)
    (hepsilon_pos : 0 < epsilon) (href_full : PMFFullSupport reference)
    (href_right : ∀ right : Right,
      (reference (Sum.inr right)).toReal = epsilon / (Fintype.card Right : ℝ)) :
    (∑ right : Right, (first (Sum.inr right)).toReal) * Real.log epsilon⁻¹ - 1 ≤
      finiteKLDivergence first reference := by
  classical
  let n : ℝ := Fintype.card Right
  let firstLeftMass : ℝ := ∑ left : Left, (first (Sum.inl left)).toReal
  let firstRightMass : ℝ := ∑ right : Right, (first (Sum.inr right)).toReal
  let referenceLeftMass : ℝ := ∑ left : Left, (reference (Sum.inl left)).toReal
  let referenceRightMass : ℝ := ∑ right : Right, (reference (Sum.inr right)).toReal
  change firstRightMass * Real.log epsilon⁻¹ - 1 ≤ finiteKLDivergence first reference
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hepsilon_ne : epsilon ≠ 0 := hepsilon_pos.ne'
  have hfirstRight_nonneg : 0 ≤ firstRightMass := by
    dsimp [firstRightMass]
    exact Finset.sum_nonneg fun right _ => ENNReal.toReal_nonneg
  have hreferenceRight_eq : referenceRightMass = epsilon := by
    dsimp [referenceRightMass]
    calc
      (∑ right : Right, (reference (Sum.inr right)).toReal) =
          ∑ right : Right, epsilon / n := by
            refine Finset.sum_congr rfl fun right _ => ?_
            simpa only [n] using href_right right
      _ = (Fintype.card Right : ℝ) * (epsilon / n) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = epsilon := by
            rw [show (Fintype.card Right : ℝ) = n by rfl]
            field_simp [hn_ne]
  have hfirst_total : firstLeftMass + firstRightMass = 1 := by
    dsimp [firstLeftMass, firstRightMass]
    have hsum := pmfToRealSum first
    rw [Fintype.sum_sum_type] at hsum
    exact hsum
  have hreference_total : referenceLeftMass + referenceRightMass = 1 := by
    dsimp [referenceLeftMass, referenceRightMass]
    have hsum := pmfToRealSum reference
    rw [Fintype.sum_sum_type] at hsum
    exact hsum
  have hleft_eq : firstLeftMass - referenceLeftMass = epsilon - firstRightMass := by
    linarith [hfirst_total, hreference_total, hreferenceRight_eq]
  have hleft_bound :
      firstLeftMass - referenceLeftMass ≤
        ∑ left : Left,
          (first (Sum.inl left)).toReal *
            (Real.log (first (Sum.inl left)).toReal -
              Real.log (reference (Sum.inl left)).toReal) := by
    calc
      firstLeftMass - referenceLeftMass =
          ∑ left : Left,
            ((first (Sum.inl left)).toReal - (reference (Sum.inl left)).toReal) := by
              dsimp [firstLeftMass, referenceLeftMass]
              rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ left : Left,
          (first (Sum.inl left)).toReal *
            (Real.log (first (Sum.inl left)).toReal -
              Real.log (reference (Sum.inl left)).toReal) := by
              refine Finset.sum_le_sum fun left _ => ?_
              exact mass_sub_le_mul_log_mass_ratio ENNReal.toReal_nonneg
                (href_full (Sum.inl left))
  have hright_eq :
      (∑ right : Right,
          (first (Sum.inr right)).toReal *
            (Real.log (first (Sum.inr right)).toReal -
              Real.log (reference (Sum.inr right)).toReal)) =
        (∑ right : Right,
          (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
          firstRightMass * (Real.log epsilon - Real.log n) := by
    have hlog_reference : ∀ right : Right,
        Real.log (reference (Sum.inr right)).toReal = Real.log epsilon - Real.log n := by
      intro right
      rw [href_right right]
      exact Real.log_div hepsilon_ne hn_ne
    simp_rw [hlog_reference]
    calc
      (∑ right : Right, (first (Sum.inr right)).toReal *
          (Real.log (first (Sum.inr right)).toReal -
            (Real.log epsilon - Real.log n))) =
          ∑ right : Right,
            ((first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal -
              (first (Sum.inr right)).toReal * (Real.log epsilon - Real.log n)) := by
              refine Finset.sum_congr rfl fun right _ => ?_
              ring
      _ = (∑ right : Right,
          (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
          ∑ right : Right,
            (first (Sum.inr right)).toReal * (Real.log epsilon - Real.log n) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ right : Right,
          (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
          firstRightMass * (Real.log epsilon - Real.log n) := by
              rw [← Finset.sum_mul]
  have hright_entropy :
      firstRightMass * Real.log (firstRightMass / n) ≤
        ∑ right : Right,
          (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal := by
    simpa only [firstRightMass] using
      (sum_mul_log_ge_mass_mul_log_div_card
        (fun right : Right => (first (Sum.inr right)).toReal)
        (fun right => ENNReal.toReal_nonneg))
  have hright_reduced :
      firstRightMass * Real.log epsilon⁻¹ - 1 ≤
        (epsilon - firstRightMass) +
          (firstRightMass * Real.log (firstRightMass / n) -
            firstRightMass * (Real.log epsilon - Real.log n)) := by
    by_cases hfirstRight_zero : firstRightMass = 0
    · simp [hfirstRight_zero]
      linarith
    · have hfirstRight_pos : 0 < firstRightMass :=
          lt_of_le_of_ne hfirstRight_nonneg (Ne.symm hfirstRight_zero)
      have hlog := Real.one_sub_inv_le_log_of_pos hfirstRight_pos
      have hmul := mul_le_mul_of_nonneg_left hlog hfirstRight_nonneg
      have hmass_log : -1 ≤
          firstRightMass * Real.log firstRightMass - firstRightMass := by
        have hrewrite : -1 =
            firstRightMass * (1 - firstRightMass⁻¹) - firstRightMass := by
          field_simp [hfirstRight_zero]
          ring
        rw [hrewrite]
        exact sub_le_sub_right hmul _
      rw [Real.log_inv, Real.log_div hfirstRight_zero hn_ne]
      linarith [hmass_log, hepsilon_pos.le]
  have hright_bound :
      firstRightMass * Real.log epsilon⁻¹ - 1 ≤
        (epsilon - firstRightMass) +
          ((∑ right : Right,
            (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
            firstRightMass * (Real.log epsilon - Real.log n)) := by
    calc
      firstRightMass * Real.log epsilon⁻¹ - 1 ≤
          (epsilon - firstRightMass) +
            (firstRightMass * Real.log (firstRightMass / n) -
              firstRightMass * (Real.log epsilon - Real.log n)) := hright_reduced
      _ ≤ (epsilon - firstRightMass) +
          ((∑ right : Right,
            (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
            firstRightMass * (Real.log epsilon - Real.log n)) := by
            gcongr
  have hkl_lower :
      (firstLeftMass - referenceLeftMass) +
          ((∑ right : Right,
            (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
            firstRightMass * (Real.log epsilon - Real.log n)) ≤
        finiteKLDivergence first reference := by
    calc
      (firstLeftMass - referenceLeftMass) +
          ((∑ right : Right,
            (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
            firstRightMass * (Real.log epsilon - Real.log n)) ≤
          (∑ left : Left,
            (first (Sum.inl left)).toReal *
              (Real.log (first (Sum.inl left)).toReal -
                Real.log (reference (Sum.inl left)).toReal)) +
          (∑ right : Right,
            (first (Sum.inr right)).toReal *
              (Real.log (first (Sum.inr right)).toReal -
                Real.log (reference (Sum.inr right)).toReal)) := by
              rw [hright_eq]
              exact add_le_add_left hleft_bound _
      _ = finiteKLDivergence first reference := by
            unfold finiteKLDivergence
            rw [Fintype.sum_sum_type]
  calc
    firstRightMass * Real.log epsilon⁻¹ - 1 ≤
        (firstLeftMass - referenceLeftMass) +
          ((∑ right : Right,
            (first (Sum.inr right)).toReal * Real.log (first (Sum.inr right)).toReal) -
            firstRightMass * (Real.log epsilon - Real.log n)) := by
          rw [hleft_eq]
          exact hright_bound
    _ ≤ finiteKLDivergence first reference := hkl_lower

end AppliedModelingLib

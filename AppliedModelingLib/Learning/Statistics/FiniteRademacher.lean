import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.BoundedDifferences
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Foundations.Probability.RademacherMatrix
import Mathlib.Topology.UnitInterval

/-!
# Finite Rademacher complexity

Reusable deterministic and finite-probability lemmas for one-sided
Rademacher complexity.  The one-sided convention matches Definition 2.2 of
Hardt--Megiddo--Papadimitriou--Wootters (2016): for a fixed sample and sign
vector, take the supremum of the normalized signed sum, without an absolute
value inside the supremum.

## Upstream provenance

The two-point contraction proof below follows the finite-supremum proof
architecture in AutoRes's `FoML/Learning/Contraction.lean` at commit
`bc333764168dab8ac58afcec4b9df8cacf9b54ad`:

* repository: <https://github.com/auto-res/lean-rademacher>
* source: <https://github.com/auto-res/lean-rademacher/blob/bc333764168dab8ac58afcec4b9df8cacf9b54ad/FoML/Learning/Contraction.lean>
* finite-class source: <https://github.com/auto-res/lean-rademacher/blob/bc333764168dab8ac58afcec4b9df8cacf9b54ad/FoML/Entropy/Massart.lean>
* maximal-inequality source: <https://github.com/auto-res/lean-rademacher/blob/bc333764168dab8ac58afcec4b9df8cacf9b54ad/FoML/Entropy/MaximalInequality.lean>
* symmetrization source: <https://github.com/auto-res/lean-rademacher/blob/bc333764168dab8ac58afcec4b9df8cacf9b54ad/FoML/Rademacher/Symmetrization.lean>
* expected-complexity source: <https://github.com/auto-res/lean-rademacher/blob/bc333764168dab8ac58afcec4b9df8cacf9b54ad/FoML/Rademacher/Expectation.lean>
* license: MIT, copyright (c) 2025 AutoRes

The upstream project targets an older Lean/Mathlib dependency stack and is not
imported here.  The contraction, finite-maximum, and sign-symmetrization proof
architectures are adapted to this repository's finite real-valued PMF API and
current pinned Mathlib.  The MIT license permits
use, modification, and redistribution provided its copyright and permission
notice are retained; the exact upstream license was checked before this
adaptation.

The upstream permission notice is:

> Permission is hereby granted, free of charge, to any person obtaining a copy
> of this software and associated documentation files (the "Software"), to deal
> in the Software without restriction, including without limitation the rights
> to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
> copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions: the copyright and
> permission notices shall be included in all copies or substantial portions of
> the Software. The Software is provided "as is", without warranty of any kind,
> express or implied, including merchantability, fitness for a particular
> purpose, and noninfringement. In no event shall the authors or copyright
> holders be liable for any claim, damages, or other liability arising from the
> Software or its use.

The Jensen, sub-Gaussian-MGF, and finite/infinite product-measure bridges use
Mathlib directly at this repository's pinned commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`:

* Jensen API: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/Jensen.lean>
* sub-Gaussian API: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/SubGaussian.lean>
* product-measure API: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProductMeasure.lean>
* license: Apache-2.0,
  <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/LICENSE>

These APIs are imported, not copied.  Apache-2.0 permits this use and
redistribution subject to its notice, attribution, and patent-license terms;
no incompatible restriction was found.
-/

namespace AppliedModelingLib
namespace Statistics
namespace FiniteRademacher

open scoped BigOperators
open AppliedModelingLib.Probability.RademacherMatrix

variable {Hypothesis : Type*}

/-- The square map clipped to `[-2, 2]`.  Unlike `x ↦ x²`, this is globally
Lipschitz while agreeing with the square on every sum or difference of two
`[-1, 1]` values. -/
noncomputable def clippedSquare (input : ℝ) : ℝ :=
  ((Set.projIcc (-2 : ℝ) 2 (by norm_num) input : ℝ) ^ 2)

/-- The clipped square map has Lipschitz constant four. -/
theorem abs_clippedSquare_sub_le_four_abs_sub (first second : ℝ) :
    |clippedSquare first - clippedSquare second| ≤ 4 * |first - second| := by
  let clip : ℝ → ℝ := fun input =>
    (Set.projIcc (-2 : ℝ) 2 (by norm_num) input : ℝ)
  have hfirst : clip first ∈ Set.Icc (-2 : ℝ) 2 :=
    (Set.projIcc (-2 : ℝ) 2 (by norm_num) first).property
  have hsecond : clip second ∈ Set.Icc (-2 : ℝ) 2 :=
    (Set.projIcc (-2 : ℝ) 2 (by norm_num) second).property
  have hsum : |clip first + clip second| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2]
  have hprojection : |clip first - clip second| ≤ |first - second| := by
    simpa only [clip] using
      Set.abs_projIcc_sub_projIcc (a := (-2 : ℝ)) (b := 2) (by norm_num)
        (c := first) (d := second)
  calc
    |clippedSquare first - clippedSquare second| =
        |clip first - clip second| * |clip first + clip second| := by
      rw [show clippedSquare first = clip first ^ 2 by rfl,
        show clippedSquare second = clip second ^ 2 by rfl, ← abs_mul]
      congr 1
      ring
    _ ≤ |clip first - clip second| * 4 :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ 4 * |first - second| := by nlinarith [abs_nonneg (clip first - clip second)]

/-- Clipping is inert on the square's defining interval. -/
theorem clippedSquare_eq_sq_of_mem_Icc
    (input : ℝ) (hinput : input ∈ Set.Icc (-2 : ℝ) 2) :
    clippedSquare input = input ^ 2 := by
  unfold clippedSquare
  rw [Set.projIcc_of_mem (by norm_num) hinput]

/-- On the unit square, multiplication is the difference of two clipped
squares.  This polarization identity turns a product class into scalar
Lipschitz transforms of sum classes. -/
theorem mul_eq_clippedSquare_polarization_of_abs_le_one
    (first second : ℝ) (hfirst : |first| ≤ 1) (hsecond : |second| ≤ 1) :
    first * second =
      (clippedSquare (first + second) - clippedSquare (first - second)) / 4 := by
  have hfirstBounds : -1 ≤ first ∧ first ≤ 1 := (abs_le.mp hfirst)
  have hsecondBounds : -1 ≤ second ∧ second ≤ 1 := (abs_le.mp hsecond)
  have hsum : first + second ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> linarith
  have hsub : first - second ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> linarith
  rw [clippedSquare_eq_sq_of_mem_Icc _ hsum,
    clippedSquare_eq_sq_of_mem_Icc _ hsub]
  ring

/-- Split a sum over `n+1` Boolean signs into the initial signs and last sign. -/
theorem sum_boolSigns_snoc (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ signs : Fin (n + 1) → Bool, f signs) =
      ∑ initial : Fin n → Bool,
        (f (Fin.snoc initial false) + f (Fin.snoc initial true)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro initial _
  simp [Fin.snocEquiv, add_comm]

/--
The deterministic two-sign contraction step.  Pairing the positive and
negative last-coordinate signs converts a Lipschitz transform `psi` to the
linear map with slope `L`.  This is the induction kernel for finite one-sided
Rademacher contraction.
-/
theorem two_iSup_lipschitz_contraction
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (offset value : Hypothesis → ℝ) (psi : ℝ → ℝ) {L : ℝ}
    (hpsi : ∀ u v, |psi u - psi v| ≤ L * |u - v|) :
    (⨆ h, offset h + psi (value h)) +
        (⨆ h, offset h - psi (value h)) ≤
      (⨆ h, offset h + L * value h) +
        (⨆ h, offset h - L * value h) := by
  obtain ⟨positiveMaximizer, hpositive⟩ :=
    exists_eq_ciSup_of_finite
      (f := fun h => offset h + psi (value h))
  obtain ⟨negativeMaximizer, hnegative⟩ :=
    exists_eq_ciSup_of_finite
      (f := fun h => offset h - psi (value h))
  rw [← hpositive, ← hnegative]
  by_cases horder : value negativeMaximizer ≤ value positiveMaximizer
  · have hdiff :
        psi (value positiveMaximizer) - psi (value negativeMaximizer) ≤
          L * (value positiveMaximizer - value negativeMaximizer) := by
      calc
        psi (value positiveMaximizer) - psi (value negativeMaximizer) ≤
            |psi (value positiveMaximizer) - psi (value negativeMaximizer)| :=
          le_abs_self _
        _ ≤ L * |value positiveMaximizer - value negativeMaximizer| :=
          hpsi _ _
        _ = L * (value positiveMaximizer - value negativeMaximizer) := by
          rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    calc
      (offset positiveMaximizer + psi (value positiveMaximizer)) +
          (offset negativeMaximizer - psi (value negativeMaximizer)) =
          offset positiveMaximizer + offset negativeMaximizer +
            (psi (value positiveMaximizer) - psi (value negativeMaximizer)) := by
        ring
      _ ≤ offset positiveMaximizer + offset negativeMaximizer +
          L * (value positiveMaximizer - value negativeMaximizer) := by
        linarith
      _ = (offset positiveMaximizer + L * value positiveMaximizer) +
          (offset negativeMaximizer - L * value negativeMaximizer) := by
        ring
      _ ≤ (⨆ h, offset h + L * value h) +
          (⨆ h, offset h - L * value h) := by
        exact add_le_add
          (le_ciSup (f := fun h => offset h + L * value h)
            (Finite.bddAbove_range _) positiveMaximizer)
          (le_ciSup (f := fun h => offset h - L * value h)
            (Finite.bddAbove_range _) negativeMaximizer)
  · have hreverse : value positiveMaximizer ≤ value negativeMaximizer :=
      le_of_not_ge horder
    have hdiff :
        psi (value positiveMaximizer) - psi (value negativeMaximizer) ≤
          L * (value negativeMaximizer - value positiveMaximizer) := by
      calc
        psi (value positiveMaximizer) - psi (value negativeMaximizer) ≤
            |psi (value positiveMaximizer) - psi (value negativeMaximizer)| :=
          le_abs_self _
        _ ≤ L * |value positiveMaximizer - value negativeMaximizer| :=
          hpsi _ _
        _ = L * (value negativeMaximizer - value positiveMaximizer) := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hreverse)]
    calc
      (offset positiveMaximizer + psi (value positiveMaximizer)) +
          (offset negativeMaximizer - psi (value negativeMaximizer)) =
          offset positiveMaximizer + offset negativeMaximizer +
            (psi (value positiveMaximizer) - psi (value negativeMaximizer)) := by
        ring
      _ ≤ offset positiveMaximizer + offset negativeMaximizer +
          L * (value negativeMaximizer - value positiveMaximizer) := by
        linarith
      _ = (offset negativeMaximizer + L * value negativeMaximizer) +
          (offset positiveMaximizer - L * value positiveMaximizer) := by
        ring
      _ ≤ (⨆ h, offset h + L * value h) +
          (⨆ h, offset h - L * value h) := by
        exact add_le_add
          (le_ciSup (f := fun h => offset h + L * value h)
            (Finite.bddAbove_range _) negativeMaximizer)
          (le_ciSup (f := fun h => offset h - L * value h)
            (Finite.bddAbove_range _) positiveMaximizer)

/--
Finite one-sided contraction before normalization and averaging.  Summing over
all Boolean sign vectors is convenient for the induction; the fair-PMF form is
obtained by multiplying both sides by the common nonnegative atom weight.
-/
theorem sum_iSup_rademacher_contraction
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ)
    (psi : Fin n → ℝ → ℝ) (offset : Hypothesis → ℝ) {L : ℝ}
    (hpsi : ∀ index u v, |psi index u - psi index v| ≤ L * |u - v|) :
    (∑ signs : Fin n → Bool,
        ⨆ hypothesis,
          offset hypothesis +
            ∑ index : Fin n,
              rademacherSign (signs index) *
                psi index (value hypothesis index)) ≤
      ∑ signs : Fin n → Bool,
        ⨆ hypothesis,
          offset hypothesis +
            L * ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index := by
  induction n generalizing offset with
  | zero =>
      simp
  | succ m inductionHypothesis =>
      let prefixValue : Hypothesis → Fin m → ℝ :=
        fun hypothesis index => value hypothesis index.castSucc
      let prefixPsi : Fin m → ℝ → ℝ :=
        fun index => psi index.castSucc
      let lastValue : Hypothesis → ℝ :=
        fun hypothesis => value hypothesis (Fin.last m)
      have hprefixPsi :
          ∀ index u v,
            |prefixPsi index u - prefixPsi index v| ≤ L * |u - v| :=
        fun index u v => hpsi index.castSucc u v
      let transformedPair : (Fin m → Bool) → ℝ :=
        fun initial =>
          (⨆ hypothesis,
              offset hypothesis +
                (∑ index : Fin m,
                  rademacherSign (initial index) *
                    prefixPsi index (prefixValue hypothesis index)) +
                psi (Fin.last m) (lastValue hypothesis)) +
            (⨆ hypothesis,
              offset hypothesis +
                (∑ index : Fin m,
                  rademacherSign (initial index) *
                    prefixPsi index (prefixValue hypothesis index)) -
                psi (Fin.last m) (lastValue hypothesis))
      let linearPair : (Fin m → Bool) → ℝ :=
        fun initial =>
          (⨆ hypothesis,
              offset hypothesis +
                (∑ index : Fin m,
                  rademacherSign (initial index) *
                    prefixPsi index (prefixValue hypothesis index)) +
                L * lastValue hypothesis) +
            (⨆ hypothesis,
              offset hypothesis +
                (∑ index : Fin m,
                  rademacherSign (initial index) *
                    prefixPsi index (prefixValue hypothesis index)) -
                L * lastValue hypothesis)
      have hlast :
          (∑ initial : Fin m → Bool, transformedPair initial) ≤
            ∑ initial : Fin m → Bool, linearPair initial := by
        apply Finset.sum_le_sum
        intro initial _
        let currentOffset : Hypothesis → ℝ :=
          fun hypothesis =>
            offset hypothesis +
              ∑ index : Fin m,
                rademacherSign (initial index) *
                  prefixPsi index (prefixValue hypothesis index)
        simpa [transformedPair, linearPair, currentOffset, add_assoc] using
          two_iSup_lipschitz_contraction currentOffset lastValue
            (psi (Fin.last m)) (hpsi (Fin.last m))
      have hminus :=
        inductionHypothesis
          (value := prefixValue) (psi := prefixPsi)
          (offset := fun hypothesis =>
            offset hypothesis - L * lastValue hypothesis)
          hprefixPsi
      have hplus :=
        inductionHypothesis
          (value := prefixValue) (psi := prefixPsi)
          (offset := fun hypothesis =>
            offset hypothesis + L * lastValue hypothesis)
          hprefixPsi
      calc
        (∑ signs : Fin (m + 1) → Bool,
            ⨆ hypothesis,
              offset hypothesis +
                ∑ index : Fin (m + 1),
                  rademacherSign (signs index) *
                    psi index (value hypothesis index)) =
            ∑ initial : Fin m → Bool,
              ((⨆ hypothesis,
                  offset hypothesis +
                    (∑ index : Fin m,
                      rademacherSign (initial index) *
                        prefixPsi index (prefixValue hypothesis index)) -
                    psi (Fin.last m) (lastValue hypothesis)) +
                (⨆ hypothesis,
                  offset hypothesis +
                    (∑ index : Fin m,
                      rademacherSign (initial index) *
                        prefixPsi index (prefixValue hypothesis index)) +
                    psi (Fin.last m) (lastValue hypothesis))) := by
          rw [sum_boolSigns_snoc]
          apply Finset.sum_congr rfl
          intro initial _
          congr 1 <;> apply congrArg <;> funext hypothesis <;>
            rw [Fin.sum_univ_castSucc] <;>
            simp [prefixValue, prefixPsi, lastValue, rademacherSign] <;> ring
        _ ≤ ∑ initial : Fin m → Bool,
              ((⨆ hypothesis,
                  offset hypothesis +
                    (∑ index : Fin m,
                      rademacherSign (initial index) *
                        prefixPsi index (prefixValue hypothesis index)) -
                    L * lastValue hypothesis) +
                (⨆ hypothesis,
                  offset hypothesis +
                    (∑ index : Fin m,
                      rademacherSign (initial index) *
                        prefixPsi index (prefixValue hypothesis index)) +
                    L * lastValue hypothesis)) := by
          simpa [transformedPair, linearPair, add_comm] using hlast
        _ = (∑ initial : Fin m → Bool,
              ⨆ hypothesis,
                (offset hypothesis - L * lastValue hypothesis) +
                  ∑ index : Fin m,
                    rademacherSign (initial index) *
                      prefixPsi index (prefixValue hypothesis index)) +
            ∑ initial : Fin m → Bool,
              ⨆ hypothesis,
                (offset hypothesis + L * lastValue hypothesis) +
                  ∑ index : Fin m,
                    rademacherSign (initial index) *
                      prefixPsi index (prefixValue hypothesis index) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro initial _
          congr 1 <;> apply congrArg <;> funext hypothesis <;> ring
        _ ≤ (∑ initial : Fin m → Bool,
              ⨆ hypothesis,
                (offset hypothesis - L * lastValue hypothesis) +
                  L * ∑ index : Fin m,
                    rademacherSign (initial index) *
                      prefixValue hypothesis index) +
            ∑ initial : Fin m → Bool,
              ⨆ hypothesis,
                (offset hypothesis + L * lastValue hypothesis) +
                  L * ∑ index : Fin m,
                    rademacherSign (initial index) *
                      prefixValue hypothesis index :=
          add_le_add hminus hplus
        _ = ∑ initial : Fin m → Bool,
              ((⨆ hypothesis,
                  offset hypothesis +
                    L * ((∑ index : Fin m,
                      rademacherSign (initial index) *
                        prefixValue hypothesis index) -
                      lastValue hypothesis)) +
                (⨆ hypothesis,
                  offset hypothesis +
                    L * ((∑ index : Fin m,
                      rademacherSign (initial index) *
                        prefixValue hypothesis index) +
                      lastValue hypothesis))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro initial _
          congr 1 <;> apply congrArg <;> funext hypothesis <;> ring
        _ = ∑ signs : Fin (m + 1) → Bool,
              ⨆ hypothesis,
                offset hypothesis +
                  L * ∑ index : Fin (m + 1),
                    rademacherSign (signs index) *
                      value hypothesis index := by
          rw [sum_boolSigns_snoc]
          apply Finset.sum_congr rfl
          intro initial _
          apply congrArg₂ (fun left right : ℝ => left + right)
          · exact congrArg (fun f : Hypothesis → ℝ => ⨆ hypothesis, f hypothesis) (by
              funext hypothesis
              rw [Fin.sum_univ_castSucc]
              simp [prefixValue, lastValue, rademacherSign, sub_eq_add_neg])
          · exact congrArg (fun f : Hypothesis → ℝ => ⨆ hypothesis, f hypothesis) (by
              funext hypothesis
              rw [Fin.sum_univ_castSucc]
              simp [prefixValue, lastValue, rademacherSign])

/-- A nonnegative constant commutes with a supremum over a finite nonempty type. -/
theorem iSup_const_mul_eq_const_iSup
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (value : Hypothesis → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (⨆ hypothesis, L * value hypothesis) =
      L * (⨆ hypothesis, value hypothesis) := by
  obtain ⟨maximizer, hmaximizer⟩ :=
    exists_eq_ciSup_of_finite (f := value)
  apply le_antisymm
  · apply ciSup_le
    intro hypothesis
    exact mul_le_mul_of_nonneg_left
      (le_ciSup (Finite.bddAbove_range value) hypothesis) hL
  · rw [← hmaximizer]
    exact le_ciSup
      (Finite.bddAbove_range (fun hypothesis => L * value hypothesis))
      maximizer

/--
Finite one-sided contraction after summing over all signs, with zero offset.
This is the direct deterministic form used by the uniform-sign expectation.
-/
theorem sum_iSup_rademacher_contraction_zeroOffset
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ)
    (psi : Fin n → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hpsi : ∀ index u v, |psi index u - psi index v| ≤ L * |u - v|) :
    (∑ signs : Fin n → Bool,
        ⨆ hypothesis,
          ∑ index : Fin n,
            rademacherSign (signs index) *
              psi index (value hypothesis index)) ≤
      L * ∑ signs : Fin n → Bool,
        ⨆ hypothesis,
          ∑ index : Fin n,
            rademacherSign (signs index) * value hypothesis index := by
  have hraw :=
    sum_iSup_rademacher_contraction n value psi (fun _ => 0) hpsi
  simp only [zero_add] at hraw
  calc
    (∑ signs : Fin n → Bool,
        ⨆ hypothesis,
          ∑ index : Fin n,
            rademacherSign (signs index) *
              psi index (value hypothesis index)) ≤
        ∑ signs : Fin n → Bool,
          ⨆ hypothesis,
            L * ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index := hraw
    _ = ∑ signs : Fin n → Bool,
          L * (⨆ hypothesis,
            ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index) := by
          apply Finset.sum_congr rfl
          intro signs _
          exact iSup_const_mul_eq_const_iSup _ hL
    _ = L * ∑ signs : Fin n → Bool,
          ⨆ hypothesis,
            ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index := by
          rw [Finset.mul_sum]

/--
One-sided empirical Rademacher complexity for a finite class and a fixed
length-`n` sample, represented as expectation under a uniform Boolean sign
vector.  Normalization by `n` is deliberately left to the caller, so the same
object also supports weighted coordinates.
-/
noncomputable def empiricalOneSidedRademacherSum
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ) : ℝ :=
  AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool)) fun signs =>
    ⨆ hypothesis,
      ∑ index : Fin n,
        rademacherSign (signs index) * value hypothesis index

/-- One-sided empirical contraction under uniform independent signs. -/
theorem empiricalOneSidedRademacherSum_contraction
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ)
    (psi : Fin n → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hpsi : ∀ index u v, |psi index u - psi index v| ≤ L * |u - v|) :
    empiricalOneSidedRademacherSum n
        (fun hypothesis index => psi index (value hypothesis index)) ≤
      L * empiricalOneSidedRademacherSum n value := by
  have hsum :=
    sum_iSup_rademacher_contraction_zeroOffset n value psi hL hpsi
  unfold empiricalOneSidedRademacherSum AppliedModelingLib.pmfExp
  simp_rw [AppliedModelingLib.uniformPMF_apply_toReal]
  calc
    (∑ signs : Fin n → Bool,
        (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
          (⨆ hypothesis,
            ∑ index : Fin n,
              rademacherSign (signs index) *
                psi index (value hypothesis index))) =
        (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
          ∑ signs : Fin n → Bool,
            ⨆ hypothesis,
              ∑ index : Fin n,
                rademacherSign (signs index) *
                  psi index (value hypothesis index) := by
          rw [Finset.mul_sum]
    _ ≤ (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
        (L * ∑ signs : Fin n → Bool,
          ⨆ hypothesis,
            ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = L * ∑ signs : Fin n → Bool,
        (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
          (⨆ hypothesis,
            ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index) := by
          rw [← Finset.mul_sum]
          ring

/-- The conventional `1/n`-normalized one-sided empirical complexity. -/
noncomputable def empiricalOneSidedRademacher
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * empiricalOneSidedRademacherSum n value

/-- Normalized one-sided empirical Rademacher contraction. -/
theorem empiricalOneSidedRademacher_contraction
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ)
    (psi : Fin n → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hpsi : ∀ index u v, |psi index u - psi index v| ≤ L * |u - v|) :
    empiricalOneSidedRademacher n
        (fun hypothesis index => psi index (value hypothesis index)) ≤
      L * empiricalOneSidedRademacher n value := by
  unfold empiricalOneSidedRademacher
  calc
    (n : ℝ)⁻¹ * empiricalOneSidedRademacherSum n
        (fun hypothesis index => psi index (value hypothesis index)) ≤
      (n : ℝ)⁻¹ *
        (L * empiricalOneSidedRademacherSum n value) :=
      mul_le_mul_of_nonneg_left
        (empiricalOneSidedRademacherSum_contraction n value psi hL hpsi)
        (by positivity)
    _ = L * ((n : ℝ)⁻¹ * empiricalOneSidedRademacherSum n value) := by
      ring

/-- One-sided empirical complexity is subadditive for two functions indexed
by the same finite class. -/
theorem empiricalOneSidedRademacher_add_le
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (left right : Hypothesis → Fin n → ℝ) :
    empiricalOneSidedRademacher n
        (fun hypothesis index => left hypothesis index + right hypothesis index) ≤
      empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right := by
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
  rw [← mul_add, ← AppliedModelingLib.pmfExp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro signs
  let leftScore : Hypothesis → ℝ := fun hypothesis =>
    ∑ index : Fin n, rademacherSign (signs index) * left hypothesis index
  let rightScore : Hypothesis → ℝ := fun hypothesis =>
    ∑ index : Fin n, rademacherSign (signs index) * right hypothesis index
  have hpoint : ∀ hypothesis,
      (∑ index : Fin n, rademacherSign (signs index) *
        (left hypothesis index + right hypothesis index)) =
        leftScore hypothesis + rightScore hypothesis := by
    intro hypothesis
    simp only [leftScore, rightScore, mul_add, Finset.sum_add_distrib]
  rw [show (fun hypothesis =>
      ∑ index : Fin n, rademacherSign (signs index) *
        (left hypothesis index + right hypothesis index)) =
      fun hypothesis => leftScore hypothesis + rightScore hypothesis by
        funext hypothesis
        exact hpoint hypothesis]
  apply ciSup_le
  intro hypothesis
  exact add_le_add
    (le_ciSup (Finite.bddAbove_range leftScore) hypothesis)
    (le_ciSup (Finite.bddAbove_range rightScore) hypothesis)

/-- An exact finite convex representation transfers one-sided empirical
Rademacher complexity to its basis without taking a signed closure.  This is
the appropriate transfer for monotone postprocessings: their threshold
increments are nonnegative and, after the zero function is included, have
total mass one. -/
theorem empiricalOneSidedRademacher_le_of_finite_convex_representation
    {Target Basis : Type*} [Fintype Target] [Nonempty Target]
    [Fintype Basis] [Nonempty Basis]
    (n : ℕ) (targetValue : Target → Fin n → ℝ)
    (basisValue : Basis → Fin n → ℝ)
    (hrepr : ∀ target, ∃ (terms : ℕ) (coefficient : Fin terms → ℝ)
      (basis : Fin terms → Basis),
        (∀ term, 0 ≤ coefficient term) ∧
        (∑ term, coefficient term) = 1 ∧
        ∀ index, targetValue target index =
          ∑ term, coefficient term * basisValue (basis term) index) :
    empiricalOneSidedRademacher n targetValue ≤
      empiricalOneSidedRademacher n basisValue := by
  classical
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro signs
  apply ciSup_le
  intro target
  rcases hrepr target with ⟨terms, coefficient, basis, hnonnegative, hmass, hvalue⟩
  let score : Basis → ℝ := fun b =>
    ∑ index : Fin n, rademacherSign (signs index) * basisValue b index
  let basisSup : ℝ := ⨆ b : Basis,
    ∑ index : Fin n, rademacherSign (signs index) * basisValue b index
  have hscore : ∀ b, score b ≤ basisSup := by
    intro b
    exact le_ciSup (Finite.bddAbove_range _) b
  calc
    (∑ index : Fin n, rademacherSign (signs index) * targetValue target index) =
        ∑ term, coefficient term * score (basis term) := by
      simp_rw [hvalue]
      dsimp [score]
      calc
        (∑ index : Fin n, rademacherSign (signs index) *
            ∑ term, coefficient term * basisValue (basis term) index) =
            ∑ index : Fin n, ∑ term,
              coefficient term *
                (rademacherSign (signs index) * basisValue (basis term) index) := by
              apply Finset.sum_congr rfl
              intro index _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro term _
              ring
        _ = ∑ term, ∑ index : Fin n,
            coefficient term *
              (rademacherSign (signs index) * basisValue (basis term) index) :=
            Finset.sum_comm
        _ = ∑ term, coefficient term * ∑ index : Fin n,
            rademacherSign (signs index) * basisValue (basis term) index := by
              apply Finset.sum_congr rfl
              intro term _
              rw [Finset.mul_sum]
    _ ≤ ∑ term, coefficient term * basisSup := by
      apply Finset.sum_le_sum
      intro term _
      exact mul_le_mul_of_nonneg_left (hscore (basis term)) (hnonnegative term)
    _ = (∑ term, coefficient term) * basisSup := by
      rw [Finset.sum_mul]
    _ = basisSup := by rw [hmass, one_mul]

/--
An exact finite `ℓ₁` representation transfers one-sided empirical
Rademacher complexity to the signed closure of its base class.  The signed
closure is essential: signed coefficients cannot in general be controlled by
the one-sided complexity of a class that is not closed under negation.
-/
theorem empiricalOneSidedRademacher_le_of_finite_l1_representation
    {Target Basis : Type*} [Fintype Target] [Nonempty Target]
    [Fintype Basis] [Nonempty Basis]
    (n : ℕ) (targetValue : Target → Fin n → ℝ)
    (basisValue : Basis → Fin n → ℝ) (coefficientNorm : ℝ)
    (hrepr : ∀ target, ∃ (terms : ℕ) (coefficient : Fin terms → ℝ)
      (basis : Fin terms → Basis),
        (∑ term, |coefficient term|) ≤ coefficientNorm ∧
        ∀ index, targetValue target index =
          ∑ term, coefficient term * basisValue (basis term) index) :
    empiricalOneSidedRademacher n targetValue ≤
      coefficientNorm * empiricalOneSidedRademacher n
        (fun (signedBasis : Bool × Basis) index =>
          if signedBasis.1 then basisValue signedBasis.2 index
          else -basisValue signedBasis.2 index) := by
  classical
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
  calc
    (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => ⨆ target,
          ∑ index : Fin n, rademacherSign (signs index) * targetValue target index) ≤
      (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => coefficientNorm *
          (⨆ signedBasis : Bool × Basis,
            ∑ index : Fin n, rademacherSign (signs index) *
              (if signedBasis.1 then basisValue signedBasis.2 index
                else -basisValue signedBasis.2 index))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
      intro signs
      apply ciSup_le
      intro target
      rcases hrepr target with ⟨terms, coefficient, basis, hnorm, hvalue⟩
      let score : Basis → ℝ := fun b =>
        ∑ index : Fin n, rademacherSign (signs index) * basisValue b index
      let signedSup : ℝ := ⨆ signedBasis : Bool × Basis,
        ∑ index : Fin n, rademacherSign (signs index) *
          (if signedBasis.1 then basisValue signedBasis.2 index
            else -basisValue signedBasis.2 index)
      have hscore : ∀ b, |score b| ≤ signedSup := by
        intro b
        apply (abs_le).2
        constructor
        · have hneg : -score b ≤ signedSup := by
            calc
              -score b = ∑ index : Fin n, rademacherSign (signs index) *
                  (if (false : Bool) then basisValue b index else -basisValue b index) := by
                simp [score]
              _ ≤ signedSup := by
                change (∑ index : Fin n, rademacherSign (signs index) *
                    (if (false : Bool) then basisValue b index else -basisValue b index)) ≤
                  ⨆ signedBasis : Bool × Basis,
                    ∑ index : Fin n, rademacherSign (signs index) *
                      (if signedBasis.1 then basisValue signedBasis.2 index
                        else -basisValue signedBasis.2 index)
                exact le_ciSup
                  (f := fun signedBasis : Bool × Basis =>
                    ∑ index : Fin n, rademacherSign (signs index) *
                      (if signedBasis.1 then basisValue signedBasis.2 index
                        else -basisValue signedBasis.2 index))
                  (Finite.bddAbove_range _) (false, b)
          linarith
        · calc
            score b = ∑ index : Fin n, rademacherSign (signs index) *
                (if (true : Bool) then basisValue b index else -basisValue b index) := by
                  simp [score]
            _ ≤ signedSup := by
              change (∑ index : Fin n, rademacherSign (signs index) *
                  (if (true : Bool) then basisValue b index else -basisValue b index)) ≤
                ⨆ signedBasis : Bool × Basis,
                  ∑ index : Fin n, rademacherSign (signs index) *
                    (if signedBasis.1 then basisValue signedBasis.2 index
                      else -basisValue signedBasis.2 index)
              exact le_ciSup
                (f := fun signedBasis : Bool × Basis =>
                  ∑ index : Fin n, rademacherSign (signs index) *
                    (if signedBasis.1 then basisValue signedBasis.2 index
                      else -basisValue signedBasis.2 index))
                (Finite.bddAbove_range _) (true, b)
      have hsupNonneg : 0 ≤ signedSup := by
        let b : Basis := Classical.choice inferInstance
        exact (abs_nonneg (score b)).trans (hscore b)
      calc
        (∑ index : Fin n, rademacherSign (signs index) * targetValue target index) =
            ∑ term, coefficient term * score (basis term) := by
          simp_rw [hvalue]
          dsimp [score]
          calc
            (∑ index : Fin n, rademacherSign (signs index) *
                ∑ term, coefficient term * basisValue (basis term) index) =
                ∑ index : Fin n, ∑ term,
                  coefficient term *
                    (rademacherSign (signs index) * basisValue (basis term) index) := by
                  apply Finset.sum_congr rfl
                  intro index _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro term _
                  ring
            _ = ∑ term, ∑ index : Fin n,
                coefficient term *
                  (rademacherSign (signs index) * basisValue (basis term) index) :=
                Finset.sum_comm
            _ = ∑ term, coefficient term * ∑ index : Fin n,
                rademacherSign (signs index) * basisValue (basis term) index := by
                  apply Finset.sum_congr rfl
                  intro term _
                  rw [Finset.mul_sum]
        _ ≤ ∑ term, |coefficient term| * |score (basis term)| := by
          apply Finset.sum_le_sum
          intro term _
          rw [← abs_mul]
          exact le_abs_self _
        _ ≤ ∑ term, |coefficient term| * signedSup := by
          apply Finset.sum_le_sum
          intro term _
          exact mul_le_mul_of_nonneg_left (hscore (basis term)) (abs_nonneg _)
        _ = (∑ term, |coefficient term|) * signedSup := by
          rw [Finset.sum_mul]
        _ ≤ coefficientNorm * signedSup :=
          mul_le_mul_of_nonneg_right hnorm hsupNonneg
    _ = coefficientNorm * ((n : ℝ)⁻¹ *
        AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => ⨆ signedBasis : Bool × Basis,
            ∑ index : Fin n, rademacherSign (signs index) *
              (if signedBasis.1 then basisValue signedBasis.2 index
                else -basisValue signedBasis.2 index))) := by
      rw [AppliedModelingLib.pmfExp_const_mul]
      ring

/--
One-sided empirical Rademacher complexity for an arbitrary (possibly
infinite) class.  The score supremum is a real `sSup`, so uses of this
definition must establish the displayed score range is bounded above.
-/
noncomputable def empiricalOneSidedRademacherSet
    (n : ℕ) (value : Hypothesis → Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
    (AppliedModelingLib.uniformPMF (Fin n → Bool)) (fun signs =>
      sSup (Set.range fun hypothesis =>
        ∑ index : Fin n, rademacherSign (signs index) * value hypothesis index))

/-- The set-based one-sided complexity extends the finite-class one.  This
one-way bridge lets a finite source class be compared with a natural
arbitrary-basis class without imposing an artificial finite enumeration of
its real parameters. -/
theorem empiricalOneSidedRademacher_le_empiricalOneSidedRademacherSet
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ) :
    empiricalOneSidedRademacher n value ≤ empiricalOneSidedRademacherSet n value := by
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
    empiricalOneSidedRademacherSet
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro signs
  apply ciSup_le
  intro hypothesis
  apply le_csSup (Finite.bddAbove_range _)
  exact ⟨hypothesis, rfl⟩

/-- A bounded value class has a bounded signed score range on every fixed
Rademacher-sign vector.  This is the analytic side condition needed when a
class is represented by a real supremum rather than a finite maximum. -/
theorem bddAbove_range_rademacherScore_of_abs_le_one
    {Class : Type*} (n : ℕ) (value : Class → Fin n → ℝ)
    (hvalue : ∀ hypothesis index, |value hypothesis index| ≤ 1)
    (signs : Fin n → Bool) :
    BddAbove (Set.range fun hypothesis =>
      ∑ index : Fin n, rademacherSign (signs index) * value hypothesis index) := by
  refine ⟨n, ?_⟩
  rintro score ⟨hypothesis, rfl⟩
  calc
    (∑ index : Fin n, rademacherSign (signs index) * value hypothesis index) ≤
        ∑ _index : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _
      calc
        rademacherSign (signs index) * value hypothesis index ≤
            |rademacherSign (signs index) * value hypothesis index| := le_abs_self _
        _ = |value hypothesis index| := by
          rw [abs_mul, abs_rademacherSign, one_mul]
        _ ≤ 1 := hvalue hypothesis index
    _ = n := by simp

/-- Reindexing an arbitrary class through a value-preserving map cannot
increase its one-sided empirical Rademacher complexity. -/
theorem empiricalOneSidedRademacherSet_le_of_map
    {Small Large : Type*} [Nonempty Small]
    (n : ℕ) (smallValue : Small → Fin n → ℝ)
    (largeValue : Large → Fin n → ℝ) (map : Small → Large)
    (hmap : ∀ small index, smallValue small index = largeValue (map small) index)
    (hlargeBdd : ∀ signs : Fin n → Bool,
      BddAbove (Set.range fun large =>
        ∑ index : Fin n, rademacherSign (signs index) * largeValue large index)) :
    empiricalOneSidedRademacherSet n smallValue ≤
      empiricalOneSidedRademacherSet n largeValue := by
  unfold empiricalOneSidedRademacherSet
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro signs
  apply csSup_le (Set.range_nonempty _)
  rintro score ⟨small, rfl⟩
  have hscore :
      (∑ index : Fin n, rademacherSign (signs index) * smallValue small index) =
        ∑ index : Fin n, rademacherSign (signs index) * largeValue (map small) index := by
    apply Finset.sum_congr rfl
    intro index _
    rw [hmap]
  change (∑ index : Fin n, rademacherSign (signs index) * smallValue small index) ≤ _
  rw [hscore]
  apply le_csSup (hlargeBdd signs)
  exact ⟨map small, rfl⟩

/-- An exact finite convex representation transfers one-sided empirical
Rademacher complexity for an arbitrary class to its basis.  Unlike the
signed `ℓ₁` transfer below, it preserves the unsymmetrized basis exactly when
the coefficients are nonnegative and have total mass one. -/
theorem empiricalOneSidedRademacherSet_le_of_finite_convex_representation
    {Target Basis : Type*} [Nonempty Target] [Nonempty Basis]
    (n : ℕ) (targetValue : Target → Fin n → ℝ)
    (basisValue : Basis → Fin n → ℝ)
    (hbasisBdd : ∀ signs : Fin n → Bool,
      BddAbove (Set.range fun basis =>
        ∑ index : Fin n, rademacherSign (signs index) * basisValue basis index))
    (hrepr : ∀ target, ∃ (terms : ℕ) (coefficient : Fin terms → ℝ)
      (basis : Fin terms → Basis),
        (∀ term, 0 ≤ coefficient term) ∧
        (∑ term, coefficient term) = 1 ∧
        ∀ index, targetValue target index =
          ∑ term, coefficient term * basisValue (basis term) index) :
    empiricalOneSidedRademacherSet n targetValue ≤
      empiricalOneSidedRademacherSet n basisValue := by
  classical
  unfold empiricalOneSidedRademacherSet
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro signs
  apply csSup_le (Set.range_nonempty _)
  rintro score ⟨target, rfl⟩
  rcases hrepr target with ⟨terms, coefficient, basis, hnonnegative, hmass, hvalue⟩
  let basisScore : Basis → ℝ := fun b =>
    ∑ index : Fin n, rademacherSign (signs index) * basisValue b index
  let basisSup : ℝ := sSup (Set.range fun b : Basis =>
    ∑ index : Fin n, rademacherSign (signs index) * basisValue b index)
  have hscore : ∀ b, basisScore b ≤ basisSup := by
    intro b
    apply le_csSup (hbasisBdd signs)
    exact ⟨b, rfl⟩
  calc
    (∑ index : Fin n, rademacherSign (signs index) * targetValue target index) =
        ∑ term, coefficient term * basisScore (basis term) := by
      simp_rw [hvalue]
      dsimp [basisScore]
      calc
        (∑ index : Fin n, rademacherSign (signs index) *
            ∑ term, coefficient term * basisValue (basis term) index) =
            ∑ index : Fin n, ∑ term,
              coefficient term *
                (rademacherSign (signs index) * basisValue (basis term) index) := by
              apply Finset.sum_congr rfl
              intro index _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro term _
              ring
        _ = ∑ term, ∑ index : Fin n,
            coefficient term *
              (rademacherSign (signs index) * basisValue (basis term) index) :=
            Finset.sum_comm
        _ = ∑ term, coefficient term * ∑ index : Fin n,
            rademacherSign (signs index) * basisValue (basis term) index := by
              apply Finset.sum_congr rfl
              intro term _
              rw [Finset.mul_sum]
    _ ≤ ∑ term, coefficient term * basisSup := by
      apply Finset.sum_le_sum
      intro term _
      exact mul_le_mul_of_nonneg_left (hscore (basis term)) (hnonnegative term)
    _ = (∑ term, coefficient term) * basisSup := by
      rw [Finset.sum_mul]
    _ = basisSup := by rw [hmass, one_mul]

/--
An exact finite `ℓ₁` representation transfers one-sided empirical
Rademacher complexity for an arbitrary class to the signed closure of its
basis class.  This is the infinite-class counterpart of
`empiricalOneSidedRademacher_le_of_finite_l1_representation`; the explicit
boundedness premise is what makes each real supremum well-defined.
-/
theorem empiricalOneSidedRademacherSet_le_of_finite_l1_representation
    {Target Basis : Type*} [Nonempty Target] [Nonempty Basis]
    (n : ℕ) (targetValue : Target → Fin n → ℝ)
    (basisValue : Basis → Fin n → ℝ) (coefficientNorm : ℝ)
    (hsignedBdd : ∀ signs : Fin n → Bool,
      BddAbove (Set.range fun signedBasis : Bool × Basis =>
        ∑ index : Fin n, rademacherSign (signs index) *
          (if signedBasis.1 then basisValue signedBasis.2 index
          else -basisValue signedBasis.2 index)))
    (hrepr : ∀ target, ∃ (terms : ℕ) (coefficient : Fin terms → ℝ)
      (basis : Fin terms → Basis),
        (∑ term, |coefficient term|) ≤ coefficientNorm ∧
        ∀ index, targetValue target index =
          ∑ term, coefficient term * basisValue (basis term) index) :
    empiricalOneSidedRademacherSet n targetValue ≤
      coefficientNorm * empiricalOneSidedRademacherSet n
        (fun (signedBasis : Bool × Basis) index =>
          if signedBasis.1 then basisValue signedBasis.2 index
          else -basisValue signedBasis.2 index) := by
  classical
  unfold empiricalOneSidedRademacherSet
  calc
    (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => sSup (Set.range fun target =>
          ∑ index : Fin n, rademacherSign (signs index) * targetValue target index)) ≤
      (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => coefficientNorm * sSup (Set.range fun signedBasis : Bool × Basis =>
          ∑ index : Fin n, rademacherSign (signs index) *
            (if signedBasis.1 then basisValue signedBasis.2 index
            else -basisValue signedBasis.2 index))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
      intro signs
      apply csSup_le (Set.range_nonempty _)
      rintro score ⟨target, rfl⟩
      rcases hrepr target with ⟨terms, coefficient, basis, hnorm, hvalue⟩
      let basisScore : Basis → ℝ := fun b =>
        ∑ index : Fin n, rademacherSign (signs index) * basisValue b index
      let signedSup : ℝ := sSup (Set.range fun signedBasis : Bool × Basis =>
        ∑ index : Fin n, rademacherSign (signs index) *
          (if signedBasis.1 then basisValue signedBasis.2 index
          else -basisValue signedBasis.2 index))
      have hscore : ∀ b, |basisScore b| ≤ signedSup := by
        intro b
        apply (abs_le).2
        constructor
        · have hneg : -basisScore b ≤ signedSup := by
            calc
              -basisScore b = ∑ index : Fin n, rademacherSign (signs index) *
                  (if (false : Bool) then basisValue b index else -basisValue b index) := by
                    simp [basisScore]
              _ ≤ signedSup := by
                apply le_csSup (hsignedBdd signs)
                exact ⟨(false, b), rfl⟩
          linarith
        · calc
            basisScore b = ∑ index : Fin n, rademacherSign (signs index) *
                (if (true : Bool) then basisValue b index else -basisValue b index) := by
                  simp [basisScore]
            _ ≤ signedSup := by
              apply le_csSup (hsignedBdd signs)
              exact ⟨(true, b), rfl⟩
      have hsupNonneg : 0 ≤ signedSup := by
        let b : Basis := Classical.choice inferInstance
        exact (abs_nonneg (basisScore b)).trans (hscore b)
      calc
        (∑ index : Fin n, rademacherSign (signs index) * targetValue target index) =
            ∑ term, coefficient term * basisScore (basis term) := by
          simp_rw [hvalue]
          dsimp [basisScore]
          calc
            (∑ index : Fin n, rademacherSign (signs index) *
                ∑ term, coefficient term * basisValue (basis term) index) =
                ∑ index : Fin n, ∑ term,
                  coefficient term *
                    (rademacherSign (signs index) * basisValue (basis term) index) := by
                  apply Finset.sum_congr rfl
                  intro index _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro term _
                  ring
            _ = ∑ term, ∑ index : Fin n,
                coefficient term *
                  (rademacherSign (signs index) * basisValue (basis term) index) :=
                Finset.sum_comm
            _ = ∑ term, coefficient term * ∑ index : Fin n,
                rademacherSign (signs index) * basisValue (basis term) index := by
                  apply Finset.sum_congr rfl
                  intro term _
                  rw [Finset.mul_sum]
        _ ≤ ∑ term, |coefficient term| * |basisScore (basis term)| := by
          apply Finset.sum_le_sum
          intro term _
          rw [← abs_mul]
          exact le_abs_self _
        _ ≤ ∑ term, |coefficient term| * signedSup := by
          apply Finset.sum_le_sum
          intro term _
          exact mul_le_mul_of_nonneg_left (hscore (basis term)) (abs_nonneg _)
        _ = (∑ term, |coefficient term|) * signedSup := by
          rw [Finset.sum_mul]
        _ ≤ coefficientNorm * signedSup :=
          mul_le_mul_of_nonneg_right hnorm hsupNonneg
    _ = coefficientNorm * ((n : ℝ)⁻¹ *
        AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => sSup (Set.range fun signedBasis : Bool × Basis =>
            ∑ index : Fin n, rademacherSign (signs index) *
              (if signedBasis.1 then basisValue signedBasis.2 index
              else -basisValue signedBasis.2 index)))) := by
      rw [AppliedModelingLib.pmfExp_const_mul]
      ring

/-- A supremum over a product class splits across additively separable scores. -/
theorem iSup_prod_add_le_add_iSup
    {Left Right : Type*} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right]
    (left : Left → ℝ) (right : Right → ℝ) :
    (⨆ pair : Left × Right, left pair.1 + right pair.2) ≤
      (⨆ hypothesis, left hypothesis) + ⨆ hypothesis, right hypothesis := by
  apply ciSup_le
  intro pair
  exact add_le_add
    (le_ciSup (Finite.bddAbove_range left) pair.1)
    (le_ciSup (Finite.bddAbove_range right) pair.2)

/-- Empirical one-sided complexity is subadditive for a product-indexed sum class. -/
theorem empiricalOneSidedRademacher_prod_add_le
    {Left Right : Type*} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right]
    (n : ℕ) (left : Left → Fin n → ℝ)
    (right : Right → Fin n → ℝ) :
    empiricalOneSidedRademacher n
        (fun pair : Left × Right => fun index =>
          left pair.1 index + right pair.2 index) ≤
      empiricalOneSidedRademacher n left +
        empiricalOneSidedRademacher n right := by
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
  rw [← mul_add]
  rw [← AppliedModelingLib.pmfExp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro signs
  let leftScore : Left → ℝ := fun hypothesis =>
    ∑ index : Fin n,
      rademacherSign (signs index) * left hypothesis index
  let rightScore : Right → ℝ := fun hypothesis =>
    ∑ index : Fin n,
      rademacherSign (signs index) * right hypothesis index
  have hpoint : ∀ pair : Left × Right,
      (∑ index : Fin n,
        rademacherSign (signs index) *
          (left pair.1 index + right pair.2 index)) =
        leftScore pair.1 + rightScore pair.2 := by
    intro pair
    simp only [leftScore, rightScore, mul_add, Finset.sum_add_distrib]
  rw [show (fun pair : Left × Right =>
      ∑ index : Fin n,
        rademacherSign (signs index) *
          (left pair.1 index + right pair.2 index)) =
      (fun pair => leftScore pair.1 + rightScore pair.2) by
        funext pair
        exact hpoint pair]
  exact iSup_prod_add_le_add_iSup leftScore rightScore

/-- A finite product class with values in `[-1, 1]` has one-sided empirical
Rademacher complexity at most twice the sum of the complexities of its two
factors.  The proof uses the clipped-square polarization identity and scalar
contraction, avoiding a separate vector-contraction theorem. -/
theorem empiricalOneSidedRademacher_mul_le_two_add
    {Left Right : Type*} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right]
    (n : ℕ) (left : Left → Fin n → ℝ) (right : Right → Fin n → ℝ)
    (hleft : ∀ hypothesis index, |left hypothesis index| ≤ 1)
    (hright : ∀ hypothesis index, |right hypothesis index| ≤ 1) :
    empiricalOneSidedRademacher n
        (fun pair : Left × Right => fun index => left pair.1 index * right pair.2 index) ≤
      2 * (empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right) := by
  let plus : Left × Right → Fin n → ℝ := fun pair index =>
    left pair.1 index + right pair.2 index
  let negativeRight : Right → Fin n → ℝ := fun hypothesis index => -right hypothesis index
  let minus : Left × Right → Fin n → ℝ := fun pair index =>
    left pair.1 index - right pair.2 index
  let squarePlus : Left × Right → Fin n → ℝ := fun pair index =>
    clippedSquare (plus pair index)
  let negativeSquareMinus : Left × Right → Fin n → ℝ := fun pair index =>
    -clippedSquare (minus pair index)
  let squareSum : Left × Right → Fin n → ℝ := fun pair index =>
    squarePlus pair index + negativeSquareMinus pair index
  have hpolarized :
      (fun pair : Left × Right => fun index => left pair.1 index * right pair.2 index) =
        fun pair index => squareSum pair index / 4 := by
    funext pair index
    dsimp [squareSum, squarePlus, negativeSquareMinus, plus, minus]
    rw [mul_eq_clippedSquare_polarization_of_abs_le_one]
    · ring
    · exact hleft pair.1 index
    · exact hright pair.2 index
  have hscale :
      empiricalOneSidedRademacher n (fun pair index => squareSum pair index / 4) ≤
        (1 / 4 : ℝ) * empiricalOneSidedRademacher n squareSum := by
    simpa using empiricalOneSidedRademacher_contraction (L := (1 / 4 : ℝ)) n squareSum
      (fun _ input => input / 4) (by norm_num)
      (fun _ first second => by
        rw [show first / 4 - second / 4 = (first - second) / 4 by ring, abs_div]
        norm_num
        nlinarith [abs_nonneg (first - second)])
  have hsum :
      empiricalOneSidedRademacher n squareSum ≤
        empiricalOneSidedRademacher n squarePlus +
          empiricalOneSidedRademacher n negativeSquareMinus := by
    simpa [squareSum] using empiricalOneSidedRademacher_add_le n squarePlus negativeSquareMinus
  have hsquarePlus :
      empiricalOneSidedRademacher n squarePlus ≤
        4 * empiricalOneSidedRademacher n plus := by
    simpa [squarePlus] using empiricalOneSidedRademacher_contraction (L := (4 : ℝ)) n plus
      (fun _ input => clippedSquare input) (by norm_num)
      (fun _ first second => abs_clippedSquare_sub_le_four_abs_sub first second)
  have hnegativeSquareMinus :
      empiricalOneSidedRademacher n negativeSquareMinus ≤
        4 * empiricalOneSidedRademacher n minus := by
    simpa [negativeSquareMinus] using
      empiricalOneSidedRademacher_contraction (L := (4 : ℝ)) n minus
      (fun _ input => -clippedSquare input) (by norm_num)
      (fun _ first second => by
        rw [show -clippedSquare first - -clippedSquare second =
          -(clippedSquare first - clippedSquare second) by ring, abs_neg]
        exact abs_clippedSquare_sub_le_four_abs_sub first second)
  have hplus :
      empiricalOneSidedRademacher n plus ≤
        empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right := by
    simpa [plus] using empiricalOneSidedRademacher_prod_add_le n left right
  have hnegativeRight :
      empiricalOneSidedRademacher n negativeRight ≤ empiricalOneSidedRademacher n right := by
    simpa [negativeRight] using
      empiricalOneSidedRademacher_contraction (L := (1 : ℝ)) n right
      (fun _ input => -input) (by norm_num)
      (fun _ first second => by
        rw [show -first - -second = -(first - second) by ring, abs_neg]
        norm_num)
  have hminusRaw :
      empiricalOneSidedRademacher n minus ≤
        empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n negativeRight := by
    simpa [minus, negativeRight, sub_eq_add_neg] using
      empiricalOneSidedRademacher_prod_add_le n left negativeRight
  have hminus :
      empiricalOneSidedRademacher n minus ≤
        empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right :=
    hminusRaw.trans (add_le_add (le_refl _) hnegativeRight)
  calc
    empiricalOneSidedRademacher n
        (fun pair : Left × Right => fun index => left pair.1 index * right pair.2 index) =
        empiricalOneSidedRademacher n (fun pair index => squareSum pair index / 4) := by
      rw [hpolarized]
    _ ≤ (1 / 4 : ℝ) * empiricalOneSidedRademacher n squareSum := hscale
    _ ≤ (1 / 4 : ℝ) *
        (empiricalOneSidedRademacher n squarePlus +
          empiricalOneSidedRademacher n negativeSquareMinus) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (1 / 4 : ℝ) *
        (4 * empiricalOneSidedRademacher n plus +
          4 * empiricalOneSidedRademacher n minus) :=
      mul_le_mul_of_nonneg_left (add_le_add hsquarePlus hnegativeSquareMinus) (by norm_num)
    _ ≤ (1 / 4 : ℝ) *
        (4 * (empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right) +
          4 * (empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hplus (by norm_num))
          (mul_le_mul_of_nonneg_left hminus (by norm_num)))
        (by norm_num)
    _ = 2 * (empiricalOneSidedRademacher n left + empiricalOneSidedRademacher n right) := by
      ring

/-- The product-class Rademacher bound does not require a finite source
class.  For every positive error tolerance, choose one almost-maximizing
factor pair for each of the finitely many sign vectors, apply the finite
product inequality to those selected factors, and then let the tolerance
vanish. -/
theorem empiricalOneSidedRademacherSet_mul_le_two_add
    {Left Right : Type*} [Nonempty Left] [Nonempty Right]
    (n : ℕ) (left : Left → Fin n → ℝ) (right : Right → Fin n → ℝ)
    (hleft : ∀ hypothesis index, |left hypothesis index| ≤ 1)
    (hright : ∀ hypothesis index, |right hypothesis index| ≤ 1) :
    empiricalOneSidedRademacherSet n
        (fun pair : Left × Right => fun index => left pair.1 index * right pair.2 index) ≤
      2 * (empiricalOneSidedRademacherSet n left +
        empiricalOneSidedRademacherSet n right) := by
  classical
  let productValue : Left × Right → Fin n → ℝ := fun pair index =>
    left pair.1 index * right pair.2 index
  have hproductBound : ∀ pair index, |productValue pair index| ≤ 1 := by
    intro pair index
    dsimp [productValue]
    calc
      |left pair.1 index * right pair.2 index| =
          |left pair.1 index| * |right pair.2 index| := abs_mul _ _
      _ ≤ 1 * 1 := by
        exact mul_le_mul (hleft pair.1 index) (hright pair.2 index)
          (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hleftBdd := bddAbove_range_rademacherScore_of_abs_le_one n left hleft
  have hrightBdd := bddAbove_range_rademacherScore_of_abs_le_one n right hright
  have hproductBdd :=
    bddAbove_range_rademacherScore_of_abs_le_one n productValue hproductBound
  by_cases hn : n = 0
  · subst n
    simp [empiricalOneSidedRademacherSet]
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hnRealNe : (n : ℝ) ≠ 0 := ne_of_gt hnRealPos
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let productScore : (Fin n → Bool) → Left × Right → ℝ := fun signs pair =>
    ∑ index : Fin n, rademacherSign (signs index) * productValue pair index
  have hselection : ∀ signs : Fin n → Bool, ∃ pair : Left × Right,
      sSup (Set.range (productScore signs)) - (n : ℝ) * epsilon <
        productScore signs pair := by
    intro signs
    have hlt : sSup (Set.range (productScore signs)) - (n : ℝ) * epsilon <
        sSup (Set.range (productScore signs)) :=
      sub_lt_self _ (mul_pos hnRealPos hepsilon)
    rcases (lt_csSup_iff (hproductBdd signs) (Set.range_nonempty _)).mp hlt with
      ⟨score, ⟨pair, rfl⟩, hscore⟩
    exact ⟨pair, hscore⟩
  choose selected hselected using hselection
  let selectedLeft : (Fin n → Bool) → Left := fun signs => (selected signs).1
  let selectedRight : (Fin n → Bool) → Right := fun signs => (selected signs).2
  let selectedLeftValue : (Fin n → Bool) → Fin n → ℝ := fun signs index =>
    left (selectedLeft signs) index
  let selectedRightValue : (Fin n → Bool) → Fin n → ℝ := fun signs index =>
    right (selectedRight signs) index
  let selectedProduct : (Fin n → Bool) × (Fin n → Bool) → Fin n → ℝ :=
    fun pair index => selectedLeftValue pair.1 index * selectedRightValue pair.2 index
  let selectedScore : (Fin n → Bool) → ℝ := fun signs =>
    ⨆ pair : (Fin n → Bool) × (Fin n → Bool),
      ∑ index : Fin n, rademacherSign (signs index) * selectedProduct pair index
  have happrox : ∀ signs : Fin n → Bool,
      sSup (Set.range (productScore signs)) ≤
        selectedScore signs + (n : ℝ) * epsilon := by
    intro signs
    have hselectedLe : productScore signs (selected signs) ≤ selectedScore signs := by
      dsimp [productScore, selectedScore, selectedProduct, selectedLeft, selectedRight]
      exact le_ciSup
        (f := fun pair : (Fin n → Bool) × (Fin n → Bool) =>
          ∑ index : Fin n, rademacherSign (signs index) *
            (left (selected pair.1).1 index * right (selected pair.2).2 index))
        (Finite.bddAbove_range _) (signs, signs)
    linarith [hselected signs]
  have hfiniteApprox :
      empiricalOneSidedRademacherSet n productValue ≤
        empiricalOneSidedRademacher n selectedProduct + epsilon := by
    change (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
        (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => sSup (Set.range (productScore signs))) ≤
      (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
        (AppliedModelingLib.uniformPMF (Fin n → Bool)) selectedScore + epsilon
    calc
      (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
          (AppliedModelingLib.uniformPMF (Fin n → Bool))
            (fun signs => sSup (Set.range (productScore signs))) ≤
          (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
            (AppliedModelingLib.uniformPMF (Fin n → Bool))
              (fun signs => selectedScore signs + (n : ℝ) * epsilon) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro signs
            exact happrox signs
      _ = (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
            (AppliedModelingLib.uniformPMF (Fin n → Bool)) selectedScore + epsilon := by
            rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const, mul_add,
              ← mul_assoc, inv_mul_cancel₀ hnRealNe, one_mul]
  have hselectedLeftBound : ∀ signs index, |selectedLeftValue signs index| ≤ 1 := by
    intro signs index
    exact hleft (selectedLeft signs) index
  have hselectedRightBound : ∀ signs index, |selectedRightValue signs index| ≤ 1 := by
    intro signs index
    exact hright (selectedRight signs) index
  have hfiniteLeft : empiricalOneSidedRademacher n selectedLeftValue ≤
      empiricalOneSidedRademacherSet n left := by
    calc
      empiricalOneSidedRademacher n selectedLeftValue ≤
          empiricalOneSidedRademacherSet n selectedLeftValue :=
        empiricalOneSidedRademacher_le_empiricalOneSidedRademacherSet n selectedLeftValue
      _ ≤ empiricalOneSidedRademacherSet n left := by
        exact empiricalOneSidedRademacherSet_le_of_map n selectedLeftValue left selectedLeft
          (fun _ _ => rfl) hleftBdd
  have hfiniteRight : empiricalOneSidedRademacher n selectedRightValue ≤
      empiricalOneSidedRademacherSet n right := by
    calc
      empiricalOneSidedRademacher n selectedRightValue ≤
          empiricalOneSidedRademacherSet n selectedRightValue :=
        empiricalOneSidedRademacher_le_empiricalOneSidedRademacherSet n selectedRightValue
      _ ≤ empiricalOneSidedRademacherSet n right := by
        exact empiricalOneSidedRademacherSet_le_of_map n selectedRightValue right selectedRight
          (fun _ _ => rfl) hrightBdd
  have hfiniteProduct : empiricalOneSidedRademacher n selectedProduct ≤
      2 * (empiricalOneSidedRademacher n selectedLeftValue +
        empiricalOneSidedRademacher n selectedRightValue) := by
    exact empiricalOneSidedRademacher_mul_le_two_add n selectedLeftValue selectedRightValue
      hselectedLeftBound hselectedRightBound
  have hfiniteBound : empiricalOneSidedRademacher n selectedProduct ≤
      2 * (empiricalOneSidedRademacherSet n left +
        empiricalOneSidedRademacherSet n right) :=
    hfiniteProduct.trans <|
      mul_le_mul_of_nonneg_left (add_le_add hfiniteLeft hfiniteRight) (by norm_num)
  change empiricalOneSidedRademacherSet n productValue ≤ _
  exact hfiniteApprox.trans (add_le_add hfiniteBound (le_refl _))

/-- One-sided scalar Rademacher contraction extends to arbitrary bounded
classes.  The proof selects one near-maximizer for each finite sign vector,
uses the finite contraction inequality on that selected class, and passes to
the limit through an arbitrary positive tolerance. -/
theorem empiricalOneSidedRademacherSet_contraction
    {Class : Type*} [Nonempty Class]
    (n : ℕ) (value : Class → Fin n → ℝ) (psi : Fin n → ℝ → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hpsi : ∀ index first second,
      |psi index first - psi index second| ≤ L * |first - second|)
    (hvalueBdd : ∀ signs : Fin n → Bool,
      BddAbove (Set.range fun hypothesis =>
        ∑ index : Fin n, rademacherSign (signs index) * value hypothesis index))
    (htransformedBdd : ∀ signs : Fin n → Bool,
      BddAbove (Set.range fun hypothesis =>
        ∑ index : Fin n, rademacherSign (signs index) *
          psi index (value hypothesis index))) :
    empiricalOneSidedRademacherSet n
        (fun hypothesis index => psi index (value hypothesis index)) ≤
      L * empiricalOneSidedRademacherSet n value := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [empiricalOneSidedRademacherSet]
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hnRealNe : (n : ℝ) ≠ 0 := ne_of_gt hnRealPos
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let transformedScore : (Fin n → Bool) → Class → ℝ := fun signs hypothesis =>
    ∑ index : Fin n, rademacherSign (signs index) * psi index (value hypothesis index)
  have hselection : ∀ signs : Fin n → Bool, ∃ hypothesis : Class,
      sSup (Set.range (transformedScore signs)) - (n : ℝ) * epsilon <
        transformedScore signs hypothesis := by
    intro signs
    have hlt : sSup (Set.range (transformedScore signs)) - (n : ℝ) * epsilon <
        sSup (Set.range (transformedScore signs)) :=
      sub_lt_self _ (mul_pos hnRealPos hepsilon)
    rcases (lt_csSup_iff (htransformedBdd signs) (Set.range_nonempty _)).mp hlt with
      ⟨score, ⟨hypothesis, rfl⟩, hscore⟩
    exact ⟨hypothesis, hscore⟩
  choose selected hselected using hselection
  let selectedValue : (Fin n → Bool) → Fin n → ℝ := fun signs index =>
    value (selected signs) index
  let selectedScore : (Fin n → Bool) → ℝ := fun signs =>
    ⨆ hypothesis : Fin n → Bool,
      ∑ index : Fin n, rademacherSign (signs index) *
        psi index (selectedValue hypothesis index)
  have happrox : ∀ signs : Fin n → Bool,
      sSup (Set.range (transformedScore signs)) ≤
        selectedScore signs + (n : ℝ) * epsilon := by
    intro signs
    have hselectedLe : transformedScore signs (selected signs) ≤ selectedScore signs := by
      dsimp [transformedScore, selectedScore, selectedValue]
      exact le_ciSup
        (f := fun hypothesis : Fin n → Bool =>
          ∑ index : Fin n, rademacherSign (signs index) *
            psi index (value (selected hypothesis) index))
        (Finite.bddAbove_range _) signs
    linarith [hselected signs]
  have hfiniteApprox :
      empiricalOneSidedRademacherSet n
          (fun hypothesis index => psi index (value hypothesis index)) ≤
        empiricalOneSidedRademacher n
          (fun hypothesis index => psi index (selectedValue hypothesis index)) + epsilon := by
    change (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
        (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => sSup (Set.range (transformedScore signs))) ≤
      (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
        (AppliedModelingLib.uniformPMF (Fin n → Bool)) selectedScore + epsilon
    calc
      (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
          (AppliedModelingLib.uniformPMF (Fin n → Bool))
            (fun signs => sSup (Set.range (transformedScore signs))) ≤
          (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
            (AppliedModelingLib.uniformPMF (Fin n → Bool))
              (fun signs => selectedScore signs + (n : ℝ) * epsilon) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro signs
            exact happrox signs
      _ = (n : ℝ)⁻¹ * AppliedModelingLib.pmfExp
            (AppliedModelingLib.uniformPMF (Fin n → Bool)) selectedScore + epsilon := by
            rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const, mul_add,
              ← mul_assoc, inv_mul_cancel₀ hnRealNe, one_mul]
  have hfiniteValue : empiricalOneSidedRademacher n selectedValue ≤
      empiricalOneSidedRademacherSet n value := by
    calc
      empiricalOneSidedRademacher n selectedValue ≤
          empiricalOneSidedRademacherSet n selectedValue :=
        empiricalOneSidedRademacher_le_empiricalOneSidedRademacherSet n selectedValue
      _ ≤ empiricalOneSidedRademacherSet n value := by
        exact empiricalOneSidedRademacherSet_le_of_map n selectedValue value selected
          (fun _ _ => rfl) hvalueBdd
  have hfiniteContraction : empiricalOneSidedRademacher n
      (fun hypothesis index => psi index (selectedValue hypothesis index)) ≤
      L * empiricalOneSidedRademacher n selectedValue := by
    exact empiricalOneSidedRademacher_contraction n selectedValue psi hL hpsi
  have hfiniteBound : empiricalOneSidedRademacher n
      (fun hypothesis index => psi index (selectedValue hypothesis index)) ≤
      L * empiricalOneSidedRademacherSet n value :=
    hfiniteContraction.trans <|
      mul_le_mul_of_nonneg_left hfiniteValue hL
  exact hfiniteApprox.trans (add_le_add hfiniteBound (le_refl _))

/--
The maximum of the image of a finite nonempty type is its order-theoretic
supremum.  This bridges executable `Finset.max'` definitions to reusable
finite-supremum lemmas.
-/
theorem image_univ_max'_eq_iSup
    [Fintype Hypothesis] [DecidableEq Hypothesis] [Nonempty Hypothesis]
    (value : Hypothesis → ℝ) :
    ((Finset.univ : Finset Hypothesis).image value).max'
        (Finset.univ_nonempty.image value) =
      ⨆ hypothesis, value hypothesis := by
  apply le_antisymm
  · apply Finset.max'_le
    intro score hscore
    rcases Finset.mem_image.mp hscore with ⟨hypothesis, _, rfl⟩
    exact le_ciSup (Finite.bddAbove_range value) hypothesis
  · apply ciSup_le
    intro hypothesis
    exact Finset.le_max' _ _
      (Finset.mem_image.mpr ⟨hypothesis, Finset.mem_univ _, rfl⟩)

/-- Finite-PMF Jensen inequality for the exponential function. -/
theorem exp_pmfExp_le_pmfExp_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (value : Outcome → ℝ) :
    Real.exp (AppliedModelingLib.pmfExp law value) ≤
      AppliedModelingLib.pmfExp law (fun outcome => Real.exp (value outcome)) := by
  unfold AppliedModelingLib.pmfExp
  simpa [smul_eq_mul] using
    (convexOn_exp.map_sum_le
      (t := (Finset.univ : Finset Outcome))
      (w := fun outcome => (law outcome).toReal)
      (p := value)
      (fun outcome _ => ENNReal.toReal_nonneg)
      (AppliedModelingLib.pmfToRealSum law)
      (fun _ _ => Set.mem_univ _))

/-- A finite expectation is invariant under a mass-preserving equivalence. -/
theorem pmfExp_comp_equiv_eq_of_apply_eq
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (equiv : Outcome ≃ Outcome)
    (hlaw : ∀ outcome, law (equiv outcome) = law outcome)
    (value : Outcome → ℝ) :
    AppliedModelingLib.pmfExp law (fun outcome => value (equiv outcome)) =
      AppliedModelingLib.pmfExp law value := by
  unfold AppliedModelingLib.pmfExp
  calc
    (∑ outcome : Outcome,
        (law outcome).toReal * value (equiv outcome)) =
      ∑ outcome : Outcome,
        (law (equiv outcome)).toReal * value (equiv outcome) := by
          apply Finset.sum_congr rfl
          intro outcome _
          rw [hlaw]
    _ = ∑ outcome : Outcome,
        (law outcome).toReal * value outcome := by
      exact equiv.sum_comp
        (fun outcome => (law outcome).toReal * value outcome)

/-- Swap the two members of selected coordinate pairs according to Boolean signs. -/
def swapPairsBySigns
    {Index Outcome : Type*} (signs : Index → Bool) :
    (Index → Outcome × Outcome) ≃ (Index → Outcome × Outcome) where
  toFun sample index := if signs index then sample index else (sample index).swap
  invFun sample index := if signs index then sample index else (sample index).swap
  left_inv sample := by
    funext index
    cases hsign : signs index <;> rcases hsample : sample index with ⟨first, second⟩ <;>
      simp [hsign, hsample]
  right_inv sample := by
    funext index
    cases hsign : signs index <;> rcases hsample : sample index with ⟨first, second⟩ <;>
      simp [hsign, hsample]

/-- The iid law of equal-coordinate pairs is invariant under sign-selected swaps. -/
theorem pmfProduct_pmfProd_apply_swapPairsBySigns
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Outcome] (law : PMF Outcome) (signs : Index → Bool)
    (sample : Index → Outcome × Outcome) :
    AppliedModelingLib.pmfProduct Index (Outcome × Outcome)
        (AppliedModelingLib.pmfProd law law) (swapPairsBySigns signs sample) =
      AppliedModelingLib.pmfProduct Index (Outcome × Outcome)
        (AppliedModelingLib.pmfProd law law) sample := by
  rw [AppliedModelingLib.pmfProduct_apply, AppliedModelingLib.pmfProduct_apply]
  apply Finset.prod_congr rfl
  intro index _
  cases hsign : signs index <;>
    rcases hsample : sample index with ⟨first, second⟩ <;>
    simp [swapPairsBySigns, hsign, hsample, AppliedModelingLib.pmfProd_apply, mul_comm]

/-- Swapping a coordinate pair inserts its corresponding Rademacher sign. -/
theorem pairDifference_swapPairsBySigns
    {Index Outcome : Type*} (signs : Index → Bool)
    (sample : Index → Outcome × Outcome) (index : Index)
    (value : Outcome → ℝ) :
    value ((swapPairsBySigns signs sample) index).1 -
        value ((swapPairsBySigns signs sample) index).2 =
      rademacherSign (signs index) *
        (value (sample index).1 - value (sample index).2) := by
  cases hsign : signs index <;>
    rcases hsample : sample index with ⟨first, second⟩ <;>
    simp [swapPairsBySigns, hsign, hsample, rademacherSign] <;> ring

/-- Mean of a real-valued hypothesis under a finite population law. -/
noncomputable def finitePopulationMean
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (value : Hypothesis → Outcome → ℝ)
    (hypothesis : Hypothesis) : ℝ :=
  AppliedModelingLib.pmfExp law (value hypothesis)

/-- Normalized empirical mean of a hypothesis on a length-`n` sample. -/
noncomputable def finiteEmpiricalMean
    {Outcome : Type*} (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) (hypothesis : Hypothesis) : ℝ :=
  (n : ℝ)⁻¹ * ∑ index : Fin n, value hypothesis (sample index)

/-- The empirical mean of an iid finite sample is unbiased. -/
theorem pmfExp_finiteEmpiricalMean_eq_finitePopulationMean
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ) (hypothesis : Hypothesis) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => finiteEmpiricalMean n value sample hypothesis) =
      finitePopulationMean law value hypothesis := by
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold finiteEmpiricalMean finitePopulationMean
  rw [AppliedModelingLib.pmfExp_const_mul]
  rw [AppliedModelingLib.pmfExp_sum]
  simp_rw [AppliedModelingLib.pmfExp_pmfProduct_eval]
  simp [hnReal]

/-- One-sided population-minus-empirical uniform deviation. -/
noncomputable def finiteUpperUniformDeviation
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) : ℝ :=
  ⨆ hypothesis,
    finitePopulationMean law value hypothesis -
      finiteEmpiricalMean n value sample hypothesis

/-- One-sided empirical-minus-population uniform deviation. -/
noncomputable def finiteLowerUniformDeviation
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) : ℝ :=
  ⨆ hypothesis,
    finiteEmpiricalMean n value sample hypothesis -
      finitePopulationMean law value hypothesis

/-- One-sided population-minus-empirical uniform deviation for an arbitrary
function class.  The real supremum is deliberate: range bounds supplied at
the theorem boundary, rather than a finite enumeration of the class, justify
the analytic uses of this definition. -/
noncomputable def finiteUpperUniformDeviationSet
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) : ℝ :=
  sSup (Set.range fun hypothesis =>
    finitePopulationMean law value hypothesis -
      finiteEmpiricalMean n value sample hypothesis)

/-- One-sided empirical-minus-population uniform deviation for an arbitrary
function class. -/
noncomputable def finiteLowerUniformDeviationSet
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) : ℝ :=
  sSup (Set.range fun hypothesis =>
    finiteEmpiricalMean n value sample hypothesis -
      finitePopulationMean law value hypothesis)

/-- A finite supremum of pointwise sums is at most the sum of the suprema. -/
theorem iSup_add_le_add_iSup_finite
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (left right : Hypothesis → ℝ) :
    (⨆ hypothesis, left hypothesis + right hypothesis) ≤
      (⨆ hypothesis, left hypothesis) + ⨆ hypothesis, right hypothesis := by
  apply ciSup_le
  intro hypothesis
  exact add_le_add
    (le_ciSup (Finite.bddAbove_range left) hypothesis)
    (le_ciSup (Finite.bddAbove_range right) hypothesis)

/-- Flip every Boolean sign; this is an involutive equivalence. -/
def negateBooleanSigns (Index : Type*) :
    (Index → Bool) ≃ (Index → Bool) where
  toFun signs index := !(signs index)
  invFun signs index := !(signs index)
  left_inv signs := by
    funext index
    simp only [Bool.not_not]
  right_inv signs := by
    funext index
    simp only [Bool.not_not]

@[simp] theorem negateBooleanSigns_apply
    (Index : Type*) (signs : Index → Bool) (index : Index) :
    negateBooleanSigns Index signs index = !(signs index) := rfl

/-- Flipping a Boolean sign negates its real Rademacher encoding. -/
theorem rademacherSign_not (sign : Bool) :
    rademacherSign (!sign) = -rademacherSign sign := by
  cases sign <;> simp [rademacherSign]

/-- Uniform sign expectation is invariant under flipping every sign. -/
theorem pmfExp_uniformPMF_negateBooleanSigns
    (Index : Type*) [Fintype Index] [DecidableEq Index]
    (value : (Index → Bool) → ℝ) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Index → Bool))
        (fun signs => value (negateBooleanSigns Index signs)) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Index → Bool)) value :=
  AppliedModelingLib.pmfExp_uniformPMF_comp_equiv (negateBooleanSigns Index) value

/--
A fixed sample's one-sided deviation is dominated by its ghost-sample
difference.  This is the finite-PMF form of the first symmetrization step.
-/
theorem finiteUpperUniformDeviation_le_ghostSample
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ) (sample : Fin n → Outcome) :
    finiteUpperUniformDeviation law n value sample ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun ghost => ⨆ hypothesis,
          finiteEmpiricalMean n value ghost hypothesis -
            finiteEmpiricalMean n value sample hypothesis) := by
  obtain ⟨maximizer, hmaximizer⟩ :=
    exists_eq_ciSup_of_finite
      (f := fun hypothesis =>
        finitePopulationMean law value hypothesis -
          finiteEmpiricalMean n value sample hypothesis)
  rw [finiteUpperUniformDeviation, ← hmaximizer]
  calc
    finitePopulationMean law value maximizer -
        finiteEmpiricalMean n value sample maximizer =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun ghost =>
          finiteEmpiricalMean n value ghost maximizer -
            finiteEmpiricalMean n value sample maximizer) := by
          rw [AppliedModelingLib.pmfExp_sub,
            pmfExp_finiteEmpiricalMean_eq_finitePopulationMean law n hn,
            AppliedModelingLib.pmfExp_const]
    _ ≤ AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun ghost => ⨆ hypothesis,
          finiteEmpiricalMean n value ghost hypothesis -
            finiteEmpiricalMean n value sample hypothesis) := by
      apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
      intro ghost
      exact le_ciSup
        (Finite.bddAbove_range fun hypothesis =>
          finiteEmpiricalMean n value ghost hypothesis -
            finiteEmpiricalMean n value sample hypothesis)
        maximizer

/-- Normalized supremum of coordinatewise differences in a paired sample. -/
noncomputable def finitePairedUniformDifference
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (pairedSample : Fin n → Outcome × Outcome) : ℝ :=
  ⨆ hypothesis,
    (n : ℝ)⁻¹ * ∑ index : Fin n,
      (value hypothesis (pairedSample index).1 -
        value hypothesis (pairedSample index).2)

/-- A difference of empirical means is the mean of paired differences. -/
theorem finiteEmpiricalMean_sub_eq_pairedDifference
    {Outcome : Type*} (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (first second : Fin n → Outcome) (hypothesis : Hypothesis) :
    finiteEmpiricalMean n value first hypothesis -
        finiteEmpiricalMean n value second hypothesis =
      (n : ℝ)⁻¹ * ∑ index : Fin n,
        (value hypothesis (first index) - value hypothesis (second index)) := by
  unfold finiteEmpiricalMean
  rw [Finset.sum_sub_distrib]
  ring

/--
After averaging the fixed-sample ghost inequality, two iid samples can be
represented as one iid sample of coordinate pairs.
-/
theorem pmfExp_finiteUpperUniformDeviation_le_pairedDifference
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteUpperUniformDeviation law n value) ≤
      AppliedModelingLib.pmfExp
        (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
          (AppliedModelingLib.pmfProd law law))
        (finitePairedUniformDifference n value) := by
  let sampleLaw := AppliedModelingLib.pmfProduct (Fin n) Outcome law
  have hghost :
      AppliedModelingLib.pmfExp sampleLaw
          (finiteUpperUniformDeviation law n value) ≤
        AppliedModelingLib.pmfPairExp sampleLaw sampleLaw
          (fun sample ghost => ⨆ hypothesis,
            finiteEmpiricalMean n value ghost hypothesis -
              finiteEmpiricalMean n value sample hypothesis) := by
    unfold AppliedModelingLib.pmfPairExp
    apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
    intro sample
    exact finiteUpperUniformDeviation_le_ghostSample
      law n hn value sample
  calc
    AppliedModelingLib.pmfExp sampleLaw
        (finiteUpperUniformDeviation law n value) ≤
      AppliedModelingLib.pmfPairExp sampleLaw sampleLaw
        (fun sample ghost => ⨆ hypothesis,
          finiteEmpiricalMean n value ghost hypothesis -
            finiteEmpiricalMean n value sample hypothesis) := hghost
    _ = AppliedModelingLib.pmfPairExp sampleLaw sampleLaw
        (fun ghost sample => ⨆ hypothesis,
          finiteEmpiricalMean n value ghost hypothesis -
            finiteEmpiricalMean n value sample hypothesis) := by
      exact AppliedModelingLib.pmfPairExp_swap sampleLaw sampleLaw _
    _ = AppliedModelingLib.pmfExp
        (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
          (AppliedModelingLib.pmfProd law law))
        (finitePairedUniformDifference n value) := by
      rw [← AppliedModelingLib.pmfExp_pmfProduct_pmfProd_eq_pairExp]
      apply AppliedModelingLib.pmfExp_congr
      intro pairedSample
      unfold finitePairedUniformDifference
      apply congrArg
      funext hypothesis
      exact finiteEmpiricalMean_sub_eq_pairedDifference n value
        (fun index => (pairedSample index).1)
        (fun index => (pairedSample index).2) hypothesis

/-- Signed normalized supremum of coordinatewise paired differences. -/
noncomputable def finiteSignedPairedUniformDifference
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin n → Bool) (pairedSample : Fin n → Outcome × Outcome) : ℝ :=
  ⨆ hypothesis,
    (n : ℝ)⁻¹ * ∑ index : Fin n,
      rademacherSign (signs index) *
        (value hypothesis (pairedSample index).1 -
          value hypothesis (pairedSample index).2)

/-- Sign-selected pair swapping turns the unsigned difference into a signed one. -/
theorem finitePairedUniformDifference_swapPairsBySigns
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin n → Bool) (pairedSample : Fin n → Outcome × Outcome) :
    finitePairedUniformDifference n value
        (swapPairsBySigns signs pairedSample) =
      finiteSignedPairedUniformDifference n value signs pairedSample := by
  unfold finitePairedUniformDifference finiteSignedPairedUniformDifference
  apply congrArg
  funext hypothesis
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  exact pairDifference_swapPairsBySigns signs pairedSample index
    (value hypothesis)

/--
For every fixed sign vector, iid equal-law pairs make the signed and unsigned
paired suprema equidistributed.
-/
theorem pmfExp_finiteSignedPairedUniformDifference_eq_unsigned
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin n → Bool) :
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
          (AppliedModelingLib.pmfProd law law))
        (finiteSignedPairedUniformDifference n value signs) =
      AppliedModelingLib.pmfExp
        (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
          (AppliedModelingLib.pmfProd law law))
        (finitePairedUniformDifference n value) := by
  let pairedLaw :=
    AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
      (AppliedModelingLib.pmfProd law law)
  calc
    AppliedModelingLib.pmfExp pairedLaw
        (finiteSignedPairedUniformDifference n value signs) =
      AppliedModelingLib.pmfExp pairedLaw
        (fun pairedSample => finitePairedUniformDifference n value
          (swapPairsBySigns signs pairedSample)) := by
            apply AppliedModelingLib.pmfExp_congr
            intro pairedSample
            exact (finitePairedUniformDifference_swapPairsBySigns
              n value signs pairedSample).symm
    _ = AppliedModelingLib.pmfExp pairedLaw
        (finitePairedUniformDifference n value) := by
      exact pmfExp_comp_equiv_eq_of_apply_eq pairedLaw
        (swapPairsBySigns signs)
        (pmfProduct_pmfProd_apply_swapPairsBySigns law signs)
        (finitePairedUniformDifference n value)

/-- The paired-difference expectation equals its uniform-sign average. -/
theorem pmfExp_finitePairedUniformDifference_eq_signAverage
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ) :
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
          (AppliedModelingLib.pmfProd law law))
        (finitePairedUniformDifference n value) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs =>
          AppliedModelingLib.pmfExp
            (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
              (AppliedModelingLib.pmfProd law law))
            (finiteSignedPairedUniformDifference n value signs)) := by
  let pairedLaw :=
    AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
      (AppliedModelingLib.pmfProd law law)
  calc
    AppliedModelingLib.pmfExp pairedLaw (finitePairedUniformDifference n value) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun _signs =>
          AppliedModelingLib.pmfExp pairedLaw
            (finitePairedUniformDifference n value)) := by
          rw [AppliedModelingLib.pmfExp_const]
    _ = AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs =>
          AppliedModelingLib.pmfExp pairedLaw
            (finiteSignedPairedUniformDifference n value signs)) := by
      apply AppliedModelingLib.pmfExp_congr
      intro signs
      exact (pmfExp_finiteSignedPairedUniformDifference_eq_unsigned
        law n value signs).symm

/-- Normalized signed empirical supremum for a fixed sample and sign vector. -/
noncomputable def finiteSignedEmpiricalSup
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin n → Bool) (sample : Fin n → Outcome) : ℝ :=
  ⨆ hypothesis,
    (n : ℝ)⁻¹ * ∑ index : Fin n,
      rademacherSign (signs index) * value hypothesis (sample index)

/-- Averaging the fixed-sample signed supremum is empirical Rademacher complexity. -/
theorem pmfExp_finiteSignedEmpiricalSup_eq_empiricalOneSidedRademacher
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n value signs sample) =
      empiricalOneSidedRademacher n
        (fun hypothesis index => value hypothesis (sample index)) := by
  have hnormalized : ∀ signs : Fin n → Bool,
      finiteSignedEmpiricalSup n value signs sample =
        (n : ℝ)⁻¹ * (⨆ hypothesis,
          ∑ index : Fin n,
            rademacherSign (signs index) * value hypothesis (sample index)) := by
    intro signs
    unfold finiteSignedEmpiricalSup
    exact iSup_const_mul_eq_const_iSup _ (by positivity)
  rw [AppliedModelingLib.pmfExp_congr
    (AppliedModelingLib.uniformPMF (Fin n → Bool)) hnormalized]
  rw [AppliedModelingLib.pmfExp_const_mul]
  rfl

/-- Flipping all uniform signs leaves the empirical signed-supremum mean unchanged. -/
theorem pmfExp_finiteSignedEmpiricalSup_negate_eq_empiricalOneSidedRademacher
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n value
          (negateBooleanSigns (Fin n) signs) sample) =
      empiricalOneSidedRademacher n
        (fun hypothesis index => value hypothesis (sample index)) := by
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n value
          (negateBooleanSigns (Fin n) signs) sample) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n value signs sample) := by
          exact pmfExp_uniformPMF_negateBooleanSigns (Fin n)
            (fun signs => finiteSignedEmpiricalSup n value signs sample)
    _ = empiricalOneSidedRademacher n
        (fun hypothesis index => value hypothesis (sample index)) :=
      pmfExp_finiteSignedEmpiricalSup_eq_empiricalOneSidedRademacher
        n value sample

/-- A signed paired supremum splits into two fixed-sample signed suprema. -/
theorem finiteSignedPairedUniformDifference_le_add_empiricalSup
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin n → Bool) (pairedSample : Fin n → Outcome × Outcome) :
    finiteSignedPairedUniformDifference n value signs pairedSample ≤
      finiteSignedEmpiricalSup n value signs
          (fun index => (pairedSample index).1) +
        finiteSignedEmpiricalSup n value
          (negateBooleanSigns (Fin n) signs)
          (fun index => (pairedSample index).2) := by
  unfold finiteSignedPairedUniformDifference finiteSignedEmpiricalSup
  let left : Hypothesis → ℝ := fun hypothesis =>
    (n : ℝ)⁻¹ * ∑ index : Fin n,
      rademacherSign (signs index) *
        value hypothesis (pairedSample index).1
  let right : Hypothesis → ℝ := fun hypothesis =>
    (n : ℝ)⁻¹ * ∑ index : Fin n,
      rademacherSign ((negateBooleanSigns (Fin n) signs) index) *
        value hypothesis (pairedSample index).2
  have hsplit : ∀ hypothesis,
      (n : ℝ)⁻¹ * ∑ index : Fin n,
          rademacherSign (signs index) *
            (value hypothesis (pairedSample index).1 -
              value hypothesis (pairedSample index).2) =
        left hypothesis + right hypothesis := by
    intro hypothesis
    simp only [left, right, negateBooleanSigns_apply, rademacherSign_not]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    simp_rw [neg_mul, Finset.sum_neg_distrib]
    ring
  rw [show (fun hypothesis =>
      (n : ℝ)⁻¹ * ∑ index : Fin n,
        rademacherSign (signs index) *
          (value hypothesis (pairedSample index).1 -
            value hypothesis (pairedSample index).2)) =
      fun hypothesis => left hypothesis + right hypothesis by
        funext hypothesis
        exact hsplit hypothesis]
  exact iSup_add_le_add_iSup_finite left right

/-- Expected one-sided empirical Rademacher complexity under an iid finite sample. -/
noncomputable def finiteExpectedOneSidedRademacher
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ) : ℝ :=
  AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
    (fun sample => empiricalOneSidedRademacher n
      (fun hypothesis index => value hypothesis (sample index)))

/-- Expected one-sided empirical Rademacher complexity for an arbitrary class
under a finite iid law.  The inner fixed-sample supremum is real-valued rather
than a finite maximum, so subsequent uses provide the boundedness implied by
their primitive range assumptions. -/
noncomputable def finiteExpectedOneSidedRademacherSet
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ) : ℝ :=
  AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
    (fun sample => empiricalOneSidedRademacherSet n
      (fun hypothesis index => value hypothesis (sample index)))

/-- Finite classes embed in the arbitrary-class expected Rademacher
complexity with no change to the sampling law. -/
theorem finiteExpectedOneSidedRademacher_le_set
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ) :
    finiteExpectedOneSidedRademacher law n value ≤
      finiteExpectedOneSidedRademacherSet law n value := by
  unfold finiteExpectedOneSidedRademacher finiteExpectedOneSidedRademacherSet
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro sample
  exact empiricalOneSidedRademacher_le_empiricalOneSidedRademacherSet n
    (fun hypothesis index => value hypothesis (sample index))

/-- Expected arbitrary-class Rademacher complexity inherits scalar Lipschitz
contraction from its fixed-sample counterpart. -/
theorem finiteExpectedOneSidedRademacherSet_contraction
    {Outcome Hypothesis : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (psi : Outcome → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hpsi : ∀ outcome first second,
      |psi outcome first - psi outcome second| ≤ L * |first - second|)
    (hvalueBdd : ∀ (sample : Fin n → Outcome) (signs : Fin n → Bool),
      BddAbove (Set.range fun hypothesis =>
        ∑ index : Fin n, rademacherSign (signs index) * value hypothesis (sample index)))
    (htransformedBdd : ∀ (sample : Fin n → Outcome) (signs : Fin n → Bool),
      BddAbove (Set.range fun hypothesis =>
        ∑ index : Fin n, rademacherSign (signs index) *
          psi (sample index) (value hypothesis (sample index)))) :
    finiteExpectedOneSidedRademacherSet law n
        (fun hypothesis outcome => psi outcome (value hypothesis outcome)) ≤
      L * finiteExpectedOneSidedRademacherSet law n value := by
  unfold finiteExpectedOneSidedRademacherSet
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacherSet n
          (fun hypothesis index => psi (sample index) (value hypothesis (sample index)))) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => L * empiricalOneSidedRademacherSet n
          (fun hypothesis index => value hypothesis (sample index))) := by
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro sample
            exact empiricalOneSidedRademacherSet_contraction n
              (fun hypothesis index => value hypothesis (sample index))
              (fun index input => psi (sample index) input) hL
              (fun index first second => hpsi (sample index) first second)
              (hvalueBdd sample) (htransformedBdd sample)
    _ = L * AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
          (fun sample => empiricalOneSidedRademacherSet n
            (fun hypothesis index => value hypothesis (sample index))) :=
      AppliedModelingLib.pmfExp_const_mul _ _ _

/-- Expected one-sided complexity of an arbitrary bounded product class is at
most twice the sum of its factor complexities.  This is the iid lift of the
fixed-sample arbitrary-class product inequality. -/
theorem finiteExpectedOneSidedRademacherSet_mul_le_two_add
    {Outcome Left Right : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Left] [Nonempty Right]
    (law : PMF Outcome) (n : ℕ) (left : Left → Outcome → ℝ)
    (right : Right → Outcome → ℝ)
    (hleft : ∀ hypothesis outcome, |left hypothesis outcome| ≤ 1)
    (hright : ∀ hypothesis outcome, |right hypothesis outcome| ≤ 1) :
    finiteExpectedOneSidedRademacherSet law n
        (fun pair : Left × Right => fun outcome => left pair.1 outcome * right pair.2 outcome) ≤
      2 * (finiteExpectedOneSidedRademacherSet law n left +
        finiteExpectedOneSidedRademacherSet law n right) := by
  unfold finiteExpectedOneSidedRademacherSet
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacherSet n
          (fun pair : Left × Right => fun index =>
            left pair.1 (sample index) * right pair.2 (sample index))) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => 2 *
          (empiricalOneSidedRademacherSet n (fun hypothesis index => left hypothesis (sample index)) +
            empiricalOneSidedRademacherSet n
              (fun hypothesis index => right hypothesis (sample index)))) := by
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro sample
            exact empiricalOneSidedRademacherSet_mul_le_two_add n
              (fun hypothesis index => left hypothesis (sample index))
              (fun hypothesis index => right hypothesis (sample index))
              (fun hypothesis index => hleft hypothesis (sample index))
              (fun hypothesis index => hright hypothesis (sample index))
    _ = 2 * (finiteExpectedOneSidedRademacherSet law n left +
        finiteExpectedOneSidedRademacherSet law n right) := by
      rw [AppliedModelingLib.pmfExp_const_mul, AppliedModelingLib.pmfExp_add]
      rfl

/-- A samplewise exact convex representation transfers expected empirical
complexity to a finite basis.  The coefficients may depend on the iid sample,
which is essential when monotone postprocessings are expanded at the realized
score cutpoints. -/
theorem finiteExpectedOneSidedRademacher_le_of_samplewise_finite_convex_representation
    {Outcome Target Basis : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Target] [Nonempty Target] [Fintype Basis] [Nonempty Basis]
    (law : PMF Outcome) (n : ℕ) (targetValue : Target → Outcome → ℝ)
    (basisValue : Basis → Outcome → ℝ)
    (hrepr : ∀ (sample : Fin n → Outcome) target,
      ∃ (terms : ℕ) (coefficient : Fin terms → ℝ) (basis : Fin terms → Basis),
        (∀ term, 0 ≤ coefficient term) ∧
        (∑ term, coefficient term) = 1 ∧
        ∀ index, targetValue target (sample index) =
          ∑ term, coefficient term * basisValue (basis term) (sample index)) :
    finiteExpectedOneSidedRademacher law n targetValue ≤
      finiteExpectedOneSidedRademacher law n basisValue := by
  unfold finiteExpectedOneSidedRademacher
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro sample
  exact empiricalOneSidedRademacher_le_of_finite_convex_representation n
    (fun target index => targetValue target (sample index))
    (fun basis index => basisValue basis (sample index)) (hrepr sample)

/-- Expected empirical complexity inherits one-sided Lipschitz contraction. -/
theorem finiteExpectedOneSidedRademacher_contraction
    {Outcome Hypothesis : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (psi : Outcome → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hpsi : ∀ outcome u v,
      |psi outcome u - psi outcome v| ≤ L * |u - v|) :
    finiteExpectedOneSidedRademacher law n
        (fun hypothesis outcome => psi outcome (value hypothesis outcome)) ≤
      L * finiteExpectedOneSidedRademacher law n value := by
  unfold finiteExpectedOneSidedRademacher
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacher n
          (fun hypothesis index =>
            psi (sample index) (value hypothesis (sample index)))) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => L * empiricalOneSidedRademacher n
          (fun hypothesis index => value hypothesis (sample index))) := by
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro sample
            exact empiricalOneSidedRademacher_contraction n
              (fun hypothesis index => value hypothesis (sample index))
              (fun index => psi (sample index)) hL
              (fun index u v => hpsi (sample index) u v)
    _ = L * AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacher n
          (fun hypothesis index => value hypothesis (sample index))) :=
      AppliedModelingLib.pmfExp_const_mul _ _ _

/-- Expected empirical complexity is subadditive for product-indexed sum classes. -/
theorem finiteExpectedOneSidedRademacher_prod_add_le
    {Outcome Left Right : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Left] [Nonempty Left] [Fintype Right] [Nonempty Right]
    (law : PMF Outcome) (n : ℕ) (left : Left → Outcome → ℝ)
    (right : Right → Outcome → ℝ) :
    finiteExpectedOneSidedRademacher law n
        (fun pair : Left × Right => fun outcome =>
          left pair.1 outcome + right pair.2 outcome) ≤
      finiteExpectedOneSidedRademacher law n left +
        finiteExpectedOneSidedRademacher law n right := by
  unfold finiteExpectedOneSidedRademacher
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacher n
          (fun pair : Left × Right => fun index =>
            left pair.1 (sample index) + right pair.2 (sample index))) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample =>
          empiricalOneSidedRademacher n
              (fun hypothesis index => left hypothesis (sample index)) +
            empiricalOneSidedRademacher n
              (fun hypothesis index => right hypothesis (sample index))) := by
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro sample
            exact empiricalOneSidedRademacher_prod_add_le n
              (fun hypothesis index => left hypothesis (sample index))
              (fun hypothesis index => right hypothesis (sample index))
    _ = AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
          (fun sample => empiricalOneSidedRademacher n
            (fun hypothesis index => left hypothesis (sample index))) +
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
          (fun sample => empiricalOneSidedRademacher n
            (fun hypothesis index => right hypothesis (sample index))) :=
      AppliedModelingLib.pmfExp_add _ _ _

/-- Expected one-sided empirical complexity of a product class is at most twice
the sum of the complexities of two `[-1,1]`-valued finite factors.  This lifts
`empiricalOneSidedRademacher_mul_le_two_add` pointwise over the iid sample
law. -/
theorem finiteExpectedOneSidedRademacher_mul_le_two_add
    {Outcome Left Right : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Left] [Nonempty Left] [Fintype Right] [Nonempty Right]
    (law : PMF Outcome) (n : ℕ) (left : Left → Outcome → ℝ)
    (right : Right → Outcome → ℝ)
    (hleft : ∀ hypothesis outcome, |left hypothesis outcome| ≤ 1)
    (hright : ∀ hypothesis outcome, |right hypothesis outcome| ≤ 1) :
    finiteExpectedOneSidedRademacher law n
        (fun pair : Left × Right => fun outcome => left pair.1 outcome * right pair.2 outcome) ≤
      2 * (finiteExpectedOneSidedRademacher law n left +
        finiteExpectedOneSidedRademacher law n right) := by
  unfold finiteExpectedOneSidedRademacher
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacher n
          (fun pair : Left × Right => fun index =>
            left pair.1 (sample index) * right pair.2 (sample index))) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => 2 *
          (empiricalOneSidedRademacher n (fun hypothesis index => left hypothesis (sample index)) +
            empiricalOneSidedRademacher n
              (fun hypothesis index => right hypothesis (sample index)))) := by
          apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
          intro sample
          exact empiricalOneSidedRademacher_mul_le_two_add n
            (fun hypothesis index => left hypothesis (sample index))
            (fun hypothesis index => right hypothesis (sample index))
            (fun hypothesis index => hleft hypothesis (sample index))
            (fun hypothesis index => hright hypothesis (sample index))
    _ = 2 * (finiteExpectedOneSidedRademacher law n left +
        finiteExpectedOneSidedRademacher law n right) := by
      rw [AppliedModelingLib.pmfExp_const_mul, AppliedModelingLib.pmfExp_add]
      rfl

/-- The sign-averaged paired supremum is at most twice expected complexity. -/
theorem pmfExp_finitePairedUniformDifference_le_two_expectedRademacher
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ) :
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
          (AppliedModelingLib.pmfProd law law))
        (finitePairedUniformDifference n value) ≤
      2 * finiteExpectedOneSidedRademacher law n value := by
  let signsLaw := AppliedModelingLib.uniformPMF (Fin n → Bool)
  let pairedLaw :=
    AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
      (AppliedModelingLib.pmfProd law law)
  let sampleLaw := AppliedModelingLib.pmfProduct (Fin n) Outcome law
  have hfixed : ∀ pairedSample : Fin n → Outcome × Outcome,
      AppliedModelingLib.pmfExp signsLaw
          (fun signs => finiteSignedPairedUniformDifference
            n value signs pairedSample) ≤
        empiricalOneSidedRademacher n
            (fun hypothesis index => value hypothesis (pairedSample index).1) +
          empiricalOneSidedRademacher n
            (fun hypothesis index => value hypothesis (pairedSample index).2) := by
    intro pairedSample
    calc
      AppliedModelingLib.pmfExp signsLaw
          (fun signs => finiteSignedPairedUniformDifference
            n value signs pairedSample) ≤
        AppliedModelingLib.pmfExp signsLaw
          (fun signs =>
            finiteSignedEmpiricalSup n value signs
                (fun index => (pairedSample index).1) +
              finiteSignedEmpiricalSup n value
                (negateBooleanSigns (Fin n) signs)
                (fun index => (pairedSample index).2)) := by
          apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
          intro signs
          exact finiteSignedPairedUniformDifference_le_add_empiricalSup
            n value signs pairedSample
      _ = empiricalOneSidedRademacher n
            (fun hypothesis index => value hypothesis (pairedSample index).1) +
          empiricalOneSidedRademacher n
            (fun hypothesis index => value hypothesis (pairedSample index).2) := by
        rw [AppliedModelingLib.pmfExp_add,
          pmfExp_finiteSignedEmpiricalSup_eq_empiricalOneSidedRademacher,
          pmfExp_finiteSignedEmpiricalSup_negate_eq_empiricalOneSidedRademacher]
  rw [pmfExp_finitePairedUniformDifference_eq_signAverage]
  calc
    AppliedModelingLib.pmfExp signsLaw
        (fun signs => AppliedModelingLib.pmfExp pairedLaw
          (finiteSignedPairedUniformDifference n value signs)) =
      AppliedModelingLib.pmfExp pairedLaw
        (fun pairedSample => AppliedModelingLib.pmfExp signsLaw
          (fun signs => finiteSignedPairedUniformDifference
            n value signs pairedSample)) := by
        exact AppliedModelingLib.pmfPairExp_swap signsLaw pairedLaw _
    _ ≤ AppliedModelingLib.pmfExp pairedLaw
        (fun pairedSample =>
          empiricalOneSidedRademacher n
              (fun hypothesis index => value hypothesis (pairedSample index).1) +
            empiricalOneSidedRademacher n
              (fun hypothesis index => value hypothesis (pairedSample index).2)) := by
        exact AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le pairedLaw _ _ hfixed
    _ = finiteExpectedOneSidedRademacher law n value +
        finiteExpectedOneSidedRademacher law n value := by
      rw [AppliedModelingLib.pmfExp_add]
      unfold finiteExpectedOneSidedRademacher
      apply congrArg₂ (fun first second : ℝ => first + second)
      · dsimp only [pairedLaw, sampleLaw]
        let complexity : (Fin n → Outcome) → ℝ := fun sample =>
          empiricalOneSidedRademacher n
            (fun hypothesis index => value hypothesis (sample index))
        change AppliedModelingLib.pmfExp
            (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
              (AppliedModelingLib.pmfProd law law))
            (fun pairedSample => complexity
              (fun index => (pairedSample index).1)) =
          AppliedModelingLib.pmfExp
            (AppliedModelingLib.pmfProduct (Fin n) Outcome law) complexity
        calc
          _ = AppliedModelingLib.pmfPairExp
              (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (fun first _second => complexity first) := by
                exact AppliedModelingLib.pmfExp_pmfProduct_pmfProd_eq_pairExp
                  law law (fun first _second => complexity first)
          _ = _ := AppliedModelingLib.pmfPairExp_ignore_right _ _ complexity
      · dsimp only [pairedLaw, sampleLaw]
        let complexity : (Fin n → Outcome) → ℝ := fun sample =>
          empiricalOneSidedRademacher n
            (fun hypothesis index => value hypothesis (sample index))
        change AppliedModelingLib.pmfExp
            (AppliedModelingLib.pmfProduct (Fin n) (Outcome × Outcome)
              (AppliedModelingLib.pmfProd law law))
            (fun pairedSample => complexity
              (fun index => (pairedSample index).2)) =
          AppliedModelingLib.pmfExp
            (AppliedModelingLib.pmfProduct (Fin n) Outcome law) complexity
        calc
          _ = AppliedModelingLib.pmfPairExp
              (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (fun _first second => complexity second) := by
                exact AppliedModelingLib.pmfExp_pmfProduct_pmfProd_eq_pairExp
                  law law (fun _first second => complexity second)
          _ = _ := AppliedModelingLib.pmfPairExp_ignore_left _ _ complexity
    _ = 2 * finiteExpectedOneSidedRademacher law n value := by ring

/-- Expected one-sided population-minus-empirical deviation symmetrization. -/
theorem pmfExp_finiteUpperUniformDeviation_le_two_expectedRademacher
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteUpperUniformDeviation law n value) ≤
      2 * finiteExpectedOneSidedRademacher law n value :=
  (pmfExp_finiteUpperUniformDeviation_le_pairedDifference law n hn value).trans
    (pmfExp_finitePairedUniformDifference_le_two_expectedRademacher law n value)

/-- Negate every member of a real-valued function class. -/
def negateFunctionClass
    {Outcome : Type*} (value : Hypothesis → Outcome → ℝ) :
    Hypothesis → Outcome → ℝ :=
  fun hypothesis outcome => -value hypothesis outcome

/-- Negating a class and every sign has no effect on its signed supremum. -/
theorem finiteSignedEmpiricalSup_negateFunctionClass
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin n → Bool) (sample : Fin n → Outcome) :
    finiteSignedEmpiricalSup n (negateFunctionClass value) signs sample =
      finiteSignedEmpiricalSup n value
        (negateBooleanSigns (Fin n) signs) sample := by
  unfold finiteSignedEmpiricalSup negateFunctionClass
  apply congrArg
  funext hypothesis
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  simp only [negateBooleanSigns_apply, rademacherSign_not]
  ring

/-- Empirical one-sided Rademacher complexity is invariant under class negation. -/
theorem empiricalOneSidedRademacher_negateFunctionClass
    {Outcome : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) :
    empiricalOneSidedRademacher n
        (fun hypothesis index => negateFunctionClass value hypothesis (sample index)) =
      empiricalOneSidedRademacher n
        (fun hypothesis index => value hypothesis (sample index)) := by
  rw [← pmfExp_finiteSignedEmpiricalSup_eq_empiricalOneSidedRademacher
      n (negateFunctionClass value) sample,
    ← pmfExp_finiteSignedEmpiricalSup_eq_empiricalOneSidedRademacher
      n value sample]
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n
          (negateFunctionClass value) signs sample) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n value
          (negateBooleanSigns (Fin n) signs) sample) := by
            apply AppliedModelingLib.pmfExp_congr
            exact fun signs =>
              finiteSignedEmpiricalSup_negateFunctionClass
                n value signs sample
    _ = AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => finiteSignedEmpiricalSup n value signs sample) := by
          exact pmfExp_uniformPMF_negateBooleanSigns (Fin n)
            (fun signs => finiteSignedEmpiricalSup n value signs sample)

/-- Expected one-sided complexity is invariant under class negation. -/
theorem finiteExpectedOneSidedRademacher_negateFunctionClass
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ) :
    finiteExpectedOneSidedRademacher law n (negateFunctionClass value) =
      finiteExpectedOneSidedRademacher law n value := by
  unfold finiteExpectedOneSidedRademacher
  apply AppliedModelingLib.pmfExp_congr
  intro sample
  exact empiricalOneSidedRademacher_negateFunctionClass n value sample

/-- Lower deviation of a class is upper deviation of the negated class. -/
theorem finiteLowerUniformDeviation_eq_upper_negateFunctionClass
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) :
    finiteLowerUniformDeviation law n value sample =
      finiteUpperUniformDeviation law n (negateFunctionClass value) sample := by
  unfold finiteLowerUniformDeviation finiteUpperUniformDeviation
  apply congrArg
  funext hypothesis
  unfold finitePopulationMean finiteEmpiricalMean negateFunctionClass
  rw [AppliedModelingLib.pmfExp_neg, Finset.sum_neg_distrib]
  ring

/-- Expected empirical-minus-population deviation symmetrization. -/
theorem pmfExp_finiteLowerUniformDeviation_le_two_expectedRademacher
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteLowerUniformDeviation law n value) ≤
      2 * finiteExpectedOneSidedRademacher law n value := by
  rw [AppliedModelingLib.pmfExp_congr
    (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
    (finiteLowerUniformDeviation_eq_upper_negateFunctionClass
      law n value)]
  rw [← finiteExpectedOneSidedRademacher_negateFunctionClass law n value]
  exact pmfExp_finiteUpperUniformDeviation_le_two_expectedRademacher
    law n hn (negateFunctionClass value)

/-- Expected uniform deviation of an arbitrary bounded class under a finite
iid law is at most twice its expected one-sided Rademacher complexity.  The
proof selects an `ε`-maximizer separately for each of the finitely many
possible samples, applies finite-class symmetrization to that selected class,
and then lets `ε` decrease to zero. -/
theorem pmfExp_finiteUpperUniformDeviationSet_le_two_expectedRademacherSet
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteUpperUniformDeviationSet law n value) ≤
      2 * finiteExpectedOneSidedRademacherSet law n value := by
  classical
  letI : Nonempty Outcome := ⟨Classical.choose law.support_nonempty⟩
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hnear : ∀ sample : Fin n → Outcome, ∃ hypothesis,
      finiteUpperUniformDeviationSet law n value sample - epsilon <
        finitePopulationMean law value hypothesis -
          finiteEmpiricalMean n value sample hypothesis := by
    intro sample
    unfold finiteUpperUniformDeviationSet
    obtain ⟨score, ⟨hypothesis, rfl⟩, hscore⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty fun hypothesis =>
        finitePopulationMean law value hypothesis -
          finiteEmpiricalMean n value sample hypothesis)
        (sub_lt_self _ hepsilon)
    exact ⟨hypothesis, hscore⟩
  let selected : (Fin n → Outcome) → Hypothesis :=
    fun sample => Classical.choose (hnear sample)
  have hselected : ∀ sample : Fin n → Outcome,
      finiteUpperUniformDeviationSet law n value sample - epsilon <
        finitePopulationMean law value (selected sample) -
          finiteEmpiricalMean n value sample (selected sample) := by
    intro sample
    exact Classical.choose_spec (hnear sample)
  let selectedValue : (Fin n → Outcome) → Outcome → ℝ :=
    fun chosen => value (selected chosen)
  have hpoint : ∀ sample : Fin n → Outcome,
      finiteUpperUniformDeviationSet law n value sample ≤
        finiteUpperUniformDeviation law n selectedValue sample + epsilon := by
    intro sample
    have hselectedLe :
        finitePopulationMean law value (selected sample) -
            finiteEmpiricalMean n value sample (selected sample) ≤
          finiteUpperUniformDeviation law n selectedValue sample := by
      change finitePopulationMean law selectedValue sample -
          finiteEmpiricalMean n selectedValue sample sample ≤ _
      exact le_ciSup (Finite.bddAbove_range fun chosen : Fin n → Outcome =>
        finitePopulationMean law selectedValue chosen -
          finiteEmpiricalMean n selectedValue sample chosen) sample
    linarith [hselected sample]
  have hselectedComplexity :
      finiteExpectedOneSidedRademacher law n selectedValue ≤
        finiteExpectedOneSidedRademacherSet law n value := by
    unfold finiteExpectedOneSidedRademacher finiteExpectedOneSidedRademacherSet
    apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
    intro sample
    calc
      empiricalOneSidedRademacher n
          (fun chosen index => selectedValue chosen (sample index)) ≤
        empiricalOneSidedRademacherSet n
          (fun chosen index => selectedValue chosen (sample index)) :=
            empiricalOneSidedRademacher_le_empiricalOneSidedRademacherSet n _
      _ ≤ empiricalOneSidedRademacherSet n
          (fun hypothesis index => value hypothesis (sample index)) := by
            apply empiricalOneSidedRademacherSet_le_of_map n
              (fun chosen index => selectedValue chosen (sample index))
              (fun hypothesis index => value hypothesis (sample index)) selected
            · intro chosen index
              rfl
            · intro signs
              exact bddAbove_range_rademacherScore_of_abs_le_one n
                (fun hypothesis index => value hypothesis (sample index))
                (fun hypothesis index => hbounded hypothesis (sample index)) signs
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteUpperUniformDeviationSet law n value) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => finiteUpperUniformDeviation law n selectedValue sample + epsilon) := by
          apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
          intro sample
          exact hpoint sample
    _ = AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
          (finiteUpperUniformDeviation law n selectedValue) + epsilon := by
            rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const]
    _ ≤ 2 * finiteExpectedOneSidedRademacher law n selectedValue + epsilon := by
          exact add_le_add
            (pmfExp_finiteUpperUniformDeviation_le_two_expectedRademacher
              law n hn selectedValue) le_rfl
    _ ≤ 2 * finiteExpectedOneSidedRademacherSet law n value + epsilon := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hselectedComplexity (by norm_num)) le_rfl

/-- Lower deviation of an arbitrary class is upper deviation of its negated
class. -/
theorem finiteLowerUniformDeviationSet_eq_upper_negateFunctionClass
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (sample : Fin n → Outcome) :
    finiteLowerUniformDeviationSet law n value sample =
      finiteUpperUniformDeviationSet law n (negateFunctionClass value) sample := by
  unfold finiteLowerUniformDeviationSet finiteUpperUniformDeviationSet
  apply congrArg sSup
  ext score
  constructor <;> rintro ⟨hypothesis, rfl⟩ <;> refine ⟨hypothesis, ?_⟩ <;>
    unfold finitePopulationMean finiteEmpiricalMean negateFunctionClass <;> dsimp <;>
    rw [AppliedModelingLib.pmfExp_neg, Finset.sum_neg_distrib] <;> ring

/-- Negating an arbitrary bounded class cannot increase its one-sided
Rademacher complexity. -/
theorem empiricalOneSidedRademacherSet_negateFunctionClass_le
    {Class : Type*} [Nonempty Class]
    (n : ℕ) (value : Class → Fin n → ℝ)
    (hbounded : ∀ hypothesis index, |value hypothesis index| ≤ 1) :
    empiricalOneSidedRademacherSet n (fun hypothesis index => -value hypothesis index) ≤
      empiricalOneSidedRademacherSet n value := by
  simpa only [one_mul] using empiricalOneSidedRademacherSet_contraction n value
    (fun _ input => -input) (L := 1) (by norm_num)
    (fun _ first second => by
      rw [show -first - -second = -(first - second) by ring, abs_neg]
      norm_num)
    (fun signs => bddAbove_range_rademacherScore_of_abs_le_one n value hbounded signs)
    (fun signs => by
      simpa only using bddAbove_range_rademacherScore_of_abs_le_one n
        (fun hypothesis index => -value hypothesis index)
        (fun hypothesis index => by simpa using hbounded hypothesis index) signs)

/-- Expected one-sided Rademacher complexity of a negated arbitrary bounded
class is no larger than that of the original class. -/
theorem finiteExpectedOneSidedRademacherSet_negateFunctionClass_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1) :
    finiteExpectedOneSidedRademacherSet law n (negateFunctionClass value) ≤
      finiteExpectedOneSidedRademacherSet law n value := by
  unfold finiteExpectedOneSidedRademacherSet negateFunctionClass
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro sample
  exact empiricalOneSidedRademacherSet_negateFunctionClass_le n
    (fun hypothesis index => value hypothesis (sample index))
    (fun hypothesis index => hbounded hypothesis (sample index))

/-- Expected empirical-minus-population deviation of an arbitrary bounded
class obeys the same one-sided Rademacher bound. -/
theorem pmfExp_finiteLowerUniformDeviationSet_le_two_expectedRademacherSet
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteLowerUniformDeviationSet law n value) ≤
      2 * finiteExpectedOneSidedRademacherSet law n value := by
  rw [AppliedModelingLib.pmfExp_congr
    (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
    (finiteLowerUniformDeviationSet_eq_upper_negateFunctionClass law n value)]
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (finiteUpperUniformDeviationSet law n (negateFunctionClass value)) ≤
      2 * finiteExpectedOneSidedRademacherSet law n (negateFunctionClass value) :=
        pmfExp_finiteUpperUniformDeviationSet_le_two_expectedRademacherSet
          law n hn (negateFunctionClass value)
          (fun hypothesis outcome => by simpa [negateFunctionClass] using hbounded hypothesis outcome)
    _ ≤ 2 * finiteExpectedOneSidedRademacherSet law n value := by
      exact mul_le_mul_of_nonneg_left
        (finiteExpectedOneSidedRademacherSet_negateFunctionClass_le law n value hbounded)
        (by norm_num)

/-- A finite population mean of a `[0,1]`-valued function remains in
`[0,1]`. -/
theorem finitePopulationMean_mem_Icc
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (hypothesis : Hypothesis) :
    finitePopulationMean law value hypothesis ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold finitePopulationMean
    exact AppliedModelingLib.pmfExp_nonneg_of_forall_nonneg law _
      (fun outcome => (hbounded hypothesis outcome).1)
  · unfold finitePopulationMean
    exact AppliedModelingLib.pmfExp_le_of_forall_le law _ 1
      (fun outcome => (hbounded hypothesis outcome).2)

/-- A nonempty empirical mean of a `[0,1]`-valued function remains in
`[0,1]`. -/
theorem finiteEmpiricalMean_mem_Icc
    {Outcome : Type*} (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) (hypothesis : Hypothesis) :
    finiteEmpiricalMean n value sample hypothesis ∈ Set.Icc (0 : ℝ) 1 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsumNonneg : 0 ≤ ∑ index : Fin n, value hypothesis (sample index) := by
    apply Finset.sum_nonneg
    intro index _
    exact (hbounded hypothesis (sample index)).1
  have hsumLe : ∑ index : Fin n, value hypothesis (sample index) ≤ (n : ℝ) := by
    calc
      ∑ index : Fin n, value hypothesis (sample index) ≤ ∑ _index : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro index _
        exact (hbounded hypothesis (sample index)).2
      _ = n := by simp
  unfold finiteEmpiricalMean
  constructor
  · exact mul_nonneg (by positivity) hsumNonneg
  · calc
      (n : ℝ)⁻¹ * ∑ index : Fin n, value hypothesis (sample index) ≤
          (n : ℝ)⁻¹ * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hsumLe (by positivity)
      _ = 1 := by field_simp

/-- The score range in an arbitrary upper deviation is bounded above under
the primitive `[0,1]` range assumption. -/
theorem bddAbove_range_finiteUpperUniformDeviationScore
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) :
    BddAbove (Set.range fun hypothesis =>
      finitePopulationMean law value hypothesis -
        finiteEmpiricalMean n value sample hypothesis) := by
  refine ⟨1, ?_⟩
  rintro score ⟨hypothesis, rfl⟩
  have hpopulation := finitePopulationMean_mem_Icc law value hbounded hypothesis
  have hempirical := finiteEmpiricalMean_mem_Icc n hn value hbounded sample hypothesis
  rcases hpopulation with ⟨hpopulationLower, hpopulationUpper⟩
  rcases hempirical with ⟨hempiricalLower, hempiricalUpper⟩
  linarith

/-- The score range in an arbitrary lower deviation is bounded above under
the primitive `[0,1]` range assumption. -/
theorem bddAbove_range_finiteLowerUniformDeviationScore
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) :
    BddAbove (Set.range fun hypothesis =>
      finiteEmpiricalMean n value sample hypothesis -
        finitePopulationMean law value hypothesis) := by
  refine ⟨1, ?_⟩
  rintro score ⟨hypothesis, rfl⟩
  have hpopulation := finitePopulationMean_mem_Icc law value hbounded hypothesis
  have hempirical := finiteEmpiricalMean_mem_Icc n hn value hbounded sample hypothesis
  rcases hpopulation with ⟨hpopulationLower, hpopulationUpper⟩
  rcases hempirical with ⟨hempiricalLower, hempiricalUpper⟩
  linarith

/-- Suprema of two nonempty bounded score ranges inherit a uniform
pointwise absolute-difference bound. -/
theorem abs_sSup_range_sub_sSup_range_le_of_forall_abs_sub_le
    [Nonempty Hypothesis]
    (first second : Hypothesis → ℝ)
    (hfirstBdd : BddAbove (Set.range first))
    (hsecondBdd : BddAbove (Set.range second))
    (bound : ℝ)
    (hbound : ∀ hypothesis, |first hypothesis - second hypothesis| ≤ bound) :
    |sSup (Set.range first) - sSup (Set.range second)| ≤ bound := by
  rw [abs_le]
  constructor
  · have hsup : sSup (Set.range second) ≤ sSup (Set.range first) + bound := by
      apply csSup_le (Set.range_nonempty _)
      rintro score ⟨hypothesis, rfl⟩
      have hpoint := hbound hypothesis
      have hfirst : first hypothesis ≤ sSup (Set.range first) :=
        le_csSup hfirstBdd ⟨hypothesis, rfl⟩
      linarith [neg_le_of_abs_le hpoint]
    linarith
  · have hsup : sSup (Set.range first) ≤ sSup (Set.range second) + bound := by
      apply csSup_le (Set.range_nonempty _)
      rintro score ⟨hypothesis, rfl⟩
      have hpoint := hbound hypothesis
      have hsecond : second hypothesis ≤ sSup (Set.range second) :=
        le_csSup hsecondBdd ⟨hypothesis, rfl⟩
      linarith [le_of_abs_le hpoint]
    linarith

/-- Finite suprema inherit a uniform pointwise absolute-difference bound. -/
theorem abs_iSup_sub_iSup_le_of_forall_abs_sub_le
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (first second : Hypothesis → ℝ) (bound : ℝ)
    (hbound : ∀ hypothesis,
      |first hypothesis - second hypothesis| ≤ bound) :
    |(⨆ hypothesis, first hypothesis) - (⨆ hypothesis, second hypothesis)| ≤
      bound := by
  obtain ⟨firstMaximizer, hfirstMaximizer⟩ :=
    exists_eq_ciSup_of_finite (f := first)
  obtain ⟨secondMaximizer, hsecondMaximizer⟩ :=
    exists_eq_ciSup_of_finite (f := second)
  rw [abs_le]
  constructor
  · have hpoint := hbound secondMaximizer
    have hfirstLe := le_ciSup (Finite.bddAbove_range first) secondMaximizer
    rw [← hsecondMaximizer]
    linarith [neg_le_of_abs_le hpoint]
  · have hpoint := hbound firstMaximizer
    have hsecondLe := le_ciSup (Finite.bddAbove_range second) firstMaximizer
    rw [← hfirstMaximizer]
    linarith [le_of_abs_le hpoint]

/-- Replacing one observation changes a `[0,1]` empirical mean by at most `1/n`. -/
theorem abs_finiteEmpiricalMean_sub_update_le_inv
    {Outcome : Type*} (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) (index : Fin n) (replacement : Outcome)
    (hypothesis : Hypothesis) :
    |finiteEmpiricalMean n value sample hypothesis -
        finiteEmpiricalMean n value
          (Function.update sample index replacement) hypothesis| ≤
      (n : ℝ)⁻¹ := by
  have hevaluatedUpdate :
      (fun coordinate : Fin n =>
        value hypothesis ((Function.update sample index replacement) coordinate)) =
      Function.update
        (fun coordinate : Fin n => value hypothesis (sample coordinate))
        index (value hypothesis replacement) := by
    funext coordinate
    by_cases hcoordinate : coordinate = index
    · subst coordinate
      simp
    · simp [Function.update_of_ne hcoordinate]
  have hsumUpdate :
      (∑ coordinate : Fin n,
        value hypothesis ((Function.update sample index replacement) coordinate)) =
      (∑ coordinate : Fin n, value hypothesis (sample coordinate)) -
        value hypothesis (sample index) + value hypothesis replacement := by
    have horiginal :
        (∑ coordinate : Fin n, value hypothesis (sample coordinate)) =
          value hypothesis (sample index) +
            ∑ coordinate ∈ (Finset.univ : Finset (Fin n)) \ {index},
              value hypothesis (sample coordinate) := by
      rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun coordinate => value hypothesis (sample coordinate))
        (Finset.mem_univ index)]
      congr 1
      rw [Finset.sdiff_singleton_eq_erase]
    rw [hevaluatedUpdate,
      Finset.sum_update_of_mem (Finset.mem_univ index)]
    rw [horiginal]
    ring
  have hdifference :
      finiteEmpiricalMean n value sample hypothesis -
          finiteEmpiricalMean n value
            (Function.update sample index replacement) hypothesis =
        (n : ℝ)⁻¹ *
          (value hypothesis (sample index) - value hypothesis replacement) := by
    unfold finiteEmpiricalMean
    rw [hsumUpdate]
    ring
  rw [hdifference, abs_mul, abs_of_nonneg (by positivity)]
  have hvalueDifference :
      |value hypothesis (sample index) - value hypothesis replacement| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [(hbounded hypothesis (sample index)).1,
        (hbounded hypothesis (sample index)).2,
        (hbounded hypothesis replacement).1,
        (hbounded hypothesis replacement).2]
  simpa using mul_le_mul_of_nonneg_left hvalueDifference (by positivity : 0 ≤ (n : ℝ)⁻¹)

/-- A `[0,1]` upper uniform deviation has coordinate sensitivity `1/n`. -/
theorem abs_finiteUpperUniformDeviation_sub_update_le_inv
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) (index : Fin n) (replacement : Outcome) :
    |finiteUpperUniformDeviation law n value sample -
        finiteUpperUniformDeviation law n value
          (Function.update sample index replacement)| ≤
      (n : ℝ)⁻¹ := by
  unfold finiteUpperUniformDeviation
  apply abs_iSup_sub_iSup_le_of_forall_abs_sub_le
  intro hypothesis
  have hempirical := abs_finiteEmpiricalMean_sub_update_le_inv
    n hn value hbounded sample index replacement hypothesis
  simpa [sub_sub_sub_cancel_left, abs_sub_comm] using hempirical

/-- A `[0,1]` lower uniform deviation has coordinate sensitivity `1/n`. -/
theorem abs_finiteLowerUniformDeviation_sub_update_le_inv
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) (index : Fin n) (replacement : Outcome) :
    |finiteLowerUniformDeviation law n value sample -
        finiteLowerUniformDeviation law n value
          (Function.update sample index replacement)| ≤
      (n : ℝ)⁻¹ := by
  unfold finiteLowerUniformDeviation
  apply abs_iSup_sub_iSup_le_of_forall_abs_sub_le
  intro hypothesis
  simpa only [sub_sub_sub_cancel_right] using
    (abs_finiteEmpiricalMean_sub_update_le_inv
      n hn value hbounded sample index replacement hypothesis)

/-- A `[0,1]` upper uniform deviation of an arbitrary class has coordinate
sensitivity `1/n`; no maximizer of the class is assumed. -/
theorem abs_finiteUpperUniformDeviationSet_sub_update_le_inv
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) (index : Fin n) (replacement : Outcome) :
    |finiteUpperUniformDeviationSet law n value sample -
        finiteUpperUniformDeviationSet law n value
          (Function.update sample index replacement)| ≤
      (n : ℝ)⁻¹ := by
  unfold finiteUpperUniformDeviationSet
  apply abs_sSup_range_sub_sSup_range_le_of_forall_abs_sub_le
  · exact bddAbove_range_finiteUpperUniformDeviationScore law n hn value hbounded sample
  · exact bddAbove_range_finiteUpperUniformDeviationScore law n hn value hbounded
      (Function.update sample index replacement)
  · intro hypothesis
    simpa [sub_sub_sub_cancel_left, abs_sub_comm] using
      (abs_finiteEmpiricalMean_sub_update_le_inv
        n hn value hbounded sample index replacement hypothesis)

/-- A `[0,1]` lower uniform deviation of an arbitrary class has coordinate
sensitivity `1/n`. -/
theorem abs_finiteLowerUniformDeviationSet_sub_update_le_inv
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (sample : Fin n → Outcome) (index : Fin n) (replacement : Outcome) :
    |finiteLowerUniformDeviationSet law n value sample -
        finiteLowerUniformDeviationSet law n value
          (Function.update sample index replacement)| ≤
      (n : ℝ)⁻¹ := by
  unfold finiteLowerUniformDeviationSet
  apply abs_sSup_range_sub_sSup_range_le_of_forall_abs_sub_le
  · exact bddAbove_range_finiteLowerUniformDeviationScore law n hn value hbounded sample
  · exact bddAbove_range_finiteLowerUniformDeviationScore law n hn value hbounded
      (Function.update sample index replacement)
  · intro hypothesis
    simpa only [sub_sub_sub_cancel_right] using
      (abs_finiteEmpiricalMean_sub_update_le_inv
        n hn value hbounded sample index replacement hypothesis)

/-- McDiarmid upper tail for the finite upper uniform deviation. -/
theorem pmfProb_finiteUpperUniformDeviation_sub_mean_ge_le_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => epsilon ≤
          finiteUpperUniformDeviation law n value sample -
            AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (finiteUpperUniformDeviation law n value)) ≤
      Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  letI : Nonempty Outcome := ⟨Classical.choose law.support_nonempty⟩
  have hsum :
      (∑ _index : Fin n, ((n : ℝ)⁻¹) ^ 2) = (n : ℝ)⁻¹ := by
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hnReal]
    field_simp
  have htail :=
    AppliedModelingLib.Probability.BoundedDifferences.pmfProb_finProduct_sub_mean_ge_le_exp_of_boundedDifferences
        law n (finiteUpperUniformDeviation law n value)
        (fun _index => (n : ℝ)⁻¹)
        (fun index sample replacement =>
          abs_finiteUpperUniformDeviation_sub_update_le_inv
            law n hn value hbounded sample index replacement)
        epsilon hepsilon (by rw [hsum]; positivity)
  rw [hsum] at htail
  convert htail using 1
  field_simp

/-- McDiarmid upper tail for the finite lower uniform deviation. -/
theorem pmfProb_finiteLowerUniformDeviation_sub_mean_ge_le_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => epsilon ≤
          finiteLowerUniformDeviation law n value sample -
            AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (finiteLowerUniformDeviation law n value)) ≤
      Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  letI : Nonempty Outcome := ⟨Classical.choose law.support_nonempty⟩
  have hsum :
      (∑ _index : Fin n, ((n : ℝ)⁻¹) ^ 2) = (n : ℝ)⁻¹ := by
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hnReal]
    field_simp
  have htail :=
    AppliedModelingLib.Probability.BoundedDifferences.pmfProb_finProduct_sub_mean_ge_le_exp_of_boundedDifferences
        law n (finiteLowerUniformDeviation law n value)
        (fun _index => (n : ℝ)⁻¹)
        (fun index sample replacement =>
          abs_finiteLowerUniformDeviation_sub_update_le_inv
            law n hn value hbounded sample index replacement)
        epsilon hepsilon (by rw [hsum]; positivity)
  rw [hsum] at htail
  convert htail using 1
  field_simp

/-- McDiarmid upper tail for an arbitrary-class upper uniform deviation. -/
theorem pmfProb_finiteUpperUniformDeviationSet_sub_mean_ge_le_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => epsilon ≤
          finiteUpperUniformDeviationSet law n value sample -
            AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (finiteUpperUniformDeviationSet law n value)) ≤
      Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  letI : Nonempty Outcome := ⟨Classical.choose law.support_nonempty⟩
  have hsum :
      (∑ _index : Fin n, ((n : ℝ)⁻¹) ^ 2) = (n : ℝ)⁻¹ := by
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hnReal]
    field_simp
  have htail :=
    AppliedModelingLib.Probability.BoundedDifferences.pmfProb_finProduct_sub_mean_ge_le_exp_of_boundedDifferences
        law n (finiteUpperUniformDeviationSet law n value)
        (fun _index => (n : ℝ)⁻¹)
        (fun index sample replacement =>
          abs_finiteUpperUniformDeviationSet_sub_update_le_inv
            law n hn value hbounded sample index replacement)
        epsilon hepsilon (by rw [hsum]; positivity)
  rw [hsum] at htail
  convert htail using 1
  field_simp

/-- McDiarmid upper tail for an arbitrary-class lower uniform deviation. -/
theorem pmfProb_finiteLowerUniformDeviationSet_sub_mean_ge_le_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => epsilon ≤
          finiteLowerUniformDeviationSet law n value sample -
            AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
              (finiteLowerUniformDeviationSet law n value)) ≤
      Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  letI : Nonempty Outcome := ⟨Classical.choose law.support_nonempty⟩
  have hsum :
      (∑ _index : Fin n, ((n : ℝ)⁻¹) ^ 2) = (n : ℝ)⁻¹ := by
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hnReal]
    field_simp
  have htail :=
    AppliedModelingLib.Probability.BoundedDifferences.pmfProb_finProduct_sub_mean_ge_le_exp_of_boundedDifferences
        law n (finiteLowerUniformDeviationSet law n value)
        (fun _index => (n : ℝ)⁻¹)
        (fun index sample replacement =>
          abs_finiteLowerUniformDeviationSet_sub_update_le_inv
            law n hn value hbounded sample index replacement)
        epsilon hepsilon (by rw [hsum]; positivity)
  rw [hsum] at htail
  convert htail using 1
  field_simp

/-- A sample-uniform empirical-complexity bound also bounds expected complexity. -/
theorem finiteExpectedOneSidedRademacher_le_of_forall
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (value : Hypothesis → Outcome → ℝ)
    (complexityBound : ℝ)
    (hcomplexity : ∀ sample : Fin n → Outcome,
      empiricalOneSidedRademacher n
        (fun hypothesis index => value hypothesis (sample index)) ≤
          complexityBound) :
    finiteExpectedOneSidedRademacher law n value ≤ complexityBound := by
  unfold finiteExpectedOneSidedRademacher
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => empiricalOneSidedRademacher n
          (fun hypothesis index => value hypothesis (sample index))) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun _sample => complexityBound) := by
          exact AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le _ _ _ hcomplexity
    _ = complexityBound := AppliedModelingLib.pmfExp_const _ _

/-- Probability is monotone under pointwise event implication. -/
theorem pmfProb_le_pmfProb_of_imp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    [DecidablePred first] [DecidablePred second]
    (himp : ∀ outcome, first outcome → second outcome) :
    AppliedModelingLib.pmfProb law first ≤ AppliedModelingLib.pmfProb law second := by
  unfold AppliedModelingLib.pmfProb
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro outcome
  by_cases hfirst : first outcome
  · simp [hfirst, himp outcome hfirst]
  · simp only [hfirst, ↓reduceIte]
    split <;> norm_num

/--
High-probability two-sided uniform deviation from a deterministic empirical
Rademacher bound.  The event is written as a finite existential so downstream
paper interfaces can use it without an additional supremum representation.
-/
theorem pmfProb_exists_abs_population_sub_empirical_gt_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (complexityBound epsilon : ℝ)
    (hexpectedComplexity :
      finiteExpectedOneSidedRademacher law n value ≤ complexityBound)
    (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound + epsilon <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  let sampleLaw := AppliedModelingLib.pmfProduct (Fin n) Outcome law
  let upperBad : (Fin n → Outcome) → Prop := fun sample =>
    2 * complexityBound + epsilon <
      finiteUpperUniformDeviation law n value sample
  let lowerBad : (Fin n → Outcome) → Prop := fun sample =>
    2 * complexityBound + epsilon <
      finiteLowerUniformDeviation law n value sample
  let upperTail : (Fin n → Outcome) → Prop := fun sample =>
    epsilon ≤ finiteUpperUniformDeviation law n value sample -
      AppliedModelingLib.pmfExp sampleLaw (finiteUpperUniformDeviation law n value)
  let lowerTail : (Fin n → Outcome) → Prop := fun sample =>
    epsilon ≤ finiteLowerUniformDeviation law n value sample -
      AppliedModelingLib.pmfExp sampleLaw (finiteLowerUniformDeviation law n value)
  have hupperMean :
      AppliedModelingLib.pmfExp sampleLaw (finiteUpperUniformDeviation law n value) ≤
        2 * complexityBound :=
    (pmfExp_finiteUpperUniformDeviation_le_two_expectedRademacher
      law n hn value).trans (mul_le_mul_of_nonneg_left hexpectedComplexity (by norm_num))
  have hlowerMean :
      AppliedModelingLib.pmfExp sampleLaw (finiteLowerUniformDeviation law n value) ≤
        2 * complexityBound :=
    (pmfExp_finiteLowerUniformDeviation_le_two_expectedRademacher
      law n hn value).trans (mul_le_mul_of_nonneg_left hexpectedComplexity (by norm_num))
  have habsToUnion : ∀ sample,
      (∃ hypothesis,
        2 * complexityBound + epsilon <
          |finitePopulationMean law value hypothesis -
            finiteEmpiricalMean n value sample hypothesis|) →
        upperBad sample ∨ lowerBad sample := by
    intro sample
    rintro ⟨hypothesis, hbad⟩
    rw [abs_eq_max_neg, lt_max_iff] at hbad
    rcases hbad with hupper | hlower
    · left
      exact hupper.trans_le
        (le_ciSup
          (Finite.bddAbove_range fun candidate =>
            finitePopulationMean law value candidate -
              finiteEmpiricalMean n value sample candidate)
          hypothesis)
    · right
      have hlower' :
          2 * complexityBound + epsilon <
            finiteEmpiricalMean n value sample hypothesis -
              finitePopulationMean law value hypothesis := by
        linarith
      exact hlower'.trans_le
        (le_ciSup
          (Finite.bddAbove_range fun candidate =>
            finiteEmpiricalMean n value sample candidate -
              finitePopulationMean law value candidate)
          hypothesis)
  have hupperToTail : ∀ sample, upperBad sample → upperTail sample := by
    intro sample hbad
    dsimp only [upperBad, upperTail] at hbad ⊢
    linarith
  have hlowerToTail : ∀ sample, lowerBad sample → lowerTail sample := by
    intro sample hbad
    dsimp only [lowerBad, lowerTail] at hbad ⊢
    linarith
  have hupperProbability :
      AppliedModelingLib.pmfProb sampleLaw upperTail ≤
        Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
    simpa [sampleLaw, upperTail] using
      pmfProb_finiteUpperUniformDeviation_sub_mean_ge_le_exp
        law n hn value hbounded epsilon hepsilon
  have hlowerProbability :
      AppliedModelingLib.pmfProb sampleLaw lowerTail ≤
        Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
    simpa [sampleLaw, lowerTail] using
      pmfProb_finiteLowerUniformDeviation_sub_mean_ge_le_exp
        law n hn value hbounded epsilon hepsilon
  calc
    AppliedModelingLib.pmfProb sampleLaw
        (fun sample => ∃ hypothesis,
          2 * complexityBound + epsilon <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      AppliedModelingLib.pmfProb sampleLaw
        (fun sample => upperBad sample ∨ lowerBad sample) :=
          pmfProb_le_pmfProb_of_imp sampleLaw _ _ habsToUnion
    _ ≤ AppliedModelingLib.pmfProb sampleLaw upperBad +
        AppliedModelingLib.pmfProb sampleLaw lowerBad :=
      AppliedModelingLib.pmfProb_or_le sampleLaw upperBad lowerBad
    _ ≤ AppliedModelingLib.pmfProb sampleLaw upperTail +
        AppliedModelingLib.pmfProb sampleLaw lowerTail :=
      add_le_add
        (pmfProb_le_pmfProb_of_imp sampleLaw upperBad upperTail hupperToTail)
        (pmfProb_le_pmfProb_of_imp sampleLaw lowerBad lowerTail hlowerToTail)
    _ ≤ Real.exp (-2 * (n : ℝ) * epsilon ^ 2) +
        Real.exp (-2 * (n : ℝ) * epsilon ^ 2) :=
      add_le_add hupperProbability hlowerProbability
    _ = 2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by ring

noncomputable local instance finiteRademacherClassicalPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- High-probability two-sided uniform deviation for an arbitrary bounded
class under a finite iid law.  The class is represented by genuine real
suprema, while concentration uses the finite sample space rather than a
finite hypothesis enumeration. -/
theorem pmfProb_exists_abs_population_sub_empirical_gt_le_set
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (complexityBound epsilon : ℝ)
    (hexpectedComplexity :
      finiteExpectedOneSidedRademacherSet law n value ≤ complexityBound)
    (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound + epsilon <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  classical
  let sampleLaw := AppliedModelingLib.pmfProduct (Fin n) Outcome law
  let upperBad : (Fin n → Outcome) → Prop := fun sample =>
    2 * complexityBound + epsilon <
      finiteUpperUniformDeviationSet law n value sample
  let lowerBad : (Fin n → Outcome) → Prop := fun sample =>
    2 * complexityBound + epsilon <
      finiteLowerUniformDeviationSet law n value sample
  let upperTail : (Fin n → Outcome) → Prop := fun sample =>
    epsilon ≤ finiteUpperUniformDeviationSet law n value sample -
      AppliedModelingLib.pmfExp sampleLaw (finiteUpperUniformDeviationSet law n value)
  let lowerTail : (Fin n → Outcome) → Prop := fun sample =>
    epsilon ≤ finiteLowerUniformDeviationSet law n value sample -
      AppliedModelingLib.pmfExp sampleLaw (finiteLowerUniformDeviationSet law n value)
  have habs : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1 := by
    intro hypothesis outcome
    rw [abs_of_nonneg (hbounded hypothesis outcome).1]
    exact (hbounded hypothesis outcome).2
  have hupperMean :
      AppliedModelingLib.pmfExp sampleLaw (finiteUpperUniformDeviationSet law n value) ≤
        2 * complexityBound :=
    (pmfExp_finiteUpperUniformDeviationSet_le_two_expectedRademacherSet
      law n hn value habs).trans
        (mul_le_mul_of_nonneg_left hexpectedComplexity (by norm_num))
  have hlowerMean :
      AppliedModelingLib.pmfExp sampleLaw (finiteLowerUniformDeviationSet law n value) ≤
        2 * complexityBound :=
    (pmfExp_finiteLowerUniformDeviationSet_le_two_expectedRademacherSet
      law n hn value habs).trans
        (mul_le_mul_of_nonneg_left hexpectedComplexity (by norm_num))
  have habsToUnion : ∀ sample,
      (∃ hypothesis,
        2 * complexityBound + epsilon <
          |finitePopulationMean law value hypothesis -
            finiteEmpiricalMean n value sample hypothesis|) →
        upperBad sample ∨ lowerBad sample := by
    intro sample
    rintro ⟨hypothesis, hbad⟩
    rw [abs_eq_max_neg, lt_max_iff] at hbad
    rcases hbad with hupper | hlower
    · left
      exact hupper.trans_le
        (le_csSup
          (bddAbove_range_finiteUpperUniformDeviationScore law n hn value hbounded sample)
          ⟨hypothesis, rfl⟩)
    · right
      have hlower' :
          2 * complexityBound + epsilon <
            finiteEmpiricalMean n value sample hypothesis -
              finitePopulationMean law value hypothesis := by
        linarith
      exact hlower'.trans_le
        (le_csSup
          (bddAbove_range_finiteLowerUniformDeviationScore law n hn value hbounded sample)
          ⟨hypothesis, rfl⟩)
  have hupperToTail : ∀ sample, upperBad sample → upperTail sample := by
    intro sample hbad
    dsimp only [upperBad, upperTail] at hbad ⊢
    linarith
  have hlowerToTail : ∀ sample, lowerBad sample → lowerTail sample := by
    intro sample hbad
    dsimp only [lowerBad, lowerTail] at hbad ⊢
    linarith
  have hupperProbability :
      AppliedModelingLib.pmfProb sampleLaw upperTail ≤
        Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
    simpa [sampleLaw, upperTail] using
      pmfProb_finiteUpperUniformDeviationSet_sub_mean_ge_le_exp
        law n hn value hbounded epsilon hepsilon
  have hlowerProbability :
      AppliedModelingLib.pmfProb sampleLaw lowerTail ≤
        Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
    simpa [sampleLaw, lowerTail] using
      pmfProb_finiteLowerUniformDeviationSet_sub_mean_ge_le_exp
        law n hn value hbounded epsilon hepsilon
  calc
    AppliedModelingLib.pmfProb sampleLaw
        (fun sample => ∃ hypothesis,
          2 * complexityBound + epsilon <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      AppliedModelingLib.pmfProb sampleLaw
        (fun sample => upperBad sample ∨ lowerBad sample) :=
          pmfProb_le_pmfProb_of_imp sampleLaw _ _ habsToUnion
    _ ≤ AppliedModelingLib.pmfProb sampleLaw upperBad +
        AppliedModelingLib.pmfProb sampleLaw lowerBad :=
      AppliedModelingLib.pmfProb_or_le sampleLaw upperBad lowerBad
    _ ≤ AppliedModelingLib.pmfProb sampleLaw upperTail +
        AppliedModelingLib.pmfProb sampleLaw lowerTail :=
      add_le_add
        (pmfProb_le_pmfProb_of_imp sampleLaw upperBad upperTail hupperToTail)
        (pmfProb_le_pmfProb_of_imp sampleLaw lowerBad lowerTail hlowerToTail)
    _ ≤ Real.exp (-2 * (n : ℝ) * epsilon ^ 2) +
        Real.exp (-2 * (n : ℝ) * epsilon ^ 2) :=
      add_le_add hupperProbability hlowerProbability
    _ = 2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by ring

/-- Confidence-level form of the arbitrary-class finite-PMF Rademacher
deviation theorem. -/
theorem pmfProb_exists_abs_population_sub_empirical_gt_confidence_le_set
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (complexityBound delta : ℝ)
    (hexpectedComplexity :
      finiteExpectedOneSidedRademacherSet law n value ≤ complexityBound)
    (hdeltaPositive : 0 < delta) (hdeltaOne : delta < 1) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound +
              Real.sqrt (2 * Real.log (2 / delta) / (n : ℝ)) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      delta := by
  let epsilon : ℝ := Real.sqrt (2 * Real.log (2 / delta) / (n : ℝ))
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratioOne : 1 ≤ 2 / delta := by
    rw [le_div_iff₀ hdeltaPositive]
    linarith
  have hlogNonneg : 0 ≤ Real.log (2 / delta) :=
    Real.log_nonneg hratioOne
  have hepsilonSq : epsilon ^ 2 =
      2 * Real.log (2 / delta) / (n : ℝ) := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hlogNonneg) hnReal.le)
  have hepsilonNonneg : 0 ≤ epsilon := Real.sqrt_nonneg _
  have hraw := pmfProb_exists_abs_population_sub_empirical_gt_le_set
    law n hn value hbounded complexityBound epsilon
      hexpectedComplexity hepsilonNonneg
  have hlogInverse : Real.log (delta / 2) = -Real.log (2 / delta) := by
    have hinverse : delta / 2 = (2 / delta)⁻¹ := by
      field_simp [hdeltaPositive.ne']
    rw [hinverse, Real.log_inv]
  have hexponent :
      -2 * (n : ℝ) * epsilon ^ 2 ≤ Real.log (delta / 2) := by
    rw [hepsilonSq, hlogInverse]
    field_simp [hnReal.ne']
    nlinarith
  calc
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound +
              Real.sqrt (2 * Real.log (2 / delta) / (n : ℝ)) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := hraw
    _ ≤ 2 * Real.exp (Real.log (delta / 2)) := by
      gcongr
    _ = delta := by
      rw [Real.exp_log (div_pos hdeltaPositive (by norm_num))]
      ring

/--
Confidence-level form of the finite-class Rademacher deviation theorem.  The
tail constant matches the deliberately conservative term printed in Hardt et
al.'s Claim 2.8.
-/
theorem pmfProb_exists_abs_population_sub_empirical_gt_confidence_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      0 ≤ value hypothesis outcome ∧ value hypothesis outcome ≤ 1)
    (complexityBound delta : ℝ)
    (hexpectedComplexity :
      finiteExpectedOneSidedRademacher law n value ≤ complexityBound)
    (hdeltaPositive : 0 < delta) (hdeltaOne : delta < 1) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound +
              Real.sqrt (2 * Real.log (2 / delta) / (n : ℝ)) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      delta := by
  let epsilon : ℝ := Real.sqrt (2 * Real.log (2 / delta) / (n : ℝ))
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratioOne : 1 ≤ 2 / delta := by
    rw [le_div_iff₀ hdeltaPositive]
    linarith
  have hlogNonneg : 0 ≤ Real.log (2 / delta) :=
    Real.log_nonneg hratioOne
  have hepsilonSq : epsilon ^ 2 =
      2 * Real.log (2 / delta) / (n : ℝ) := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hlogNonneg) hnReal.le)
  have hepsilonNonneg : 0 ≤ epsilon := Real.sqrt_nonneg _
  have hraw := pmfProb_exists_abs_population_sub_empirical_gt_le
    law n hn value hbounded complexityBound epsilon
      hexpectedComplexity hepsilonNonneg
  have hlogInverse : Real.log (delta / 2) = -Real.log (2 / delta) := by
    have hinverse : delta / 2 = (2 / delta)⁻¹ := by
      field_simp [hdeltaPositive.ne']
    rw [hinverse, Real.log_inv]
  have hexponent :
      -2 * (n : ℝ) * epsilon ^ 2 ≤ Real.log (delta / 2) := by
    rw [hepsilonSq, hlogInverse]
    field_simp [hnReal.ne']
    nlinarith
  calc
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound +
              Real.sqrt (2 * Real.log (2 / delta) / (n : ℝ)) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := hraw
    _ ≤ 2 * Real.exp (Real.log (delta / 2)) := by
      gcongr
    _ = delta := by
      rw [Real.exp_log (div_pos hdeltaPositive (by norm_num))]
      ring

/-- The finite-class uniform-deviation theorem for scores in `[-1,1]`.
It is obtained by the affine normalization `(value + 1) / 2`; the complexity
parameter is therefore that of the normalized class, and the displayed
deviation is rescaled by two. -/
theorem pmfProb_exists_abs_population_sub_empirical_gt_le_of_abs_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (complexityBound epsilon : ℝ)
    (hexpectedComplexity :
      finiteExpectedOneSidedRademacher law n
        (fun hypothesis outcome => (value hypothesis outcome + 1) / 2) ≤ complexityBound)
    (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * (2 * complexityBound + epsilon) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  let normalized : Hypothesis → Outcome → ℝ :=
    fun hypothesis outcome => (value hypothesis outcome + 1) / 2
  have hnormalizedBounded : ∀ hypothesis outcome,
      0 ≤ normalized hypothesis outcome ∧ normalized hypothesis outcome ≤ 1 := by
    intro hypothesis outcome
    dsimp [normalized]
    have h := hbounded hypothesis outcome
    rw [abs_le] at h
    constructor <;> linarith
  have htail := pmfProb_exists_abs_population_sub_empirical_gt_le
    law n hn normalized hnormalizedBounded complexityBound epsilon
      (by simpa [normalized] using hexpectedComplexity) hepsilon
  have hscale : ∀ sample hypothesis,
      finitePopulationMean law normalized hypothesis -
          finiteEmpiricalMean n normalized sample hypothesis =
        (finitePopulationMean law value hypothesis -
          finiteEmpiricalMean n value sample hypothesis) / 2 := by
    intro sample hypothesis
    unfold finitePopulationMean finiteEmpiricalMean normalized
    have hfun : (fun outcome => (value hypothesis outcome + 1) / 2) =
        (fun outcome => value hypothesis outcome * (1 / 2) + 1 / 2) := by
      funext outcome
      ring
    rw [hfun, pmfExp_add, pmfExp_mul_const, pmfExp_const]
    have hsum : (∑ index : Fin n, (value hypothesis (sample index) + 1) / 2) =
        (∑ index : Fin n, value hypothesis (sample index)) / 2 + (n : ℝ) / 2 := by
      calc
        (∑ index : Fin n, (value hypothesis (sample index) + 1) / 2) =
            ∑ index : Fin n, (value hypothesis (sample index) * (1 / 2) + 1 / 2) := by
              apply Finset.sum_congr rfl
              intro index _
              ring
        _ = (∑ index : Fin n, value hypothesis (sample index)) / 2 + (n : ℝ) / 2 := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
              simp
              ring
    rw [hsum]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnReal]
    ring
  calc
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * (2 * complexityBound + epsilon) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) =
      AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound + epsilon <
            |finitePopulationMean law normalized hypothesis -
              finiteEmpiricalMean n normalized sample hypothesis|) := by
          apply AppliedModelingLib.pmfProb_congr
          intro sample
          constructor
          · rintro ⟨hypothesis, h⟩
            refine ⟨hypothesis, ?_⟩
            rw [hscale]
            rw [abs_div]
            norm_num
            linarith
          · rintro ⟨hypothesis, h⟩
            refine ⟨hypothesis, ?_⟩
            rw [hscale] at h
            rw [abs_div] at h
            norm_num at h
            linarith
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := htail

/-- The arbitrary-class finite-PMF uniform-deviation theorem for scores in
`[-1,1]`, obtained by affine normalization. -/
theorem pmfProb_exists_abs_population_sub_empirical_gt_le_set_of_abs_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Hypothesis]
    (law : PMF Outcome) (n : ℕ) (hn : 0 < n)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (complexityBound epsilon : ℝ)
    (hexpectedComplexity :
      finiteExpectedOneSidedRademacherSet law n
        (fun hypothesis outcome => (value hypothesis outcome + 1) / 2) ≤ complexityBound)
    (hepsilon : 0 ≤ epsilon) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * (2 * complexityBound + epsilon) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) ≤
      2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := by
  let normalized : Hypothesis → Outcome → ℝ :=
    fun hypothesis outcome => (value hypothesis outcome + 1) / 2
  have hnormalizedBounded : ∀ hypothesis outcome,
      0 ≤ normalized hypothesis outcome ∧ normalized hypothesis outcome ≤ 1 := by
    intro hypothesis outcome
    dsimp [normalized]
    have h := hbounded hypothesis outcome
    rw [abs_le] at h
    constructor <;> linarith
  have htail := pmfProb_exists_abs_population_sub_empirical_gt_le_set
    law n hn normalized hnormalizedBounded complexityBound epsilon
      (by simpa [normalized] using hexpectedComplexity) hepsilon
  have hscale : ∀ sample hypothesis,
      finitePopulationMean law normalized hypothesis -
          finiteEmpiricalMean n normalized sample hypothesis =
        (finitePopulationMean law value hypothesis -
          finiteEmpiricalMean n value sample hypothesis) / 2 := by
    intro sample hypothesis
    unfold finitePopulationMean finiteEmpiricalMean normalized
    have hfun : (fun outcome => (value hypothesis outcome + 1) / 2) =
        (fun outcome => value hypothesis outcome * (1 / 2) + 1 / 2) := by
      funext outcome
      ring
    rw [hfun, pmfExp_add, pmfExp_mul_const, pmfExp_const]
    have hsum : (∑ index : Fin n, (value hypothesis (sample index) + 1) / 2) =
        (∑ index : Fin n, value hypothesis (sample index)) / 2 + (n : ℝ) / 2 := by
      calc
        (∑ index : Fin n, (value hypothesis (sample index) + 1) / 2) =
            ∑ index : Fin n, (value hypothesis (sample index) * (1 / 2) + 1 / 2) := by
              apply Finset.sum_congr rfl
              intro index _
              ring
        _ = (∑ index : Fin n, value hypothesis (sample index)) / 2 + (n : ℝ) / 2 := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
              simp
              ring
    rw [hsum]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnReal]
    ring
  calc
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * (2 * complexityBound + epsilon) <
            |finitePopulationMean law value hypothesis -
              finiteEmpiricalMean n value sample hypothesis|) =
      AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Outcome law)
        (fun sample => ∃ hypothesis,
          2 * complexityBound + epsilon <
            |finitePopulationMean law normalized hypothesis -
              finiteEmpiricalMean n normalized sample hypothesis|) := by
          apply AppliedModelingLib.pmfProb_congr
          intro sample
          constructor
          · rintro ⟨hypothesis, h⟩
            refine ⟨hypothesis, ?_⟩
            rw [hscale]
            rw [abs_div]
            norm_num
            linarith
          · rintro ⟨hypothesis, h⟩
            refine ⟨hypothesis, ?_⟩
            rw [hscale] at h
            rw [abs_div] at h
            norm_num at h
            linarith
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * epsilon ^ 2) := htail

/--
Finite-class exponential-moment maximum bound at an arbitrary positive tilt.
This is the reusable log-sum-exp core of Massart's finite-class lemma.
-/
theorem pmfExp_iSup_le_log_card_div_add_of_expMoment
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (law : PMF Outcome) (value : Hypothesis → Outcome → ℝ)
    {tilt variance : ℝ} (htilt : 0 < tilt)
    (hexpMoment : ∀ hypothesis,
      AppliedModelingLib.pmfExp law
          (fun outcome => Real.exp (tilt * value hypothesis outcome)) ≤
        Real.exp (tilt ^ 2 * variance / 2)) :
    AppliedModelingLib.pmfExp law (fun outcome => ⨆ hypothesis, value hypothesis outcome) ≤
      Real.log (Fintype.card Hypothesis : ℝ) / tilt + tilt * variance / 2 := by
  let maximum : Outcome → ℝ :=
    fun outcome => ⨆ hypothesis, value hypothesis outcome
  have hpointwise : ∀ outcome,
      Real.exp (tilt * maximum outcome) ≤
        ∑ hypothesis : Hypothesis,
          Real.exp (tilt * value hypothesis outcome) := by
    intro outcome
    obtain ⟨maximizer, hmaximizer⟩ :=
      exists_eq_ciSup_of_finite
        (f := fun hypothesis => value hypothesis outcome)
    change Real.exp (tilt * (⨆ hypothesis, value hypothesis outcome)) ≤ _
    rw [← hmaximizer]
    exact Finset.single_le_sum
      (fun hypothesis _ => Real.exp_nonneg
        (tilt * value hypothesis outcome))
      (Finset.mem_univ maximizer)
  have hjensen :
      Real.exp
          (tilt * AppliedModelingLib.pmfExp law maximum) ≤
        AppliedModelingLib.pmfExp law
          (fun outcome => Real.exp (tilt * maximum outcome)) := by
    simpa only [AppliedModelingLib.pmfExp_const_mul] using
      exp_pmfExp_le_pmfExp_exp law (fun outcome => tilt * maximum outcome)
  have hmoment :
      Real.exp (tilt * AppliedModelingLib.pmfExp law maximum) ≤
        (Fintype.card Hypothesis : ℝ) *
          Real.exp (tilt ^ 2 * variance / 2) := by
    calc
      Real.exp (tilt * AppliedModelingLib.pmfExp law maximum) ≤
          AppliedModelingLib.pmfExp law
            (fun outcome => Real.exp (tilt * maximum outcome)) := hjensen
      _ ≤ AppliedModelingLib.pmfExp law
          (fun outcome => ∑ hypothesis : Hypothesis,
            Real.exp (tilt * value hypothesis outcome)) :=
        AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le law _ _ hpointwise
      _ = ∑ hypothesis : Hypothesis,
          AppliedModelingLib.pmfExp law
            (fun outcome => Real.exp (tilt * value hypothesis outcome)) := by
        simpa using AppliedModelingLib.pmfExp_sum law
          (Finset.univ : Finset Hypothesis)
          (fun hypothesis outcome =>
            Real.exp (tilt * value hypothesis outcome))
      _ ≤ ∑ _hypothesis : Hypothesis,
          Real.exp (tilt ^ 2 * variance / 2) := by
        apply Finset.sum_le_sum
        intro hypothesis _
        exact hexpMoment hypothesis
      _ = (Fintype.card Hypothesis : ℝ) *
          Real.exp (tilt ^ 2 * variance / 2) := by simp
  have hcardPositive : 0 < (Fintype.card Hypothesis : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty Hypothesis)
  have hlog := Real.log_le_log (Real.exp_pos _) hmoment
  rw [Real.log_exp,
    Real.log_mul hcardPositive.ne' (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  change AppliedModelingLib.pmfExp law maximum ≤
    Real.log (Fintype.card Hypothesis : ℝ) / tilt +
      tilt * variance / 2
  have hquotient :
      AppliedModelingLib.pmfExp law maximum ≤
        (Real.log (Fintype.card Hypothesis : ℝ) +
          tilt ^ 2 * variance / 2) / tilt := by
    apply (le_div_iff₀ htilt).2
    simpa [mul_comm] using hlog
  calc
    AppliedModelingLib.pmfExp law maximum ≤
        (Real.log (Fintype.card Hypothesis : ℝ) +
          tilt ^ 2 * variance / 2) / tilt := hquotient
    _ = Real.log (Fintype.card Hypothesis : ℝ) / tilt +
        tilt * variance / 2 := by
      field_simp

/-- The uniform Boolean PMF is Mathlib's fair Bernoulli law. -/
theorem uniformPMF_bool_toMeasure_eq_fairMeasure :
    (AppliedModelingLib.uniformPMF Bool).toMeasure =
      AppliedModelingLib.FairCoin.fairMeasure := by
  have hlaw :
      AppliedModelingLib.uniformPMF Bool =
        PMF.bernoulli (1 / 2 : NNReal) (by norm_num) := by
    ext sign
    cases sign <;>
      norm_num [AppliedModelingLib.uniformPMF, PMF.bernoulli]
  rw [hlaw]
  rfl

/--
For a finite coordinate type, the uniform Boolean-function PMF induces the
same measure as the reusable fair-product Rademacher construction.
-/
theorem uniformBooleanFunction_toMeasure_eq_fairProduct
    (Index : Type*) [Fintype Index] [DecidableEq Index] :
    (AppliedModelingLib.uniformPMF (Index → Bool)).toMeasure =
      AppliedModelingLib.FairCoin.productMeasure Index := by
  rw [← AppliedModelingLib.pmfProduct_uniformPMF_eq_uniformPMF_fun]
  rw [AppliedModelingLib.pmfProduct_toMeasure_eq_measurePi]
  rw [uniformPMF_bool_toMeasure_eq_fairMeasure]
  exact
    (@MeasureTheory.Measure.infinitePi_eq_pi Index (fun _ => Bool)
      (fun _ => inferInstance)
      (fun _ => AppliedModelingLib.FairCoin.fairMeasure)
      (fun _ => AppliedModelingLib.FairCoin.fairMeasure_isProbabilityMeasure) _).symm

/--
Exponential-moment bound for a deterministic Rademacher linear form under the
uniform finite sign PMF.  This transports the existing library
`HasSubgaussianMGF` theorem rather than reproving Hoeffding's lemma.
-/
theorem pmfExp_exp_rademacherSum_le
    (n : ℕ) (coefficient : Fin n → ℝ) (tilt : ℝ) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => Real.exp
          (tilt * ∑ index : Fin n,
            rademacherSign (signs index) * coefficient index)) ≤
      Real.exp
        (tilt ^ 2 *
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq coefficient / 2) := by
  have hmgf :=
    (hasSubgaussianMGF_sum_weightedSign_l2Sq coefficient).mgf_le tilt
  rw [AppliedModelingLib.pmfExp_eq_integral_toMeasure]
  rw [uniformBooleanFunction_toMeasure_eq_fairProduct]
  simpa [ProbabilityTheory.mgf, weightedSign, mul_comm] using hmgf

/-- Every coordinate of a uniform finite Rademacher sign vector has mean zero. -/
theorem pmfExp_rademacherSign_uniformBooleanFunction
    (n : ℕ) (index : Fin n) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
        (fun signs => rademacherSign (signs index)) = 0 := by
  rw [AppliedModelingLib.pmfExp_eq_integral_toMeasure]
  rw [uniformBooleanFunction_toMeasure_eq_fairProduct]
  exact integral_rademacherSign_productMeasure (Fin n) index

/-- A singleton function class has zero one-sided empirical complexity. -/
theorem empiricalOneSidedRademacher_eq_zero_of_subsingleton
    [Fintype Hypothesis] [Nonempty Hypothesis] [Subsingleton Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ) :
    empiricalOneSidedRademacher n value = 0 := by
  let sole : Hypothesis := Classical.choice (inferInstance : Nonempty Hypothesis)
  have hsup : ∀ signs : Fin n → Bool,
      (⨆ hypothesis,
        ∑ index : Fin n,
          rademacherSign (signs index) * value hypothesis index) =
        ∑ index : Fin n,
          rademacherSign (signs index) * value sole index := by
    intro signs
    apply le_antisymm
    · apply ciSup_le
      intro hypothesis
      rw [Subsingleton.elim hypothesis sole]
    · exact le_ciSup
        (Finite.bddAbove_range fun hypothesis =>
          ∑ index : Fin n,
            rademacherSign (signs index) * value hypothesis index)
        sole
  have hmean :
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => ∑ index : Fin n,
            rademacherSign (signs index) * value sole index) = 0 := by
    calc
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => ∑ index : Fin n,
            rademacherSign (signs index) * value sole index) =
        ∑ index : Fin n,
          AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
            (fun signs => rademacherSign (signs index) * value sole index) := by
          simpa using AppliedModelingLib.pmfExp_sum
            (AppliedModelingLib.uniformPMF (Fin n → Bool))
            (Finset.univ : Finset (Fin n))
            (fun index signs =>
              rademacherSign (signs index) * value sole index)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro index _
        rw [AppliedModelingLib.pmfExp_mul_const,
          pmfExp_rademacherSign_uniformBooleanFunction, zero_mul]
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
  rw [AppliedModelingLib.pmfExp_congr
    (AppliedModelingLib.uniformPMF (Fin n → Bool)) hsup, hmean, mul_zero]

/--
Massart-style finite-class bound for a `[-1,1]`-valued class, with the slightly
looser constant `2` used in Hardt et al.'s Claim 2.8.  The proof chooses a
simple positive exponential tilt rather than optimizing the constant.
-/
theorem empiricalOneSidedRademacher_le_two_sqrt_log_card_div
    [Fintype Hypothesis] [Nonempty Hypothesis]
    (n : ℕ) (value : Hypothesis → Fin n → ℝ)
    (hn : 0 < n) (hcard : 1 < Fintype.card Hypothesis)
    (hbounded : ∀ hypothesis index, |value hypothesis index| ≤ 1) :
    empiricalOneSidedRademacher n value ≤
      2 * Real.sqrt
        (Real.log (Fintype.card Hypothesis : ℝ) / (n : ℝ)) := by
  let logCard : ℝ := Real.log (Fintype.card Hypothesis : ℝ)
  let tilt : ℝ := Real.sqrt (logCard / (n : ℝ))
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcardReal : 1 < (Fintype.card Hypothesis : ℝ) := by
    exact_mod_cast hcard
  have hlogCard : 0 < logCard := by
    exact Real.log_pos hcardReal
  have hratio : 0 < logCard / (n : ℝ) :=
    div_pos hlogCard hnReal
  have htilt : 0 < tilt := Real.sqrt_pos.2 hratio
  have htiltSq : tilt ^ 2 = logCard / (n : ℝ) := by
    exact Real.sq_sqrt hratio.le
  have hlogCardEq : logCard = (n : ℝ) * tilt ^ 2 := by
    rw [htiltSq]
    field_simp
  have hl2Sq : ∀ hypothesis,
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (value hypothesis) ≤ (n : ℝ) := by
    intro hypothesis
    rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
    calc
      (∑ index : Fin n, value hypothesis index ^ 2) ≤
          ∑ _index : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro index _
        nlinarith [sq_abs (value hypothesis index), abs_nonneg (value hypothesis index),
          hbounded hypothesis index]
      _ = (n : ℝ) := by simp
  have hexpMoment : ∀ hypothesis,
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => Real.exp
            (tilt * ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index)) ≤
        Real.exp (tilt ^ 2 * (n : ℝ) / 2) := by
    intro hypothesis
    refine (pmfExp_exp_rademacherSum_le n (value hypothesis) tilt).trans ?_
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg tilt, hl2Sq hypothesis]
  have hmaximum :=
    pmfExp_iSup_le_log_card_div_add_of_expMoment
      (AppliedModelingLib.uniformPMF (Fin n → Bool))
      (fun hypothesis signs =>
        ∑ index : Fin n,
          rademacherSign (signs index) * value hypothesis index)
      htilt hexpMoment
  unfold empiricalOneSidedRademacher empiricalOneSidedRademacherSum
  calc
    (n : ℝ)⁻¹ *
        AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin n → Bool))
          (fun signs => ⨆ hypothesis,
            ∑ index : Fin n,
              rademacherSign (signs index) * value hypothesis index) ≤
      (n : ℝ)⁻¹ *
        (Real.log (Fintype.card Hypothesis : ℝ) / tilt +
          tilt * (n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hmaximum (by positivity)
    _ ≤ 2 * tilt := by
      change (n : ℝ)⁻¹ *
        (logCard / tilt + tilt * (n : ℝ) / 2) ≤ 2 * tilt
      rw [hlogCardEq]
      field_simp [hnReal.ne', htilt.ne']
      nlinarith [htilt.le]
    _ = 2 * Real.sqrt
        (Real.log (Fintype.card Hypothesis : ℝ) / (n : ℝ)) := rfl

end FiniteRademacher
end Statistics
end AppliedModelingLib

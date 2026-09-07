import AppliedModelingLib.Foundations.Probability.FiniteTransport
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Probability.Moments.SubGaussian

/-!
# Finite-product bounded differences

Reusable finite-PMF exponential-moment and tail bounds for functions whose
value changes by a controlled amount when one input coordinate is replaced.

## Upstream provenance

The Doob/conditional-Hoeffding proof architecture is adapted to a finite PMF
API from AutoRes's `FoML/Probability/McDiarmid.lean` at commit
`bc333764168dab8ac58afcec4b9df8cacf9b54ad`:

* repository: <https://github.com/auto-res/lean-rademacher>
* source: <https://github.com/auto-res/lean-rademacher/blob/bc333764168dab8ac58afcec4b9df8cacf9b54ad/FoML/Probability/McDiarmid.lean>
* license: MIT, copyright (c) 2025 AutoRes

The upstream project targets an older Lean/Mathlib stack and is not imported.
Its MIT license permits use, modification, and redistribution provided the
copyright and permission notice are retained; that license was checked before
this adaptation.

The scalar Hoeffding lemma is used directly from Mathlib at this repository's
pinned commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`:

* source: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/SubGaussian.lean>
* license: Apache-2.0,
  <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/LICENSE>

The Mathlib API is imported, not copied.  Apache-2.0 permits this use and
redistribution subject to its notice, attribution, and patent-license terms.
-/

namespace AppliedModelingLib
namespace Probability
namespace BoundedDifferences

open MeasureTheory ProbabilityTheory

/--
A finite random variable with pairwise oscillation at most `bound` has the
centered Hoeffding exponential-moment bound with variance proxy
`bound^2/4`.
-/
theorem pmfExp_exp_mul_sub_mean_le_of_pairwise_abs_sub_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
    (law : PMF Outcome) (value : Outcome → ℝ) (bound tilt : ℝ)
    (hoscillation : ∀ first second,
      |value first - value second| ≤ bound) :
    pmfExp law
        (fun outcome => Real.exp
          (tilt * (value outcome - pmfExp law value))) ≤
      Real.exp (bound ^ 2 * tilt ^ 2 / 8) := by
  classical
  letI : MeasurableSpace Outcome := ⊤
  obtain ⟨minimum, hminimum⟩ :=
    exists_eq_ciInf_of_finite (f := value)
  obtain ⟨maximum, hmaximum⟩ :=
    exists_eq_ciSup_of_finite (f := value)
  have hbounds : ∀ outcome,
      value outcome ∈ Set.Icc (value minimum) (value maximum) := by
    intro outcome
    constructor
    · rw [hminimum]
      exact ciInf_le (Finite.bddBelow_range value) outcome
    · rw [hmaximum]
      exact le_ciSup (Finite.bddAbove_range value) outcome
  have hwidth : value maximum - value minimum ≤ bound := by
    calc
      value maximum - value minimum ≤
          |value maximum - value minimum| := le_abs_self _
      _ ≤ bound := hoscillation maximum minimum
  have hwidthNonneg : 0 ≤ value maximum - value minimum := by
    exact sub_nonneg.mpr (hbounds minimum).2
  have hboundNonneg : 0 ≤ bound := hwidthNonneg.trans hwidth
  have hsubgaussian :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (X := value) (a := value minimum) (b := value maximum)
      (μ := law.toMeasure) (measurable_of_finite value).aemeasurable
      (Filter.Eventually.of_forall hbounds)
  have hmgf := hsubgaussian.mgf_le tilt
  rw [pmfExp_eq_integral_toMeasure law value]
  rw [ProbabilityTheory.mgf, PMF.integral_eq_sum] at hmgf
  calc
    pmfExp law
        (fun outcome => Real.exp
          (tilt * (value outcome - ∫ outcome, value outcome ∂law.toMeasure))) ≤
      Real.exp
        ((‖value maximum - value minimum‖₊ / 2 : ℝ) ^ 2 *
          tilt ^ 2 / 2) := by
            simpa [pmfExp, smul_eq_mul] using hmgf
    _ ≤ Real.exp (bound ^ 2 * tilt ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr
      have hnnnorm : (‖value maximum - value minimum‖₊ : ℝ) =
          value maximum - value minimum := by
        simp [hwidthNonneg]
      rw [hnnnorm]
      have hwidthSq :
          (value maximum - value minimum) ^ 2 ≤ bound ^ 2 :=
        (sq_le_sq₀ hwidthNonneg hboundNonneg).2 hwidth
      nlinarith [mul_le_mul_of_nonneg_right hwidthSq (sq_nonneg tilt)]

/-- Average over the newly adjoined coordinate of an `Option`-indexed sample. -/
noncomputable def optionCoordinateConditionalMean
    {Index Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (value : (Option Index → Outcome) → ℝ)
    (oldSample : Index → Outcome) : ℝ :=
  pmfExp law (fun newItem => value (extendDraw oldSample newItem))

/--
One conditional-Hoeffding tensorization step.  An exponential-moment bound
for the conditional mean over the old coordinates gains `newBound^2/4` in
sub-Gaussian variance proxy after adjoining one coordinate.
-/
theorem pmfExp_optionProduct_exp_mul_sub_mean_le
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
    (law : PMF Outcome) (value : (Option Index → Outcome) → ℝ)
    (oldProxy newBound tilt : ℝ)
    (hnew : ∀ oldSample first second,
      |value (extendDraw oldSample first) -
          value (extendDraw oldSample second)| ≤ newBound)
    (hold :
      pmfExp (pmfProduct Index Outcome law)
          (fun oldSample => Real.exp
            (tilt *
              (optionCoordinateConditionalMean law value oldSample -
                pmfExp (pmfProduct Index Outcome law)
                  (optionCoordinateConditionalMean law value)))) ≤
        Real.exp (oldProxy * tilt ^ 2 / 2)) :
    pmfExp (pmfProduct (Option Index) Outcome law)
        (fun sample => Real.exp
          (tilt *
            (value sample -
              pmfExp (pmfProduct (Option Index) Outcome law) value))) ≤
      Real.exp ((oldProxy + newBound ^ 2 / 4) * tilt ^ 2 / 2) := by
  let oldLaw := pmfProduct Index Outcome law
  let optionLaw := pmfProduct (Option Index) Outcome law
  let conditionalMean := optionCoordinateConditionalMean law value
  have hmean : pmfExp optionLaw value = pmfExp oldLaw conditionalMean := by
    dsimp only [optionLaw, oldLaw, conditionalMean,
      optionCoordinateConditionalMean]
    rw [pmfExp_pmfProduct_option_eq_pairExp]
    rfl
  have hconditional : ∀ oldSample,
      pmfExp law
          (fun newItem => Real.exp
            (tilt *
              (value (extendDraw oldSample newItem) -
                conditionalMean oldSample))) ≤
        Real.exp (newBound ^ 2 * tilt ^ 2 / 8) := by
    intro oldSample
    exact pmfExp_exp_mul_sub_mean_le_of_pairwise_abs_sub_le
      law (fun newItem => value (extendDraw oldSample newItem))
      newBound tilt (hnew oldSample)
  rw [hmean]
  rw [pmfExp_pmfProduct_option_eq_pairExp]
  unfold pmfPairExp
  calc
    pmfExp oldLaw
        (fun oldSample => pmfExp law
          (fun newItem => Real.exp
            (tilt *
              (value (extendDraw oldSample newItem) -
                pmfExp oldLaw conditionalMean)))) =
      pmfExp oldLaw
        (fun oldSample =>
          Real.exp
              (tilt *
                (conditionalMean oldSample - pmfExp oldLaw conditionalMean)) *
            pmfExp law
              (fun newItem => Real.exp
                (tilt *
                  (value (extendDraw oldSample newItem) -
                    conditionalMean oldSample)))) := by
          apply pmfExp_congr
          intro oldSample
          rw [← pmfExp_const_mul]
          apply pmfExp_congr
          intro newItem
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ pmfExp oldLaw
        (fun oldSample =>
          Real.exp
              (tilt *
                (conditionalMean oldSample - pmfExp oldLaw conditionalMean)) *
            Real.exp (newBound ^ 2 * tilt ^ 2 / 8)) := by
          apply pmfExp_le_pmfExp_of_forall_le
          intro oldSample
          exact mul_le_mul_of_nonneg_left
            (hconditional oldSample) (Real.exp_nonneg _)
    _ = pmfExp oldLaw
          (fun oldSample => Real.exp
            (tilt *
              (conditionalMean oldSample - pmfExp oldLaw conditionalMean))) *
        Real.exp (newBound ^ 2 * tilt ^ 2 / 8) := by
          rw [pmfExp_mul_const]
    _ ≤ Real.exp (oldProxy * tilt ^ 2 / 2) *
        Real.exp (newBound ^ 2 * tilt ^ 2 / 8) := by
          exact mul_le_mul_of_nonneg_right hold (Real.exp_nonneg _)
    _ = Real.exp ((oldProxy + newBound ^ 2 / 4) * tilt ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Reindexing an `Option` extension gives the usual `Fin.snoc` sample. -/
theorem extendDraw_reindex_optionFinEquivFinSucc
    {Outcome : Type*} (n : ℕ) (oldSample : Fin n → Outcome) (newItem : Outcome) :
    (fun index : Fin (n + 1) =>
      extendDraw oldSample newItem ((optionFinEquivFinSucc n).symm index)) =
      Fin.snoc oldSample newItem := by
  funext index
  refine Fin.lastCases ?_ (fun oldIndex => ?_) index
  · simp [optionFinEquivFinSucc, extendDraw]
  · simp [optionFinEquivFinSucc, extendDraw]

/-- Replacing an old coordinate commutes with adjoining a final coordinate. -/
theorem snoc_update_castSucc
    {Outcome : Type*} (n : ℕ) (oldSample : Fin n → Outcome)
    (index : Fin n) (replacement newItem : Outcome) :
    Fin.snoc (Function.update oldSample index replacement) newItem =
      Function.update
        (Fin.snoc oldSample newItem : Fin (n + 1) → Outcome)
        index.castSucc replacement := by
  funext coordinate
  by_cases hlt : coordinate.val < n
  · let oldCoordinate : Fin n := coordinate.castLT hlt
    by_cases hold : oldCoordinate = index
    · have hcoordinate : coordinate = index.castSucc := by
        apply Fin.ext
        simpa [oldCoordinate] using congrArg Fin.val hold
      subst coordinate
      simp [Fin.snoc, Function.update]
    · have hcoordinate : coordinate ≠ index.castSucc := by
        intro hcoordinate
        apply hold
        apply Fin.ext
        simpa [oldCoordinate] using congrArg Fin.val hcoordinate
      rw [show
          (Fin.snoc (Function.update oldSample index replacement) newItem :
            Fin (n + 1) → Outcome) coordinate =
          Function.update oldSample index replacement oldCoordinate by
        simp [Fin.snoc, hlt, oldCoordinate]]
      rw [Function.update_of_ne hold, Function.update_of_ne hcoordinate]
      simp [Fin.snoc, hlt, oldCoordinate]
  · have hcoordinate : coordinate ≠ index.castSucc := by
      intro hcoordinate
      apply hlt
      rw [congrArg Fin.val hcoordinate]
      exact index.isLt
    simp [Fin.snoc, Function.update, hlt, hcoordinate]

/--
Finite-PMF bounded-differences exponential-moment inequality on an iid
length-`n` sample.  The sub-Gaussian proxy is `∑_i bound_i² / 4`, yielding
McDiarmid's exponent `-2 ε² / ∑_i bound_i²` after Chernoff optimization.
-/
theorem pmfExp_finProduct_exp_mul_sub_mean_le_of_boundedDifferences
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
    (law : PMF Outcome) (n : ℕ)
    (value : (Fin n → Outcome) → ℝ) (bound : Fin n → ℝ)
    (hbounded : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤
        bound index)
    (tilt : ℝ) :
    pmfExp (pmfProduct (Fin n) Outcome law)
        (fun sample => Real.exp
          (tilt *
            (value sample -
              pmfExp (pmfProduct (Fin n) Outcome law) value))) ≤
      Real.exp
        ((∑ index : Fin n, bound index ^ 2 / 4) * tilt ^ 2 / 2) := by
  induction n with
  | zero =>
      let emptySample : Fin 0 → Outcome := fun index => Fin.elim0 index
      have hconstant : ∀ sample : Fin 0 → Outcome,
          value sample = value emptySample := by
        intro sample
        congr
        funext index
        exact Fin.elim0 index
      have hmean :
          pmfExp (pmfProduct (Fin 0) Outcome law) value =
            value emptySample := by
        rw [pmfExp_congr (pmfProduct (Fin 0) Outcome law) hconstant]
        exact pmfExp_const _ _
      rw [hmean]
      have hcentered : ∀ sample : Fin 0 → Outcome,
          Real.exp (tilt * (value sample - value emptySample)) = 1 := by
        intro sample
        rw [hconstant sample]
        simp
      rw [pmfExp_congr (pmfProduct (Fin 0) Outcome law) hcentered]
      simp
  | succ m inductionHypothesis =>
      let equivalence := optionFinEquivFinSucc m
      let optionValue : (Option (Fin m) → Outcome) → ℝ := fun sample =>
        value (fun index => sample (equivalence.symm index))
      let oldBound : Fin m → ℝ := fun index => bound index.castSucc
      let newBound : ℝ := bound (Fin.last m)
      have hnew : ∀ oldSample first second,
          |optionValue (extendDraw oldSample first) -
              optionValue (extendDraw oldSample second)| ≤ newBound := by
        intro oldSample first second
        have hfirst :
            (fun index : Fin (m + 1) =>
              extendDraw oldSample first (equivalence.symm index)) =
                Fin.snoc oldSample first := by
          exact extendDraw_reindex_optionFinEquivFinSucc m oldSample first
        have hsecond :
            (fun index : Fin (m + 1) =>
              extendDraw oldSample second (equivalence.symm index)) =
                Fin.snoc oldSample second := by
          exact extendDraw_reindex_optionFinEquivFinSucc m oldSample second
        have hupdate :
            Function.update
                (Fin.snoc oldSample first : Fin (m + 1) → Outcome)
                (Fin.last m) second =
              (Fin.snoc oldSample second : Fin (m + 1) → Outcome) := by
          funext index
          refine Fin.lastCases ?_ (fun oldIndex => ?_) index <;> simp
        simpa [optionValue, newBound, hfirst, hsecond, hupdate] using
          hbounded (Fin.last m) (Fin.snoc oldSample first) second
      have hconditionalBounded : ∀ index oldSample replacement,
          |optionCoordinateConditionalMean law optionValue oldSample -
              optionCoordinateConditionalMean law optionValue
                (Function.update oldSample index replacement)| ≤
            oldBound index := by
        intro index oldSample replacement
        unfold optionCoordinateConditionalMean
        apply AppliedModelingLib.FiniteCoupling.abs_pmfExp_sub_le_of_forall_abs_sub_le
        intro newItem
        have horiginal :
            (fun coordinate : Fin (m + 1) =>
              extendDraw oldSample newItem (equivalence.symm coordinate)) =
                Fin.snoc oldSample newItem := by
          exact extendDraw_reindex_optionFinEquivFinSucc m oldSample newItem
        have hupdated :
            (fun coordinate : Fin (m + 1) =>
              extendDraw (Function.update oldSample index replacement) newItem
                (equivalence.symm coordinate)) =
              Fin.snoc (Function.update oldSample index replacement) newItem := by
          exact extendDraw_reindex_optionFinEquivFinSucc m
            (Function.update oldSample index replacement) newItem
        have hsnocUpdate :=
          snoc_update_castSucc m oldSample index replacement newItem
        simpa [optionValue, oldBound, horiginal, hupdated, hsnocUpdate] using
          hbounded index.castSucc (Fin.snoc oldSample newItem) replacement
      have hold := inductionHypothesis
        (optionCoordinateConditionalMean law optionValue) oldBound
        hconditionalBounded
      have hoption := pmfExp_optionProduct_exp_mul_sub_mean_le
        law optionValue
        (∑ index : Fin m, oldBound index ^ 2 / 4) newBound tilt
        hnew hold
      have hmeanReindex :
          pmfExp (pmfProduct (Option (Fin m)) Outcome law) optionValue =
            pmfExp (pmfProduct (Fin (m + 1)) Outcome law) value := by
        exact pmfExp_pmfProduct_equiv equivalence law value
      have hmgfReindex :
          pmfExp (pmfProduct (Option (Fin m)) Outcome law)
              (fun sample => Real.exp
                (tilt *
                  (optionValue sample -
                    pmfExp (pmfProduct (Fin (m + 1)) Outcome law) value))) =
            pmfExp (pmfProduct (Fin (m + 1)) Outcome law)
              (fun sample => Real.exp
                (tilt *
                  (value sample -
                    pmfExp (pmfProduct (Fin (m + 1)) Outcome law) value))) := by
        simpa [optionValue] using
          (pmfExp_pmfProduct_equiv equivalence law
            (fun sample => Real.exp
              (tilt *
                (value sample -
                  pmfExp (pmfProduct (Fin (m + 1)) Outcome law) value))))
      rw [hmeanReindex] at hoption
      rw [hmgfReindex] at hoption
      calc
        pmfExp (pmfProduct (Fin (m + 1)) Outcome law)
            (fun sample => Real.exp
              (tilt *
                (value sample -
                  pmfExp (pmfProduct (Fin (m + 1)) Outcome law) value))) ≤
          Real.exp
            (((∑ index : Fin m, oldBound index ^ 2 / 4) +
              newBound ^ 2 / 4) * tilt ^ 2 / 2) := hoption
        _ = Real.exp
            ((∑ index : Fin (m + 1), bound index ^ 2 / 4) *
              tilt ^ 2 / 2) := by
          congr 2
          rw [Fin.sum_univ_castSucc]

/--
Finite-PMF McDiarmid upper tail.  The strict positivity assumption isolates
the nondegenerate coordinate-sensitivity case; a separate zero-sensitivity
corollary can discharge constant statistics when needed.
-/
theorem pmfProb_finProduct_sub_mean_ge_le_exp_of_boundedDifferences
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
    (law : PMF Outcome) (n : ℕ)
    (value : (Fin n → Outcome) → ℝ) (bound : Fin n → ℝ)
    (hbounded : ∀ index sample replacement,
      |value sample - value (Function.update sample index replacement)| ≤
        bound index)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hsumPositive : 0 < ∑ index : Fin n, bound index ^ 2) :
    pmfProb (pmfProduct (Fin n) Outcome law)
        (fun sample => epsilon ≤
          value sample - pmfExp (pmfProduct (Fin n) Outcome law) value) ≤
      Real.exp
        (-2 * epsilon ^ 2 / (∑ index : Fin n, bound index ^ 2)) := by
  let sampleLaw := pmfProduct (Fin n) Outcome law
  let totalSensitivity : ℝ := ∑ index : Fin n, bound index ^ 2
  let tilt : ℝ := 4 * epsilon / totalSensitivity
  let centered : (Fin n → Outcome) → ℝ := fun sample =>
    value sample - pmfExp sampleLaw value
  have htilt : 0 ≤ tilt := by
    exact div_nonneg (mul_nonneg (by norm_num) hepsilon) hsumPositive.le
  have hmgf :=
    pmfExp_finProduct_exp_mul_sub_mean_le_of_boundedDifferences
      law n value bound hbounded tilt
  have hsumQuarter :
      (∑ index : Fin n, bound index ^ 2 / 4) = totalSensitivity / 4 := by
    dsimp [totalSensitivity]
    rw [Finset.sum_div]
  rw [hsumQuarter] at hmgf
  letI : MeasurableSpace (Fin n → Outcome) := ⊤
  rw [pmfProb_eq_toMeasure_real]
  have hchernoff := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := centered) (μ := sampleLaw.toMeasure) epsilon htilt
    (Integrable.of_finite : Integrable
      (fun sample => Real.exp (tilt * centered sample)) sampleLaw.toMeasure)
  calc
    sampleLaw.toMeasure.real {sample | epsilon ≤ centered sample} ≤
      Real.exp (-tilt * epsilon) *
        ProbabilityTheory.mgf centered sampleLaw.toMeasure tilt := hchernoff
    _ = Real.exp (-tilt * epsilon) *
        pmfExp sampleLaw
          (fun sample => Real.exp (tilt * centered sample)) := by
      rw [ProbabilityTheory.mgf, ← pmfExp_eq_integral_toMeasure]
    _ ≤ Real.exp (-tilt * epsilon) *
        Real.exp ((totalSensitivity / 4) * tilt ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp
        (-2 * epsilon ^ 2 / (∑ index : Fin n, bound index ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [tilt, totalSensitivity]
      field_simp [hsumPositive.ne']
      ring

end BoundedDifferences
end Probability
end AppliedModelingLib

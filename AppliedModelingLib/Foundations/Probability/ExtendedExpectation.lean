import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory
open scoped ENNReal

namespace AppliedModelingLib

/-!
# Upper extended expectations

`upperExpectation` records an extended-value convention appropriate for
maximization over probability laws.  It is the difference of the lower
integrals of the positive and negative parts, except that an infinite
positive part is assigned `⊤`, including the indeterminate `∞ - ∞` case.
Thus a law whose positive and negative reward parts are both nonintegrable
cannot artificially lower a supremum merely because its Bochner integral is
undefined.

This is the convention used for the robust primal value in Blanchet and
Murthy, *Quantifying Distributional Model Risk via Optimal Transport*,
Section 2 (arXiv:1604.01446).  The definition and proofs below are local;
they use Mathlib's Apache-2.0 Lebesgue and Bochner integration APIs and do
not adapt external Lean proof text.
-/

/--
The extended expected value of a real reward for a maximization problem.

If the positive part has infinite lower integral, the value is `⊤`.  This
includes the otherwise indeterminate `∞ - ∞` case.  If only the negative part
has infinite lower integral, the value is `⊥`.
-/
noncomputable def upperExpectation {α : Type*} [MeasurableSpace α]
    (reward : α → ℝ) (μ : Measure α) : EReal :=
  if ∫⁻ x, ENNReal.ofReal (reward x) ∂μ = ∞ then ⊤
  else (↑(∫⁻ x, ENNReal.ofReal (reward x) ∂μ) : EReal) -
    ↑(∫⁻ x, ENNReal.ofReal (-reward x) ∂μ)

/-- An infinite positive reward part gives infinite upper expectation. -/
theorem upperExpectation_eq_top_of_lintegral_ofReal_eq_top
    {α : Type*} [MeasurableSpace α] (reward : α → ℝ) (μ : Measure α)
    (hpositive : ∫⁻ x, ENNReal.ofReal (reward x) ∂μ = ∞) :
    upperExpectation reward μ = ⊤ := by
  simp [upperExpectation, hpositive]

/--
When the positive reward part is finite, upper expectation is the literal
extended-real difference of the positive and negative lower integrals.
-/
theorem upperExpectation_eq_lintegral_sub
    {α : Type*} [MeasurableSpace α] (reward : α → ℝ) (μ : Measure α)
    (hpositive : ∫⁻ x, ENNReal.ofReal (reward x) ∂μ ≠ ∞) :
    upperExpectation reward μ =
      (↑(∫⁻ x, ENNReal.ofReal (reward x) ∂μ) : EReal) -
        ↑(∫⁻ x, ENNReal.ofReal (-reward x) ∂μ) := by
  simp [upperExpectation, hpositive]

/--
On ordinary integrable rewards, `upperExpectation` is exactly the Bochner
integral, embedded into the extended reals.
-/
theorem upperExpectation_eq_coe_integral_of_integrable
    {α : Type*} [MeasurableSpace α] (reward : α → ℝ) (μ : Measure α)
    (hintegrable : Integrable reward μ) :
    upperExpectation reward μ = ((∫ x, reward x ∂μ : ℝ) : EReal) := by
  have hpositive : (∫⁻ x, ENNReal.ofReal (reward x) ∂μ) ≠ ∞ :=
    hintegrable.lintegral_lt_top.ne
  have hnegative : (∫⁻ x, ENNReal.ofReal (-reward x) ∂μ) ≠ ∞ :=
    hintegrable.neg.lintegral_lt_top.ne
  rw [upperExpectation_eq_lintegral_sub reward μ hpositive]
  rw [← EReal.coe_ennreal_toReal hpositive,
    ← EReal.coe_ennreal_toReal hnegative, ← EReal.coe_sub]
  rw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hintegrable]

/--
At a Dirac law, upper expectation recovers the realized reward exactly.

This is the basic bridge from pointwise maximization to an unrestricted
supremum over probability laws.  Measurability is sufficient; no integrability
condition is imposed because a Dirac law has finite positive and negative
reward parts.
-/
theorem upperExpectation_dirac
    {α : Type*} [MeasurableSpace α] (reward : α → ℝ)
    (hreward : Measurable reward) (point : α) :
    upperExpectation reward (Measure.dirac point) = (reward point : EReal) := by
  unfold upperExpectation
  have hpositive : (∫⁻ x, ENNReal.ofReal (reward x) ∂Measure.dirac point) =
      ENNReal.ofReal (reward point) := by
    simpa only [Function.comp_apply] using
      (lintegral_dirac' point (ENNReal.measurable_ofReal.comp hreward))
  have hnegative : (∫⁻ x, ENNReal.ofReal (-reward x) ∂Measure.dirac point) =
      ENNReal.ofReal (-reward point) := by
    simpa only [Function.comp_apply] using
      (lintegral_dirac' point (ENNReal.measurable_ofReal.comp hreward.neg))
  rw [hpositive, hnegative]
  simp
  rw [← EReal.coe_sub]
  exact congrArg (fun value : ℝ => (value : EReal))
    (max_zero_sub_max_neg_zero_eq_self (reward point))

end AppliedModelingLib

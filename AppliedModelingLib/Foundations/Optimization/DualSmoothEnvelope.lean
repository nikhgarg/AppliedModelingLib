import AppliedModelingLib.Foundations.Optimization.DualStrongConcaveArgmax
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Smooth pointwise envelopes in real normed spaces

This module provides the Fréchet-derivative analogue of `SmoothEnvelope`.
Unlike the Hilbert-space API, derivative values remain continuous linear maps
to `ℝ`, so the results apply to statements formulated with an arbitrary norm
and its dual norm.

All uses of duality are through Mathlib's operator norm and
[`ContinuousLinearMap.le_opNorm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/NormedSpace.html#ContinuousLinearMap.le_opNorm),
and the line-calculus step uses
[`HasFDerivAt.comp_hasDerivAt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Comp.html#HasFDerivAt.comp_hasDerivAt),
from the repository-pinned Apache-2.0 Mathlib
[`NormedSpace`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Normed/Operator/NormedSpace.lean)
and
[`Deriv/Comp`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/Deriv/Comp.lean)
modules.  No external proof or code is copied or ported.
-/

namespace AppliedModelingLib
namespace Optimization

open Asymptotics

variable {Parameter : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- A two-sided quadratic first-order bound stated with a Fréchet derivative. -/
def HasQuadraticFirstOrderEnvelopeBoundDual
    (value : Parameter → ℝ) (derivative : Parameter →L[ℝ] ℝ) (base : Parameter) : Prop :=
  ∃ curvature : ℝ, 0 ≤ curvature ∧ ∀ candidate,
    value base + derivative (candidate - base) - curvature * ‖candidate - base‖ ^ 2 ≤
      value candidate ∧
    value candidate ≤
      value base + derivative (candidate - base) + curvature * ‖candidate - base‖ ^ 2

/-- A two-sided quadratic first-order bound proves Fréchet differentiability. -/
theorem hasFDerivAt_of_quadraticFirstOrderEnvelopeBoundDual
    (value : Parameter → ℝ) (derivative : Parameter →L[ℝ] ℝ) (base : Parameter)
    (hbound : HasQuadraticFirstOrderEnvelopeBoundDual value derivative base) :
    HasFDerivAt value derivative base := by
  rw [hasFDerivAt_iff_isLittleO]
  rcases hbound with ⟨curvature, hcurvature, hbound⟩
  refine (isBigO_iff.2 ⟨curvature, Filter.Eventually.of_forall (fun candidate => ?_)⟩).trans_isLittleO
    (isLittleO_pow_sub_sub base (m := 2) (by norm_num))
  have htwoSided := hbound candidate
  let remainder : ℝ :=
    value candidate - value base - derivative (candidate - base)
  have hlower : -(curvature * ‖candidate - base‖ ^ 2) ≤ remainder := by
    dsimp [remainder]
    linarith [htwoSided.1]
  have hupper : remainder ≤ curvature * ‖candidate - base‖ ^ 2 := by
    dsimp [remainder]
    linarith [htwoSided.2]
  have habs : |remainder| ≤ curvature * ‖candidate - base‖ ^ 2 :=
    abs_le.2 ⟨hlower, hupper⟩
  simpa only [remainder, Real.norm_eq_abs, norm_norm,
    abs_of_nonneg (sq_nonneg ‖candidate - base‖)] using habs

/-- A parameter derivative is Lipschitz in the parameter coordinate, uniformly in state. -/
def ParameterDerivativeParameterLipschitz {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ) (constant : ℝ) : Prop :=
  ∀ state first second,
    ‖parameterDerivative first state - parameterDerivative second state‖ ≤
      constant * ‖first - second‖

/-- Parameter-derivative smoothness restricted to a feasible state domain. -/
def ParameterDerivativeParameterLipschitzOn {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (domain : Set State)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ) (constant : ℝ) : Prop :=
  ∀ state, state ∈ domain → ∀ first second,
    ‖parameterDerivative first state - parameterDerivative second state‖ ≤
      constant * ‖first - second‖

/-- A parameter derivative is Lipschitz in the state coordinate, uniformly in parameter. -/
def ParameterDerivativeStateLipschitz {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ) (constant : ℝ) : Prop :=
  ∀ parameter first second,
    ‖parameterDerivative parameter first - parameterDerivative parameter second‖ ≤
      constant * ‖first - second‖

/-- Parameter-derivative/state-coordinate smoothness on a feasible state domain. -/
def ParameterDerivativeStateLipschitzOn {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (domain : Set State)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ) (constant : ℝ) : Prop :=
  ∀ parameter first, first ∈ domain → ∀ second, second ∈ domain →
    ‖parameterDerivative parameter first - parameterDerivative parameter second‖ ≤
      constant * ‖first - second‖

/-- A state derivative is Lipschitz in the state coordinate, uniformly in parameter. -/
def StateDerivativeStateLipschitz {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ) (constant : ℝ) : Prop :=
  ∀ parameter first second,
    ‖stateDerivative parameter first - stateDerivative parameter second‖ ≤
      constant * ‖first - second‖

/-- A selected state is Lipschitz as a function of the parameter. -/
def StateSelectionLipschitzDual {State : Type*} [NormedAddCommGroup State]
    (select : Parameter → State) (constant : ℝ) : Prop :=
  ∀ first second, ‖select first - select second‖ ≤ constant * ‖first - second‖

/-- A Fréchet-differentiable scalar function lies below its quadratic smoothness model. -/
theorem smooth_upper_model_bound_dual
    (f : Parameter → ℝ) (derivative : Parameter → Parameter →L[ℝ] ℝ) (smoothness : ℝ)
    (hderivative : ∀ first second,
      ‖derivative first - derivative second‖ ≤ smoothness * ‖first - second‖)
    (hderivativeAt : ∀ parameter, HasFDerivAt f (derivative parameter) parameter)
    (first second : Parameter) :
    f second ≤ f first + derivative first (second - first) +
      smoothness / 2 * ‖second - first‖ ^ 2 := by
  let line : ℝ → Parameter := AffineMap.lineMap first second
  have hline : ∀ t : ℝ,
      HasDerivAt (f ∘ line) (derivative (line t) (second - first)) t := by
    intro t
    simpa [line] using
      HasFDerivAt.comp_hasDerivAt t (hderivativeAt (line t))
        (AffineMap.hasDerivAt_lineMap (a := first) (b := second) (x := t))
  let displacement := second - first
  let q : ℝ → ℝ := fun t =>
    f (line t) - t * derivative first displacement -
      (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2
  have hq : ∀ t : ℝ,
      HasDerivAt q
        (derivative (line t) displacement - derivative first displacement -
          smoothness * t * ‖displacement‖ ^ 2) t := by
    intro t
    have hlinear : HasDerivAt (fun t : ℝ => t * derivative first displacement)
        (derivative first displacement) t := by
      simpa using (hasDerivAt_id t).mul_const (derivative first displacement)
    have hquadratic : HasDerivAt
        (fun t : ℝ => (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2)
        (smoothness * t * ‖displacement‖ ^ 2) t := by
      have hpow := ((hasDerivAt_id t).pow 2).const_mul
        ((smoothness / 2) * ‖displacement‖ ^ 2)
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hpow
      convert hpow using 1
      · ext y
        change smoothness / 2 * y ^ 2 * ‖displacement‖ ^ 2 =
          smoothness / 2 * ‖displacement‖ ^ 2 * y ^ 2
        ring
      · ring
    simpa only [q, Function.comp_apply, displacement] using
      ((hline t).sub hlinear).sub hquadratic
  have hline_sub : ∀ t : ℝ, line t - first = t • displacement := by
    intro t
    simp only [line, displacement, AffineMap.lineMap_apply_module']
    abel
  have hq_deriv_nonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      derivative (line t) displacement - derivative first displacement -
        smoothness * t * ‖displacement‖ ^ 2 ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have ht_nonneg : 0 ≤ t := ht.1.le
    have hderivative_norm :
        ‖derivative (line t) - derivative first‖ ≤
          smoothness * (t * ‖displacement‖) := by
      calc
        ‖derivative (line t) - derivative first‖ ≤ smoothness * ‖line t - first‖ :=
          hderivative (line t) first
        _ = smoothness * (t * ‖displacement‖) := by
          rw [hline_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    have happly :
        (derivative (line t) - derivative first) displacement ≤
          smoothness * t * ‖displacement‖ ^ 2 := by
      calc
        (derivative (line t) - derivative first) displacement ≤
            |(derivative (line t) - derivative first) displacement| := le_abs_self _
        _ = ‖(derivative (line t) - derivative first) displacement‖ := by
          simp only [Real.norm_eq_abs]
        _ ≤ ‖derivative (line t) - derivative first‖ * ‖displacement‖ :=
          (derivative (line t) - derivative first).le_opNorm displacement
        _ ≤ (smoothness * (t * ‖displacement‖)) * ‖displacement‖ := by
          exact mul_le_mul_of_nonneg_right hderivative_norm (norm_nonneg _)
        _ = smoothness * t * ‖displacement‖ ^ 2 := by ring
    have happly' :
        derivative (line t) displacement - derivative first displacement ≤
          smoothness * t * ‖displacement‖ ^ 2 := by
      simpa only [ContinuousLinearMap.sub_apply] using happly
    linarith
  have hq_antitone : AntitoneOn q (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
      (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).hasDerivWithinAt) hq_deriv_nonpos
  have hq01 := hq_antitone (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [q, line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    one_mul, zero_mul, one_pow, sub_zero] at hq01
  linarith

/--
An attained pointwise envelope has the selected Fréchet derivative whenever
the fixed-state derivatives are smooth and the selected state is Lipschitz.
The maximization input is only the comparison of pairs of selected states,
which is the exact fragment needed by the envelope calculation.  The explicit
split between parameter and state derivatives keeps the theorem valid in
arbitrary real normed spaces.
-/
theorem pointwiseStateEnvelope_quadraticBound_dual
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (domain : Set State)
    (objective : Parameter → State → ℝ)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ)
    (select : Parameter → State)
    {parameterSmoothness stateCross selectionConstant : ℝ}
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hstateCross : 0 ≤ stateCross)
    (hselectionConstant : 0 ≤ selectionConstant)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hselectionDominant : PointwiseStateSelectionDominant objective select)
    (hderivativeAt : ∀ parameter state, state ∈ domain →
      HasFDerivAt (fun other => objective other state) (parameterDerivative parameter state)
        parameter)
    (hparameterDerivative : ParameterDerivativeParameterLipschitzOn domain
      parameterDerivative parameterSmoothness)
    (hstateDerivative : ParameterDerivativeStateLipschitzOn domain
      parameterDerivative stateCross)
    (hselection : StateSelectionLipschitzDual select selectionConstant)
    (base : Parameter) :
    HasQuadraticFirstOrderEnvelopeBoundDual
      (fun parameter => objective parameter (select parameter))
      (parameterDerivative base (select base)) base := by
  refine ⟨3 * parameterSmoothness / 2 + stateCross * selectionConstant, ?_, ?_⟩
  · positivity
  intro candidate
  have hfixedBaseReverse := smooth_upper_model_bound_dual
    (fun parameter => objective parameter (select base))
    (fun parameter => parameterDerivative parameter (select base)) parameterSmoothness
    (fun first second => hparameterDerivative (select base) (hselect base) first second)
    (fun parameter => hderivativeAt parameter (select base) (hselect base)) candidate base
  have hfixedBaseLower :
      objective base (select base) +
          parameterDerivative base (select base) (candidate - base) -
            3 * parameterSmoothness / 2 * ‖candidate - base‖ ^ 2 ≤
        objective candidate (select base) := by
    have hfixedBaseReverse' :
        objective base (select base) ≤
          objective candidate (select base) -
              parameterDerivative candidate (select base) (candidate - base) +
            parameterSmoothness / 2 * ‖candidate - base‖ ^ 2 := by
      have hreverseDisplacement : base - candidate = -(candidate - base) := by
        abel
      rw [hreverseDisplacement, map_neg, norm_neg] at hfixedBaseReverse
      linarith [hfixedBaseReverse]
    have hderivativeDifference :
      ‖parameterDerivative candidate (select base) - parameterDerivative base (select base)‖ ≤
          parameterSmoothness * ‖candidate - base‖ :=
      hparameterDerivative (select base) (hselect base) candidate base
    have hnegativeApply :
        -(parameterDerivative candidate (select base) - parameterDerivative base (select base))
            (candidate - base) ≤
          ‖parameterDerivative candidate (select base) - parameterDerivative base (select base)‖ *
            ‖candidate - base‖ := by
      calc
        -(parameterDerivative candidate (select base) - parameterDerivative base (select base))
            (candidate - base) =
            (-(parameterDerivative candidate (select base) - parameterDerivative base (select base)))
              (candidate - base) := by simp
        _ ≤ |(-(parameterDerivative candidate (select base) - parameterDerivative base (select base)))
              (candidate - base)| := le_abs_self _
        _ = ‖(-(parameterDerivative candidate (select base) - parameterDerivative base (select base)))
              (candidate - base)‖ := by simp only [Real.norm_eq_abs]
        _ ≤ ‖-(parameterDerivative candidate (select base) - parameterDerivative base (select base))‖ *
              ‖candidate - base‖ :=
          (-(parameterDerivative candidate (select base) - parameterDerivative base (select base))).le_opNorm
            (candidate - base)
        _ = ‖parameterDerivative candidate (select base) - parameterDerivative base (select base)‖ *
              ‖candidate - base‖ := by rw [norm_neg]
    have hderivativeProduct :
        ‖parameterDerivative candidate (select base) - parameterDerivative base (select base)‖ *
            ‖candidate - base‖ ≤
          (parameterSmoothness * ‖candidate - base‖) * ‖candidate - base‖ :=
      mul_le_mul_of_nonneg_right hderivativeDifference (norm_nonneg _)
    have hderivativeLower :
        -(parameterSmoothness * ‖candidate - base‖ ^ 2) ≤
          (parameterDerivative candidate (select base) - parameterDerivative base (select base))
            (candidate - base) := by
      nlinarith [hnegativeApply, hderivativeProduct]
    have hderivativeSplitBase :
        parameterDerivative candidate (select base) (candidate - base) =
          parameterDerivative base (select base) (candidate - base) +
            (parameterDerivative candidate (select base) - parameterDerivative base (select base))
              (candidate - base) := by
      rw [ContinuousLinearMap.sub_apply]
      ring
    rw [hderivativeSplitBase] at hfixedBaseReverse'
    nlinarith [hfixedBaseReverse', hderivativeLower]
  have hfixedCandidate := smooth_upper_model_bound_dual
    (fun parameter => objective parameter (select candidate))
    (fun parameter => parameterDerivative parameter (select candidate)) parameterSmoothness
    (fun first second => hparameterDerivative (select candidate) (hselect candidate) first second)
    (fun parameter => hderivativeAt parameter (select candidate) (hselect candidate)) base candidate
  have hmaxAtCandidate :
      objective candidate (select base) ≤ objective candidate (select candidate) :=
    hselectionDominant candidate base
  have hmaxAtBase :
      objective base (select candidate) ≤ objective base (select base) :=
    hselectionDominant base candidate
  have hselectionBound :
      ‖select candidate - select base‖ ≤ selectionConstant * ‖candidate - base‖ :=
    hselection candidate base
  have hparameterDifference :
      ‖parameterDerivative base (select candidate) - parameterDerivative base (select base)‖ ≤
        stateCross * ‖select candidate - select base‖ :=
    hstateDerivative base (select candidate) (hselect candidate) (select base) (hselect base)
  have happlyDifference :
      (parameterDerivative base (select candidate) - parameterDerivative base (select base))
          (candidate - base) ≤
        stateCross * selectionConstant * ‖candidate - base‖ ^ 2 := by
    calc
      (parameterDerivative base (select candidate) - parameterDerivative base (select base))
          (candidate - base) ≤
          |(parameterDerivative base (select candidate) - parameterDerivative base (select base))
            (candidate - base)| := le_abs_self _
      _ = ‖(parameterDerivative base (select candidate) - parameterDerivative base (select base))
            (candidate - base)‖ := by simp only [Real.norm_eq_abs]
      _ ≤ ‖parameterDerivative base (select candidate) - parameterDerivative base (select base)‖ *
            ‖candidate - base‖ :=
        (parameterDerivative base (select candidate) - parameterDerivative base (select base)).le_opNorm
          (candidate - base)
      _ ≤ (stateCross * ‖select candidate - select base‖) * ‖candidate - base‖ :=
        mul_le_mul_of_nonneg_right hparameterDifference (norm_nonneg _)
      _ ≤ (stateCross * (selectionConstant * ‖candidate - base‖)) * ‖candidate - base‖ := by
        gcongr
      _ = stateCross * selectionConstant * ‖candidate - base‖ ^ 2 := by ring
  have hderivativeSplit :
      parameterDerivative base (select candidate) (candidate - base) =
        parameterDerivative base (select base) (candidate - base) +
          (parameterDerivative base (select candidate) - parameterDerivative base (select base))
            (candidate - base) := by
    rw [ContinuousLinearMap.sub_apply]
    ring
  constructor
  · have hnonneg : 0 ≤ stateCross * selectionConstant * ‖candidate - base‖ ^ 2 := by
      positivity
    rw [show (fun parameter => objective parameter (select parameter)) base =
      objective base (select base) by rfl]
    rw [show (fun parameter => objective parameter (select parameter)) candidate =
      objective candidate (select candidate) by rfl]
    nlinarith [hfixedBaseLower]
  · rw [show (fun parameter => objective parameter (select parameter)) base =
      objective base (select base) by rfl]
    rw [show (fun parameter => objective parameter (select parameter)) candidate =
      objective candidate (select candidate) by rfl]
    rw [hderivativeSplit] at hfixedCandidate
    nlinarith [hfixedCandidate, hmaxAtBase, happlyDifference]

/-- The selected-derivative formula for a smooth, attained pointwise envelope. -/
theorem pointwiseStateEnvelope_hasFDerivAt_dual
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (domain : Set State)
    (objective : Parameter → State → ℝ)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ)
    (select : Parameter → State)
    {parameterSmoothness stateCross selectionConstant : ℝ}
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hstateCross : 0 ≤ stateCross)
    (hselectionConstant : 0 ≤ selectionConstant)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hselectionDominant : PointwiseStateSelectionDominant objective select)
    (hderivativeAt : ∀ parameter state, state ∈ domain →
      HasFDerivAt (fun other => objective other state) (parameterDerivative parameter state)
        parameter)
    (hparameterDerivative : ParameterDerivativeParameterLipschitzOn domain
      parameterDerivative parameterSmoothness)
    (hstateDerivative : ParameterDerivativeStateLipschitzOn domain
      parameterDerivative stateCross)
    (hselection : StateSelectionLipschitzDual select selectionConstant)
    (base : Parameter) :
    HasFDerivAt (fun parameter => objective parameter (select parameter))
      (parameterDerivative base (select base)) base :=
  hasFDerivAt_of_quadraticFirstOrderEnvelopeBoundDual _ _ _
    (pointwiseStateEnvelope_quadraticBound_dual domain objective parameterDerivative select
      hparameterSmoothness hstateCross hselectionConstant hselect hselectionDominant hderivativeAt hparameterDerivative
      hstateDerivative hselection base)

/-- The selected parameter derivative of a stable pointwise envelope is Lipschitz. -/
theorem pointwiseStateEnvelope_derivative_lipschitz_dual
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (domain : Set State)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ) (select : Parameter → State)
    {parameterSmoothness stateCross selectionConstant : ℝ}
    (hstateCross : 0 ≤ stateCross)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hparameterDerivative : ParameterDerivativeParameterLipschitzOn domain
      parameterDerivative parameterSmoothness)
    (hstateDerivative : ParameterDerivativeStateLipschitzOn domain
      parameterDerivative stateCross)
    (hselection : StateSelectionLipschitzDual select selectionConstant)
    (first second : Parameter) :
    ‖parameterDerivative first (select first) - parameterDerivative second (select second)‖ ≤
      (parameterSmoothness + stateCross * selectionConstant) * ‖first - second‖ := by
  calc
    ‖parameterDerivative first (select first) - parameterDerivative second (select second)‖ ≤
        ‖parameterDerivative first (select first) - parameterDerivative first (select second)‖ +
          ‖parameterDerivative first (select second) - parameterDerivative second (select second)‖ := by
      rw [show parameterDerivative first (select first) - parameterDerivative second (select second) =
          (parameterDerivative first (select first) - parameterDerivative first (select second)) +
            (parameterDerivative first (select second) - parameterDerivative second (select second)) by
          abel]
      exact norm_add_le _ _
    _ ≤ stateCross * ‖select first - select second‖ +
          parameterSmoothness * ‖first - second‖ := by
      gcongr
      · exact hstateDerivative first (select first) (hselect first) (select second) (hselect second)
      · exact hparameterDerivative (select second) (hselect second) first second
    _ ≤ stateCross * (selectionConstant * ‖first - second‖) +
          parameterSmoothness * ‖first - second‖ := by
      gcongr
      exact hselection first second
    _ = (parameterSmoothness + stateCross * selectionConstant) * ‖first - second‖ := by
      ring

/--
The smoothness conclusion for a strongly-concave attained pointwise maximum,
formulated in the continuous dual of an arbitrary real normed parameter space.
The explicit first-order condition is the analytic/domain clarification needed
to apply the source's displayed argmax notation on a general feasible set.
-/
theorem smoothPointwiseStateEnvelope_of_strongConcavity_dual
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (objective : Parameter → State → ℝ)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ) (select : Parameter → State)
    {modulus parameterSmoothness parameterStateCross stateDerivativeCross : ℝ}
    (hmodulus : 0 < modulus)
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hparameterStateCross : 0 ≤ parameterStateCross)
    (hstateDerivativeCross : 0 ≤ stateDerivativeCross)
    (hstrong : StrongConcaveInStateFirstOrderDual objective stateDerivative modulus)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerConditionDual stateDerivative select)
    (hparameterDerivativeAt : ∀ parameter state,
      HasFDerivAt (fun other => objective other state) (parameterDerivative parameter state)
        parameter)
    (hparameterDerivativeParameter :
      ParameterDerivativeParameterLipschitz parameterDerivative parameterSmoothness)
    (hparameterDerivativeState :
      ParameterDerivativeStateLipschitz parameterDerivative parameterStateCross)
    (hstateDerivativeParameter : StateDerivativeCrossLipschitz stateDerivative stateDerivativeCross) :
    (∀ parameter,
      HasFDerivAt (fun other => objective other (select other))
        (parameterDerivative parameter (select parameter)) parameter) ∧
    (∀ first second,
      ‖parameterDerivative first (select first) - parameterDerivative second (select second)‖ ≤
        (parameterSmoothness + parameterStateCross * stateDerivativeCross / modulus) *
          ‖first - second‖) := by
  have hselection : StateSelectionLipschitzDual select (stateDerivativeCross / modulus) := by
    intro first second
    exact pointwiseStateMaximizer_lipschitz_dual objective stateDerivative select hmodulus hstrong hmax
      hfirstOrder hstateDerivativeParameter first second
  have hselectionNonneg : 0 ≤ stateDerivativeCross / modulus :=
    div_nonneg hstateDerivativeCross hmodulus.le
  have hselectionDominant : PointwiseStateSelectionDominant objective select := by
    intro parameter other
    exact hmax parameter (select other)
  constructor
  · intro parameter
    exact pointwiseStateEnvelope_hasFDerivAt_dual Set.univ objective parameterDerivative select
      hparameterSmoothness hparameterStateCross hselectionNonneg (fun _ => Set.mem_univ _)
      hselectionDominant (fun parameter state _ => hparameterDerivativeAt parameter state)
      (fun state _ => hparameterDerivativeParameter state)
      (fun parameter first _ second _ => hparameterDerivativeState parameter first second)
      hselection parameter
  · intro first second
    have hsmooth := pointwiseStateEnvelope_derivative_lipschitz_dual Set.univ parameterDerivative select
      hparameterStateCross (fun _ => Set.mem_univ _)
      (fun state _ => hparameterDerivativeParameter state)
      (fun parameter first _ second _ => hparameterDerivativeState parameter first second)
      hselection first second
    simpa only [mul_div_assoc] using hsmooth

/--
The smooth-envelope conclusion on a convex feasible state domain.  The
selected-state membership, constrained strong-concavity inequality, and
feasible-direction first-order condition are explicit, so no ambient-space
maximization is inferred from a source statement over a proper domain.
-/
theorem smoothPointwiseStateEnvelopeOn_of_strongConcavity_dual
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (domain : Set State)
    (objective : Parameter → State → ℝ)
    (parameterDerivative : Parameter → State → Parameter →L[ℝ] ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ) (select : Parameter → State)
    {modulus parameterSmoothness parameterStateCross stateDerivativeCross : ℝ}
    (hmodulus : 0 < modulus)
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hparameterStateCross : 0 ≤ parameterStateCross)
    (hstateDerivativeCross : 0 ≤ stateDerivativeCross)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hstrong : StrongConcaveInStateFirstOrderDualOn domain objective stateDerivative modulus)
    (hmax : IsPointwiseStateMaximizerOn domain objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerConditionDualOn domain stateDerivative select)
    (hparameterDerivativeAt : ∀ parameter state, state ∈ domain →
      HasFDerivAt (fun other => objective other state) (parameterDerivative parameter state)
        parameter)
    (hparameterDerivativeParameter : ParameterDerivativeParameterLipschitzOn domain
      parameterDerivative parameterSmoothness)
    (hparameterDerivativeState : ParameterDerivativeStateLipschitzOn domain
      parameterDerivative parameterStateCross)
    (hstateDerivativeParameter : StateDerivativeCrossLipschitzOn domain stateDerivative stateDerivativeCross) :
    (∀ parameter,
      HasFDerivAt (fun other => objective other (select other))
        (parameterDerivative parameter (select parameter)) parameter) ∧
    (∀ first second,
      ‖parameterDerivative first (select first) - parameterDerivative second (select second)‖ ≤
        (parameterSmoothness + parameterStateCross * stateDerivativeCross / modulus) *
          ‖first - second‖) := by
  have hselection : StateSelectionLipschitzDual select (stateDerivativeCross / modulus) := by
    intro first second
    exact pointwiseStateMaximizerOn_lipschitz_dual domain objective stateDerivative select hmodulus
      hselect hstrong hmax hfirstOrder hstateDerivativeParameter first second
  have hselectionNonneg : 0 ≤ stateDerivativeCross / modulus :=
    div_nonneg hstateDerivativeCross hmodulus.le
  have hselectionDominant : PointwiseStateSelectionDominant objective select :=
    hmax.selectionDominant domain objective select hselect
  constructor
  · intro parameter
    exact pointwiseStateEnvelope_hasFDerivAt_dual domain objective parameterDerivative select
      hparameterSmoothness hparameterStateCross hselectionNonneg hselect hselectionDominant
      hparameterDerivativeAt hparameterDerivativeParameter hparameterDerivativeState hselection parameter
  · intro first second
    have hsmooth := pointwiseStateEnvelope_derivative_lipschitz_dual domain parameterDerivative select
      hparameterStateCross hselect hparameterDerivativeParameter
      hparameterDerivativeState hselection first second
    simpa only [mul_div_assoc] using hsmooth

end Optimization
end AppliedModelingLib

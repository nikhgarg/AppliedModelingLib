import AppliedModelingLib.Foundations.Optimization.StrongConcaveArgmax

/-!
# Differentiability from a quadratic envelope bound

This module isolates a reusable envelope-calculus fact.  When a scalar value
function is trapped above and below its first-order affine model by a
quadratic remainder, it has the displayed gradient.  This is the analytic
core needed to turn an attained, stable argmax selection into a smooth value
function without assuming differentiability of that value function.

## External formalization credit

The statement design was checked against Daniel Lyng's Apache-2.0
[`Econlib.Math.Analysis.Danskin`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/Analysis/Danskin.lean)
at revision `003655ccf010cdf44c4f67d6675167b54ce0e9df`.  Econlib currently
pins an incompatible Lean/Mathlib 4.29 environment, so this module is an
independent proof under this repository's 4.30 dependencies; no upstream code
is copied or imported.
-/

namespace AppliedModelingLib
namespace Optimization

open Asymptotics
open scoped InnerProductSpace

variable {Parameter : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]

/-- A two-sided quadratic first-order bound for a scalar value function. -/
def HasQuadraticFirstOrderEnvelopeBound
    (value : Parameter → ℝ) (gradient : Parameter) (base : Parameter) : Prop :=
  ∃ curvature : ℝ, 0 ≤ curvature ∧ ∀ candidate,
    value base + ⟪gradient, candidate - base⟫_ℝ - curvature * ‖candidate - base‖ ^ 2 ≤
      value candidate ∧
    value candidate ≤
      value base + ⟪gradient, candidate - base⟫_ℝ + curvature * ‖candidate - base‖ ^ 2

/--
A two-sided quadratic first-order envelope bound gives differentiability at
the base point.  The result is independent of any particular optimization
problem and is useful whenever max/min envelopes admit matching quadratic
models.
-/
theorem hasGradientAt_of_quadraticFirstOrderEnvelopeBound
    (value : Parameter → ℝ) (gradient : Parameter) (base : Parameter)
    (hbound : HasQuadraticFirstOrderEnvelopeBound value gradient base) :
    HasGradientAt value gradient base := by
  rw [hasGradientAt_iff_isLittleO]
  rcases hbound with ⟨curvature, hcurvature, hbound⟩
  refine (isBigO_iff.2 ⟨curvature, Filter.Eventually.of_forall (fun candidate => ?_)⟩).trans_isLittleO
    (isLittleO_pow_sub_sub base (m := 2) (by norm_num))
  have htwoSided := hbound candidate
  let remainder : ℝ :=
    value candidate - value base - ⟪gradient, candidate - base⟫_ℝ
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

/-- A parameter gradient is Lipschitz in the parameter coordinate, uniformly in state. -/
def ParameterGradientParameterLipschitz {State : Type*}
    (parameterGradient : Parameter → State → Parameter) (constant : ℝ) : Prop :=
  ∀ state first second,
    ‖parameterGradient first state - parameterGradient second state‖ ≤
      constant * ‖first - second‖

/-- A parameter gradient is Lipschitz in the state coordinate, uniformly in parameter. -/
def ParameterGradientStateLipschitz {State : Type*} [NormedAddCommGroup State]
    (parameterGradient : Parameter → State → Parameter) (constant : ℝ) : Prop :=
  ∀ parameter first second,
    ‖parameterGradient parameter first - parameterGradient parameter second‖ ≤
      constant * ‖first - second‖

/-- A parameter gradient is Lipschitz between feasible states of a domain. -/
def ParameterGradientStateLipschitzOn {State : Type*} [NormedAddCommGroup State]
    (domain : Set State) (parameterGradient : Parameter → State → Parameter)
    (constant : ℝ) : Prop :=
  ∀ parameter first, first ∈ domain → ∀ second, second ∈ domain →
    ‖parameterGradient parameter first - parameterGradient parameter second‖ ≤
      constant * ‖first - second‖

/--
An approximate strongly-concave state maximizer induces a squared parameter-
gradient error controlled by the state-gradient cross constant.  This combines
the objective-gap-to-state-distance estimate with a Lipschitz parameter
gradient, while keeping the attainment and first-order-maximizer conditions
explicit.
-/
theorem sq_norm_parameterGradient_sub_le_two_mul_sq_div_of_approximateStateMaximizer
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    (objective : Parameter → State → ℝ) (parameterGradient : Parameter → State → Parameter)
    (stateGradient : Parameter → State → State) (select : Parameter → State)
    {modulus stateCross error : ℝ}
    (hmodulus : 0 < modulus) (hstateCross : 0 ≤ stateCross)
    (hstrong : StrongConcaveInStateFirstOrder objective stateGradient modulus)
    (hfirstOrder : HasStateFirstOrderMaximizerCondition stateGradient select)
    (hparameterGradient : ParameterGradientStateLipschitz parameterGradient stateCross)
    (parameter : Parameter) (candidate : State)
    (happroximate : objective parameter (select parameter) - objective parameter candidate ≤ error) :
    ‖parameterGradient parameter candidate - parameterGradient parameter (select parameter)‖ ^ 2 ≤
      2 * stateCross ^ 2 * error / modulus := by
  have hdistance : ‖candidate - select parameter‖ ^ 2 ≤ 2 * error / modulus :=
    sq_norm_sub_le_two_mul_div_of_approximateStateMaximizer objective stateGradient select
      hmodulus hstrong hfirstOrder parameter candidate happroximate
  have hgradient := hparameterGradient parameter candidate (select parameter)
  have hgradientRightNonneg : 0 ≤ stateCross * ‖candidate - select parameter‖ :=
    mul_nonneg hstateCross (norm_nonneg _)
  have hgradientSq :
      ‖parameterGradient parameter candidate - parameterGradient parameter (select parameter)‖ ^ 2 ≤
        (stateCross * ‖candidate - select parameter‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hgradientRightNonneg).mpr hgradient
  calc
    ‖parameterGradient parameter candidate - parameterGradient parameter (select parameter)‖ ^ 2 ≤
        stateCross ^ 2 * ‖candidate - select parameter‖ ^ 2 := by
          simpa [mul_pow] using hgradientSq
    _ ≤ stateCross ^ 2 * (2 * error / modulus) := by
      exact mul_le_mul_of_nonneg_left hdistance (sq_nonneg stateCross)
    _ = 2 * stateCross ^ 2 * error / modulus := by ring

/--
The approximate-inner gradient estimate on a feasible state domain.  The
selected and candidate states are explicitly required to lie in the domain,
so a constrained maximization is not treated as an ambient one.
-/
theorem sq_norm_parameterGradient_sub_le_two_mul_sq_div_of_approximateStateMaximizerOn
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    (domain : Set State) (objective : Parameter → State → ℝ)
    (parameterGradient : Parameter → State → Parameter)
    (stateGradient : Parameter → State → State) (select : Parameter → State)
    {modulus stateCross error : ℝ}
    (hmodulus : 0 < modulus) (hstateCross : 0 ≤ stateCross)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hstrong : StrongConcaveInStateFirstOrderOn domain objective stateGradient modulus)
    (hfirstOrder : HasStateFirstOrderMaximizerConditionOn domain stateGradient select)
    (hparameterGradient : ParameterGradientStateLipschitzOn domain parameterGradient stateCross)
    (parameter : Parameter) (candidate : State) (hcandidate : candidate ∈ domain)
    (happroximate : objective parameter (select parameter) - objective parameter candidate ≤ error) :
    ‖parameterGradient parameter candidate - parameterGradient parameter (select parameter)‖ ^ 2 ≤
      2 * stateCross ^ 2 * error / modulus := by
  have hdistance : ‖candidate - select parameter‖ ^ 2 ≤ 2 * error / modulus :=
    sq_norm_sub_le_two_mul_div_of_approximateStateMaximizerOn domain objective stateGradient
      select hmodulus hselect hstrong hfirstOrder parameter candidate hcandidate happroximate
  have hgradient := hparameterGradient parameter candidate hcandidate (select parameter)
    (hselect parameter)
  have hgradientRightNonneg : 0 ≤ stateCross * ‖candidate - select parameter‖ :=
    mul_nonneg hstateCross (norm_nonneg _)
  have hgradientSq :
      ‖parameterGradient parameter candidate - parameterGradient parameter (select parameter)‖ ^ 2 ≤
        (stateCross * ‖candidate - select parameter‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hgradientRightNonneg).mpr hgradient
  calc
    ‖parameterGradient parameter candidate - parameterGradient parameter (select parameter)‖ ^ 2 ≤
        stateCross ^ 2 * ‖candidate - select parameter‖ ^ 2 := by
          simpa [mul_pow] using hgradientSq
    _ ≤ stateCross ^ 2 * (2 * error / modulus) := by
      exact mul_le_mul_of_nonneg_left hdistance (sq_nonneg stateCross)
    _ = 2 * stateCross ^ 2 * error / modulus := by ring

/-- A state gradient is Lipschitz in the state coordinate, uniformly in parameter. -/
def StateGradientStateLipschitz {State : Type*} [NormedAddCommGroup State]
    (stateGradient : Parameter → State → State) (constant : ℝ) : Prop :=
  ∀ parameter first second,
    ‖stateGradient parameter first - stateGradient parameter second‖ ≤
      constant * ‖first - second‖

/-- A chosen state is Lipschitz as a function of the parameter. -/
def StateSelectionLipschitz {State : Type*} [NormedAddCommGroup State]
    (select : Parameter → State) (constant : ℝ) : Prop :=
  ∀ first second, ‖select first - select second‖ ≤ constant * ‖first - second‖

/-- The optimizer-map estimate from `StrongConcaveArgmax` as a named Lipschitz property. -/
theorem stateSelectionLipschitz_of_pointwiseStateMaximizer
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    (objective : Parameter → State → ℝ) (stateGradient : Parameter → State → State)
    (select : Parameter → State) {modulus crossConstant : ℝ}
    (hmodulus : 0 < modulus)
    (hstrong : StrongConcaveInStateFirstOrder objective stateGradient modulus)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerCondition stateGradient select)
    (hcross : StateGradientCrossLipschitz stateGradient crossConstant) :
    StateSelectionLipschitz select (crossConstant / modulus) := by
  intro first second
  exact pointwiseStateMaximizer_lipschitz objective stateGradient select hmodulus hstrong hmax
    hfirstOrder hcross first second

/--
An attained pointwise envelope has the selected parameter gradient whenever
the fixed-state parameter gradients are smooth and the selected state is
Lipschitz.  The hypotheses are stated separately so the result applies to
maxima, minima after negation, and implicitly defined best responses.
-/
theorem pointwiseStateEnvelope_quadraticBound
    {State : Type*} [NormedAddCommGroup State]
    (objective : Parameter → State → ℝ) (parameterGradient : Parameter → State → Parameter)
    (select : Parameter → State) {parameterSmoothness stateCross selectionConstant : ℝ}
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hstateCross : 0 ≤ stateCross)
    (hselectionConstant : 0 ≤ selectionConstant)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hgradientAt : ∀ parameter state,
      HasGradientAt (fun other => objective other state) (parameterGradient parameter state) parameter)
    (hparameterGradient :
      ParameterGradientParameterLipschitz parameterGradient parameterSmoothness)
    (hstateGradient : ParameterGradientStateLipschitz parameterGradient stateCross)
    (hselection : StateSelectionLipschitz select selectionConstant)
    (base : Parameter) :
    HasQuadraticFirstOrderEnvelopeBound
      (fun parameter => objective parameter (select parameter))
      (parameterGradient base (select base)) base := by
  refine ⟨3 * parameterSmoothness / 2 + stateCross * selectionConstant, ?_, ?_⟩
  · positivity
  intro candidate
  have hfixedBaseReverse := smooth_upper_model_bound
    (fun parameter => objective parameter (select base))
    (fun parameter => parameterGradient parameter (select base)) parameterSmoothness
    (fun first second => hparameterGradient (select base) first second)
    (fun parameter => hgradientAt parameter (select base)) candidate base
  have hfixedBaseLower :
      objective base (select base) +
          ⟪parameterGradient base (select base), candidate - base⟫_ℝ -
            3 * parameterSmoothness / 2 * ‖candidate - base‖ ^ 2 ≤
        objective candidate (select base) := by
    have hfixedBaseReverse' :
        objective base (select base) ≤
          objective candidate (select base) -
              ⟪parameterGradient candidate (select base), candidate - base⟫_ℝ +
            parameterSmoothness / 2 * ‖candidate - base‖ ^ 2 := by
      have hreverseDisplacement : base - candidate = -(candidate - base) := by
        abel
      rw [hreverseDisplacement, inner_neg_right, norm_neg] at hfixedBaseReverse
      linarith [hfixedBaseReverse]
    have hgradientDifference :
        ‖parameterGradient candidate (select base) - parameterGradient base (select base)‖ ≤
          parameterSmoothness * ‖candidate - base‖ :=
      hparameterGradient (select base) candidate base
    have hnegativeInner :
        -⟪parameterGradient candidate (select base) - parameterGradient base (select base),
          candidate - base⟫_ℝ ≤
          ‖parameterGradient candidate (select base) - parameterGradient base (select base)‖ *
            ‖candidate - base‖ := by
      rw [← inner_neg_left]
      simpa only [norm_neg] using real_inner_le_norm
        (-(parameterGradient candidate (select base) - parameterGradient base (select base)))
        (candidate - base)
    have hgradientProduct :
        ‖parameterGradient candidate (select base) - parameterGradient base (select base)‖ *
            ‖candidate - base‖ ≤
          (parameterSmoothness * ‖candidate - base‖) * ‖candidate - base‖ :=
      mul_le_mul_of_nonneg_right hgradientDifference (norm_nonneg _)
    have hinnerLower :
        -(parameterSmoothness * ‖candidate - base‖ ^ 2) ≤
          ⟪parameterGradient candidate (select base) - parameterGradient base (select base),
            candidate - base⟫_ℝ := by
      nlinarith [hnegativeInner, hgradientProduct]
    have hgradientSplitBase :
        ⟪parameterGradient candidate (select base), candidate - base⟫_ℝ =
          ⟪parameterGradient base (select base), candidate - base⟫_ℝ +
            ⟪parameterGradient candidate (select base) - parameterGradient base (select base),
              candidate - base⟫_ℝ := by
      rw [← inner_add_left]
      congr 1
      abel
    rw [hgradientSplitBase] at hfixedBaseReverse'
    nlinarith [hfixedBaseReverse', hinnerLower]
  have hfixedCandidate := smooth_upper_model_bound
    (fun parameter => objective parameter (select candidate))
    (fun parameter => parameterGradient parameter (select candidate)) parameterSmoothness
    (fun first second => hparameterGradient (select candidate) first second)
    (fun parameter => hgradientAt parameter (select candidate)) base candidate
  have hmaxAtCandidate :
      objective candidate (select base) ≤ objective candidate (select candidate) :=
    hmax candidate (select base)
  have hmaxAtBase :
      objective base (select candidate) ≤ objective base (select base) :=
    hmax base (select candidate)
  have hselectionBound :
      ‖select candidate - select base‖ ≤ selectionConstant * ‖candidate - base‖ :=
    hselection candidate base
  have hparameterDifference :
      ‖parameterGradient base (select candidate) - parameterGradient base (select base)‖ ≤
        stateCross * ‖select candidate - select base‖ :=
    hstateGradient base (select candidate) (select base)
  have hinnerDifference :
      ⟪parameterGradient base (select candidate) - parameterGradient base (select base),
        candidate - base⟫_ℝ ≤
        stateCross * selectionConstant * ‖candidate - base‖ ^ 2 := by
    calc
      ⟪parameterGradient base (select candidate) - parameterGradient base (select base),
          candidate - base⟫_ℝ ≤
          ‖parameterGradient base (select candidate) - parameterGradient base (select base)‖ *
            ‖candidate - base‖ :=
        real_inner_le_norm _ _
      _ ≤ (stateCross * ‖select candidate - select base‖) * ‖candidate - base‖ :=
        mul_le_mul_of_nonneg_right hparameterDifference (norm_nonneg _)
      _ ≤ (stateCross * (selectionConstant * ‖candidate - base‖)) * ‖candidate - base‖ := by
        gcongr
      _ = stateCross * selectionConstant * ‖candidate - base‖ ^ 2 := by ring
  have hgradientSplit :
      ⟪parameterGradient base (select candidate), candidate - base⟫_ℝ =
        ⟪parameterGradient base (select base), candidate - base⟫_ℝ +
          ⟪parameterGradient base (select candidate) - parameterGradient base (select base),
            candidate - base⟫_ℝ := by
    rw [← inner_add_left]
    congr 1
    abel
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
    rw [hgradientSplit] at hfixedCandidate
    nlinarith [hfixedCandidate, hmaxAtBase, hinnerDifference]

/-- The selected-gradient formula for a smooth, attained pointwise envelope. -/
theorem pointwiseStateEnvelope_hasGradientAt
    {State : Type*} [NormedAddCommGroup State]
    (objective : Parameter → State → ℝ) (parameterGradient : Parameter → State → Parameter)
    (select : Parameter → State) {parameterSmoothness stateCross selectionConstant : ℝ}
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hstateCross : 0 ≤ stateCross)
    (hselectionConstant : 0 ≤ selectionConstant)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hgradientAt : ∀ parameter state,
      HasGradientAt (fun other => objective other state) (parameterGradient parameter state) parameter)
    (hparameterGradient :
      ParameterGradientParameterLipschitz parameterGradient parameterSmoothness)
    (hstateGradient : ParameterGradientStateLipschitz parameterGradient stateCross)
    (hselection : StateSelectionLipschitz select selectionConstant)
    (base : Parameter) :
    HasGradientAt (fun parameter => objective parameter (select parameter))
      (parameterGradient base (select base)) base :=
  hasGradientAt_of_quadraticFirstOrderEnvelopeBound _ _ _
    (pointwiseStateEnvelope_quadraticBound objective parameterGradient select hparameterSmoothness
      hstateCross hselectionConstant hmax hgradientAt hparameterGradient hstateGradient hselection base)

/-- The selected parameter gradient of a stable pointwise envelope is Lipschitz. -/
theorem pointwiseStateEnvelope_gradient_lipschitz
    {State : Type*} [NormedAddCommGroup State]
    (parameterGradient : Parameter → State → Parameter) (select : Parameter → State)
    {parameterSmoothness stateCross selectionConstant : ℝ}
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hstateCross : 0 ≤ stateCross)
    (hselectionConstant : 0 ≤ selectionConstant)
    (hparameterGradient :
      ParameterGradientParameterLipschitz parameterGradient parameterSmoothness)
    (hstateGradient : ParameterGradientStateLipschitz parameterGradient stateCross)
    (hselection : StateSelectionLipschitz select selectionConstant)
    (first second : Parameter) :
    ‖parameterGradient first (select first) - parameterGradient second (select second)‖ ≤
      (parameterSmoothness + stateCross * selectionConstant) * ‖first - second‖ := by
  calc
    ‖parameterGradient first (select first) - parameterGradient second (select second)‖ ≤
        ‖parameterGradient first (select first) - parameterGradient first (select second)‖ +
          ‖parameterGradient first (select second) - parameterGradient second (select second)‖ := by
      rw [show parameterGradient first (select first) - parameterGradient second (select second) =
          (parameterGradient first (select first) - parameterGradient first (select second)) +
            (parameterGradient first (select second) - parameterGradient second (select second)) by
          abel]
      exact norm_add_le _ _
    _ ≤ stateCross * ‖select first - select second‖ +
          parameterSmoothness * ‖first - second‖ := by
      gcongr
      · exact hstateGradient first (select first) (select second)
      · exact hparameterGradient (select second) first second
    _ ≤ stateCross * (selectionConstant * ‖first - second‖) +
          parameterSmoothness * ‖first - second‖ := by
      gcongr
      exact hselection first second
    _ = (parameterSmoothness + stateCross * selectionConstant) * ‖first - second‖ := by
      ring

/--
The smoothness conclusion for a strongly-concave attained pointwise maximum.
This combines the optimizer-map bound with the quadratic envelope argument.
The explicit attainment and first-order hypotheses are essential on a general
state domain; a convex-domain optimizer theorem can supply them separately.
-/
theorem smoothPointwiseStateEnvelope_of_strongConcavity
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    (objective : Parameter → State → ℝ)
    (parameterGradient : Parameter → State → Parameter)
    (stateGradient : Parameter → State → State) (select : Parameter → State)
    {modulus parameterSmoothness parameterStateCross stateGradientCross : ℝ}
    (hmodulus : 0 < modulus)
    (hparameterSmoothness : 0 ≤ parameterSmoothness)
    (hparameterStateCross : 0 ≤ parameterStateCross)
    (hstateGradientCross : 0 ≤ stateGradientCross)
    (hstrong : StrongConcaveInStateFirstOrder objective stateGradient modulus)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerCondition stateGradient select)
    (hparameterGradientAt : ∀ parameter state,
      HasGradientAt (fun other => objective other state) (parameterGradient parameter state) parameter)
    (hparameterGradientParameter :
      ParameterGradientParameterLipschitz parameterGradient parameterSmoothness)
    (hparameterGradientState : ParameterGradientStateLipschitz parameterGradient parameterStateCross)
    (hstateGradientParameter : StateGradientCrossLipschitz stateGradient stateGradientCross) :
    (∀ parameter,
      HasGradientAt (fun other => objective other (select other))
        (parameterGradient parameter (select parameter)) parameter) ∧
    (∀ first second,
      ‖parameterGradient first (select first) - parameterGradient second (select second)‖ ≤
        (parameterSmoothness + parameterStateCross * stateGradientCross / modulus) *
          ‖first - second‖) := by
  have hselection : StateSelectionLipschitz select (stateGradientCross / modulus) :=
    stateSelectionLipschitz_of_pointwiseStateMaximizer objective stateGradient select hmodulus
      hstrong hmax hfirstOrder hstateGradientParameter
  have hselectionNonneg : 0 ≤ stateGradientCross / modulus :=
    div_nonneg hstateGradientCross hmodulus.le
  constructor
  · intro parameter
    exact pointwiseStateEnvelope_hasGradientAt objective parameterGradient select
      hparameterSmoothness hparameterStateCross hselectionNonneg hmax hparameterGradientAt
      hparameterGradientParameter hparameterGradientState hselection parameter
  · intro first second
    have hsmooth := pointwiseStateEnvelope_gradient_lipschitz parameterGradient select
      hparameterSmoothness hparameterStateCross hselectionNonneg hparameterGradientParameter
      hparameterGradientState hselection first second
    simpa only [mul_div_assoc] using hsmooth

end Optimization
end AppliedModelingLib

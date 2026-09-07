import AppliedModelingLib.Foundations.Optimization.CoordinatewiseSmooth
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Topology.Piecewise

/-!
# Standard smooth activation maps

Checked scalar and finite-coordinate sigmoid and ELU activations with the
global constants commonly used in neural-network smoothness calculations.
The finite-coordinate maps reuse the dimension-free coordinatewise lifting
theorem from `CoordinatewiseSmooth`.
-/

namespace AppliedModelingLib.Optimization

open Filter Topology

noncomputable section

/-- The scalar sigmoid derivative. -/
def sigmoidSlope (x : ℝ) : ℝ := Real.sigmoid x * (1 - Real.sigmoid x)

theorem sigmoidSlope_nonneg (x : ℝ) : 0 ≤ sigmoidSlope x := by
  exact mul_nonneg (Real.sigmoid_nonneg x) (sub_nonneg.mpr (Real.sigmoid_le_one x))

theorem sigmoidSlope_le_one_quarter (x : ℝ) : sigmoidSlope x ≤ (1 : ℝ) / 4 := by
  unfold sigmoidSlope
  nlinarith [sq_nonneg (Real.sigmoid x - (1 : ℝ) / 2)]

/-- The derivative of the sigmoid slope in factorized form. -/
theorem hasDerivAt_sigmoidSlope (x : ℝ) :
    HasDerivAt sigmoidSlope
      (sigmoidSlope x * (1 - 2 * Real.sigmoid x)) x := by
  unfold sigmoidSlope
  convert ((Real.hasDerivAt_sigmoid x).mul
    ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_sigmoid x))) using 1
  all_goals
    simp only [Pi.sub_apply]
    ring

/-- The sharp-enough rational bound used in the SNVD17 sigmoid example. -/
theorem abs_sigmoidSlope_deriv_le_one_tenth (x : ℝ) :
    |sigmoidSlope x * (1 - 2 * Real.sigmoid x)| ≤ (1 : ℝ) / 10 := by
  let probability := Real.sigmoid x
  let deviation := |1 - 2 * probability|
  have hp0 : 0 ≤ probability := Real.sigmoid_nonneg x
  have hp1 : probability ≤ 1 := Real.sigmoid_le_one x
  have hdeviation0 : 0 ≤ deviation := abs_nonneg _
  have hdeviation1 : deviation ≤ 1 := by
    apply abs_le.mpr
    constructor <;> dsimp only [probability] <;> linarith
  have hslope : sigmoidSlope x = (1 - deviation ^ 2) / 4 := by
    dsimp only [deviation, probability]
    rw [sq_abs]
    unfold sigmoidSlope
    ring
  have hcubic : deviation - deviation ^ 3 ≤ (2 : ℝ) / 5 := by
    by_cases hsmall : deviation ≤ (2 : ℝ) / 5
    · have hcube : 0 ≤ deviation ^ 3 := pow_nonneg hdeviation0 3
      linarith
    · have hlarge : (2 : ℝ) / 5 ≤ deviation := le_of_not_ge hsmall
      have hfactor :
          0 ≤ (deviation - (3 : ℝ) / 5) ^ 2 * (deviation + (6 : ℝ) / 5) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have hremainder : 0 ≤ (2 : ℝ) / 25 * (deviation - (2 : ℝ) / 5) :=
        mul_nonneg (by norm_num) (sub_nonneg.mpr hlarge)
      have hid :
          (2 : ℝ) / 5 - deviation + deviation ^ 3 =
            (deviation - (3 : ℝ) / 5) ^ 2 * (deviation + (6 : ℝ) / 5) +
              (2 : ℝ) / 25 * (deviation - (2 : ℝ) / 5) := by ring
      linarith
  have hslopeNonneg : 0 ≤ sigmoidSlope x := sigmoidSlope_nonneg x
  calc
    |sigmoidSlope x * (1 - 2 * Real.sigmoid x)| = sigmoidSlope x * deviation := by
      rw [abs_mul, abs_of_nonneg hslopeNonneg]
    _ = (deviation - deviation ^ 3) / 4 := by rw [hslope]; ring
    _ ≤ ((2 : ℝ) / 5) / 4 := div_le_div_of_nonneg_right hcubic (by norm_num)
    _ = (1 : ℝ) / 10 := by norm_num

/-- The scalar sigmoid derivative is globally `1/10`-Lipschitz. -/
theorem sigmoidSlope_lipschitz (first second : ℝ) :
    |sigmoidSlope first - sigmoidSlope second| ≤ (1 : ℝ) / 10 * |first - second| := by
  have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun point _ => (hasDerivAt_sigmoidSlope point).hasDerivWithinAt)
    (fun point _ => by
      rw [Real.norm_eq_abs]
      exact abs_sigmoidSlope_deriv_le_one_tenth point)
    (Set.mem_univ second) (Set.mem_univ first)
  simpa only [Real.norm_eq_abs] using hbound

/-- Scalar sigmoid as a globally first-order smooth map. -/
def scalarSigmoidSmoothMap : FirstOrderSmoothMap ℝ ℝ where
  toFun := Real.sigmoid
  deriv := fun x => ContinuousLinearMap.toSpanSingleton ℝ (sigmoidSlope x)
  valueLipschitz := (1 : ℝ) / 4
  derivBound := (1 : ℝ) / 4
  derivSmoothness := (1 : ℝ) / 10
  valueLipschitz_nonneg := by norm_num
  derivBound_nonneg := by norm_num
  derivSmoothness_nonneg := by norm_num
  hasFDerivAt := fun x => by
    simpa only [sigmoidSlope] using (Real.hasDerivAt_sigmoid x).hasFDerivAt
  value_lipschitz := by
    intro first second
    have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun point _ => (Real.hasDerivAt_sigmoid point).hasDerivWithinAt)
      (fun point _ => by
        change |sigmoidSlope point| ≤ (1 : ℝ) / 4
        rw [abs_of_nonneg (sigmoidSlope_nonneg point)]
        exact sigmoidSlope_le_one_quarter point)
      (Set.mem_univ second) (Set.mem_univ first)
    simpa only [Real.norm_eq_abs, sigmoidSlope] using hbound
  deriv_bound := by
    intro point
    rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs,
      abs_of_nonneg (sigmoidSlope_nonneg point)]
    exact sigmoidSlope_le_one_quarter point
  deriv_lipschitz := by
    intro first second
    have heq :
        ContinuousLinearMap.toSpanSingleton ℝ (sigmoidSlope first) -
            ContinuousLinearMap.toSpanSingleton ℝ (sigmoidSlope second) =
          ContinuousLinearMap.toSpanSingleton ℝ (sigmoidSlope first - sigmoidSlope second) := by
      apply ContinuousLinearMap.ext
      intro direction
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul]
      ring
    rw [heq, ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs, Real.norm_eq_abs]
    exact sigmoidSlope_lipschitz first second

/-- Coordinatewise sigmoid on any finite Euclidean space, with source constants `1/4`, `1/10`. -/
def finiteSigmoidSmoothMap (Index : Type*) [Fintype Index] [DecidableEq Index] :
    FirstOrderSmoothMap (EuclideanSpace ℝ Index) (EuclideanSpace ℝ Index) :=
  scalarSigmoidSmoothMap.coordinatewise

/-- The ELU activation with scale parameter one. -/
def eluOne (x : ℝ) : ℝ := if 0 ≤ x then x else Real.exp x - 1

/-- The continuous derivative selected for scale-one ELU. -/
def eluOneSlope (x : ℝ) : ℝ := if 0 ≤ x then 1 else Real.exp x

theorem continuous_eluOne : Continuous eluOne := by
  unfold eluOne
  apply Continuous.if
  · intro x hx
    change x ∈ frontier (Set.Ici (0 : ℝ)) at hx
    rw [frontier_Ici] at hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    norm_num
  · exact continuous_id
  · exact Real.continuous_exp.sub continuous_const

theorem continuous_eluOneSlope : Continuous eluOneSlope := by
  unfold eluOneSlope
  apply Continuous.if
  · intro x hx
    change x ∈ frontier (Set.Ici (0 : ℝ)) at hx
    rw [frontier_Ici] at hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    norm_num
  · exact continuous_const
  · exact Real.continuous_exp

theorem hasDerivAt_eluOne_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt eluOne (eluOneSlope x) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hlocal : ∀ᶠ y in 𝓝 x, ¬ 0 ≤ y :=
      (eventually_lt_nhds hxneg).mono fun _ hy => not_le.mpr hy
    have heq : eluOne =ᶠ[𝓝 x] fun y => Real.exp y - 1 :=
      hlocal.mono fun y hy => by simp [eluOne, hy]
    simpa [eluOneSlope, not_le.mpr hxneg] using
      ((Real.hasDerivAt_exp x).sub_const 1).congr_of_eventuallyEq heq
  · have hlocal : ∀ᶠ y in 𝓝 x, 0 ≤ y :=
      eventually_ge_nhds hxpos
    have heq : eluOne =ᶠ[𝓝 x] id :=
      hlocal.mono fun y hy => by simp [eluOne, hy]
    simpa [eluOneSlope, hxpos.le] using (hasDerivAt_id x).congr_of_eventuallyEq heq

theorem hasDerivAt_eluOne (x : ℝ) : HasDerivAt eluOne (eluOneSlope x) x := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := 0)
    hasDerivAt_eluOne_of_ne_zero continuous_eluOne.continuousAt
    continuous_eluOneSlope.continuousAt

theorem eluOneSlope_nonneg (x : ℝ) : 0 ≤ eluOneSlope x := by
  unfold eluOneSlope
  split_ifs
  · norm_num
  · exact (Real.exp_pos x).le

theorem eluOneSlope_le_one (x : ℝ) : eluOneSlope x ≤ 1 := by
  unfold eluOneSlope
  split_ifs with hx
  · exact le_rfl
  · exact Real.exp_le_one_iff.mpr (le_of_not_ge hx)

theorem exp_lipschitz_on_nonpositive {first second : ℝ}
    (hfirst : first ≤ 0) (hsecond : second ≤ 0) :
    |Real.exp first - Real.exp second| ≤ |first - second| := by
  have hbound := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun point _ => (Real.hasDerivAt_exp point).hasDerivWithinAt)
    (fun point hpoint => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos point)]
      exact Real.exp_le_one_iff.mpr hpoint)
    hsecond hfirst
  simpa only [Real.norm_eq_abs, one_mul] using hbound

/-- The ELU derivative is globally one-Lipschitz. -/
theorem eluOneSlope_lipschitz (first second : ℝ) :
    |eluOneSlope first - eluOneSlope second| ≤ |first - second| := by
  by_cases hfirst : 0 ≤ first
  · by_cases hsecond : 0 ≤ second
    · simp [eluOneSlope, hfirst, hsecond]
    · have hsecondNonpos : second ≤ 0 := le_of_not_ge hsecond
      have hexp : Real.exp second ≤ 1 := Real.exp_le_one_iff.mpr hsecondNonpos
      have htangent := Real.add_one_le_exp second
      simp only [eluOneSlope, if_pos hfirst, if_neg hsecond]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  · have hfirstNonpos : first ≤ 0 := le_of_not_ge hfirst
    by_cases hsecond : 0 ≤ second
    · have hexp : Real.exp first ≤ 1 := Real.exp_le_one_iff.mpr hfirstNonpos
      have htangent := Real.add_one_le_exp first
      simp only [eluOneSlope, if_neg hfirst, if_pos hsecond]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have hsecondNonpos : second ≤ 0 := le_of_not_ge hsecond
      simp only [eluOneSlope, if_neg hfirst, if_neg hsecond]
      exact exp_lipschitz_on_nonpositive hfirstNonpos hsecondNonpos

/-- Scalar scale-one ELU as a globally first-order smooth map. -/
def scalarEluOneSmoothMap : FirstOrderSmoothMap ℝ ℝ where
  toFun := eluOne
  deriv := fun x => ContinuousLinearMap.toSpanSingleton ℝ (eluOneSlope x)
  valueLipschitz := 1
  derivBound := 1
  derivSmoothness := 1
  valueLipschitz_nonneg := zero_le_one
  derivBound_nonneg := zero_le_one
  derivSmoothness_nonneg := zero_le_one
  hasFDerivAt := fun x => (hasDerivAt_eluOne x).hasFDerivAt
  value_lipschitz := by
    intro first second
    have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun point _ => (hasDerivAt_eluOne point).hasDerivWithinAt)
      (fun point _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (eluOneSlope_nonneg point)]
        exact eluOneSlope_le_one point)
      (Set.mem_univ second) (Set.mem_univ first)
    simpa only [Real.norm_eq_abs, one_mul] using hbound
  deriv_bound := by
    intro point
    rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs,
      abs_of_nonneg (eluOneSlope_nonneg point)]
    exact eluOneSlope_le_one point
  deriv_lipschitz := by
    intro first second
    have heq :
        ContinuousLinearMap.toSpanSingleton ℝ (eluOneSlope first) -
            ContinuousLinearMap.toSpanSingleton ℝ (eluOneSlope second) =
          ContinuousLinearMap.toSpanSingleton ℝ (eluOneSlope first - eluOneSlope second) := by
      apply ContinuousLinearMap.ext
      intro direction
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul]
      ring
    rw [heq, ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs, Real.norm_eq_abs,
      one_mul]
    exact eluOneSlope_lipschitz first second

/-- Coordinatewise scale-one ELU on any finite Euclidean space, with constants `1`, `1`. -/
def finiteEluOneSmoothMap (Index : Type*) [Fintype Index] [DecidableEq Index] :
    FirstOrderSmoothMap (EuclideanSpace ℝ Index) (EuclideanSpace ℝ Index) :=
  scalarEluOneSmoothMap.coordinatewise

end
end AppliedModelingLib.Optimization

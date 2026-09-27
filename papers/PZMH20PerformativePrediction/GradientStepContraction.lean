import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex

/-!
# Gradient-step contraction from sharp interpolation

This is the deterministic Hilbert-space step used after the feasible-domain
interpolation inequality. The AM--GM step-size calculation is the same one
used in `norm_measureRepeatedGradientDescentUpdate_sub_le_of_interpolation`
in the shared performative-prediction development. It is isolated here from
the statistical model and from the domain on which interpolation was proved.
-/

namespace PZMH20PerformativePrediction.DomainGradient

open scoped InnerProductSpace

/-- The usual smooth--strong step-size range puts the classical contraction
gap at most one half. -/
theorem classical_step_gap_le_half {β γ η : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hstep : η ≤ 2 / (β + γ)) : η * (β * γ / (β + γ)) ≤ 1 / 2 := by
  have hsum : 0 < β + γ := by positivity
  have hamgm : 4 * β * γ ≤ (β + γ) ^ 2 := by nlinarith [sq_nonneg (β - γ)]
  have hscaled := mul_le_mul_of_nonneg_right hstep
    (by positivity : 0 ≤ β * γ / (β + γ))
  have hratio : 2 * β * γ / (β + γ) ^ 2 ≤ 1 / 2 :=
    (div_le_iff₀ (sq_pos_of_pos hsum)).mpr (by nlinarith only [hamgm])
  calc
    η * (β * γ / (β + γ)) ≤ (2 / (β + γ)) * (β * γ / (β + γ)) := hscaled
    _ = 2 * β * γ / (β + γ) ^ 2 := by field_simp
    _ ≤ 1 / 2 := hratio

/-- Sharp interpolation controls one gradient step. The bound is slightly
weaker than the square-root classical factor but convenient for the paper's
linear contraction coefficient. -/
theorem norm_sub_smul_le_of_interpolation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (displacement gradientDifference : E) {β γ η : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hη : 0 ≤ η)
    (hstep : η ≤ 2 / (β + γ))
    (hinterpolation : β * γ * ‖displacement‖ ^ 2 + ‖gradientDifference‖ ^ 2 ≤
      (β + γ) * ⟪gradientDifference, displacement⟫_ℝ) :
    ‖displacement - η • gradientDifference‖ ≤
      (1 - η * (β * γ / (β + γ))) * ‖displacement‖ := by
  have hsum : 0 < β + γ := by positivity
  have hpair : (β * γ * ‖displacement‖ ^ 2 + ‖gradientDifference‖ ^ 2) / (β + γ) ≤
      ⟪gradientDifference, displacement⟫_ℝ :=
    (div_le_iff₀ hsum).mpr (by simpa only [mul_comm] using hinterpolation)
  have hpairScaled := mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ 2 * η)
  have hstepSq : η ^ 2 ≤ 2 * η / (β + γ) := by
    calc
      η ^ 2 = η * η := by ring
      _ ≤ η * (2 / (β + γ)) := mul_le_mul_of_nonneg_left hstep hη
      _ = _ := by ring
  have hstepSqScaled := mul_le_mul_of_nonneg_right hstepSq (sq_nonneg ‖gradientDifference‖)
  have hraw : ‖displacement - η • gradientDifference‖ ^ 2 ≤
      (1 - 2 * η * (β * γ / (β + γ))) * ‖displacement‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm gradientDifference displacement,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_pow]
    simp only [div_eq_mul_inv] at hpairScaled hstepSqScaled ⊢
    nlinarith only [hpairScaled, hstepSqScaled]
  have hgap := classical_step_gap_le_half hβ hγ hstep
  have hright : 0 ≤ (1 - η * (β * γ / (β + γ))) * ‖displacement‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  exact hraw.trans (by
    nlinarith [mul_nonneg (sq_nonneg (η * (β * γ / (β + γ))))
      (sq_nonneg ‖displacement‖)])

/-- The source's step-size and sensitivity restrictions make its displayed
RGD factor nonnegative and strictly less than one. The same-law/law-shift
proof gives a stronger factor, which is bounded by the displayed one. -/
theorem rgd_source_factor_bounds {β γ ε η : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 ≤ ε) (hη : 0 < η)
    (hstep : η ≤ 2 / (γ + β))
    (hsmall : ε < γ / ((γ + β) * (1 + (3 / 2) * η * β))) :
    (0 ≤ 1 - η * (γ * β / (γ + β) - ε * ((3 / 2) * η * β ^ 2 + β)) ∧
      1 - η * (γ * β / (γ + β) - ε * ((3 / 2) * η * β ^ 2 + β)) < 1) ∧
    1 - η * (β * γ / (β + γ) - β * ε) ≤
      1 - η * (γ * β / (γ + β) - ε * ((3 / 2) * η * β ^ 2 + β)) := by
  let gap := γ * β / (γ + β) - ε * ((3 / 2) * η * β ^ 2 + β)
  have hsum : 0 < γ + β := by positivity
  have hdenominator : 0 < (γ + β) * (1 + (3 / 2) * η * β) := by positivity
  have hscaled := (lt_div_iff₀ hdenominator).mp hsmall
  have htransport := mul_lt_mul_of_pos_right hscaled (by positivity : 0 < β / (γ + β))
  have hidentity : ((γ + β) * (1 + (3 / 2) * η * β)) * (β / (γ + β)) =
      (3 / 2) * η * β ^ 2 + β := by
    field_simp
    ring
  rw [mul_assoc ε, hidentity] at htransport
  have htransport' : ε * ((3 / 2) * η * β ^ 2 + β) < γ * β / (γ + β) := by
    calc
      ε * ((3 / 2) * η * β ^ 2 + β) < γ * (β / (γ + β)) := htransport
      _ = γ * β / (γ + β) := by field_simp
  have hgap : 0 < gap := by dsimp [gap]; linarith only [htransport']
  have hgap_le : gap ≤ γ * β / (γ + β) := by
    dsimp [gap]
    exact sub_le_self _ (by positivity)
  have hclassical := classical_step_gap_le_half hγ hβ hstep
  have hstepGap : η * gap ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hgap_le hη.le).trans hclassical
  have hpositive : 0 < η * gap := mul_pos hη hgap
  constructor
  · change 0 ≤ 1 - η * gap ∧ 1 - η * gap < 1
    constructor <;> linarith
  · rw [add_comm β γ, mul_comm β γ]
    have hextra : 0 ≤ η * ε * ((3 / 2) * η * β ^ 2) := by positivity
    nlinarith only [hextra]

end PZMH20PerformativePrediction.DomainGradient

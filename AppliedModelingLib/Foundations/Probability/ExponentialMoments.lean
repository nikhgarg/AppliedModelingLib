import AppliedModelingLib.Foundations.Probability.Exponential

/-!
# First moments of exponential measures

This module exposes the basic mean identity for the rate-parameterized
exponential measure.  It uses the concrete exponential model already
constructed for order-statistic arguments.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The identity observable is integrable under every positive-rate
exponential probability measure. -/
theorem integrable_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x) (expMeasure rate) := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  change Integrable (fun x : ℝ => x) M.measure
  exact M.integrable_id

/-- A rate-`rate` exponential random variable has mean `1 / rate`. -/
theorem integral_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    ∫ x, x ∂expMeasure rate = 1 / rate := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  change ∫ x, x ∂M.measure = 1 / rate
  rw [M.integral_id_eq_expectedMaxValue_one]
  simp [Exponential.Model.expectedMaxValue, Exponential.expectedMaxValueOfRate_one, M]

/-- The square of the identity times a rate-`rate` exponential density is a
constant multiple of the shape-three Gamma density. -/
theorem sq_mul_gammaPDFReal_one_eq_gammaPDFReal_three
    {rate : ℝ} (hrate : 0 < rate) (x : ℝ) :
    x ^ 2 * gammaPDFReal 1 rate x =
      (2 / rate ^ 2) * gammaPDFReal 3 rate x := by
  by_cases hx : 0 ≤ x
  · simp only [gammaPDFReal, if_pos hx]
    rw [show (1 : ℝ) - 1 = 0 by norm_num,
      show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_zero, Real.rpow_one]
    norm_num [Real.Gamma_nat_eq_factorial]
    field_simp [ne_of_gt hrate]
  · simp [gammaPDFReal, hx]

/-- A positive-rate Gamma density has real integral one. -/
theorem integral_gammaPDFReal_eq_one {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    ∫ x, gammaPDFReal shape rate x = 1 := by
  calc
    ∫ x, gammaPDFReal shape rate x =
        (∫⁻ x, ENNReal.ofReal (gammaPDFReal shape rate x)).toReal :=
      (integral_eq_lintegral_of_nonneg_ae
        (ae_of_all (μ := volume) (gammaPDFReal_nonneg hshape hrate))
        (stronglyMeasurable_gammaPDFReal shape rate).aestronglyMeasurable)
    _ = (∫⁻ x, gammaPDF shape rate x).toReal := rfl
    _ = 1 := by rw [lintegral_gammaPDF_eq_one hshape hrate]; norm_num

/-- The second raw moment of a rate-`rate` exponential variable is
`2 / rate²`. -/
theorem integral_sq_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    ∫ x, x ^ 2 ∂expMeasure rate = 2 / rate ^ 2 := by
  have hmeas : Measurable (gammaPDF 1 rate) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 rate)
  have htop : ∀ᵐ x ∂volume, gammaPDF 1 rate x < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have htoReal : ∀ x : ℝ,
      (gammaPDF 1 rate x).toReal = gammaPDFReal 1 rate x := by
    intro x
    simp [gammaPDF, ENNReal.toReal_ofReal,
      gammaPDFReal_nonneg zero_lt_one hrate]
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas htop]
  simp only [smul_eq_mul]
  simp_rw [htoReal]
  calc
    ∫ x, gammaPDFReal 1 rate x * x ^ 2 =
        ∫ x, x ^ 2 * gammaPDFReal 1 rate x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    _ = ∫ x, (2 / rate ^ 2) * gammaPDFReal 3 rate x := by
      apply integral_congr_ae
      exact ae_of_all _ (sq_mul_gammaPDFReal_one_eq_gammaPDFReal_three hrate)
    _ = (2 / rate ^ 2) * ∫ x, gammaPDFReal 3 rate x := by
      rw [integral_const_mul]
    _ = 2 / rate ^ 2 := by
      rw [integral_gammaPDFReal_eq_one (by norm_num) hrate]
      ring

/-- The squared identity observable is integrable under a positive-rate
exponential measure. -/
theorem integrable_sq_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x ^ 2) (expMeasure rate) := by
  by_contra hnot
  have hzero : ∫ x, x ^ 2 ∂expMeasure rate = 0 := integral_undef hnot
  rw [integral_sq_expMeasure hrate] at hzero
  have hpositive : 0 < 2 / rate ^ 2 := by
    exact div_pos (by norm_num) (sq_pos_of_pos hrate)
  linarith

/-- Centering an exponential holding time by its rate gives an integrable
mean-zero clock increment. -/
theorem integrable_one_sub_mul_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    Integrable (fun x : ℝ => 1 - rate * x) (expMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  exact (integrable_const _).sub ((integrable_id_expMeasure hrate).const_mul rate)

/-- The rate-centered exponential holding-time increment has mean zero. -/
theorem integral_one_sub_mul_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    ∫ x, 1 - rate * x ∂expMeasure rate = 0 := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  rw [integral_sub (integrable_const _)
    ((integrable_id_expMeasure hrate).const_mul rate), integral_const,
    integral_const_mul, integral_id_expMeasure hrate]
  simp only [MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  field_simp [ne_of_gt hrate]
  ring

/-- The square of a rate-centered exponential holding-time increment is
integrable. -/
theorem integrable_sq_one_sub_mul_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    Integrable (fun x : ℝ => (1 - rate * x) ^ 2) (expMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  have hsq : (fun x : ℝ => (1 - rate * x) ^ 2) =
      fun x => 1 - 2 * rate * x + rate ^ 2 * x ^ 2 := by
    funext x
    ring
  rw [hsq]
  exact ((integrable_const _).sub
    ((integrable_id_expMeasure hrate).const_mul (2 * rate))).add
      ((integrable_sq_expMeasure hrate).const_mul (rate ^ 2))

/-- The squared rate-centered exponential holding-time increment has unit
mean. -/
theorem integral_sq_one_sub_mul_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    ∫ x, (1 - rate * x) ^ 2 ∂expMeasure rate = 1 := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  have hsq : (fun x : ℝ => (1 - rate * x) ^ 2) =
      fun x => 1 - 2 * rate * x + rate ^ 2 * x ^ 2 := by
    funext x
    ring
  rw [hsq]
  calc
    ∫ x, 1 - 2 * rate * x + rate ^ 2 * x ^ 2 ∂expMeasure rate =
        (∫ x, 1 - 2 * rate * x ∂expMeasure rate) +
          ∫ x, rate ^ 2 * x ^ 2 ∂expMeasure rate := by
            rw [MeasureTheory.integral_add]
            · exact (integrable_const _).sub
                ((integrable_id_expMeasure hrate).const_mul (2 * rate))
            · exact (integrable_sq_expMeasure hrate).const_mul (rate ^ 2)
    _ = (∫ x, 1 ∂expMeasure rate) -
          (∫ x, 2 * rate * x ∂expMeasure rate) +
          ∫ x, rate ^ 2 * x ^ 2 ∂expMeasure rate := by
            rw [MeasureTheory.integral_sub (integrable_const _)
              ((integrable_id_expMeasure hrate).const_mul (2 * rate))]
    _ = 1 := by
      rw [integral_const, integral_const_mul,
        integral_const_mul, integral_id_expMeasure hrate,
        integral_sq_expMeasure hrate]
      simp only [MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      field_simp [ne_of_gt hrate]
      ring

/-- A positive exponential moment of a positive-rate exponential variable is
finite precisely below its rate parameter.  The proof stays at the density
level: after multiplying by the exponential density, the integrand is the
integrable tail with decay `rate - tilt`. -/
theorem integrable_exp_mul_id_expMeasure {rate tilt : ℝ}
    (hrate : 0 < rate) (htilt : tilt < rate) :
    Integrable (fun x : ℝ => Real.exp (tilt * x)) (expMeasure rate) := by
  have hdecay : 0 < rate - tilt := sub_pos.mpr htilt
  have htail : IntegrableOn (fun x : ℝ => Real.exp (-((rate - tilt) * x)))
      (Set.Ici (0 : ℝ)) volume := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hdecay
  have hindicator : Integrable
      ((Set.Ici (0 : ℝ)).indicator
        (fun x : ℝ => rate * Real.exp (-((rate - tilt) * x))) : ℝ → ℝ) volume :=
    IntegrableOn.integrable_indicator (htail.const_mul rate) measurableSet_Ici
  have htoReal : ∀ x : ℝ,
      (gammaPDF 1 rate x).toReal = gammaPDFReal 1 rate x := by
    intro x
    simp [gammaPDF, ENNReal.toReal_ofReal,
      gammaPDFReal_nonneg zero_lt_one hrate]
  change Integrable (fun x : ℝ => Real.exp (tilt * x))
    (volume.withDensity (gammaPDF 1 rate))
  apply (integrable_withDensity_iff (μ := volume) (f := gammaPDF 1 rate)
    (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 rate))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2
  refine hindicator.congr ?_
  filter_upwards with x
  by_cases hx : 0 ≤ x
  · have hx' : x ∈ Set.Ici (0 : ℝ) := hx
    symm
    rw [Set.indicator_of_mem hx', htoReal x, gammaPDFReal, if_pos hx]
    norm_num [Real.Gamma_nat_eq_factorial]
    calc
      Real.exp (tilt * x) * (rate * Real.exp (-(rate * x))) =
          rate * (Real.exp (tilt * x) * Real.exp (-(rate * x))) := by ring
      _ = rate * Real.exp (tilt * x + -(rate * x)) := by
          rw [← Real.exp_add]
      _ = rate * Real.exp (-((rate - tilt) * x)) := by
          congr 2
          ring
  · have hx' : x ∉ Set.Ici (0 : ℝ) := hx
    symm
    rw [Set.indicator_of_notMem hx', htoReal x, gammaPDFReal, if_neg hx]
    norm_num

/-- The exponential moment of a rate-`rate` exponential variable has its
elementary rational form below the rate boundary. -/
theorem integral_exp_mul_id_expMeasure {rate tilt : ℝ}
    (hrate : 0 < rate) (htilt : tilt < rate) :
    ∫ x, Real.exp (tilt * x) ∂expMeasure rate = rate / (rate - tilt) := by
  have hdecay : 0 < rate - tilt := sub_pos.mpr htilt
  have htoReal : ∀ x : ℝ,
      (gammaPDF 1 rate x).toReal = gammaPDFReal 1 rate x := by
    intro x
    simp [gammaPDF, ENNReal.toReal_ofReal,
      gammaPDFReal_nonneg zero_lt_one hrate]
  change ∫ x, Real.exp (tilt * x) ∂volume.withDensity (gammaPDF 1 rate) =
    rate / (rate - tilt)
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := gammaPDF 1 rate)
    (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 rate))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpointwise : (fun x : ℝ => (gammaPDF 1 rate x).toReal •
      Real.exp (tilt * x)) =
      (Set.Ici (0 : ℝ)).indicator
        (fun x : ℝ => rate * Real.exp (-((rate - tilt) * x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · have hx' : x ∈ Set.Ici (0 : ℝ) := hx
      rw [Set.indicator_of_mem hx', htoReal x, gammaPDFReal, if_pos hx]
      norm_num [Real.Gamma_nat_eq_factorial]
      calc
        (rate * Real.exp (-(rate * x))) • Real.exp (tilt * x) =
            rate * (Real.exp (tilt * x) * Real.exp (-(rate * x))) := by
              simp only [smul_eq_mul]
              ring
        _ = rate * Real.exp (tilt * x + -(rate * x)) := by
              rw [← Real.exp_add]
        _ = rate * Real.exp (-((rate - tilt) * x)) := by
              congr 2
              ring
    · have hx' : x ∉ Set.Ici (0 : ℝ) := hx
      rw [Set.indicator_of_notMem hx', htoReal x, gammaPDFReal, if_neg hx]
      norm_num
  rw [hpointwise, integral_indicator measurableSet_Ici,
    integral_const_mul, integral_Ici_eq_integral_Ioi,
    Exponential.integral_exp_neg_mul_Ioi (rate - tilt) hdecay]
  field_simp [ne_of_gt hdecay]

/-- In mean parametrization, an exponential service time has first moment
equal to its mean. -/
theorem integral_id_expMeasure_inv {mean : ℝ} (hmean : 0 < mean) :
    ∫ x, x ∂expMeasure mean⁻¹ = mean := by
  rw [integral_id_expMeasure (inv_pos.mpr hmean)]
  field_simp [ne_of_gt hmean]

/-- In mean parametrization, an exponential service time has second raw
moment twice the squared mean. -/
theorem integral_sq_expMeasure_inv {mean : ℝ} (hmean : 0 < mean) :
    ∫ x, x ^ 2 ∂expMeasure mean⁻¹ = 2 * mean ^ 2 := by
  rw [integral_sq_expMeasure (inv_pos.mpr hmean)]
  field_simp [ne_of_gt hmean]

/-- The first moment observable is integrable in mean parametrization. -/
theorem integrable_id_expMeasure_inv {mean : ℝ} (hmean : 0 < mean) :
    Integrable (fun x : ℝ => x) (expMeasure mean⁻¹) :=
  integrable_id_expMeasure (inv_pos.mpr hmean)

/-- The second moment observable is integrable in mean parametrization. -/
theorem integrable_sq_expMeasure_inv {mean : ℝ} (hmean : 0 < mean) :
    Integrable (fun x : ℝ => x ^ 2) (expMeasure mean⁻¹) :=
  integrable_sq_expMeasure (inv_pos.mpr hmean)

end

end AppliedModelingLib.Probability

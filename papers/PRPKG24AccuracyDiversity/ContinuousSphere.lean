import AppliedModelingLib.Foundations.Optimization.Averaging
import AppliedModelingLib.Foundations.Probability.IntegralLargeDeviations
import AppliedModelingLib.Foundations.Probability.LargeDeviations
import AppliedModelingLib.Foundations.Optimization.Certificate

namespace PRPKG24AccuracyDiversity

open MeasureTheory
open scoped BigOperators

/-!
# Continuous-Sphere Proposition 4 Layer

This file keeps the paper-facing Proposition 4 averaging names stable while the
reusable averaging/minimization certificate lives in
`AppliedModelingLib.Foundations.Optimization.Averaging`.
-/

/--
Paper-facing alias for the reusable averaging/minimization certificate used in
Proposition 4.
-/
abbrev Proposition4AveragingCertificate :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate

namespace Proposition4AveragingCertificate

/--
If `gamma alpha` is the supremum over user-level values for `alpha`, then it
dominates every user-level value.  This is the Proposition 4 optimization seam
that turns the paper's pointwise `sup` convention into the domination premise
used by the averaging certificate.
-/
theorem rho_le_gamma_of_gamma_eq_sSup_range
    {Profile User : Type*}
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (rho_bddAbove : ∀ alpha : Profile, BddAbove (Set.range (rho alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile, gamma alpha = sSup (Set.range (rho alpha))) :
    ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha := by
  intro alpha u
  rw [gamma_eq_sSup_range alpha]
  exact AppliedModelingLib.Optimization.le_sSup_range
    (rho alpha) u (rho_bddAbove alpha)

/--
Kernel-integral specialization of
`rho_le_gamma_of_gamma_eq_sSup_range`.
-/
theorem kernelIntegral_le_gamma_of_gamma_eq_sSup_range
    {Profile User Item : Type*} [MeasurableSpace Item]
    (profileMeasure : Profile → Measure Item)
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (rho_bddAbove :
      ∀ alpha : Profile,
        BddAbove
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile,
        gamma alpha =
          sSup
            (Set.range
              (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha))) :
    ∀ alpha : Profile, ∀ u : User,
      (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha :=
  rho_le_gamma_of_gamma_eq_sSup_range gamma
    (fun alpha u => ∫ x, kernel x u ∂profileMeasure alpha)
    rho_bddAbove gamma_eq_sSup_range

/--
If a source Laplace integral has exact exponential rate `-gamma alpha`, and a
Laplace-principle theorem computes the same integral's exact rate as the
negative supremum of `rho alpha`, then exact-rate uniqueness identifies
`gamma alpha` with that supremum.
-/
theorem gamma_eq_sSup_range_of_laplace_rate_unique
    {Profile User : Type*}
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (laplace : Profile → ℕ → ℝ)
    (hgamma :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (laplace alpha) (-(gamma alpha)))
    (hsup :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (laplace alpha) (-(sSup (Set.range (rho alpha))))) :
    ∀ alpha : Profile,
      gamma alpha = sSup (Set.range (rho alpha)) := by
  intro alpha
  have hneg :
      -(gamma alpha) = -(sSup (Set.range (rho alpha))) :=
    AppliedModelingLib.Probability.HasExponentialRate.unique
      (hgamma alpha) (hsup alpha)
  linarith

/--
Kernel-integral specialization of
`gamma_eq_sSup_range_of_laplace_rate_unique`.
-/
theorem gamma_eq_sSup_kernelIntegral_range_of_laplace_rate_unique
    {Profile User Item : Type*} [MeasurableSpace Item]
    (profileMeasure : Profile → Measure Item)
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (laplace : Profile → ℕ → ℝ)
    (hgamma :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (laplace alpha) (-(gamma alpha)))
    (hsup :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (laplace alpha)
          (-(sSup
            (Set.range
              (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha))))) :
    ∀ alpha : Profile,
      gamma alpha =
        sSup
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)) :=
  gamma_eq_sSup_range_of_laplace_rate_unique gamma
    (fun alpha u => ∫ x, kernel x u ∂profileMeasure alpha)
    laplace hgamma hsup

/--
If `gamma alpha` is an attained pointwise maximum of the user-level payoff for
every profile, then it is exactly the supremum over users.
-/
theorem gamma_eq_sSup_range_of_attained_pointwise_max
    {Profile User : Type*}
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (hmax : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha)
    (hattain : ∀ alpha : Profile, ∃ u : User, rho alpha u = gamma alpha) :
    ∀ alpha : Profile,
      gamma alpha = sSup (Set.range (rho alpha)) := by
  intro alpha
  symm
  exact AppliedModelingLib.Optimization.sSup_range_eq_of_forall_le_of_exists_eq
    (rho alpha) (hmax alpha) (hattain alpha)

/--
Kernel-integral specialization of
`gamma_eq_sSup_range_of_attained_pointwise_max`.
-/
theorem gamma_eq_sSup_kernelIntegral_range_of_attained_pointwise_max
    {Profile User Item : Type*} [MeasurableSpace Item]
    (profileMeasure : Profile → Measure Item)
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha)
    (hattain :
      ∀ alpha : Profile, ∃ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) = gamma alpha) :
    ∀ alpha : Profile,
      gamma alpha =
        sSup
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)) :=
  gamma_eq_sSup_range_of_attained_pointwise_max gamma
    (fun alpha u => ∫ x, kernel x u ∂profileMeasure alpha)
    hmax hattain

/--
Positive-exponential compact-Laplace bridge for Proposition 4.  If every
profile has an attained user-level maximum `gamma alpha`, and the source
Laplace integral is the weighted integral of `exp (n * rho alpha u)`, then the
integral has exact exponential rate `-gamma alpha`.
-/
theorem positive_laplace_rate_of_attained_pointwise_max_uniformWeightLower
    {Profile User : Type*} [TopologicalSpace User] [MeasurableSpace User]
    [OpensMeasurableSpace User]
    (userMeasure : Profile → Measure User)
    (w : Profile → User → ℝ) (gamma : Profile → ℝ)
    (rho : Profile → User → ℝ) (W c : Profile → ℝ)
    (hfinite : ∀ alpha : Profile, IsFiniteMeasure (userMeasure alpha))
    (hopen : ∀ alpha : Profile,
      Measure.IsOpenPosMeasure (userMeasure alpha))
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        Integrable
          (fun u : User =>
            w alpha u * Real.exp ((n : ℝ) * rho alpha u))
          (userMeasure alpha))
    (hw_int :
      ∀ alpha : Profile,
        Integrable (w alpha) (userMeasure alpha))
    (hWpos : ∀ alpha : Profile, 0 < W alpha)
    (hcpos : ∀ alpha : Profile, 0 < c alpha)
    (hw_lower :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure alpha, c alpha ≤ w alpha u)
    (hw_bound :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure alpha, w alpha u ≤ W alpha)
    (x0 : Profile → User)
    (hmax : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha)
    (hx0 : ∀ alpha : Profile, rho alpha (x0 alpha) = gamma alpha)
    (hcont : ∀ alpha : Profile, ContinuousAt (rho alpha) (x0 alpha)) :
    ∀ alpha : Profile,
      AppliedModelingLib.Probability.ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ u, w alpha u * Real.exp ((n : ℝ) * rho alpha u)
            ∂userMeasure alpha)
        (-(gamma alpha)) := by
  intro alpha
  haveI : IsFiniteMeasure (userMeasure alpha) := hfinite alpha
  haveI : Measure.IsOpenPosMeasure (userMeasure alpha) := hopen alpha
  exact
    AppliedModelingLib.Probability.weightedExactPositiveExponentialIntegral_exponentialRateCertificate_of_continuous_max_uniformWeightLower
      (userMeasure alpha) (w alpha) (rho alpha)
      (hF_int alpha) (hw_int alpha) (hWpos alpha) (hcpos alpha)
      (hw_lower alpha) (hw_bound alpha) (x0 alpha)
      (hmax alpha) (hx0 alpha) (hcont alpha)

/--
Unit-weight positive-exponential compact-Laplace bridge for Proposition 4.
This is the common source form when the Laplace integral is simply
`∫ exp (n * rho)`.
-/
theorem positive_laplace_rate_of_attained_pointwise_max_unitWeight
    {Profile User : Type*} [TopologicalSpace User] [MeasurableSpace User]
    [OpensMeasurableSpace User]
    (userMeasure : Profile → Measure User)
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (hfinite : ∀ alpha : Profile, IsFiniteMeasure (userMeasure alpha))
    (hopen : ∀ alpha : Profile,
      Measure.IsOpenPosMeasure (userMeasure alpha))
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        Integrable
          (fun u : User => Real.exp ((n : ℝ) * rho alpha u))
          (userMeasure alpha))
    (x0 : Profile → User)
    (hmax : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha)
    (hx0 : ∀ alpha : Profile, rho alpha (x0 alpha) = gamma alpha)
    (hcont : ∀ alpha : Profile, ContinuousAt (rho alpha) (x0 alpha)) :
    ∀ alpha : Profile,
      AppliedModelingLib.Probability.ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ u, Real.exp ((n : ℝ) * rho alpha u) ∂userMeasure alpha)
        (-(gamma alpha)) := by
  intro alpha
  have hcert :=
    positive_laplace_rate_of_attained_pointwise_max_uniformWeightLower
      userMeasure (fun _ _ => (1 : ℝ)) gamma rho (fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ)) hfinite hopen
      (by
        intro alpha n
        simpa using hF_int alpha n)
      (by
        intro alpha
        haveI : IsFiniteMeasure (userMeasure alpha) := hfinite alpha
        simpa using
          (integrable_const (1 : ℝ) :
            Integrable (fun _ : User => (1 : ℝ)) (userMeasure alpha)))
      (fun _ => zero_lt_one) (fun _ => zero_lt_one)
      (by
        intro alpha
        filter_upwards with u
        norm_num)
      (by
        intro alpha
        filter_upwards with u
        norm_num)
      x0 hmax hx0 hcont
  refine AppliedModelingLib.Probability.ExponentialRateCertificate.congr ?_
    (hcert alpha)
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards with u
  simp

/--
Positive-exponential Laplace uniqueness bridge for Proposition 4.  If the
source identifies `gamma alpha` as the exact exponential rate of the same
weighted Laplace integral, and the compact Laplace theorem computes that
integral from an attained maximum `supValue alpha`, then `gamma alpha` equals
the user-level supremum.
-/
theorem gamma_eq_sSup_range_of_positive_laplace_rate_unique_attained_max_uniformWeightLower
    {Profile User : Type*} [TopologicalSpace User] [MeasurableSpace User]
    [OpensMeasurableSpace User]
    (userMeasure : Profile → Measure User)
    (w : Profile → User → ℝ) (gamma supValue : Profile → ℝ)
    (rho : Profile → User → ℝ) (W c : Profile → ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u, w alpha u * Real.exp ((n : ℝ) * rho alpha u)
              ∂userMeasure alpha)
          (-(gamma alpha)))
    (hfinite : ∀ alpha : Profile, IsFiniteMeasure (userMeasure alpha))
    (hopen : ∀ alpha : Profile,
      Measure.IsOpenPosMeasure (userMeasure alpha))
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        Integrable
          (fun u : User =>
            w alpha u * Real.exp ((n : ℝ) * rho alpha u))
          (userMeasure alpha))
    (hw_int :
      ∀ alpha : Profile,
        Integrable (w alpha) (userMeasure alpha))
    (hWpos : ∀ alpha : Profile, 0 < W alpha)
    (hcpos : ∀ alpha : Profile, 0 < c alpha)
    (hw_lower :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure alpha, c alpha ≤ w alpha u)
    (hw_bound :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure alpha, w alpha u ≤ W alpha)
    (x0 : Profile → User)
    (hmax : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ supValue alpha)
    (hx0 : ∀ alpha : Profile, rho alpha (x0 alpha) = supValue alpha)
    (hcont : ∀ alpha : Profile, ContinuousAt (rho alpha) (x0 alpha)) :
    ∀ alpha : Profile,
      gamma alpha = sSup (Set.range (rho alpha)) := by
  intro alpha
  have hcert :=
    positive_laplace_rate_of_attained_pointwise_max_uniformWeightLower
      userMeasure w supValue rho W c hfinite hopen hF_int hw_int hWpos
      hcpos hw_lower hw_bound x0 hmax hx0 hcont
  have hrate_eq :
      -(gamma alpha) = -(supValue alpha) :=
    AppliedModelingLib.Probability.HasExponentialRate.unique
      (hsource alpha) (hcert alpha).has_rate
  have hgamma_eq : gamma alpha = supValue alpha := by
    linarith
  have hsSup_eq :
      sSup (Set.range (rho alpha)) = supValue alpha :=
    AppliedModelingLib.Optimization.sSup_range_eq_of_forall_le_of_exists_eq
      (rho alpha) (hmax alpha) ⟨x0 alpha, hx0 alpha⟩
  exact hgamma_eq.trans hsSup_eq.symm

/--
Unit-weight positive-exponential Laplace uniqueness bridge for Proposition 4.
-/
theorem gamma_eq_sSup_range_of_positive_laplace_rate_unique_attained_max_unitWeight
    {Profile User : Type*} [TopologicalSpace User] [MeasurableSpace User]
    [OpensMeasurableSpace User]
    (userMeasure : Profile → Measure User)
    (gamma supValue : Profile → ℝ)
    (rho : Profile → User → ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u, Real.exp ((n : ℝ) * rho alpha u) ∂userMeasure alpha)
          (-(gamma alpha)))
    (hfinite : ∀ alpha : Profile, IsFiniteMeasure (userMeasure alpha))
    (hopen : ∀ alpha : Profile,
      Measure.IsOpenPosMeasure (userMeasure alpha))
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        Integrable
          (fun u : User => Real.exp ((n : ℝ) * rho alpha u))
          (userMeasure alpha))
    (x0 : Profile → User)
    (hmax : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ supValue alpha)
    (hx0 : ∀ alpha : Profile, rho alpha (x0 alpha) = supValue alpha)
    (hcont : ∀ alpha : Profile, ContinuousAt (rho alpha) (x0 alpha)) :
    ∀ alpha : Profile,
      gamma alpha = sSup (Set.range (rho alpha)) := by
  intro alpha
  have hcert :=
    positive_laplace_rate_of_attained_pointwise_max_unitWeight
      userMeasure supValue rho hfinite hopen hF_int x0 hmax hx0 hcont
  have hrate_eq :
      -(gamma alpha) = -(supValue alpha) :=
    AppliedModelingLib.Probability.HasExponentialRate.unique
      (hsource alpha) (hcert alpha).has_rate
  have hgamma_eq : gamma alpha = supValue alpha := by
    linarith
  have hsSup_eq :
      sSup (Set.range (rho alpha)) = supValue alpha :=
    AppliedModelingLib.Optimization.sSup_range_eq_of_forall_le_of_exists_eq
      (rho alpha) (hmax alpha) ⟨x0 alpha, hx0 alpha⟩
  exact hgamma_eq.trans hsSup_eq.symm

noncomputable def ofFiniteUniformAverage
    {Profile User : Type*} [Fintype User] [Nonempty User]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (average_rho_eq_uniformValue :
      ∀ alpha : Profile,
        (∑ u : User, rho alpha u) / (Fintype.card User : ℝ) =
          uniformValue)
    (rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.ofFiniteUniformAverage
    gamma rho uniformProfile uniformValue uniform_gamma_eq
    average_rho_eq_uniformValue rho_le_gamma

noncomputable def ofFiniteUniformAverageOfSupremum
    {Profile User : Type*} [Fintype User] [Nonempty User]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (average_rho_eq_uniformValue :
      ∀ alpha : Profile,
        (∑ u : User, rho alpha u) / (Fintype.card User : ℝ) =
          uniformValue)
    (rho_bddAbove : ∀ alpha : Profile, BddAbove (Set.range (rho alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile, gamma alpha = sSup (Set.range (rho alpha))) :
    Proposition4AveragingCertificate Profile User :=
  ofFiniteUniformAverage gamma rho uniformProfile uniformValue
    uniform_gamma_eq average_rho_eq_uniformValue
    (rho_le_gamma_of_gamma_eq_sSup_range gamma rho
      rho_bddAbove gamma_eq_sSup_range)

noncomputable def ofProbabilityIntegralAverage
    {Profile User : Type*} [MeasurableSpace User]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable : ∀ alpha : Profile, Integrable (rho alpha) userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_rho_eq_uniformValue :
      ∀ alpha : Profile, (∫ u, rho alpha u ∂userMeasure) =
        uniformValue)
    (rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.ofProbabilityIntegralAverage
    userMeasure gamma rho uniformProfile uniformValue rho_integrable
    uniform_gamma_eq integral_rho_eq_uniformValue rho_le_gamma

noncomputable def ofProbabilityIntegralAverageOfSupremum
    {Profile User : Type*} [MeasurableSpace User]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable : ∀ alpha : Profile, Integrable (rho alpha) userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_rho_eq_uniformValue :
      ∀ alpha : Profile, (∫ u, rho alpha u ∂userMeasure) =
        uniformValue)
    (rho_bddAbove : ∀ alpha : Profile, BddAbove (Set.range (rho alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile, gamma alpha = sSup (Set.range (rho alpha))) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityIntegralAverage userMeasure gamma rho uniformProfile
    uniformValue rho_integrable uniform_gamma_eq integral_rho_eq_uniformValue
    (rho_le_gamma_of_gamma_eq_sSup_range gamma rho
      rho_bddAbove gamma_eq_sSup_range)

noncomputable def ofProbabilityIntegralAverageOfPositiveLaplaceRateUniqueAttainedMaxUniformWeightLower
    {Profile User : Type*} [TopologicalSpace User] [MeasurableSpace User]
    [OpensMeasurableSpace User]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (w : Profile → User → ℝ) (gamma supValue : Profile → ℝ)
    (rho : Profile → User → ℝ) (W c : Profile → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u, w alpha u * Real.exp ((n : ℝ) * rho alpha u)
              ∂userMeasure)
          (-(gamma alpha)))
    (hopen : Measure.IsOpenPosMeasure userMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        Integrable
          (fun u : User =>
            w alpha u * Real.exp ((n : ℝ) * rho alpha u))
          userMeasure)
    (hw_int :
      ∀ alpha : Profile,
        Integrable (w alpha) userMeasure)
    (hWpos : ∀ alpha : Profile, 0 < W alpha)
    (hcpos : ∀ alpha : Profile, 0 < c alpha)
    (hw_lower :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure, c alpha ≤ w alpha u)
    (hw_bound :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure, w alpha u ≤ W alpha)
    (rho_integrable : ∀ alpha : Profile, Integrable (rho alpha) userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_rho_eq_uniformValue :
      ∀ alpha : Profile, (∫ u, rho alpha u ∂userMeasure) =
        uniformValue)
    (x0 : Profile → User)
    (hmax : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ supValue alpha)
    (hx0 : ∀ alpha : Profile, rho alpha (x0 alpha) = supValue alpha)
    (hcont : ∀ alpha : Profile, ContinuousAt (rho alpha) (x0 alpha)) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityIntegralAverageOfSupremum userMeasure gamma rho uniformProfile
    uniformValue rho_integrable uniform_gamma_eq integral_rho_eq_uniformValue
    (AppliedModelingLib.Optimization.bddAbove_range_apply_of_forall_le rho hmax)
    (gamma_eq_sSup_range_of_positive_laplace_rate_unique_attained_max_uniformWeightLower
      (fun _ : Profile => userMeasure) w gamma supValue rho W c hsource
      (fun _ => inferInstance) (fun _ => hopen) hF_int hw_int hWpos
      hcpos hw_lower hw_bound x0 hmax hx0 hcont)

noncomputable def ofProbabilityKernelAverage
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable :
      ∀ alpha : Profile,
        Integrable (fun u => ∫ x, kernel x u ∂profileMeasure alpha)
          userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_kernel_swap :
      ∀ alpha : Profile,
        (∫ u, (∫ x, kernel x u ∂profileMeasure alpha) ∂userMeasure) =
          ∫ x, (∫ u, kernel x u ∂userMeasure) ∂profileMeasure alpha)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.ofProbabilityKernelAverage
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue rho_integrable uniform_gamma_eq integral_kernel_swap
    kernel_user_integral_eq rho_le_gamma

noncomputable def ofProbabilityKernelAverageOfSupremum
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable :
      ∀ alpha : Profile,
        Integrable (fun u => ∫ x, kernel x u ∂profileMeasure alpha)
          userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_kernel_swap :
      ∀ alpha : Profile,
        (∫ u, (∫ x, kernel x u ∂profileMeasure alpha) ∂userMeasure) =
          ∫ x, (∫ u, kernel x u ∂userMeasure) ∂profileMeasure alpha)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_bddAbove :
      ∀ alpha : Profile,
        BddAbove
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile,
        gamma alpha =
          sSup
            (Set.range
              (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha))) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityKernelAverage userMeasure profileMeasure profile_probability
    gamma kernel uniformProfile uniformValue rho_integrable uniform_gamma_eq
    integral_kernel_swap kernel_user_integral_eq
    (kernelIntegral_le_gamma_of_gamma_eq_sSup_range
      profileMeasure gamma kernel rho_bddAbove gamma_eq_sSup_range)

noncomputable def ofProbabilityKernelAverageOfIntegrable
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.ofProbabilityKernelAverageOfIntegrable
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue kernel_integrable uniform_gamma_eq kernel_user_integral_eq
    rho_le_gamma

noncomputable def ofProbabilityKernelAverageOfIntegrableOfSupremum
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_bddAbove :
      ∀ alpha : Profile,
        BddAbove
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile,
        gamma alpha =
          sSup
            (Set.range
              (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha))) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityKernelAverageOfIntegrable userMeasure profileMeasure
    profile_probability gamma kernel uniformProfile uniformValue
    kernel_integrable uniform_gamma_eq kernel_user_integral_eq
    (kernelIntegral_le_gamma_of_gamma_eq_sSup_range
      profileMeasure gamma kernel rho_bddAbove gamma_eq_sSup_range)

noncomputable def ofProbabilityKernelAverageOfIntegrableOfPositiveLaplaceRateUniqueAttainedMaxUniformWeightLower
    {Profile User Item : Type*} [TopologicalSpace User] [MeasurableSpace User]
    [OpensMeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (w : Profile → User → ℝ) (gamma supValue : Profile → ℝ)
    (kernel : Item → User → ℝ) (W c : Profile → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u,
              w alpha u *
                Real.exp
                  ((n : ℝ) *
                    (∫ x, kernel x u ∂profileMeasure alpha))
              ∂userMeasure)
          (-(gamma alpha)))
    (hopen : Measure.IsOpenPosMeasure userMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        Integrable
          (fun u : User =>
            w alpha u *
              Real.exp
                ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha)))
          userMeasure)
    (hw_int :
      ∀ alpha : Profile,
        Integrable (w alpha) userMeasure)
    (hWpos : ∀ alpha : Profile, 0 < W alpha)
    (hcpos : ∀ alpha : Profile, 0 < c alpha)
    (hw_lower :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure, c alpha ≤ w alpha u)
    (hw_bound :
      ∀ alpha : Profile,
        ∀ᵐ u ∂userMeasure, w alpha u ≤ W alpha)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (x0 : Profile → User)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, kernel x (x0 alpha) ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)
          (x0 alpha)) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityKernelAverageOfIntegrableOfSupremum userMeasure profileMeasure
    profile_probability gamma kernel uniformProfile uniformValue
    kernel_integrable uniform_gamma_eq kernel_user_integral_eq
    (AppliedModelingLib.Optimization.bddAbove_range_apply_of_forall_le
      (fun alpha u => ∫ x, kernel x u ∂profileMeasure alpha) hmax)
    (gamma_eq_sSup_range_of_positive_laplace_rate_unique_attained_max_uniformWeightLower
      (fun _ : Profile => userMeasure) w gamma supValue
      (fun alpha u => ∫ x, kernel x u ∂profileMeasure alpha) W c hsource
      (fun _ => inferInstance) (fun _ => hopen) hF_int hw_int hWpos
      hcpos hw_lower hw_bound x0 hmax hx0 hcont)

noncomputable def ofProbabilityKernelSymmetryAverageOfIntegrable
    {Profile User Item Sym : Type*} [MeasurableSpace User]
    [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving :
      ∀ g : Sym, MeasurePreserving (userAction g) userMeasure userMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.ofProbabilityKernelSymmetryAverageOfIntegrable
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue kernel_integrable uniform_gamma_eq userAction itemAction anchor
    userAction_measurePreserving userAction_measurableEmbedding
    kernel_diagonal_invariant itemAction_transitive anchor_integral_eq_uniformValue
    rho_le_gamma

noncomputable def ofProbabilityKernelSymmetryAverageOfIntegrableOfSupremum
    {Profile User Item Sym : Type*} [MeasurableSpace User]
    [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving :
      ∀ g : Sym, MeasurePreserving (userAction g) userMeasure userMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂userMeasure) = uniformValue)
    (rho_bddAbove :
      ∀ alpha : Profile,
        BddAbove
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile,
        gamma alpha =
          sSup
            (Set.range
              (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha))) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityKernelSymmetryAverageOfIntegrable userMeasure profileMeasure
    profile_probability gamma kernel uniformProfile uniformValue
    kernel_integrable uniform_gamma_eq userAction itemAction anchor
    userAction_measurePreserving userAction_measurableEmbedding
    kernel_diagonal_invariant itemAction_transitive anchor_integral_eq_uniformValue
    (kernelIntegral_le_gamma_of_gamma_eq_sSup_range
      profileMeasure gamma kernel rho_bddAbove gamma_eq_sSup_range)

noncomputable def ofProbabilityKernelAverageOfBounded
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ) (C : ℝ)
    (kernel_aestronglyMeasurable :
      ∀ alpha : Profile,
        AEStronglyMeasurable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (kernel_norm_le :
      ∀ alpha : Profile,
        ∀ᵐ xu ∂((profileMeasure alpha).prod userMeasure),
          ‖Function.uncurry kernel xu‖ ≤ C)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.ofProbabilityKernelAverageOfBounded
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue C kernel_aestronglyMeasurable kernel_norm_le uniform_gamma_eq
    kernel_user_integral_eq rho_le_gamma

noncomputable def ofProbabilityKernelAverageOfBoundedOfSupremum
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ) (C : ℝ)
    (kernel_aestronglyMeasurable :
      ∀ alpha : Profile,
        AEStronglyMeasurable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (kernel_norm_le :
      ∀ alpha : Profile,
        ∀ᵐ xu ∂((profileMeasure alpha).prod userMeasure),
          ‖Function.uncurry kernel xu‖ ≤ C)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_bddAbove :
      ∀ alpha : Profile,
        BddAbove
          (Set.range
            (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)))
    (gamma_eq_sSup_range :
      ∀ alpha : Profile,
        gamma alpha =
          sSup
            (Set.range
              (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha))) :
    Proposition4AveragingCertificate Profile User :=
  ofProbabilityKernelAverageOfBounded userMeasure profileMeasure
    profile_probability gamma kernel uniformProfile uniformValue C
    kernel_aestronglyMeasurable kernel_norm_le uniform_gamma_eq
    kernel_user_integral_eq
    (kernelIntegral_le_gamma_of_gamma_eq_sSup_range
      profileMeasure gamma kernel rho_bddAbove gamma_eq_sSup_range)

/--
The abstract averaging step from Proposition 4, forwarded through the
paper-facing namespace.
-/
theorem uniform_minimizes {Profile User : Type*}
    (C : Proposition4AveragingCertificate Profile User) :
    ∀ alpha : Profile, C.gamma C.uniformProfile ≤ C.gamma alpha :=
  AppliedModelingLib.Optimization.AveragingMinimizationCertificate.uniform_minimizes C

end Proposition4AveragingCertificate

end PRPKG24AccuracyDiversity

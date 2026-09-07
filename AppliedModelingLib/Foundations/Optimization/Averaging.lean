import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.Foundations.Optimization.Certificate
import AppliedModelingLib.Foundations.Probability.Symmetry
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod

namespace AppliedModelingLib
namespace Optimization

open MeasureTheory
open scoped BigOperators

/-!
# Averaging Certificates

This file packages a common continuous-probability optimization argument.  If
a reference profile has objective value equal to the average user-level value,
every profile has the same user-level average, some user reaches at least that
average, and the objective dominates all user-level values, then the reference
profile minimizes the objective.
-/

/--
Abstract averaging certificate for proving that a reference profile minimizes
an objective.

`rho alpha u` is a user-level value attached to profile `alpha`, while `gamma`
is the objective being minimized.  The certificate records that the reference
profile has value `uniformValue`, every profile has the same user average
`uniformValue`, some user reaches at least that average, and `gamma alpha`
dominates each user-level value.
-/
structure AveragingMinimizationCertificate (Profile User : Type*) where
  gamma : Profile → ℝ
  rho : Profile → User → ℝ
  uniformProfile : Profile
  uniformValue : ℝ
  average : (User → ℝ) → ℝ
  uniform_gamma_eq : gamma uniformProfile = uniformValue
  average_rho_eq_uniformValue : ∀ alpha : Profile, average (rho alpha) = uniformValue
  average_le_rho_witness :
    ∀ alpha : Profile, ∃ u : User, average (rho alpha) ≤ rho alpha u
  rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha

namespace AveragingMinimizationCertificate

/--
Finite-user constructor for an averaging-minimization certificate.

For finite nonempty user spaces, the average-to-witness field follows from the
elementary fact that a nonempty finite average is no larger than at least one
summand.
-/
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
    AveragingMinimizationCertificate Profile User where
  gamma := gamma
  rho := rho
  uniformProfile := uniformProfile
  uniformValue := uniformValue
  average :=
    fun f => (∑ u : User, f u) / (Fintype.card User : ℝ)
  uniform_gamma_eq := uniform_gamma_eq
  average_rho_eq_uniformValue := average_rho_eq_uniformValue
  average_le_rho_witness := by
    intro alpha
    exact AppliedModelingLib.FiniteSum.exists_fintype_average_le
      (fun u : User => rho alpha u)
  rho_le_gamma := rho_le_gamma

/--
Probability-measure constructor for an averaging-minimization certificate.

This is the continuous-user analogue of `ofFiniteUniformAverage`: once the
source proves that the user-level value is integrable and has the reference
profile's integral for every profile, mathlib's first-moment method supplies a
user whose value is at least the integral.
-/
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
    AveragingMinimizationCertificate Profile User where
  gamma := gamma
  rho := rho
  uniformProfile := uniformProfile
  uniformValue := uniformValue
  average := fun f => ∫ u, f u ∂userMeasure
  uniform_gamma_eq := uniform_gamma_eq
  average_rho_eq_uniformValue := integral_rho_eq_uniformValue
  average_le_rho_witness := by
    intro alpha
    exact MeasureTheory.exists_integral_le (rho_integrable alpha)
  rho_le_gamma := rho_le_gamma

/--
Kernel-average constructor for an averaging-minimization certificate.

This packages a common Fubini/symmetry step: if each item/profile point has the
same user integral and profile measures are probabilities, then every profile
has the same average user-level value.
-/
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
    AveragingMinimizationCertificate Profile User :=
  ofProbabilityIntegralAverage userMeasure gamma
    (fun alpha u => ∫ x, kernel x u ∂profileMeasure alpha)
    uniformProfile uniformValue rho_integrable uniform_gamma_eq
    (by
      intro alpha
      haveI : IsProbabilityMeasure (profileMeasure alpha) :=
        profile_probability alpha
      calc
        (∫ u, (∫ x, kernel x u ∂profileMeasure alpha) ∂userMeasure)
            = ∫ x, (∫ u, kernel x u ∂userMeasure) ∂profileMeasure alpha :=
              integral_kernel_swap alpha
        _ = ∫ _x : Item, uniformValue ∂profileMeasure alpha := by
              simp [kernel_user_integral_eq]
        _ = uniformValue := by
              simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ])
    rho_le_gamma

/--
Product-integrable kernel-average constructor.

This is the Fubini-ready form: product integrability of the item/user kernel
gives the user-level integrability and swaps the item/user integrals.
-/
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
    AveragingMinimizationCertificate Profile User :=
  ofProbabilityKernelAverage userMeasure profileMeasure profile_probability
    gamma kernel uniformProfile uniformValue
    (by
      intro alpha
      haveI : IsProbabilityMeasure (profileMeasure alpha) :=
        profile_probability alpha
      simpa [Function.uncurry] using
        (kernel_integrable alpha).integral_prod_right)
    uniform_gamma_eq
    (by
      intro alpha
      have hswap :=
        MeasureTheory.integral_integral_swap
          (μ := profileMeasure alpha) (ν := userMeasure)
          (f := kernel) (kernel_integrable alpha)
      simpa using hswap.symm)
    kernel_user_integral_eq rho_le_gamma

/--
Symmetry-driven product-integrable kernel-average constructor.

A transitive item action and a measure-preserving user action make a
diagonally invariant kernel have the same user integral at every item. Product
integrability still supplies Fubini.
-/
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
    AveragingMinimizationCertificate Profile User :=
  ofProbabilityKernelAverageOfIntegrable userMeasure profileMeasure
    profile_probability gamma kernel uniformProfile uniformValue
    kernel_integrable uniform_gamma_eq
    (by
      intro x
      calc
        (∫ u, kernel x u ∂userMeasure)
            = ∫ u, kernel anchor u ∂userMeasure :=
              AppliedModelingLib.Probability.integral_kernel_eq_anchor_of_transitive_diagonal_invariance
                userMeasure userAction itemAction kernel anchor
                userAction_measurePreserving userAction_measurableEmbedding
                kernel_diagonal_invariant itemAction_transitive x
        _ = uniformValue := anchor_integral_eq_uniformValue)
    rho_le_gamma

/--
Bounded-kernel constructor for an averaging-minimization certificate.

Product-measurability plus an a.e. real bound gives product integrability.
-/
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
    AveragingMinimizationCertificate Profile User :=
  ofProbabilityKernelAverageOfIntegrable userMeasure profileMeasure
    profile_probability gamma kernel uniformProfile uniformValue
    (by
      intro alpha
      haveI : IsProbabilityMeasure (profileMeasure alpha) :=
        profile_probability alpha
      exact Integrable.of_bound
        (kernel_aestronglyMeasurable alpha) C (kernel_norm_le alpha))
    uniform_gamma_eq kernel_user_integral_eq rho_le_gamma

/--
If every profile has the reference average user-level value and the objective
dominates user-level values, the reference profile is a global minimizer.
This is the certificate's reusable optimization endpoint.
-/
theorem isGlobalMinimizer {Profile User : Type*}
    (C : AveragingMinimizationCertificate Profile User) :
    IsGlobalMinimizer C.gamma C.uniformProfile := by
  intro alpha
  rw [C.uniform_gamma_eq]
  obtain ⟨u, hu⟩ := C.average_le_rho_witness alpha
  rw [C.average_rho_eq_uniformValue alpha] at hu
  exact le_trans hu (C.rho_le_gamma alpha u)

/--
Pointwise compatibility form of `isGlobalMinimizer` for existing paper-facing
endpoints.
-/
theorem uniform_minimizes {Profile User : Type*}
    (C : AveragingMinimizationCertificate Profile User) :
    ∀ alpha : Profile, C.gamma C.uniformProfile ≤ C.gamma alpha :=
  C.isGlobalMinimizer

end AveragingMinimizationCertificate

end Optimization
end AppliedModelingLib

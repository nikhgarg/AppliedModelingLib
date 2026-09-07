import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import AppliedModelingLib.Applications.RatingSystems.BinaryRating
import AppliedModelingLib.Foundations.Probability.FinsetVariance
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

namespace MBJG25ProducerFairness
namespace Responsive

/--
Selection Rate (SR) for a product $v$.
Defined in the responsive market section as the expected number of times selected
divided by its lifespan. We parameterize this directly.
-/
noncomputable def selectionRate (selections : ℝ) (lifespan : ℝ) : ℝ :=
  selections / lifespan

/--
Individual Producer Unfairness.
Defined as the standard deviation in Selection Rate (SR) among producers with
the same true quality `q`. The source leaves the finite-sample divisor implicit;
`finsetVariance` uses the empirical-distribution (`1 / |S|`) convention.
-/
noncomputable def producerUnfairnessVariance
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  let S := Finset.univ.filter (fun v => q_v v = q)
  AppliedModelingLib.Statistics.finsetVariance S (fun v => selectionRate (selections v) (lifespan v))

/--
Individual Producer Unfairness.
The standard deviation counterpart.
-/
noncomputable def producerUnfairness
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  Real.sqrt (producerUnfairnessVariance selections lifespan q_v q)

/-- Finite bias--variance decomposition for one conditional rating law. -/
theorem finite_bias_variance_decomposition
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (X : Ω → ℝ) (q : ℝ) :
    AppliedModelingLib.pmfExp μ (fun ω => (X ω - q) ^ 2) =
      (AppliedModelingLib.pmfExp μ X - q) ^ 2 +
        AppliedModelingLib.pmfExp μ (fun ω =>
          (X ω - AppliedModelingLib.pmfExp μ X) ^ 2) := by
  let mean := AppliedModelingLib.pmfExp μ X
  have hpoint :
      (fun ω => (X ω - q) ^ 2) =
        (fun ω =>
          (X ω - mean) ^ 2 +
            (2 * (mean - q)) * (X ω - mean) + (mean - q) ^ 2) := by
    funext ω
    ring
  rw [hpoint, AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_add,
    AppliedModelingLib.pmfExp_const_mul, AppliedModelingLib.pmfExp_sub,
    AppliedModelingLib.pmfExp_const, AppliedModelingLib.pmfExp_const]
  change _ = (mean - q) ^ 2 + _
  ring

/--
Mean Squared Error (MSE) decomposition in the responsive setting.
As shown in Appendix C, when the number of reviews $N$ is a random variable,
the expected MSE conditional on true quality $q_v$ decomposes into the expected
squared bias and the expected variance over the random variable $N$.
-/
theorem paper_responsive_mse_decomposition
    {α Ω : Type*} [Fintype α] [DecidableEq α]
    [Fintype Ω] [DecidableEq Ω]
    {alpha beta eta q_v : ℝ}
    (state_dist : PMF α)
    (rating_dist : α → PMF Ω)
    (N : α → ℝ)
    (posterior_rating : α → Ω → ℝ)
    (h_cond_mean : ∀ s,
      AppliedModelingLib.pmfExp (rating_dist s) (posterior_rating s) =
      AppliedModelingLib.Statistics.priorWeightedPosteriorMean alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      AppliedModelingLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω -
          AppliedModelingLib.pmfExp (rating_dist s) (posterior_rating s)) ^ 2) =
      AppliedModelingLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) :
    AppliedModelingLib.pmfExp state_dist (fun s =>
      AppliedModelingLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω - q_v) ^ 2)) =
      AppliedModelingLib.pmfExp state_dist (fun s =>
        AppliedModelingLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v) +
      AppliedModelingLib.pmfExp state_dist (fun s =>
        AppliedModelingLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) := by
  have h_eq : ∀ s,
      AppliedModelingLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω - q_v) ^ 2) =
      AppliedModelingLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v +
      AppliedModelingLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v := by
    intro s
    have h := finite_bias_variance_decomposition
      (rating_dist s) (posterior_rating s) q_v
    rw [h_cond_var s, h_cond_mean s] at h
    simpa [AppliedModelingLib.Statistics.priorWeightedSquaredBias,
      AppliedModelingLib.Statistics.priorWeightedBias] using h
  simp only [h_eq]
  exact AppliedModelingLib.pmfExp_add state_dist _ _

end Responsive
end MBJG25ProducerFairness

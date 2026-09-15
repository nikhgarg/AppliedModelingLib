import AppliedModelingLib.Foundations.Optimization.ProjectedSubgradient
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Stochastic Subgradient Method

Reusable probability lemmas for finite-dimensional stochastic projected
subgradient methods.  The deterministic update estimates live in
`ProjectedSubgradient`; this file supplies the conditional-expectation and
martingale ingredients needed to turn them into almost-sure statements.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory NNReal ENNReal

namespace AppliedModelingLib
namespace Optimization

/-- A finite Euclidean dot product of strongly measurable coordinate processes is strongly measurable. -/
theorem stronglyMeasurable_finiteDot
    {Omega Coord : Type*} {m : MeasurableSpace Omega} [Fintype Coord]
    (f g : Coord → Omega → ℝ)
    (hf : ∀ i, StronglyMeasurable[m] (f i))
    (hg : ∀ i, StronglyMeasurable[m] (g i)) :
    StronglyMeasurable[m]
      (fun omega => FiniteDimensionalNorms.dot (fun i => f i omega) (fun i => g i omega)) := by
  convert Finset.stronglyMeasurable_sum (Finset.univ : Finset Coord)
    (fun i _hi => (hf i).mul (hg i)) using 1
  funext omega
  simp [FiniteDimensionalNorms.dot]

/-- The squared Euclidean norm of a finite-coordinate process is strongly measurable. -/
theorem stronglyMeasurable_finiteL2Sq
    {Omega Coord : Type*} {m : MeasurableSpace Omega} [Fintype Coord]
    (f : Coord → Omega → ℝ)
    (hf : ∀ i, StronglyMeasurable[m] (f i)) :
    StronglyMeasurable[m]
      (fun omega => FiniteDimensionalNorms.l2Sq (fun i => f i omega)) := by
  convert Finset.stronglyMeasurable_sum (Finset.univ : Finset Coord)
    (fun i _hi => (hf i).pow 2) using 1
  funext omega
  simp [FiniteDimensionalNorms.l2Sq]

/-- A finite Euclidean dot product of two strongly adapted coordinate processes is strongly adapted. -/
theorem stronglyAdapted_finiteDot
    {Omega Coord : Type*} {m : MeasurableSpace Omega} [Fintype Coord]
    (filtration : Filtration (Ω := Omega) ℕ m)
    (f g : ℕ → Coord → Omega → ℝ)
    (hf : ∀ i, StronglyAdapted filtration (fun t omega => f t i omega))
    (hg : ∀ i, StronglyAdapted filtration (fun t omega => g t i omega)) :
    StronglyAdapted filtration
      (fun t omega =>
        FiniteDimensionalNorms.dot (fun i => f t i omega) (fun i => g t i omega)) := by
  intro t
  exact stronglyMeasurable_finiteDot
    (fun i omega => f t i omega) (fun i omega => g t i omega)
    (fun i => hf i t) (fun i => hg i t)

/-- The squared Euclidean norm of a coordinatewise adapted process is adapted. -/
theorem stronglyAdapted_finiteL2Sq
    {Omega Coord : Type*} {m : MeasurableSpace Omega} [Fintype Coord]
    (filtration : Filtration (Ω := Omega) ℕ m)
    (f : ℕ → Coord → Omega → ℝ)
    (hf : ∀ i, StronglyAdapted filtration (fun t omega => f t i omega)) :
    StronglyAdapted filtration
      (fun t omega => FiniteDimensionalNorms.l2Sq (fun i => f t i omega)) := by
  intro t
  exact stronglyMeasurable_finiteL2Sq
    (fun i omega => f t i omega) (fun i => hf i t)

/--
An adapted finite-coordinate pairing with conditionally mean-zero noise has
conditional expectation zero.  The product-integrability assumptions keep this
lemma usable with either bounded or square-integrable noise models.
-/
theorem condExp_finiteDot_eq_zero_of_coordinatewise
    {Omega Coord : Type*} {mOmega m : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsFiniteMeasure mu] [Fintype Coord]
    (weight noise : Coord → Omega → ℝ)
    (hweight : ∀ i, StronglyMeasurable[m] (weight i))
    (hproduct : ∀ i, Integrable (fun omega => weight i omega * noise i omega) mu)
    (hnoise : ∀ i, Integrable (noise i) mu)
    (hmean_zero : ∀ i, mu[noise i | m] =ᵐ[mu] 0) :
    mu[fun omega =>
      FiniteDimensionalNorms.dot (fun i => noise i omega) (fun i => weight i omega)
      | m] =ᵐ[mu] 0 := by
  classical
  have hterms : ∀ i,
      mu[fun omega => weight i omega * noise i omega | m] =ᵐ[mu] 0 := by
    intro i
    filter_upwards [condExp_mul_of_stronglyMeasurable_left
      (hweight i) (hproduct i) (hnoise i), hmean_zero i] with omega hpull hzero
    simpa [Pi.mul_apply, hzero] using hpull
  have hsum := MeasureTheory.condExp_finset_sum
    (μ := mu) (s := (Finset.univ : Finset Coord))
    (f := fun i omega => weight i omega * noise i omega)
    (fun i _hi => hproduct i) m
  calc
    mu[fun omega =>
        FiniteDimensionalNorms.dot (fun i => noise i omega) (fun i => weight i omega)
        | m] =ᵐ[mu]
        mu[∑ i : Coord, fun omega => weight i omega * noise i omega | m] := by
          apply condExp_congr_ae
          filter_upwards [] with omega
          simp only [FiniteDimensionalNorms.dot, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ =ᵐ[mu] ∑ i : Coord, mu[fun omega => weight i omega * noise i omega | m] := hsum
    _ =ᵐ[mu] 0 := by
      filter_upwards [(Finset.eventually_all (Finset.univ : Finset Coord)).2
        (fun i _hi => hterms i)] with omega homega
      simp [homega]

/--
An almost-sure Euclidean bound on a finite-dimensional noise vector gives the
conditional squared-moment bound required by projected stochastic-gradient
descent.  This is useful when an oracle is uniformly bounded; it deliberately
does not infer a second moment from a first-moment hypothesis alone.
-/
theorem condExp_l2Sq_le_of_ae_l2_le
    {Omega Coord : Type*} {mOmega m : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsFiniteMeasure mu] [Fintype Coord]
    (noise : Omega → Coord → ℝ) (K : ℝ) (hm : m ≤ mOmega)
    (hK : 0 ≤ K)
    (hnoise_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise omega)) mu)
    (hbound : ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (noise omega) ≤ K) :
    mu[fun omega => FiniteDimensionalNorms.l2Sq (noise omega) | m] ≤ᵐ[mu]
      fun _ => K ^ 2 := by
  have hpoint : (fun omega => FiniteDimensionalNorms.l2Sq (noise omega)) ≤ᵐ[mu]
      fun _ => K ^ 2 := by
    filter_upwards [hbound] with omega homega
    rw [← Real.sq_sqrt (FiniteDimensionalNorms.normL2Sq_nonneg _)]
    exact (sq_le_sq₀ (FiniteDimensionalNorms.normL2_nonneg _) hK).mpr homega
  calc
    mu[fun omega => FiniteDimensionalNorms.l2Sq (noise omega) | m] ≤ᵐ[mu]
        mu[fun _ : Omega => K ^ 2 | m] :=
      condExp_mono hnoise_integrable (integrable_const _) hpoint
    _ =ᵐ[mu] fun _ => K ^ 2 := by
      exact Filter.Eventually.of_forall fun omega =>
        congrFun (condExp_const (μ := mu) (m₀ := mOmega) hm (K ^ 2)) omega

/--
Conditional one-step descent for a finite-dimensional projected stochastic
subgradient update. The only random term remaining on the right is the
conditional noise energy; a conditionally mean-zero noise pairing vanishes.
-/
theorem conditional_l2Sq_projected_subgradient_noise_bias_step_le_bounded
    {Omega Coord : Type*} {mOmega m : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsFiniteMeasure mu] [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    {cost : (Coord → ℝ) → ℝ}
    {previous gradient noise : Omega → Coord → ℝ}
    {bias target : Coord → ℝ} {radius C distanceBound : ℝ}
    (hproject : SquaredDistanceNonexpansiveOn X project)
    (hm : m ≤ mOmega) (htarget : target ∈ X) (hradius : 0 ≤ radius)
    (hprevious_measurable : ∀ i, StronglyMeasurable[m] (fun omega => previous omega i))
    (hgap_measurable : StronglyMeasurable[m]
      (fun omega => cost (previous omega) - cost target))
    (hprevious_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => previous omega i - target i)) mu)
    (hgap_integrable : Integrable
      (fun omega => cost (previous omega) - cost target) mu)
    (hnoise_dot_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.dot (noise omega)
        (fun i => previous omega i - target i)) mu)
    (hnoise_energy_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise omega)) mu)
    (hnoise_dot_zero :
      mu[fun omega => FiniteDimensionalNorms.dot (noise omega)
        (fun i => previous omega i - target i) | m] =ᵐ[mu] 0)
    (hsubgradient : ∀ᵐ omega ∂mu,
      FiniteSubgradientOn cost X (previous omega) (gradient omega))
    (hgradient_bound : ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (gradient omega) ≤ C)
    (hdistance_bound : ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (fun i => previous omega i - target i) ≤ distanceBound)
    (hnext_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous omega j - radius *
          (gradient omega j + noise omega j + bias j)) i - target i)) mu) :
    mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous omega j - radius *
          (gradient omega j + noise omega j + bias j)) i - target i) | m] ≤ᵐ[mu]
      fun omega =>
        FiniteDimensionalNorms.l2Sq (fun i => previous omega i - target i) -
          2 * radius * (cost (previous omega) - cost target) +
          2 * radius * distanceBound * FiniteDimensionalNorms.l2 bias +
          3 * radius ^ 2 *
            (C ^ 2 +
              mu[fun omega => FiniteDimensionalNorms.l2Sq (noise omega) | m] omega +
              FiniteDimensionalNorms.l2Sq bias) := by
  let potential : Omega → ℝ := fun omega =>
    FiniteDimensionalNorms.l2Sq (fun i => previous omega i - target i)
  let gap : Omega → ℝ := fun omega => cost (previous omega) - cost target
  let noiseDot : Omega → ℝ := fun omega =>
    FiniteDimensionalNorms.dot (noise omega)
      (fun i => previous omega i - target i)
  let noiseEnergy : Omega → ℝ := fun omega =>
    FiniteDimensionalNorms.l2Sq (noise omega)
  let deterministic : Omega → ℝ := fun omega =>
    potential omega - 2 * radius * gap omega +
      2 * radius * distanceBound * FiniteDimensionalNorms.l2 bias +
      3 * radius ^ 2 * (C ^ 2 + FiniteDimensionalNorms.l2Sq bias)
  let stochastic : Omega → ℝ := fun omega =>
    -(2 * radius) * noiseDot omega + 3 * radius ^ 2 * noiseEnergy omega
  have hpotential_measurable : StronglyMeasurable[m] potential := by
    dsimp [potential]
    exact stronglyMeasurable_finiteL2Sq
      (fun i omega => previous omega i - target i)
      (fun i => (hprevious_measurable i).sub stronglyMeasurable_const)
  have hdeterministic_measurable : StronglyMeasurable[m] deterministic := by
    dsimp [deterministic]
    exact (((hpotential_measurable.sub
      (hgap_measurable.const_mul (2 * radius))).add stronglyMeasurable_const).add
        stronglyMeasurable_const)
  have hdeterministic_integrable : Integrable deterministic mu := by
    dsimp [deterministic]
    exact (((hprevious_integrable.sub
      (hgap_integrable.const_mul (2 * radius))).add (integrable_const _)).add
        (integrable_const _))
  have hstochastic_integrable : Integrable stochastic mu := by
    dsimp [stochastic]
    exact (hnoise_dot_integrable.const_mul (-(2 * radius))).add
      (hnoise_energy_integrable.const_mul (3 * radius ^ 2))
  have hrhs_integrable : Integrable (fun omega =>
      deterministic omega + stochastic omega) mu :=
    hdeterministic_integrable.add hstochastic_integrable
  have hpoint :
      (fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => project (fun j => previous omega j - radius *
            (gradient omega j + noise omega j + bias j)) i - target i)) ≤ᵐ[mu]
        fun omega => deterministic omega + stochastic omega := by
    filter_upwards [hsubgradient, hgradient_bound, hdistance_bound] with omega hsub hgrad hdist
    have hstep := l2Sq_projected_subgradient_noise_bias_step_le_bounded
      (noise := noise omega) (bias := bias) hproject hsub htarget hradius hgrad hdist
    dsimp [deterministic, stochastic, potential, gap, noiseDot, noiseEnergy]
    nlinarith
  calc
    mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous omega j - radius *
          (gradient omega j + noise omega j + bias j)) i - target i) | m] ≤ᵐ[mu]
        mu[fun omega => deterministic omega + stochastic omega | m] :=
      condExp_mono hnext_integrable hrhs_integrable hpoint
    _ =ᵐ[mu] mu[deterministic | m] + mu[stochastic | m] :=
      condExp_add hdeterministic_integrable hstochastic_integrable m
    _ =ᵐ[mu] deterministic + mu[stochastic | m] := by
      rw [condExp_of_stronglyMeasurable hm hdeterministic_measurable
        hdeterministic_integrable]
    _ =ᵐ[mu] deterministic +
        (fun omega => -(2 * radius) * 0 +
          3 * radius ^ 2 * mu[noiseEnergy | m] omega) := by
      have hstochastic_cond :
          mu[stochastic | m] =ᵐ[mu]
            fun omega => -(2 * radius) * 0 +
              3 * radius ^ 2 * mu[noiseEnergy | m] omega := by
        calc
          mu[stochastic | m] =ᵐ[mu]
              mu[((-(2 * radius)) • noiseDot) +
                ((3 * radius ^ 2) • noiseEnergy) | m] := by
            apply condExp_congr_ae
            filter_upwards [] with omega
            simp [stochastic, Pi.smul_apply, smul_eq_mul]
          _ =ᵐ[mu]
              mu[(-(2 * radius)) • noiseDot | m] +
                mu[(3 * radius ^ 2) • noiseEnergy | m] :=
            condExp_add (hnoise_dot_integrable.const_mul (-(2 * radius)))
              (hnoise_energy_integrable.const_mul (3 * radius ^ 2)) m
          _ =ᵐ[mu]
              (-(2 * radius)) • mu[noiseDot | m] +
                (3 * radius ^ 2) • mu[noiseEnergy | m] := by
            exact (condExp_smul (-(2 * radius)) noiseDot m).add
              (condExp_smul (3 * radius ^ 2) noiseEnergy m)
          _ =ᵐ[mu] fun omega => -(2 * radius) * 0 +
                3 * radius ^ 2 * mu[noiseEnergy | m] omega := by
            filter_upwards [hnoise_dot_zero] with omega hzero
            have hzero' : mu[noiseDot | m] omega = 0 := by
              simpa [noiseDot] using hzero
            change -(2 * radius) * mu[noiseDot | m] omega +
                3 * radius ^ 2 * mu[noiseEnergy | m] omega =
              -(2 * radius) * 0 +
                3 * radius ^ 2 * mu[noiseEnergy | m] omega
            rw [hzero']
      exact (Filter.EventuallyEq.rfl : deterministic =ᵐ[mu] deterministic).add
        hstochastic_cond
    _ =ᵐ[mu] fun omega =>
        FiniteDimensionalNorms.l2Sq (fun i => previous omega i - target i) -
          2 * radius * (cost (previous omega) - cost target) +
          2 * radius * distanceBound * FiniteDimensionalNorms.l2 bias +
          3 * radius ^ 2 *
            (C ^ 2 +
              mu[fun omega => FiniteDimensionalNorms.l2Sq (noise omega) | m] omega +
              FiniteDimensionalNorms.l2Sq bias) := by
      filter_upwards [] with omega
      dsimp [deterministic, potential, gap, noiseEnergy]
      ring

/--
Conditional one-step descent with a sample-dependent perturbation.  Unlike a
deterministic bias, the perturbation need not be measurable with respect to
the current filtration: its nonnegative contribution remains inside the
conditional expectation and can subsequently be controlled by a rare-event or
conditional-moment estimate.
-/
theorem conditional_l2Sq_projected_subgradient_noise_perturbation_step_le
    {Omega Coord : Type*} {mOmega m : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsFiniteMeasure mu] [Fintype Coord]
    {X : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    {cost : (Coord → ℝ) → ℝ}
    {previous gradient noise perturbation : Omega → Coord → ℝ}
    {target : Coord → ℝ} {radius C distanceBound : ℝ}
    (hproject : SquaredDistanceNonexpansiveOn X project)
    (hm : m ≤ mOmega) (htarget : target ∈ X) (hradius : 0 ≤ radius)
    (hprevious_measurable : ∀ i, StronglyMeasurable[m] (fun omega => previous omega i))
    (hgap_measurable : StronglyMeasurable[m]
      (fun omega => cost (previous omega) - cost target))
    (hprevious_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => previous omega i - target i)) mu)
    (hgap_integrable : Integrable
      (fun omega => cost (previous omega) - cost target) mu)
    (hnoise_dot_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.dot (noise omega)
        (fun i => previous omega i - target i)) mu)
    (hnoise_energy_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise omega)) mu)
    (hperturbation_norm_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2 (perturbation omega)) mu)
    (hperturbation_energy_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (perturbation omega)) mu)
    (hnoise_dot_zero :
      mu[fun omega => FiniteDimensionalNorms.dot (noise omega)
        (fun i => previous omega i - target i) | m] =ᵐ[mu] 0)
    (hsubgradient : ∀ᵐ omega ∂mu,
      FiniteSubgradientOn cost X (previous omega) (gradient omega))
    (hgradient_bound : ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (gradient omega) ≤ C)
    (hdistance_bound : ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (fun i => previous omega i - target i) ≤ distanceBound)
    (hnext_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous omega j - radius *
          (gradient omega j + noise omega j + perturbation omega j)) i - target i)) mu) :
    mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous omega j - radius *
          (gradient omega j + noise omega j + perturbation omega j)) i - target i) | m] ≤ᵐ[mu]
      fun omega =>
        FiniteDimensionalNorms.l2Sq (fun i => previous omega i - target i) -
          2 * radius * (cost (previous omega) - cost target) +
          3 * radius ^ 2 *
            (C ^ 2 + mu[fun omega =>
              FiniteDimensionalNorms.l2Sq (noise omega) | m] omega) +
          mu[fun omega =>
            2 * radius * distanceBound * FiniteDimensionalNorms.l2 (perturbation omega) +
              3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (perturbation omega) | m] omega := by
  let potential : Omega → ℝ := fun omega =>
    FiniteDimensionalNorms.l2Sq (fun i => previous omega i - target i)
  let gap : Omega → ℝ := fun omega => cost (previous omega) - cost target
  let noiseDot : Omega → ℝ := fun omega =>
    FiniteDimensionalNorms.dot (noise omega)
      (fun i => previous omega i - target i)
  let noiseEnergy : Omega → ℝ := fun omega =>
    FiniteDimensionalNorms.l2Sq (noise omega)
  let perturbationError : Omega → ℝ := fun omega =>
    2 * radius * distanceBound * FiniteDimensionalNorms.l2 (perturbation omega) +
      3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (perturbation omega)
  let deterministic : Omega → ℝ := fun omega =>
    potential omega - 2 * radius * gap omega + 3 * radius ^ 2 * C ^ 2
  let stochastic : Omega → ℝ := fun omega =>
    -(2 * radius) * noiseDot omega + 3 * radius ^ 2 * noiseEnergy omega
  have hpotential_measurable : StronglyMeasurable[m] potential := by
    dsimp [potential]
    exact stronglyMeasurable_finiteL2Sq
      (fun i omega => previous omega i - target i)
      (fun i => (hprevious_measurable i).sub stronglyMeasurable_const)
  have hdeterministic_measurable : StronglyMeasurable[m] deterministic := by
    dsimp [deterministic]
    exact ((hpotential_measurable.sub
      (hgap_measurable.const_mul (2 * radius))).add stronglyMeasurable_const)
  have hdeterministic_integrable : Integrable deterministic mu := by
    dsimp [deterministic]
    exact (hprevious_integrable.sub
      (hgap_integrable.const_mul (2 * radius))).add (integrable_const _)
  have hstochastic_integrable : Integrable stochastic mu := by
    dsimp [stochastic]
    exact (hnoise_dot_integrable.const_mul (-(2 * radius))).add
      (hnoise_energy_integrable.const_mul (3 * radius ^ 2))
  have hperturbationError_integrable : Integrable perturbationError mu := by
    dsimp [perturbationError]
    exact (hperturbation_norm_integrable.const_mul (2 * radius * distanceBound)).add
      (hperturbation_energy_integrable.const_mul (3 * radius ^ 2))
  have hrhs_integrable : Integrable (fun omega =>
      (deterministic omega + stochastic omega) + perturbationError omega) mu :=
    (hdeterministic_integrable.add hstochastic_integrable).add
      hperturbationError_integrable
  have hpoint :
      (fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => project (fun j => previous omega j - radius *
            (gradient omega j + noise omega j + perturbation omega j)) i - target i)) ≤ᵐ[mu]
        fun omega => (deterministic omega + stochastic omega) + perturbationError omega := by
    filter_upwards [hsubgradient, hgradient_bound, hdistance_bound] with omega hsub hgrad hdist
    have hstep := l2Sq_projected_subgradient_noise_bias_step_le_bounded
      (noise := noise omega) (bias := perturbation omega)
      hproject hsub htarget hradius hgrad hdist
    dsimp [deterministic, stochastic, perturbationError, potential, gap, noiseDot, noiseEnergy]
    nlinarith
  calc
    mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => previous omega j - radius *
          (gradient omega j + noise omega j + perturbation omega j)) i - target i) | m] ≤ᵐ[mu]
        mu[fun omega =>
          (deterministic omega + stochastic omega) + perturbationError omega | m] :=
      condExp_mono hnext_integrable hrhs_integrable hpoint
    _ =ᵐ[mu] mu[fun omega => deterministic omega + stochastic omega | m] +
        mu[perturbationError | m] :=
      condExp_add (hdeterministic_integrable.add hstochastic_integrable)
        hperturbationError_integrable m
    _ =ᵐ[mu] mu[deterministic | m] + mu[stochastic | m] +
        mu[perturbationError | m] := by
      exact (condExp_add hdeterministic_integrable hstochastic_integrable m).add
        Filter.EventuallyEq.rfl
    _ =ᵐ[mu] deterministic + mu[stochastic | m] +
        mu[perturbationError | m] := by
      rw [condExp_of_stronglyMeasurable hm hdeterministic_measurable
        hdeterministic_integrable]
    _ =ᵐ[mu] deterministic +
        (fun omega => -(2 * radius) * 0 +
          3 * radius ^ 2 * mu[noiseEnergy | m] omega) +
        mu[perturbationError | m] := by
      have hstochastic_cond :
          mu[stochastic | m] =ᵐ[mu]
            fun omega => -(2 * radius) * 0 +
              3 * radius ^ 2 * mu[noiseEnergy | m] omega := by
        calc
          mu[stochastic | m] =ᵐ[mu]
              mu[((-(2 * radius)) • noiseDot) +
                ((3 * radius ^ 2) • noiseEnergy) | m] := by
            apply condExp_congr_ae
            filter_upwards [] with omega
            simp [stochastic, Pi.smul_apply, smul_eq_mul]
          _ =ᵐ[mu]
              mu[(-(2 * radius)) • noiseDot | m] +
                mu[(3 * radius ^ 2) • noiseEnergy | m] :=
            condExp_add (hnoise_dot_integrable.const_mul (-(2 * radius)))
              (hnoise_energy_integrable.const_mul (3 * radius ^ 2)) m
          _ =ᵐ[mu]
              (-(2 * radius)) • mu[noiseDot | m] +
                (3 * radius ^ 2) • mu[noiseEnergy | m] := by
            exact (condExp_smul (-(2 * radius)) noiseDot m).add
              (condExp_smul (3 * radius ^ 2) noiseEnergy m)
          _ =ᵐ[mu] fun omega => -(2 * radius) * 0 +
                3 * radius ^ 2 * mu[noiseEnergy | m] omega := by
            filter_upwards [hnoise_dot_zero] with omega hzero
            have hzero' : mu[noiseDot | m] omega = 0 := by
              simpa [noiseDot] using hzero
            change -(2 * radius) * mu[noiseDot | m] omega +
                3 * radius ^ 2 * mu[noiseEnergy | m] omega =
              -(2 * radius) * 0 +
                3 * radius ^ 2 * mu[noiseEnergy | m] omega
            rw [hzero']
      exact ((Filter.EventuallyEq.rfl : deterministic =ᵐ[mu] deterministic).add
        hstochastic_cond).add Filter.EventuallyEq.rfl
    _ =ᵐ[mu] fun omega =>
        FiniteDimensionalNorms.l2Sq (fun i => previous omega i - target i) -
          2 * radius * (cost (previous omega) - cost target) +
          3 * radius ^ 2 *
            (C ^ 2 + mu[fun omega => FiniteDimensionalNorms.l2Sq (noise omega) | m] omega) +
          mu[fun omega =>
            2 * radius * distanceBound * FiniteDimensionalNorms.l2 (perturbation omega) +
              3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (perturbation omega) | m] omega := by
      filter_upwards [] with omega
      dsimp [deterministic, potential, gap, noiseEnergy, perturbationError]
      ring

/--
Turn conditional noise-energy and perturbation-error bounds into the
deterministic residual required by a Robbins--Siegmund descent argument.  This
small algebraic adapter is intentionally independent of how the rare-event
estimate producing `perturbationBound` is obtained.
-/
theorem conditional_l2Sq_descent_le_of_noise_and_perturbation_bounds
    {Omega : Type*} {mOmega m : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega}
    {potential gap noiseEnergy perturbationError : Omega → ℝ}
    {radius C noiseBound perturbationBound : ℝ}
    (hstep : mu[potential | m] ≤ᵐ[mu]
      fun omega => potential omega - 2 * radius * gap omega +
        3 * radius ^ 2 * (C ^ 2 + mu[noiseEnergy | m] omega) +
        mu[perturbationError | m] omega)
    (hnoise : mu[noiseEnergy | m] ≤ᵐ[mu] fun _ => noiseBound)
    (hperturbation : mu[perturbationError | m] ≤ᵐ[mu] fun _ => perturbationBound) :
    mu[potential | m] ≤ᵐ[mu]
      fun omega => potential omega - 2 * radius * gap omega +
        (3 * radius ^ 2 * (C ^ 2 + noiseBound) + perturbationBound) := by
  filter_upwards [hstep, hnoise, hperturbation] with omega hstep hnoise hperturbation
  nlinarith [sq_nonneg radius]

/--
A nonnegative linear combination of two conditionally bounded integrable
processes is conditionally bounded by the same combination of their bounds.
This is useful for converting separate first- and second-moment controls of a
random update perturbation into the single descent-error estimate.
-/
theorem condExp_linear_combination_le_of_bounds
    {Omega : Type*} {mOmega m : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} {f g : Omega → ℝ}
    {a b fBound gBound : ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf_bound : mu[f | m] ≤ᵐ[mu] fun _ => fBound)
    (hg_bound : mu[g | m] ≤ᵐ[mu] fun _ => gBound) :
    mu[fun omega => a * f omega + b * g omega | m] ≤ᵐ[mu]
      fun _ => a * fBound + b * gBound := by
  have hsplit : mu[fun omega => a * f omega + b * g omega | m] =ᵐ[mu]
      fun omega => a * mu[f | m] omega + b * mu[g | m] omega := by
    calc
      mu[fun omega => a * f omega + b * g omega | m] =ᵐ[mu]
          mu[(a • f) + (b • g) | m] := by
            filter_upwards [] with omega
            rfl
      _ =ᵐ[mu] mu[a • f | m] + mu[b • g | m] :=
        condExp_add (hf.const_mul a) (hg.const_mul b) m
      _ =ᵐ[mu] (a • mu[f | m]) + (b • mu[g | m]) := by
        exact (condExp_smul a f m).add (condExp_smul b g m)
      _ =ᵐ[mu] fun omega => a * mu[f | m] omega + b * mu[g | m] omega := by
        filter_upwards [] with omega
        rfl
  filter_upwards [hsplit, hf_bound, hg_bound] with omega hsplit hf_bound hg_bound
  rw [hsplit]
  nlinarith


/--
Square-summable deterministic weights turn a conditionally bounded nonnegative
error process into an almost-surely summable error series. This is the
non-martingale error term in stochastic projected-subgradient descent.
-/
theorem ae_summable_squared_error_of_condExp_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (radius : ℕ → ℝ) (energy : ℕ → Omega → ℝ) (C : ℝ)
    (henergy_integrable : ∀ t, Integrable (energy t) mu)
    (henergy_nonneg : ∀ t, 0 ≤ᵐ[mu] energy t)
    (hcond : ∀ t, mu[energy t | filtration t] ≤ᵐ[mu] fun _ => C)
    (hradius : Summable (fun t => radius (t + 1) ^ 2)) :
    ∀ᵐ omega ∂mu, Summable (fun t => radius (t + 1) ^ 2 * energy t omega) := by
  let error : ℕ → Omega → ℝ :=
    fun t omega => radius (t + 1) ^ 2 * energy t omega
  have hinterg : ∀ t, Integrable (error t) mu := by
    intro t
    exact (henergy_integrable t).const_mul (radius (t + 1) ^ 2)
  have hnonneg : ∀ t, 0 ≤ᵐ[mu] error t := by
    intro t
    filter_upwards [henergy_nonneg t] with omega homega
    dsimp [error]
    exact mul_nonneg (sq_nonneg _) homega
  apply AppliedModelingLib.ae_summable_of_summable_integral_of_nonneg
    (fun t => (hinterg t).aestronglyMeasurable) hinterg hnonneg
  have henergy_integral_le : ∀ t, (∫ omega, energy t omega ∂mu) ≤ C := by
    intro t
    calc
      (∫ omega, energy t omega ∂mu) =
          ∫ omega, mu[energy t | filtration t] omega ∂mu := by
            exact (integral_condExp (μ := mu) (f := energy t)
              (m := filtration t) (m₀ := mOmega) (filtration.le t)).symm
      _ ≤ ∫ _omega : Omega, C ∂mu := by
            apply integral_mono_ae
            · exact integrable_condExp
            · exact integrable_const C
            · exact hcond t
      _ = C := by simp
  have hbound : ∀ t,
      (∫ omega, error t omega ∂mu) ≤ radius (t + 1) ^ 2 * C := by
    intro t
    rw [show error t = fun omega => radius (t + 1) ^ 2 * energy t omega by rfl,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (henergy_integral_le t) (sq_nonneg _)
  have hsum_bound : Summable (fun t => radius (t + 1) ^ 2 * C) := by
    simpa [mul_comm] using hradius.mul_left C
  exact Summable.of_nonneg_of_le
    (fun t => integral_nonneg_of_ae (hnonneg t)) hbound hsum_bound

/--
Finite-dimensional specialization of
`ae_summable_squared_error_of_condExp_le` for squared Euclidean noise norms.
-/
theorem ae_summable_radius_sq_l2Sq_noise_of_condExp_le
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] [Fintype Coord]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (radius : ℕ → ℝ) (noise : ℕ → Omega → Coord → ℝ) (C : ℝ)
    (hnoise_integrable : ∀ t,
      Integrable (fun omega => FiniteDimensionalNorms.l2Sq (noise t omega)) mu)
    (hcond : ∀ t,
      mu[fun omega => FiniteDimensionalNorms.l2Sq (noise t omega) | filtration t]
        ≤ᵐ[mu] fun _ => C)
    (hradius : Summable (fun t => radius (t + 1) ^ 2)) :
    ∀ᵐ omega ∂mu,
      Summable (fun t => radius (t + 1) ^ 2 *
        FiniteDimensionalNorms.l2Sq (noise t omega)) := by
  apply ae_summable_squared_error_of_condExp_le filtration radius
    (fun t omega => FiniteDimensionalNorms.l2Sq (noise t omega)) C
    hnoise_integrable
  · intro t
    exact Filter.Eventually.of_forall fun omega =>
      FiniteDimensionalNorms.normL2Sq_nonneg (noise t omega)
  · exact hcond
  · exact hradius

/--
Uniformly bounded finite-dimensional noise has almost-summable squared energy
under square-summable step radii.  This packages the bounded-noise route to
the conditional-moment premise used by stochastic projected-subgradient
arguments.
-/
theorem ae_summable_radius_sq_l2Sq_noise_of_ae_l2_le
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] [Fintype Coord]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (radius : ℕ → ℝ) (noise : ℕ → Omega → Coord → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hnoise_integrable : ∀ t,
      Integrable (fun omega => FiniteDimensionalNorms.l2Sq (noise t omega)) mu)
    (hbound : ∀ t, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (noise t omega) ≤ K)
    (hradius : Summable (fun t => radius (t + 1) ^ 2)) :
    ∀ᵐ omega ∂mu,
      Summable (fun t => radius (t + 1) ^ 2 *
        FiniteDimensionalNorms.l2Sq (noise t omega)) := by
  apply ae_summable_radius_sq_l2Sq_noise_of_condExp_le
    filtration radius noise (K ^ 2) hnoise_integrable
  · intro t
    exact condExp_l2Sq_le_of_ae_l2_le (noise t) K (filtration.le t) hK
      (hnoise_integrable t) (hbound t)
  · exact hradius

/--
The summability half of the deterministic Robbins--Siegmund descent argument.
If a potential bounded below loses a nonnegative amount `c n` at each step,
up to a summable nonnegative error `b n`, then the cumulative losses are
summable.
-/
theorem summable_loss_of_bddBelow_descent
    {potential error loss : ℕ → ℝ}
    (hpotential_bdd : BddBelow (Set.range potential))
    (hloss_nonneg : ∀ n, 0 ≤ loss n)
    (hstep : ∀ n,
      potential (n + 1) ≤ potential n + error n - loss n)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n) :
    Summable loss := by
  rcases hpotential_bdd with ⟨lower, hlower⟩
  have hpotential_lower : ∀ n, lower ≤ potential n := by
    intro n
    exact hlower ⟨n, rfl⟩
  have hpartial : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, loss i) ≤
        potential 0 + (∑ i ∈ Finset.range n, error i) - potential n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hstep' := hstep n
        nlinarith
  refine summable_of_sum_range_le hloss_nonneg
    (c := potential 0 + ∑' i, error i - lower) ?_
  intro n
  calc
    (∑ i ∈ Finset.range n, loss i) ≤
        potential 0 + (∑ i ∈ Finset.range n, error i) - potential n := hpartial n
    _ ≤ potential 0 + (∑ i ∈ Finset.range n, error i) - lower := by
      linarith [hpotential_lower n]
    _ ≤ potential 0 + ∑' i, error i - lower := by
      gcongr
      exact herror.sum_le_tsum (Finset.range n) (fun i _hi => herror_nonneg i)

/--
Nonnegative potentials are a common special case of
`summable_loss_of_bddBelow_descent`.
-/
theorem summable_loss_of_nonnegative_descent
    {potential error loss : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, 0 ≤ potential n)
    (hloss_nonneg : ∀ n, 0 ≤ loss n)
    (hstep : ∀ n,
      potential (n + 1) ≤ potential n + error n - loss n)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n) :
    Summable loss := by
  apply summable_loss_of_bddBelow_descent
    (potential := potential) (error := error) (loss := loss)
  · refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hpotential_nonneg n
  · exact hloss_nonneg
  · exact hstep
  · exact herror
  · exact herror_nonneg

/--
Pathwise descent remains summable when its additional increments have uniformly
upper-bounded partial sums.  This is the deterministic handoff used after a
martingale partial-sum convergence theorem has controlled the noise term.
-/
theorem summable_loss_of_nonnegative_descent_add_increment
    {potential error loss increment : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, 0 ≤ potential n)
    (hloss_nonneg : ∀ n, 0 ≤ loss n)
    (hstep : ∀ n,
      potential (n + 1) ≤
        potential n + error n - loss n + increment n)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n)
    (hincrement_upper : ∃ upper : ℝ,
      ∀ n : ℕ, (∑ i ∈ Finset.range n, increment i) ≤ upper) :
    Summable loss := by
  rcases hincrement_upper with ⟨upper, hupper⟩
  let adjusted : ℕ → ℝ :=
    fun n => potential n - ∑ i ∈ Finset.range n, increment i
  have hadjusted_bdd : BddBelow (Set.range adjusted) := by
    refine ⟨-upper, ?_⟩
    rintro x ⟨n, rfl⟩
    dsimp [adjusted]
    linarith [hpotential_nonneg n, hupper n]
  have hadjusted_step : ∀ n,
      adjusted (n + 1) ≤ adjusted n + error n - loss n := by
    intro n
    dsimp [adjusted]
    rw [Finset.sum_range_succ]
    have h := hstep n
    linarith
  exact summable_loss_of_bddBelow_descent hadjusted_bdd hloss_nonneg
    hadjusted_step herror herror_nonneg

/--
The preceding partial-sum condition may be required only eventually: finitely
many early increments can be absorbed into one larger deterministic bound.
-/
theorem summable_loss_of_nonnegative_descent_add_increment_eventually_upper
    {potential error loss increment : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, 0 ≤ potential n)
    (hloss_nonneg : ∀ n, 0 ≤ loss n)
    (hstep : ∀ n,
      potential (n + 1) ≤
        potential n + error n - loss n + increment n)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n)
    (hincrement_eventual_upper : ∃ upper : ℝ, ∃ T : ℕ,
      ∀ n : ℕ, T ≤ n → (∑ i ∈ Finset.range n, increment i) ≤ upper) :
    Summable loss := by
  rcases hincrement_eventual_upper with ⟨upper, T, hupper⟩
  have hrange_nonempty : (Finset.range (T + 1)).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    omega
  let initialUpper : ℝ :=
    (Finset.range (T + 1)).sup' hrange_nonempty
      (fun n => ∑ i ∈ Finset.range n, increment i)
  have hinitial : ∀ n : ℕ, n < T →
      (∑ i ∈ Finset.range n, increment i) ≤ initialUpper := by
    intro n hn
    dsimp [initialUpper]
    exact Finset.le_sup' (s := Finset.range (T + 1))
      (f := fun n => ∑ i ∈ Finset.range n, increment i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_lt hn))
  apply summable_loss_of_nonnegative_descent_add_increment
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  refine ⟨max upper initialUpper, ?_⟩
  intro n
  by_cases hT : T ≤ n
  · exact (hupper n hT).trans (le_max_left _ _)
  · exact (hinitial n (Nat.lt_of_not_ge hT)).trans (le_max_right _ _)

/--
Almost-sure wrapper for pathwise descent.  It converts per-time almost-everywhere
descent and positivity statements, together with an almost-sure eventual upper
bound on the cumulative increment, into almost-sure summability of the losses.
-/
theorem ae_summable_loss_of_nonnegative_descent_add_increment
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {potential loss increment : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n, ∀ᵐ omega ∂mu,
      potential (n + 1) omega ≤
        potential n omega + error n - loss n omega + increment n omega)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n)
    (hincrement_eventual_upper : ∀ᵐ omega ∂mu,
      ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ i ∈ Finset.range n, increment i omega) ≤ upper) :
    ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) := by
  filter_upwards [ae_all_iff.2 hpotential_nonneg,
    ae_all_iff.2 hloss_nonneg, ae_all_iff.2 hstep,
    hincrement_eventual_upper] with omega hpotential hloss hstep_omega hupper
  exact summable_loss_of_nonnegative_descent_add_increment_eventually_upper
    hpotential hloss hstep_omega herror herror_nonneg hupper

/--
Martingale version of the almost-sure descent wrapper.  An `L2`-bounded
conditionally centered increment process supplies the eventual partial-sum
upper bound required by the pathwise argument.
-/
theorem ae_summable_loss_of_nonnegative_descent_martingale_L2
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss increment : ℕ → Omega → ℝ} {error : ℕ → ℝ} {R : ℝ≥0}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n, ∀ᵐ omega ∂mu,
      potential (n + 1) omega ≤
        potential n omega + error n - loss n omega + increment n omega)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n)
    (hincrement_adapted :
      StronglyAdapted filtration
        (fun n omega => ∑ i ∈ Finset.range n, increment i omega))
    (hincrement_integrable :
      ∀ n, Integrable (fun omega => ∑ i ∈ Finset.range n, increment i omega) mu)
    (hincrement_centered : ∀ n,
      mu[increment n | filtration n] =ᵐ[mu] 0)
    (hincrement_L2 : ∀ n,
      eLpNorm (fun omega => ∑ i ∈ Finset.range n, increment i omega) 2 mu ≤ R) :
    ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) := by
  apply ae_summable_loss_of_nonnegative_descent_add_increment
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  exact ae_eventually_le_of_partial_sum_condExp_zero_L2_bdd
    hincrement_adapted hincrement_integrable hincrement_centered hincrement_L2

/-- A convergent control process bounds nonnegative cumulative losses by a finite constant. -/
theorem ae_summable_loss_of_tendsto_control
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {loss control : ℕ → Omega → ℝ}
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hcontrol : ∀ᵐ omega ∂mu, ∀ n : ℕ,
      (∑ i ∈ Finset.range n, loss i omega) ≤ control n omega)
    (hcontrol_tendsto : ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun n => control n omega) atTop (nhds limit)) :
    ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) := by
  filter_upwards [ae_all_iff.2 hloss_nonneg, hcontrol, hcontrol_tendsto]
    with omega hloss hcontrol_omega ⟨limit, hlimit⟩
  rcases hlimit.bddAbove_range with ⟨upper, hupper⟩
  refine summable_of_sum_range_le hloss (c := upper) ?_
  intro n
  exact (hcontrol_omega n).trans (hupper ⟨n, rfl⟩)

/--
A nonnegative loss series is almost surely summable when its partial sums are
controlled by an L1-bounded supermartingale.
-/
theorem ae_summable_loss_of_supermartingale_control_L1
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {loss control : ℕ → Omega → ℝ} {R : ℝ≥0}
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hcontrol_partial : ∀ᵐ omega ∂mu, ∀ n : ℕ,
      (∑ i ∈ Finset.range n, loss i omega) ≤ control n omega)
    (hcontrol_supermartingale : Supermartingale control filtration mu)
    (hcontrol_L1 : ∀ n, eLpNorm (control n) 1 mu ≤ R) :
    ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) := by
  apply ae_summable_loss_of_tendsto_control hloss_nonneg hcontrol_partial
  have hneg_tendsto :=
    hcontrol_supermartingale.neg.ae_tendsto_limitProcess (R := R) (by
      intro n
      simpa using hcontrol_L1 n)
  filter_upwards [hneg_tendsto] with omega homega
  refine ⟨-filtration.limitProcess (-control) mu omega, ?_⟩
  simpa only [Pi.neg_apply, neg_neg] using homega.neg

/--
The compensated potential formed from a conditionally descending process, its
cumulative nonnegative losses, and the remaining deterministic error budget.
-/
noncomputable def compensatedDescentControl
    {Omega : Type*} (potential loss : ℕ → Omega → ℝ) (error : ℕ → ℝ)
    (n : ℕ) (omega : Omega) : ℝ :=
  potential n omega + ∑ i ∈ Finset.range n, loss i omega +
    (∑' i, error i - ∑ i ∈ Finset.range n, error i)

/--
A one-step conditional descent inequality makes the compensated potential a
supermartingale. This is the probabilistic core of Robbins--Siegmund descent.
-/
theorem supermartingale_compensatedDescentControl
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_adapted : StronglyAdapted filtration potential)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hpotential_integrable : ∀ n, Integrable (potential n) mu)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega) :
    Supermartingale
      (compensatedDescentControl potential loss error) filtration mu := by
  let tail : ℕ → ℝ :=
    fun n => ∑' i, error i - ∑ i ∈ Finset.range n, error i
  have hpartial_adapted : StronglyAdapted filtration
      (fun n omega => ∑ i ∈ Finset.range n, loss i omega) := by
    intro n
    convert Finset.stronglyMeasurable_sum (Finset.range n) (fun i hi =>
      (hloss_adapted i).mono (filtration.mono (Nat.le_of_lt (Finset.mem_range.mp hi)))) using 1
    funext omega
    simp
  have hcontrol_adapted : StronglyAdapted filtration
      (compensatedDescentControl potential loss error) := by
    intro n
    exact (hpotential_adapted n).add (hpartial_adapted n) |>.add
      stronglyMeasurable_const
  have hpartial_integrable : ∀ n,
      Integrable (fun omega => ∑ i ∈ Finset.range n, loss i omega) mu := by
    intro n
    exact integrable_finset_sum _ fun i _hi => hloss_integrable i
  have hcontrol_integrable : ∀ n,
      Integrable (compensatedDescentControl potential loss error n) mu := by
    intro n
    exact ((hpotential_integrable n).add (hpartial_integrable n)).add (integrable_const _)
  apply supermartingale_nat hcontrol_adapted hcontrol_integrable
  intro n
  let rest : Omega → ℝ := fun omega =>
    (∑ i ∈ Finset.range (n + 1), loss i omega) + tail (n + 1)
  have hrest_adapted : StronglyMeasurable[filtration n] rest := by
    dsimp [rest]
    have hsum : StronglyMeasurable[filtration n]
        (fun omega => ∑ i ∈ Finset.range (n + 1), loss i omega) := by
      have hcomponent : ∀ i ∈ Finset.range (n + 1),
          StronglyMeasurable[filtration n] (loss i) := by
        intro i hi
        exact (hloss_adapted i).mono
          (filtration.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      convert Finset.stronglyMeasurable_sum (Finset.range (n + 1)) hcomponent using 1
      funext omega
      simp
    exact hsum.add stronglyMeasurable_const
  have hrest_integrable : Integrable rest mu := by
    dsimp [rest]
    exact (hpartial_integrable (n + 1)).add (integrable_const _)
  have hcontrol_succ :
      compensatedDescentControl potential loss error (n + 1) =
        fun omega => potential (n + 1) omega + rest omega := by
    funext omega
    dsimp [compensatedDescentControl, rest, tail]
    ring
  calc
    mu[compensatedDescentControl potential loss error (n + 1) | filtration n] =ᵐ[mu]
        mu[potential (n + 1) | filtration n] + rest := by
          rw [hcontrol_succ]
          exact (condExp_add (hpotential_integrable (n + 1)) hrest_integrable _).trans
            (by
              filter_upwards [] with omega
              rw [condExp_of_stronglyMeasurable
                (filtration.le n) hrest_adapted hrest_integrable])
    _ ≤ᵐ[mu] fun omega =>
        (potential n omega + error n - loss n omega) + rest omega := by
          filter_upwards [hstep n] with omega homega
          change mu[potential (n + 1) | filtration n] omega + rest omega ≤
            potential n omega + error n - loss n omega + rest omega
          linarith
    _ =ᵐ[mu] compensatedDescentControl potential loss error n := by
      filter_upwards [] with omega
      dsimp [compensatedDescentControl, rest, tail]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      ring

/--
The partial sums of a loss process are bounded by the compensated potential
when both the potential and the deterministic residual error budget are
nonnegative.
-/
theorem ae_partialSum_loss_le_compensatedDescentControl
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n) :
    ∀ᵐ omega ∂mu, ∀ n : ℕ,
      (∑ i ∈ Finset.range n, loss i omega) ≤
        compensatedDescentControl potential loss error n omega := by
  filter_upwards [ae_all_iff.2 hpotential_nonneg] with omega hpotential
  intro n
  have htail_nonneg : 0 ≤ ∑' i, error i - ∑ i ∈ Finset.range n, error i :=
    sub_nonneg.mpr (herror.sum_le_tsum (Finset.range n) fun i _hi => herror_nonneg i)
  dsimp [compensatedDescentControl]
  calc
    ∑ i ∈ Finset.range n, loss i omega ≤
        potential n omega + ∑ i ∈ Finset.range n, loss i omega := by
          linarith [hpotential n]
    _ ≤ potential n omega + ∑ i ∈ Finset.range n, loss i omega +
        (∑' i, error i - ∑ i ∈ Finset.range n, error i) := by
          linarith

/-- The compensated potential is nonnegative under nonnegative losses and residual errors. -/
theorem ae_nonneg_compensatedDescentControl
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n) :
    ∀ n, ∀ᵐ omega ∂mu, 0 ≤ compensatedDescentControl potential loss error n omega := by
  intro n
  filter_upwards [hpotential_nonneg n, ae_all_iff.2 hloss_nonneg] with omega hpotential hloss
  have htail_nonneg : 0 ≤ ∑' i, error i - ∑ i ∈ Finset.range n, error i :=
    sub_nonneg.mpr (herror.sum_le_tsum (Finset.range n) fun i _hi => herror_nonneg i)
  have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range n, loss i omega := by
    exact Finset.sum_nonneg fun i _hi => hloss i
  dsimp [compensatedDescentControl]
  positivity

/--
The L1 norm of a nonnegative compensated supermartingale is bounded by its
initial expectation.
-/
theorem eLpNorm_one_compensatedDescentControl_le_initial
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hcontrol : Supermartingale (compensatedDescentControl potential loss error) filtration mu)
    (hnonneg : ∀ n, ∀ᵐ omega ∂mu,
      0 ≤ compensatedDescentControl potential loss error n omega) :
    ∀ n, eLpNorm (compensatedDescentControl potential loss error n) 1 mu ≤
      ENNReal.ofReal (∫ omega,
        compensatedDescentControl potential loss error 0 omega ∂mu) := by
  intro n
  have hintegral :
      (∫ omega, compensatedDescentControl potential loss error n omega ∂mu) ≤
        ∫ omega, compensatedDescentControl potential loss error 0 omega ∂mu := by
    simpa using hcontrol.setIntegral_le (Nat.zero_le n) MeasurableSet.univ
  calc
    eLpNorm (compensatedDescentControl potential loss error n) 1 mu =
        ∫⁻ omega, ENNReal.ofReal (compensatedDescentControl potential loss error n omega) ∂mu := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          apply lintegral_congr_ae
          filter_upwards [hnonneg n] with omega homega
          rw [Real.enorm_eq_ofReal homega]
    _ = ENNReal.ofReal (∫ omega,
        compensatedDescentControl potential loss error n omega ∂mu) := by
          exact (ofReal_integral_eq_lintegral_ofReal
            (hcontrol.integrable n) (hnonneg n)).symm
    _ ≤ ENNReal.ofReal (∫ omega,
        compensatedDescentControl potential loss error 0 omega ∂mu) :=
          ENNReal.ofReal_le_ofReal hintegral

/--
Conditional descent with summable deterministic errors has almost-summable
losses once the natural compensated potential is uniformly L1-bounded.
-/
theorem ae_summable_loss_of_condExp_descent_L1
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ} {R : ℝ≥0}
    (hpotential_adapted : StronglyAdapted filtration potential)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hpotential_integrable : ∀ n, Integrable (potential n) mu)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hcontrol_L1 : ∀ n,
      eLpNorm (compensatedDescentControl potential loss error n) 1 mu ≤ R) :
    ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) := by
  apply ae_summable_loss_of_supermartingale_control_L1
    hloss_nonneg
    (ae_partialSum_loss_le_compensatedDescentControl hpotential_nonneg herror herror_nonneg)
    (supermartingale_compensatedDescentControl hpotential_adapted hloss_adapted
      hpotential_integrable hloss_integrable hstep)
    hcontrol_L1

/--
Conditional descent with nonnegative summable residual errors has almost-surely
summable losses. The proof constructs and bounds the compensated
supermartingale internally.
-/
theorem ae_summable_loss_of_condExp_descent
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_adapted : StronglyAdapted filtration potential)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hpotential_integrable : ∀ n, Integrable (potential n) mu)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n) :
    ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) := by
  let control := compensatedDescentControl potential loss error
  have hcontrol_supermartingale : Supermartingale control filtration mu :=
    supermartingale_compensatedDescentControl hpotential_adapted hloss_adapted
      hpotential_integrable hloss_integrable hstep
  have hcontrol_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ control n omega :=
    ae_nonneg_compensatedDescentControl hpotential_nonneg hloss_nonneg herror herror_nonneg
  have hcontrol_initial_nonneg : 0 ≤ ∫ omega, control 0 omega ∂mu :=
    integral_nonneg_of_ae (hcontrol_nonneg 0)
  let R : ℝ≥0 := ⟨∫ omega, control 0 omega ∂mu, hcontrol_initial_nonneg⟩
  refine ae_summable_loss_of_supermartingale_control_L1 (R := R)
    hloss_nonneg
    (ae_partialSum_loss_le_compensatedDescentControl hpotential_nonneg herror herror_nonneg)
    hcontrol_supermartingale ?_
  intro n
  calc
    eLpNorm (control n) 1 mu ≤ ENNReal.ofReal (∫ omega, control 0 omega ∂mu) :=
      eLpNorm_one_compensatedDescentControl_le_initial
        hcontrol_supermartingale hcontrol_nonneg n
    _ = R := by
      exact ENNReal.ofReal_eq_coe_nnreal hcontrol_initial_nonneg

/--
Under the same conditional descent hypotheses, the potential itself has an
almost-sure finite limit.  Together with
`ae_summable_loss_of_condExp_descent`, this is the reusable
Robbins--Siegmund conclusion needed by stochastic projected-subgradient
arguments.
-/
theorem ae_tendsto_potential_of_condExp_descent
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_adapted : StronglyAdapted filtration potential)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hpotential_integrable : ∀ n, Integrable (potential n) mu)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n) :
    ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun n => potential n omega) atTop (nhds limit) := by
  let control := compensatedDescentControl potential loss error
  have hcontrol_supermartingale : Supermartingale control filtration mu :=
    supermartingale_compensatedDescentControl hpotential_adapted hloss_adapted
      hpotential_integrable hloss_integrable hstep
  have hcontrol_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ control n omega :=
    ae_nonneg_compensatedDescentControl hpotential_nonneg hloss_nonneg herror herror_nonneg
  have hcontrol_initial_nonneg : 0 ≤ ∫ omega, control 0 omega ∂mu :=
    integral_nonneg_of_ae (hcontrol_nonneg 0)
  let R : ℝ≥0 := ⟨∫ omega, control 0 omega ∂mu, hcontrol_initial_nonneg⟩
  have hcontrol_L1 : ∀ n, eLpNorm (control n) 1 mu ≤ R := by
    intro n
    calc
      eLpNorm (control n) 1 mu ≤ ENNReal.ofReal (∫ omega, control 0 omega ∂mu) :=
        eLpNorm_one_compensatedDescentControl_le_initial
          hcontrol_supermartingale hcontrol_nonneg n
      _ = R := ENNReal.ofReal_eq_coe_nnreal hcontrol_initial_nonneg
  have hcontrol_tendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun n => control n omega) atTop
        (nhds (-filtration.limitProcess (-control) mu omega)) := by
    have hneg_tendsto :=
      hcontrol_supermartingale.neg.ae_tendsto_limitProcess (R := R) (by
        intro n
        simpa using hcontrol_L1 n)
    filter_upwards [hneg_tendsto] with omega homega
    simpa only [Pi.neg_apply, neg_neg] using homega.neg
  have hloss_summable : ∀ᵐ omega ∂mu, Summable (fun n => loss n omega) :=
    ae_summable_loss_of_condExp_descent
      hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
      hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  filter_upwards [hcontrol_tendsto, hloss_summable] with omega hcontrol hloss
  have hloss_tendsto :
      Tendsto (fun n => ∑ i ∈ Finset.range n, loss i omega) atTop
        (nhds (∑' i, loss i omega)) :=
    hloss.hasSum.tendsto_sum_nat
  have herror_tendsto :
      Tendsto (fun n => ∑ i ∈ Finset.range n, error i) atTop
        (nhds (∑' i, error i)) :=
    herror.hasSum.tendsto_sum_nat
  refine ⟨-filtration.limitProcess (-control) mu omega - ∑' i, loss i omega, ?_⟩
  have hrewrite : (fun n => potential n omega) =
      fun n => control n omega - (∑ i ∈ Finset.range n, loss i omega) -
        (∑' i, error i - ∑ i ∈ Finset.range n, error i) := by
    funext n
    dsimp [control, compensatedDescentControl]
    ring
  rw [hrewrite]
  have htail : Tendsto
      (fun n => ∑' i, error i - ∑ i ∈ Finset.range n, error i) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ∑' i, error i) atTop (nhds (∑' i, error i))).sub herror_tendsto)
  simpa using (hcontrol.sub hloss_tendsto).sub htail

/--
If nonnegative weighted losses are summable while the nonnegative weights have
divergent partial sums, arbitrarily small loss gaps occur arbitrarily late.
-/
theorem frequently_lt_of_summable_mul_of_tendsto_sum_atTop
    {gap radius : ℕ → ℝ}
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hsummable : Summable (fun n => radius (n + 1) * gap n))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in atTop, gap n < epsilon := by
  intro epsilon hepsilon
  by_contra hfrequently
  have heventually_large : ∀ᶠ n in atTop, epsilon ≤ gap n :=
    (Filter.not_frequently.mp hfrequently).mono fun n hn => le_of_not_gt hn
  have hscale_nonneg : 0 ≤ 1 / epsilon := le_of_lt (one_div_pos.mpr hepsilon)
  have hradius_le : ∀ᶠ n in atTop,
      radius (n + 1) ≤ (1 / epsilon) * (radius (n + 1) * gap n) := by
    filter_upwards [heventually_large] with n hgap
    have hmul : epsilon * radius (n + 1) ≤ radius (n + 1) * gap n := by
      calc
        epsilon * radius (n + 1) = radius (n + 1) * epsilon := by ring
        _ ≤ radius (n + 1) * gap n :=
          mul_le_mul_of_nonneg_left hgap (hradius_nonneg n)
    calc
      radius (n + 1) = (1 / epsilon) * (epsilon * radius (n + 1)) := by
        field_simp
      _ ≤ (1 / epsilon) * (radius (n + 1) * gap n) :=
        mul_le_mul_of_nonneg_left hmul hscale_nonneg
  have hradius_summable : Summable (fun n => radius (n + 1)) := by
    apply Summable.of_norm_bounded_eventually (hsummable.mul_left (1 / epsilon))
    simpa only [Nat.cofinite_eq_atTop] using
      hradius_le.mono fun n hn => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hradius_nonneg n)]
        exact hn
  have hpartial_le : ∀ n : ℕ,
      (∑ t ∈ Finset.range n, radius (t + 1)) ≤ ∑' t, radius (t + 1) := by
    intro n
    exact hradius_summable.sum_le_tsum (Finset.range n)
      (fun t _ht => hradius_nonneg t)
  rcases Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp hradius_diverges) (∑' t, radius (t + 1) + 1)) with
      ⟨n, hn⟩
  linarith [hpartial_le n, hn n le_rfl]

/--
Arbitrarily late nonnegative terms below every positive threshold yield a
strictly increasing subsequence converging to zero.
-/
theorem exists_strictMono_tendsto_zero_of_frequently_lt
    {gap : ℕ → ℝ} (hgap_nonneg : ∀ n, 0 ≤ gap n)
    (hfrequently : ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in atTop, gap n < epsilon) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      Tendsto (fun n => gap (subseq n)) atTop (nhds 0) := by
  have hpick : ∀ k N : ℕ, ∃ n : ℕ, N < n ∧ gap n < 1 / ((k : ℝ) + 1) := by
    intro k N
    have hpositive : 0 < 1 / ((k : ℝ) + 1) := by positivity
    rcases ((hfrequently (1 / ((k : ℝ) + 1)) hpositive).and_eventually
      (eventually_gt_atTop N)).exists with ⟨n, hgap, hN⟩
    exact ⟨n, hN, hgap⟩
  let pick : ℕ → ℕ → ℕ := fun k N => Classical.choose (hpick k N)
  have hpick_gt : ∀ k N, N < pick k N := fun k N =>
    (Classical.choose_spec (hpick k N)).1
  have hpick_small : ∀ k N, gap (pick k N) < 1 / ((k : ℝ) + 1) := fun k N =>
    (Classical.choose_spec (hpick k N)).2
  let subseq : ℕ → ℕ := Nat.rec (pick 0 0) (fun k n => pick (k + 1) (n + 1))
  have hsubseq_strict : StrictMono subseq := by
    apply strictMono_nat_of_lt_succ
    intro n
    change subseq n < pick (n + 1) (subseq n + 1)
    exact Nat.lt_trans (Nat.lt_succ_self _) (hpick_gt (n + 1) (subseq n + 1))
  have hsubseq_small : ∀ n, gap (subseq n) < 1 / ((n : ℝ) + 1) := by
    intro n
    cases n with
    | zero =>
        exact hpick_small 0 0
    | succ n =>
        exact hpick_small (n + 1) (subseq n + 1)
  refine ⟨subseq, hsubseq_strict, ?_⟩
  apply squeeze_zero (fun n => hgap_nonneg (subseq n))
  · intro n
    exact (hsubseq_small n).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/--
A conditionally descending nonnegative potential converges almost surely to
zero when every positive potential level forces a fixed positive multiple of a
nonsummable step sequence into the loss.  This is the final separation step in
Robbins--Siegmund arguments for convergence to a unique optimizer.
-/
theorem ae_tendsto_potential_zero_of_condExp_descent_of_loss_separation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error radius : ℕ → ℝ}
    (hpotential_adapted : StronglyAdapted filtration potential)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hpotential_integrable : ∀ n, Integrable (potential n) mu)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ n omega, epsilon ≤ potential n omega →
          delta * radius (n + 1) ≤ loss n omega) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => potential n omega) atTop (nhds 0) := by
  have hpotential_tendsto := ae_tendsto_potential_of_condExp_descent
    hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  have hloss_summable := ae_summable_loss_of_condExp_descent
    hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  filter_upwards [hpotential_tendsto, hloss_summable,
    ae_all_iff.2 hpotential_nonneg] with omega hpotential hsum hnonneg
  rcases hpotential with ⟨limit, hlimit⟩
  have hlimit_nonneg : 0 ≤ limit :=
    ge_of_tendsto hlimit (Filter.Eventually.of_forall hnonneg)
  have hlimit_zero : limit = 0 := by
    by_contra hlimit_ne_zero
    have hlimit_pos : 0 < limit :=
      lt_of_le_of_ne hlimit_nonneg (Ne.symm hlimit_ne_zero)
    let epsilon : ℝ := limit / 2
    have hepsilon_pos : 0 < epsilon := by
      dsimp [epsilon]
      linarith
    rcases hloss_separation epsilon hepsilon_pos with ⟨delta, hdelta_pos, hseparate⟩
    have heventually_potential : ∀ᶠ n in atTop,
        epsilon ≤ potential n omega :=
      (hlimit.eventually (eventually_gt_nhds (by
        change limit / 2 < limit
        linarith))).mono fun _ h => h.le
    have heventually_radius_le_loss : ∀ᶠ n in atTop,
        radius (n + 1) ≤ (1 / delta) * loss n omega := by
      filter_upwards [heventually_potential] with n hn
      have hbound := hseparate n omega hn
      have hdivision : radius (n + 1) ≤ loss n omega / delta := by
        rw [le_div_iff₀ hdelta_pos]
        nlinarith
      simpa [div_eq_mul_inv, mul_comm] using hdivision
    have hradius_summable : Summable (fun n => radius (n + 1)) := by
      apply Summable.of_norm_bounded_eventually (hsum.mul_left (1 / delta))
      simpa only [Nat.cofinite_eq_atTop] using
        heventually_radius_le_loss.mono fun n hn => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hradius_nonneg n)]
          exact hn
    have hpartial_le : ∀ n : ℕ,
        (∑ t ∈ Finset.range n, radius (t + 1)) ≤
          ∑' t, radius (t + 1) := by
      intro n
      exact hradius_summable.sum_le_tsum (Finset.range n)
        (fun t _ht => hradius_nonneg t)
    have hlarge := (Filter.tendsto_atTop.mp hradius_diverges)
      (∑' t, radius (t + 1) + 1)
    have hfalse_eventually : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [hlarge] with n hn
      linarith [hpartial_le n]
    rcases (Filter.eventually_atTop.mp hfalse_eventually :
      ∃ n : ℕ, ∀ m ≥ n, False) with ⟨n, hn⟩
    exact (hn n le_rfl).elim
  simpa [hlimit_zero] using hlimit

/--
A finite-coordinate trajectory converges almost surely to its target when its
squared Euclidean distance satisfies the Robbins--Siegmund descent conditions
and the loss separates every positive distance level.
-/
theorem ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_loss_separation
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {trajectory : ℕ → Omega → Coord → ℝ} {target : Coord → ℝ}
    {loss : ℕ → Omega → ℝ} {error radius : ℕ → ℝ}
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory (n + 1) omega i - target i) | filtration n] ≤ᵐ[mu]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => trajectory n omega i - target i) + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ n omega, epsilon ≤
          FiniteDimensionalNorms.l2Sq (fun i => trajectory n omega i - target i) →
          delta * radius (n + 1) ≤ loss n omega) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => trajectory n omega) atTop (nhds target) := by
  let potential : ℕ → Omega → ℝ :=
    fun n omega => FiniteDimensionalNorms.l2Sq
      (fun i => trajectory n omega i - target i)
  have hpotential_adapted : StronglyAdapted filtration potential := by
    apply stronglyAdapted_finiteL2Sq
    intro i
    exact (htrajectory_adapted i).sub (fun _ => stronglyMeasurable_const)
  have hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega := by
    intro n
    filter_upwards [] with omega
    exact FiniteDimensionalNorms.normL2Sq_nonneg _
  have hpotential_tendsto :=
    ae_tendsto_potential_zero_of_condExp_descent_of_loss_separation
      hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
      hpotential_nonneg hloss_nonneg hstep herror herror_nonneg hradius_nonneg
      hradius_diverges hloss_separation
  filter_upwards [hpotential_tendsto] with omega homega
  exact FiniteDimensionalNorms.tendsto_pi_of_tendsto_l2Sq_sub_zero homega

/--
An almost-surely valid trajectory converges to zero in potential when the
loss separation is available on its valid states. This form supports feasible
sets specified only almost everywhere.
-/
theorem ae_tendsto_potential_zero_of_condExp_descent_of_ae_loss_separation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {potential loss : ℕ → Omega → ℝ} {error radius : ℕ → ℝ}
    {valid : ℕ → Omega → Prop}
    (hpotential_adapted : StronglyAdapted filtration potential)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hpotential_integrable : ∀ n, Integrable (potential n) mu)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hvalid : ∀ᵐ omega ∂mu, ∀ n, valid n omega)
    (hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ n omega, valid n omega → epsilon ≤ potential n omega →
          delta * radius (n + 1) ≤ loss n omega) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => potential n omega) atTop (nhds 0) := by
  have hpotential_tendsto := ae_tendsto_potential_of_condExp_descent
    hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  have hloss_summable := ae_summable_loss_of_condExp_descent
    hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg
  filter_upwards [hpotential_tendsto, hloss_summable,
    ae_all_iff.2 hpotential_nonneg, hvalid] with omega hpotential hsum hnonneg hvalid_omega
  rcases hpotential with ⟨limit, hlimit⟩
  have hlimit_nonneg : 0 ≤ limit :=
    ge_of_tendsto hlimit (Filter.Eventually.of_forall hnonneg)
  have hlimit_zero : limit = 0 := by
    by_contra hlimit_ne_zero
    have hlimit_pos : 0 < limit :=
      lt_of_le_of_ne hlimit_nonneg (Ne.symm hlimit_ne_zero)
    let epsilon : ℝ := limit / 2
    have hepsilon_pos : 0 < epsilon := by
      dsimp [epsilon]
      linarith
    rcases hloss_separation epsilon hepsilon_pos with ⟨delta, hdelta_pos, hseparate⟩
    have heventually_potential : ∀ᶠ n in atTop,
        epsilon ≤ potential n omega :=
      (hlimit.eventually (eventually_gt_nhds (by
        change limit / 2 < limit
        linarith))).mono fun _ h => h.le
    have heventually_radius_le_loss : ∀ᶠ n in atTop,
        radius (n + 1) ≤ (1 / delta) * loss n omega := by
      filter_upwards [heventually_potential] with n hn
      have hbound := hseparate n omega (hvalid_omega n) hn
      have hdivision : radius (n + 1) ≤ loss n omega / delta := by
        rw [le_div_iff₀ hdelta_pos]
        nlinarith
      simpa [div_eq_mul_inv, mul_comm] using hdivision
    have hradius_summable : Summable (fun n => radius (n + 1)) := by
      apply Summable.of_norm_bounded_eventually (hsum.mul_left (1 / delta))
      simpa only [Nat.cofinite_eq_atTop] using
        heventually_radius_le_loss.mono fun n hn => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hradius_nonneg n)]
          exact hn
    have hpartial_le : ∀ n : ℕ,
        (∑ t ∈ Finset.range n, radius (t + 1)) ≤
          ∑' t, radius (t + 1) := by
      intro n
      exact hradius_summable.sum_le_tsum (Finset.range n)
        (fun t _ht => hradius_nonneg t)
    have hlarge := (Filter.tendsto_atTop.mp hradius_diverges)
      (∑' t, radius (t + 1) + 1)
    have hfalse_eventually : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [hlarge] with n hn
      linarith [hpartial_le n]
    rcases (Filter.eventually_atTop.mp hfalse_eventually :
      ∃ n : ℕ, ∀ m ≥ n, False) with ⟨n, hn⟩
    exact (hn n le_rfl).elim
  simpa [hlimit_zero] using hlimit

/--
A finite-coordinate trajectory converges almost surely to its target when its
valid states satisfy an almost-sure Robbins--Siegmund loss-separation bound.
-/
theorem ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_ae_loss_separation
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {trajectory : ℕ → Omega → Coord → ℝ} {target : Coord → ℝ}
    {loss : ℕ → Omega → ℝ} {error radius : ℕ → ℝ}
    {valid : ℕ → Omega → Prop}
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory (n + 1) omega i - target i) | filtration n] ≤ᵐ[mu]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => trajectory n omega i - target i) + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hvalid : ∀ᵐ omega ∂mu, ∀ n, valid n omega)
    (hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ n omega, valid n omega → epsilon ≤
          FiniteDimensionalNorms.l2Sq (fun i => trajectory n omega i - target i) →
          delta * radius (n + 1) ≤ loss n omega) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => trajectory n omega) atTop (nhds target) := by
  let potential : ℕ → Omega → ℝ :=
    fun n omega => FiniteDimensionalNorms.l2Sq
      (fun i => trajectory n omega i - target i)
  have hpotential_adapted : StronglyAdapted filtration potential := by
    apply stronglyAdapted_finiteL2Sq
    intro i
    exact (htrajectory_adapted i).sub (fun _ => stronglyMeasurable_const)
  have hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega := by
    intro n
    filter_upwards [] with omega
    exact FiniteDimensionalNorms.normL2Sq_nonneg _
  have hpotential_tendsto :=
    ae_tendsto_potential_zero_of_condExp_descent_of_ae_loss_separation
      hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
      hpotential_nonneg hloss_nonneg hstep herror herror_nonneg hradius_nonneg
      hradius_diverges hvalid hloss_separation
  filter_upwards [hpotential_tendsto] with omega homega
  exact FiniteDimensionalNorms.tendsto_pi_of_tendsto_l2Sq_sub_zero homega

/--
A compact continuous objective with a unique minimizer supplies the
loss-separation condition needed for almost-sure finite-coordinate stochastic
subgradient convergence.
-/
theorem ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_compact_continuous_unique_min
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {trajectory : ℕ → Omega → Coord → ℝ} {target : Coord → ℝ}
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {loss : ℕ → Omega → ℝ} {error radius : ℕ → ℝ}
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hloss_formula : ∀ n omega,
      loss n omega = 2 * radius (n + 1) *
        (objective (trajectory n omega) - objective target))
    (hstep : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory (n + 1) omega i - target i) | filtration n] ≤ᵐ[mu]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => trajectory n omega i - target i) + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hcompact : IsCompact solutionSpace)
    (hcontinuous : ContinuousOn objective solutionSpace)
    (hmin : IsMinOn objective solutionSpace target)
    (hunique : ∀ x, x ∈ solutionSpace → objective x = objective target → x = target) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => trajectory n omega) atTop (nhds target) := by
  have hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega := by
    intro n
    filter_upwards [htrajectory_mem] with omega hmem
    rw [hloss_formula n omega]
    exact mul_nonneg (mul_nonneg (by norm_num) (hradius_nonneg n))
      (sub_nonneg.mpr (hmin (hmem n)))
  apply ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_ae_loss_separation
    htrajectory_adapted hpotential_integrable hloss_adapted hloss_integrable hloss_nonneg
    hstep herror herror_nonneg hradius_nonneg hradius_diverges htrajectory_mem
  intro epsilon hepsilon
  rcases FiniteDimensionalNorms.exists_pos_le_objective_gap_of_isCompact_of_continuousOn_of_unique_min
    hcompact hcontinuous hmin hunique epsilon hepsilon with ⟨delta, hdelta_pos, hgap⟩
  refine ⟨2 * delta, mul_pos (by norm_num) hdelta_pos, ?_⟩
  intro n omega hmem hpotential
  have hgap_value := hgap (trajectory n omega) hmem hpotential
  rw [hloss_formula n omega]
  have hfactor_nonneg : 0 ≤ 2 * radius (n + 1) :=
    mul_nonneg (by norm_num) (hradius_nonneg n)
  have hscale : (2 * radius (n + 1)) * delta ≤
      (2 * radius (n + 1)) *
        (objective (trajectory n omega) - objective target) :=
    mul_le_mul_of_nonneg_left hgap_value hfactor_nonneg
  calc
    2 * delta * radius (n + 1) = (2 * radius (n + 1)) * delta := by ring
    _ ≤ 2 * radius (n + 1) *
        (objective (trajectory n omega) - objective target) := hscale

/--
The compact unique-minimizer convergence theorem when objective continuity is
obtained from uniformly bounded feasible-set subgradients.  Existence of such
a subgradient at every feasible point is explicit, avoiding a vacuous bound at
points whose subdifferential is empty.
-/
theorem ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_compact_bounded_subgradients
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {trajectory : ℕ → Omega → Coord → ℝ} {target : Coord → ℝ}
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {loss : ℕ → Omega → ℝ} {error radius : ℕ → ℝ} {C : ℝ}
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hloss_adapted : StronglyAdapted filtration loss)
    (hloss_integrable : ∀ n, Integrable (loss n) mu)
    (hloss_formula : ∀ n omega,
      loss n omega = 2 * radius (n + 1) *
        (objective (trajectory n omega) - objective target))
    (hstep : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory (n + 1) omega i - target i) | filtration n] ≤ᵐ[mu]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => trajectory n omega i - target i) + error n - loss n omega)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hcompact : IsCompact solutionSpace)
    (hC : 0 ≤ C)
    (hsub : ∀ x, x ∈ solutionSpace → ∃ g,
      FiniteSubgradientOn objective solutionSpace x g ∧
        FiniteDimensionalNorms.l2 g ≤ C)
    (hmin : IsMinOn objective solutionSpace target)
    (hunique : ∀ x, x ∈ solutionSpace → objective x = objective target → x = target) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => trajectory n omega) atTop (nhds target) := by
  apply ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_compact_continuous_unique_min
    htrajectory_adapted htrajectory_mem hpotential_integrable hloss_adapted
    hloss_integrable hloss_formula hstep herror herror_nonneg hradius_nonneg
    hradius_diverges hcompact
  · exact continuousOn_of_exists_bounded_subgradientOn hC hsub
  · exact hmin
  · exact hunique

/--
The potential half of the deterministic Robbins--Siegmund descent argument.
A nonnegative potential satisfying the same summable-error descent inequality
has a finite limit.
-/
theorem exists_tendsto_potential_of_nonnegative_descent
    {potential error loss : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, 0 ≤ potential n)
    (hloss_nonneg : ∀ n, 0 ≤ loss n)
    (hstep : ∀ n,
      potential (n + 1) ≤ potential n + error n - loss n)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n) :
    ∃ limit : ℝ, Tendsto potential Filter.atTop (nhds limit) := by
  let corrected : ℕ → ℝ :=
    fun n => potential n - ∑ i ∈ Finset.range n, error i
  have hcorrected_anti : Antitone corrected := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [corrected]
    rw [Finset.sum_range_succ]
    have h := hstep n
    nlinarith [hloss_nonneg n]
  have hpartial_le_tsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, error i) ≤ ∑' i, error i := by
    intro n
    exact herror.sum_le_tsum (Finset.range n) (fun i _hi => herror_nonneg i)
  have hcorrected_bdd : BddBelow (Set.range corrected) := by
    refine ⟨-(∑' i, error i), ?_⟩
    rintro x ⟨n, rfl⟩
    dsimp [corrected]
    linarith [hpotential_nonneg n, hpartial_le_tsum n]
  have hcorrected_tendsto :
      Tendsto corrected Filter.atTop (nhds (⨅ n, corrected n)) :=
    tendsto_atTop_ciInf hcorrected_anti hcorrected_bdd
  have hsum_tendsto :
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, error i)
        Filter.atTop (nhds (∑' i, error i)) :=
    herror.hasSum.tendsto_sum_nat
  refine ⟨(⨅ n, corrected n) + ∑' i, error i, ?_⟩
  have hrewrite : potential =
      fun n => corrected n + ∑ i ∈ Finset.range n, error i := by
    funext n
    dsimp [corrected]
    ring
  rw [hrewrite]
  exact hcorrected_tendsto.add hsum_tendsto

/--
The pathwise potential half of stochastic descent when the one-step estimate
also contains an increment whose partial sums converge.  This is the form
needed when a summable adapted bias and a convergent martingale fluctuation are
kept as realized pathwise terms, rather than being replaced by a deterministic
conditional-expectation envelope.
-/
theorem exists_tendsto_potential_of_nonnegative_descent_add_increment
    {potential error loss increment : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, 0 ≤ potential n)
    (hloss_nonneg : ∀ n, 0 ≤ loss n)
    (hstep : ∀ n,
      potential (n + 1) ≤ potential n + error n - loss n + increment n)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n)
    (hincrement : ∃ incrementLimit : ℝ,
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, increment i) atTop
        (nhds incrementLimit)) :
    ∃ limit : ℝ, Tendsto potential Filter.atTop (nhds limit) := by
  rcases hincrement with ⟨incrementLimit, hincrement⟩
  let corrected : ℕ → ℝ := fun n =>
    potential n - ∑ i ∈ Finset.range n, error i - ∑ i ∈ Finset.range n, increment i
  have hcorrected_anti : Antitone corrected := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [corrected]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := hstep n
    linarith [hloss_nonneg n]
  have hpartial_le_tsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, error i) ≤ ∑' i, error i := by
    intro n
    exact herror.sum_le_tsum (Finset.range n) (fun i _hi => herror_nonneg i)
  rcases hincrement.bddAbove_range with ⟨incrementUpper, hincrementUpper⟩
  have hcorrected_bdd : BddBelow (Set.range corrected) := by
    refine ⟨-(∑' i, error i) - incrementUpper, ?_⟩
    rintro x ⟨n, rfl⟩
    dsimp [corrected]
    have hinc : (∑ i ∈ Finset.range n, increment i) ≤ incrementUpper :=
      hincrementUpper ⟨n, rfl⟩
    linarith [hpotential_nonneg n, hpartial_le_tsum n]
  have hcorrected_tendsto :
      Tendsto corrected Filter.atTop (nhds (⨅ n, corrected n)) :=
    tendsto_atTop_ciInf hcorrected_anti hcorrected_bdd
  have herror_tendsto :
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, error i)
        Filter.atTop (nhds (∑' i, error i)) :=
    herror.hasSum.tendsto_sum_nat
  refine ⟨(⨅ n, corrected n) + ∑' i, error i + incrementLimit, ?_⟩
  have hrewrite : potential = fun n => corrected n +
      (∑ i ∈ Finset.range n, error i) + (∑ i ∈ Finset.range n, increment i) := by
    funext n
    dsimp [corrected]
    ring
  rw [hrewrite]
  exact (hcorrected_tendsto.add herror_tendsto).add hincrement

/--
Almost-sure wrapper for
`exists_tendsto_potential_of_nonnegative_descent_add_increment`.
-/
theorem ae_exists_tendsto_potential_of_nonnegative_descent_add_increment
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {potential loss increment : ℕ → Omega → ℝ} {error : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega)
    (hstep : ∀ n, ∀ᵐ omega ∂mu,
      potential (n + 1) omega ≤ potential n omega + error n - loss n omega + increment n omega)
    (herror : Summable error)
    (herror_nonneg : ∀ n, 0 ≤ error n)
    (hincrement : ∀ᵐ omega ∂mu, ∃ incrementLimit : ℝ,
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, increment i omega) atTop
        (nhds incrementLimit)) :
    ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun n => potential n omega) atTop (nhds limit) := by
  filter_upwards [ae_all_iff.2 hpotential_nonneg, ae_all_iff.2 hloss_nonneg,
    ae_all_iff.2 hstep, hincrement] with omega hpotential hloss hstep_omega hinc
  exact exists_tendsto_potential_of_nonnegative_descent_add_increment
    hpotential hloss hstep_omega herror herror_nonneg hinc

/--
If a nonnegative potential has an almost-sure limit and its nonnegative loss
is almost-surely summable, the usual loss-separation argument forces that
limit to be zero.  This separates the deterministic topological conclusion
from the particular conditional- or pathwise-descent route that supplied the
two premises.
-/
theorem ae_tendsto_potential_zero_of_tendsto_and_summable_of_loss_separation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {potential loss : ℕ → Omega → ℝ} {radius : ℕ → ℝ}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hpotential_tendsto : ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun n => potential n omega) atTop (nhds limit))
    (hloss_summable : ∀ᵐ omega ∂mu, Summable (fun n => loss n omega))
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ n omega, epsilon ≤ potential n omega →
          delta * radius (n + 1) ≤ loss n omega) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => potential n omega) atTop (nhds 0) := by
  filter_upwards [hpotential_tendsto, hloss_summable,
    ae_all_iff.2 hpotential_nonneg] with omega hpotential hsum hnonneg
  rcases hpotential with ⟨limit, hlimit⟩
  have hlimit_nonneg : 0 ≤ limit :=
    ge_of_tendsto hlimit (Filter.Eventually.of_forall hnonneg)
  have hlimit_zero : limit = 0 := by
    by_contra hlimit_ne_zero
    have hlimit_pos : 0 < limit :=
      lt_of_le_of_ne hlimit_nonneg (Ne.symm hlimit_ne_zero)
    let epsilon : ℝ := limit / 2
    have hepsilon_pos : 0 < epsilon := by
      dsimp [epsilon]
      linarith
    rcases hloss_separation epsilon hepsilon_pos with ⟨delta, hdelta_pos, hseparate⟩
    have heventually_potential : ∀ᶠ n in atTop,
        epsilon ≤ potential n omega :=
      (hlimit.eventually (eventually_gt_nhds (by
        change limit / 2 < limit
        linarith))).mono fun _ h => h.le
    have heventually_radius_le_loss : ∀ᶠ n in atTop,
        radius (n + 1) ≤ (1 / delta) * loss n omega := by
      filter_upwards [heventually_potential] with n hn
      have hbound := hseparate n omega hn
      have hdivision : radius (n + 1) ≤ loss n omega / delta := by
        rw [le_div_iff₀ hdelta_pos]
        nlinarith
      simpa [div_eq_mul_inv, mul_comm] using hdivision
    have hradius_summable : Summable (fun n => radius (n + 1)) := by
      apply Summable.of_norm_bounded_eventually (hsum.mul_left (1 / delta))
      simpa only [Nat.cofinite_eq_atTop] using
        heventually_radius_le_loss.mono fun n hn => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hradius_nonneg n)]
          exact hn
    have hpartial_le : ∀ n : ℕ,
        (∑ t ∈ Finset.range n, radius (t + 1)) ≤
          ∑' t, radius (t + 1) := by
      intro n
      exact hradius_summable.sum_le_tsum (Finset.range n)
        (fun t _ht => hradius_nonneg t)
    have hlarge := (Filter.tendsto_atTop.mp hradius_diverges)
      (∑' t, radius (t + 1) + 1)
    have hfalse_eventually : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [hlarge] with n hn
      linarith [hpartial_le n]
    rcases (Filter.eventually_atTop.mp hfalse_eventually :
      ∃ n : ℕ, ∀ m ≥ n, False) with ⟨n, hn⟩
    exact (hn n le_rfl).elim
  simpa [hlimit_zero] using hlimit

/--
Almost-sure feasible-state variant of
`ae_tendsto_potential_zero_of_tendsto_and_summable_of_loss_separation`.
The descent argument only needs loss separation at the states actually visited
on its common probability-one event; this keeps projected stochastic methods
from strengthening an a.s. update invariant into a pointwise one.
-/
theorem ae_tendsto_potential_zero_of_tendsto_and_summable_of_ae_valid_loss_separation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {potential loss : ℕ → Omega → ℝ} {radius : ℕ → ℝ}
    {valid : ℕ → Omega → Prop}
    (hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega)
    (hpotential_tendsto : ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun n => potential n omega) atTop (nhds limit))
    (hloss_summable : ∀ᵐ omega ∂mu, Summable (fun n => loss n omega))
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hvalid : ∀ᵐ omega ∂mu, ∀ n, valid n omega)
    (hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ n omega, valid n omega → epsilon ≤ potential n omega →
          delta * radius (n + 1) ≤ loss n omega) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => potential n omega) atTop (nhds 0) := by
  filter_upwards [hpotential_tendsto, hloss_summable,
    ae_all_iff.2 hpotential_nonneg, hvalid] with omega hpotential hsum hnonneg hvalidω
  rcases hpotential with ⟨limit, hlimit⟩
  have hlimit_nonneg : 0 ≤ limit :=
    ge_of_tendsto hlimit (Filter.Eventually.of_forall hnonneg)
  have hlimit_zero : limit = 0 := by
    by_contra hlimit_ne_zero
    have hlimit_pos : 0 < limit :=
      lt_of_le_of_ne hlimit_nonneg (Ne.symm hlimit_ne_zero)
    let epsilon : ℝ := limit / 2
    have hepsilon_pos : 0 < epsilon := by
      dsimp [epsilon]
      linarith
    rcases hloss_separation epsilon hepsilon_pos with ⟨delta, hdelta_pos, hseparate⟩
    have heventually_potential : ∀ᶠ n in atTop,
        epsilon ≤ potential n omega :=
      (hlimit.eventually (eventually_gt_nhds (by
        change limit / 2 < limit
        linarith))).mono fun _ h => h.le
    have heventually_radius_le_loss : ∀ᶠ n in atTop,
        radius (n + 1) ≤ (1 / delta) * loss n omega := by
      filter_upwards [heventually_potential] with n hn
      have hbound := hseparate n omega (hvalidω n) hn
      have hdivision : radius (n + 1) ≤ loss n omega / delta := by
        rw [le_div_iff₀ hdelta_pos]
        nlinarith
      simpa [div_eq_mul_inv, mul_comm] using hdivision
    have hradius_summable : Summable (fun n => radius (n + 1)) := by
      apply Summable.of_norm_bounded_eventually (hsum.mul_left (1 / delta))
      simpa only [Nat.cofinite_eq_atTop] using
        heventually_radius_le_loss.mono fun n hn => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hradius_nonneg n)]
          exact hn
    have hpartial_le : ∀ n : ℕ,
        (∑ t ∈ Finset.range n, radius (t + 1)) ≤
          ∑' t, radius (t + 1) := by
      intro n
      exact hradius_summable.sum_le_tsum (Finset.range n)
        (fun t _ht => hradius_nonneg t)
    have hlarge := (Filter.tendsto_atTop.mp hradius_diverges)
      (∑' t, radius (t + 1) + 1)
    have hfalse_eventually : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [hlarge] with n hn
      linarith [hpartial_le n]
    rcases (Filter.eventually_atTop.mp hfalse_eventually :
      ∃ n : ℕ, ∀ m ≥ n, False) with ⟨n, hn⟩
    exact (hn n le_rfl).elim
  simpa [hlimit_zero] using hlimit

/--
Library-level marker for consequences whose remaining unformalized ingredient
is stochastic subgradient method convergence.

This is intentionally an `abbrev`, not a primitive postulate: the consequence
still has to be supplied as an explicit assumption at the paper boundary.  The
value of this declaration is provenance control: papers should depend on one
named SSGM boundary instead of accumulating many theorem-specific proof
assumptions.
-/
abbrev SSGMConvergenceBoundary (consequence : Prop) : Prop :=
  consequence

/-- Eliminator for a consequence routed through the SSGM convergence boundary. -/
theorem SSGMConvergenceBoundary.elim {consequence : Prop}
    (h : SSGMConvergenceBoundary consequence) : consequence :=
  h

end Optimization
end AppliedModelingLib

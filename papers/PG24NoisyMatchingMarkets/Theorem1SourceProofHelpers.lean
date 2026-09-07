import PG24NoisyMatchingMarkets.MainTheorems
import PG24NoisyMatchingMarkets.Theorem1TailMassHelpers
import Mathlib.Tactic

/-!
# PG24 Theorem 1 source-proof helpers

This module formalizes the model-independent arithmetic portions of the two
case proof of Proposition `thm1v2` in
`source_tex/proof-attenuating.tex`.  In particular, it does not assume a
cutoff sandwich, an interval-mass conclusion, or a tail-mass conclusion.
Those are the remaining semantic/model obligations of the source proof.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter
open AppliedModelingLib.Matching

/--
The sparse-block capacity calculation used in both cases of the source
attenuation proof.  A block containing at most `C^phi3` colleges has capacity
at most `alpha * C^(phi3 - 1)` when each college has capacity at most
`alpha / C`.
-/
theorem theorem1Tail_sparseBlock_capacity_le_alpha_rpow_phi3_sub_one
    {College : Type*} (active : Finset College) (capacity : College → ℝ)
    {alpha beta gamma : ℝ} {C : ℕ}
    (hC_pos : 0 < (C : ℝ)) (halpha_nonneg : 0 ≤ alpha)
    (hcard : (active.card : ℝ) ≤
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma))
    (hcapacity : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ)) :
    activeCapacity active capacity ≤
      alpha * Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma - 1) := by
  have hcap_nonneg : 0 ≤ alpha / (C : ℝ) :=
    div_nonneg halpha_nonneg (le_of_lt hC_pos)
  calc
    activeCapacity active capacity ≤
        (active.card : ℝ) * (alpha / (C : ℝ)) :=
      activeCapacity_le_card_mul_alpha_div_of_forall_le active capacity hcapacity
    _ ≤ Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
          (alpha / (C : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hcap_nonneg
    _ = alpha * Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma - 1) := by
      rw [div_eq_mul_inv]
      have hpow_one : Real.rpow (C : ℝ) (-1 : ℝ) = ((C : ℝ)⁻¹) := by
        exact Real.rpow_neg_one (C : ℝ)
      rw [← hpow_one]
      calc
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
            (alpha * Real.rpow (C : ℝ) (-1 : ℝ)) =
            alpha *
              (Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
                Real.rpow (C : ℝ) (-1 : ℝ)) := by ring
        _ = alpha * Real.rpow (C : ℝ)
            (theorem1TailPhi3 beta gamma + (-1 : ℝ)) := by
          exact congrArg (fun x : ℝ => alpha * x)
            (Real.rpow_add hC_pos
              (theorem1TailPhi3 beta gamma) (-1 : ℝ)).symm
        _ = alpha * Real.rpow (C : ℝ)
            (theorem1TailPhi3 beta gamma - 1) := by ring

/--
The sparse-block capacity calculation at the source rate `K(beta,gamma)`.
This is the checked content of the capacity estimate in Propositions
`duck-1` and `goose-1`; identifying a concrete cutoff block as sparse remains
a separate source-proof obligation.
-/
theorem theorem1Tail_sparseBlock_capacity_le_alpha_rpow_neg_K
    {College : Type*} (active : Finset College) (capacity : College → ℝ)
    {alpha beta gamma : ℝ} {C : ℕ}
    (hC_pos : 0 < (C : ℝ)) (halpha_nonneg : 0 ≤ alpha)
    (hcard : (active.card : ℝ) ≤
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma))
    (hcapacity : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ)) :
    activeCapacity active capacity ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rw [← theorem1TailPhi3_sub_one_eq_neg_K beta gamma]
  exact theorem1Tail_sparseBlock_capacity_le_alpha_rpow_phi3_sub_one
    active capacity hC_pos halpha_nonneg hcard hcapacity

/--
The strict version of the sparse-block capacity calculation.  This is the
literal inequality needed by Appendix Proposition `goose-1`: strict
per-college capacities and a strict sparse-cardinality bound preserve
strictness after summation.  Unlike the source proof, the exponent identity
is stated with the correct `phi3 - 1 = -K` sign.
-/
theorem theorem1Tail_sparseBlock_capacity_lt_alpha_rpow_neg_K
    {College : Type*} (active : Finset College) (capacity : College → ℝ)
    {alpha beta gamma : ℝ} {C : ℕ}
    (hC_pos : 0 < (C : ℝ)) (halpha_pos : 0 < alpha)
    (hcard : (active.card : ℝ) <
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma))
    (hcapacity : ∀ c ∈ active, capacity c < alpha / (C : ℝ)) :
    activeCapacity active capacity <
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rw [← theorem1TailPhi3_sub_one_eq_neg_K beta gamma]
  by_cases hactive : active.Nonempty
  · have hsum_lt : active.sum capacity <
        active.sum (fun _ : College => alpha / (C : ℝ)) := by
      exact Finset.sum_lt_sum_of_nonempty hactive (fun c hc => hcapacity c hc)
    have hcap_pos : 0 < alpha / (C : ℝ) := div_pos halpha_pos hC_pos
    have hcard_mul_lt :
        (active.card : ℝ) * (alpha / (C : ℝ)) <
          Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
            (alpha / (C : ℝ)) :=
      mul_lt_mul_of_pos_right hcard hcap_pos
    calc
      activeCapacity active capacity = active.sum capacity := rfl
      _ < active.sum (fun _ : College => alpha / (C : ℝ)) := hsum_lt
      _ = (active.card : ℝ) * (alpha / (C : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ < Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
            (alpha / (C : ℝ)) := hcard_mul_lt
      _ = alpha * Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma - 1) := by
        rw [div_eq_mul_inv]
        have hpow_one : Real.rpow (C : ℝ) (-1 : ℝ) = ((C : ℝ)⁻¹) := by
          exact Real.rpow_neg_one (C : ℝ)
        rw [← hpow_one]
        calc
          Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
              (alpha * Real.rpow (C : ℝ) (-1 : ℝ)) =
              alpha *
                (Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) *
                  Real.rpow (C : ℝ) (-1 : ℝ)) := by ring
          _ = alpha * Real.rpow (C : ℝ)
              (theorem1TailPhi3 beta gamma + (-1 : ℝ)) := by
            exact congrArg (fun x : ℝ => alpha * x)
              (Real.rpow_add hC_pos
                (theorem1TailPhi3 beta gamma) (-1 : ℝ)).symm
          _ = alpha * Real.rpow (C : ℝ)
              (theorem1TailPhi3 beta gamma - 1) := by ring
  · have hempty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
    subst active
    simp only [activeCapacity, Finset.sum_empty]
    exact mul_pos halpha_pos (Real.rpow_pos_of_pos hC_pos _)

/--
Rescale a polynomial variance bound by the square of a polynomial deviation
window.  This is the analytic calculation underneath each application of
Chebyshev in the source attenuation proof.
-/
theorem theorem1Tail_variance_div_rpow_window_sq_le
    {C beta window variance A : ℝ}
    (hC_pos : 0 < C)
    (hvariance : variance ≤ A * Real.rpow C (-beta)) :
    variance / (Real.rpow C window) ^ 2 ≤
      A * Real.rpow C (-beta - 2 * window) := by
  have hdenom_nonneg : 0 ≤ (Real.rpow C window) ^ 2 := sq_nonneg _
  calc
    variance / (Real.rpow C window) ^ 2 ≤
        (A * Real.rpow C (-beta)) / (Real.rpow C window) ^ 2 :=
      div_le_div_of_nonneg_right hvariance hdenom_nonneg
    _ = A * Real.rpow C (-beta - 2 * window) := by
      have hsq : (Real.rpow C window) ^ 2 =
          Real.rpow C (window + window) := by
        calc
          (Real.rpow C window) ^ 2 =
              Real.rpow C window * Real.rpow C window := by ring
          _ = Real.rpow C (window + window) :=
            (Real.rpow_add hC_pos window window).symm
      rw [hsq]
      calc
        (A * Real.rpow C (-beta)) / Real.rpow C (window + window) =
            A * (Real.rpow C (-beta) /
              Real.rpow C (window + window)) := by ring
        _ = A * Real.rpow C ((-beta) - (window + window)) := by
          exact congrArg (fun x : ℝ => A * x)
            (Real.rpow_sub hC_pos (-beta) (window + window)).symm
        _ = A * Real.rpow C (-beta - 2 * window) := by ring

/--
The large-gap Case 2 Chebyshev step at the source exponent `K(beta,gamma)`.
The caller supplies the concrete deviation event and variance estimate; no
cutoff geometry is hidden in this lemma.
-/
theorem theorem1Tail_case2_chebyshev_error_le_rpow_neg_K
    {beta gamma C probability variance A : ℝ}
    (hC_pos : 0 < C)
    (hdeviation : probability ≤
      variance / (Real.rpow C (theorem1TailPhi4 beta gamma)) ^ 2)
    (hvariance : variance ≤ A * Real.rpow C (-beta)) :
    probability ≤ A * Real.rpow C (-(theorem1TailK beta gamma)) := by
  calc
    probability ≤ variance / (Real.rpow C (theorem1TailPhi4 beta gamma)) ^ 2 :=
      hdeviation
    _ ≤ A * Real.rpow C (-beta - 2 * theorem1TailPhi4 beta gamma) :=
      theorem1Tail_variance_div_rpow_window_sq_le hC_pos hvariance
    _ = A * Real.rpow C (-(theorem1TailK beta gamma)) := by
      rw [theorem1Tail_case2_chebyshev_exp_eq_neg_K beta gamma]

/--
The dense-cluster Case 1 Chebyshev step before the source union-bound factor.
The exponent `beta * phi2` is the variance rate of the maximum over the dense
cluster; proving that rate for the integer-sized cluster remains separate.
-/
theorem theorem1Tail_case1_denseCluster_chebyshev_error_le
    {beta gamma C probability variance A : ℝ}
    (hC_pos : 0 < C)
    (hdeviation : probability ≤
      variance / (Real.rpow C (theorem1TailPhi1 beta gamma)) ^ 2)
    (hvariance : variance ≤
      A * Real.rpow C (-(beta * theorem1TailPhi2 beta gamma))) :
    probability ≤ A * Real.rpow C
      (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma) := by
  have hscaled := theorem1Tail_variance_div_rpow_window_sq_le
    (C := C) (beta := beta * theorem1TailPhi2 beta gamma)
    (window := theorem1TailPhi1 beta gamma) hC_pos hvariance
  calc
    probability ≤ variance / (Real.rpow C (theorem1TailPhi1 beta gamma)) ^ 2 :=
      hdeviation
    _ ≤ A * Real.rpow C
        (-(beta * theorem1TailPhi2 beta gamma) -
          2 * theorem1TailPhi1 beta gamma) := hscaled
    _ = A * Real.rpow C
        (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma) := by
      ring

/--
Algebraic form of the source's Case 1 union-bound/Chebyshev exponent
calculation.  It is intentionally stated for an arbitrary error;
the event inclusion and the variance estimate that yield the hypotheses are
separate obligations.
-/
theorem theorem1Tail_case1_union_error_le_rpow_neg_K
    {beta gamma C error A : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hC_pos : 0 < C)
    (herror : error ≤
      A * Real.rpow C
        (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma)) :
    Real.rpow C (1 - theorem1TailPhi2 beta gamma) * error ≤
      A * Real.rpow C (-(theorem1TailK beta gamma)) := by
  have hfactor_nonneg : 0 ≤ Real.rpow C (1 - theorem1TailPhi2 beta gamma) :=
    le_of_lt (Real.rpow_pos_of_pos hC_pos _)
  calc
    Real.rpow C (1 - theorem1TailPhi2 beta gamma) * error ≤
        Real.rpow C (1 - theorem1TailPhi2 beta gamma) *
          (A * Real.rpow C
            (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma)) :=
      mul_le_mul_of_nonneg_left herror hfactor_nonneg
    _ = A * Real.rpow C
        (1 - 2 * theorem1TailPhi1 beta gamma -
          (1 + beta) * theorem1TailPhi2 beta gamma) := by
      calc
        Real.rpow C (1 - theorem1TailPhi2 beta gamma) *
            (A * Real.rpow C
              (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma)) =
            A *
              (Real.rpow C (1 - theorem1TailPhi2 beta gamma) *
                Real.rpow C
                  (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma)) := by
          ring
        _ = A * Real.rpow C
            ((1 - theorem1TailPhi2 beta gamma) +
              (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma)) := by
          exact congrArg (fun x : ℝ => A * x)
            (Real.rpow_add hC_pos
              (1 - theorem1TailPhi2 beta gamma)
              (-2 * theorem1TailPhi1 beta gamma - beta * theorem1TailPhi2 beta gamma)).symm
        _ = A * Real.rpow C
            (1 - 2 * theorem1TailPhi1 beta gamma -
              (1 + beta) * theorem1TailPhi2 beta gamma) := by ring
    _ = A * Real.rpow C (-(theorem1TailK beta gamma)) := by
      rw [theorem1Tail_case1_chebyshev_exp_eq_neg_K hbeta hgamma]

/--
The full dense-cluster probability rate after Chebyshev and the source's
union-bound factor.  The group decomposition/event inclusion remains an
explicit caller premise.
-/
theorem theorem1Tail_case1_union_chebyshev_error_le_rpow_neg_K
    {beta gamma C probability deviation variance A : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hC_pos : 0 < C)
    (hunion : probability ≤
      Real.rpow C (1 - theorem1TailPhi2 beta gamma) * deviation)
    (hdeviation : deviation ≤
      variance / (Real.rpow C (theorem1TailPhi1 beta gamma)) ^ 2)
    (hvariance : variance ≤
      A * Real.rpow C (-(beta * theorem1TailPhi2 beta gamma))) :
    probability ≤ A * Real.rpow C (-(theorem1TailK beta gamma)) := by
  have hdense := theorem1Tail_case1_denseCluster_chebyshev_error_le
    (beta := beta) (gamma := gamma) hC_pos hdeviation hvariance
  calc
    probability ≤ Real.rpow C (1 - theorem1TailPhi2 beta gamma) * deviation :=
      hunion
    _ ≤ A * Real.rpow C (-(theorem1TailK beta gamma)) :=
      theorem1Tail_case1_union_error_le_rpow_neg_K
        hbeta hgamma hC_pos hdense

/--
The Holder-window contribution in Case 1 has the source rate `C^(-K)` once
the window has width `3 * C^phi1`.  This lemma does not assert Holder
regularity; the concrete interval-mass bound is kept as an input.
-/
theorem theorem1Tail_case1_holder_window_le_rpow_neg_K
    {beta gamma C intervalMass holderConstant : ℝ}
    (hC_pos : 0 < C)
    (hwindow : intervalMass ≤
      holderConstant * Real.rpow
        (3 * Real.rpow C (theorem1TailPhi1 beta gamma)) gamma) :
    intervalMass ≤
      (holderConstant * Real.rpow 3 gamma) *
        Real.rpow C (-(theorem1TailK beta gamma)) := by
  calc
    intervalMass ≤ holderConstant * Real.rpow
        (3 * Real.rpow C (theorem1TailPhi1 beta gamma)) gamma := hwindow
    _ = (holderConstant * Real.rpow 3 gamma) *
        Real.rpow C (gamma * theorem1TailPhi1 beta gamma) := by
      have hmul : Real.rpow
          (3 * Real.rpow C (theorem1TailPhi1 beta gamma)) gamma =
          Real.rpow 3 gamma *
            Real.rpow (Real.rpow C (theorem1TailPhi1 beta gamma)) gamma := by
        exact Real.mul_rpow (by norm_num) (le_of_lt
          (Real.rpow_pos_of_pos hC_pos _))
      have hcompose : Real.rpow
          (Real.rpow C (theorem1TailPhi1 beta gamma)) gamma =
          Real.rpow C (theorem1TailPhi1 beta gamma * gamma) := by
        exact (Real.rpow_mul (le_of_lt hC_pos)
          (theorem1TailPhi1 beta gamma) gamma).symm
      rw [hmul, hcompose]
      ring
    _ = (holderConstant * Real.rpow 3 gamma) *
        Real.rpow C (-(theorem1TailK beta gamma)) := by
      rw [← theorem1Tail_gamma_mul_phi1_eq_neg_K beta gamma]

/--
Combine four independently verified polynomial-rate terms.  This is the
bookkeeping step at the end of the dense-cluster branch: source geometry and
measure arguments must establish the four component bounds before this lemma
can be used.
-/
theorem theorem1Tail_four_component_rate_bound
    {tailMass component1 component2 component3 component4 C rate
      constant1 constant2 constant3 constant4 : ℝ}
    (htail : tailMass ≤ component1 + component2 + component3 + component4)
    (h1 : component1 ≤ constant1 * Real.rpow C (-rate))
    (h2 : component2 ≤ constant2 * Real.rpow C (-rate))
    (h3 : component3 ≤ constant3 * Real.rpow C (-rate))
    (h4 : component4 ≤ constant4 * Real.rpow C (-rate)) :
    tailMass ≤ (constant1 + constant2 + constant3 + constant4) *
      Real.rpow C (-rate) := by
  calc
    tailMass ≤ component1 + component2 + component3 + component4 := htail
    _ ≤ constant1 * Real.rpow C (-rate) +
          constant2 * Real.rpow C (-rate) +
          constant3 * Real.rpow C (-rate) +
          constant4 * Real.rpow C (-rate) := by
      gcongr
    _ = (constant1 + constant2 + constant3 + constant4) *
          Real.rpow C (-rate) := by ring

/--
Combine the three polynomial-rate terms in the source large-gap branch,
including its sparse-block capacity contribution.
-/
theorem theorem1Tail_three_component_rate_bound
    {tailMass component1 component2 component3 C rate
      constant1 constant2 constant3 : ℝ}
    (htail : tailMass ≤ component1 + component2 + component3)
    (h1 : component1 ≤ constant1 * Real.rpow C (-rate))
    (h2 : component2 ≤ constant2 * Real.rpow C (-rate))
    (h3 : component3 ≤ constant3 * Real.rpow C (-rate)) :
    tailMass ≤ (constant1 + constant2 + constant3) *
      Real.rpow C (-rate) := by
  calc
    tailMass ≤ component1 + component2 + component3 := htail
    _ ≤ constant1 * Real.rpow C (-rate) +
          constant2 * Real.rpow C (-rate) +
          constant3 * Real.rpow C (-rate) := by
      gcongr
    _ = (constant1 + constant2 + constant3) *
          Real.rpow C (-rate) := by ring

/--
Algebraic form of the source's Case 2 Chebyshev exponent calculation.  The
probability event and variance bound are inputs; this lemma only discharges
their polynomial-rate conversion.
-/
theorem theorem1Tail_case2_error_le_rpow_neg_K
    {beta gamma C error A : ℝ}
    (herror : error ≤
      A * Real.rpow C
        (-beta - 2 * theorem1TailPhi4 beta gamma)) :
    error ≤ A * Real.rpow C (-(theorem1TailK beta gamma)) := by
  rw [← theorem1Tail_case2_chebyshev_exp_eq_neg_K beta gamma]
  exact herror

/--
The mass-budget rearrangement used in `duck-2` and `goose-2`.  If every value
in a region of mass `intervalMass` matches with probability at least
`1 - error`, while total matched mass is at most `totalSupply`, then that
region's mass is bounded by `totalSupply * error / (1 - error)`.
-/
theorem theorem1Tail_interval_mass_le_supply_mul_error_div_one_sub
    {totalSupply intervalMass error : ℝ}
    (herror_lt_one : error < 1)
    (hbudget : (1 - error) * (totalSupply + intervalMass) ≤ totalSupply) :
    intervalMass ≤ totalSupply * error / (1 - error) := by
  have hfactor_pos : 0 < 1 - error := by linarith
  have hscaled : (1 - error) * intervalMass ≤ totalSupply * error := by
    nlinarith [hbudget]
  rw [le_div_iff₀ hfactor_pos]
  nlinarith [hscaled]

/--
A denominator-free corollary of the source mass-budget calculation.  Once the
failure error is at most one half, the interval mass is at most twice the
total supply times that error.
-/
theorem theorem1Tail_interval_mass_le_two_mul_supply_mul_error
    {totalSupply intervalMass error : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply) (herror_nonneg : 0 ≤ error)
    (herror_le_half : error ≤ 1 / 2)
    (hbudget : (1 - error) * (totalSupply + intervalMass) ≤ totalSupply) :
    intervalMass ≤ 2 * totalSupply * error := by
  have herror_lt_one : error < 1 := by linarith
  have hbase := theorem1Tail_interval_mass_le_supply_mul_error_div_one_sub
    herror_lt_one hbudget
  have hdenom_pos : 0 < 1 - error := by linarith
  have hrecip_le_two : (1 : ℝ) / (1 - error) ≤ 2 := by
    rw [div_le_iff₀ hdenom_pos]
    linarith
  have hsupply_error_nonneg : 0 ≤ totalSupply * error :=
    mul_nonneg htotalSupply_nonneg herror_nonneg
  calc
    intervalMass ≤ totalSupply * error / (1 - error) := hbase
    _ = (totalSupply * error) * ((1 : ℝ) / (1 - error)) := by ring
    _ ≤ (totalSupply * error) * 2 :=
      mul_le_mul_of_nonneg_left hrecip_le_two hsupply_error_nonneg
    _ = 2 * totalSupply * error := by ring

end

end PG24NoisyMatchingMarkets

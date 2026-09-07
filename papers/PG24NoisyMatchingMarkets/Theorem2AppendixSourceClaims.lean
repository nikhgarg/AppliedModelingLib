import PG24NoisyMatchingMarkets.MainTheorems

/-!
# PG24 Theorem 2 appendix source claims

This module packages exact local consequences used by named propositions in
`source_tex/proof-amplifying.tex`.  It deliberately retains the source's
strict open intervals when the preceding endpoint/product hypotheses provide
them, instead of weakening a source proposition merely for convenience.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter

/--
The strict, uniform-in-value form of the large-firm interval calculation in
Appendix Proposition `lt-large-firms`.  The strict endpoint-gap estimate is
the output of the preceding `lt-approx-F2` step; no strictness is assumed for
the two supply endpoint estimates.
-/
theorem theorem2_largeFirm_strict_interval_eventually_of_endpoint_product_error
    {pLarge : ℕ → ℝ → ℝ} {vLow vHigh S alpha epsilon sigma : ℝ}
    (hp_mono : ∀ᶠ C : ℕ in atTop, Monotone (pLarge C))
    (hupper_low : ∀ᶠ C : ℕ in atTop, pLarge C vLow ≤ S + epsilon)
    (hlower_high : ∀ᶠ C : ℕ in atTop,
      S - (1 + alpha) * epsilon ≤ pLarge C vHigh)
    (hdiff : ∀ᶠ C : ℕ in atTop,
      pLarge C vHigh - pLarge C vLow <
        1 - Real.exp (-(2 * epsilon * sigma))) :
    ∀ᶠ C : ℕ in atTop, ∀ v : ℝ, vLow < v → v < vHigh →
      S - (1 + alpha) * epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))) < pLarge C v ∧
        pLarge C v < S + epsilon +
          (1 - Real.exp (-(2 * epsilon * sigma))) := by
  filter_upwards [hp_mono, hupper_low, hlower_high, hdiff] with
    C hmono hupperC hlowerC hdiffC
  intro v hvLow hvHigh
  have hlow_mono : pLarge C vLow ≤ pLarge C v := hmono hvLow.le
  have hhigh_mono : pLarge C v ≤ pLarge C vHigh := hmono hvHigh.le
  constructor <;> linarith

/--
The uniform-in-value form of Appendix Proposition `lt-small-firms`.  The
source first derives its capacity-mass inequality at `vStar` and then invokes
monotonicity for every lower value; the conclusion here keeps that order of
quantifiers explicit.
-/
theorem theorem2_smallFirmSourceBound_eventually_uniform_of_star_capacity_mass
    {pSmall : ℕ → ℝ → ℝ} {vStar totalSupply alpha epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hp_mono : ∀ᶠ C : ℕ in atTop, Monotone (pSmall C))
    (hcapacity_mass_star :
      ∀ᶠ C : ℕ in atTop,
        Real.sqrt epsilon *
            (1 - totalSupply - epsilon -
              (1 - Real.exp (-(2 * epsilon * sigma)))) *
            pSmall C vStar ≤
          epsilon * alpha) :
    ∀ᶠ C : ℕ in atTop, ∀ v : ℝ, v < vStar →
      theorem2_smallFirmSourceBound
        totalSupply alpha epsilon sigma (pSmall C v) := by
  filter_upwards [hp_mono, hcapacity_mass_star] with C hmono hcapacityC
  intro v hv
  exact theorem2_smallFirmSourceBound_of_star_capacity_mass
    hepsilon_pos hden_pos hmono hv.le hcapacityC

/--
The strict finite-product calculation in Appendix Proposition `lt-approx-F2`.
The source's displayed strict inequality needs both a nonempty large-firm set
and a strict per-college failure-ratio floor; the weaker non-strict variant is
insufficient to recover it.  These two facts are therefore explicit here.
-/
theorem theorem2_independentAffordanceProbability_difference_lt_exp_error
    {College : Type*} (active : Finset College)
    (qLow qHigh : College → ℝ) {C : ℕ} {epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon) (hsigma_pos : 0 < sigma)
    (hC_pos : 0 < (C : ℝ)) (hcard : (active.card : ℝ) ≤ (C : ℝ))
    (hactive : active.Nonempty)
    (hratio : ∀ c ∈ active,
      Real.exp (-(2 * epsilon * sigma / (C : ℝ))) <
        (1 - qHigh c) / (1 - qLow c))
    (hlow_failure_pos : ∀ c ∈ active, 0 < 1 - qLow c)
    (hlow_failure_le_one : ∀ c ∈ active, 1 - qLow c ≤ 1) :
    independentAffordanceProbability active qHigh -
        independentAffordanceProbability active qLow <
      1 - Real.exp (-(2 * epsilon * sigma)) := by
  have hA_pos : 0 < 2 * epsilon * sigma := by nlinarith
  have hprod_floor :
      Real.exp (-(2 * epsilon * sigma)) ≤
        ∏ _c ∈ active, Real.exp (-(2 * epsilon * sigma / (C : ℝ))) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      AppliedModelingLib.Math.exp_neg_le_finset_prod_const_exp_neg_div_of_card_le
        (s := active) (A := 2 * epsilon * sigma) (C := (C : ℝ))
        hA_pos.le hC_pos hcard
  let lowProd : ℝ := ∏ c ∈ active, (1 - qLow c)
  let highProd : ℝ := ∏ c ∈ active, (1 - qHigh c)
  let ratioProd : ℝ :=
    ∏ c ∈ active, (1 - qHigh c) / (1 - qLow c)
  have hlow_nonneg : ∀ c ∈ active, 0 ≤ 1 - qLow c :=
    fun c hc => (hlow_failure_pos c hc).le
  have hlowProd_pos : 0 < lowProd := by
    dsimp [lowProd]
    exact Finset.prod_pos hlow_failure_pos
  have hlowProd_le_one : lowProd ≤ 1 := by
    dsimp [lowProd]
    exact Finset.prod_le_one hlow_nonneg hlow_failure_le_one
  have hconstant_lt_ratioProd :
      (∏ _c ∈ active, Real.exp (-(2 * epsilon * sigma / (C : ℝ)))) <
        ratioProd := by
    dsimp [ratioProd]
    refine Finset.prod_lt_prod (fun _ _ => Real.exp_pos _)
      (fun c hc => (hratio c hc).le) ?_
    rcases hactive with ⟨c, hc⟩
    exact ⟨c, hc, hratio c hc⟩
  have hfloor_lt_ratioProd :
      Real.exp (-(2 * epsilon * sigma)) < ratioProd :=
    lt_of_le_of_lt hprod_floor hconstant_lt_ratioProd
  have hratioProd_eq : ratioProd = highProd / lowProd := by
    dsimp [ratioProd, highProd, lowProd]
    exact Finset.prod_div_distrib (s := active)
      (f := fun c => 1 - qHigh c) (g := fun c => 1 - qLow c)
  have hfloor_lt_div :
      Real.exp (-(2 * epsilon * sigma)) < highProd / lowProd := by
    simpa [hratioProd_eq] using hfloor_lt_ratioProd
  have hmul :
      Real.exp (-(2 * epsilon * sigma)) * lowProd < highProd := by
    have h := mul_lt_mul_of_pos_right hfloor_lt_div hlowProd_pos
    have hcancel : highProd / lowProd * lowProd = highProd := by
      exact div_mul_cancel₀ highProd (ne_of_gt hlowProd_pos)
    simpa [hcancel] using h
  have hdiff :
      lowProd - highProd <
        lowProd - Real.exp (-(2 * epsilon * sigma)) * lowProd :=
    sub_lt_sub_left hmul lowProd
  have hfactor :
      lowProd - Real.exp (-(2 * epsilon * sigma)) * lowProd =
        (1 - Real.exp (-(2 * epsilon * sigma))) * lowProd := by
    ring
  have hglobal_le_one : Real.exp (-(2 * epsilon * sigma)) ≤ 1 := by
    exact (Real.exp_le_one_iff).mpr (by linarith)
  have hscale :
      (1 - Real.exp (-(2 * epsilon * sigma))) * lowProd ≤
        1 - Real.exp (-(2 * epsilon * sigma)) := by
    exact mul_le_of_le_one_right (sub_nonneg.mpr hglobal_le_one)
      hlowProd_le_one
  have hproduct :
      (∏ c ∈ active, (1 - qLow c)) -
          (∏ c ∈ active, (1 - qHigh c)) <
        1 - Real.exp (-(2 * epsilon * sigma)) := by
    calc
      (∏ c ∈ active, (1 - qLow c)) -
          (∏ c ∈ active, (1 - qHigh c)) =
          lowProd - highProd := by rfl
      _ < lowProd - Real.exp (-(2 * epsilon * sigma)) * lowProd := hdiff
      _ = (1 - Real.exp (-(2 * epsilon * sigma))) * lowProd := hfactor
      _ ≤ 1 - Real.exp (-(2 * epsilon * sigma)) := hscale
  simpa [independentAffordanceProbability, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc] using hproduct

/-- Eventual source-indexed form of the strict `lt-approx-F2` product bound. -/
theorem theorem2_independentAffordanceProbability_difference_eventually_lt_exp_error
    {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {qLow qHigh : ∀ n : ℕ, Fin (n + 1) → ℝ} {epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon) (hsigma_pos : 0 < sigma)
    (hactive : ∀ᶠ n : ℕ in atTop, (active n).Nonempty)
    (hratio : ∀ᶠ n : ℕ in atTop, ∀ c ∈ active n,
      Real.exp (-(2 * epsilon * sigma / ((n + 1 : ℕ) : ℝ))) <
        (1 - qHigh n c) / (1 - qLow n c))
    (hlow_failure_pos : ∀ᶠ n : ℕ in atTop, ∀ c ∈ active n,
      0 < 1 - qLow n c)
    (hlow_failure_le_one : ∀ᶠ n : ℕ in atTop, ∀ c ∈ active n,
      1 - qLow n c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      independentAffordanceProbability (active n) (qHigh n) -
          independentAffordanceProbability (active n) (qLow n) <
        1 - Real.exp (-(2 * epsilon * sigma)) := by
  filter_upwards [hactive, hratio, hlow_failure_pos, hlow_failure_le_one] with
    n hactiveN hratioN hlowPosN hlowLeN
  have hn_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have hcard : ((active n).card : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    have hcard_nat : (active n).card ≤ Fintype.card (Fin (n + 1)) :=
      Finset.card_le_univ (s := active n)
    have hcard_nat' : (active n).card ≤ n + 1 := by
      simpa using hcard_nat
    exact_mod_cast hcard_nat'
  exact theorem2_independentAffordanceProbability_difference_lt_exp_error
    (active n) (qLow n) (qHigh n) hepsilon_pos hsigma_pos hn_pos hcard
      hactiveN hratioN hlowPosN hlowLeN

end

end PG24NoisyMatchingMarkets

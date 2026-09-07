import AppliedModelingLib.Foundations.Math.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter Topology

namespace AppliedModelingLib
namespace Math

/-!
# Power Comparison Lemmas

Reusable algebraic comparisons for objectives whose marginal terms are
negative powers.

## Main declarations

- `rpow_neg_marginal_lt_of_scaled_lt`: a scaled-count inequality implies the
  corresponding strict comparison between negative-power weighted marginals.
-/

/--
If `y / p_dst^(1/eta) < x / p_src^(1/eta)`, then the weighted negative-power
marginal at `x` is smaller than the destination marginal at `y`.

This is the algebraic core behind power-law first-order conditions.
-/
theorem rpow_neg_marginal_lt_of_scaled_lt
    {p_src p_dst c eta x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst) (hc : 0 < c)
    (heta : 0 < eta) (hx : 0 < x) (hy : 0 < y)
    (hscaled : y / p_dst ^ (1 / eta) < x / p_src ^ (1 / eta)) :
    p_src * (c * x ^ (-eta)) < p_dst * (c * y ^ (-eta)) := by
  let wsrc : ℝ := p_src ^ (1 / eta)
  let wdst : ℝ := p_dst ^ (1 / eta)
  have hwsrc_pos : 0 < wsrc := by
    dsimp [wsrc]
    exact Real.rpow_pos_of_pos hp_src (1 / eta)
  have hwdst_pos : 0 < wdst := by
    dsimp [wdst]
    exact Real.rpow_pos_of_pos hp_dst (1 / eta)
  have hleft_pos : 0 < y / wdst := div_pos hy hwdst_pos
  have hright_pos : 0 < x / wsrc := div_pos hx hwsrc_pos
  have hpow_lt :
      (y / wdst) ^ eta < (x / wsrc) ^ eta :=
    Real.rpow_lt_rpow (le_of_lt hleft_pos)
      (by simpa [wsrc, wdst] using hscaled) heta
  have hsrc_pow :
      (x / wsrc) ^ eta = x ^ eta / p_src := by
    dsimp [wsrc]
    rw [Real.div_rpow (le_of_lt hx) (le_of_lt hwsrc_pos) eta]
    rw [← Real.rpow_mul (le_of_lt hp_src) (1 / eta) eta]
    have hmul : (1 / eta) * eta = 1 := by field_simp [ne_of_gt heta]
    rw [hmul, Real.rpow_one]
  have hdst_pow :
      (y / wdst) ^ eta = y ^ eta / p_dst := by
    dsimp [wdst]
    rw [Real.div_rpow (le_of_lt hy) (le_of_lt hwdst_pos) eta]
    rw [← Real.rpow_mul (le_of_lt hp_dst) (1 / eta) eta]
    have hmul : (1 / eta) * eta = 1 := by field_simp [ne_of_gt heta]
    rw [hmul, Real.rpow_one]
  have hpow_ratio_lt :
      y ^ eta / p_dst < x ^ eta / p_src := by
    simpa [hsrc_pow, hdst_pow] using hpow_lt
  have hxpow_pos : 0 < x ^ eta := Real.rpow_pos_of_pos hx eta
  have hypow_pos : 0 < y ^ eta := Real.rpow_pos_of_pos hy eta
  have hscaled_marginal :
      p_src * x ^ (-eta) < p_dst * y ^ (-eta) := by
    have hinv_lt :
        1 / (x ^ eta / p_src) < 1 / (y ^ eta / p_dst) :=
      one_div_lt_one_div_of_lt (div_pos hypow_pos hp_dst) hpow_ratio_lt
    have hleft :
        1 / (x ^ eta / p_src) = p_src / x ^ eta := by
      field_simp [ne_of_gt hp_src, ne_of_gt hxpow_pos]
    have hright :
        1 / (y ^ eta / p_dst) = p_dst / y ^ eta := by
      field_simp [ne_of_gt hp_dst, ne_of_gt hypow_pos]
    calc
      p_src * x ^ (-eta) = p_src / x ^ eta := by
        rw [Real.rpow_neg (le_of_lt hx)]
        ring
      _ = 1 / (x ^ eta / p_src) := by rw [hleft]
      _ < 1 / (y ^ eta / p_dst) := hinv_lt
      _ = p_dst / y ^ eta := hright
      _ = p_dst * y ^ (-eta) := by
        rw [Real.rpow_neg (le_of_lt hy)]
        ring
  nlinarith [mul_lt_mul_of_pos_right hscaled_marginal hc]

/--
Two-coefficient version of `rpow_neg_marginal_lt_of_scaled_lt`.

This is useful when asymptotic sandwich bounds put a `(1 + ε)` coefficient on
the source upper bound and a `(1 - ε)` coefficient on the destination lower
bound.
-/
theorem rpow_neg_marginal_lt_of_scaled_lt'
    {p_src p_dst c_src c_dst eta x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst)
    (hc_src : 0 < c_src) (hc_dst : 0 < c_dst)
    (heta : 0 < eta) (hx : 0 < x) (hy : 0 < y)
    (hscaled :
      y / (p_dst * c_dst) ^ (1 / eta) <
        x / (p_src * c_src) ^ (1 / eta)) :
    p_src * (c_src * x ^ (-eta)) <
      p_dst * (c_dst * y ^ (-eta)) := by
  have hcore :=
    rpow_neg_marginal_lt_of_scaled_lt
      (p_src := p_src * c_src) (p_dst := p_dst * c_dst)
      (c := 1) (eta := eta) (x := x) (y := y)
      (mul_pos hp_src hc_src) (mul_pos hp_dst hc_dst)
      (by norm_num) heta hx hy hscaled
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcore

/--
Reciprocal powered weights are stable under a `1 + o(1)` multiplicative
perturbation.

This packages the continuity step needed by asymptotic first-order-condition
proofs: replacing a positive weight `p` by `p * (1 + ε_N)` changes
`1 / weight^γ` by `o(1)` whenever `ε_N -> 0`.
-/
theorem reciprocal_rpow_one_add_perturb_tendsToZero
    {ε : ℕ → ℝ} (hε : TendsToZero ε) {p γ : ℝ} (hp : 0 < p) :
    TendsToZero
      (fun N : ℕ =>
        |1 / (p ^ γ) - 1 / ((p * (1 + ε N)) ^ γ)|) := by
  rw [TendsToZero] at hε ⊢
  have hbase :
      Tendsto (fun N : ℕ => p * (1 + ε N)) atTop (nhds (p * (1 + 0))) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.add hε).const_mul p
  have hpow :
      Tendsto (fun N : ℕ => (p * (1 + ε N)) ^ γ)
        atTop (nhds ((p * (1 + 0)) ^ γ)) := by
    exact hbase.rpow_const (p := γ)
      (Or.inl (by positivity : p * (1 + 0) ≠ 0))
  have hrecip :
      Tendsto (fun N : ℕ => 1 / ((p * (1 + ε N)) ^ γ))
        atTop (nhds (1 / ((p * (1 + 0)) ^ γ))) := by
    simpa [one_div] using
      hpow.inv₀
        (by
          have hpos : 0 < (p * (1 + 0 : ℝ)) ^ γ := by
            exact Real.rpow_pos_of_pos (by positivity : 0 < p * (1 + 0 : ℝ)) γ
          exact ne_of_gt hpos)
  have hsub :
      Tendsto
        (fun N : ℕ =>
          1 / (p ^ γ) - 1 / ((p * (1 + ε N)) ^ γ))
        atTop
        (nhds (1 / (p ^ γ) - 1 / ((p * (1 + 0)) ^ γ))) := by
    exact tendsto_const_nhds.sub hrecip
  have hlimit_zero :
      1 / (p ^ γ) - 1 / ((p * (1 + 0 : ℝ)) ^ γ) = 0 := by
    ring_nf
  have habs := hsub.abs
  simpa [hlimit_zero] using habs

/--
Reciprocal powered weights are stable under a `1 - o(1)` multiplicative
perturbation.
-/
theorem reciprocal_rpow_one_sub_perturb_tendsToZero
    {ε : ℕ → ℝ} (hε : TendsToZero ε) {p γ : ℝ} (hp : 0 < p) :
    TendsToZero
      (fun N : ℕ =>
        |1 / ((p * (1 - ε N)) ^ γ) - 1 / (p ^ γ)|) := by
  rw [TendsToZero] at hε ⊢
  have hbase :
      Tendsto (fun N : ℕ => p * (1 - ε N)) atTop (nhds (p * (1 - 0))) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hε).const_mul p
  have hpow :
      Tendsto (fun N : ℕ => (p * (1 - ε N)) ^ γ)
        atTop (nhds ((p * (1 - 0)) ^ γ)) := by
    exact hbase.rpow_const (p := γ)
      (Or.inl (by positivity : p * (1 - 0) ≠ 0))
  have hrecip :
      Tendsto (fun N : ℕ => 1 / ((p * (1 - ε N)) ^ γ))
        atTop (nhds (1 / ((p * (1 - 0)) ^ γ))) := by
    simpa [one_div] using
      hpow.inv₀
        (by
          have hpos : 0 < (p * (1 - 0 : ℝ)) ^ γ := by
            exact Real.rpow_pos_of_pos (by positivity : 0 < p * (1 - 0 : ℝ)) γ
          exact ne_of_gt hpos)
  have hsub :
      Tendsto
        (fun N : ℕ =>
          1 / ((p * (1 - ε N)) ^ γ) - 1 / (p ^ γ))
        atTop
        (nhds (1 / ((p * (1 - 0)) ^ γ) - 1 / (p ^ γ))) := by
    exact hrecip.sub tendsto_const_nhds
  have hlimit_zero :
      1 / ((p * (1 - 0 : ℝ)) ^ γ) - 1 / (p ^ γ) = 0 := by
    ring_nf
  have habs := hsub.abs
  simpa [hlimit_zero] using habs

end Math
end AppliedModelingLib

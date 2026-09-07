import PRPKG24AccuracyDiversity.Exchange
import PRPKG24AccuracyDiversity.Optimization
import PRPKG24AccuracyDiversity.TopKOracle
import AppliedModelingLib.Applications.RecommenderSystems.AllocationSequence
import AppliedModelingLib.Foundations.Math.PowerComparisons
import AppliedModelingLib.Foundations.Probability.OrderStatistics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Changing finitely many entries of a zero-convergent error schedule preserves
zero convergence. This is useful when an asymptotic certificate only starts
after a finite threshold: make the finitely many early errors deliberately
large, and keep the original asymptotic schedule afterwards.
-/
theorem tendsToZero_if_lt_const
    {ε : ℕ → ℝ} (hε : AppliedModelingLib.Math.TendsToZero ε)
    (threshold : ℕ) (C : ℝ) :
    AppliedModelingLib.Math.TendsToZero
      (fun N => if N < threshold then C else ε N) :=  AppliedModelingLib.Math.tendsToZero_if_lt_const hε threshold C

/--
Source Theorem 1(i) asymptotic algebra: an exact geometric tail has the
paper's logarithmic saturation ratio.
-/
theorem finiteDiscrete_log_geometric_tail_ratio
    {C r : ℝ} (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.log (C * r ^ N) / (Real.log r * (N : ℝ)))
      atTop (nhds 1) :=
  AppliedModelingLib.Math.log_geometric_tail_ratio hC hr_pos hr_lt_one

/-- `log N / N -> 0`, used by the finite-discrete polynomial tail factor. -/
theorem tendsto_log_nat_div_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
  AppliedModelingLib.Math.tendsto_log_nat_div_nat_nhds_zero

/-- Natural square root tends to infinity along natural numbers. -/
theorem tendsto_nat_sqrt_atTop :
    Tendsto (fun N : ℕ => Nat.sqrt N) atTop atTop :=
  AppliedModelingLib.Math.tendsto_nat_sqrt_atTop

/--
The square-root integer gap is sublinear in the certificate sense:
`(sqrt N + 1) / N -> 0`.
-/
theorem finiteDiscrete_nat_sqrt_gap_error_tendsToZero :
    AppliedModelingLib.Math.TendsToZero
      (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)) :=
  AppliedModelingLib.Math.nat_sqrt_gap_error_tendsToZero

/--
For any `0 < rho < 1`, the square-root integer gap kills every fixed
polynomial factor: `N^k * rho^(sqrt N) -> 0`.
-/
theorem finiteDiscrete_nat_sqrt_gap_polynomial_geometric_tends_to_zero
    (k : ℕ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ) ^ k * rho ^ (Nat.sqrt N))
      atTop (nhds 0) :=
  AppliedModelingLib.Math.nat_sqrt_gap_polynomial_geometric_tends_to_zero
    k hrho_pos hrho_lt_one

/--
Source Theorem 1(i) asymptotic algebra: multiplying a geometric tail by any
fixed polynomial factor does not change the logarithmic saturation ratio.
-/
theorem finiteDiscrete_log_polynomial_geometric_tail_ratio
    {C r : ℝ} (d : ℕ)
    (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ)))
      atTop (nhds 1) :=
  AppliedModelingLib.Math.log_polynomial_geometric_tail_ratio
    d hC hr_pos hr_lt_one

/--
Source Theorem 1(i) asymptotic algebra: the paper's lower geometric and upper
polynomial-times-geometric bounds squeeze the logarithmic saturation ratio to
one.
-/
theorem finiteDiscrete_log_tail_ratio_of_geometric_bounds
    {gap : ℕ → ℝ} {lower upper r : ℝ} (d : ℕ)
    (hlower_pos : 0 < lower) (hupper_pos : 0 < upper)
    (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hlower :
      ∀ᶠ N in atTop, lower * r ^ N ≤ gap N)
    (hupper :
      ∀ᶠ N in atTop, gap N ≤ upper * (N : ℝ) ^ d * r ^ N) :
    Tendsto
      (fun N : ℕ =>
        Real.log (gap N) / (Real.log r * (N : ℝ)))
      atTop (nhds 1) :=
  AppliedModelingLib.Math.log_tail_ratio_of_geometric_bounds
    d hlower_pos hupper_pos hr_pos hr_lt_one hlower hupper

/--
The binomial lower-tail expression from the finite-discrete proof of Theorem
1(i): fewer than `k` draws land on the top support point when the top mass is
`q` and the non-top mass is `rho`.
-/
noncomputable def finiteDiscreteTopMassFailureTail
    (k a : ℕ) (q rho : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j)

theorem finiteDiscreteTopMassFailureTail_nonneg
    (k a : ℕ) {q rho : ℝ}
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    0 ≤ finiteDiscreteTopMassFailureTail k a q rho := by
  unfold finiteDiscreteTopMassFailureTail
  refine Finset.sum_nonneg ?_
  intro j _hj
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq_nonneg j))
    (pow_nonneg hrho_nonneg (a - j))

/--
Probability mass of the event used for the finite-discrete lower marginal:
before adding the new item there are exactly `k-1` top-support draws, and the
new item is itself top-support.
-/
noncomputable def finiteDiscreteTopMassPromotingEvent
    (k a : ℕ) (q rho : ℝ) : ℝ := (Nat.choose a (k - 1) : ℝ) * q ^ k * rho ^ (a + 1 - k)

theorem finiteDiscreteTopMassPromotingEvent_nonneg
    (k a : ℕ) {q rho : ℝ}
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    0 ≤ finiteDiscreteTopMassPromotingEvent k a q rho := by
  unfold finiteDiscreteTopMassPromotingEvent
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq_nonneg k))
    (pow_nonneg hrho_nonneg (a + 1 - k))

/--
Finite-discrete binomial tail estimate used in equations (81)-(83).

For fixed `k`, the probability of fewer than `k` top-support draws is bounded
by a degree-`k` polynomial times the geometric tail `rho^(a+1-k)`.  A later
constant absorbs the fixed shift from `a+1-k` to `a`.
-/
theorem finiteDiscreteTopMassFailureTail_le_polynomial_geometric
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
  have ha_pos : 0 < a := lt_of_lt_of_le hk_pos hk_le_a
  have ha_one_le : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
  have hterm :
      ∀ j ∈ Finset.range k,
        (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j) ≤
          (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
    intro j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    have hj_le_k : j ≤ k := Nat.le_of_lt hj_lt
    have hj_le_a : j ≤ a := le_trans hj_le_k hk_le_a
    have hchoose_le : (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_pow a j
    have hq_pow_le_one : q ^ j ≤ 1 :=
      pow_le_one₀ (n := j) hq_nonneg hq_le_one
    have ha_pow_nonneg : 0 ≤ (a : ℝ) ^ j :=
      pow_nonneg (Nat.cast_nonneg a) j
    have hrho_pow_nonneg : 0 ≤ rho ^ (a - j) :=
      pow_nonneg hrho_nonneg (a - j)
    have hchoose_q_le : (Nat.choose a j : ℝ) * q ^ j ≤ (a : ℝ) ^ j := by
      calc
        (Nat.choose a j : ℝ) * q ^ j
            ≤ (a : ℝ) ^ j * q ^ j :=
              mul_le_mul_of_nonneg_right hchoose_le
                (pow_nonneg hq_nonneg j)
        _ ≤ (a : ℝ) ^ j * 1 :=
              mul_le_mul_of_nonneg_left hq_pow_le_one ha_pow_nonneg
        _ = (a : ℝ) ^ j := by ring
    have ha_pow_le : (a : ℝ) ^ j ≤ (a : ℝ) ^ k :=
      pow_le_pow_right₀ ha_one_le hj_le_k
    have hpoly_le : (Nat.choose a j : ℝ) * q ^ j ≤ (a : ℝ) ^ k :=
      le_trans hchoose_q_le ha_pow_le
    have hexp_le : rho ^ (a - j) ≤ rho ^ (a + 1 - k) := by
      have hexp_order : a + 1 - k ≤ a - j := by omega
      exact pow_le_pow_of_le_one hrho_nonneg hrho_le_one hexp_order
    have hpoly_nonneg : 0 ≤ (a : ℝ) ^ k :=
      pow_nonneg (Nat.cast_nonneg a) k
    calc
      (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j)
          ≤ (a : ℝ) ^ k * rho ^ (a - j) :=
            mul_le_mul_of_nonneg_right hpoly_le hrho_pow_nonneg
      _ ≤ (a : ℝ) ^ k * rho ^ (a + 1 - k) :=
            mul_le_mul_of_nonneg_left hexp_le hpoly_nonneg
  calc
    finiteDiscreteTopMassFailureTail k a q rho
        ≤ ∑ _j ∈ Finset.range k,
            (a : ℝ) ^ k * rho ^ (a + 1 - k) :=
          Finset.sum_le_sum hterm
    _ = (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
          simp [Finset.card_range, mul_assoc]

theorem finiteDiscrete_rho_pow_shift
    {k a : ℕ} {rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a) (hrho_ne : rho ≠ 0) :
    rho ^ (a + 1 - k) = rho ^ a * (rho ^ (k - 1))⁻¹ := by
  have hsum : (a + 1 - k) + (k - 1) = a := by omega
  have hpow_ne : rho ^ (k - 1) ≠ 0 := pow_ne_zero _ hrho_ne
  calc
    rho ^ (a + 1 - k)
        = rho ^ (a + 1 - k) *
            (rho ^ (k - 1) * (rho ^ (k - 1))⁻¹) := by
          field_simp [hpow_ne]
    _ = rho ^ a * (rho ^ (k - 1))⁻¹ := by
          rw [← mul_assoc, ← pow_add, hsum]

/--
Off-by-one failure-tail comparison.  The marginal proof naturally sees the
failure event in the old `a-1` sample; multiplying by one non-top draw embeds
that event into the failure event for an `a`-sample.
-/
theorem finiteDiscreteTopMassFailureTail_pred_mul_le
    {k a : ℕ} {q rho : ℝ}
    (ha_pos : 0 < a) (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    rho * finiteDiscreteTopMassFailureTail k (a - 1) q rho ≤
      finiteDiscreteTopMassFailureTail k a q rho := by
  classical
  unfold finiteDiscreteTopMassFailureTail
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j hj
  by_cases hj_le : j ≤ a - 1
  · have hchoose :
        (Nat.choose (a - 1) j : ℝ) ≤ (Nat.choose a j : ℝ) := by
      exact_mod_cast Nat.choose_le_choose j (Nat.pred_le a)
    have hexp : (a - 1 - j) + 1 = a - j := by omega
    have hpow_nonneg : 0 ≤ q ^ j * rho ^ (a - j) :=
      mul_nonneg (pow_nonneg hq_nonneg j)
        (pow_nonneg hrho_pos.le (a - j))
    calc
      rho * ((Nat.choose (a - 1) j : ℝ) * q ^ j *
          rho ^ (a - 1 - j))
          = (Nat.choose (a - 1) j : ℝ) * q ^ j *
              (rho * rho ^ (a - 1 - j)) := by
            ring
      _ = (Nat.choose (a - 1) j : ℝ) * (q ^ j * rho ^ (a - j)) := by
            rw [mul_comm rho (rho ^ (a - 1 - j)), ← pow_succ, hexp]
            ring
      _ ≤ (Nat.choose a j : ℝ) * (q ^ j * rho ^ (a - j)) :=
            mul_le_mul_of_nonneg_right hchoose hpow_nonneg
      _ = (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j) := by
            ring
  · have hj_gt : a - 1 < j := Nat.lt_of_not_ge hj_le
    have hchoose_zero : Nat.choose (a - 1) j = 0 :=
      Nat.choose_eq_zero_of_lt hj_gt
    have hright_nonneg :
        0 ≤ (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j) :=
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq_nonneg j))
        (pow_nonneg hrho_pos.le (a - j))
    simpa [hchoose_zero] using hright_nonneg

/-- Certificate-normalized version of the off-by-one failure-tail comparison. -/
theorem finiteDiscreteTopMassFailureTail_pred_le_inv_mul
    {k a : ℕ} {q rho : ℝ}
    (ha_pos : 0 < a) (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    finiteDiscreteTopMassFailureTail k (a - 1) q rho ≤
      rho⁻¹ * finiteDiscreteTopMassFailureTail k a q rho := by
  have hmul :=
    finiteDiscreteTopMassFailureTail_pred_mul_le
      (k := k) (a := a) (q := q) (rho := rho)
      ha_pos hq_nonneg hrho_pos
  calc
    finiteDiscreteTopMassFailureTail k (a - 1) q rho
        = rho⁻¹ *
            (rho * finiteDiscreteTopMassFailureTail k (a - 1) q rho) := by
          field_simp [hrho_pos.ne']
    _ ≤ rho⁻¹ * finiteDiscreteTopMassFailureTail k a q rho :=         mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hrho_pos.le)

/--
The binomial upper tail in the clean certificate form: the fixed exponent shift
from the paper's `rho^(a+1-k)` bound is absorbed into the positive constant.
-/
theorem finiteDiscreteTopMassFailureTail_le_polynomial_geometric_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      ((k : ℝ) * (rho ^ (k - 1))⁻¹) * (a : ℝ) ^ k * rho ^ a := by
  have hbase :=
    finiteDiscreteTopMassFailureTail_le_polynomial_geometric
      hk_pos hk_le_a hq_nonneg hq_le_one hrho_pos.le hrho_le_one
  calc
    finiteDiscreteTopMassFailureTail k a q rho
        ≤ (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) := hbase
    _ = ((k : ℝ) * (rho ^ (k - 1))⁻¹) * (a : ℝ) ^ k * rho ^ a := by
          rw [finiteDiscrete_rho_pow_shift hk_pos hk_le_a hrho_pos.ne']
          ring

/--
Finite-discrete exact-event lower bound used for the Theorem 1(i) lower
marginal: once at least `k-1` old draws are available, the exact `k-1`
top-count event has at least the single-term mass
`q^k * rho^(a+1-k)`.
-/
theorem finiteDiscreteTopMassPromotingEvent_lower_geometric
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_pred_le_a : k - 1 ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    q ^ k * rho ^ (a + 1 - k) ≤
      finiteDiscreteTopMassPromotingEvent k a q rho := by
  have hchoose_one_le : (1 : ℝ) ≤ (Nat.choose a (k - 1) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hk_pred_le_a)
  have hmass_nonneg : 0 ≤ q ^ k * rho ^ (a + 1 - k) :=
    mul_nonneg (pow_nonneg hq_nonneg k)
      (pow_nonneg hrho_nonneg (a + 1 - k))
  calc
    q ^ k * rho ^ (a + 1 - k)
        = (1 : ℝ) * (q ^ k * rho ^ (a + 1 - k)) := by ring
    _ ≤ (Nat.choose a (k - 1) : ℝ) *
          (q ^ k * rho ^ (a + 1 - k)) :=
          mul_le_mul_of_nonneg_right hchoose_one_le hmass_nonneg
    _ = finiteDiscreteTopMassPromotingEvent k a q rho := by
          simp [finiteDiscreteTopMassPromotingEvent, mul_assoc]

/--
The exact-event lower bound in the clean certificate form, with the fixed
`k-1` exponent shift absorbed into the lower-tail constant.
-/
theorem finiteDiscreteTopMassPromotingEvent_lower_geometric_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ a ≤
      finiteDiscreteTopMassPromotingEvent k a q rho := by
  have hbase :=
    finiteDiscreteTopMassPromotingEvent_lower_geometric
      hk_pos (by omega : k - 1 ≤ a) hq_nonneg hrho_pos.le
  calc
    q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ a
        = q ^ k * rho ^ (a + 1 - k) := by
          rw [finiteDiscrete_rho_pow_shift hk_pos hk_le_a hrho_pos.ne']
          ring
    _ ≤ finiteDiscreteTopMassPromotingEvent k a q rho := hbase

/--
The paper's `γ = ∞` profile: all representation mass is assigned to a chosen
type whose likelihood is maximal.
-/
structure InfiniteGammaHomogeneityProfile (T : ℕ) where
  likelihood : ItemType T → ℝ
  best : ItemType T
  isArgmax : ∀ t : ItemType T, likelihood t ≤ likelihood best

namespace InfiniteGammaHomogeneityProfile

/-- Target share for the `γ = ∞` profile. -/
noncomputable def targetShare {T : ℕ}
    (G : InfiniteGammaHomogeneityProfile T) (t : ItemType T) : ℝ :=
  if t = G.best then 1 else 0

/-- Forget the `γ = ∞` label and keep only the induced target-share profile. -/
noncomputable def toHomogeneityProfile {T : ℕ}
    (G : InfiniteGammaHomogeneityProfile T) : HomogeneityProfile T where
  targetShare := G.targetShare

/-- Exact `γ = ∞` homogeneity for a finite allocation. -/
noncomputable def Exact {T : ℕ}
    (G : InfiniteGammaHomogeneityProfile T) (a : CountAllocation T) : Prop :=
  CountAllocation.HasExactRepresentation a G.targetShare

@[simp] theorem targetShare_best {T : ℕ}
    (G : InfiniteGammaHomogeneityProfile T) :
    G.targetShare G.best = 1 := by
  simp [targetShare]

theorem targetShare_of_ne {T : ℕ}
    (G : InfiniteGammaHomogeneityProfile T) {t : ItemType T}
    (h : t ≠ G.best) :
    G.targetShare t = 0 := by
  simp [targetShare, h]

end InfiniteGammaHomogeneityProfile

/-- Build the paper's `γ = ∞` profile from a likelihood maximizer. -/
noncomputable def infiniteLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) (best : ItemType T)
    (hbest : ∀ t : ItemType T, likelihood t ≤ likelihood best) :
    InfiniteGammaHomogeneityProfile T where
  likelihood := likelihood
  best := best
  isArgmax := hbest

/--
The paper's equation (5) profile: target shares proportional to
`likelihood t ^ gamma`.
-/
noncomputable def gammaLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ) :
    GammaHomogeneityProfile T where
  gamma := gamma
  targetWeight := fun t => (likelihood t) ^ gamma

/--
The paper's equation (5)/(6) target share induced by
`gammaLikelihoodProfile`: `p_t^gamma / sum_i p_i^gamma`.
-/
theorem gammaLikelihoodProfile_targetShare_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ gamma) ≠ 0) :
    (gammaLikelihoodProfile likelihood gamma).targetShare t =
      (likelihood t) ^ gamma /
        ∑ i : ItemType T, (likelihood i) ^ gamma :=
    GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
      (G := gammaLikelihoodProfile likelihood gamma) (t := t)
      (by
        simpa [GammaHomogeneityProfile.normalizer, gammaLikelihoodProfile]
          using hnorm)

/-- Positive likelihoods give a positive normalizer for every real gamma. -/
theorem gammaLikelihoodProfile_normalizer_pos {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    0 < (gammaLikelihoodProfile likelihood gamma).normalizer := by
  unfold GammaHomogeneityProfile.normalizer gammaLikelihoodProfile
  exact Finset.sum_pos
    (fun t _ => Real.rpow_pos_of_pos (hlike_pos t) gamma)
    Finset.univ_nonempty

/--
Positive likelihoods make the paper's `gammaLikelihoodProfile` target shares a
finite simplex point.
-/
theorem gammaLikelihoodProfile_targetShare_mem_stdSimplex {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    (gammaLikelihoodProfile likelihood gamma).targetShare ∈
      stdSimplex ℝ (ItemType T) := by
  exact
    GammaHomogeneityProfile.targetShare_mem_stdSimplex_of_targetWeight_nonneg
      (gammaLikelihoodProfile likelihood gamma)
      (fun t => le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) gamma))
      (gammaLikelihoodProfile_normalizer_pos likelihood gamma hlike_pos)

/-- A raw weight profile, useful for Lemma D.1(iii)'s proportional target. -/
noncomputable def weightProfile {T : ℕ}
    (weight : ItemType T → ℝ) (gamma : ℝ) :
    GammaHomogeneityProfile T where
  gamma := gamma
  targetWeight := weight

/-- Positive raw weights give a positive normalizer. -/
theorem weightProfile_normalizer_pos {T : ℕ} [NeZero T]
    (weight : ItemType T → ℝ) (gamma : ℝ)
    (hweight_pos : ∀ t : ItemType T, 0 < weight t) :
    0 < (weightProfile weight gamma).normalizer := by
  unfold GammaHomogeneityProfile.normalizer weightProfile
  exact Finset.sum_pos (fun t _ => hweight_pos t) Finset.univ_nonempty

/-- Positive raw weights make `weightProfile` target shares a finite simplex point. -/
theorem weightProfile_targetShare_mem_stdSimplex {T : ℕ} [NeZero T]
    (weight : ItemType T → ℝ) (gamma : ℝ)
    (hweight_pos : ∀ t : ItemType T, 0 < weight t) :
    (weightProfile weight gamma).targetShare ∈ stdSimplex ℝ (ItemType T) := by
  exact
    GammaHomogeneityProfile.targetShare_mem_stdSimplex_of_targetWeight_nonneg
      (weightProfile weight gamma) (fun t => le_of_lt (hweight_pos t))
      (weightProfile_normalizer_pos weight gamma hweight_pos)

namespace GammaHomogeneityProfile

theorem weightProfile_targetShare_eq_of_sum_eq_one {T : ℕ}
    (weight : ItemType T → ℝ) (gamma : ℝ)
    (hsum : ∑ t : ItemType T, weight t = 1) (t : ItemType T) :
    (weightProfile weight gamma).targetShare t = weight t := by
  have hnorm : (weightProfile weight gamma).normalizer = 1 := by
    simpa [weightProfile, normalizer] using hsum
  rw [targetShare_eq_div_of_normalizer_ne_zero
    (G := weightProfile weight gamma) (t := t)]
  · change weight t / (weightProfile weight gamma).normalizer = weight t
    rw [hnorm]
    ring
  · rw [hnorm]
    norm_num

end GammaHomogeneityProfile

/--
A sequence of feasible finite allocations, matching the paper's `{S_n}` after
passing from sets to type-count vectors.
-/
structure AllocationSequence (T : ℕ) where
  allocation : ℕ → CountAllocation T
  feasible : ∀ N, ConsumptionModel.FeasibleAtTotal N (allocation N)

namespace AllocationSequence

/-- Type representation in the `N`th allocation of a sequence. -/
noncomputable def representation {T : ℕ}
    (seq : AllocationSequence T) (N : ℕ) (t : ItemType T) : ℝ := CountAllocation.representation (seq.allocation N) t

/--
Definition 2-style asymptotic homogeneity for a concrete allocation sequence:
each type share converges to the profile's target share.
-/
def ConvergesToProfile {T : ℕ}
    (seq : AllocationSequence T) (G : GammaHomogeneityProfile T) : Prop := ∀ t, Tendsto (fun N => seq.representation N t) atTop (nhds (G.targetShare t))

/--
An eventual uniform approximation rate tending to zero implies Definition 2
sequence convergence.
-/
theorem convergesToProfile_of_eventual_approx {T : ℕ}
    (seq : AllocationSequence T) (G : GammaHomogeneityProfile T)
    (ε : ℕ → ℝ)
    (hε : AppliedModelingLib.Math.TendsToZero ε)
    (happrox : ∀ᶠ N in atTop, G.Approx (seq.allocation N) (ε N)) :
    seq.ConvergesToProfile G := by
  intro t
  have hd :
      Tendsto
        (fun N =>
          CountAllocation.representation (seq.allocation N) t - G.targetShare t)
        atTop (nhds 0) := by
    have hneg : Tendsto (fun N => -ε N) atTop (nhds 0) := by
      have h := hε.neg
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hε
    · filter_upwards [happrox] with N hN
      exact (abs_le.mp (hN t)).1
    · filter_upwards [happrox] with N hN
      exact (abs_le.mp (hN t)).2
  have hconst :
      Tendsto (fun _ : ℕ => G.targetShare t) atTop (nhds (G.targetShare t)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun N =>
          G.targetShare t +
            (CountAllocation.representation (seq.allocation N) t - G.targetShare t))
        atTop (nhds (G.targetShare t)) := by
    simpa using hconst.add hd
  simpa [AllocationSequence.representation, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hsum

end AllocationSequence

/-- A sequence selecting an optimum of the `N`th finite problem for each `N`. -/
structure OptimalAllocationSequence {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) where
  allocation : ℕ → CountAllocation T
  optimal : ∀ N, (Mseq N).IsOptimalAtTotal N (allocation N)

namespace OptimalAllocationSequence

/-- Forget optimality and keep only the feasible allocation sequence. -/
def toAllocationSequence {T : ℕ} {Mseq : ℕ → ConsumptionModel T}
    (seq : OptimalAllocationSequence Mseq) : AllocationSequence T where
  allocation := seq.allocation
  feasible := fun N => (seq.optimal N).1

@[simp] theorem toAllocationSequence_allocation {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} (seq : OptimalAllocationSequence Mseq)
    (N : ℕ) :
    seq.toAllocationSequence.allocation N = seq.allocation N := rfl

/--
The reusable Lemma D.1 endpoint: once all finite optima satisfy an asymptotic
homogeneity target, every selected sequence of finite optima converges to the
same target profile.
-/
theorem convergesToProfile_of_asymptoticHomogeneityTarget {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (h :
      ConsumptionModel.AsymptoticHomogeneityTarget
        Mseq G AppliedModelingLib.Math.TendsToZero) :
    seq.toAllocationSequence.ConvergesToProfile G := by
  rcases h with ⟨ε, hε, happrox⟩
  apply AllocationSequence.convergesToProfile_of_eventual_approx
    seq.toAllocationSequence G ε hε
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact happrox N (seq.allocation N) hN (seq.optimal N)

theorem convergesToProfile_of_asymptoticHomogeneity {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (h : ConsumptionModel.AsymptoticHomogeneity Mseq G) :
    seq.toAllocationSequence.ConvergesToProfile G := seq.convergesToProfile_of_asymptoticHomogeneityTarget h

/--
Lemma D.1-style optimizer convergence from a unique limiting objective gap.

This wraps the shared recommender-allocation theorem in PRPKG notation.  The
comparison objective `finiteObj` may be any normalized or shifted version of
the finite separable objective, provided the selected finite optima also
maximize it.  The limiting objective must have a quantitative strict gap away
from `G.targetShare`, and the comparison allocation must asymptotically attain
the target value from below.
-/
theorem convergesToProfile_of_unique_limit_objective_gap {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (finiteObj : ℕ → CountAllocation T → ℝ)
    (limitObj : (ItemType T → ℝ) → ℝ)
    (candidate : ℕ → CountAllocation T)
    (hopt_le :
      ∀ᶠ N in atTop, ∀ b : CountAllocation T,
        ConsumptionModel.FeasibleAtTotal N b →
          finiteObj N b ≤ finiteObj N (seq.allocation N))
    (hcand_feas :
      ∀ᶠ N in atTop, ConsumptionModel.FeasibleAtTotal N (candidate N))
    (hcand_lower :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in atTop,
          limitObj G.targetShare - δ ≤ finiteObj N (candidate N))
    (hupper :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in atTop, ∀ a : CountAllocation T,
          ConsumptionModel.FeasibleAtTotal N a →
            finiteObj N a ≤
              limitObj (fun t => CountAllocation.representation a t) + δ)
    (hgap :
      ∀ ε : ℝ, 0 < ε →
        ∃ η : ℝ, 0 < η ∧
          ∀ N (a : CountAllocation T),
            0 < N →
            ConsumptionModel.FeasibleAtTotal N a →
              ¬ G.Approx a ε →
                limitObj (fun t => CountAllocation.representation a t) ≤
                  limitObj G.targetShare - η) :
    seq.toAllocationSequence.ConvergesToProfile G := by
  let sharedSeq :
      AppliedModelingLib.Allocation.OptimalSequence
        (fun N => (Mseq N).likelihood)
        (fun N => (Mseq N).valueOfCount) :=
    { allocation := seq.allocation
      optimal := by
        intro N
        simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
          ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
          ConsumptionModel.objective] using seq.optimal N }
  have hshared :
      sharedSeq.toSequence.ConvergesToProfile G.targetShare :=
    AppliedModelingLib.Allocation.OptimalSequence.convergesToProfile_of_unique_limit_objective_gap
      (seq := sharedSeq) finiteObj limitObj candidate hopt_le hcand_feas
      hcand_lower hupper (by
        intro ε hε
        rcases hgap ε hε with ⟨η, hη_pos, hη⟩
        exact ⟨η, hη_pos, by
          intro N a hNpos hfeas hnot
          exact hη N a hNpos hfeas hnot⟩)
  intro t
  have ht := hshared t
  simpa [AllocationSequence.representation, CountAllocation.representation,
    AppliedModelingLib.Allocation.Sequence.share, sharedSeq]
    using ht

/--
Lemma D.1-style optimizer convergence from a strict unique maximizer of the
limiting objective on the finite simplex.

This is the common source-proof pattern after the finite objectives have been
bounded above by a relaxed limiting objective and a rounded target allocation
has been shown to attain the target value from below. The compact simplex gap
is discharged by the shared library theorem.
-/
theorem convergesToProfile_of_unique_limit_objective_gap_on_simplex {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (finiteObj : ℕ → CountAllocation T → ℝ)
    (limitObj : (ItemType T → ℝ) → ℝ)
    (candidate : ℕ → CountAllocation T)
    (htarget_simplex : G.targetShare ∈ stdSimplex ℝ (ItemType T))
    (hlimit_cont : ContinuousOn limitObj (stdSimplex ℝ (ItemType T)))
    (hlimit_strict :
      ∀ x : ItemType T → ℝ, x ∈ stdSimplex ℝ (ItemType T) →
        x ≠ G.targetShare → limitObj x < limitObj G.targetShare)
    (hopt_le :
      ∀ᶠ N in Filter.atTop, ∀ b : CountAllocation T,
        ConsumptionModel.FeasibleAtTotal N b →
          finiteObj N b ≤ finiteObj N (seq.allocation N))
    (hcand_feas :
      ∀ᶠ N in Filter.atTop, ConsumptionModel.FeasibleAtTotal N (candidate N))
    (hcand_lower :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in Filter.atTop,
          limitObj G.targetShare - δ ≤ finiteObj N (candidate N))
    (hupper :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in Filter.atTop, ∀ a : CountAllocation T,
          ConsumptionModel.FeasibleAtTotal N a →
            finiteObj N a ≤
              limitObj (fun t => CountAllocation.representation a t) + δ) :
    seq.toAllocationSequence.ConvergesToProfile G := by
  refine seq.convergesToProfile_of_unique_limit_objective_gap
    finiteObj limitObj candidate hopt_le hcand_feas hcand_lower hupper ?_
  intro ε hε_pos
  rcases
    AppliedModelingLib.Allocation.exists_gap_on_stdSimplex_of_strict_unique_max
      limitObj G.targetShare htarget_simplex hlimit_cont hlimit_strict
      ε hε_pos with
    ⟨η, hη_pos, hgap_simplex⟩
  refine ⟨η, hη_pos, ?_⟩
  intro N a hNpos hfeas hnot
  have htotal_ne : AppliedModelingLib.Allocation.total a ≠ 0 := by
    rw [hfeas]
    exact Nat.ne_of_gt hNpos
  have hshare_simplex :
      (fun t : ItemType T => CountAllocation.representation a t) ∈
        stdSimplex ℝ (ItemType T) := by
    constructor
    · intro t
      exact CountAllocation.representation_nonneg a t
    · exact CountAllocation.sum_representation_eq_one_of_total_ne_zero
        a htotal_ne
  have hfar :
      ∃ t : ItemType T,
        ε < |CountAllocation.representation a t - G.targetShare t| := by
    have hnot' :
        ¬ ∀ t : ItemType T,
          |CountAllocation.representation a t - G.targetShare t| ≤ ε := by
      simpa [GammaHomogeneityProfile.Approx,
        CountAllocation.HasApproxRepresentation] using hnot
    rcases not_forall.mp hnot' with ⟨t, ht⟩
    exact ⟨t, lt_of_not_ge ht⟩
  exact hgap_simplex
    (fun t : ItemType T => CountAllocation.representation a t)
    hshare_simplex hfar

end OptimalAllocationSequence

/--
Certificate for Theorem 1-style top-`k` asymptotic conclusions. The hard
distribution-specific work is proving the asymptotic homogeneity field from
order-statistic asymptotics and Lemma D.1.
-/
structure TopKAsymptoticHomogeneityCertificate {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (G : GammaHomogeneityProfile T) where
  asymptotic_homogeneity :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) G

/--
Bridge PRPKG's paper-local top-`k` oracle to the reusable probability
order-statistic interface in `AppliedModelingLib`.
-/
def topKExpectationOracleOfTopKValueOracle {T : ℕ}
    (O : TopKValueOracle T) :
    AppliedModelingLib.Probability.TopKExpectationOracle (ItemType T) where
  expectedTopSum := O.expectedTopSum

@[simp] theorem topKExpectationOracle_expectedTopSum {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (topKExpectationOracleOfTopKValueOracle O).expectedTopSum k t q =
      O.expectedTopSum k t q := rfl

@[simp] theorem topKExpectationOracle_marginalTopK_eq {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (topKExpectationOracleOfTopKValueOracle O).marginalTopK k t q =
      O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q := rfl

/--
Reusable probability-facing certificate for Theorem 1(ii)-(iv): the top-`k`
marginal has a common asymptotic scale and type weight.
-/
abbrev TopKScaledMarginalLimitCertificate {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ) :=
  AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate
    (topKExpectationOracleOfTopKValueOracle O) k scale weight

namespace TopKScaledMarginalLimitCertificate

theorem eventually_marginal_sandwich {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : ItemType T,
        (1 - ε) * (scale q * weight t) ≤
            O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ∧
          O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ≤
            (1 + ε) * (scale q * weight t) := by
  simpa using
    AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich
      C hε

/--
Pointwise marginal sandwich using the certificate's concrete uniform ratio
error schedule.
-/
theorem marginal_sandwich_uniformRatioError {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {q : ℕ} (hq_base : C.uniformRatioThreshold 0 ≤ q)
    (hscale_pos : 0 < scale q) :
    ∀ t : ItemType T,
      (1 - C.uniformRatioError q) * (scale q * weight t) ≤
          O.marginalTopK k t q ∧
        O.marginalTopK k t q ≤
          (1 + C.uniformRatioError q) * (scale q * weight t) := by
  intro t
  have hratio := C.uniform_ratio_abs_sub_lt_uniformRatioError
    (q := q) hq_base t
  rw [abs_lt] at hratio
  have hratioO :
      -C.uniformRatioError q <
          O.marginalTopK k t q / (scale q * weight t) - 1 ∧
        O.marginalTopK k t q / (scale q * weight t) - 1 <
          C.uniformRatioError q := by
    simpa [topKExpectationOracle_marginalTopK_eq] using hratio
  have hlow :
      1 - C.uniformRatioError q ≤
        O.marginalTopK k t q / (scale q * weight t) := by
    linarith [hratioO.1]
  have hhigh :
      O.marginalTopK k t q / (scale q * weight t) ≤
        1 + C.uniformRatioError q := by
    linarith [hratioO.2]
  have hden_pos : 0 < scale q * weight t :=
    mul_pos hscale_pos (C.weight_pos t)
  have heq :=
    show O.marginalTopK k t q =
        O.marginalTopK k t q / (scale q * weight t) *
          (scale q * weight t) from
      by
        simpa [topKExpectationOracle_marginalTopK_eq] using
          C.marginalTopK_eq_ratio_mul
            (q := q) (t := t) (ne_of_gt hscale_pos)
  constructor
  · calc
      (1 - C.uniformRatioError q) * (scale q * weight t)
          ≤ (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) :=
            mul_le_mul_of_nonneg_right hlow hden_pos.le
      _ = O.marginalTopK k t q := by rw [← heq]
  · calc
      O.marginalTopK k t q
          = (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) := heq
      _ ≤ (1 + C.uniformRatioError q) * (scale q * weight t) :=
            mul_le_mul_of_nonneg_right hhigh hden_pos.le

theorem eventually_same_count_marginal_lt_of_weight_gap {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) {src dst : ItemType T}
    (hgap : (1 + ε) * weight src < (1 - ε) * weight dst) :
    ∀ᶠ q in atTop,
      O.expectedTopSum k src (q + 1) - O.expectedTopSum k src q <
        O.expectedTopSum k dst (q + 1) - O.expectedTopSum k dst q := by
  simpa using
    AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap
      C hε hgap

/--
If the common marginal scale vanishes, then each paper-local top-`k` marginal
vanishes.
-/
theorem marginal_tendsto_zero {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (hscale_zero : Tendsto scale atTop (nhds 0)) (t : ItemType T) :
    Tendsto
      (fun q => O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q)
      atTop (nhds 0) := by
  simpa [topKExpectationOracle_marginalTopK_eq] using
    AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate.marginalTopK_tendsto_zero
      C hscale_zero t

/--
Lift a top-`k` marginal certificate through the likelihood weights used by the
recommendation objective.
-/
theorem weightedLikelihood {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight likelihood : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate
      ((topKExpectationOracleOfTopKValueOracle O).weighted likelihood)
      k scale (fun t => likelihood t * weight t) :=
  AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate.weighted
    C hlike_pos

end TopKScaledMarginalLimitCertificate

/--
Generic top-`k` interiority/count-floor bridge.

If every fixed low-count forward marginal is positive, while high-count
backward marginals vanish because the corresponding forward marginal tends to
zero, then every optimum eventually gives each type count above the supplied
finite floor.  Bounded, Pareto, and exponential order-statistic routes use
this to separate source positivity from the optimization argument.
-/
theorem topK_count_floor_eventually_of_marginal_tendsto_zero_and_positive_low_forward
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k floor : ℕ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (hforward_pos :
      ∀ t : ItemType T, ∀ q : ℕ, q ≤ floor → 0 < O.marginalTopK k t q)
    (hforward_tendsto_zero :
      ∀ t : ItemType T,
        Tendsto (fun q : ℕ => O.marginalTopK k t q) atTop (nhds 0)) :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t := by
  classical
  let M : ConsumptionModel T := O.toConsumptionModel likelihood k
  have hdom_ev :
      ∀ᶠ q in atTop,
        ∀ src dst : ItemType T, ∀ qdst : Fin (floor + 1),
          M.weightedBackwardMarginal src q <
            M.weightedForwardMarginal dst qdst.val := by
    refine Filter.eventually_all.2 ?_
    intro src
    refine Filter.eventually_all.2 ?_
    intro dst
    refine Filter.eventually_all.2 ?_
    intro qdst
    have hforward_pos_weighted :
        0 < M.weightedForwardMarginal dst qdst.val := by
      have hbase :
          0 < O.marginalTopK k dst qdst.val :=
        hforward_pos dst qdst.val (Nat.le_of_lt_succ qdst.isLt)
      simpa [M, TopKValueOracle.toConsumptionModel,
        ConsumptionModel.weightedForwardMarginal,
        ConsumptionModel.marginalValue, TopKValueOracle.marginalTopK,
        AppliedModelingLib.Allocation.marginal] using
        mul_pos (hlike_pos dst) hbase
    have hback_tend :
        Tendsto
          (fun q : ℕ =>
            O.expectedTopSum k src q -
              O.expectedTopSum k src (q - 1))
          atTop (nhds 0) := by
      have hcomp :=
        (hforward_tendsto_zero src).comp (Filter.tendsto_sub_atTop_nat 1)
      refine Tendsto.congr' ?_ hcomp
      filter_upwards [eventually_gt_atTop 0] with q hq
      dsimp [Function.comp_def]
      simp [Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
    have hweighted_tend :
        Tendsto
          (fun q : ℕ =>
            likelihood src *
              (O.expectedTopSum k src q -
                O.expectedTopSum k src (q - 1)))
          atTop (nhds 0) := by
      simpa using hback_tend.const_mul (likelihood src)
    have hlt :=
      hweighted_tend.eventually
        (eventually_lt_nhds hforward_pos_weighted)
    filter_upwards [hlt, eventually_gt_atTop 0] with q hltq hqpos
    unfold M
    rw [show
        (O.toConsumptionModel likelihood k).weightedBackwardMarginal src q =
          likelihood src *
            (O.expectedTopSum k src q -
              O.expectedTopSum k src (q - 1)) by
        unfold ConsumptionModel.weightedBackwardMarginal
          TopKValueOracle.toConsumptionModel
        rw [dif_neg (Nat.ne_of_gt hqpos)]]
    simpa [TopKValueOracle.toConsumptionModel,
      ConsumptionModel.weightedForwardMarginal,
      ConsumptionModel.marginalValue, TopKValueOracle.marginalTopK,
      AppliedModelingLib.Allocation.marginal] using hltq
  rcases Filter.eventually_atTop.1 hdom_ev with ⟨marginal_threshold, hthreshold⟩
  let source_threshold := max marginal_threshold floor
  have hmarginal_le_source : marginal_threshold ≤ source_threshold := by
    exact le_max_left _ _
  have hfloor_le_source : floor ≤ source_threshold := by
    exact le_max_right _ _
  refine Filter.eventually_atTop.2 ?_
  refine ⟨T * source_threshold + 1, ?_⟩
  intro N hNlarge a _hNpos hopt dst
  by_contra hnot_floor
  have hdst_le_floor : a.count dst ≤ floor := le_of_not_gt hnot_floor
  have hlarge : T * source_threshold < N := by omega
  have hexists_src :
      ∃ src : ItemType T, source_threshold < a.count src := by
    by_contra hnone
    push Not at hnone
    have hsum_le :
        AppliedModelingLib.Allocation.total a ≤ T * source_threshold := by
      unfold AppliedModelingLib.Allocation.total
      calc
        (∑ t : ItemType T, a.count t)
            ≤ ∑ _t : ItemType T, source_threshold :=
              Finset.sum_le_sum (fun t _ => hnone t)
        _ = T * source_threshold := by
              simp [Finset.sum_const, Fintype.card_fin]
    rw [hopt.1] at hsum_le
    exact (not_lt_of_ge hsum_le) hlarge
  obtain ⟨src, hsrc_large⟩ := hexists_src
  have hsrc_pos : 0 < a.count src := Nat.zero_lt_of_lt hsrc_large
  have hne : src ≠ dst := by
    intro hsame
    subst dst
    exact (not_lt_of_ge (le_trans hdst_le_floor hfloor_le_source)) hsrc_large
  have hfoc :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := O.toConsumptionModel likelihood k)
      (N := N) (a := a) (src := src) (dst := dst)
      hopt hne hsrc_pos
  let qdstFin : Fin (floor + 1) :=
    ⟨a.count dst, Nat.lt_succ_of_le hdst_le_floor⟩
  have hdom :=
    hthreshold (a.count src)
      (le_trans hmarginal_le_source (le_of_lt hsrc_large)) src dst qdstFin
  simpa [M, qdstFin] using (not_lt_of_ge hfoc) hdom

/--
Reusable finite-to-asymptotic bridge for Lemma D.1-style conclusions.

If all finite optima have pairwise bounded scaled counts
`count t / weight t`, then their counts are uniformly `O(1)` close to the
allocation with shares proportional to `weight`, hence the induced
representations converge at exact `C / N` rate.
-/
structure PairwiseScaledHomogeneityCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  scaled_bound : ℝ
  scaled_bound_pos : 0 < scaled_bound
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / weight i -
          (a.count j : ℝ) / weight j| ≤ scaled_bound

namespace PairwiseScaledHomogeneityCertificate

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledHomogeneityCertificate Mseq weight G) :
    AppliedModelingLib.Allocation.PairwiseScaledBoundedProfileCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  bound := hcert.scaled_bound
  bound_pos := hcert.scaled_bound_pos
  pairwise_scaled := by
    intro N a hN hopt i j
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    exact hcert.pairwise_scaled N a hN hopt' i j

theorem asymptoticHomogeneityTarget {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledHomogeneityCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneityTarget Mseq G
      AppliedModelingLib.Math.ExactInvRate := by
  have hgeneric :
      AppliedModelingLib.Allocation.AsymptoticProfileTarget
        (fun N => (Mseq N).likelihood)
        (fun N => (Mseq N).valueOfCount)
        G.targetShare AppliedModelingLib.Math.ExactInvRate :=
    hcert.toShared.asymptoticProfileTarget
  rcases hgeneric with ⟨ε, hε, happrox⟩
  refine ⟨ε, hε, ?_⟩
  intro N a hN hopt
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        (Mseq N).likelihood (Mseq N).valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
      ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
      ConsumptionModel.objective] using hopt
  have happ := happrox N a hN hopt'
  simpa [AppliedModelingLib.Allocation.HasApproxShare,
    GammaHomogeneityProfile.Approx, CountAllocation.HasApproxRepresentation,
    CountAllocation.representation] using happ

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledHomogeneityCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G :=
  ConsumptionModel.AsymptoticHomogeneityTarget.of_exactInvRate
    hcert.asymptoticHomogeneityTarget

end PairwiseScaledHomogeneityCertificate

/--
Sublinear pairwise-scaled bridge for Lemma D.1-style asymptotic proofs.

This weakens `PairwiseScaledHomogeneityCertificate`: the scaled counts may
differ by `ε_N * N`, provided `ε_N → 0`. After averaging, representation error
is at most `ε_N` times the total target weight.
-/
structure PairwiseScaledSublinearHomogeneityCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / weight i -
          (a.count j : ℝ) / weight j| ≤ error N * (N : ℝ)

namespace PairwiseScaledSublinearHomogeneityCertificate

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearHomogeneityCertificate Mseq weight G) :
    AppliedModelingLib.Allocation.PairwiseScaledSublinearProfileCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  pairwise_scaled := by
    intro N a hN hopt i j
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    exact hcert.pairwise_scaled N a hN hopt' i j

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearHomogeneityCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G := by
  have hgeneric :
      AppliedModelingLib.Allocation.AsymptoticProfile
        (fun N => (Mseq N).likelihood)
        (fun N => (Mseq N).valueOfCount)
        G.targetShare :=
    hcert.toShared.asymptoticProfile
  rcases hgeneric with ⟨ε, hε, happrox⟩
  refine ⟨ε, hε, ?_⟩
  intro N a hN hopt
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        (Mseq N).likelihood (Mseq N).valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
      ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
      ConsumptionModel.objective] using hopt
  have happ := happrox N a hN hopt'
  simpa [AppliedModelingLib.Allocation.HasApproxShare,
    GammaHomogeneityProfile.Approx, CountAllocation.HasApproxRepresentation,
    CountAllocation.representation] using happ

end PairwiseScaledSublinearHomogeneityCertificate

/--
FOC-based sublinear pairwise-scaled bridge.

This is the reusable endpoint for asymptotic product estimates: if every
scaled-count gap larger than `error N * N` would make the source backward
marginal strictly smaller than the destination forward marginal, then the
finite first-order condition rules out such gaps in every optimum. The existing
sublinear pairwise-scaled bridge then gives asymptotic homogeneity.
-/
structure PairwiseScaledSublinearFOCCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ src dst,
        error N * (N : ℝ) <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst →
        (Mseq N).weightedBackwardMarginal src (a.count src) <
          (Mseq N).weightedForwardMarginal dst (a.count dst)

namespace PairwiseScaledSublinearFOCCertificate

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearFOCCertificate Mseq weight G) :
    AppliedModelingLib.Allocation.PairwiseScaledSublinearFOCCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  large_gap_backward_lt_forward := by
    intro N a hN hopt src dst hgap
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    have hdom :=
      hcert.large_gap_backward_lt_forward N a hN hopt' src dst hgap
    simpa [ConsumptionModel.weightedBackwardMarginal,
      ConsumptionModel.weightedForwardMarginal, ConsumptionModel.marginalValue,
      AppliedModelingLib.Allocation.weightedBackwardMarginal,
      AppliedModelingLib.Allocation.weightedForwardMarginal,
      AppliedModelingLib.Allocation.marginal] using hdom

noncomputable def toPairwiseScaledSublinearHomogeneityCertificate
    {T : ℕ} [NeZero T] {Mseq : ℕ → ConsumptionModel T}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearFOCCertificate Mseq weight G) :
    PairwiseScaledSublinearHomogeneityCertificate Mseq weight G :=
  let hshared := hcert.toShared.toPairwiseScaledSublinearProfileCertificate
  { weight_pos := hshared.weight_pos
    targetShare_eq := hshared.target_eq
    error := hshared.error
    error_nonneg := hshared.error_nonneg
    error_tends_to_zero := hshared.error_tends_to_zero
    pairwise_scaled := by
      intro N a hN hopt i j
      have hopt' :
          AppliedModelingLib.Allocation.IsOptimalAtTotal
            (Mseq N).likelihood (Mseq N).valueOfCount N a := by
        simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
          ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
          ConsumptionModel.objective] using hopt
      exact hshared.pairwise_scaled N a hN hopt' i j }

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearFOCCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G := hcert.toPairwiseScaledSublinearHomogeneityCertificate.asymptoticHomogeneity

end PairwiseScaledSublinearFOCCertificate

/-- Finite-prefix error for exact power-law marginal FOC proofs. -/
noncomputable def powerLawSublinearFOCError {T : ℕ}
    (likelihood : ItemType T → ℝ) (γ : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    ((∑ t : ItemType T, 1 / (likelihood t ^ γ)) + 1) / (N : ℝ)

theorem powerLawSublinearFOCError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ powerLawSublinearFOCError likelihood γ N := by
  by_cases hN : N = 0
  · simp [powerLawSublinearFOCError, hN]
  · have hS_nonneg :
        0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ γ) :=
      Finset.sum_nonneg
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) γ)))
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have hnum_nonneg :
        0 ≤ (∑ t : ItemType T, 1 / (likelihood t ^ γ)) + 1 :=
      add_nonneg hS_nonneg zero_le_one
    rw [powerLawSublinearFOCError, if_neg hN]
    exact div_nonneg hnum_nonneg (le_of_lt hN_pos)

theorem powerLawSublinearFOCError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Math.TendsToZero
      (powerLawSublinearFOCError likelihood γ) := by
  let S : ℝ := (∑ t : ItemType T, 1 / (likelihood t ^ γ)) + 1
  have hsum_nonneg :
      0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ γ) :=
    Finset.sum_nonneg
      (fun t _ => div_nonneg zero_le_one
        (le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) γ)))
  have hS_pos : 0 < S := by
    dsimp [S]
    linarith
  refine AppliedModelingLib.Math.TendsToZero_of_nonneg_le_const_div
    (powerLawSublinearFOCError likelihood γ) hS_pos
    (powerLawSublinearFOCError_nonneg likelihood γ hlike_pos) ?_
  intro N hN
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  simp [powerLawSublinearFOCError, hN_ne, S]

/--
Source-side reciprocal-weight perturbation induced by the uniform marginal
ratio error of a top-`k` scaled marginal certificate.
-/
noncomputable def topKPowerLawAsymptoticSrcPerturbation {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (t : ItemType T) (q : ℕ) : ℝ :=
  |1 / (likelihood t ^ γ) -
    1 / ((likelihood t * (1 + C.uniformRatioError q)) ^ γ)|

/--
Destination-side reciprocal-weight perturbation induced by the uniform marginal
ratio error of a top-`k` scaled marginal certificate.
-/
noncomputable def topKPowerLawAsymptoticDstPerturbation {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (t : ItemType T) (q : ℕ) : ℝ :=
  |1 / ((likelihood t * (1 - C.uniformRatioError q)) ^ γ) -
    1 / (likelihood t ^ γ)|

theorem topKPowerLawAsymptoticSrcPerturbation_nonneg {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (t : ItemType T) (q : ℕ) :
    0 ≤ topKPowerLawAsymptoticSrcPerturbation C likelihood γ t q := by
  simp [topKPowerLawAsymptoticSrcPerturbation]

theorem topKPowerLawAsymptoticDstPerturbation_nonneg {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (t : ItemType T) (q : ℕ) :
    0 ≤ topKPowerLawAsymptoticDstPerturbation C likelihood γ t q := by
  simp [topKPowerLawAsymptoticDstPerturbation]

theorem topKPowerLawAsymptoticSrcPerturbation_tends_to_zero {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (t : ItemType T) :
    AppliedModelingLib.Math.TendsToZero
      (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) := by
  change
    AppliedModelingLib.Math.TendsToZero
      (fun q : ℕ =>
        |1 / (likelihood t ^ γ) -
          1 / ((likelihood t * (1 + C.uniformRatioError q)) ^ γ)|)
  simpa [one_div] using
    AppliedModelingLib.Math.reciprocal_rpow_one_add_perturb_tendsToZero
      C.uniformRatioError_tendsToZero (p := likelihood t) (γ := γ)
      (hlike_pos t)

theorem topKPowerLawAsymptoticDstPerturbation_tends_to_zero {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (t : ItemType T) :
    AppliedModelingLib.Math.TendsToZero
      (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) := by
  change
    AppliedModelingLib.Math.TendsToZero
      (fun q : ℕ =>
        |1 / ((likelihood t * (1 - C.uniformRatioError q)) ^ γ) -
          1 / (likelihood t ^ γ)|)
  simpa [one_div] using
    AppliedModelingLib.Math.reciprocal_rpow_one_sub_perturb_tendsToZero
      C.uniformRatioError_tendsToZero (p := likelihood t) (γ := γ)
      (hlike_pos t)

/--
Concrete `o(1)` error schedule for asymptotic power-law FOC comparisons.

The inverse-square-root term absorbs fixed integer shifts.  The prefix-scaled
perturbation terms absorb the finite-type `1 ± ε_q` marginal-ratio errors
uniformly over all counts `q ≤ N`.
-/
noncomputable def topKPowerLawAsymptoticFOCError {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ) (N : ℕ) : ℝ :=
  AppliedModelingLib.Math.invSqrtSuccError N +
    2 * (∑ t : ItemType T,
      AppliedModelingLib.Math.prefixScaledError
        (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N) +
    2 * (∑ t : ItemType T,
      AppliedModelingLib.Math.prefixScaledError
        (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N)

theorem topKPowerLawAsymptoticFOCError_nonneg {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ) (N : ℕ) :
    0 ≤ topKPowerLawAsymptoticFOCError C likelihood γ N := by
  unfold topKPowerLawAsymptoticFOCError
  have hsrc :
      0 ≤
        ∑ t : ItemType T,
          AppliedModelingLib.Math.prefixScaledError
            (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N := by
    exact Finset.sum_nonneg
      (fun t _ =>
        AppliedModelingLib.Math.prefixScaledError_nonneg
          (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t)
          (topKPowerLawAsymptoticSrcPerturbation_nonneg
            C likelihood γ t) N)
  have hdst :
      0 ≤
        ∑ t : ItemType T,
          AppliedModelingLib.Math.prefixScaledError
            (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N := by
    exact Finset.sum_nonneg
      (fun t _ =>
        AppliedModelingLib.Math.prefixScaledError_nonneg
          (topKPowerLawAsymptoticDstPerturbation C likelihood γ t)
          (topKPowerLawAsymptoticDstPerturbation_nonneg
            C likelihood γ t) N)
  have hinv : 0 ≤ AppliedModelingLib.Math.invSqrtSuccError N :=
    AppliedModelingLib.Math.invSqrtSuccError_nonneg N
  nlinarith

theorem topKPowerLawAsymptoticFOCError_tends_to_zero {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ} {scale : ℕ → ℝ}
    {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Math.TendsToZero
      (topKPowerLawAsymptoticFOCError C likelihood γ) := by
  rw [AppliedModelingLib.Math.TendsToZero]
  have hsrc :
      Tendsto
        (fun N : ℕ =>
          ∑ t : ItemType T,
            AppliedModelingLib.Math.prefixScaledError
              (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N)
        atTop (nhds 0) := by
    have hsum :
        Tendsto
          (fun N : ℕ =>
            ∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N)
          atTop (nhds (∑ _t : ItemType T, (0 : ℝ))) := by
      exact tendsto_finset_sum Finset.univ
        (fun t _ =>
          AppliedModelingLib.Math.prefixScaledError_tendsToZero
            (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t)
            (topKPowerLawAsymptoticSrcPerturbation_nonneg
              C likelihood γ t)
            (topKPowerLawAsymptoticSrcPerturbation_tends_to_zero
              C likelihood γ hlike_pos t))
    simpa using hsum
  have hdst :
      Tendsto
        (fun N : ℕ =>
          ∑ t : ItemType T,
            AppliedModelingLib.Math.prefixScaledError
              (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N)
        atTop (nhds 0) := by
    have hsum :
        Tendsto
          (fun N : ℕ =>
            ∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N)
          atTop (nhds (∑ _t : ItemType T, (0 : ℝ))) := by
      exact tendsto_finset_sum Finset.univ
        (fun t _ =>
          AppliedModelingLib.Math.prefixScaledError_tendsToZero
            (topKPowerLawAsymptoticDstPerturbation C likelihood γ t)
            (topKPowerLawAsymptoticDstPerturbation_nonneg
              C likelihood γ t)
            (topKPowerLawAsymptoticDstPerturbation_tends_to_zero
              C likelihood γ hlike_pos t))
    simpa using hsum
  simpa [topKPowerLawAsymptoticFOCError] using
    (AppliedModelingLib.Math.invSqrtSuccError_tendsToZero.add
      (hsrc.const_mul 2)).add (hdst.const_mul 2)

/--
Asymptotic power-law marginal FOC comparison.

If the top-`k` marginal is uniformly asymptotic to
`coeff * (q+1)^(-η)`, then a concrete `o(1)` error schedule eventually turns a
large scaled-count gap into the strict backward/forward marginal inequality
needed by the pairwise FOC bridge.
-/
theorem topKPowerLawAsymptotic_large_gap_count_eventually
    {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {k floor : ℕ} {η γ coeff : ℝ}
    {scale : ℕ → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale
      (fun _ : ItemType T => coeff))
    (hscale : ∀ q : ℕ, scale q = (((q + 1 : ℕ) : ℝ) ^ (-η)))
    (likelihood : ItemType T → ℝ)
    (hη_pos : 0 < η)
    (hγ_eq : 1 / η = γ)
    (hcoeff_pos : 0 < coeff)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (hfloor_pos : 0 < floor)
    (hfloor_threshold0 : C.uniformRatioThreshold 0 ≤ floor)
    (hfloor_threshold1 : C.uniformRatioThreshold 1 ≤ floor) :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        topKPowerLawAsymptoticFOCError C likelihood γ N * (N : ℝ) <
          (qsrc : ℝ) / likelihood src ^ γ -
            (qdst : ℝ) / likelihood dst ^ γ →
        (O.toConsumptionModel likelihood k).weightedBackwardMarginal
            src qsrc <
          (O.toConsumptionModel likelihood k).weightedForwardMarginal
            dst qdst := by
  classical
  have hshift_ev :
      ∀ᶠ N in atTop,
        ∀ dst : ItemType T,
          1 / likelihood dst ^ γ <
            AppliedModelingLib.Math.invSqrtSuccError N * (N : ℝ) := by
    simpa using
      AppliedModelingLib.Math.invSqrtSuccError_mul_nat_eventually_gt_fintype_pair
        (fun _src : ItemType T => fun dst : ItemType T =>
          1 / likelihood dst ^ γ)
  filter_upwards [hshift_ev, eventually_gt_atTop 0] with
    N hshift hN_pos src dst qsrc qdst hqsrc_le_N hqdst_le_N
    hqsrc_floor hqdst_floor hgap
  have hqsrc_pos : 0 < qsrc := Nat.lt_trans hfloor_pos hqsrc_floor
  have hqdst_pos : 0 < qdst := Nat.lt_trans hfloor_pos hqdst_floor
  have hqsrc_pred_le_N : qsrc - 1 ≤ N := by omega
  have hqsrc_pred_threshold0 : C.uniformRatioThreshold 0 ≤ qsrc - 1 := by
    omega
  have hqsrc_pred_threshold1 : C.uniformRatioThreshold 1 ≤ qsrc - 1 := by
    omega
  have hqdst_threshold0 : C.uniformRatioThreshold 0 ≤ qdst := by
    omega
  have hqdst_threshold1 : C.uniformRatioThreshold 1 ≤ qdst := by
    omega
  have hqsrc_pred_ge_one : 1 ≤ qsrc - 1 := by omega
  have hqdst_ge_one : 1 ≤ qdst := by omega
  let esrc : ℝ := C.uniformRatioError (qsrc - 1)
  let edst : ℝ := C.uniformRatioError qdst
  have hesrc_nonneg : 0 ≤ esrc := by
    dsimp [esrc]
    exact C.uniformRatioError_nonneg (qsrc - 1)
  have hedst_nonneg : 0 ≤ edst := by
    dsimp [edst]
    exact C.uniformRatioError_nonneg qdst
  have hesrc_le_half : esrc ≤ (1 / 2 : ℝ) := by
    dsimp [esrc]
    simpa using
      C.uniformRatioError_le_of_threshold_le
        (m := 1) (N := qsrc - 1) hqsrc_pred_ge_one
        hqsrc_pred_threshold1
  have hedst_le_half : edst ≤ (1 / 2 : ℝ) := by
    dsimp [edst]
    simpa using
      C.uniformRatioError_le_of_threshold_le
        (m := 1) (N := qdst) hqdst_ge_one hqdst_threshold1
  have hone_add_esrc_pos : 0 < 1 + esrc := by linarith
  have hone_sub_edst_pos : 0 < 1 - edst := by linarith
  have hscale_src_pos :
      0 < scale (qsrc - 1) := by
    rw [hscale]
    exact Real.rpow_pos_of_pos (by positivity) (-η)
  have hscale_dst_pos :
      0 < scale qdst := by
    rw [hscale]
    exact Real.rpow_pos_of_pos (by positivity) (-η)
  have hsrc_sandwich :=
    C.marginal_sandwich_uniformRatioError
      (q := qsrc - 1) hqsrc_pred_threshold0 hscale_src_pos src
  have hdst_sandwich :=
    C.marginal_sandwich_uniformRatioError
      (q := qdst) hqdst_threshold0 hscale_dst_pos dst
  have hsrc_marg_le :
      O.marginalTopK k src (qsrc - 1) ≤
        (1 + esrc) *
          ((((qsrc - 1 + 1 : ℕ) : ℝ) ^ (-η)) * coeff) := by
    simpa [esrc, hscale] using hsrc_sandwich.2
  have hdst_marg_ge :
      (1 - edst) *
          ((((qdst + 1 : ℕ) : ℝ) ^ (-η)) * coeff) ≤
        O.marginalTopK k dst qdst := by
    simpa [edst, hscale] using hdst_sandwich.1
  let srcPert : ℝ :=
    topKPowerLawAsymptoticSrcPerturbation C likelihood γ src (qsrc - 1)
  let dstPert : ℝ :=
    topKPowerLawAsymptoticDstPerturbation C likelihood γ dst qdst
  let srcPrefix : ℝ :=
    AppliedModelingLib.Math.prefixScaledError
      (topKPowerLawAsymptoticSrcPerturbation C likelihood γ src) N
  let dstPrefix : ℝ :=
    AppliedModelingLib.Math.prefixScaledError
      (topKPowerLawAsymptoticDstPerturbation C likelihood γ dst) N
  have hsrcPert_nonneg : 0 ≤ srcPert := by
    dsimp [srcPert]
    exact topKPowerLawAsymptoticSrcPerturbation_nonneg C likelihood γ src
      (qsrc - 1)
  have hdstPert_nonneg : 0 ≤ dstPert := by
    dsimp [dstPert]
    exact topKPowerLawAsymptoticDstPerturbation_nonneg C likelihood γ dst
      qdst
  have hsrcPrefix_bound :
      srcPert * ((qsrc - 1 : ℕ) : ℝ) ≤ srcPrefix * (N : ℝ) := by
    dsimp [srcPert, srcPrefix]
    exact
      AppliedModelingLib.Math.le_prefixScaledError_mul_nat
        (topKPowerLawAsymptoticSrcPerturbation C likelihood γ src)
        hN_pos hqsrc_pred_le_N
  have hdstPrefix_bound :
      dstPert * (qdst : ℝ) ≤ dstPrefix * (N : ℝ) := by
    dsimp [dstPert, dstPrefix]
    exact
      AppliedModelingLib.Math.le_prefixScaledError_mul_nat
        (topKPowerLawAsymptoticDstPerturbation C likelihood γ dst)
        hN_pos hqdst_le_N
  have hsrcPert_count_bound :
      srcPert * (qsrc : ℝ) ≤ 2 * srcPrefix * (N : ℝ) := by
    have hcount :
        (qsrc : ℝ) ≤ 2 * ((qsrc - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : qsrc ≤ 2 * (qsrc - 1))
    have hmul :=
      mul_le_mul_of_nonneg_left hcount hsrcPert_nonneg
    nlinarith [hsrcPrefix_bound, hmul]
  have hdstPert_count_bound :
      dstPert * (((qdst + 1 : ℕ) : ℝ)) ≤ 2 * dstPrefix * (N : ℝ) := by
    have hcount :
        (((qdst + 1 : ℕ) : ℝ)) ≤ 2 * (qdst : ℝ) := by
      exact_mod_cast (by omega : qdst + 1 ≤ 2 * qdst)
    have hmul :=
      mul_le_mul_of_nonneg_left hcount hdstPert_nonneg
    nlinarith [hdstPrefix_bound, hmul]
  have hsrcPrefix_nonneg : 0 ≤ srcPrefix := by
    dsimp [srcPrefix]
    exact
      AppliedModelingLib.Math.prefixScaledError_nonneg
        (topKPowerLawAsymptoticSrcPerturbation C likelihood γ src)
        (topKPowerLawAsymptoticSrcPerturbation_nonneg
          C likelihood γ src) N
  have hdstPrefix_nonneg : 0 ≤ dstPrefix := by
    dsimp [dstPrefix]
    exact
      AppliedModelingLib.Math.prefixScaledError_nonneg
        (topKPowerLawAsymptoticDstPerturbation C likelihood γ dst)
        (topKPowerLawAsymptoticDstPerturbation_nonneg
          C likelihood γ dst) N
  have hsrcPrefix_le_sum :
      srcPrefix ≤
        ∑ t : ItemType T,
          AppliedModelingLib.Math.prefixScaledError
            (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N := by
    dsimp [srcPrefix]
    exact Finset.single_le_sum
      (fun t _ =>
        AppliedModelingLib.Math.prefixScaledError_nonneg
          (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t)
          (topKPowerLawAsymptoticSrcPerturbation_nonneg
            C likelihood γ t) N)
      (Finset.mem_univ src)
  have hdstPrefix_le_sum :
      dstPrefix ≤
        ∑ t : ItemType T,
          AppliedModelingLib.Math.prefixScaledError
            (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N := by
    dsimp [dstPrefix]
    exact Finset.single_le_sum
      (fun t _ =>
        AppliedModelingLib.Math.prefixScaledError_nonneg
          (topKPowerLawAsymptoticDstPerturbation C likelihood γ t)
          (topKPowerLawAsymptoticDstPerturbation_nonneg
            C likelihood γ t) N)
      (Finset.mem_univ dst)
  have hbudget_lt_error :
      1 / likelihood dst ^ γ +
          srcPert * (qsrc : ℝ) +
            dstPert * (((qdst + 1 : ℕ) : ℝ)) <
        topKPowerLawAsymptoticFOCError C likelihood γ N * (N : ℝ) := by
    have hshift' := hshift dst
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hsrc_sum_nonneg :
        0 ≤
          ∑ t : ItemType T,
            AppliedModelingLib.Math.prefixScaledError
              (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N := by
      exact Finset.sum_nonneg
        (fun t _ =>
          AppliedModelingLib.Math.prefixScaledError_nonneg
            (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t)
            (topKPowerLawAsymptoticSrcPerturbation_nonneg
              C likelihood γ t) N)
    have hdst_sum_nonneg :
        0 ≤
          ∑ t : ItemType T,
            AppliedModelingLib.Math.prefixScaledError
              (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N := by
      exact Finset.sum_nonneg
        (fun t _ =>
          AppliedModelingLib.Math.prefixScaledError_nonneg
            (topKPowerLawAsymptoticDstPerturbation C likelihood γ t)
            (topKPowerLawAsymptoticDstPerturbation_nonneg
              C likelihood γ t) N)
    have hsrc_to_sum :
        srcPert * (qsrc : ℝ) ≤
          2 *
            (∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N) *
              (N : ℝ) := by
      have hmul :
          srcPrefix * (N : ℝ) ≤
            (∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N) *
              (N : ℝ) :=
        mul_le_mul_of_nonneg_right hsrcPrefix_le_sum hN_nonneg
      calc
        srcPert * (qsrc : ℝ)
            ≤ 2 * srcPrefix * (N : ℝ) := hsrcPert_count_bound
        _ = 2 * (srcPrefix * (N : ℝ)) := by ring
        _ ≤ 2 *
            ((∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N) *
              (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 *
            (∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticSrcPerturbation C likelihood γ t) N) *
              (N : ℝ) := by ring
    have hdst_to_sum :
        dstPert * (((qdst + 1 : ℕ) : ℝ)) ≤
          2 *
            (∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N) *
              (N : ℝ) := by
      have hmul :
          dstPrefix * (N : ℝ) ≤
            (∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N) *
              (N : ℝ) :=
        mul_le_mul_of_nonneg_right hdstPrefix_le_sum hN_nonneg
      calc
        dstPert * (((qdst + 1 : ℕ) : ℝ))
            ≤ 2 * dstPrefix * (N : ℝ) := hdstPert_count_bound
        _ = 2 * (dstPrefix * (N : ℝ)) := by ring
        _ ≤ 2 *
            ((∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N) *
              (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 *
            (∑ t : ItemType T,
              AppliedModelingLib.Math.prefixScaledError
                (topKPowerLawAsymptoticDstPerturbation C likelihood γ t) N) *
              (N : ℝ) := by ring
    unfold topKPowerLawAsymptoticFOCError
    nlinarith [hshift', hsrc_to_sum, hdst_to_sum, hsrc_sum_nonneg,
      hdst_sum_nonneg, hN_nonneg]
  have hbudget_lt_gap :
      1 / likelihood dst ^ γ +
          srcPert * (qsrc : ℝ) +
            dstPert * (((qdst + 1 : ℕ) : ℝ)) <
        (qsrc : ℝ) / likelihood src ^ γ -
          (qdst : ℝ) / likelihood dst ^ γ :=
    lt_trans hbudget_lt_error hgap
  have hsrc_den_pos :
      0 < (likelihood src * (1 + esrc)) ^ γ := by
    exact Real.rpow_pos_of_pos
      (mul_pos (hlike_pos src) hone_add_esrc_pos) γ
  have hdst_den_pos :
      0 < (likelihood dst * (1 - edst)) ^ γ := by
    exact Real.rpow_pos_of_pos
      (mul_pos (hlike_pos dst) hone_sub_edst_pos) γ
  have hsrc_scaled_lower :
      (qsrc : ℝ) / likelihood src ^ γ -
          srcPert * (qsrc : ℝ) ≤
        (qsrc : ℝ) / ((likelihood src * (1 + esrc)) ^ γ) := by
    have hdiff :
        1 / likelihood src ^ γ -
            1 / ((likelihood src * (1 + esrc)) ^ γ) ≤
          srcPert := by
      have hle :=
        le_abs_self
          (1 / likelihood src ^ γ -
            1 / ((likelihood src * (1 + esrc)) ^ γ))
      simpa [srcPert, topKPowerLawAsymptoticSrcPerturbation, esrc]
        using hle
    have hq_nonneg : 0 ≤ (qsrc : ℝ) := Nat.cast_nonneg qsrc
    have hmul := mul_le_mul_of_nonneg_right hdiff hq_nonneg
    calc
      (qsrc : ℝ) / likelihood src ^ γ -
          srcPert * (qsrc : ℝ)
          ≤ (qsrc : ℝ) / likelihood src ^ γ -
              (1 / likelihood src ^ γ -
                  1 / ((likelihood src * (1 + esrc)) ^ γ)) *
                (qsrc : ℝ) := by
            linarith
      _ = (qsrc : ℝ) /
          ((likelihood src * (1 + esrc)) ^ γ) := by ring
  have hdst_scaled_upper :
      (((qdst + 1 : ℕ) : ℝ)) /
          ((likelihood dst * (1 - edst)) ^ γ) ≤
        (qdst : ℝ) / likelihood dst ^ γ +
          1 / likelihood dst ^ γ +
            dstPert * (((qdst + 1 : ℕ) : ℝ)) := by
    have hdiff :
        1 / ((likelihood dst * (1 - edst)) ^ γ) -
            1 / likelihood dst ^ γ ≤
          dstPert := by
      have hle :=
        le_abs_self
          (1 / ((likelihood dst * (1 - edst)) ^ γ) -
            1 / likelihood dst ^ γ)
      simpa [dstPert, topKPowerLawAsymptoticDstPerturbation, edst]
        using hle
    have hq_nonneg :
        0 ≤ (((qdst + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hdiff hq_nonneg
    calc
      (((qdst + 1 : ℕ) : ℝ)) /
          ((likelihood dst * (1 - edst)) ^ γ)
          = (((qdst + 1 : ℕ) : ℝ)) / likelihood dst ^ γ +
              (1 / ((likelihood dst * (1 - edst)) ^ γ) -
                  1 / likelihood dst ^ γ) *
                (((qdst + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (((qdst + 1 : ℕ) : ℝ)) / likelihood dst ^ γ +
            dstPert * (((qdst + 1 : ℕ) : ℝ)) := by
            linarith
      _ = (qdst : ℝ) / likelihood dst ^ γ +
          1 / likelihood dst ^ γ +
            dstPert * (((qdst + 1 : ℕ) : ℝ)) := by
            norm_num
            ring
  have hscaled :
      (((qdst + 1 : ℕ) : ℝ)) /
          ((likelihood dst * (1 - edst)) ^ γ) <
        (qsrc : ℝ) / ((likelihood src * (1 + esrc)) ^ γ) := by
    have hbase_gap :
        (qdst : ℝ) / likelihood dst ^ γ +
            1 / likelihood dst ^ γ +
              dstPert * (((qdst + 1 : ℕ) : ℝ)) <
          (qsrc : ℝ) / likelihood src ^ γ -
            srcPert * (qsrc : ℝ) := by
      linarith only [hbudget_lt_gap]
    calc
      (((qdst + 1 : ℕ) : ℝ)) /
          ((likelihood dst * (1 - edst)) ^ γ)
          ≤ (qdst : ℝ) / likelihood dst ^ γ +
              1 / likelihood dst ^ γ +
                dstPert * (((qdst + 1 : ℕ) : ℝ)) :=
            hdst_scaled_upper
      _ < (qsrc : ℝ) / likelihood src ^ γ -
            srcPert * (qsrc : ℝ) := hbase_gap
      _ ≤ (qsrc : ℝ) /
          ((likelihood src * (1 + esrc)) ^ γ) := hsrc_scaled_lower
  have hscaled_power :
      (((qdst + 1 : ℕ) : ℝ)) /
          (likelihood dst * (1 - edst)) ^ (1 / η) <
        (qsrc : ℝ) /
          (likelihood src * (1 + esrc)) ^ (1 / η) := by
    simpa [hγ_eq] using hscaled
  have hpower_core :
      likelihood src * ((1 + esrc) * (qsrc : ℝ) ^ (-η)) <
        likelihood dst *
          ((1 - edst) * (((qdst + 1 : ℕ) : ℝ) ^ (-η))) :=
    AppliedModelingLib.Math.rpow_neg_marginal_lt_of_scaled_lt'
      (p_src := likelihood src) (p_dst := likelihood dst)
      (c_src := 1 + esrc) (c_dst := 1 - edst)
      (eta := η) (x := (qsrc : ℝ))
      (y := (((qdst + 1 : ℕ) : ℝ)))
      (hlike_pos src) (hlike_pos dst)
      hone_add_esrc_pos hone_sub_edst_pos hη_pos
      (by exact_mod_cast hqsrc_pos)
      (by positivity) hscaled_power
  have hpower_coeff :
      likelihood src *
          ((1 + esrc) * ((qsrc : ℝ) ^ (-η) * coeff)) <
        likelihood dst *
          ((1 - edst) *
            ((((qdst + 1 : ℕ) : ℝ) ^ (-η)) * coeff)) := by
    calc
      likelihood src *
          ((1 + esrc) * ((qsrc : ℝ) ^ (-η) * coeff))
          = (likelihood src *
              ((1 + esrc) * (qsrc : ℝ) ^ (-η))) * coeff := by ring
      _ < (likelihood dst *
              ((1 - edst) *
                (((qdst + 1 : ℕ) : ℝ) ^ (-η)))) * coeff :=
            mul_lt_mul_of_pos_right hpower_core hcoeff_pos
      _ = likelihood dst *
          ((1 - edst) *
            ((((qdst + 1 : ℕ) : ℝ) ^ (-η)) * coeff)) := by ring
  have hback_le :
      (O.toConsumptionModel likelihood k).weightedBackwardMarginal
          src qsrc ≤
        likelihood src *
          ((1 + esrc) * ((qsrc : ℝ) ^ (-η) * coeff)) := by
    have hmarg :
        O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1) =
          O.marginalTopK k src (qsrc - 1) := by
      simp [Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)]
    unfold ConsumptionModel.weightedBackwardMarginal
      TopKValueOracle.toConsumptionModel
    rw [dif_neg hqsrc_pos.ne']
    rw [hmarg]
    have hle := mul_le_mul_of_nonneg_left hsrc_marg_le
      (le_of_lt (hlike_pos src))
    have hscale_rewrite :
        (((qsrc - 1 + 1 : ℕ) : ℝ) ^ (-η)) = (qsrc : ℝ) ^ (-η) := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)]
    calc
      likelihood src * O.marginalTopK k src (qsrc - 1)
          ≤ likelihood src *
              ((1 + esrc) *
                ((((qsrc - 1 + 1 : ℕ) : ℝ) ^ (-η)) * coeff)) := hle
      _ = likelihood src *
            ((1 + esrc) * ((qsrc : ℝ) ^ (-η) * coeff)) := by
              rw [hscale_rewrite]
  have hforward_ge :
      likelihood dst *
          ((1 - edst) *
            ((((qdst + 1 : ℕ) : ℝ) ^ (-η)) * coeff)) ≤
        (O.toConsumptionModel likelihood k).weightedForwardMarginal
          dst qdst := by
    unfold ConsumptionModel.weightedForwardMarginal
      TopKValueOracle.toConsumptionModel
    have hle := mul_le_mul_of_nonneg_left hdst_marg_ge
      (le_of_lt (hlike_pos dst))
    simpa [TopKValueOracle.marginalTopK, mul_assoc, mul_left_comm, mul_comm]
      using hle
  exact lt_of_le_of_lt hback_le (lt_of_lt_of_le hpower_coeff hforward_ge)

/--
Generic exact power-law marginal FOC certificate.

If a top-`k` oracle has exact backward/forward marginals
`q^(-η)` and `(q+1)^(-η)`, then positive likelihood weights make every
large scaled-count gap violate the finite first-order condition. This is the
shared optimization core behind the bounded and Pareto exact power-marginal
checkpoints.
-/
noncomputable def topKPowerLawSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {k : ℕ}
    (likelihood : ItemType T → ℝ) {η γ : ℝ}
    (hη_pos : 0 < η)
    (hγ_eq : 1 / η = γ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (hback :
      ∀ t : ItemType T, ∀ {q : ℕ}, 0 < q →
        O.expectedTopSum k t q - O.expectedTopSum k t (q - 1) =
          (q : ℝ) ^ (-η))
    (hforw :
      ∀ t : ItemType T, ∀ q : ℕ,
        O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q =
          (((q + 1 : ℕ) : ℝ) ^ (-η))) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ => O.toConsumptionModel likelihood k)
      (fun t : ItemType T => likelihood t ^ γ)
      (gammaLikelihoodProfile likelihood γ) where
  weight_pos := by
    intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) γ
  targetShare_eq := by
    intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ γ :=
      Finset.sum_pos
        (fun i _ => Real.rpow_pos_of_pos (hlike_pos i) γ)
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood γ t
      (ne_of_gt hnorm_pos)
  error := powerLawSublinearFOCError likelihood γ
  error_nonneg := powerLawSublinearFOCError_nonneg likelihood γ hlike_pos
  error_tends_to_zero :=
    powerLawSublinearFOCError_tends_to_zero likelihood γ hlike_pos
  large_gap_backward_lt_forward := by
    intro N a hN _hopt src dst hgap
    let weight : ItemType T → ℝ := fun t => likelihood t ^ γ
    let S : ℝ := (∑ t : ItemType T, 1 / weight t) + 1
    have hweight_pos : ∀ t, 0 < weight t := by
      intro t
      dsimp [weight]
      exact Real.rpow_pos_of_pos (hlike_pos t) γ
    have hS_pos : 0 < S := by
      dsimp [S]
      have hsum_nonneg :
          0 ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.sum_nonneg
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
      linarith
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hN_real_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
    have hgapS :
        S <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst := by
      have hmul :
          powerLawSublinearFOCError likelihood γ N * (N : ℝ) = S := by
        simp [powerLawSublinearFOCError, hN_ne, S, weight, hN_real_ne]
      simpa [hmul, weight] using hgap
    have hdst_nonneg :
        0 ≤ (a.count dst : ℝ) / weight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
    have hsrc_div_pos : 0 < (a.count src : ℝ) / weight src := by
      linarith
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hsrc_div_pos
      simp at hsrc_div_pos
    have hinv_dst_lt_S : 1 / weight dst < S := by
      have hinv_le_sum :
          1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.single_le_sum
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
          (Finset.mem_univ dst)
      dsimp [S]
      linarith
    have hscaled_add :
        ((a.count dst : ℝ) + 1) / weight dst <
          (a.count src : ℝ) / weight src := by
      have hsum_lt :
          (a.count dst : ℝ) / weight dst + 1 / weight dst <
            (a.count src : ℝ) / weight src := by
        linarith
      have hadd :
          ((a.count dst : ℝ) + 1) / weight dst =
            (a.count dst : ℝ) / weight dst + 1 / weight dst := by
        ring
      simpa [hadd] using hsum_lt
    have hqsrc_real_pos : 0 < (a.count src : ℝ) := by
      exact_mod_cast hsrc_pos
    have hqdst_succ_pos :
        0 < ((a.count dst + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos (a.count dst)
    have hscaled_for_power :
        ((a.count dst + 1 : ℕ) : ℝ) / likelihood dst ^ (1 / η) <
          (a.count src : ℝ) / likelihood src ^ (1 / η) := by
      have hscaled' :
          ((a.count dst + 1 : ℕ) : ℝ) / weight dst <
            (a.count src : ℝ) / weight src := by
        simpa [Nat.cast_add, Nat.cast_one] using hscaled_add
      simpa [weight, hγ_eq] using hscaled'
    have hmarginal_core :
        likelihood src * (1 * (a.count src : ℝ) ^ (-η)) <
          likelihood dst *
            (1 * (((a.count dst + 1 : ℕ) : ℝ) ^ (-η))) :=
      AppliedModelingLib.Math.rpow_neg_marginal_lt_of_scaled_lt
        (c := 1) (eta := η)
        (hlike_pos src) (hlike_pos dst) zero_lt_one hη_pos
        hqsrc_real_pos hqdst_succ_pos hscaled_for_power
    have hmarginal :
        likelihood src * ((a.count src : ℝ) ^ (-η)) <
          likelihood dst *
            (((a.count dst + 1 : ℕ) : ℝ) ^ (-η)) := by
      simpa using hmarginal_core
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    rw [hback src hsrc_pos, hforw dst (a.count dst)]
    exact hmarginal

/--
Floor-aware version of the pairwise-scaled FOC bridge.

Distribution-specific estimates often prove the large-gap marginal dominance
only after every compared count is above a fixed floor and after the total
problem size is large.  This certificate records those eventual facts and
absorbs the finite prefix by using a deliberately large temporary error, then
produces the clean `PairwiseScaledSublinearFOCCertificate`.
-/
structure PairwiseScaledEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ src dst,
          floor < a.count src →
          floor < a.count dst →
          base_error N * (N : ℝ) <
            (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst →
          (Mseq N).weightedBackwardMarginal src (a.count src) <
            (Mseq N).weightedForwardMarginal dst (a.count dst)

namespace PairwiseScaledEventualSublinearFOCCertificate

/--
Source-shaped constructor for the floor-aware FOC certificate.

Distribution arguments usually prove large-gap marginal dominance directly for
integer source/destination counts.  This constructor turns that count-level
statement into the allocation-level certificate by using feasibility to bound
each realized count by the total problem size.
-/
noncomputable def of_count_gap {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hweight_pos : ∀ t, 0 < weight t)
    (htarget :
      ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error)
    (floor : ℕ)
    (count_floor_eventually :
      ∀ᶠ N in atTop,
        ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
          ∀ t, floor < a.count t)
    (large_gap_count :
      ∀ᶠ N in atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          floor < qsrc →
          floor < qdst →
          base_error N * (N : ℝ) <
            (qsrc : ℝ) / weight src - (qdst : ℝ) / weight dst →
          (Mseq N).weightedBackwardMarginal src qsrc <
            (Mseq N).weightedForwardMarginal dst qdst) :
    PairwiseScaledEventualSublinearFOCCertificate Mseq weight G where
  weight_pos := hweight_pos
  targetShare_eq := htarget
  base_error := base_error
  base_error_nonneg := base_error_nonneg
  base_error_tends_to_zero := base_error_tends_to_zero
  floor := floor
  count_floor_eventually := count_floor_eventually
  large_gap_backward_lt_forward_after_floor := by
    filter_upwards [large_gap_count] with N hN a _hNpos hopt src dst
      hsrc_floor hdst_floor hgap
    have hsrc_count_le_N : a.count src ≤ N := by
      have hle := AppliedModelingLib.Allocation.count_le_total a src
      rw [hopt.1] at hle
      exact hle
    have hdst_count_le_N : a.count dst ≤ N := by
      have hle := AppliedModelingLib.Allocation.count_le_total a dst
      rw [hopt.1] at hle
      exact hle
    exact hN src dst (a.count src) (a.count dst)
      hsrc_count_le_N hdst_count_le_N hsrc_floor hdst_floor hgap

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledEventualSublinearFOCCertificate Mseq weight G) :
    AppliedModelingLib.Allocation.PairwiseScaledEventualSublinearFOCCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  baseError := hcert.base_error
  baseError_nonneg := hcert.base_error_nonneg
  baseError_tends_to_zero := hcert.base_error_tends_to_zero
  floor := hcert.floor
  count_floor_eventually := by
    filter_upwards [hcert.count_floor_eventually] with N hN a hNpos hopt
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    exact hN a hNpos hopt'
  large_gap_backward_lt_forward_after_floor := by
    filter_upwards [hcert.large_gap_backward_lt_forward_after_floor] with
      N hN a hNpos hopt src dst hsrc hdst hgap
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    have hdom := hN a hNpos hopt' src dst hsrc hdst hgap
    simpa [ConsumptionModel.weightedBackwardMarginal,
      ConsumptionModel.weightedForwardMarginal, ConsumptionModel.marginalValue,
      AppliedModelingLib.Allocation.weightedBackwardMarginal,
      AppliedModelingLib.Allocation.weightedForwardMarginal,
      AppliedModelingLib.Allocation.marginal] using hdom

noncomputable def toPairwiseScaledSublinearFOCCertificate
    {T : ℕ} [NeZero T] {Mseq : ℕ → ConsumptionModel T}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledEventualSublinearFOCCertificate Mseq weight G) :
    PairwiseScaledSublinearFOCCertificate Mseq weight G :=
  let hshared := hcert.toShared.toPairwiseScaledSublinearFOCCertificate
  { weight_pos := hshared.weight_pos
    targetShare_eq := hshared.target_eq
    error := hshared.error
    error_nonneg := hshared.error_nonneg
    error_tends_to_zero := hshared.error_tends_to_zero
    large_gap_backward_lt_forward := by
      intro N a hN hopt src dst hgap
      have hopt' :
          AppliedModelingLib.Allocation.IsOptimalAtTotal
            (Mseq N).likelihood (Mseq N).valueOfCount N a := by
        simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
          ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
          ConsumptionModel.objective] using hopt
      have hdom :=
        hshared.large_gap_backward_lt_forward N a hN hopt' src dst hgap
      simpa [ConsumptionModel.weightedBackwardMarginal,
        ConsumptionModel.weightedForwardMarginal, ConsumptionModel.marginalValue,
        AppliedModelingLib.Allocation.weightedBackwardMarginal,
        AppliedModelingLib.Allocation.weightedForwardMarginal,
        AppliedModelingLib.Allocation.marginal] using hdom }

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledEventualSublinearFOCCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G := by
  have hgeneric :
      AppliedModelingLib.Allocation.AsymptoticProfile
        (fun N => (Mseq N).likelihood)
        (fun N => (Mseq N).valueOfCount)
        G.targetShare :=
    hcert.toShared.asymptoticProfile
  rcases hgeneric with ⟨ε, hε, happrox⟩
  refine ⟨ε, hε, ?_⟩
  intro N a hN hopt
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        (Mseq N).likelihood (Mseq N).valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal,
      ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
      ConsumptionModel.objective] using hopt
  have happ := happrox N a hN hopt'
  simpa [AppliedModelingLib.Allocation.HasApproxShare,
    GammaHomogeneityProfile.Approx, CountAllocation.HasApproxRepresentation,
    CountAllocation.representation] using happ

end PairwiseScaledEventualSublinearFOCCertificate

/--
Top-`k` source-shaped sublinear FOC certificate for Theorem 1(i).

For the finite-discrete branch, the remaining probability/order-statistic work
should prove the `large_gap_backward_lt_forward` field: if one type has more
than `error N * N` extra recommendations relative to another, then the source's
last-item top-`k` marginal is strictly smaller than the destination's next-item
top-`k` marginal. This specialized certificate avoids exposing reviewers to
the generic scaled-weight interface when the target is uniform.
-/
structure TopKUniformSublinearFOCCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : CountAllocation T), 0 < N →
      (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
      ∀ src dst,
        error N * (N : ℝ) < (a.count src : ℝ) - (a.count dst : ℝ) →
        likelihood src *
            (O.expectedTopSum k src (a.count src) -
              O.expectedTopSum k src (a.count src - 1)) <
          likelihood dst *
            (O.expectedTopSum k dst (a.count dst + 1) -
              O.expectedTopSum k dst (a.count dst))

namespace TopKUniformSublinearFOCCertificate

noncomputable def toPairwiseScaledSublinearFOCCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ => O.toConsumptionModel likelihood k)
      (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T) where
  weight_pos := by
    intro t
    norm_num
  targetShare_eq := by
    intro t
    rw [uniformProfile_targetShare]
    simp [Finset.sum_const, Fintype.card_fin]
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  large_gap_backward_lt_forward := by
    intro N a hN hopt src dst hgap
    have hgap_unweighted :
        hcert.error N * (N : ℝ) <
          (a.count src : ℝ) - (a.count dst : ℝ) := by
      simpa using hgap
    have hC_nonneg : 0 ≤ hcert.error N * (N : ℝ) :=
      mul_nonneg (hcert.error_nonneg N) (Nat.cast_nonneg N)
    have hdiff_pos :
        0 < (a.count src : ℝ) - (a.count dst : ℝ) :=
      lt_of_le_of_lt hC_nonneg hgap_unweighted
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      have hdst_nonneg : 0 ≤ (a.count dst : ℝ) := Nat.cast_nonneg _
      rw [hzero] at hdiff_pos
      have hnonpos : (0 : ℝ) - (a.count dst : ℝ) ≤ 0 := by
        linarith
      exact (not_lt_of_ge hnonpos) (by simpa using hdiff_pos)
    have hdom :=
      hcert.large_gap_backward_lt_forward N a hN hopt src dst hgap_unweighted
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel at *
    rw [dif_neg hsrc_pos.ne'] at *
    exact hdom

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) := hcert.toPairwiseScaledSublinearFOCCertificate.asymptoticHomogeneity

end TopKUniformSublinearFOCCertificate

/--
Count-floor certificate for source Theorem 1(i)'s top-`k` route.

If every sufficiently large source count has a last-item marginal below every
destination count at or below `floor`, then no large finite optimum can leave a
type at or below that floor: moving one recommendation from an overlarge source
to the underfilled destination would strictly improve the objective.
-/
structure TopKUniformCountFloorCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  floor : ℕ
  source_threshold : ℕ
  floor_le_source_threshold : floor ≤ source_threshold
  backward_lt_forward_to_floor :
    ∀ src dst qsrc qdst,
      source_threshold < qsrc →
      qdst ≤ floor →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) <
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformCountFloorCertificate

theorem exists_count_gt_source_threshold {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformCountFloorCertificate O likelihood k)
    {N : ℕ} (a : CountAllocation T)
    (htotal : AppliedModelingLib.Allocation.total a = N)
    (hlarge : T * hcert.source_threshold < N) :
    ∃ src : ItemType T, hcert.source_threshold < a.count src := by
  by_contra hnone
  push Not at hnone
  have hsum_le :
      AppliedModelingLib.Allocation.total a ≤ T * hcert.source_threshold := by
    unfold AppliedModelingLib.Allocation.total
    calc
      (∑ t : ItemType T, a.count t)
          ≤ ∑ _t : ItemType T, hcert.source_threshold :=
            Finset.sum_le_sum (fun t _ => hnone t)
      _ = T * hcert.source_threshold := by
            simp [Finset.sum_const, Fintype.card_fin]
  rw [htotal] at hsum_le
  exact (not_lt_of_ge hsum_le) hlarge

theorem count_floor_eventually {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformCountFloorCertificate O likelihood k) :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, hcert.floor < a.count t := by
  refine eventually_atTop.2 ?_
  refine ⟨T * hcert.source_threshold + 1, ?_⟩
  intro N hN a hNpos hopt dst
  by_contra hnot
  have hdst_le_floor : a.count dst ≤ hcert.floor := le_of_not_gt hnot
  have hlarge : T * hcert.source_threshold < N := by omega
  obtain ⟨src, hsrc_large⟩ :=
    hcert.exists_count_gt_source_threshold a hopt.1 hlarge
  have hsrc_pos : 0 < a.count src :=
    Nat.zero_lt_of_lt hsrc_large
  have hne : src ≠ dst := by
    intro hsame
    subst dst
    exact (not_lt_of_ge
      (le_trans hdst_le_floor hcert.floor_le_source_threshold)) hsrc_large
  have hfoc :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := O.toConsumptionModel likelihood k) (N := N) (a := a)
      (src := src) (dst := dst) hopt hne hsrc_pos
  have hdom :=
    hcert.backward_lt_forward_to_floor src dst (a.count src) (a.count dst)
      hsrc_large hdst_le_floor
  unfold ConsumptionModel.weightedBackwardMarginal
    ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel at hfoc
  rw [dif_neg hsrc_pos.ne'] at hfoc
  exact (not_lt_of_ge hfoc) hdom

end TopKUniformCountFloorCertificate

/--
Eventual, floor-dependent top-`k` FOC certificate for Theorem 1(i).

Distribution-level order-statistic estimates are typically only available once
both compared type counts are above a fixed floor and the total slate size is
large.  This certificate records that source-shaped obligation, together with
the matching eventual count-floor fact for finite optima.  The wrapper below
absorbs the finite prefix by assigning a deliberately large temporary error,
then produces the clean `TopKUniformSublinearFOCCertificate` consumed by the
paper-facing theorem.
-/
structure TopKUniformEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) <
          likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)

namespace TopKUniformEventualSublinearFOCCertificate

noncomputable def toPairwiseScaledEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    PairwiseScaledEventualSublinearFOCCertificate
      (fun _ => O.toConsumptionModel likelihood k)
      (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T) where
  weight_pos := by
    intro t
    norm_num
  targetShare_eq := by
    intro t
    rw [uniformProfile_targetShare]
    simp [Finset.sum_const, Fintype.card_fin]
  base_error := hcert.base_error
  base_error_nonneg := hcert.base_error_nonneg
  base_error_tends_to_zero := hcert.base_error_tends_to_zero
  floor := hcert.floor
  count_floor_eventually := hcert.count_floor_eventually
  large_gap_backward_lt_forward_after_floor := by
    filter_upwards [hcert.large_gap_backward_lt_forward_after_floor] with
      N hN a _hNpos hopt src dst hsrc hdst hgap
    have hsrc_count_le_N : a.count src ≤ N := by
      have hle := AppliedModelingLib.Allocation.count_le_total a src
      rw [hopt.1] at hle
      exact hle
    have hdst_count_le_N : a.count dst ≤ N := by
      have hle := AppliedModelingLib.Allocation.count_le_total a dst
      rw [hopt.1] at hle
      exact hle
    have hgap_unweighted :
        hcert.base_error N * (N : ℝ) <
          (a.count src : ℝ) - (a.count dst : ℝ) := by
      simpa using hgap
    have hdom :=
      hN src dst (a.count src) (a.count dst)
        hsrc_count_le_N hdst_count_le_N hsrc hdst hgap_unweighted
    have hsrc_pos : 0 < a.count src := Nat.zero_lt_of_lt hsrc
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    exact hdom

noncomputable def of_count_floor_certificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hfloor : TopKUniformCountFloorCertificate O likelihood k)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error)
    (large_gap_backward_lt_forward_after_floor :
      ∀ᶠ N in atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          hfloor.floor < qsrc →
          hfloor.floor < qdst →
          base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
          likelihood src *
              (O.expectedTopSum k src qsrc -
                O.expectedTopSum k src (qsrc - 1)) <
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    TopKUniformEventualSublinearFOCCertificate O likelihood k where
  base_error := base_error
  base_error_nonneg := base_error_nonneg
  base_error_tends_to_zero := base_error_tends_to_zero
  floor := hfloor.floor
  count_floor_eventually := hfloor.count_floor_eventually
  large_gap_backward_lt_forward_after_floor :=   large_gap_backward_lt_forward_after_floor

noncomputable def toTopKUniformSublinearFOCCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    TopKUniformSublinearFOCCertificate O likelihood k :=
  let hpair :=
    hcert.toPairwiseScaledEventualSublinearFOCCertificate
      |>.toPairwiseScaledSublinearFOCCertificate
  { error := hpair.error
    error_nonneg := hpair.error_nonneg
    error_tends_to_zero := hpair.error_tends_to_zero
    large_gap_backward_lt_forward := by
      intro N a hN hopt src dst hgap
      have hgap_scaled :
          hpair.error N * (N : ℝ) <
            (a.count src : ℝ) / (1 : ℝ) -
              (a.count dst : ℝ) / (1 : ℝ) := by
        simpa using hgap
      have hdom :=
        hpair.large_gap_backward_lt_forward N a hN hopt src dst hgap_scaled
      have hC_nonneg : 0 ≤ hpair.error N * (N : ℝ) :=
        mul_nonneg (hpair.error_nonneg N) (Nat.cast_nonneg N)
      have hdiff_pos :
          0 < (a.count src : ℝ) - (a.count dst : ℝ) :=
        lt_of_le_of_lt hC_nonneg hgap
      have hsrc_pos : 0 < a.count src := by
        by_contra hnot
        have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
        have hdst_nonneg : 0 ≤ (a.count dst : ℝ) := Nat.cast_nonneg _
        rw [hzero] at hdiff_pos
        have hnonpos : (0 : ℝ) - (a.count dst : ℝ) ≤ 0 := by
          linarith
        exact (not_lt_of_ge hnonpos) (by simpa using hdiff_pos)
      unfold ConsumptionModel.weightedBackwardMarginal
        ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
        AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel at hdom
      rw [dif_neg hsrc_pos.ne'] at hdom
      exact hdom }

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) := hcert.toTopKUniformSublinearFOCCertificate.asymptoticHomogeneity

end TopKUniformEventualSublinearFOCCertificate

/--
Finite-discrete geometric marginal-bound certificate for Theorem 1(i).

The source proof bounds top-`k` marginals by a polynomial-times-geometric upper
tail and a geometric lower tail.  This certificate is the optimization-facing
form of that probability estimate: it supplies the marginal bounds and a
sublinear integer gap schedule whose polynomial-geometric product is eventually
smaller than the lower-tail constant.
-/
structure TopKUniformGeometricMarginalBoundCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  floor : ℕ
  source_threshold : ℕ
  floor_le_source_threshold : floor ≤ source_threshold
  floor_backward_lt_forward :
    ∀ src dst qsrc qdst,
      source_threshold < qsrc →
      qdst ≤ floor →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) <
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  degree : ℕ
  gap : ℕ → ℕ
  gap_error_tends_to_zero :
    AppliedModelingLib.Math.TendsToZero
      (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ))
  gap_dominance_eventually :
    ∀ᶠ (N : ℕ) in atTop,
      upper * (N : ℝ) ^ degree * rho ^ (gap N) < lower
  weighted_backward_upper :
    ∀ src qsrc,
      floor < qsrc →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) ≤
        upper * (qsrc : ℝ) ^ degree * rho ^ qsrc
  weighted_forward_lower :
    ∀ dst qdst,
      floor < qdst →
      lower * rho ^ qdst ≤
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformGeometricMarginalBoundCertificate

noncomputable def toCountFloorCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert :
      TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    TopKUniformCountFloorCertificate O likelihood k where
  floor := hcert.floor
  source_threshold := hcert.source_threshold
  floor_le_source_threshold := hcert.floor_le_source_threshold
  backward_lt_forward_to_floor := hcert.floor_backward_lt_forward

noncomputable def toEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert :
      TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    TopKUniformEventualSublinearFOCCertificate O likelihood k := by
  classical
  refine
    TopKUniformEventualSublinearFOCCertificate.of_count_floor_certificate
      hcert.toCountFloorCertificate
      (fun N => ((hcert.gap N + 1 : ℕ) : ℝ) / (N : ℝ))
      ?_ hcert.gap_error_tends_to_zero ?_
  · intro N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards
      [hcert.gap_dominance_eventually, eventually_gt_atTop 0]
      with N hdom hNpos src dst qsrc qdst hsrc_le_N hdst_le_N
        hsrc_floor hdst_floor hgap
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
    have hgap_real :
        (((hcert.gap N + 1 : ℕ) : ℝ) <
          (qsrc : ℝ) - (qdst : ℝ)) := by
      simpa [div_mul_cancel₀ _ hN_ne] using hgap
    have hsum_real :
        ((qdst + (hcert.gap N + 1) : ℕ) : ℝ) < (qsrc : ℝ) := by
      rw [Nat.cast_add]
      linarith
    have hsum_nat :
        qdst + (hcert.gap N + 1) < qsrc := by
      exact_mod_cast hsum_real
    have hqdst_gap_le_qsrc : qdst + hcert.gap N ≤ qsrc := by
      omega
    have hpow_gap :
        hcert.rho ^ qsrc ≤ hcert.rho ^ qdst * hcert.rho ^ hcert.gap N := by
      calc
        hcert.rho ^ qsrc
            ≤ hcert.rho ^ (qdst + hcert.gap N) :=
              pow_le_pow_of_le_one hcert.rho_pos.le hcert.rho_lt_one.le
                hqdst_gap_le_qsrc
        _ = hcert.rho ^ qdst * hcert.rho ^ hcert.gap N := by
              rw [pow_add]
    have hqsrc_pow_le_N_pow :
        (qsrc : ℝ) ^ hcert.degree ≤ (N : ℝ) ^ hcert.degree :=
      pow_le_pow_left₀ (Nat.cast_nonneg qsrc)
        (by exact_mod_cast hsrc_le_N) hcert.degree
    have hupper_nonneg : 0 ≤ hcert.upper := le_of_lt hcert.upper_pos
    have hNpow_nonneg : 0 ≤ (N : ℝ) ^ hcert.degree :=
      pow_nonneg (Nat.cast_nonneg N) hcert.degree
    have hrho_qsrc_nonneg : 0 ≤ hcert.rho ^ qsrc :=
      pow_nonneg hcert.rho_pos.le qsrc
    have hback_upper :=
      hcert.weighted_backward_upper src qsrc hsrc_floor
    have hforward_lower :=
      hcert.weighted_forward_lower dst qdst hdst_floor
    have hback_le_gap :
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) ≤
          hcert.upper * (N : ℝ) ^ hcert.degree *
            (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N) := by
      calc
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1))
            ≤ hcert.upper * (qsrc : ℝ) ^ hcert.degree *
                hcert.rho ^ qsrc := hback_upper
        _ ≤ hcert.upper * (N : ℝ) ^ hcert.degree *
                hcert.rho ^ qsrc :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hqsrc_pow_le_N_pow hupper_nonneg)
                hrho_qsrc_nonneg
        _ ≤ hcert.upper * (N : ℝ) ^ hcert.degree *
                (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N) :=
              mul_le_mul_of_nonneg_left hpow_gap
                (mul_nonneg hupper_nonneg hNpow_nonneg)
    have hgap_weighted_lt :
        hcert.upper * (N : ℝ) ^ hcert.degree *
            (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N) <
          hcert.lower * hcert.rho ^ qdst := by
      have hrho_qdst_pos : 0 < hcert.rho ^ qdst :=
        pow_pos hcert.rho_pos qdst
      have hmul :=
        mul_lt_mul_of_pos_right hdom hrho_qdst_pos
      calc
        hcert.upper * (N : ℝ) ^ hcert.degree *
            (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N)
            = (hcert.upper * (N : ℝ) ^ hcert.degree *
                hcert.rho ^ hcert.gap N) * hcert.rho ^ qdst := by
              ring
        _ < hcert.lower * hcert.rho ^ qdst := hmul
    exact lt_of_le_of_lt hback_le_gap
      (lt_of_lt_of_le hgap_weighted_lt hforward_lower)

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert :
      TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) := hcert.toEventualSublinearFOCCertificate.asymptoticHomogeneity

end TopKUniformGeometricMarginalBoundCertificate

/--
Finite-discrete geometric tail certificate for Theorem 1(i).

This is one step closer to the source distribution argument than
`TopKUniformGeometricMarginalBoundCertificate`: it assumes a positive lower
bound on the finitely many destination marginals up to the floor, and derives
the large-source/small-destination count-floor comparison from the geometric
upper tail.
-/
structure TopKUniformGeometricTailCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  floor : ℕ
  small_forward_lower : ℝ
  small_forward_lower_pos : 0 < small_forward_lower
  weighted_forward_lower_to_floor :
    ∀ dst qdst,
      qdst ≤ floor →
        small_forward_lower ≤
          likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  degree : ℕ
  gap : ℕ → ℕ
  gap_error_tends_to_zero :
    AppliedModelingLib.Math.TendsToZero
      (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ))
  gap_dominance_eventually :
    ∀ᶠ (N : ℕ) in atTop,
      upper * (N : ℝ) ^ degree * rho ^ (gap N) < lower
  weighted_backward_upper :
    ∀ src qsrc,
      floor < qsrc →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) ≤
        upper * (qsrc : ℝ) ^ degree * rho ^ qsrc
  weighted_forward_lower :
    ∀ dst qdst,
      floor < qdst →
      lower * rho ^ qdst ≤
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformGeometricTailCertificate

noncomputable def of_binomial_event_bounds {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (small_forward_lower : ℝ)
    (small_forward_lower_pos : 0 < small_forward_lower)
    (weighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          small_forward_lower ≤
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst))
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in atTop,
        (backwardLoss * ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          forwardGain * q ^ k * (rho ^ (k - 1))⁻¹)
    (weighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (weighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    TopKUniformGeometricTailCertificate O likelihood k where
  rho := rho
  rho_pos := hrho_pos
  rho_lt_one := hrho_lt_one
  floor := floor
  small_forward_lower := small_forward_lower
  small_forward_lower_pos := small_forward_lower_pos
  weighted_forward_lower_to_floor := weighted_forward_lower_to_floor
  lower := forwardGain * q ^ k * (rho ^ (k - 1))⁻¹
  upper := backwardLoss * ((k : ℝ) * (rho ^ (k - 1))⁻¹)
  lower_pos :=
    mul_pos (mul_pos forwardGain_pos (pow_pos hq_pos k))
      (inv_pos.mpr (pow_pos hrho_pos (k - 1)))
  upper_pos :=
    mul_pos backwardLoss_pos
      (mul_pos (by exact_mod_cast hk_pos)
        (inv_pos.mpr (pow_pos hrho_pos (k - 1))))
  degree := k
  gap := gap
  gap_error_tends_to_zero := gap_error_tends_to_zero
  gap_dominance_eventually := gap_dominance_eventually
  weighted_backward_upper := by
    intro src qsrc hfloor_lt
    have hk_le_qsrc : k ≤ qsrc := by omega
    have htail :=
      finiteDiscreteTopMassFailureTail_le_polynomial_geometric_at_a
        hk_pos hk_le_qsrc hq_pos.le hq_le_one hrho_pos hrho_lt_one.le
    have hback :=
      weighted_backward_upper_by_failure_tail src qsrc hfloor_lt
    have hbackwardLoss_nonneg : 0 ≤ backwardLoss := le_of_lt backwardLoss_pos
    calc
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1))
          ≤ backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho :=
            hback
      _ ≤ backwardLoss *
            (((k : ℝ) * (rho ^ (k - 1))⁻¹) *
              (qsrc : ℝ) ^ k * rho ^ qsrc) :=
            mul_le_mul_of_nonneg_left htail hbackwardLoss_nonneg
      _ = backwardLoss * ((k : ℝ) * (rho ^ (k - 1))⁻¹) *
            (qsrc : ℝ) ^ k * rho ^ qsrc := by
            ring
  weighted_forward_lower := by
    intro dst qdst hfloor_lt
    have hk_le_qdst : k ≤ qdst := by omega
    have htail :=
      finiteDiscreteTopMassPromotingEvent_lower_geometric_at_a
        hk_pos hk_le_qdst hq_pos.le hrho_pos
    have hforward :=
      weighted_forward_lower_by_promoting_event dst qdst hfloor_lt
    have hforwardGain_nonneg : 0 ≤ forwardGain := le_of_lt forwardGain_pos
    calc
      forwardGain * q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ qdst
          = forwardGain *
              (q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ qdst) := by
            ring
      _ ≤ forwardGain *
              finiteDiscreteTopMassPromotingEvent k qdst q rho :=
            mul_le_mul_of_nonneg_left htail hforwardGain_nonneg
      _ ≤ likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) := hforward

noncomputable def of_unweighted_binomial_event_bounds {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (unweighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          smallForward ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
    (unweighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (unweighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) :
    TopKUniformGeometricTailCertificate O likelihood k :=
  of_binomial_event_bounds
    (O := O) (likelihood := likelihood) (k := k)
    q rho hk_pos hq_pos hq_le_one hrho_pos hrho_lt_one
    floor hk_le_floor_succ
    (likelihoodLower * smallForward)
    (mul_pos likelihoodLower_pos smallForward_pos)
    (by
      intro dst qdst hfloor
      have hcore := unweighted_forward_lower_to_floor dst qdst hfloor
      have hmarg_nonneg :
          0 ≤ O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst :=
        le_trans smallForward_pos.le hcore
      calc
        likelihoodLower * smallForward
            ≤ likelihoodLower *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_left hcore likelihoodLower_pos.le
        _ ≤ likelihood dst *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_right (likelihoodLower_le dst)
                hmarg_nonneg)
    (likelihoodUpper * backwardLoss)
    (likelihoodLower * forwardGain)
    (mul_pos likelihoodUpper_pos backwardLoss_pos)
    (mul_pos likelihoodLower_pos forwardGain_pos)
    gap gap_error_tends_to_zero gap_dominance_eventually
    (by
      intro src qsrc hfloor_lt
      have hraw :=
        unweighted_backward_upper_by_failure_tail src qsrc hfloor_lt
      have htail_nonneg :
          0 ≤ finiteDiscreteTopMassFailureTail k qsrc q rho :=
        finiteDiscreteTopMassFailureTail_nonneg k qsrc hq_pos.le hrho_pos.le
      have hright_nonneg :
          0 ≤ backwardLoss *
            finiteDiscreteTopMassFailureTail k qsrc q rho :=
        mul_nonneg backwardLoss_pos.le htail_nonneg
      have hlike_nonneg : 0 ≤ likelihood src :=
        le_trans likelihoodLower_pos.le (likelihoodLower_le src)
      calc
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1))
            ≤ likelihood src *
                (backwardLoss *
                  finiteDiscreteTopMassFailureTail k qsrc q rho) :=
              mul_le_mul_of_nonneg_left hraw hlike_nonneg
        _ ≤ likelihoodUpper *
                (backwardLoss *
                  finiteDiscreteTopMassFailureTail k qsrc q rho) :=
              mul_le_mul_of_nonneg_right (likelihood_le_upper src)
                hright_nonneg
        _ = likelihoodUpper * backwardLoss *
              finiteDiscreteTopMassFailureTail k qsrc q rho := by
              ring)
    (by
      intro dst qdst hfloor_lt
      have hraw :=
        unweighted_forward_lower_by_promoting_event dst qdst hfloor_lt
      have hevent_nonneg :
          0 ≤ finiteDiscreteTopMassPromotingEvent k qdst q rho :=
        finiteDiscreteTopMassPromotingEvent_nonneg k qdst hq_pos.le hrho_pos.le
      have hleft_nonneg :
          0 ≤ forwardGain *
            finiteDiscreteTopMassPromotingEvent k qdst q rho :=
        mul_nonneg forwardGain_pos.le hevent_nonneg
      have hmarg_nonneg :
          0 ≤ O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst :=
        le_trans hleft_nonneg hraw
      calc
        likelihoodLower * forwardGain *
            finiteDiscreteTopMassPromotingEvent k qdst q rho
            = likelihoodLower *
                (forwardGain *
                  finiteDiscreteTopMassPromotingEvent k qdst q rho) := by
              ring
        _ ≤ likelihoodLower *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_left hraw likelihoodLower_pos.le
        _ ≤ likelihood dst *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_right (likelihoodLower_le dst)
                hmarg_nonneg)

theorem polynomial_geometric_tail_tendsToZero {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    Tendsto
      (fun q : ℕ =>
        hcert.upper * (q : ℝ) ^ hcert.degree * hcert.rho ^ q)
      atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun q : ℕ => (q : ℝ) ^ hcert.degree * hcert.rho ^ q)
        atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one hcert.degree
      hcert.rho_pos.le hcert.rho_lt_one
  simpa [mul_assoc] using hbase.const_mul hcert.upper

noncomputable def toGeometricMarginalBoundCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    TopKUniformGeometricMarginalBoundCertificate O likelihood k := by
  classical
  have heventually_small :
      ∀ᶠ (q : ℕ) in atTop,
        hcert.upper * (q : ℝ) ^ hcert.degree * hcert.rho ^ q <
          hcert.small_forward_lower :=
    hcert.polynomial_geometric_tail_tendsToZero.eventually
      (Iio_mem_nhds hcert.small_forward_lower_pos)
  let threshold : ℕ := Classical.choose (eventually_atTop.1 heventually_small)
  have hthreshold :
      ∀ q ≥ threshold,
        hcert.upper * (q : ℝ) ^ hcert.degree * hcert.rho ^ q <
          hcert.small_forward_lower :=
    Classical.choose_spec (eventually_atTop.1 heventually_small)
  refine
    { rho := hcert.rho
      rho_pos := hcert.rho_pos
      rho_lt_one := hcert.rho_lt_one
      floor := hcert.floor
      source_threshold := max hcert.floor threshold
      floor_le_source_threshold := Nat.le_max_left hcert.floor threshold
      floor_backward_lt_forward := ?_
      lower := hcert.lower
      upper := hcert.upper
      lower_pos := hcert.lower_pos
      upper_pos := hcert.upper_pos
      degree := hcert.degree
      gap := hcert.gap
      gap_error_tends_to_zero := hcert.gap_error_tends_to_zero
      gap_dominance_eventually := hcert.gap_dominance_eventually
      weighted_backward_upper := hcert.weighted_backward_upper
      weighted_forward_lower := hcert.weighted_forward_lower }
  intro src dst qsrc qdst hsrc_large hdst_floor
  have hfloor_lt_qsrc : hcert.floor < qsrc :=
    lt_of_le_of_lt (Nat.le_max_left hcert.floor threshold) hsrc_large
  have hthreshold_le_qsrc : threshold ≤ qsrc :=
    le_trans (Nat.le_max_right hcert.floor threshold) hsrc_large.le
  have htail_small :=
    hthreshold qsrc hthreshold_le_qsrc
  have hback_le :=
    hcert.weighted_backward_upper src qsrc hfloor_lt_qsrc
  have hforward_ge :=
    hcert.weighted_forward_lower_to_floor dst qdst hdst_floor
  exact lt_of_le_of_lt hback_le (lt_of_lt_of_le htail_small hforward_ge)

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) := hcert.toGeometricMarginalBoundCertificate.asymptoticHomogeneity

end TopKUniformGeometricTailCertificate

end PRPKG24AccuracyDiversity

import AppliedModelingLib.Foundations.Probability.FiniteSupportMGF
import AppliedModelingLib.Foundations.Math.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Large-Deviation Certificate Interfaces

Reusable certificate-level infrastructure for EC papers that use exponential
convergence rates but where the analytic theorem itself is best supplied as a
paper-local or distribution-family certificate.

The motivating pattern is the rating-system large-deviation proof:

1. prove or assume a pairwise sample-mean ranking error has exponent `r`;
2. aggregate finitely many pairwise errors;
3. use that finite sums/unions preserve the minimum exponent.

This file formalizes the reusable algebra around steps 2 and 3.

## Main declarations

- `logDecay`
- `HasExponentialRate`
- `HasExtendedExponentialRate`
- `ExponentialRateCertificate`
- `HasExpUpperBoundWithConst`
- `HasExpLowerBoundWithConst`
- `ExponentialRateCertificate.hasExpUpperBoundWithConst_of_lt`
- `ExponentialRateCertificate.hasExpLowerBoundWithConst_of_gt`
- `ExponentialRateCertificate.of_eventually_const_sandwich`
- `finite_weighted_sum_hasExpUpperBoundWithConst`
- `finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates`
- `finite_weighted_sum_hasExpLowerBoundWithConst_of_component`
- `finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component`
- `FiniteErrorRateCertificate`
- `FiniteErrorRateCertificate.aggregateError_hasExponentialRate_of_dominating_subfamily`
- `FiniteErrorRateEnvelopeCertificate`
- `PairwiseErrorUpperBoundCertificate`
- `PairwiseErrorRateCertificate`
- `PairwiseErrorRateEnvelopeCertificate`
-/

/-- Paper-style negative normalized log sequence, `- log(p n) / n`. -/
def logDecay (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  -((n : ℝ)⁻¹) * Real.log (p n)

/-- `p n` has exponential decay rate `rate`. -/
def HasExponentialRate (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  Tendsto (logDecay p) atTop (nhds rate)

namespace HasExponentialRate

/--
Exponential rates are invariant under eventual equality of the underlying
error-probability sequence.
-/
theorem congr {p q : ℕ → ℝ} {rate : ℝ}
    (hpq : p =ᶠ[atTop] q) (h : HasExponentialRate p rate) :
    HasExponentialRate q rate := by
  rw [HasExponentialRate] at h ⊢
  refine h.congr' ?_
  filter_upwards [hpq] with n hn
  simp [logDecay, hn]

/--
Pointwise equality is a convenient special case of eventual congruence for
exponential rates.
-/
theorem congr_of_forall {p q : ℕ → ℝ} {rate : ℝ}
    (hpq : ∀ n, p n = q n) (h : HasExponentialRate p rate) :
    HasExponentialRate q rate :=
  congr (Eventually.of_forall hpq) h

/-- Exact exponential rates are unique. -/
theorem unique {p : ℕ → ℝ} {rate₁ rate₂ : ℝ}
    (h₁ : HasExponentialRate p rate₁)
    (h₂ : HasExponentialRate p rate₂) :
    rate₁ = rate₂ :=
  tendsto_nhds_unique h₁ h₂

/--
A nonnegative sequence with a strictly positive exact exponential rate is
eventually positive.  This packages the standard paper convention that a
positive finite log-decay rate rules out infinitely many zero error terms.
-/
theorem eventually_pos_of_eventually_nonneg_of_pos_rate
    {p : ℕ → ℝ} {rate : ℝ}
    (h : HasExponentialRate p rate) (hrate : 0 < rate)
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ p n) :
    ∀ᶠ n in atTop, 0 < p n := by
  have hhalf_pos : 0 < rate / 2 := by linarith
  have hhalf_lt : rate / 2 < rate := by linarith
  have hdecay : ∀ᶠ n in atTop, rate / 2 ≤ logDecay p n :=
    h.eventually_const_le hhalf_lt
  filter_upwards [hnonneg, hdecay] with n hp_nonneg hdecay_n
  by_contra hnot_pos
  have hp_le : p n ≤ 0 := le_of_not_gt hnot_pos
  have hp_zero : p n = 0 := le_antisymm hp_le hp_nonneg
  have hlogDecay_zero : logDecay p n = 0 := by
    simp [logDecay, hp_zero, Real.log_zero]
  linarith

/--
Finite families of exponential-rate convergences are uniform over the finite
index set. This is the certificate-level form of taking the maximum burn-in
over finitely many large-deviation components.
-/
theorem uniform_logDecay_fintype
    {ι : Type*} [Fintype ι] {p : ι → ℕ → ℝ} {rate : ι → ℝ}
    (h : ∀ i : ι, HasExponentialRate (p i) (rate i)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ i : ι, |logDecay (p i) n - rate i| ≤ ε := by
  intro ε hε
  have hclose :
      ∀ i : ι, ∀ᶠ n in atTop,
        |logDecay (p i) n - rate i| < ε := by
    intro i
    have hi : Tendsto (logDecay (p i)) atTop (nhds (rate i)) := h i
    exact (Metric.tendsto_nhds.1 hi) ε hε
  exact (eventually_all.2 hclose).mono fun _n hn i => (hn i).le

end HasExponentialRate

/--
Extended paper-style exponential rate.  A finite real rate is the usual
`HasExponentialRate`; `⊤` records the boundary case where the error
probability is eventually zero, i.e. has infinite exponential rate in the
source convention.
-/
inductive HasExtendedExponentialRate (p : ℕ → ℝ) : WithTop ℝ → Prop
  | finite {rate : ℝ} (h : HasExponentialRate p rate) :
      HasExtendedExponentialRate p rate
  | infinite (hzero : ∀ᶠ n in atTop, p n = 0) :
      HasExtendedExponentialRate p ⊤

namespace HasExtendedExponentialRate

/--
An extended-rate statement at a finite real rate is exactly the ordinary
real-valued exponential-rate statement.
-/
theorem to_finite {p : ℕ → ℝ} {rate : ℝ}
    (h : HasExtendedExponentialRate p (rate : WithTop ℝ)) :
    HasExponentialRate p rate := by
  cases h with
  | finite hfinite => exact hfinite

end HasExtendedExponentialRate

/--
Certificate that a nonnegative error probability sequence has a named
exponential decay rate.
-/
structure ExponentialRateCertificate (p : ℕ → ℝ) (rate : ℝ) where
  eventually_pos : ∀ᶠ n in atTop, 0 < p n
  has_rate : HasExponentialRate p rate

/--
Eventual exponential upper bound with an arbitrary positive prefactor:
`p n <= C * exp(-n * rate)` eventually.
-/
def HasExpUpperBoundWithConst (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ n in atTop,
    0 ≤ p n ∧ p n ≤ C * Real.exp (-(n : ℝ) * rate)

/--
Eventual exponential lower bound with an arbitrary positive prefactor:
`c * exp(-n * rate) <= p n` eventually.
-/
def HasExpLowerBoundWithConst (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ n : ℕ in atTop,
    c * Real.exp (-(n : ℝ) * rate) ≤ p n

namespace HasExpUpperBoundWithConst

theorem of_eventually_le {p : ℕ → ℝ} {rate C : ℝ}
    (hC : 0 < C)
    (hbound : ∀ᶠ n in atTop,
      0 ≤ p n ∧ p n ≤ C * Real.exp (-(n : ℝ) * rate)) :
    HasExpUpperBoundWithConst p rate :=
  ⟨C, hC, hbound⟩

theorem of_eventually_zero {p : ℕ → ℝ} {rate : ℝ}
    (hzero : ∀ᶠ n in atTop, p n = 0) :
    HasExpUpperBoundWithConst p rate := by
  refine of_eventually_le (C := 1) (by norm_num) ?_
  filter_upwards [hzero] with n hn
  constructor
  · simp [hn]
  · have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * rate) :=
      (Real.exp_pos _).le
    simpa [hn] using hexp_nonneg

theorem weaken_rate {p : ℕ → ℝ} {rate strongRate : ℝ}
    (h : HasExpUpperBoundWithConst p strongRate)
    (hrate : rate ≤ strongRate) :
    HasExpUpperBoundWithConst p rate := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC] with n hn
  refine ⟨hn.1, ?_⟩
  have hexp :
      Real.exp (-(n : ℝ) * strongRate) ≤
        Real.exp (-(n : ℝ) * rate) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hrate
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact hn.2.trans
    (mul_le_mul_of_nonneg_left hexp hCpos.le)

theorem const_mul {p : ℕ → ℝ} {rate c : ℝ}
    (h : HasExpUpperBoundWithConst p rate) (hc : 0 ≤ c) :
    HasExpUpperBoundWithConst (fun n => c * p n) rate := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨(c + 1) * C, mul_pos (by linarith) hCpos, ?_⟩
  filter_upwards [hC] with n hn
  have hnonneg : 0 ≤ c * p n := mul_nonneg hc hn.1
  refine ⟨hnonneg, ?_⟩
  have hmain :
      c * p n ≤ c * (C * Real.exp (-(n : ℝ) * rate)) :=
    mul_le_mul_of_nonneg_left hn.2 hc
  have hcoef :
      c * C ≤ (c + 1) * C := by
    exact mul_le_mul_of_nonneg_right (by linarith) hCpos.le
  calc
    c * p n ≤ c * (C * Real.exp (-(n : ℝ) * rate)) := hmain
    _ = (c * C) * Real.exp (-(n : ℝ) * rate) := by ring
    _ ≤ ((c + 1) * C) * Real.exp (-(n : ℝ) * rate) := by
      exact mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

theorem tendsto_zero_of_pos_rate {p : ℕ → ℝ} {rate : ℝ}
    (h : HasExpUpperBoundWithConst p rate) (hrate : 0 < rate) :
    Tendsto p atTop (nhds 0) := by
  rcases h with ⟨C, hCpos, hCevent⟩
  let rho : ℝ := Real.exp (-rate)
  have hrho_nonneg : 0 ≤ rho := (Real.exp_pos _).le
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hpow : Tendsto (fun n : ℕ => rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho_nonneg hrho_lt_one
  have hexp_zero :
      Tendsto
        (fun n : ℕ => C * Real.exp (-(n : ℝ) * rate))
        atTop (nhds 0) := by
    have hCpow : Tendsto (fun n : ℕ => C * rho ^ n) atTop (nhds 0) := by
      simpa using hpow.const_mul C
    refine hCpow.congr' ?_
    filter_upwards with n
    dsimp [rho]
    rw [← Real.exp_nat_mul]
    congr 1
    ring_nf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexp_zero ?_ ?_
  · filter_upwards [hCevent] with n hn
    exact hn.1
  · filter_upwards [hCevent] with n hn
    exact hn.2

/--
If `1 - P_n` has a positive exponential upper bound, then `P_n` tends to one.
-/
theorem tendsto_one_of_one_sub_pos_rate {P : ℕ → ℝ} {rate : ℝ}
    (h : HasExpUpperBoundWithConst (fun n : ℕ => 1 - P n) rate)
    (hrate : 0 < rate) :
    Tendsto P atTop (nhds 1) := by
  have hzero : Tendsto (fun n : ℕ => 1 - P n) atTop (nhds 0) :=
    h.tendsto_zero_of_pos_rate hrate
  have hone_sub :
      Tendsto (fun n : ℕ => 1 - (1 - P n)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hzero
  simpa using hone_sub

/--
A sequence that is frequently bounded below by a fixed positive constant cannot
have an exponential upper bound at a positive rate.
-/
theorem not_of_frequently_ge_pos {p : ℕ → ℝ} {rate ε : ℝ}
    (hrate : 0 < rate) (hε : 0 < ε)
    (hfreq : ∃ᶠ n in atTop, ε ≤ p n) :
    ¬ HasExpUpperBoundWithConst p rate := by
  intro hupper
  have hzero : Tendsto p atTop (nhds 0) :=
    hupper.tendsto_zero_of_pos_rate hrate
  have hsmall : ∀ᶠ n : ℕ in atTop, p n < ε := by
    have hmetric := (Metric.tendsto_nhds.mp hzero) ε hε
    filter_upwards [hmetric] with n hn
    have hlt := (abs_lt.mp hn).2
    simpa using hlt
  rcases (hfreq.and_eventually hsmall).exists with ⟨n, hge, hlt⟩
  exact not_lt_of_ge hge hlt

/--
A sequence that is frequently at least `exp (-n * lowerRate)` cannot have an
eventual exponential upper bound at any strictly larger rate.
-/
theorem not_of_frequently_ge_exp_neg_mul
    {p : ℕ → ℝ} {upperRate lowerRate : ℝ}
    (hlt_rate : lowerRate < upperRate)
    (hfreq : ∃ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * lowerRate) ≤ p n) :
    ¬ HasExpUpperBoundWithConst p upperRate := by
  intro hupper
  rcases hupper with ⟨C, hCpos, hCevent⟩
  let gap : ℝ := upperRate - lowerRate
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  let rho : ℝ := Real.exp (-gap)
  have hrho_nonneg : 0 ≤ rho := (Real.exp_pos _).le
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hpow : Tendsto (fun n : ℕ => rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho_nonneg hrho_lt_one
  have hratio :
      Tendsto
        (fun n : ℕ => C * Real.exp (-(n : ℝ) * gap))
        atTop (nhds 0) := by
    have hCpow : Tendsto (fun n : ℕ => C * rho ^ n) atTop (nhds 0) := by
      simpa using hpow.const_mul C
    refine hCpow.congr' ?_
    filter_upwards with n
    dsimp [rho]
    rw [← Real.exp_nat_mul]
    congr 1
    ring_nf
  have hratio_lt_one :
      ∀ᶠ n : ℕ in atTop,
        C * Real.exp (-(n : ℝ) * gap) < 1 :=
    hratio.eventually (Iio_mem_nhds zero_lt_one)
  have hupper_strict :
      ∀ᶠ n : ℕ in atTop,
        p n < Real.exp (-(n : ℝ) * lowerRate) := by
    filter_upwards [hCevent, hratio_lt_one] with n hn hratio_n
    have hexp_lower_pos : 0 < Real.exp (-(n : ℝ) * lowerRate) :=
      Real.exp_pos _
    have hCexp_lt :
        C * Real.exp (-(n : ℝ) * upperRate) <
          Real.exp (-(n : ℝ) * lowerRate) := by
      calc
        C * Real.exp (-(n : ℝ) * upperRate)
            =
            (C * Real.exp (-(n : ℝ) * gap)) *
              Real.exp (-(n : ℝ) * lowerRate) := by
              have hexp :
                  Real.exp (-(n : ℝ) * upperRate) =
                    Real.exp (-(n : ℝ) * gap) *
                      Real.exp (-(n : ℝ) * lowerRate) := by
                rw [← Real.exp_add]
                congr 1
                dsimp [gap]
                ring
              rw [hexp]
              ring
        _ < 1 * Real.exp (-(n : ℝ) * lowerRate) :=
            mul_lt_mul_of_pos_right hratio_n hexp_lower_pos
        _ = Real.exp (-(n : ℝ) * lowerRate) := by ring
    exact hn.2.trans_lt hCexp_lt
  rcases (hfreq.and_eventually hupper_strict).exists with ⟨n, hge, hlt⟩
  exact not_lt_of_ge hge hlt

end HasExpUpperBoundWithConst

namespace HasExpLowerBoundWithConst

theorem of_eventually_ge {p : ℕ → ℝ} {rate c : ℝ}
    (hc : 0 < c)
    (hbound : ∀ᶠ n : ℕ in atTop,
      c * Real.exp (-(n : ℝ) * rate) ≤ p n) :
    HasExpLowerBoundWithConst p rate :=
  ⟨c, hc, hbound⟩

theorem weaken_rate {p : ℕ → ℝ} {rate weakRate : ℝ}
    (h : HasExpLowerBoundWithConst p rate)
    (hrate : rate ≤ weakRate) :
    HasExpLowerBoundWithConst p weakRate := by
  rcases h with ⟨c, hcpos, hc⟩
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hc] with n hn
  have hexp :
      Real.exp (-(n : ℝ) * weakRate) ≤
        Real.exp (-(n : ℝ) * rate) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hrate
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact (mul_le_mul_of_nonneg_left hexp hcpos.le).trans hn

/--
Compose an exponential lower bound with the deterministic floor scale
`floor (k * g)`.  If `p_n` is lower bounded at rate `rate`, then
`p_{floor(k g)}` is lower bounded at every rate strictly above `g * rate`.
-/
theorem comp_nat_floor_mul_const
    {p : ℕ → ℝ} {rate g targetRate : ℝ}
    (h : HasExpLowerBoundWithConst p rate)
    (hg : 0 < g)
    (htarget : g * rate < targetRate) :
    HasExpLowerBoundWithConst
      (fun k : ℕ => p (Nat.floor ((k : ℝ) * g))) targetRate := by
  rcases h with ⟨c, hcpos, hbound⟩
  have hfloor_atTop :
      Tendsto (fun k : ℕ => Nat.floor ((k : ℝ) * g)) atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_floor_mul_const_atTop hg
  have hbound_floor :
      ∀ᶠ k : ℕ in atTop,
        c * Real.exp (-(Nat.floor ((k : ℝ) * g) : ℝ) * rate) ≤
          p (Nat.floor ((k : ℝ) * g)) :=
    hfloor_atTop.eventually hbound
  have hratio :
      Tendsto
        (fun k : ℕ => ((Nat.floor ((k : ℝ) * g) : ℝ) / (k : ℝ)) * rate)
        atTop (nhds (g * rate)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (AppliedModelingLib.Math.tendsto_nat_floor_mul_const_div_nat hg.le).mul_const rate
  have hratio_event :
      ∀ᶠ k : ℕ in atTop,
        ((Nat.floor ((k : ℝ) * g) : ℝ) / (k : ℝ)) * rate < targetRate :=
    hratio.eventually (Iio_mem_nhds htarget)
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hbound_floor, hratio_event, Filter.eventually_gt_atTop 0]
    with k hbound_k hratio_k hk
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hrate_lt :
      (Nat.floor ((k : ℝ) * g) : ℝ) * rate < (k : ℝ) * targetRate := by
    have hmul :=
      mul_lt_mul_of_pos_right hratio_k hk_pos
    field_simp [hk_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hexp_le :
      Real.exp (-(k : ℝ) * targetRate) ≤
        Real.exp (-(Nat.floor ((k : ℝ) * g) : ℝ) * rate) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact
    (mul_le_mul_of_nonneg_left hexp_le hcpos.le).trans hbound_k

theorem const_mul {p : ℕ → ℝ} {rate c : ℝ}
    (h : HasExpLowerBoundWithConst p rate) (hc : 0 < c) :
    HasExpLowerBoundWithConst (fun n => c * p n) rate := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨c * C, mul_pos hc hCpos, ?_⟩
  filter_upwards [hC] with n hn
  have hmain :
      c * (C * Real.exp (-(n : ℝ) * rate)) ≤ c * p n :=
    mul_le_mul_of_nonneg_left hn hc.le
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Products of two lower exponential bounds have the summed rate. -/
theorem mul {p q : ℕ → ℝ} {rateP rateQ : ℝ}
    (hp : HasExpLowerBoundWithConst p rateP)
    (hq : HasExpLowerBoundWithConst q rateQ) :
    HasExpLowerBoundWithConst
      (fun n : ℕ => p n * q n) (rateP + rateQ) := by
  rcases hp with ⟨cP, hcPpos, hp_bound⟩
  rcases hq with ⟨cQ, hcQpos, hq_bound⟩
  refine ⟨cP * cQ, mul_pos hcPpos hcQpos, ?_⟩
  filter_upwards [hp_bound, hq_bound] with n hp_n hq_n
  have hleftP_pos : 0 < cP * Real.exp (-(n : ℝ) * rateP) :=
    mul_pos hcPpos (Real.exp_pos _)
  have hp_nonneg : 0 ≤ p n :=
    (le_trans hleftP_pos.le hp_n)
  have hleftQ_pos : 0 < cQ * Real.exp (-(n : ℝ) * rateQ) :=
    mul_pos hcQpos (Real.exp_pos _)
  calc
    (cP * cQ) * Real.exp (-(n : ℝ) * (rateP + rateQ))
        =
        (cP * Real.exp (-(n : ℝ) * rateP)) *
          (cQ * Real.exp (-(n : ℝ) * rateQ)) := by
          have hexp :
              Real.exp (-(n : ℝ) * (rateP + rateQ)) =
                Real.exp (-(n : ℝ) * rateP) *
                  Real.exp (-(n : ℝ) * rateQ) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring
    _ ≤ p n * (cQ * Real.exp (-(n : ℝ) * rateQ)) :=
        mul_le_mul_of_nonneg_right hp_n hleftQ_pos.le
    _ ≤ p n * q n :=
        mul_le_mul_of_nonneg_left hq_n hp_nonneg

/--
An eventual polynomially corrected geometric lower bound implies every
exponential lower bound with any strictly slower rate.

This is the reusable final step after a finite-type or multinomial argument
has produced a lower bound like `c * r^n / (n+1)^d`.
-/
theorem of_eventually_geometric_div_polynomial_lower
    {p : ℕ → ℝ} {c r targetRate : ℝ} (d : ℕ)
    (hc : 0 < c) (hr_pos : 0 < r)
    (htarget : -Real.log r < targetRate)
    (hlower : ∀ᶠ n : ℕ in atTop,
      c * r ^ n / (((n.succ : ℕ) : ℝ) ^ d) ≤ p n) :
    HasExpLowerBoundWithConst p targetRate := by
  refine ⟨c, hc, ?_⟩
  let delta : ℝ := targetRate + Real.log r
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    linarith
  let rho : ℝ := Real.exp (-delta)
  have hrho_pos : 0 < rho := Real.exp_pos _
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have htend_succ_base :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ d) * rho ^ (m + 1))
        atTop (nhds 0) :=
    (tendsto_pow_const_mul_const_pow_of_lt_one d hrho_pos.le hrho_lt_one).comp
      (tendsto_add_atTop_nat 1)
  have htend_succ :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ d) * rho ^ m)
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun m : ℕ =>
            rho⁻¹ * ((((m + 1 : ℕ) : ℝ) ^ d) * rho ^ (m + 1)))
          atTop (nhds 0) := by
      simpa using htend_succ_base.const_mul rho⁻¹
    refine hmul.congr' ?_
    filter_upwards with m
    show rho⁻¹ * ((((m + 1 : ℕ) : ℝ) ^ d) * rho ^ (m + 1)) =
      (((m + 1 : ℕ) : ℝ) ^ d) * rho ^ m
    rw [pow_succ]
    field_simp [hrho_pos.ne']
  have hevent_small :
      ∀ᶠ n : ℕ in atTop,
        (((n.succ : ℕ) : ℝ) ^ d) * rho ^ n ≤ 1 := by
    have h := htend_succ.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h] with n hn
    simpa [Nat.succ_eq_add_one] using hn
  filter_upwards [hlower, hevent_small] with n hn hsmall
  have hden_pos : 0 < (((n.succ : ℕ) : ℝ) ^ d) := by
    positivity
  have hpow_r : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    calc
      r ^ n = (Real.exp (Real.log r)) ^ n := by
        rw [Real.exp_log hr_pos]
      _ = Real.exp ((n : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul]
  have hrho_pow : rho ^ n = Real.exp (-(n : ℝ) * delta) := by
    dsimp [rho]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio :
      (((n.succ : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * targetRate) ≤ r ^ n := by
    have hsmall_exp :
        (((n.succ : ℕ) : ℝ) ^ d) *
            Real.exp (-(n : ℝ) * delta) ≤ 1 := by
      simpa [hrho_pow] using hsmall
    have hrpow_pos : 0 < r ^ n := pow_pos hr_pos n
    have hmul := mul_le_mul_of_nonneg_right hsmall_exp hrpow_pos.le
    calc
      (((n.succ : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * targetRate)
          =
        (((n.succ : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * delta + (n : ℝ) * Real.log r) := by
            congr 1
            congr 1
            dsimp [delta]
            ring
      _ =
        (((n.succ : ℕ) : ℝ) ^ d) *
          (Real.exp (-(n : ℝ) * delta) *
            Real.exp ((n : ℝ) * Real.log r)) := by
            rw [Real.exp_add]
      _ =
        ((((n.succ : ℕ) : ℝ) ^ d) *
            Real.exp (-(n : ℝ) * delta)) * r ^ n := by
            rw [hpow_r]
            ring
      _ ≤ 1 * r ^ n := hmul
      _ = r ^ n := by ring
  have hmain :
      c * Real.exp (-(n : ℝ) * targetRate) ≤
        c * r ^ n / (((n.succ : ℕ) : ℝ) ^ d) := by
    have hdiv :
        Real.exp (-(n : ℝ) * targetRate) ≤
          r ^ n / (((n.succ : ℕ) : ℝ) ^ d) := by
      rw [le_div_iff₀ hden_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hratio
    have hmul := mul_le_mul_of_nonneg_left hdiv hc.le
    simpa [mul_div_assoc, mul_assoc] using hmul
  exact hmain.trans hn

end HasExpLowerBoundWithConst

/--
If a positive sequence has exponential upper bounds at every rate below `rate`
and exponential lower bounds at every rate above `rate`, then its paper-style
normalized log decay converges to `rate`.
-/
theorem hasExponentialRate_of_expUpperLowerBounds
    {p : ℕ → ℝ} {rate : ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < p n)
    (hupper : ∀ targetRate, targetRate < rate →
      HasExpUpperBoundWithConst p targetRate)
    (hlower : ∀ targetRate, rate < targetRate →
      HasExpLowerBoundWithConst p targetRate) :
    HasExponentialRate p rate := by
  rw [HasExponentialRate]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let mid : ℝ := (a + rate) / 2
    have ha_mid : a < mid := by dsimp [mid]; linarith
    have hmid_rate : mid < rate := by dsimp [mid]; linarith
    rcases hupper mid hmid_rate with ⟨C, hCpos, hCevent⟩
    have hdiv_tendsto :
        Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
    have hdelta : 0 < mid - a := by linarith
    have hdiv_event : ∀ᶠ n : ℕ in atTop,
        Real.log C / (n : ℝ) < mid - a :=
      hdiv_tendsto.eventually_lt_const hdelta
    filter_upwards [hpos, hCevent, hdiv_event, eventually_gt_atTop 0]
      with n hp_pos hC hdiv hn
    have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog_le :
        Real.log (p n) ≤ Real.log C + (-(n : ℝ) * mid) := by
      have hlog_bound := Real.log_le_log hp_pos hC.2
      rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne',
        Real.log_exp] at hlog_bound
      exact hlog_bound
    have hdiv_le :
        Real.log (p n) / (n : ℝ) ≤
          (Real.log C + (-(n : ℝ) * mid)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hlog_le hnreal_pos.le
    have hupper_norm :
        -((Real.log C + (-(n : ℝ) * mid)) / (n : ℝ)) =
          mid - Real.log C / (n : ℝ) := by
      field_simp [hnreal_pos.ne']
      ring
    have hlogDecay_eq :
        logDecay p n = -(Real.log (p n) / (n : ℝ)) := by
      dsimp [logDecay]
      field_simp [hnreal_pos.ne']
    have hdecay_ge :
        mid - Real.log C / (n : ℝ) ≤ logDecay p n := by
      rw [← hupper_norm, hlogDecay_eq]
      exact neg_le_neg hdiv_le
    exact lt_of_lt_of_le (by linarith) hdecay_ge
  · intro b hb
    let mid : ℝ := (rate + b) / 2
    have hrate_mid : rate < mid := by dsimp [mid]; linarith
    have hmid_b : mid < b := by dsimp [mid]; linarith
    rcases hlower mid hrate_mid with ⟨c, hcpos, hcevent⟩
    have hdiv_tendsto :
        Tendsto (fun n : ℕ => Real.log c / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log c)
    have hdelta : 0 < b - mid := by linarith
    have hdiv_event : ∀ᶠ n : ℕ in atTop,
        -(Real.log c / (n : ℝ)) < b - mid := by
      have hneg_tendsto :
          Tendsto (fun n : ℕ => -(Real.log c / (n : ℝ)))
            atTop (nhds 0) := by
        simpa using hdiv_tendsto.neg
      exact hneg_tendsto.eventually_lt_const hdelta
    filter_upwards [hpos, hcevent, hdiv_event, eventually_gt_atTop 0]
      with n hp_pos hc hdiv hn
    have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlower_pos : 0 < c * Real.exp (-(n : ℝ) * mid) :=
      mul_pos hcpos (Real.exp_pos _)
    have hlog_lower :
        Real.log c + (-(n : ℝ) * mid) ≤ Real.log (p n) := by
      have hlog_bound := Real.log_le_log hlower_pos hc
      rw [Real.log_mul hcpos.ne' (Real.exp_pos _).ne',
        Real.log_exp] at hlog_bound
      exact hlog_bound
    have hdiv_le :
        (Real.log c + (-(n : ℝ) * mid)) / (n : ℝ) ≤
          Real.log (p n) / (n : ℝ) :=
      div_le_div_of_nonneg_right hlog_lower hnreal_pos.le
    have hlower_norm :
        -((Real.log c + (-(n : ℝ) * mid)) / (n : ℝ)) =
          mid - Real.log c / (n : ℝ) := by
      field_simp [hnreal_pos.ne']
      ring
    have hlogDecay_eq :
        logDecay p n = -(Real.log (p n) / (n : ℝ)) := by
      dsimp [logDecay]
      field_simp [hnreal_pos.ne']
    have hdecay_le :
        logDecay p n ≤ mid - Real.log c / (n : ℝ) := by
      rw [hlogDecay_eq, ← hlower_norm]
      exact neg_le_neg hdiv_le
    exact lt_of_le_of_lt hdecay_le (by linarith)

/--
A positive sequence has exponential rate zero when it is eventually bounded
above by a fixed positive constant and has exponential lower bounds at every
positive rate.

This is the sequence-level skeleton behind many "no exponentially small loss"
arguments: the upper side at negative target rates follows from the constant
bound, while the lower side is supplied by local positive-mass witnesses.
-/
theorem hasExponentialRate_zero_of_eventually_le_const_and_expLowerBounds
    {p : ℕ → ℝ} {B : ℝ}
    (hBpos : 0 < B)
    (hpos : ∀ᶠ n in atTop, 0 < p n)
    (hupper_const : ∀ᶠ n in atTop, p n ≤ B)
    (hlower : ∀ targetRate : ℝ, 0 < targetRate →
      HasExpLowerBoundWithConst p targetRate) :
    HasExponentialRate p 0 := by
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    refine HasExpUpperBoundWithConst.of_eventually_le
      (C := B) hBpos ?_
    filter_upwards [hpos, hupper_const] with n hp_pos hp_le
    refine ⟨hp_pos.le, hp_le.trans ?_⟩
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp (-(n : ℝ) * targetRate) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    exact le_mul_of_one_le_right hBpos.le hexp_ge_one
  · intro targetRate htarget
    exact hlower targetRate htarget

/--
Compose an exact exponential rate with the deterministic floor scale
`floor (k * g)`. If `p_n` has rate `rate`, then `p_{floor(k g)}` has rate
`g * rate`.
-/
theorem HasExponentialRate.comp_nat_floor_mul_const
    {p : ℕ → ℝ} {rate g : ℝ}
    (h : HasExponentialRate p rate) (hg : 0 < g) :
    HasExponentialRate
      (fun k : ℕ => p (Nat.floor ((k : ℝ) * g)))
      (g * rate) := by
  rw [HasExponentialRate] at h ⊢
  let floorCount : ℕ → ℕ := fun k => Nat.floor ((k : ℝ) * g)
  have hfloor_atTop : Tendsto floorCount atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_floor_mul_const_atTop hg
  have hcomp :
      Tendsto (fun k : ℕ => logDecay p (floorCount k)) atTop
        (nhds rate) :=
    h.comp hfloor_atTop
  have hratio :
      Tendsto
        (fun k : ℕ => ((floorCount k : ℕ) : ℝ) / (k : ℝ))
        atTop (nhds g) := by
    simpa [floorCount] using
      AppliedModelingLib.Math.tendsto_nat_floor_mul_const_div_nat hg.le
  have hmul :
      Tendsto
        (fun k : ℕ =>
          (((floorCount k : ℕ) : ℝ) / (k : ℝ)) *
            logDecay p (floorCount k))
        atTop (nhds (g * rate)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hratio.mul hcomp
  refine hmul.congr' ?_
  have hfloor_pos_event : ∀ᶠ k : ℕ in atTop, 0 < floorCount k :=
    hfloor_atTop.eventually (eventually_gt_atTop 0)
  filter_upwards [eventually_gt_atTop 0, hfloor_pos_event] with k hk hfloor_pos
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfloor_ne_real : ((floorCount k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hfloor_pos)
  unfold logDecay
  field_simp [hk_pos.ne', hfloor_ne_real]
  ring

namespace ExponentialRateCertificate

/--
Build an exact exponential-rate certificate from a positive exact rate and
eventual nonnegativity.
-/
theorem of_has_rate_of_eventually_nonneg_of_pos_rate
    {p : ℕ → ℝ} {rate : ℝ}
    (h : HasExponentialRate p rate) (hrate : 0 < rate)
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ p n) :
    ExponentialRateCertificate p rate where
  eventually_pos :=
    h.eventually_pos_of_eventually_nonneg_of_pos_rate hrate hnonneg
  has_rate := h

/--
Eventually equal sequences have the same exact exponential-rate certificate.
-/
theorem congr
    {p q : ℕ → ℝ} {rate : ℝ}
    (heq : ∀ᶠ n in atTop, p n = q n)
    (h : ExponentialRateCertificate q rate) :
    ExponentialRateCertificate p rate where
  eventually_pos := by
    filter_upwards [heq, h.eventually_pos] with n hpq hqpos
    simpa [hpq] using hqpos
  has_rate :=
    HasExponentialRate.congr (heq.mono fun _n hpq => hpq.symm) h.has_rate

/--
Adding a term that is eventually exactly zero preserves an exact
exponential-rate certificate.  This is the valid residual-erasure form; a
merely zero-rate residual is not negligible for positive-rate existence.
-/
theorem congr_add_eventually_zero
    {target selected extra : ℕ → ℝ} {rate : ℝ}
    (hdecomp : ∀ᶠ n in atTop, target n = selected n + extra n)
    (hextra_zero : ∀ᶠ n in atTop, extra n = 0)
    (h : ExponentialRateCertificate selected rate) :
    ExponentialRateCertificate target rate := by
  refine congr ?_ h
  filter_upwards [hdecomp, hextra_zero] with n hn hzero
  rw [hn, hzero, add_zero]

/--
Existential positive-rate form of `congr_add_eventually_zero`.
-/
theorem exists_pos_of_eventually_eq_add_eventually_zero
    {target selected extra : ℕ → ℝ}
    (hdecomp : ∀ᶠ n in atTop, target n = selected n + extra n)
    (hextra_zero : ∀ᶠ n in atTop, extra n = 0)
    (hselected :
      ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate selected rate) :
    ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate target rate := by
  rcases hselected with ⟨rate, hrate, hcert⟩
  exact ⟨rate, hrate, congr_add_eventually_zero hdecomp hextra_zero hcert⟩

/--
Finite families of exact exponential-rate certificates give uniform
normalized-log convergence over the finite component index set.
-/
theorem uniform_logDecay_fintype
    {ι : Type*} [Fintype ι] {p : ι → ℕ → ℝ} {rate : ι → ℝ}
    (h : ∀ i : ι, ExponentialRateCertificate (p i) (rate i)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ i : ι, |logDecay (p i) n - rate i| ≤ ε :=
  HasExponentialRate.uniform_logDecay_fintype fun i => (h i).has_rate

/--
Compose an exact exponential-rate certificate with the deterministic floor
scale `floor (k * g)`.
-/
theorem comp_nat_floor_mul_const
    {p : ℕ → ℝ} {rate g : ℝ}
    (h : ExponentialRateCertificate p rate) (hg : 0 < g) :
    ExponentialRateCertificate
      (fun k : ℕ => p (Nat.floor ((k : ℝ) * g)))
      (g * rate) := by
  let floorCount : ℕ → ℕ := fun k => Nat.floor ((k : ℝ) * g)
  have hfloor_atTop : Tendsto floorCount atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_floor_mul_const_atTop hg
  refine
    { eventually_pos := ?_
      has_rate := h.has_rate.comp_nat_floor_mul_const hg }
  exact hfloor_atTop.eventually h.eventually_pos

/--
An exact exponential-rate certificate gives an eventual exponential upper
bound at every strictly smaller rate. This is the standard bridge from
`-log p_n / n -> r` to `p_n <= exp(-n * r')` for `r' < r`.
-/
theorem hasExpUpperBoundWithConst_of_lt
    {p : ℕ → ℝ} {rate targetRate : ℝ}
    (h : ExponentialRateCertificate p rate)
    (htarget : targetRate < rate) :
    HasExpUpperBoundWithConst p targetRate := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hdecay : ∀ᶠ n in atTop, targetRate ≤ logDecay p n :=
    h.has_rate.eventually_const_le htarget
  filter_upwards [h.eventually_pos, hdecay, eventually_gt_atTop 0]
    with n hpos hdecay_n hnpos
  refine ⟨hpos.le, ?_⟩
  have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmul :
      (n : ℝ) * targetRate ≤ (n : ℝ) * logDecay p n :=
    mul_le_mul_of_nonneg_left hdecay_n hnreal_pos.le
  have hlogdecay :
      (n : ℝ) * logDecay p n = -Real.log (p n) := by
    dsimp [logDecay]
    field_simp [(ne_of_gt hnreal_pos)]
  have hlog : Real.log (p n) ≤ -(n : ℝ) * targetRate := by
    linarith
  have hple :
      p n ≤ Real.exp (-(n : ℝ) * targetRate) :=
    (Real.log_le_iff_le_exp hpos).1 hlog
  simpa using hple

/--
An exact exponential-rate certificate gives an eventual exponential lower
bound at every strictly larger rate: if `-log p_n / n -> r`, then
`exp(-n * r') <= p_n` eventually for `r < r'`.
-/
theorem hasExpLowerBoundWithConst_of_gt
    {p : ℕ → ℝ} {rate targetRate : ℝ}
    (h : ExponentialRateCertificate p rate)
    (htarget : rate < targetRate) :
    HasExpLowerBoundWithConst p targetRate := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hdecay : ∀ᶠ n in atTop, logDecay p n ≤ targetRate :=
    h.has_rate.eventually_le_const htarget
  filter_upwards [h.eventually_pos, hdecay, eventually_gt_atTop 0]
    with n hpos hdecay_n hnpos
  have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmul :
      (n : ℝ) * logDecay p n ≤ (n : ℝ) * targetRate :=
    mul_le_mul_of_nonneg_left hdecay_n hnreal_pos.le
  have hlogdecay :
      (n : ℝ) * logDecay p n = -Real.log (p n) := by
    dsimp [logDecay]
    field_simp [(ne_of_gt hnreal_pos)]
  have hlog : -(n : ℝ) * targetRate ≤ Real.log (p n) := by
    linarith
  have hple :
      Real.exp (-(n : ℝ) * targetRate) ≤ p n :=
    (Real.le_log_iff_exp_le hpos).1 hlog
  simpa using hple

/--
An exact exponential-rate certificate at a strictly positive rate implies the
event probabilities converge to zero.
-/
theorem tendsto_zero_of_pos_rate
    {p : ℕ → ℝ} {rate : ℝ}
    (h : ExponentialRateCertificate p rate) (hrate : 0 < rate) :
    Tendsto p atTop (nhds 0) := by
  have hhalf_lt : rate / 2 < rate := by linarith
  have hhalf_pos : 0 < rate / 2 := by linarith
  exact
    (h.hasExpUpperBoundWithConst_of_lt hhalf_lt).tendsto_zero_of_pos_rate
      hhalf_pos

/--
If `1 - P_n` has an exact positive exponential-rate certificate, then `P_n`
tends to one.
-/
theorem tendsto_one_of_one_sub_pos_rate
    {P : ℕ → ℝ} {rate : ℝ}
    (h : ExponentialRateCertificate (fun n : ℕ => 1 - P n) rate)
    (hrate : 0 < rate) :
    Tendsto P atTop (nhds 1) := by
  have hzero : Tendsto (fun n : ℕ => 1 - P n) atTop (nhds 0) :=
    h.tendsto_zero_of_pos_rate hrate
  have hone_sub :
      Tendsto (fun n : ℕ => 1 - (1 - P n)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hzero
  simpa using hone_sub

/--
A sequence that is frequently bounded below by a fixed positive constant cannot
carry an exact exponential-rate certificate at a positive rate.
-/
theorem not_of_frequently_ge_pos
    {p : ℕ → ℝ} {rate ε : ℝ}
    (hrate : 0 < rate) (hε : 0 < ε)
    (hfreq : ∃ᶠ n in atTop, ε ≤ p n) :
    ¬ ExponentialRateCertificate p rate := by
  intro hcert
  have hhalf_lt : rate / 2 < rate := by linarith
  have hhalf_pos : 0 < rate / 2 := by linarith
  exact
    HasExpUpperBoundWithConst.not_of_frequently_ge_pos hhalf_pos hε hfreq
      (hcert.hasExpUpperBoundWithConst_of_lt hhalf_lt)

/--
A sequence that is frequently at least `exp (-n * lowerRate)` cannot carry an
exact exponential-rate certificate at any strictly larger positive rate.
-/
theorem not_of_frequently_ge_exp_neg_mul
    {p : ℕ → ℝ} {rate lowerRate : ℝ}
    (hlower_lt : lowerRate < rate)
    (hfreq : ∃ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * lowerRate) ≤ p n) :
    ¬ ExponentialRateCertificate p rate := by
  intro hcert
  let upperRate : ℝ := (lowerRate + rate) / 2
  have hlower_upper : lowerRate < upperRate := by
    dsimp [upperRate]
    linarith
  have hupper_rate : upperRate < rate := by
    dsimp [upperRate]
    linarith
  exact
    HasExpUpperBoundWithConst.not_of_frequently_ge_exp_neg_mul
      hlower_upper hfreq (hcert.hasExpUpperBoundWithConst_of_lt hupper_rate)

/--
Subexponential lower hits rule out every positive exact exponential-rate
certificate.  This is the certificate-level shape used when a continuum model
can make pairwise errors at least `exp (-δ n)` infinitely often for every
`δ > 0`.
-/
theorem not_of_frequently_ge_subexponential
    {p : ℕ → ℝ} {rate : ℝ}
    (hrate : 0 < rate)
    (hfreq : ∀ δ : ℝ, 0 < δ →
      ∃ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ) * δ) ≤ p n) :
    ¬ ExponentialRateCertificate p rate := by
  have hhalf_pos : 0 < rate / 2 := by linarith
  have hhalf_lt : rate / 2 < rate := by linarith
  exact
    not_of_frequently_ge_exp_neg_mul hhalf_lt
      (hfreq (rate / 2) hhalf_pos)

/--
An exact zero exponential rate rules out any positive exact exponential-rate
certificate for the same sequence.
-/
theorem not_of_hasExponentialRate_zero
    {p : ℕ → ℝ} {rate : ℝ}
    (hrate : 0 < rate)
    (hzero : HasExponentialRate p 0) :
    ¬ ExponentialRateCertificate p rate := by
  intro hcert
  have hrate_eq_zero : rate = 0 :=
    HasExponentialRate.unique hcert.has_rate hzero
  linarith

/--
Logical packaging for source statements of the form "a structural property
holds iff the error sequence has some positive exact exponential rate."  The
forward direction supplies the positive-rate certificate; the reverse direction
is discharged by proving exact zero rate when the structural property fails.
-/
theorem exists_pos_rate_iff_of_forward_and_zero_reverse
    {p : ℕ → ℝ} {P : Prop}
    (hforward : P → ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate p rate)
    (hzero_reverse : ¬ P → HasExponentialRate p 0) :
    P ↔ ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate p rate := by
  constructor
  · exact hforward
  · intro hpos
    by_contra hnot
    rcases hpos with ⟨rate, hrate, hcert⟩
    exact not_of_hasExponentialRate_zero hrate (hzero_reverse hnot) hcert

/--
Logical packaging for source statements where the reverse branch rules out
positive exact exponential-rate certificates directly, without first proving an
exact zero-rate theorem.  This is the form used by subexponential lower-bound
arguments.
-/
theorem exists_pos_rate_iff_of_forward_and_no_positive_reverse
    {p : ℕ → ℝ} {P : Prop}
    (hforward : P → ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate p rate)
    (hno_positive_reverse :
      ¬ P → ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate p rate) :
    P ↔ ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate p rate := by
  constructor
  · exact hforward
  · intro hpos
    by_contra hnot
    rcases hpos with ⟨rate, hrate, hcert⟩
    exact hno_positive_reverse hnot rate hrate hcert

/--
If a certified exact-rate sequence is eventually bounded above at exponential
rate `upperRate`, then that upper-bound rate cannot exceed the exact rate.
-/
theorem rate_ge_of_expUpperBoundWithConst
    {p : ℕ → ℝ} {rate upperRate : ℝ}
    (h : ExponentialRateCertificate p rate)
    (hupper : HasExpUpperBoundWithConst p upperRate) :
    upperRate ≤ rate := by
  rcases hupper with ⟨C, hCpos, hCevent⟩
  have hdiv_tendsto :
      Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
  have hleft_tendsto :
      Tendsto (fun n : ℕ => upperRate - Real.log C / (n : ℝ))
        atTop (nhds upperRate) := by
    simpa using tendsto_const_nhds.sub hdiv_tendsto
  refine le_of_tendsto_of_tendsto hleft_tendsto h.has_rate ?_
  filter_upwards [h.eventually_pos, hCevent, eventually_gt_atTop 0]
    with n hp_pos hC hn
  have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog_le :
      Real.log (p n) ≤ Real.log C + (-(n : ℝ) * upperRate) := by
    have hlog_bound := Real.log_le_log hp_pos hC.2
    rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne',
      Real.log_exp] at hlog_bound
    exact hlog_bound
  have hdiv_le :
      Real.log (p n) / (n : ℝ) ≤
        (Real.log C + (-(n : ℝ) * upperRate)) / (n : ℝ) :=
    div_le_div_of_nonneg_right hlog_le hnreal_pos.le
  have hupper_norm :
      -((Real.log C + (-(n : ℝ) * upperRate)) / (n : ℝ)) =
        upperRate - Real.log C / (n : ℝ) := by
    field_simp [hnreal_pos.ne']
    ring
  have hlogDecay_eq :
      logDecay p n = -(Real.log (p n) / (n : ℝ)) := by
    dsimp [logDecay]
    field_simp [hnreal_pos.ne']
  rw [← hupper_norm, hlogDecay_eq]
  exact neg_le_neg hdiv_le

/--
Build an exact exponential-rate certificate from upper bounds at every
strictly smaller rate and lower bounds at every strictly larger rate.
-/
theorem of_expUpperLowerBounds
    {p : ℕ → ℝ} {rate : ℝ}
    (hupper : ∀ targetRate, targetRate < rate →
      HasExpUpperBoundWithConst p targetRate)
    (hlower : ∀ targetRate, rate < targetRate →
      HasExpLowerBoundWithConst p targetRate) :
    ExponentialRateCertificate p rate := by
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    rcases hlower (rate + 1) (by linarith) with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    have hleft_pos : 0 < c * Real.exp (-(n : ℝ) * (rate + 1)) :=
      mul_pos hcpos (Real.exp_pos _)
    exact lt_of_lt_of_le hleft_pos hn
  exact
    { eventually_pos := hpos
      has_rate := hasExponentialRate_of_expUpperLowerBounds
        hpos hupper hlower }

/--
Constant-factor equivalent error probabilities have the same exact
exponential rate.  This packages the common large-deviation step where a
paper replaces one event probability by another up to fixed positive factors,
for example after symmetrizing pairwise comparison errors.
-/
theorem of_eventually_const_sandwich
    {p q : ℕ → ℝ} {rate lower upper : ℝ}
    (h : ExponentialRateCertificate q rate)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsandwich : ∀ᶠ n in atTop,
      lower * q n ≤ p n ∧ p n ≤ upper * q n) :
    ExponentialRateCertificate p rate := by
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    filter_upwards [h.eventually_pos, hsandwich] with n hqpos hsandwich_n
    exact lt_of_lt_of_le (mul_pos hlower hqpos) hsandwich_n.1
  refine
    { eventually_pos := hpos
      has_rate := ?_ }
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    rcases h.hasExpUpperBoundWithConst_of_lt htarget with
      ⟨C, hCpos, hCevent⟩
    refine HasExpUpperBoundWithConst.of_eventually_le
      (C := (upper + 1) * C) (mul_pos (by linarith) hCpos) ?_
    filter_upwards [hpos, hsandwich, hCevent] with n hp_pos hsandwich_n hC_n
    refine ⟨hp_pos.le, ?_⟩
    have hq_bound :
        upper * q n ≤ upper * (C * Real.exp (-(n : ℝ) * targetRate)) :=
      mul_le_mul_of_nonneg_left hC_n.2 hupper.le
    have hcoef :
        upper * C ≤ (upper + 1) * C :=
      mul_le_mul_of_nonneg_right (by linarith) hCpos.le
    calc
      p n ≤ upper * q n := hsandwich_n.2
      _ ≤ upper * (C * Real.exp (-(n : ℝ) * targetRate)) := hq_bound
      _ = (upper * C) * Real.exp (-(n : ℝ) * targetRate) := by ring
      _ ≤ ((upper + 1) * C) * Real.exp (-(n : ℝ) * targetRate) := by
        exact mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
  · intro targetRate htarget
    rcases h.hasExpLowerBoundWithConst_of_gt htarget with
      ⟨c, hcpos, hcevent⟩
    refine HasExpLowerBoundWithConst.of_eventually_ge
      (c := lower * c) (mul_pos hlower hcpos) ?_
    filter_upwards [hsandwich, hcevent] with n hsandwich_n hc_n
    calc
      (lower * c) * Real.exp (-(n : ℝ) * targetRate)
          = lower * (c * Real.exp (-(n : ℝ) * targetRate)) := by ring
      _ ≤ lower * q n := mul_le_mul_of_nonneg_left hc_n hlower.le
      _ ≤ p n := hsandwich_n.1

end ExponentialRateCertificate

/--
Zero-rate lower-bound transfer. If a positive zero-rate obstruction sequence
is eventually bounded above by a target sequence, and the target sequence has
a fixed positive constant upper bound, then the target sequence also has exact
exponential rate zero.

This is the sequence-level bridge used to lift local positive-mass
obstructions to larger error integrals.
-/
theorem hasExponentialRate_zero_of_eventually_le_const_of_zero_rate_minorant
    {minorant target : ℕ → ℝ} {B : ℝ}
    (hBpos : 0 < B)
    (hminorant_pos : ∀ᶠ n in atTop, 0 < minorant n)
    (hminorant_zero : HasExponentialRate minorant 0)
    (hminorant_le_target : ∀ᶠ n in atTop, minorant n ≤ target n)
    (htarget_upper_const : ∀ᶠ n in atTop, target n ≤ B) :
    HasExponentialRate target 0 := by
  have htarget_pos : ∀ᶠ n in atTop, 0 < target n := by
    filter_upwards [hminorant_pos, hminorant_le_target] with n hpos hle
    exact hpos.trans_le hle
  refine
    hasExponentialRate_zero_of_eventually_le_const_and_expLowerBounds
      hBpos htarget_pos htarget_upper_const ?_
  intro targetRate htargetRate
  have hminorant_cert : ExponentialRateCertificate minorant 0 :=
    ⟨hminorant_pos, hminorant_zero⟩
  rcases hminorant_cert.hasExpLowerBoundWithConst_of_gt htargetRate with
    ⟨c, hcpos, hc⟩
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hc, hminorant_le_target] with n hcn hle
  exact hcn.trans hle

theorem finite_weighted_sum_hasExpUpperBoundWithConst
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hbound : ∀ i, HasExpUpperBoundWithConst (p i) (rate i))
    (hrate : ∀ i, targetRate ≤ rate i) :
    HasExpUpperBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate := by
  classical
  choose C hCpos hCevent using hbound
  let Csum : ℝ := 1 + ∑ i : ι, weight i * C i
  have hsum_nonneg : 0 ≤ ∑ i : ι, weight i * C i := by
    exact Finset.sum_nonneg (by
      intro i _
      exact mul_nonneg (hweight i) (hCpos i).le)
  have hCsum_pos : 0 < Csum := by
    dsimp [Csum]
    linarith
  refine ⟨Csum, hCsum_pos, ?_⟩
  have hall :
      ∀ᶠ n in atTop,
        ∀ i : ι, 0 ≤ p i n ∧
          p i n ≤ C i * Real.exp (-(n : ℝ) * rate i) := by
    exact eventually_all.2 hCevent
  filter_upwards [hall] with n hn
  have hnonneg :
      0 ≤ ∑ i : ι, weight i * p i n := by
    exact Finset.sum_nonneg (by
      intro i _
      exact mul_nonneg (hweight i) (hn i).1)
  refine ⟨hnonneg, ?_⟩
  have hterm :
      ∀ i : ι,
        weight i * p i n ≤
          (weight i * C i) *
            Real.exp (-(n : ℝ) * targetRate) := by
    intro i
    have hmul :
        weight i * p i n ≤
          weight i * (C i * Real.exp (-(n : ℝ) * rate i)) :=
      mul_le_mul_of_nonneg_left (hn i).2 (hweight i)
    have hexp :
        Real.exp (-(n : ℝ) * rate i) ≤
          Real.exp (-(n : ℝ) * targetRate) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hrate i)
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hcoef_nonneg : 0 ≤ weight i * C i :=
      mul_nonneg (hweight i) (hCpos i).le
    calc
      weight i * p i n ≤
          weight i * (C i * Real.exp (-(n : ℝ) * rate i)) := hmul
      _ = (weight i * C i) * Real.exp (-(n : ℝ) * rate i) := by ring
      _ ≤ (weight i * C i) * Real.exp (-(n : ℝ) * targetRate) := by
        exact mul_le_mul_of_nonneg_left hexp hcoef_nonneg
  calc
    ∑ i : ι, weight i * p i n ≤
        ∑ i : ι, (weight i * C i) *
          Real.exp (-(n : ℝ) * targetRate) := by
      exact Finset.sum_le_sum (by intro i _; exact hterm i)
    _ = (∑ i : ι, weight i * C i) *
          Real.exp (-(n : ℝ) * targetRate) := by
      rw [Finset.sum_mul]
    _ ≤ Csum * Real.exp (-(n : ℝ) * targetRate) := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [Csum]; linarith) (Real.exp_pos _).le

/--
If each component in a finite nonempty weighted error sum has some strictly
positive exponential upper-bound rate, then the whole weighted sum has a
strictly positive exponential upper-bound rate.
-/
theorem finite_weighted_sum_exists_pos_expUpperBoundWithConst
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hbound :
      ∀ i : ι,
        ∃ rate : ℝ,
          0 < rate ∧ HasExpUpperBoundWithConst (p i) rate) :
    ∃ targetRate : ℝ,
      0 < targetRate ∧
        HasExpUpperBoundWithConst
          (fun n => ∑ i : ι, weight i * p i n) targetRate := by
  classical
  choose rate hrate_pos hrate_bound using hbound
  let minRate : ℝ := (Finset.univ : Finset ι).inf' Finset.univ_nonempty rate
  have hmin_pos : 0 < minRate := by
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hrate_pos i
  let targetRate : ℝ := minRate / 2
  have htarget_pos : 0 < targetRate := by
    dsimp [targetRate]
    linarith
  have htarget_le : ∀ i : ι, targetRate ≤ rate i := by
    intro i
    have hmin_le : minRate ≤ rate i := by
      dsimp [minRate]
      exact Finset.inf'_le rate (Finset.mem_univ i)
    dsimp [targetRate]
    linarith
  exact
    ⟨targetRate, htarget_pos,
      finite_weighted_sum_hasExpUpperBoundWithConst
        (p := p) (weight := weight) (rate := rate)
        hweight hrate_bound htarget_le⟩

theorem finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hcert : ∀ i, ExponentialRateCertificate (p i) (rate i))
    (hrate : ∀ i, targetRate < rate i) :
    HasExpUpperBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate :=
  finite_weighted_sum_hasExpUpperBoundWithConst
    (rate := fun _ => targetRate)
    hweight
    (fun i => (hcert i).hasExpUpperBoundWithConst_of_lt (hrate i))
    (fun _ => le_rfl)

/--
If a certified exact-rate sequence is eventually bounded by a finite sum of
certified exact-rate components, then at least one component has rate no larger
than the ambient sequence. This is the rate-theoretic core behind finite
union-bound dominance arguments.
-/
theorem exists_component_rate_le_of_eventually_le_finite_sum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ → ℝ} {q : ι → ℕ → ℝ} {rateP : ℝ} {rate : ι → ℝ}
    (hp : ExponentialRateCertificate p rateP)
    (hq : ∀ i : ι, ExponentialRateCertificate (q i) (rate i))
    (hupper : ∀ᶠ n in atTop, p n ≤ ∑ i : ι, q i n) :
    ∃ i : ι, rate i ≤ rateP := by
  classical
  by_contra hnone
  have hlt : ∀ i : ι, rateP < rate i := by
    intro i
    exact not_le.mp (fun hi => hnone ⟨i, hi⟩)
  let minRate : ℝ := (Finset.univ : Finset ι).inf' Finset.univ_nonempty rate
  have hrateP_lt_min : rateP < minRate := by
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hlt i
  let targetRate : ℝ := (rateP + minRate) / 2
  have hrateP_lt_target : rateP < targetRate := by
    dsimp [targetRate]
    linarith
  have htarget_lt_min : targetRate < minRate := by
    dsimp [targetRate]
    linarith
  have htarget_lt_rate : ∀ i : ι, targetRate < rate i := by
    intro i
    have hmin_le : minRate ≤ rate i := by
      dsimp [minRate]
      exact Finset.inf'_le rate (Finset.mem_univ i)
    exact lt_of_lt_of_le htarget_lt_min hmin_le
  have hsum_upper :
      HasExpUpperBoundWithConst
        (fun n : ℕ => ∑ i : ι, q i n) targetRate := by
    simpa using
      finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
        (ι := ι) (p := q) (weight := fun _ : ι => (1 : ℝ))
        (rate := rate) (targetRate := targetRate)
        (fun _ => by norm_num)
        hq htarget_lt_rate
  have hp_upper :
      HasExpUpperBoundWithConst p targetRate := by
    rcases hsum_upper with ⟨C, hCpos, hCevent⟩
    refine HasExpUpperBoundWithConst.of_eventually_le hCpos ?_
    filter_upwards [hp.eventually_pos, hupper, hCevent] with n hp_pos hp_le hC_n
    exact ⟨hp_pos.le, hp_le.trans hC_n.2⟩
  have htarget_le_rateP := hp.rate_ge_of_expUpperBoundWithConst hp_upper
  linarith

/--
Exact rate for an event probability squeezed between one certified component
and the finite sum of certified components.  This packages the common
large-deviation pattern after an event-inclusion or union-bound reduction.
-/
theorem hasExponentialRate_of_event_between_component_and_finite_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ → ℝ} {q : ι → ℕ → ℝ} {rate : ι → ℝ}
    (hcert : ∀ i : ι, ExponentialRateCertificate (q i) (rate i))
    (iMin : ι)
    (hmin : ∀ i : ι, rate iMin ≤ rate i)
    (hupper : ∀ᶠ n in atTop, 0 ≤ p n ∧ p n ≤ ∑ i : ι, q i n)
    (hlower : ∀ᶠ n in atTop, q iMin n ≤ p n) :
    HasExponentialRate p (rate iMin) := by
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    rcases (hcert iMin).hasExpLowerBoundWithConst_of_gt
        (by linarith : rate iMin < rate iMin + 1) with
      ⟨c, hcpos, hc⟩
    filter_upwards [hc, hlower] with n hc_n hlower_n
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (rate iMin + 1))))
      (hc_n.trans hlower_n)
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    have hsum_upper :
        HasExpUpperBoundWithConst
          (fun n : ℕ => ∑ i : ι, q i n) targetRate := by
      simpa using
        finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
          (ι := ι) (p := q) (weight := fun _ : ι => (1 : ℝ))
          (rate := rate) (targetRate := targetRate)
          (fun _ => by norm_num)
          hcert
          (fun i => lt_of_lt_of_le htarget (hmin i))
    rcases hsum_upper with ⟨C, hCpos, hCevent⟩
    refine HasExpUpperBoundWithConst.of_eventually_le hCpos ?_
    filter_upwards [hupper, hCevent] with n hp hC_n
    exact ⟨hp.1, hp.2.trans hC_n.2⟩
  · intro targetRate htarget
    rcases (hcert iMin).hasExpLowerBoundWithConst_of_gt htarget with
      ⟨c, hcpos, hc⟩
    refine HasExpLowerBoundWithConst.of_eventually_ge hcpos ?_
    filter_upwards [hc, hlower] with n hc_n hlower_n
    exact hc_n.trans hlower_n

/--
If every component in a finite weighted sum is eventually zero, then the
weighted sum itself is eventually zero.
-/
theorem finite_weighted_sum_eventually_zero
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hzero : ∀ i : ι, ∀ᶠ n in atTop, p i n = 0) :
    ∀ᶠ n in atTop, (∑ i : ι, weight i * p i n) = 0 := by
  classical
  have hall : ∀ᶠ n in atTop, ∀ i : ι, p i n = 0 :=
    eventually_all.2 hzero
  filter_upwards [hall] with n hn
  simp [hn]

/--
A finite weighted sum whose components are eventually zero has an exponential
upper bound at every finite target rate.
-/
theorem finite_weighted_sum_hasExpUpperBoundWithConst_of_eventually_zero
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hzero : ∀ i : ι, ∀ᶠ n in atTop, p i n = 0)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n)
      targetRate :=
  HasExpUpperBoundWithConst.of_eventually_zero
    (finite_weighted_sum_eventually_zero (p := p) (weight := weight) hzero)

theorem finite_weighted_sum_hasExpLowerBoundWithConst_of_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hp_nonneg : ∀ i, ∀ᶠ n : ℕ in atTop, 0 ≤ p i n)
    (i0 : ι) (hweight_pos : 0 < weight i0)
    (hlower : HasExpLowerBoundWithConst (p i0) targetRate) :
    HasExpLowerBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate := by
  classical
  rcases hlower with ⟨c, hcpos, hc⟩
  refine ⟨weight i0 * c, mul_pos hweight_pos hcpos, ?_⟩
  have hp_all : ∀ᶠ n in atTop, ∀ i : ι, 0 ≤ p i n :=
    eventually_all.2 hp_nonneg
  filter_upwards [hc, hp_all] with n hn hnonneg
  have hcomponent :
      weight i0 * (c * Real.exp (-(n : ℝ) * targetRate)) ≤
        weight i0 * p i0 n :=
    mul_le_mul_of_nonneg_left hn hweight_pos.le
  have hterm_sum :
      weight i0 * p i0 n ≤ ∑ i : ι, weight i * p i n := by
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (hweight_nonneg i) (hnonneg i))
      (Finset.mem_univ i0)
  calc
    (weight i0 * c) * Real.exp (-(n : ℝ) * targetRate)
        = weight i0 * (c * Real.exp (-(n : ℝ) * targetRate)) := by ring
    _ ≤ weight i0 * p i0 n := hcomponent
    _ ≤ ∑ i : ι, weight i * p i n := hterm_sum

theorem finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hp_nonneg : ∀ i, ∀ᶠ n : ℕ in atTop, 0 ≤ p i n)
    (i0 : ι) (hweight_pos : 0 < weight i0)
    (hcert : ExponentialRateCertificate (p i0) (rate i0))
    (hrate : rate i0 < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate :=
  finite_weighted_sum_hasExpLowerBoundWithConst_of_component
    hweight_nonneg hp_nonneg i0 hweight_pos
    (hcert.hasExpLowerBoundWithConst_of_gt hrate)

/--
Finite weighted-sum exact rate with mixed exact and eventually-zero
components.  One positive-weight component certifies the minimum rate; every
other component either has an exact rate at least that minimum, or is
eventually zero.
-/
theorem finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hmin : ExponentialRateCertificate (p iMin) minRate)
    (hcase :
      ∀ i : ι,
        (∃ rate_i : ℝ,
          minRate ≤ rate_i ∧
            ExponentialRateCertificate (p i) rate_i) ∨
          (∀ᶠ n in atTop, p i n = 0)) :
    HasExponentialRate
      (fun n => ∑ i : ι, weight i * p i n)
      minRate := by
  classical
  have hp_nonneg :
      ∀ i : ι, ∀ᶠ n : ℕ in atTop, 0 ≤ p i n := by
    intro i
    rcases hcase i with hcert | hzero
    · rcases hcert with ⟨rate_i, _hrate_ge, hcert_i⟩
      exact hcert_i.eventually_pos.mono (fun _ hn => hn.le)
    · exact hzero.mono (fun _ hn => by simp [hn])
  have hlower_one :
      HasExpLowerBoundWithConst
        (fun n => ∑ i : ι, weight i * p i n) (minRate + 1) :=
    finite_weighted_sum_hasExpLowerBoundWithConst_of_component
      hweight_nonneg hp_nonneg iMin hweight_pos
      (hmin.hasExpLowerBoundWithConst_of_gt (by linarith))
  have hpos :
      ∀ᶠ n in atTop, 0 < ∑ i : ι, weight i * p i n := by
    rcases hlower_one with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (minRate + 1)))) hn
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    have hbound :
        ∀ i : ι, HasExpUpperBoundWithConst (p i) targetRate := by
      intro i
      rcases hcase i with hcert | hzero
      · rcases hcert with ⟨rate_i, hrate_ge, hcert_i⟩
        exact hcert_i.hasExpUpperBoundWithConst_of_lt
          (lt_of_lt_of_le htarget hrate_ge)
      · exact HasExpUpperBoundWithConst.of_eventually_zero hzero
    exact
      finite_weighted_sum_hasExpUpperBoundWithConst
        (p := p) (weight := weight) (rate := fun _ : ι => targetRate)
        hweight_nonneg hbound (fun _ => le_rfl)
  · intro targetRate htarget
    exact
      finite_weighted_sum_hasExpLowerBoundWithConst_of_component
        hweight_nonneg hp_nonneg iMin hweight_pos
        (hmin.hasExpLowerBoundWithConst_of_gt htarget)

/--
Finite weighted-sum exact rate when every component has an exact certificate
and one positive-weight component attains the minimum rate.
-/
theorem finite_weighted_sum_hasExponentialRate_of_min_component_certificates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hcert : ∀ i, ExponentialRateCertificate (p i) (rate i))
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_ge : ∀ i, rate iMin ≤ rate i) :
    HasExponentialRate
      (fun n => ∑ i : ι, weight i * p i n)
      (rate iMin) :=
  finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
    hweight_nonneg iMin hweight_pos (hcert iMin) fun i =>
      Or.inl ⟨rate i, hrate_ge i, hcert i⟩

/--
Finite weighted-sum exact rate from a dominating subfamily.  The selected
subfamily contains a positive-weight component attaining the subfamily
minimum, and every ambient component has rate at least one selected
subfamily rate.
-/
theorem finite_weighted_sum_hasExponentialRate_of_dominating_subfamily_certificates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Type*}
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ}
    (select : σ → ι)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hcert : ∀ i, ExponentialRateCertificate (p i) (rate i))
    (aMin : σ)
    (hweight_pos : 0 < weight (select aMin))
    (hsub_min : ∀ a : σ, rate (select aMin) ≤ rate (select a))
    (hdominates : ∀ i : ι, ∃ a : σ, rate (select a) ≤ rate i) :
    HasExponentialRate
      (fun n => ∑ i : ι, weight i * p i n)
      (rate (select aMin)) :=
  finite_weighted_sum_hasExponentialRate_of_min_component_certificates
    hweight_nonneg hcert (select aMin) hweight_pos fun i => by
      rcases hdominates i with ⟨a, ha⟩
      exact (hsub_min a).trans ha

/--
Automatic finite weighted-sum dichotomy for mixed exact/eventually-zero
components.  If every component either has some exact finite exponential rate
or is eventually zero, then a nonnegative finite weighted aggregate with
positive weights is either eventually zero, or has the exact rate of the
minimum finite-rate component.
-/
theorem finite_weighted_sum_hasExponentialRate_or_eventually_zero_of_cert_or_eventually_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_pos : ∀ i, 0 < weight i)
    (hcase :
      ∀ i : ι,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i) ∨
          (∀ᶠ n in atTop, p i n = 0)) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun n => ∑ i : ι, weight i * p i n) minRate) ∨
      (∀ᶠ n in atTop, (∑ i : ι, weight i * p i n) = 0) := by
  classical
  by_cases hfinite_exists :
      ∃ i : ι, ∃ rate_i : ℝ,
        ExponentialRateCertificate (p i) rate_i
  · let finiteSet : Finset ι :=
      (Finset.univ : Finset ι).filter
        (fun i => ∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i)
    have hfiniteSet_nonempty : finiteSet.Nonempty := by
      rcases hfinite_exists with ⟨i, hcert⟩
      exact ⟨i, by simp [finiteSet, hcert]⟩
    let rate : ι → ℝ := fun i =>
      if h : ∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i then
        Classical.choose h
      else
        0
    rcases Finset.exists_mem_eq_inf'
        (s := finiteSet) hfiniteSet_nonempty rate with
      ⟨iMin, hiMin_mem, hmin_eq⟩
    have hiMin_has :
        ∃ rate_i : ℝ, ExponentialRateCertificate (p iMin) rate_i := by
      simpa [finiteSet] using hiMin_mem
    let minRate : ℝ := rate iMin
    have hmin_cert :
        ExponentialRateCertificate (p iMin) minRate := by
      dsimp [minRate, rate]
      rw [dif_pos hiMin_has]
      exact Classical.choose_spec hiMin_has
    have hcase_ge :
        ∀ i : ι,
          (∃ rate_i : ℝ,
            minRate ≤ rate_i ∧
              ExponentialRateCertificate (p i) rate_i) ∨
            (∀ᶠ n in atTop, p i n = 0) := by
      intro i
      rcases hcase i with hfinite | hzero
      · left
        let rate_i : ℝ := rate i
        have hcert_i : ExponentialRateCertificate (p i) rate_i := by
          dsimp [rate_i, rate]
          rw [dif_pos hfinite]
          exact Classical.choose_spec hfinite
        have hi_mem : i ∈ finiteSet := by
          simp [finiteSet, hfinite]
        have hmin_le_rate : minRate ≤ rate_i := by
          dsimp [minRate, rate_i]
          rw [← hmin_eq]
          exact Finset.inf'_le rate hi_mem
        exact ⟨rate_i, hmin_le_rate, hcert_i⟩
      · right
        exact hzero
    left
    exact
      ⟨minRate,
        finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
          (p := p) (weight := weight)
          hweight_nonneg iMin (hweight_pos iMin) hmin_cert hcase_ge⟩
  · right
    have hzero_all :
        ∀ i : ι, ∀ᶠ n in atTop, p i n = 0 := by
      intro i
      rcases hcase i with hfinite | hzero
      · exact False.elim (hfinite_exists ⟨i, hfinite⟩)
      · exact hzero
    exact finite_weighted_sum_eventually_zero
      (p := p) (weight := weight) hzero_all

/--
Minimizer-returning version of
`finite_weighted_sum_hasExponentialRate_or_eventually_zero_of_cert_or_eventually_zero`.
In the finite-rate branch it exposes a component whose certificate realizes
the aggregate rate, together with the comparison data showing every other
finite component has rate at least that minimum.
-/
theorem finite_weighted_sum_hasExponentialRate_with_min_component_or_eventually_zero_of_cert_or_eventually_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_pos : ∀ i, 0 < weight i)
    (hcase :
      ∀ i : ι,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i) ∨
          (∀ᶠ n in atTop, p i n = 0)) :
    (∃ iMin : ι, ∃ minRate : ℝ,
      ExponentialRateCertificate (p iMin) minRate ∧
        (∀ i : ι,
          (∃ rate_i : ℝ,
            minRate ≤ rate_i ∧
              ExponentialRateCertificate (p i) rate_i) ∨
            (∀ᶠ n in atTop, p i n = 0)) ∧
        HasExponentialRate
          (fun n => ∑ i : ι, weight i * p i n) minRate) ∨
      (∀ᶠ n in atTop, (∑ i : ι, weight i * p i n) = 0) := by
  classical
  by_cases hfinite_exists :
      ∃ i : ι, ∃ rate_i : ℝ,
        ExponentialRateCertificate (p i) rate_i
  · let finiteSet : Finset ι :=
      (Finset.univ : Finset ι).filter
        (fun i => ∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i)
    have hfiniteSet_nonempty : finiteSet.Nonempty := by
      rcases hfinite_exists with ⟨i, hcert⟩
      exact ⟨i, by simp [finiteSet, hcert]⟩
    let rate : ι → ℝ := fun i =>
      if h : ∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i then
        Classical.choose h
      else
        0
    rcases Finset.exists_mem_eq_inf'
        (s := finiteSet) hfiniteSet_nonempty rate with
      ⟨iMin, hiMin_mem, hmin_eq⟩
    have hiMin_has :
        ∃ rate_i : ℝ, ExponentialRateCertificate (p iMin) rate_i := by
      simpa [finiteSet] using hiMin_mem
    let minRate : ℝ := rate iMin
    have hmin_cert :
        ExponentialRateCertificate (p iMin) minRate := by
      dsimp [minRate, rate]
      rw [dif_pos hiMin_has]
      exact Classical.choose_spec hiMin_has
    have hcase_ge :
        ∀ i : ι,
          (∃ rate_i : ℝ,
            minRate ≤ rate_i ∧
              ExponentialRateCertificate (p i) rate_i) ∨
            (∀ᶠ n in atTop, p i n = 0) := by
      intro i
      rcases hcase i with hfinite | hzero
      · left
        let rate_i : ℝ := rate i
        have hcert_i : ExponentialRateCertificate (p i) rate_i := by
          dsimp [rate_i, rate]
          rw [dif_pos hfinite]
          exact Classical.choose_spec hfinite
        have hi_mem : i ∈ finiteSet := by
          simp [finiteSet, hfinite]
        have hmin_le_rate : minRate ≤ rate_i := by
          dsimp [minRate, rate_i]
          rw [← hmin_eq]
          exact Finset.inf'_le rate hi_mem
        exact ⟨rate_i, hmin_le_rate, hcert_i⟩
      · right
        exact hzero
    left
    refine ⟨iMin, minRate, hmin_cert, hcase_ge, ?_⟩
    exact
      finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
        (p := p) (weight := weight)
        hweight_nonneg iMin (hweight_pos iMin) hmin_cert hcase_ge
  · right
    have hzero_all :
        ∀ i : ι, ∀ᶠ n in atTop, p i n = 0 := by
      intro i
      rcases hcase i with hfinite | hzero
      · exact False.elim (hfinite_exists ⟨i, hfinite⟩)
      · exact hzero
    exact finite_weighted_sum_eventually_zero
      (p := p) (weight := weight) hzero_all

/--
Payload-carrying minimizer version of finite weighted-sum aggregation.  The
`payload` predicate is ignored by the aggregation proof but preserved for the
selected finite-rate component.  This is useful when a paper needs additional
data about the pivotal component, such as a comparison certificate to another
rate expression.
-/
theorem finite_weighted_sum_hasExponentialRate_with_min_component_payload_or_eventually_zero_of_cert_or_eventually_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (payload : ι → ℝ → Prop)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_pos : ∀ i, 0 < weight i)
    (hcase :
      ∀ i : ι,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i ∧
            payload i rate_i) ∨
          (∀ᶠ n in atTop, p i n = 0)) :
    (∃ iMin : ι, ∃ minRate : ℝ,
      ExponentialRateCertificate (p iMin) minRate ∧
        payload iMin minRate ∧
        (∀ i : ι,
          (∃ rate_i : ℝ,
            minRate ≤ rate_i ∧
              ExponentialRateCertificate (p i) rate_i) ∨
            (∀ᶠ n in atTop, p i n = 0)) ∧
        HasExponentialRate
          (fun n => ∑ i : ι, weight i * p i n) minRate) ∨
      (∀ᶠ n in atTop, (∑ i : ι, weight i * p i n) = 0) := by
  classical
  by_cases hfinite_exists :
      ∃ i : ι, ∃ rate_i : ℝ,
        ExponentialRateCertificate (p i) rate_i ∧
          payload i rate_i
  · let finiteSet : Finset ι :=
      (Finset.univ : Finset ι).filter
        (fun i => ∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i ∧
            payload i rate_i)
    have hfiniteSet_nonempty : finiteSet.Nonempty := by
      rcases hfinite_exists with ⟨i, hcert⟩
      exact ⟨i, by simp [finiteSet, hcert]⟩
    let rate : ι → ℝ := fun i =>
      if h : ∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i ∧
            payload i rate_i then
        Classical.choose h
      else
        0
    rcases Finset.exists_mem_eq_inf'
        (s := finiteSet) hfiniteSet_nonempty rate with
      ⟨iMin, hiMin_mem, hmin_eq⟩
    have hiMin_has :
        ∃ rate_i : ℝ,
          ExponentialRateCertificate (p iMin) rate_i ∧
            payload iMin rate_i := by
      simpa [finiteSet] using hiMin_mem
    let minRate : ℝ := rate iMin
    have hmin_cert :
        ExponentialRateCertificate (p iMin) minRate := by
      dsimp [minRate, rate]
      rw [dif_pos hiMin_has]
      exact (Classical.choose_spec hiMin_has).1
    have hmin_payload : payload iMin minRate := by
      dsimp [minRate, rate]
      rw [dif_pos hiMin_has]
      exact (Classical.choose_spec hiMin_has).2
    have hcase_ge :
        ∀ i : ι,
          (∃ rate_i : ℝ,
            minRate ≤ rate_i ∧
              ExponentialRateCertificate (p i) rate_i) ∨
            (∀ᶠ n in atTop, p i n = 0) := by
      intro i
      rcases hcase i with hfinite | hzero
      · left
        rcases hfinite with ⟨rate_exists, hcert_exists, hpayload_exists⟩
        let rate_i : ℝ := rate i
        have hfinite_payload :
            ∃ rate_i : ℝ,
              ExponentialRateCertificate (p i) rate_i ∧
                payload i rate_i :=
          ⟨rate_exists, hcert_exists, hpayload_exists⟩
        have hcert_i : ExponentialRateCertificate (p i) rate_i := by
          dsimp [rate_i, rate]
          rw [dif_pos hfinite_payload]
          exact (Classical.choose_spec hfinite_payload).1
        have hi_mem : i ∈ finiteSet := by
          simp [finiteSet, hfinite_payload]
        have hmin_le_rate : minRate ≤ rate_i := by
          dsimp [minRate, rate_i]
          rw [← hmin_eq]
          exact Finset.inf'_le rate hi_mem
        exact ⟨rate_i, hmin_le_rate, hcert_i⟩
      · right
        exact hzero
    left
    refine ⟨iMin, minRate, hmin_cert, hmin_payload, hcase_ge, ?_⟩
    exact
      finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
        (p := p) (weight := weight)
        hweight_nonneg iMin (hweight_pos iMin) hmin_cert hcase_ge
  · right
    have hzero_all :
        ∀ i : ι, ∀ᶠ n in atTop, p i n = 0 := by
      intro i
      rcases hcase i with hfinite | hzero
      · exact False.elim (hfinite_exists ⟨i, hfinite⟩)
      · exact hzero
    exact finite_weighted_sum_eventually_zero
      (p := p) (weight := weight) hzero_all

/--
Extended-rate version of
`finite_weighted_sum_hasExponentialRate_or_eventually_zero_of_cert_or_eventually_zero`.
The returned `WithTop ℝ` rate is finite when at least one weighted component has
a finite exact rate, and `⊤` when all components are eventually zero.
-/
theorem finite_weighted_sum_hasExtendedExponentialRate_of_cert_or_eventually_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_pos : ∀ i, 0 < weight i)
    (hcase :
      ∀ i : ι,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (p i) rate_i) ∨
          (∀ᶠ n in atTop, p i n = 0)) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun n => ∑ i : ι, weight i * p i n) rate := by
  rcases
      finite_weighted_sum_hasExponentialRate_or_eventually_zero_of_cert_or_eventually_zero
        (p := p) (weight := weight)
        hweight_nonneg hweight_pos hcase with
    hfinite | hzero
  · rcases hfinite with ⟨minRate, hrate⟩
    exact ⟨(minRate : WithTop ℝ),
      HasExtendedExponentialRate.finite hrate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
A positive constant times a pure exponential sequence has exactly the displayed
exponential rate.  This is the finite-discrete Laplace primitive used when a
finite sum is reduced to its slowest exponential term.
-/
theorem exponentialRateCertificate_const_mul_exp
    {C rate : ℝ} (hC : 0 < C) :
    ExponentialRateCertificate
      (fun n : ℕ => C * Real.exp (-(n : ℝ) * rate)) rate := by
  refine
    { eventually_pos := ?_
      has_rate := ?_ }
  · filter_upwards with n
    exact mul_pos hC (Real.exp_pos _)
  · refine hasExponentialRate_of_expUpperLowerBounds ?_ ?_ ?_
    · filter_upwards with n
      exact mul_pos hC (Real.exp_pos _)
    · intro targetRate htarget
      refine ⟨C, hC, ?_⟩
      filter_upwards with n
      have hexp :
          Real.exp (-(n : ℝ) * rate) ≤
            Real.exp (-(n : ℝ) * targetRate) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (le_of_lt htarget)
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact
        ⟨mul_nonneg hC.le (Real.exp_pos _).le,
          mul_le_mul_of_nonneg_left hexp hC.le⟩
    · intro targetRate htarget
      refine ⟨C, hC, ?_⟩
      filter_upwards with n
      have hexp :
          Real.exp (-(n : ℝ) * targetRate) ≤
            Real.exp (-(n : ℝ) * rate) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (le_of_lt htarget)
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact mul_le_mul_of_nonneg_left hexp hC.le

/--
Generic finite family of exact error-rate certificates.  This abstracts the
common EC large-deviation pattern before specializing to pairwise ranking
errors: each index has an error probability and an exact exponential rate.
-/
structure FiniteErrorRateCertificate (ι : Type*) where
  errorProb : ι → ℕ → ℝ
  rate : ι → ℝ
  has_rate : ∀ i, ExponentialRateCertificate (errorProb i) (rate i)

namespace FiniteErrorRateCertificate

variable {ι : Type*} [Fintype ι]

/-- Weighted finite aggregate of certified error probabilities. -/
def aggregateError (C : FiniteErrorRateCertificate ι)
    (weight : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i : ι, weight i * C.errorProb i n

/-- Unit-weight finite aggregates are the plain sum of component errors. -/
@[simp]
theorem aggregateError_unit (C : FiniteErrorRateCertificate ι) :
    C.aggregateError (fun _ => (1 : ℝ)) =
      fun n => ∑ i : ι, C.errorProb i n := by
  funext n
  simp [aggregateError]

theorem aggregateError_hasExpUpperBoundWithConst_of_lt
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst
      (C.aggregateError weight) targetRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
      (ι := ι)
      (p := fun i n => C.errorProb i n)
      (weight := weight)
      (rate := C.rate)
      (targetRate := targetRate)
      hweight
      C.has_rate
      hrate

/--
If every component exact rate is bounded below by a strictly positive floor,
then any nonnegative finite weighted aggregate of the component errors tends
to zero.
-/
theorem aggregateError_tendsto_zero_of_pos_rate_floor
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {rateFloor : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor : ∀ i, rateFloor ≤ C.rate i) :
    Tendsto (C.aggregateError weight) atTop (nhds 0) := by
  let targetRate : ℝ := rateFloor / 2
  have htarget_pos : 0 < targetRate := by
    dsimp [targetRate]
    linarith
  have htarget_lt : ∀ i : ι, targetRate < C.rate i := by
    intro i
    exact lt_of_lt_of_le (by dsimp [targetRate]; linarith) (hrateFloor i)
  exact
    (C.aggregateError_hasExpUpperBoundWithConst_of_lt hweight htarget_lt)
      |>.tendsto_zero_of_pos_rate htarget_pos

theorem aggregateError_hasExpLowerBoundWithConst_of_component_gt
    [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (i0 : ι) (hweight_pos : 0 < weight i0)
    (hrate : C.rate i0 < targetRate) :
    HasExpLowerBoundWithConst
      (C.aggregateError weight) targetRate := by
  have hp_nonneg :
      ∀ i : ι, ∀ᶠ n : ℕ in atTop, 0 ≤ C.errorProb i n := by
    intro i
    exact (C.has_rate i).eventually_pos.mono (fun _ hn => hn.le)
  simpa [aggregateError] using
    finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
      (ι := ι)
      (p := fun i n => C.errorProb i n)
      (weight := weight)
      (rate := C.rate)
      (targetRate := targetRate)
      hweight_nonneg
      hp_nonneg
      i0
      hweight_pos
      (C.has_rate i0)
      hrate

theorem aggregateError_hasExponentialRate_of_min_component
    [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : C.rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ C.rate i) :
    HasExponentialRate (C.aggregateError weight) minRate := by
  have hlower_one :
      HasExpLowerBoundWithConst (C.aggregateError weight) (minRate + 1) :=
    C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg iMin hweight_pos
      (by rw [hrate_min]; linarith)
  have hpos :
      ∀ᶠ n in atTop, 0 < C.aggregateError weight n := by
    rcases hlower_one with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (minRate + 1)))) hn
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    exact C.aggregateError_hasExpUpperBoundWithConst_of_lt
      hweight_nonneg
      (fun i => lt_of_lt_of_le htarget (hrate_ge i))
  · intro targetRate htarget
    exact C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg iMin hweight_pos
      (by rw [hrate_min]; exact htarget)

/--
Exact finite-aggregate rate from a dominating subfamily.  The subfamily
contains a positive-weight component attaining the subfamily minimum, and every
ambient component has rate at least one subfamily rate.  This is the finite
large-deviation algebra behind adjacent-pair reductions.
-/
theorem aggregateError_hasExponentialRate_of_dominating_subfamily
    [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {σ : Type*} (select : σ → ι)
    {weight : ι → ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (aMin : σ) (hweight_pos : 0 < weight (select aMin))
    (hsub_min : ∀ a : σ, C.rate (select aMin) ≤ C.rate (select a))
    (hdominates : ∀ i : ι, ∃ a : σ, C.rate (select a) ≤ C.rate i) :
    HasExponentialRate
      (C.aggregateError weight) (C.rate (select aMin)) := by
  refine C.aggregateError_hasExponentialRate_of_min_component
    hweight_nonneg (select aMin) hweight_pos rfl ?_
  intro i
  rcases hdominates i with ⟨a, ha⟩
  exact (hsub_min a).trans ha

end FiniteErrorRateCertificate

/--
Finite family whose components are known relative to a candidate aggregate
rate.  Each component either has some exact finite rate at least `minRate`, or
is eventually zero.  This is the reusable wrapper for mixed finite-rate /
boundary aggregations where a paper wants a finite real rate for the aggregate
without choosing a dummy component rate for eventually-zero terms.
-/
structure FiniteErrorRateEnvelopeCertificate (ι : Type*) (minRate : ℝ) where
  errorProb : ι → ℕ → ℝ
  component :
    ∀ i : ι,
      (∃ rate_i : ℝ,
        minRate ≤ rate_i ∧
          ExponentialRateCertificate (errorProb i) rate_i) ∨
        (∀ᶠ n in atTop, errorProb i n = 0)

namespace FiniteErrorRateEnvelopeCertificate

variable {ι : Type*} [Fintype ι] {minRate : ℝ}

/-- Weighted finite aggregate of envelope-certified error probabilities. -/
def aggregateError (C : FiniteErrorRateEnvelopeCertificate ι minRate)
    (weight : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i : ι, weight i * C.errorProb i n

/-- Unit-weight envelope aggregates are the plain sum of component errors. -/
@[simp]
theorem aggregateError_unit
    (C : FiniteErrorRateEnvelopeCertificate ι minRate) :
    C.aggregateError (fun _ => (1 : ℝ)) =
      fun n => ∑ i : ι, C.errorProb i n := by
  funext n
  simp [aggregateError]

theorem aggregateError_hasExpUpperBoundWithConst_of_lt
    (C : FiniteErrorRateEnvelopeCertificate ι minRate)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : targetRate < minRate) :
    HasExpUpperBoundWithConst
      (C.aggregateError weight) targetRate := by
  have hbound :
      ∀ i : ι, HasExpUpperBoundWithConst (C.errorProb i) targetRate := by
    intro i
    rcases C.component i with hfinite | hzero
    · rcases hfinite with ⟨rate_i, hrate_ge, hcert⟩
      exact hcert.hasExpUpperBoundWithConst_of_lt
        (lt_of_lt_of_le hrate hrate_ge)
    · exact HasExpUpperBoundWithConst.of_eventually_zero hzero
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst
      (ι := ι)
      (p := fun i n => C.errorProb i n)
      (weight := weight)
      (rate := fun _ : ι => targetRate)
      (targetRate := targetRate)
      hweight
      hbound
      (fun _ => le_rfl)

/--
Exact finite aggregate rate from a rate envelope: one positive-weight
component supplies the exact minimum rate, while every other component is
either exact at a rate no smaller than that minimum or eventually zero.
-/
theorem aggregateError_hasExponentialRate_of_min_component
    [DecidableEq ι]
    (C : FiniteErrorRateEnvelopeCertificate ι minRate)
    {weight : ι → ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hmin : ExponentialRateCertificate (C.errorProb iMin) minRate) :
    HasExponentialRate (C.aggregateError weight) minRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
      (ι := ι)
      (p := fun i n => C.errorProb i n)
      (weight := weight)
      (minRate := minRate)
      hweight_nonneg
      iMin
      hweight_pos
      hmin
      C.component

end FiniteErrorRateEnvelopeCertificate

/--
Finite discrete Laplace principle for a nonnegative weighted sum of pure
exponentials: if one positive-weight term realizes the minimum exponent, then
the whole finite sum has that exponent.
-/
theorem finite_exp_sum_hasExponentialRate_of_min_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight rate : ι → ℝ) {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ rate i) :
    HasExponentialRate
      (fun n : ℕ =>
        ∑ i : ι, weight i * Real.exp (-(n : ℝ) * rate i))
      minRate := by
  let C : FiniteErrorRateCertificate ι :=
    { errorProb := fun i n => Real.exp (-(n : ℝ) * rate i)
      rate := rate
      has_rate := fun i => by
        simpa [one_mul] using
          (exponentialRateCertificate_const_mul_exp
            (C := 1) (rate := rate i) zero_lt_one) }
  simpa [FiniteErrorRateCertificate.aggregateError, C] using
    C.aggregateError_hasExponentialRate_of_min_component
      hweight_nonneg iMin hweight_pos hrate_min hrate_ge

/--
Certificate form of `finite_exp_sum_hasExponentialRate_of_min_component`.
-/
theorem finite_exp_sum_exponentialRateCertificate_of_min_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight rate : ι → ℝ) {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ rate i) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∑ i : ι, weight i * Real.exp (-(n : ℝ) * rate i))
      minRate where
  eventually_pos := by
    filter_upwards with n
    have hterm_pos :
        0 < weight iMin * Real.exp (-(n : ℝ) * rate iMin) :=
      mul_pos hweight_pos (Real.exp_pos _)
    have hterm_le :
        weight iMin * Real.exp (-(n : ℝ) * rate iMin) ≤
          ∑ i : ι, weight i * Real.exp (-(n : ℝ) * rate i) := by
      exact Finset.single_le_sum
        (fun i _hi =>
          show 0 ≤ weight i * Real.exp (-(n : ℝ) * rate i) from
            mul_nonneg (hweight_nonneg i) (Real.exp_pos _).le)
        (Finset.mem_univ iMin)
    exact lt_of_lt_of_le hterm_pos hterm_le
  has_rate :=
    finite_exp_sum_hasExponentialRate_of_min_component
      weight rate hweight_nonneg iMin hweight_pos hrate_min hrate_ge

/--
Pairwise ranking-error upper-bound certificate.  `errorProb hi lo n` is the
probability that the pair `(hi, lo)` is misordered after scale `n`; `rate hi lo`
is a certified exponential upper-bound rate.
-/
structure PairwiseErrorUpperBoundCertificate (θ : Type*) where
  errorProb : θ → θ → ℕ → ℝ
  rate : θ → θ → ℝ
  has_bound : ∀ hi lo, HasExpUpperBoundWithConst (errorProb hi lo) (rate hi lo)

namespace PairwiseErrorUpperBoundCertificate

variable {θ : Type*} [Fintype θ]

/-- Weighted aggregate of finitely many pairwise ranking errors. -/
def aggregateError (C : PairwiseErrorUpperBoundCertificate θ)
    (pairWeight : θ → θ → ℝ) (n : ℕ) : ℝ :=
  ∑ p : θ × θ, pairWeight p.1 p.2 * C.errorProb p.1 p.2 n

/-- Unit-weight pairwise aggregates are the plain sum of pairwise errors. -/
@[simp]
theorem aggregateError_unit (C : PairwiseErrorUpperBoundCertificate θ) :
    C.aggregateError (fun _ _ => (1 : ℝ)) =
      fun n => ∑ p : θ × θ, C.errorProb p.1 p.2 n := by
  funext n
  simp [aggregateError]

theorem aggregateError_hasExpUpperBoundWithConst
    (C : PairwiseErrorUpperBoundCertificate θ)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : ∀ hi lo, targetRate ≤ C.rate hi lo) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst
      (ι := θ × θ)
      (p := fun pair n => C.errorProb pair.1 pair.2 n)
      (weight := fun pair => pairWeight pair.1 pair.2)
      (rate := fun pair => C.rate pair.1 pair.2)
      (targetRate := targetRate)
      (fun pair => hweight pair.1 pair.2)
      (fun pair => C.has_bound pair.1 pair.2)
      (fun pair => hrate pair.1 pair.2)

end PairwiseErrorUpperBoundCertificate

/--
Pairwise ranking-error exact-rate certificate. Unlike
`PairwiseErrorUpperBoundCertificate`, this stores exact normalized-log decay
certificates and can be weakened to any strictly smaller aggregate upper-bound
rate.
-/
structure PairwiseErrorRateCertificate (θ : Type*) where
  errorProb : θ → θ → ℕ → ℝ
  rate : θ → θ → ℝ
  has_rate : ∀ hi lo, ExponentialRateCertificate (errorProb hi lo) (rate hi lo)

namespace PairwiseErrorRateCertificate

variable {θ : Type*} [Fintype θ]

/-- View a pairwise ranking-error certificate as a generic finite certificate. -/
def toFiniteErrorRateCertificate (C : PairwiseErrorRateCertificate θ) :
    FiniteErrorRateCertificate (θ × θ) where
  errorProb := fun pair n => C.errorProb pair.1 pair.2 n
  rate := fun pair => C.rate pair.1 pair.2
  has_rate := fun pair => C.has_rate pair.1 pair.2

/-- Weighted aggregate of finitely many pairwise ranking errors. -/
def aggregateError (C : PairwiseErrorRateCertificate θ)
    (pairWeight : θ → θ → ℝ) (n : ℕ) : ℝ :=
  ∑ p : θ × θ, pairWeight p.1 p.2 * C.errorProb p.1 p.2 n

/-- Unit-weight pairwise aggregates are the plain sum of pairwise errors. -/
@[simp]
theorem aggregateError_unit (C : PairwiseErrorRateCertificate θ) :
    C.aggregateError (fun _ _ => (1 : ℝ)) =
      fun n => ∑ p : θ × θ, C.errorProb p.1 p.2 n := by
  funext n
  simp [aggregateError]

theorem aggregateError_hasExpUpperBoundWithConst_of_lt
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : ∀ hi lo, targetRate < C.rate hi lo) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
      (ι := θ × θ)
      (p := fun pair n => C.errorProb pair.1 pair.2 n)
      (weight := fun pair => pairWeight pair.1 pair.2)
      (rate := fun pair => C.rate pair.1 pair.2)
      (targetRate := targetRate)
      (fun pair => hweight pair.1 pair.2)
      (fun pair => C.has_rate pair.1 pair.2)
      (fun pair => hrate pair.1 pair.2)

/--
If all pairwise exact rates are bounded below by a positive floor, the
nonnegative finite weighted aggregate of pairwise errors tends to zero.
-/
theorem aggregateError_tendsto_zero_of_pos_rate_floor
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {rateFloor : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor : ∀ hi lo, rateFloor ≤ C.rate hi lo) :
    Tendsto (C.aggregateError pairWeight) atTop (nhds 0) := by
  simpa [aggregateError] using
    C.toFiniteErrorRateCertificate.aggregateError_tendsto_zero_of_pos_rate_floor
      (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
      (rateFloor := rateFloor)
      (fun pair => hweight pair.1 pair.2)
      hrateFloor_pos
      (fun pair => hrateFloor pair.1 pair.2)

theorem aggregateError_hasExpLowerBoundWithConst_of_component_gt
    [DecidableEq θ]
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hi lo : θ) (hweight_pos : 0 < pairWeight hi lo)
    (hrate : C.rate hi lo < targetRate) :
    HasExpLowerBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  have hp_nonneg :
      ∀ pair : θ × θ,
        ∀ᶠ n : ℕ in atTop, 0 ≤ C.errorProb pair.1 pair.2 n := by
    intro pair
    exact (C.has_rate pair.1 pair.2).eventually_pos.mono
      (fun _ hn => hn.le)
  simpa [aggregateError] using
    finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
      (ι := θ × θ)
      (p := fun pair n => C.errorProb pair.1 pair.2 n)
      (weight := fun pair => pairWeight pair.1 pair.2)
      (rate := fun pair => C.rate pair.1 pair.2)
      (targetRate := targetRate)
      (fun pair => hweight_nonneg pair.1 pair.2)
      hp_nonneg
      (hi, lo)
      hweight_pos
      (C.has_rate hi lo)
      hrate

theorem aggregateError_hasExponentialRate_of_min_pair
    [DecidableEq θ]
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hi lo : θ) (hweight_pos : 0 < pairWeight hi lo)
    (hrate_min : C.rate hi lo = minRate)
    (hrate_ge : ∀ hi lo, minRate ≤ C.rate hi lo) :
    HasExponentialRate (C.aggregateError pairWeight) minRate := by
  have hlower_one :
      HasExpLowerBoundWithConst
        (C.aggregateError pairWeight) (minRate + 1) :=
    C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg hi lo hweight_pos
      (by rw [hrate_min]; linarith)
  have hpos :
      ∀ᶠ n in atTop, 0 < C.aggregateError pairWeight n := by
    rcases hlower_one with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (minRate + 1)))) hn
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    exact C.aggregateError_hasExpUpperBoundWithConst_of_lt
      hweight_nonneg
      (fun hi lo => lt_of_lt_of_le htarget (hrate_ge hi lo))
  · intro targetRate htarget
    exact C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg hi lo hweight_pos
      (by rw [hrate_min]; exact htarget)

end PairwiseErrorRateCertificate

/--
Pairwise version of `FiniteErrorRateEnvelopeCertificate`.  This keeps the
rating-system and social-choice pairwise APIs aligned with the generic finite
envelope while preserving the paper-facing `hi lo` indexing.
-/
structure PairwiseErrorRateEnvelopeCertificate (θ : Type*) (minRate : ℝ) where
  errorProb : θ → θ → ℕ → ℝ
  component :
    ∀ hi lo : θ,
      (∃ rate_i : ℝ,
        minRate ≤ rate_i ∧
          ExponentialRateCertificate (errorProb hi lo) rate_i) ∨
        (∀ᶠ n in atTop, errorProb hi lo n = 0)

namespace PairwiseErrorRateEnvelopeCertificate

variable {θ : Type*} [Fintype θ] {minRate : ℝ}

/-- View a pairwise envelope certificate as a generic finite envelope. -/
def toFiniteErrorRateEnvelopeCertificate
    (C : PairwiseErrorRateEnvelopeCertificate θ minRate) :
    FiniteErrorRateEnvelopeCertificate (θ × θ) minRate where
  errorProb := fun pair n => C.errorProb pair.1 pair.2 n
  component := fun pair => C.component pair.1 pair.2

/-- Weighted aggregate of finitely many pairwise envelope errors. -/
def aggregateError (C : PairwiseErrorRateEnvelopeCertificate θ minRate)
    (pairWeight : θ → θ → ℝ) (n : ℕ) : ℝ :=
  ∑ p : θ × θ, pairWeight p.1 p.2 * C.errorProb p.1 p.2 n

/-- Unit-weight pairwise envelope aggregates are the plain sum of errors. -/
@[simp]
theorem aggregateError_unit
    (C : PairwiseErrorRateEnvelopeCertificate θ minRate) :
    C.aggregateError (fun _ _ => (1 : ℝ)) =
      fun n => ∑ p : θ × θ, C.errorProb p.1 p.2 n := by
  funext n
  simp [aggregateError]

theorem aggregateError_hasExpUpperBoundWithConst_of_lt
    (C : PairwiseErrorRateEnvelopeCertificate θ minRate)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : targetRate < minRate) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  simpa [aggregateError] using
    C.toFiniteErrorRateEnvelopeCertificate
      |>.aggregateError_hasExpUpperBoundWithConst_of_lt
        (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
        (fun pair => hweight pair.1 pair.2)
        hrate

theorem aggregateError_hasExponentialRate_of_min_pair
    [DecidableEq θ]
    (C : PairwiseErrorRateEnvelopeCertificate θ minRate)
    {pairWeight : θ → θ → ℝ}
    (hweight_nonneg : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : θ) (hweight_pos : 0 < pairWeight hiMin loMin)
    (hmin :
      ExponentialRateCertificate
        (C.errorProb hiMin loMin) minRate) :
    HasExponentialRate (C.aggregateError pairWeight) minRate := by
  simpa [aggregateError] using
    C.toFiniteErrorRateEnvelopeCertificate
      |>.aggregateError_hasExponentialRate_of_min_component
        (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
        (fun pair => hweight_nonneg pair.1 pair.2)
        (hiMin, loMin)
        hweight_pos
        hmin

end PairwiseErrorRateEnvelopeCertificate

/--
Certificate boundary for a Laplace-principle or Gartner-Ellis calculation.
The paper or distribution-family layer supplies `has_rate`; downstream proofs
can use the exponential-rate statement without unfolding the analytic proof.
-/
structure LargeDeviationRateCertificate (eventProb : ℕ → ℝ) (rate : ℝ) where
  rate_certificate : ExponentialRateCertificate eventProb rate

end

end Probability
end AppliedModelingLib

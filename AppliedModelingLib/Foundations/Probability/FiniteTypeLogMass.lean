import AppliedModelingLib.Foundations.Math.EpsilonContinuity
import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts

open scoped BigOperators
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
# Logarithmic lower bounds for finite empirical-type masses

This file provides a small bridge used by finite-alphabet large-deviation
arguments: once a one-period empirical type has a logarithmic mass lower bound,
it can be fed directly into the reusable empirical-type lower certificates.
-/

/--
If the logarithm of a finite empirical type mass is at least `-Q * baseRate`,
then the empirical type mass itself is at least `exp (-Q * baseRate)`.

Only coordinates with nonzero count need positive atom mass; zero-count atoms
contribute a factor of one.
-/
theorem empiricalTypeBlockMass_ge_exp_of_log_sum_bound
    (μ : PMF α) {Q : ℕ} (q : α → ℕ) {baseRate : ℝ}
    (hμpos : ∀ a : α, q a ≠ 0 → 0 < (μ a).toReal)
    (hlog :
      -(Q : ℝ) * baseRate ≤
        Real.log (Nat.multinomial (Finset.univ : Finset α) q : ℝ) +
          ∑ a : α, (q a : ℝ) * Real.log (μ a).toReal) :
    Real.exp (-(Q : ℝ) * baseRate) ≤
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
        ∏ a : α, (μ a).toReal ^ q a := by
  classical
  let M : ℝ := (Nat.multinomial (Finset.univ : Finset α) q : ℝ)
  let P : ℝ := ∏ a : α, (μ a).toReal ^ q a
  have hM_pos : 0 < M := by
    dsimp [M]
    exact_mod_cast Nat.multinomial_pos (Finset.univ : Finset α) q
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have hpow_pos : ∀ a : α, 0 < (μ a).toReal ^ q a := by
    intro a
    by_cases hq : q a = 0
    · simp [hq]
    · exact pow_pos (hμpos a hq) (q a)
  have hpow_ne : ∀ a : α, (μ a).toReal ^ q a ≠ 0 := by
    intro a
    exact ne_of_gt (hpow_pos a)
  have hP_pos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (fun a _ => hpow_pos a)
  have hP_ne : P ≠ 0 := ne_of_gt hP_pos
  have hMP_pos : 0 < M * P := mul_pos hM_pos hP_pos
  have hlog_prod :
      Real.log P =
        ∑ a : α, (q a : ℝ) * Real.log (μ a).toReal := by
    dsimp [P]
    calc
      Real.log (∏ a : α, (μ a).toReal ^ q a)
          = ∑ a : α, Real.log ((μ a).toReal ^ q a) := by
              simpa using
                (Real.log_prod (s := (Finset.univ : Finset α))
                  (f := fun a : α => (μ a).toReal ^ q a)
                  (by
                    intro a _
                    exact hpow_ne a))
      _ = ∑ a : α, (q a : ℝ) * Real.log (μ a).toReal := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa using (Real.log_pow (μ a).toReal (q a))
  have hlog_mass :
      Real.log (M * P) =
        Real.log M +
          ∑ a : α, (q a : ℝ) * Real.log (μ a).toReal := by
    rw [Real.log_mul hM_ne hP_ne, hlog_prod]
  have hlog_to_mass : -(Q : ℝ) * baseRate ≤ Real.log (M * P) := by
    rw [hlog_mass]
    simpa [M] using hlog
  have hmass :=
    (Real.le_log_iff_exp_le hMP_pos).mp hlog_to_mass
  simpa [M, P] using hmass

/--
Full-support convenience version of
`empiricalTypeBlockMass_ge_exp_of_log_sum_bound`.
-/
theorem empiricalTypeBlockMass_ge_exp_of_log_sum_bound_of_forall_pos
    (μ : PMF α) {Q : ℕ} (q : α → ℕ) {baseRate : ℝ}
    (hμpos : ∀ a : α, 0 < (μ a).toReal)
    (hlog :
      -(Q : ℝ) * baseRate ≤
        Real.log (Nat.multinomial (Finset.univ : Finset α) q : ℝ) +
          ∑ a : α, (q a : ℝ) * Real.log (μ a).toReal) :
    Real.exp (-(Q : ℝ) * baseRate) ≤
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
        ∏ a : α, (μ a).toReal ^ q a :=
  empiricalTypeBlockMass_ge_exp_of_log_sum_bound
    μ q (fun a _ => hμpos a) hlog

/--
Method-of-types block lower bound with the modal polynomial loss isolated.

The empirical-law mode bound gives the factor
`((Q + 1) ^ card α)^{-1}`.  A caller supplies the remaining product comparison
between the empirical law `q / Q` and the target finite law `ν`; the optional
`baseRate` inequality accounts for choosing a block size large enough that the
polynomial term is within the available rate slack.
-/
theorem empiricalTypeBlockMass_ge_exp_of_product_compare
    (ν : α → ℝ) {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ)
    (hqsum : ∑ a : α, q a = Q)
    {baseRate eps : ℝ}
    (hcompare :
      Real.exp (-(Q : ℝ) * eps) *
          ∏ a : α, (((q a : ℝ) / Q) ^ q a) ≤
        ∏ a : α, ν a ^ q a)
    (hrate :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        Real.exp (-(Q : ℝ) * eps) /
          (((Q.succ : ℕ) : ℝ) ^ Fintype.card α)) :
    Real.exp (-(Q : ℝ) * baseRate) ≤
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
        ∏ a : α, ν a ^ q a := by
  classical
  let M : ℝ := (Nat.multinomial (Finset.univ : Finset α) q : ℝ)
  let Pq : ℝ := ∏ a : α, (((q a : ℝ) / Q) ^ q a)
  let Pν : ℝ := ∏ a : α, ν a ^ q a
  let countBound : ℝ := ((Q.succ : ℕ) : ℝ) ^ Fintype.card α
  have hmodal : 1 / countBound ≤ M * Pq := by
    dsimp [M, Pq, countBound]
    exact multinomial_empirical_mode_mass_ge_inv_countVectors hQpos q hqsum
  have hexp_nonneg : 0 ≤ Real.exp (-(Q : ℝ) * eps) :=
    (Real.exp_pos _).le
  have hpoly :
      Real.exp (-(Q : ℝ) * eps) / countBound ≤
        Real.exp (-(Q : ℝ) * eps) * (M * Pq) := by
    calc
      Real.exp (-(Q : ℝ) * eps) / countBound
          = Real.exp (-(Q : ℝ) * eps) * (1 / countBound) := by ring
      _ ≤ Real.exp (-(Q : ℝ) * eps) * (M * Pq) :=
            mul_le_mul_of_nonneg_left hmodal hexp_nonneg
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact_mod_cast Nat.zero_le _
  have hcompareM :
      M * (Real.exp (-(Q : ℝ) * eps) * Pq) ≤ M * Pν := by
    exact mul_le_mul_of_nonneg_left (by simpa [Pq, Pν] using hcompare) hM_nonneg
  calc
    Real.exp (-(Q : ℝ) * baseRate)
        ≤ Real.exp (-(Q : ℝ) * eps) / countBound := hrate
    _ ≤ Real.exp (-(Q : ℝ) * eps) * (M * Pq) := hpoly
    _ = M * (Real.exp (-(Q : ℝ) * eps) * Pq) := by ring
    _ ≤ M * Pν := hcompareM
    _ =
        (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
          ∏ a : α, ν a ^ q a := by rfl

/-- `log (Q + 1) / Q -> 0` along positive natural denominators. -/
theorem tendsto_log_nat_succ_div_nat_nhds_zero :
    Tendsto
      (fun Q : ℕ => Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ))
      atTop (nhds 0) := by
  have hlog_succ_div_succ :
      Tendsto
        (fun Q : ℕ =>
          Real.log (((Q.succ : ℕ) : ℝ)) /
            (((Q.succ : ℕ) : ℝ)))
        atTop (nhds 0) := by
    have hbase :
        Tendsto
          (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds 0) :=
      AppliedModelingLib.Math.tendsto_log_nat_div_nat_nhds_zero
    have hsucc_atTop : Tendsto (fun Q : ℕ => Q.succ) atTop atTop := by
      simpa [Nat.succ_eq_add_one] using (tendsto_add_atTop_nat 1)
    change
      Tendsto
        ((fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) ∘
          fun Q : ℕ => Q.succ)
        atTop (nhds 0)
    exact hbase.comp hsucc_atTop
  have hsucc_div :
      Tendsto
        (fun Q : ℕ => (((Q.succ : ℕ) : ℝ)) / (Q : ℝ))
        atTop (nhds 1) := by
    have hinv :
        Tendsto (fun Q : ℕ => (1 : ℝ) / (Q : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have hlim :
        Tendsto (fun Q : ℕ => 1 + (1 : ℝ) / (Q : ℝ)) atTop
          (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with Q hQ
    have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    rw [Nat.cast_succ]
    field_simp [Nat.cast_succ, hQne]
  have hmul :
      Tendsto
        (fun Q : ℕ =>
          (Real.log (((Q.succ : ℕ) : ℝ)) /
              (((Q.succ : ℕ) : ℝ))) *
            ((((Q.succ : ℕ) : ℝ)) / (Q : ℝ)))
        atTop (nhds 0) := by
    simpa using hlog_succ_div_succ.mul hsucc_div
  refine Tendsto.congr' ?_ hmul
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hsucc_ne : (((Q.succ : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero Q)
  field_simp [hQne, hsucc_ne]

/--
Choose a denominator large enough both for finite-simplex rounding and for
absorbing the method-of-types polynomial loss.
-/
theorem exists_denominator_card_div_lt_and_polynomial_loss_lt
    {η slack : ℝ} (hη : 0 < η) (hslack : 0 < slack) :
    ∃ Q : ℕ,
      0 < Q ∧
      (Fintype.card α : ℝ) / (Q : ℝ) < η ∧
      (Fintype.card α : ℝ) *
          (Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ)) < slack := by
  have hcard_div_tend :
      Tendsto
        (fun Q : ℕ => (Fintype.card α : ℝ) / (Q : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Fintype.card α : ℝ)
  have hpoly_tend :
      Tendsto
        (fun Q : ℕ =>
          (Fintype.card α : ℝ) *
            (Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ)))
        atTop (nhds 0) :=
    by
      simpa using
        tendsto_log_nat_succ_div_nat_nhds_zero.const_mul
          (Fintype.card α : ℝ)
  have hcard_event :
      ∀ᶠ Q : ℕ in atTop,
        (Fintype.card α : ℝ) / (Q : ℝ) < η :=
    hcard_div_tend.eventually_lt_const hη
  have hpoly_event :
      ∀ᶠ Q : ℕ in atTop,
        (Fintype.card α : ℝ) *
            (Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ)) < slack :=
    hpoly_tend.eventually_lt_const hslack
  have hall :
      ∀ᶠ Q : ℕ in atTop,
        (Fintype.card α : ℝ) / (Q : ℝ) < η ∧
          (Fintype.card α : ℝ) *
              (Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ)) < slack ∧
          0 < Q :=
    hcard_event.and (hpoly_event.and (eventually_gt_atTop 0))
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hall
  have hQprops := hQ Q le_rfl
  exact ⟨Q, hQprops.2.2, hQprops.1, hQprops.2.1⟩

/--
Convert a per-sample rate inequality into the exponential form needed to absorb
the method-of-types polynomial count-vector loss.
-/
theorem exp_neg_mul_rate_le_exp_neg_mul_div_countBound
    {Q : ℕ} (hQpos : 0 < Q) {eps baseRate : ℝ}
    (hrate :
      eps +
          (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) / (Q : ℝ) ≤
        baseRate) :
    Real.exp (-(Q : ℝ) * baseRate) ≤
      Real.exp (-(Q : ℝ) * eps) /
        (((Q.succ : ℕ) : ℝ) ^ Fintype.card α) := by
  let countBound : ℝ := ((Q.succ : ℕ) : ℝ) ^ Fintype.card α
  have hQreal_pos : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hsucc_pos : 0 < ((Q.succ : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos Q
  have hcount_pos : 0 < countBound := by
    dsimp [countBound]
    exact pow_pos hsucc_pos _
  have hrhs_pos :
      0 <
        Real.exp (-(Q : ℝ) * eps) /
          (((Q.succ : ℕ) : ℝ) ^ Fintype.card α) := by
    exact div_pos (Real.exp_pos _) hcount_pos
  have hmul := mul_le_mul_of_nonneg_left hrate hQreal_pos.le
  have hrate_log :
      -(Q : ℝ) * baseRate ≤
        -(Q : ℝ) * eps -
          (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) := by
    have hrewrite :
        (Q : ℝ) *
            (eps +
              (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) /
                (Q : ℝ)) =
          (Q : ℝ) * eps +
            (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) := by
      field_simp [ne_of_gt hQreal_pos]
    rw [hrewrite] at hmul
    linarith
  have hlog_rhs :
      Real.log
          (Real.exp (-(Q : ℝ) * eps) /
            (((Q.succ : ℕ) : ℝ) ^ Fintype.card α)) =
        -(Q : ℝ) * eps -
          (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) := by
    rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hcount_pos),
      Real.log_exp, Real.log_pow]
  exact (Real.le_log_iff_exp_le hrhs_pos).mp (by
    rw [hlog_rhs]
    exact hrate_log)

/--
A log-ratio upper bound implies the product comparison used by
`empiricalTypeBlockMass_ge_exp_of_product_compare`.

Only coordinates with nonzero count need positive masses.
-/
theorem product_pow_ge_exp_neg_of_log_ratio_bound
    (p ν : α → ℝ) {Q : ℕ} (q : α → ℕ) {eps : ℝ}
    (hp_pos : ∀ a : α, q a ≠ 0 → 0 < p a)
    (hν_pos : ∀ a : α, q a ≠ 0 → 0 < ν a)
    (hlog :
      ∑ a : α, (q a : ℝ) * (Real.log (p a) - Real.log (ν a)) ≤
        (Q : ℝ) * eps) :
    Real.exp (-(Q : ℝ) * eps) * ∏ a : α, p a ^ q a ≤
      ∏ a : α, ν a ^ q a := by
  classical
  let Pp : ℝ := ∏ a : α, p a ^ q a
  let Pν : ℝ := ∏ a : α, ν a ^ q a
  have hp_pow_pos : ∀ a : α, 0 < p a ^ q a := by
    intro a
    by_cases hq : q a = 0
    · simp [hq]
    · exact pow_pos (hp_pos a hq) (q a)
  have hν_pow_pos : ∀ a : α, 0 < ν a ^ q a := by
    intro a
    by_cases hq : q a = 0
    · simp [hq]
    · exact pow_pos (hν_pos a hq) (q a)
  have hPp_pos : 0 < Pp := by
    dsimp [Pp]
    exact Finset.prod_pos (fun a _ => hp_pow_pos a)
  have hPν_pos : 0 < Pν := by
    dsimp [Pν]
    exact Finset.prod_pos (fun a _ => hν_pow_pos a)
  have hlogPp :
      Real.log Pp = ∑ a : α, (q a : ℝ) * Real.log (p a) := by
    dsimp [Pp]
    calc
      Real.log (∏ a : α, p a ^ q a)
          = ∑ a : α, Real.log (p a ^ q a) := by
              simpa using
                (Real.log_prod (s := (Finset.univ : Finset α))
                  (f := fun a : α => p a ^ q a)
                  (by
                    intro a _
                    exact ne_of_gt (hp_pow_pos a)))
      _ = ∑ a : α, (q a : ℝ) * Real.log (p a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa using (Real.log_pow (p a) (q a))
  have hlogPν :
      Real.log Pν = ∑ a : α, (q a : ℝ) * Real.log (ν a) := by
    dsimp [Pν]
    calc
      Real.log (∏ a : α, ν a ^ q a)
          = ∑ a : α, Real.log (ν a ^ q a) := by
              simpa using
                (Real.log_prod (s := (Finset.univ : Finset α))
                  (f := fun a : α => ν a ^ q a)
                  (by
                    intro a _
                    exact ne_of_gt (hν_pow_pos a)))
      _ = ∑ a : α, (q a : ℝ) * Real.log (ν a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa using (Real.log_pow (ν a) (q a))
  have hlog_le :
      Real.log Pp - (Q : ℝ) * eps ≤ Real.log Pν := by
    rw [hlogPp, hlogPν]
    have hsplit :
        ∑ a : α, (q a : ℝ) * (Real.log (p a) - Real.log (ν a)) =
          (∑ a : α, (q a : ℝ) * Real.log (p a)) -
            ∑ a : α, (q a : ℝ) * Real.log (ν a) := by
      calc
        ∑ a : α, (q a : ℝ) * (Real.log (p a) - Real.log (ν a))
            =
            ∑ a : α,
              ((q a : ℝ) * Real.log (p a) -
                (q a : ℝ) * Real.log (ν a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              ring
        _ =
            (∑ a : α, (q a : ℝ) * Real.log (p a)) -
              ∑ a : α, (q a : ℝ) * Real.log (ν a) := by
              rw [Finset.sum_sub_distrib]
    linarith
  have hexp_le : Real.exp (Real.log Pp - (Q : ℝ) * eps) ≤ Pν :=
    (Real.le_log_iff_exp_le hPν_pos).mp hlog_le
  have hexp_eq :
      Real.exp (Real.log Pp - (Q : ℝ) * eps) =
        Real.exp (-(Q : ℝ) * eps) * Pp := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hPp_pos]
    ring_nf
  simpa [Pp, Pν, hexp_eq] using hexp_le

/--
Specialization of `product_pow_ge_exp_neg_of_log_ratio_bound` to the empirical
frequency vector `q / Q`.
-/
theorem empiricalFreqProduct_pow_ge_exp_neg_of_log_ratio_bound
    (ν : α → ℝ) {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) {eps : ℝ}
    (hν_pos : ∀ a : α, q a ≠ 0 → 0 < ν a)
    (hlog :
      ∑ a : α,
          (q a : ℝ) *
            (Real.log ((q a : ℝ) / Q) - Real.log (ν a)) ≤
        (Q : ℝ) * eps) :
    Real.exp (-(Q : ℝ) * eps) *
        ∏ a : α, (((q a : ℝ) / Q) ^ q a) ≤
      ∏ a : α, ν a ^ q a :=
  product_pow_ge_exp_neg_of_log_ratio_bound
    (fun a : α => (q a : ℝ) / Q) ν q
    (fun a hq => by
      have hqa_pos : 0 < (q a : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hq
      have hQ_pos : 0 < (Q : ℝ) := by exact_mod_cast hQpos
      exact div_pos hqa_pos hQ_pos)
    hν_pos hlog

/--
Convert an empirical-frequency log-ratio bound into the count-weighted form
used by finite empirical-type masses.
-/
theorem count_log_ratio_sum_eq_denominator_mul_freq_log_ratio_sum
    (ν : α → ℝ) {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) :
    (∑ a : α,
        (q a : ℝ) *
          (Real.log ((q a : ℝ) / Q) - Real.log (ν a))) =
      (Q : ℝ) *
        ∑ a : α,
          ((q a : ℝ) / Q) *
            (Real.log ((q a : ℝ) / Q) - Real.log (ν a)) := by
  classical
  have hQne : (Q : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hQpos)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  field_simp [hQne]

/--
Finite-dimensional continuity of the log-ratio objective.  If `ν` and `μ` are
strictly positive finite laws, then any vector `p` sufficiently close to `ν`
coordinatewise has log-ratio sum at most the value at `ν` plus `eps`.
-/
theorem exists_forall_close_log_ratio_sum_le
    [Nonempty α]
    (ν μ : α → ℝ)
    (hν_pos : ∀ a : α, 0 < ν a)
    (hμ_pos : ∀ a : α, 0 < μ a)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ p : α → ℝ,
        (∀ a : α, |p a - ν a| < δ) →
          (∑ a : α, p a * (Real.log (p a) - Real.log (μ a))) ≤
            (∑ a : α, ν a * (Real.log (ν a) - Real.log (μ a))) + eps := by
  classical
  let unit : ℝ := eps / ((Fintype.card α : ℝ) + 1)
  have hunit_pos : 0 < unit := by
    dsimp [unit]
    positivity
  have hcont :
      ∀ a : α,
        AppliedModelingLib.EpsilonContinuousAt
          (fun x : ℝ => x * (Real.log x - Real.log (μ a))) (ν a) := by
    intro a
    apply AppliedModelingLib.epsilonContinuousAt_of_continuousAt
    exact
      continuousAt_id.mul
        ((Real.continuousAt_log (ne_of_gt (hν_pos a))).sub continuousAt_const)
  choose δ hδ_pos hδ_spec using fun a : α => hcont a unit hunit_pos
  let δmin : ℝ := (Finset.univ : Finset α).inf' Finset.univ_nonempty δ
  have hδmin_pos : 0 < δmin := by
    dsimp [δmin]
    rw [Finset.lt_inf'_iff]
    intro a _ha
    exact hδ_pos a
  refine ⟨δmin, hδmin_pos, ?_⟩
  intro p hpclose
  have hpoint :
      ∀ a : α,
        |p a * (Real.log (p a) - Real.log (μ a)) -
          ν a * (Real.log (ν a) - Real.log (μ a))| < unit := by
    intro a
    exact hδ_spec a (p a)
      (lt_of_lt_of_le (hpclose a)
        (by
          dsimp [δmin]
          exact Finset.inf'_le δ (Finset.mem_univ a)))
  have hle_point :
      ∀ a : α,
        p a * (Real.log (p a) - Real.log (μ a)) ≤
          ν a * (Real.log (ν a) - Real.log (μ a)) + unit := by
    intro a
    exact le_of_lt (lt_add_of_sub_left_lt (abs_lt.mp (hpoint a)).2)
  have hsum_le :
      (∑ a : α, p a * (Real.log (p a) - Real.log (μ a))) ≤
        ∑ a : α, (ν a * (Real.log (ν a) - Real.log (μ a)) + unit) := by
    exact Finset.sum_le_sum (fun a _ => hle_point a)
  have hunit_sum_lt :
      (Fintype.card α : ℝ) * unit < eps := by
    dsimp [unit]
    have hden_pos : 0 < (Fintype.card α : ℝ) + 1 := by positivity
    have hfrac_lt_one :
        (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) + 1) < 1 := by
      rw [div_lt_one hden_pos]
      linarith
    have hmul := mul_lt_mul_of_pos_left hfrac_lt_one heps
    have heq :
        (Fintype.card α : ℝ) *
            (eps / ((Fintype.card α : ℝ) + 1)) =
          eps * ((Fintype.card α : ℝ) /
            ((Fintype.card α : ℝ) + 1)) := by
      field_simp [hden_pos.ne']
    linarith
  calc
    (∑ a : α, p a * (Real.log (p a) - Real.log (μ a)))
        ≤ ∑ a : α, (ν a * (Real.log (ν a) - Real.log (μ a)) + unit) :=
          hsum_le
    _ =
        (∑ a : α, ν a * (Real.log (ν a) - Real.log (μ a))) +
          (Fintype.card α : ℝ) * unit := by
          rw [Finset.sum_add_distrib]
          simp
    _ ≤
        (∑ a : α, ν a * (Real.log (ν a) - Real.log (μ a))) + eps := by
          linarith

/--
Support-aware continuity of the finite log-ratio objective.

This variant avoids a full-support assumption.  Coordinates where the reference
point `ν` has zero mass must also be zero under admissible perturbations `p`;
on the positive support, ordinary real continuity applies.
-/
theorem exists_forall_close_log_ratio_sum_le_of_same_support
    [Nonempty α]
    (ν μ : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hμ_nonneg : ∀ a, 0 ≤ μ a)
    (hsupport : ∀ a, 0 < ν a ↔ 0 < μ a)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ p : α → ℝ,
        (∀ a, 0 ≤ p a) →
        (∀ a, p a ≠ 0 → 0 < μ a) →
        (∀ a : α, |p a - ν a| < δ) →
          (∑ a : α, p a * (Real.log (p a) - Real.log (μ a))) ≤
            (∑ a : α, ν a * (Real.log (ν a) - Real.log (μ a))) + eps := by
  classical
  let unit : ℝ := eps / ((Fintype.card α : ℝ) + 1)
  have hunit_pos : 0 < unit := by
    dsimp [unit]
    positivity
  have hcont :
      ∀ a : α,
        0 < ν a →
          AppliedModelingLib.EpsilonContinuousAt
            (fun x : ℝ => x * (Real.log x - Real.log (μ a))) (ν a) := by
    intro a hνpos
    apply AppliedModelingLib.epsilonContinuousAt_of_continuousAt
    exact
      continuousAt_id.mul
        ((Real.continuousAt_log (ne_of_gt hνpos)).sub continuousAt_const)
  choose δpos hδpos_pos hδpos_spec using
    fun a : {a : α // 0 < ν a} =>
      hcont a.1 a.2 unit hunit_pos
  let δraw : α → ℝ := fun a =>
    if h : 0 < ν a then δpos ⟨a, h⟩ else 1
  let δmin : ℝ := (Finset.univ : Finset α).inf' Finset.univ_nonempty δraw
  have hδraw_pos : ∀ a : α, 0 < δraw a := by
    intro a
    dsimp [δraw]
    by_cases h : 0 < ν a
    · simp [h, hδpos_pos ⟨a, h⟩]
    · simp [h]
  have hδmin_pos : 0 < δmin := by
    dsimp [δmin]
    rw [Finset.lt_inf'_iff]
    intro a _ha
    exact hδraw_pos a
  refine ⟨δmin, hδmin_pos, ?_⟩
  intro p hp_nonneg hp_support hpclose
  have hpoint :
      ∀ a : α,
        p a * (Real.log (p a) - Real.log (μ a)) ≤
          ν a * (Real.log (ν a) - Real.log (μ a)) + unit := by
    intro a
    by_cases hνpos : 0 < ν a
    · have hclose_a : |p a - ν a| < δpos ⟨a, hνpos⟩ := by
        have hle_raw : δmin ≤ δraw a := by
          dsimp [δmin]
          exact Finset.inf'_le δraw (Finset.mem_univ a)
        have hraw_eq : δraw a = δpos ⟨a, hνpos⟩ := by
          simp [δraw, hνpos]
        exact lt_of_lt_of_le (hpclose a) (by simpa [hraw_eq] using hle_raw)
      have hpoint_abs :
          |p a * (Real.log (p a) - Real.log (μ a)) -
            ν a * (Real.log (ν a) - Real.log (μ a))| < unit :=
        hδpos_spec ⟨a, hνpos⟩ (p a) hclose_a
      exact le_of_lt (lt_add_of_sub_left_lt (abs_lt.mp hpoint_abs).2)
    · have hν_zero : ν a = 0 :=
        le_antisymm (le_of_not_gt hνpos) (hν_nonneg a)
      have hμ_not_pos : ¬ 0 < μ a := by
        intro hμpos
        exact hνpos ((hsupport a).2 hμpos)
      have hμ_zero : μ a = 0 :=
        le_antisymm (le_of_not_gt hμ_not_pos) (hμ_nonneg a)
      have hp_zero : p a = 0 := by
        by_contra hpne
        have hp_pos : 0 < p a :=
          lt_of_le_of_ne (hp_nonneg a) (Ne.symm hpne)
        exact hμ_not_pos (hp_support a hpne)
      simp [hν_zero, hμ_zero, hp_zero, hunit_pos.le]
  have hsum_le :
      (∑ a : α, p a * (Real.log (p a) - Real.log (μ a))) ≤
        ∑ a : α,
          (ν a * (Real.log (ν a) - Real.log (μ a)) + unit) := by
    exact Finset.sum_le_sum (fun a _ => hpoint a)
  have hunit_sum_lt :
      (Fintype.card α : ℝ) * unit < eps := by
    dsimp [unit]
    have hden_pos : 0 < (Fintype.card α : ℝ) + 1 := by positivity
    have hfrac_lt_one :
        (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) + 1) < 1 := by
      rw [div_lt_one hden_pos]
      linarith
    have hmul := mul_lt_mul_of_pos_left hfrac_lt_one heps
    have heq :
        (Fintype.card α : ℝ) *
            (eps / ((Fintype.card α : ℝ) + 1)) =
          eps * ((Fintype.card α : ℝ) /
            ((Fintype.card α : ℝ) + 1)) := by
      field_simp [hden_pos.ne']
    linarith
  calc
    (∑ a : α, p a * (Real.log (p a) - Real.log (μ a)))
        ≤ ∑ a : α,
            (ν a * (Real.log (ν a) - Real.log (μ a)) + unit) :=
          hsum_le
    _ =
        (∑ a : α, ν a * (Real.log (ν a) - Real.log (μ a))) +
          (Fintype.card α : ℝ) * unit := by
          rw [Finset.sum_add_distrib]
          simp
    _ ≤
        (∑ a : α, ν a * (Real.log (ν a) - Real.log (μ a))) + eps := by
          linarith

/--
The finite log-ratio objective at an exponential tilt equals
`z * tilted_mean - log MGF(z)`.
-/
theorem finiteExponentialTilt_log_ratio_sum_eq
    (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    (∑ a : α,
        (finiteExponentialTilt μ score z a).toReal *
          (Real.log (finiteExponentialTilt μ score z a).toReal -
            Real.log (μ a).toReal)) =
      z * pmfExp (finiteExponentialTilt μ score z) score -
        Real.log (finiteMGF μ score z) := by
  classical
  calc
    (∑ a : α,
        (finiteExponentialTilt μ score z a).toReal *
          (Real.log (finiteExponentialTilt μ score z a).toReal -
            Real.log (μ a).toReal))
        =
      ∑ a : α,
        (finiteExponentialTilt μ score z a).toReal *
          (z * score a - Real.log (finiteMGF μ score z)) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        by_cases hμzero : (μ a).toReal = 0
        · have htilt_zero :
            (finiteExponentialTilt μ score z a).toReal = 0 := by
            rw [finiteExponentialTilt_apply_toReal, hμzero]
            ring
          simp [htilt_zero]
        · have hμpos : 0 < (μ a).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hμzero)
          have htilt_pos :
              0 < (finiteExponentialTilt μ score z a).toReal := by
            rw [finiteExponentialTilt_apply_toReal]
            exact div_pos
              (mul_pos hμpos (Real.exp_pos _))
              (finiteMGF_pos μ score z)
          rw [finiteExponentialTilt_apply_toReal,
            Real.log_div
              (mul_ne_zero hμzero (Real.exp_ne_zero _))
              (ne_of_gt (finiteMGF_pos μ score z)),
            Real.log_mul hμzero (Real.exp_ne_zero _), Real.log_exp]
          ring
    _ =
      z * pmfExp (finiteExponentialTilt μ score z) score -
        Real.log (finiteMGF μ score z) *
          (∑ a : α, (finiteExponentialTilt μ score z a).toReal) := by
        calc
          ∑ a : α,
              (finiteExponentialTilt μ score z a).toReal *
                (z * score a - Real.log (finiteMGF μ score z))
              =
            ∑ a : α,
              (z * ((finiteExponentialTilt μ score z a).toReal * score a) -
                Real.log (finiteMGF μ score z) *
                  (finiteExponentialTilt μ score z a).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              ring
          _ =
              z * pmfExp (finiteExponentialTilt μ score z) score -
                Real.log (finiteMGF μ score z) *
                  (∑ a : α, (finiteExponentialTilt μ score z a).toReal) := by
              rw [Finset.sum_sub_distrib]
              congr 1
              · simp [pmfExp, Finset.mul_sum, mul_comm]
              · rw [← Finset.mul_sum]
    _ =
      z * pmfExp (finiteExponentialTilt μ score z) score -
        Real.log (finiteMGF μ score z) := by
        rw [pmfToRealSum]
        ring

/--
At a stationary exponential tilt, the finite log-ratio objective is
`-log MGF(z)`.
-/
theorem finiteExponentialTilt_log_ratio_sum_eq_neg_log_mgf_of_stationary
    (μ : PMF α) (score : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0) :
    (∑ a : α,
        (finiteExponentialTilt μ score z a).toReal *
          (Real.log (finiteExponentialTilt μ score z a).toReal -
            Real.log (μ a).toReal)) =
      -Real.log (finiteMGF μ score z) := by
  rw [finiteExponentialTilt_log_ratio_sum_eq,
    pmfExp_finiteExponentialTilt_eq_zero_of_stationary μ score hstationary]
  ring

/--
Finite-alphabet Cramer certificate from a stationary exponential tilt.

This is the entropy-aware method-of-types route: approximate the stationary
tilted law by support-preserving empirical types whose score sum stays in the
nonpositive tail, use the multinomial type mass lower bound, and absorb the
polynomial type-count loss into any strictly slower target rate.
-/
theorem finiteIidScoreCramerCertificate_of_stationary_tilted_empiricalTypes_of_pos_neg_atoms
    [Nonempty α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0) :
    FiniteIidScoreCramerCertificate μ score := by
  classical
  refine
    finiteIidScoreCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg ?_
  intro targetRate htarget
  let rate : ℝ := finiteChernoffRate μ score
  let slack : ℝ := targetRate - rate
  have hslack_pos : 0 < slack := by
    dsimp [slack, rate]
    exact sub_pos.mpr htarget
  let tilt : α → ℝ := fun a => (finiteExponentialTilt μ score z a).toReal
  let μreal : α → ℝ := fun a => (μ a).toReal
  have htilt_nonneg : ∀ a, 0 ≤ tilt a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hμ_nonneg : ∀ a, 0 ≤ μreal a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hsupport : ∀ a, 0 < tilt a ↔ 0 < μreal a := by
    intro a
    simpa [tilt, μreal] using
      (finiteExponentialTilt_apply_toReal_pos_iff μ score z a)
  obtain ⟨δCont, hδCont_pos, hδCont_spec⟩ :=
    exists_forall_close_log_ratio_sum_le_of_same_support
      tilt μreal htilt_nonneg hμ_nonneg hsupport
      (show 0 < slack / 4 by positivity)
  let δRound : ℝ := min (δCont / 2) (1 / 2)
  have hδRound_pos : 0 < δRound := by
    dsimp [δRound]
    exact lt_min (half_pos hδCont_pos) (by norm_num)
  have hδRound_nonneg : 0 ≤ δRound := hδRound_pos.le
  have hδRound_le_one : δRound ≤ 1 := by
    dsimp [δRound]
    exact (min_le_right _ _).trans (by norm_num)
  have hδRound_le_half : δRound ≤ δCont / 2 := by
    dsimp [δRound]
    exact min_le_left _ _
  have hδRound_lt_δCont : δRound < δCont := by
    have hhalf_lt : δCont / 2 < δCont := by linarith
    exact lt_of_le_of_lt hδRound_le_half hhalf_lt
  let scoreAbs : ℝ := ∑ a : α, |score a|
  have hscoreAbs_nonneg : 0 ≤ scoreAbs := by
    dsimp [scoreAbs]
    exact Finset.sum_nonneg (fun a _ => abs_nonneg (score a))
  have hneg_pos : 0 < -score aNeg := by linarith
  let η : ℝ := min (δRound / 2) (δRound * (-score aNeg) / (scoreAbs + 1))
  have hη_pos : 0 < η := by
    dsimp [η]
    refine lt_min ?_ ?_
    · exact half_pos hδRound_pos
    · exact div_pos (mul_pos hδRound_pos hneg_pos) (by linarith)
  have hη_le_half : η ≤ δRound / 2 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_le_margin : η ≤ δRound * (-score aNeg) / (scoreAbs + 1) := by
    dsimp [η]
    exact min_le_right _ _
  have hmargin :
      η * scoreAbs ≤ δRound * (-(score aNeg)) := by
    have hden_pos : 0 < scoreAbs + 1 := by linarith
    have hmul_le :
        η * scoreAbs ≤
          (δRound * (-score aNeg) / (scoreAbs + 1)) * scoreAbs :=
      mul_le_mul_of_nonneg_right hη_le_margin hscoreAbs_nonneg
    have hfrac_le :
        (δRound * (-score aNeg) / (scoreAbs + 1)) * scoreAbs ≤
          δRound * (-score aNeg) := by
      have hnum_nonneg : 0 ≤ δRound * (-score aNeg) :=
        (mul_pos hδRound_pos hneg_pos).le
      have hratio_le_one : scoreAbs / (scoreAbs + 1) ≤ 1 := by
        rw [div_le_one hden_pos]
        linarith
      calc
        (δRound * (-score aNeg) / (scoreAbs + 1)) * scoreAbs
            = δRound * (-score aNeg) * (scoreAbs / (scoreAbs + 1)) := by
                field_simp [ne_of_gt hden_pos]
        _ ≤ δRound * (-score aNeg) * 1 :=
              mul_le_mul_of_nonneg_left hratio_le_one hnum_nonneg
        _ = δRound * (-score aNeg) := by ring
    exact hmul_le.trans hfrac_le
  have hclose_total : η + δRound < δCont := by
    have hη_le_quarter : η ≤ δCont / 4 := by
      have hη_le : η ≤ δRound / 2 := hη_le_half
      have hδ_le : δRound / 2 ≤ δCont / 4 := by linarith
      exact hη_le.trans hδ_le
    have hδ_le_half : δRound ≤ δCont / 2 := hδRound_le_half
    linarith
  obtain ⟨Q, hQpos, hQ_large, hpoly_loss⟩ :=
    exists_denominator_card_div_lt_and_polynomial_loss_lt
      (α := α) hη_pos (show 0 < slack / 4 by positivity)
  obtain ⟨q, hqsum, hqclose, hqtail, hq_support⟩ :=
    exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom_of_large_denominator_with_support
      μ score hstationary hmassNeg hscoreNeg hQpos
      hδRound_nonneg hδRound_le_one hη_pos hQ_large hmargin
      hclose_total
  let p : α → ℝ := fun a => (q a : ℝ) / Q
  have hp_nonneg : ∀ a, 0 ≤ p a := by
    intro a
    dsimp [p]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp_support : ∀ a, p a ≠ 0 → 0 < μreal a := by
    intro a hpne
    have hqa : q a ≠ 0 := by
      intro hqzero
      apply hpne
      simp [p, hqzero]
    simpa [μreal] using hq_support a hqa
  have hpclose : ∀ a : α, |p a - tilt a| < δCont := by
    intro a
    simpa [p, tilt] using hqclose a
  have hlogratio_le :
      (∑ a : α, p a * (Real.log (p a) - Real.log (μreal a))) ≤
        (∑ a : α, tilt a * (Real.log (tilt a) - Real.log (μreal a))) +
          slack / 4 :=
    hδCont_spec p hp_nonneg hp_support hpclose
  have htilt_log :
      (∑ a : α, tilt a * (Real.log (tilt a) - Real.log (μreal a))) =
        rate := by
    dsimp [tilt, μreal, rate]
    rw [finiteExponentialTilt_log_ratio_sum_eq_neg_log_mgf_of_stationary
      μ score hstationary]
    symm
    exact
      finiteChernoffRate_eq_neg_log_base_of_convex_stationary
        μ score (finiteLogMGF_convex μ score) hstationary (by rfl)
  let epsRate : ℝ := rate + slack / 4
  have hfreq_log :
      (∑ a : α,
          p a * (Real.log (p a) - Real.log (μreal a))) ≤ epsRate := by
    dsimp [epsRate]
    rw [htilt_log] at hlogratio_le
    exact hlogratio_le
  have hcount_log :
      (∑ a : α,
          (q a : ℝ) *
            (Real.log ((q a : ℝ) / Q) - Real.log (μreal a))) ≤
        (Q : ℝ) * epsRate := by
    rw [count_log_ratio_sum_eq_denominator_mul_freq_log_ratio_sum
      (ν := μreal) hQpos q]
    exact mul_le_mul_of_nonneg_left hfreq_log (Nat.cast_nonneg Q)
  have hprod_compare :
      Real.exp (-(Q : ℝ) * epsRate) *
          ∏ a : α, (((q a : ℝ) / Q) ^ q a) ≤
        ∏ a : α, μreal a ^ q a :=
    empiricalFreqProduct_pow_ge_exp_neg_of_log_ratio_bound
      (ν := μreal) hQpos q
      (fun a hqa => by simpa [μreal] using hq_support a hqa)
      hcount_log
  let baseRate : ℝ := rate + slack / 2
  have hbaseRate_lt : baseRate < targetRate := by
    dsimp [baseRate, slack, rate]
    linarith
  have hpoly_absorb :
      epsRate +
          (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) / (Q : ℝ) ≤
        baseRate := by
    have hpoly_loss' :
        (Fintype.card α : ℝ) * Real.log ((Q.succ : ℕ) : ℝ) / (Q : ℝ) <
          slack / 4 := by
      simpa [mul_div_assoc] using hpoly_loss
    dsimp [epsRate, baseRate]
    linarith
  have htype_mass :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
          ∏ a : α, μreal a ^ q a := by
    refine
      empiricalTypeBlockMass_ge_exp_of_product_compare
        (ν := μreal) hQpos q hqsum hprod_compare ?_
    exact
      exp_neg_mul_rate_le_exp_neg_mul_div_countBound
        (α := α) hQpos hpoly_absorb
  refine
    ⟨FiniteIidScoreEmpiricalTypeLowerCertificate.of_periodic_rate
      (μ := μ) (score := score) hQpos q aNeg hqsum hqtail
      (le_of_lt hscoreNeg) htype_mass hmassNeg, ?_⟩
  change -Real.log (Real.exp (-baseRate)) < targetRate
  rw [Real.log_exp]
  simpa using hbaseRate_lt

/--
Finite-alphabet Cramer certificate from a stationary log-MGF minimizer written
as a zero-derivative condition.  This is a wrapper around
`finiteIidScoreCramerCertificate_of_stationary_tilted_empiricalTypes_of_pos_neg_atoms`
using the explicit finite log-MGF derivative formula.
-/
theorem finiteIidScoreCramerCertificate_of_logMGF_hasDerivAt_zero_empiricalTypes_of_pos_neg_atoms
    [Nonempty α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {z : ℝ}
    (hderiv : HasDerivAt (fun t : ℝ => finiteLogMGF μ score t) 0 z) :
    FiniteIidScoreCramerCertificate μ score := by
  have hformula := finiteLogMGF_hasDerivAt μ score z
  have hquot_zero :
      (∑ a : α, (μ a).toReal * (score a * Real.exp (z * score a))) /
          finiteMGF μ score z = 0 :=
    hformula.unique hderiv
  have hstationary :
      (∑ a : α, (μ a).toReal * (score a * Real.exp (z * score a))) = 0 := by
    have hmgf_ne : finiteMGF μ score z ≠ 0 :=
      (finiteMGF_pos μ score z).ne'
    have hmul :=
      congrArg (fun x : ℝ => x * finiteMGF μ score z) hquot_zero
    field_simp [hmgf_ne] at hmul
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  exact
    finiteIidScoreCramerCertificate_of_stationary_tilted_empiricalTypes_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg hstationary

end

end Probability
end AppliedModelingLib

import KR21Monoculture.MallowsFiniteLemmas
import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.SocialChoice.Ranking.RankPower
import AppliedModelingLib.SocialChoice.Ranking.MallowsRankFactorization
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/-- The geometric rank-power sum over the candidate positions. -/
noncomputable def candidateRankPowerSum (n : ℕ) (q : ℝ) : ℝ := ∑ i : Candidate n, q ^ (i : ℕ)

/-- The same geometric rank-power sum, indexed from the worst rank downward. -/
noncomputable def candidateRankReversePowerSum (n : ℕ) (q : ℝ) : ℝ := ∑ i : Candidate n, q ^ (n + 1 - (i : ℕ))

/-- The geometric rank-power sum over the prefix of ranks up to `k`. -/
noncomputable def candidateRankPrefixPowerSum
    (n : ℕ) (q : ℝ) (k : Fin (n + 1)) : ℝ := ∑ i : Candidate n, if (i : ℕ) ≤ k.val then q ^ (i : ℕ) else 0

noncomputable def candidateRankCrossDelta
    (n : ℕ) (qA qH : ℝ) (r : Candidate n) : ℝ :=
  qA ^ (r : ℕ) * candidateRankPowerSum n qH -
    qH ^ (r : ℕ) * candidateRankPowerSum n qA

noncomputable def candidateRankAdjacentCoeff
    (n : ℕ) (qA qH : ℝ) (k : ℕ) : ℝ :=
  ∑ r : Candidate n, ∑ s : Candidate n,
    if (r : ℕ) ≤ k ∧ k < (s : ℕ) then
      qH ^ ((r : ℕ) + (s : ℕ) - 1) *
        (candidateRankCrossDelta n qA qH r -
          qH * candidateRankCrossDelta n qA qH s)
    else
      0

noncomputable def candidateRankWeightedPrefixCrossDeltaSum
    (n : ℕ) (qA qH : ℝ) (k : ℕ) : ℝ :=
  ∑ r : Candidate n,
    if (r : ℕ) ≤ k then
      qH ^ (r : ℕ) * candidateRankCrossDelta n qA qH r
    else
      0

noncomputable def candidateRankWeightedSuffixCrossDeltaSum
    (n : ℕ) (qA qH : ℝ) (k : ℕ) : ℝ :=
  ∑ s : Candidate n,
    if k < (s : ℕ) then
      qH ^ (s : ℕ) * candidateRankCrossDelta n qA qH s
    else
      0

noncomputable def candidateRankPrefixWeightSum
    (n : ℕ) (q : ℝ) (k : ℕ) : ℝ := ∑ r : Candidate n, if (r : ℕ) ≤ k then q ^ (r : ℕ) else 0

noncomputable def candidateRankShiftedSuffixWeightSum
    (n : ℕ) (q : ℝ) (k : ℕ) : ℝ := ∑ s : Candidate n, if k < (s : ℕ) then q ^ ((s : ℕ) - 1) else 0

/-- Rank-power sum over all candidates except the removed rank, with lower
ranks unchanged and higher ranks shifted down by one. -/
noncomputable def candidateRankRemovalPowerSum
    (n : ℕ) (q : ℝ) (k : Candidate n) : ℝ :=
  ∑ r : Candidate n,
    if r < k then q ^ (r : ℕ)
    else if k < r then q ^ ((r : ℕ) - 1)
    else 0

/-- Rank-only numerator weight for the best remaining candidate after center
rank `k` has been removed. -/
noncomputable def candidateRankBestAfterRemovalWeight
    (n : ℕ) (q : ℝ) (k r : Candidate n) : ℝ :=
  if r < k then
    q ^ (r : ℕ) * candidateRankRemovalPowerSum n q k + q ^ ((r : ℕ) + (k : ℕ))
  else if k < r then
    q ^ (r : ℕ) * candidateRankRemovalPowerSum n q k +
      q ^ ((k : ℕ) + (r : ℕ) - 1)
  else
    0

theorem candidateRankRemovalPowerSum_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k : Candidate n) :
    0 < candidateRankRemovalPowerSum n q k := by
  simpa [candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum_pos n hq_pos k

theorem candidateRankRemovalPowerSum_nonneg
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k : Candidate n) :
    0 ≤ candidateRankRemovalPowerSum n q k :=
  by
    simpa [candidateRankRemovalPowerSum,
      AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
      AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum_nonneg n hq_pos k

theorem candidateRankBestAfterRemovalWeight_nonneg
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k r : Candidate n) :
    0 ≤ candidateRankBestAfterRemovalWeight n q k r := by
  simpa [candidateRankBestAfterRemovalWeight,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight,
    candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight_nonneg
      n hq_pos k r

theorem candidateRankRemovalPowerSum_eq_range
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankRemovalPowerSum n q k =
      ∑ m ∈ Finset.range (n + 1), q ^ m := by
  simpa [candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum_eq_range n q k

theorem candidateRankRemovalPowerSum_mul_one_sub
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankRemovalPowerSum n q k * (1 - q) = 1 - q ^ (n + 1) := by
  simpa [candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum_mul_one_sub n q k

@[simp] theorem candidateRankBestAfterRemovalWeight_self
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankBestAfterRemovalWeight n q k k = 0 := by
  simpa [candidateRankBestAfterRemovalWeight,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight,
    candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight_self n q k

theorem candidateRankBestAfterRemovalWeight_of_lt
    (n : ℕ) (q : ℝ) {k r : Candidate n} (hrk : r < k) :
    candidateRankBestAfterRemovalWeight n q k r =
      q ^ (r : ℕ) *
        (candidateRankRemovalPowerSum n q k + q ^ (k : ℕ)) := by
  simpa [candidateRankBestAfterRemovalWeight,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight,
    candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight_of_lt
      n q hrk

theorem candidateRankBestAfterRemovalWeight_of_gt
    (n : ℕ) (q : ℝ) {k r : Candidate n} (hkr : k < r) :
    candidateRankBestAfterRemovalWeight n q k r =
      q ^ ((r : ℕ) - 1) *
        (q * candidateRankRemovalPowerSum n q k + q ^ (k : ℕ)) := by
  simpa [candidateRankBestAfterRemovalWeight,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight,
    candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankBestAfterRemovalWeight_of_gt
      n q hkr

/--
Rank-only conditional top-gap summand.

For a first candidate at center rank `r`, this is the contribution of a possible
second candidate at center rank `s` after dividing out the common first-rank
Mallows factor.  It is the Lean version of the paper's conditional
`x_i - V_{-i}` gap.
-/
noncomputable def candidateRankConditionalGapTerm
    (q : ℝ) (value : Candidate n → ℝ) (r s : Candidate n) : ℝ :=
  if r < s then
    q ^ ((s : ℕ) - 1) * (value r - value s)
  else if s < r then
    q ^ (s : ℕ) * (value r - value s)
  else
    0

/-- Rank-only conditional first-minus-second gap for a fixed first rank. -/
noncomputable def candidateRankConditionalGap
    (n : ℕ) (q : ℝ) (value : Candidate n → ℝ) (r : Candidate n) : ℝ := ∑ s : Candidate n, candidateRankConditionalGapTerm q value r s

theorem candidateRankPowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankPowerSum n q := by
  simpa [candidateRankPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum_pos n hq_pos

theorem candidateRankReversePowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankReversePowerSum n q := by
  simpa [candidateRankReversePowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankReversePowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankReversePowerSum_pos n hq_pos

theorem candidateRankPowerSum_strict_mono
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_nonneg : 0 ≤ q₁) (hq_lt : q₁ < q₂) :
    candidateRankPowerSum n q₁ < candidateRankPowerSum n q₂ := by
  simpa [candidateRankPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum_strict_mono
      n hq₁_nonneg hq_lt

theorem natPower_mul_lt_mul_natPower
    {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : ℕ} (hij : i < j) :
    q₁ ^ j * q₂ ^ i < q₁ ^ i * q₂ ^ j :=
   AppliedModelingLib.SocialChoice.Ranking.natPower_mul_lt_mul_natPower
    hq₁_pos hq_lt hij

theorem candidateRankRemovalBoundaryFactor_cross_nonneg
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    (k : Candidate n) :
    0 ≤
      (candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
          (q₂ * candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ)) -
        (q₁ * candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
          (candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ)) := by
  let S₁ : ℝ := candidateRankRemovalPowerSum n q₁ k
  let S₂ : ℝ := candidateRankRemovalPowerSum n q₂ k
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  have hS₁_nonneg : 0 ≤ S₁ :=
    candidateRankRemovalPowerSum_nonneg n hq₁_pos k
  have hS₂_nonneg : 0 ≤ S₂ :=
    candidateRankRemovalPowerSum_nonneg n hq₂_pos k
  have hgeom₁ : S₁ * (1 - q₁) = 1 - q₁ ^ (n + 1) := by
    simpa [S₁] using candidateRankRemovalPowerSum_mul_one_sub n q₁ k
  have hgeom₂ : S₂ * (1 - q₂) = 1 - q₂ ^ (n + 1) := by
    simpa [S₂] using candidateRankRemovalPowerSum_mul_one_sub n q₂ k
  have hmain_rewrite :
      (S₁ + q₁ ^ (k : ℕ)) * (q₂ * S₂ + q₂ ^ (k : ℕ)) -
          (q₁ * S₁ + q₁ ^ (k : ℕ)) * (S₂ + q₂ ^ (k : ℕ)) =
        (q₂ - q₁) * S₁ * S₂ +
          (q₂ ^ (k : ℕ) * (1 - q₁ ^ (n + 1)) -
            q₁ ^ (k : ℕ) * (1 - q₂ ^ (n + 1))) := by
    rw [← hgeom₁, ← hgeom₂]
    ring
  have hprod_le :
      q₁ ^ (k : ℕ) * (1 - q₂ ^ (n + 1)) ≤
        q₂ ^ (k : ℕ) * (1 - q₁ ^ (n + 1)) := by
    have hpow_k : q₁ ^ (k : ℕ) ≤ q₂ ^ (k : ℕ) :=
      pow_le_pow_left₀ (le_of_lt hq₁_pos) (le_of_lt hq_lt) (k : ℕ)
    have hpow_tail : q₁ ^ (n + 1) ≤ q₂ ^ (n + 1) :=
      pow_le_pow_left₀ (le_of_lt hq₁_pos) (le_of_lt hq_lt) (n + 1)
    have hgap :
        1 - q₂ ^ (n + 1) ≤ 1 - q₁ ^ (n + 1) := by
      linarith
    have hgap_nonneg : 0 ≤ 1 - q₂ ^ (n + 1) :=
      sub_nonneg.mpr
        (pow_le_one₀ (le_of_lt hq₂_pos) (le_of_lt hq₂_lt_one))
    exact mul_le_mul hpow_k hgap hgap_nonneg
      (pow_nonneg (le_of_lt hq₂_pos) (k : ℕ))
  have hfactor_nonneg :
      0 ≤ (q₂ - q₁) * S₁ * S₂ :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr (le_of_lt hq_lt)) hS₁_nonneg)
      hS₂_nonneg
  have htail_nonneg :
      0 ≤ q₂ ^ (k : ℕ) * (1 - q₁ ^ (n + 1)) -
        q₁ ^ (k : ℕ) * (1 - q₂ ^ (n + 1)) :=
    sub_nonneg.mpr hprod_le
  change 0 ≤
    (S₁ + q₁ ^ (k : ℕ)) * (q₂ * S₂ + q₂ ^ (k : ℕ)) -
      (q₁ * S₁ + q₁ ^ (k : ℕ)) * (S₂ + q₂ ^ (k : ℕ))
  rw [hmain_rewrite]
  exact add_nonneg hfactor_nonneg htail_nonneg

theorem candidateRankBestAfterRemovalWeight_pairwise_cross_nonneg
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1) (k : Candidate n) :
    ∀ i j : Candidate n, i < j →
      0 ≤
        candidateRankBestAfterRemovalWeight n q₁ k i *
            candidateRankBestAfterRemovalWeight n q₂ k j -
          candidateRankBestAfterRemovalWeight n q₁ k j *
            candidateRankBestAfterRemovalWeight n q₂ k i := by
  intro i j hij
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  by_cases hik : i < k
  · by_cases hjk : j < k
    · rw [candidateRankBestAfterRemovalWeight_of_lt n q₁ hik,
        candidateRankBestAfterRemovalWeight_of_lt n q₂ hjk,
        candidateRankBestAfterRemovalWeight_of_lt n q₁ hjk,
        candidateRankBestAfterRemovalWeight_of_lt n q₂ hik]
      have hpow :
          0 ≤ q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
              q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) :=
        sub_nonneg.mpr (le_of_lt (by
          have h := natPower_mul_lt_mul_natPower hq₁_pos hq_lt
            (show (i : ℕ) < (j : ℕ) by exact hij)
          simpa [mul_comm, mul_left_comm, mul_assoc] using h))
      have hleft_nonneg :
          0 ≤ candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ) :=
        add_nonneg (candidateRankRemovalPowerSum_nonneg n hq₁_pos k)
          (pow_nonneg (le_of_lt hq₁_pos) (k : ℕ))
      have hright_nonneg :
          0 ≤ candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ) :=
        add_nonneg (candidateRankRemovalPowerSum_nonneg n hq₂_pos k)
          (pow_nonneg (le_of_lt hq₂_pos) (k : ℕ))
      have heq :
          q₁ ^ (i : ℕ) *
                (candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
              (q₂ ^ (j : ℕ) *
                (candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ))) -
            q₁ ^ (j : ℕ) *
                (candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
              (q₂ ^ (i : ℕ) *
                (candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ))) =
            (candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
              (candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ)) *
                (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
                  q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ)) := by
        ring
      rw [heq]
      exact mul_nonneg (mul_nonneg hleft_nonneg hright_nonneg) hpow
    · by_cases hkj : k < j
      · rw [candidateRankBestAfterRemovalWeight_of_lt n q₁ hik,
          candidateRankBestAfterRemovalWeight_of_gt n q₂ hkj,
          candidateRankBestAfterRemovalWeight_of_gt n q₁ hkj,
          candidateRankBestAfterRemovalWeight_of_lt n q₂ hik]
        let P₁ : ℝ := candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)
        let P₂ : ℝ := candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ)
        let T₁ : ℝ := q₁ * candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)
        let T₂ : ℝ := q₂ * candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ)
        have hcoeff :
            q₁ ^ ((j : ℕ) - 1) * q₂ ^ (i : ℕ) ≤
              q₁ ^ (i : ℕ) * q₂ ^ ((j : ℕ) - 1) :=
          le_of_lt (by
            have hik_nat : (i : ℕ) < (k : ℕ) := by exact hik
            have hkj_nat : (k : ℕ) < (j : ℕ) := by exact hkj
            have hij_pred : (i : ℕ) < (j : ℕ) - 1 := by omega
            have h := natPower_mul_lt_mul_natPower hq₁_pos hq_lt hij_pred
            simpa [mul_comm, mul_left_comm, mul_assoc] using h)
        have hboundary : T₁ * P₂ ≤ P₁ * T₂ := by
          have h := candidateRankRemovalBoundaryFactor_cross_nonneg
            n hq₁_pos hq_lt hq₂_lt_one k
          dsimp [P₁, P₂, T₁, T₂]
          exact sub_nonneg.mp h
        have hT₁_nonneg : 0 ≤ T₁ := by
          dsimp [T₁]
          exact add_nonneg
            (mul_nonneg (le_of_lt hq₁_pos)
              (candidateRankRemovalPowerSum_nonneg n hq₁_pos k))
            (pow_nonneg (le_of_lt hq₁_pos) (k : ℕ))
        have hP₂_nonneg : 0 ≤ P₂ := by
          dsimp [P₂]
          exact add_nonneg (candidateRankRemovalPowerSum_nonneg n hq₂_pos k)
            (pow_nonneg (le_of_lt hq₂_pos) (k : ℕ))
        have hcoeff_rhs_nonneg :
            0 ≤ q₁ ^ (i : ℕ) * q₂ ^ ((j : ℕ) - 1) :=
          mul_nonneg (pow_nonneg (le_of_lt hq₁_pos) (i : ℕ))
            (pow_nonneg (le_of_lt hq₂_pos) ((j : ℕ) - 1))
        have hprod :
            q₁ ^ ((j : ℕ) - 1) * q₂ ^ (i : ℕ) * (T₁ * P₂) ≤
              q₁ ^ (i : ℕ) * q₂ ^ ((j : ℕ) - 1) * (P₁ * T₂) :=
          mul_le_mul hcoeff hboundary
            (mul_nonneg hT₁_nonneg hP₂_nonneg) hcoeff_rhs_nonneg
        have heq :
            q₁ ^ (i : ℕ) * P₁ * (q₂ ^ ((j : ℕ) - 1) * T₂) -
                q₁ ^ ((j : ℕ) - 1) * T₁ * (q₂ ^ (i : ℕ) * P₂) =
              q₁ ^ (i : ℕ) * q₂ ^ ((j : ℕ) - 1) * (P₁ * T₂) -
                q₁ ^ ((j : ℕ) - 1) * q₂ ^ (i : ℕ) * (T₁ * P₂) := by
          ring
        rw [heq]
        exact sub_nonneg.mpr hprod
      · have hj_eq : j = k := by
          apply le_antisymm
          · exact le_of_not_gt hkj
          · exact le_of_not_gt hjk
        subst j
        rw [candidateRankBestAfterRemovalWeight_of_lt n q₁ hik,
          candidateRankBestAfterRemovalWeight_self,
          candidateRankBestAfterRemovalWeight_self,
          candidateRankBestAfterRemovalWeight_of_lt n q₂ hik]
        ring_nf
        exact le_rfl
  · by_cases hki : k < i
    · have hkj : k < j := lt_trans hki hij
      rw [candidateRankBestAfterRemovalWeight_of_gt n q₁ hki,
        candidateRankBestAfterRemovalWeight_of_gt n q₂ hkj,
        candidateRankBestAfterRemovalWeight_of_gt n q₁ hkj,
        candidateRankBestAfterRemovalWeight_of_gt n q₂ hki]
      have hpow :
          0 ≤ q₁ ^ ((i : ℕ) - 1) * q₂ ^ ((j : ℕ) - 1) -
              q₁ ^ ((j : ℕ) - 1) * q₂ ^ ((i : ℕ) - 1) :=
        sub_nonneg.mpr (le_of_lt (by
          have hij_nat : (i : ℕ) < (j : ℕ) := by exact hij
          have hi_pos : 0 < (i : ℕ) :=
            lt_of_le_of_lt (Nat.zero_le (k : ℕ)) hki
          have hij_pred : (i : ℕ) - 1 < (j : ℕ) - 1 := by omega
          have h := natPower_mul_lt_mul_natPower hq₁_pos hq_lt hij_pred
          simpa [mul_comm, mul_left_comm, mul_assoc] using h))
      have hleft_nonneg :
          0 ≤ q₁ * candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ) :=
        add_nonneg
          (mul_nonneg (le_of_lt hq₁_pos)
            (candidateRankRemovalPowerSum_nonneg n hq₁_pos k))
          (pow_nonneg (le_of_lt hq₁_pos) (k : ℕ))
      have hright_nonneg :
          0 ≤ q₂ * candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ) :=
        add_nonneg
          (mul_nonneg (le_of_lt hq₂_pos)
            (candidateRankRemovalPowerSum_nonneg n hq₂_pos k))
          (pow_nonneg (le_of_lt hq₂_pos) (k : ℕ))
      have heq :
          q₁ ^ ((i : ℕ) - 1) *
                (q₁ * candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
              (q₂ ^ ((j : ℕ) - 1) *
                (q₂ * candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ))) -
            q₁ ^ ((j : ℕ) - 1) *
                (q₁ * candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
              (q₂ ^ ((i : ℕ) - 1) *
                (q₂ * candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ))) =
            (q₁ * candidateRankRemovalPowerSum n q₁ k + q₁ ^ (k : ℕ)) *
              (q₂ * candidateRankRemovalPowerSum n q₂ k + q₂ ^ (k : ℕ)) *
                (q₁ ^ ((i : ℕ) - 1) * q₂ ^ ((j : ℕ) - 1) -
                  q₁ ^ ((j : ℕ) - 1) * q₂ ^ ((i : ℕ) - 1)) := by
        ring
      rw [heq]
      exact mul_nonneg (mul_nonneg hleft_nonneg hright_nonneg) hpow
    · have hi_eq : i = k := by
        apply le_antisymm
        · exact le_of_not_gt hki
        · exact le_of_not_gt hik
      subst i
      have hkj : k < j := hij
      rw [candidateRankBestAfterRemovalWeight_self,
        candidateRankBestAfterRemovalWeight_of_gt n q₂ hkj,
        candidateRankBestAfterRemovalWeight_of_gt n q₁ hkj,
        candidateRankBestAfterRemovalWeight_self]
      ring_nf
      exact le_rfl

theorem rankPower_mul_lt_mul_rankPower
    {n : ℕ} {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : Candidate n} (hij : i < j) :
    q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) <
      q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  obtain ⟨d, hd_pos, hd_eq⟩ :
      ∃ d : ℕ, 0 < d ∧ (j : ℕ) = (i : ℕ) + d := by
    refine ⟨(j : ℕ) - (i : ℕ), Nat.sub_pos_of_lt hij, ?_⟩
    exact (Nat.add_sub_of_le (le_of_lt hij)).symm
  have hpow : q₁ ^ d < q₂ ^ d :=
    pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (Nat.ne_of_gt hd_pos)
  have hscale : 0 < q₁ ^ (i : ℕ) * q₂ ^ (i : ℕ) :=
    mul_pos (pow_pos hq₁_pos (i : ℕ)) (pow_pos hq₂_pos (i : ℕ))
  have hmul := mul_lt_mul_of_pos_left hpow hscale
  rw [hd_eq, pow_add, pow_add]
  nlinarith

/-- Endpoint-position exponent for a correctly ordered pair in the reduced
Mallows pair calculation from Appendix F.1.  The type `Candidate m` represents
the interval of candidates from the better endpoint to the worse endpoint,
including both endpoints. -/
def pairPositionCorrectExp (m : ℕ) (betterPos worsePos : Candidate m) : ℕ := betterPos.val + (m + 1 - worsePos.val)

/-- Endpoint-position exponent for an incorrectly ordered pair in the reduced
Mallows pair calculation from Appendix F.1. -/
def pairPositionWrongExp (m : ℕ) (betterPos worsePos : Candidate m) : ℕ := betterPos.val + (m + 1 - worsePos.val) - 1

/-- Rank-only contribution of one endpoint placement to the correctly ordered
side of Lemma 8's pairwise Mallows odds. -/
noncomputable def pairPositionCorrectTerm
    (m : ℕ) (q : ℝ) (p : Candidate m × Candidate m) : ℝ := if p.1 < p.2 then q ^ pairPositionCorrectExp m p.1 p.2 else 0

/-- Rank-only contribution of one endpoint placement to the incorrectly ordered
side of Lemma 8's pairwise Mallows odds. -/
noncomputable def pairPositionWrongTerm
    (m : ℕ) (q : ℝ) (p : Candidate m × Candidate m) : ℝ := if p.2 < p.1 then q ^ pairPositionWrongExp m p.1 p.2 else 0

/-- Reduced rank-only weight of correctly ordering a fixed pair. -/
noncomputable def pairPositionCorrectWeight (m : ℕ) (q : ℝ) : ℝ := ∑ p : Candidate m × Candidate m, pairPositionCorrectTerm m q p

/-- Reduced rank-only weight of incorrectly ordering a fixed pair. -/
noncomputable def pairPositionWrongWeight (m : ℕ) (q : ℝ) : ℝ := ∑ p : Candidate m × Candidate m, pairPositionWrongTerm m q p

theorem pairPositionCorrectExp_le
    (m : ℕ) {betterPos worsePos : Candidate m} (hpos : betterPos < worsePos) :
    pairPositionCorrectExp m betterPos worsePos ≤ m := by
  unfold pairPositionCorrectExp
  have hlt : betterPos.val < worsePos.val := hpos
  have hworse : worsePos.val < m + 2 := worsePos.isLt
  omega

theorem pairPositionWrongExp_gt
    (m : ℕ) {betterPos worsePos : Candidate m} (hpos : worsePos < betterPos) :
    m < pairPositionWrongExp m betterPos worsePos := by
  unfold pairPositionWrongExp
  have hlt : worsePos.val < betterPos.val := hpos
  have hbetter : betterPos.val < m + 2 := betterPos.isLt
  have hworse : worsePos.val < m + 2 := worsePos.isLt
  omega

theorem pairPositionCorrectExp_lt_wrongExp
    (m : ℕ) {correct wrong : Candidate m × Candidate m}
    (hcorrect : correct.1 < correct.2) (hwrong : wrong.2 < wrong.1) :
    pairPositionCorrectExp m correct.1 correct.2 <
      pairPositionWrongExp m wrong.1 wrong.2 :=
   lt_of_le_of_lt
    (pairPositionCorrectExp_le m hcorrect)
    (pairPositionWrongExp_gt m hwrong)

theorem natPower_cross_nonneg_of_le
    {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {a b : ℕ} (hab : a ≤ b) :
    0 ≤ q₁ ^ a * q₂ ^ b - q₂ ^ a * q₁ ^ b := by
  by_cases h_eq : a = b
  · subst b
    have hzero :
        q₁ ^ a * q₂ ^ a - q₂ ^ a * q₁ ^ a = 0 := by
      ring
    rw [hzero]
  · have hlt_ab : a < b := lt_of_le_of_ne hab h_eq
    exact le_of_lt (by
      have h := natPower_mul_lt_mul_natPower
        (q₁ := q₁) (q₂ := q₂) hq₁_pos hq_lt hlt_ab
      exact sub_pos.mpr (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h))

theorem natPower_cross_pos_of_lt
    {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {a b : ℕ} (hab : a < b) :
    0 < q₁ ^ a * q₂ ^ b - q₂ ^ a * q₁ ^ b := by
  have h := natPower_mul_lt_mul_natPower
    (q₁ := q₁) (q₂ := q₂) hq₁_pos hq_lt hab
  exact sub_pos.mpr (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h)

theorem pairPositionTerm_cross_nonneg
    (m : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    (correct wrong : Candidate m × Candidate m) :
    0 ≤
      pairPositionCorrectTerm m q₁ correct *
          pairPositionWrongTerm m q₂ wrong -
        pairPositionCorrectTerm m q₂ correct *
          pairPositionWrongTerm m q₁ wrong := by
  by_cases hcorrect : correct.1 < correct.2
  · by_cases hwrong : wrong.2 < wrong.1
    · simp [pairPositionCorrectTerm, pairPositionWrongTerm, hcorrect, hwrong]
      exact sub_nonneg.mp
        (natPower_cross_nonneg_of_le hq₁_pos hq_lt
          (le_of_lt (pairPositionCorrectExp_lt_wrongExp m hcorrect hwrong)))
    · simp [pairPositionWrongTerm, hwrong]
  · simp [pairPositionCorrectTerm, hcorrect]

theorem pairPositionTerm_cross_pos
    (m : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    (correct wrong : Candidate m × Candidate m)
    (hcorrect : correct.1 < correct.2) (hwrong : wrong.2 < wrong.1) :
    0 <
      pairPositionCorrectTerm m q₁ correct *
          pairPositionWrongTerm m q₂ wrong -
        pairPositionCorrectTerm m q₂ correct *
          pairPositionWrongTerm m q₁ wrong := by
  simp [pairPositionCorrectTerm, pairPositionWrongTerm, hcorrect, hwrong]
  exact sub_pos.mp
    (natPower_cross_pos_of_lt hq₁_pos hq_lt
      (pairPositionCorrectExp_lt_wrongExp m hcorrect hwrong))

theorem pairPositionCorrectWrong_cross_pos
    (m : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂) :
    0 <
      pairPositionCorrectWeight m q₁ * pairPositionWrongWeight m q₂ -
        pairPositionCorrectWeight m q₂ * pairPositionWrongWeight m q₁ := by
  classical
  let last : Candidate m := ⟨m + 1, by omega⟩
  let correct₀ : Candidate m × Candidate m := (0, last)
  let wrong₀ : Candidate m × Candidate m := (last, 0)
  have hcorrect₀ : correct₀.1 < correct₀.2 := by
    change (0 : ℕ) < m + 1
    omega
  have hwrong₀ : wrong₀.2 < wrong₀.1 := by
    change (0 : ℕ) < m + 1
    omega
  have hsum_eq :
      pairPositionCorrectWeight m q₁ * pairPositionWrongWeight m q₂ -
          pairPositionCorrectWeight m q₂ * pairPositionWrongWeight m q₁ =
        ∑ correct : Candidate m × Candidate m,
          ∑ wrong : Candidate m × Candidate m,
            (pairPositionCorrectTerm m q₁ correct *
                pairPositionWrongTerm m q₂ wrong -
              pairPositionCorrectTerm m q₂ correct *
                pairPositionWrongTerm m q₁ wrong) := by
    unfold pairPositionCorrectWeight pairPositionWrongWeight
    rw [Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro correct _
    rw [← Finset.sum_sub_distrib]
  rw [hsum_eq]
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (a₀ := correct₀)
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (a₀ := wrong₀)
    · exact pairPositionTerm_cross_pos m hq₁_pos hq_lt
        correct₀ wrong₀ hcorrect₀ hwrong₀
    · intro wrong
      exact pairPositionTerm_cross_nonneg m hq₁_pos hq_lt correct₀ wrong
  · intro correct
    exact Finset.sum_nonneg (by
      intro wrong _
      exact pairPositionTerm_cross_nonneg m hq₁_pos hq_lt correct wrong)

/-- Reduced rank-only probability of correctly ordering a fixed pair. -/
noncomputable def pairPositionCorrectProb (m : ℕ) (q : ℝ) : ℝ :=
  pairPositionCorrectWeight m q /
    (pairPositionCorrectWeight m q + pairPositionWrongWeight m q)

theorem pairPositionCorrectWeight_pos
    (m : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < pairPositionCorrectWeight m q := by
  classical
  let last : Candidate m := ⟨m + 1, by omega⟩
  let correct₀ : Candidate m × Candidate m := (0, last)
  have hcorrect₀ : correct₀.1 < correct₀.2 := by
    change (0 : ℕ) < m + 1
    omega
  unfold pairPositionCorrectWeight
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (a₀ := correct₀)
  · simp [pairPositionCorrectTerm, hcorrect₀, pairPositionCorrectExp]
    exact pow_pos hq_pos _
  · intro correct
    unfold pairPositionCorrectTerm
    by_cases hcorrect : correct.1 < correct.2
    · exact by
        rw [if_pos hcorrect]
        exact pow_nonneg (le_of_lt hq_pos) _
    · rw [if_neg hcorrect]

theorem pairPositionWrongWeight_pos
    (m : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < pairPositionWrongWeight m q := by
  classical
  let last : Candidate m := ⟨m + 1, by omega⟩
  let wrong₀ : Candidate m × Candidate m := (last, 0)
  have hwrong₀ : wrong₀.2 < wrong₀.1 := by
    change (0 : ℕ) < m + 1
    omega
  unfold pairPositionWrongWeight
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (a₀ := wrong₀)
  · simp [pairPositionWrongTerm, hwrong₀, pairPositionWrongExp]
    exact pow_pos hq_pos _
  · intro wrong
    unfold pairPositionWrongTerm
    by_cases hwrong : wrong.2 < wrong.1
    · exact by
        rw [if_pos hwrong]
        exact pow_nonneg (le_of_lt hq_pos) _
    · rw [if_neg hwrong]

theorem pairPositionCorrectProb_strictAnti
    (m : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂) :
    pairPositionCorrectProb m q₂ < pairPositionCorrectProb m q₁ := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  let A₁ : ℝ := pairPositionCorrectWeight m q₁
  let B₁ : ℝ := pairPositionWrongWeight m q₁
  let A₂ : ℝ := pairPositionCorrectWeight m q₂
  let B₂ : ℝ := pairPositionWrongWeight m q₂
  have hA₁_pos : 0 < A₁ := pairPositionCorrectWeight_pos m hq₁_pos
  have hB₁_pos : 0 < B₁ := pairPositionWrongWeight_pos m hq₁_pos
  have hA₂_pos : 0 < A₂ := pairPositionCorrectWeight_pos m hq₂_pos
  have hB₂_pos : 0 < B₂ := pairPositionWrongWeight_pos m hq₂_pos
  have hcross : 0 < A₁ * B₂ - A₂ * B₁ := by
    simpa [A₁, B₁, A₂, B₂] using
      pairPositionCorrectWrong_cross_pos m hq₁_pos hq_lt
  unfold pairPositionCorrectProb
  change A₂ / (A₂ + B₂) < A₁ / (A₁ + B₁)
  have hden₁_pos : 0 < A₁ + B₁ := add_pos hA₁_pos hB₁_pos
  have hden₂_pos : 0 < A₂ + B₂ := add_pos hA₂_pos hB₂_pos
  rw [div_lt_div_iff₀ hden₂_pos hden₁_pos]
  nlinarith [hcross]

/--
Bridge data for the final step of Appendix F.1 Lemma 8: the actual Mallows
correct/wrong weights for a pair are a common positive scale times the reduced
endpoint-position weights.

The paper obtains this by canceling candidates outside the interval and
inversions among candidates inside the interval.
-/
structure PairPositionReduction
    {n : ℕ} (M : MallowsSpec n) (c d : Candidate n) (m : ℕ) where
  scale : ℝ
  scale_pos : 0 < scale
  correct_eq :
    M.pairCorrectWeight c d =
      scale * pairPositionCorrectWeight m M.q
  wrong_eq :
    M.pairWrongWeight c d =
      scale * pairPositionWrongWeight m M.q

theorem pairCorrectProb_eq_pairPositionCorrectProb_of_reduction
    {n m : ℕ} (M : MallowsSpec n) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d)
    (red : PairPositionReduction M c d m) :
    M.pairCorrectProb c d = pairPositionCorrectProb m M.q := by
  rw [M.pairCorrectProb_eq_pairCorrectWeight_div_correct_add_wrong hcd]
  rw [red.correct_eq, red.wrong_eq]
  unfold pairPositionCorrectProb
  have hscale_ne : red.scale ≠ 0 := ne_of_gt red.scale_pos
  have hden_pos :
      0 <
        pairPositionCorrectWeight m M.q +
          pairPositionWrongWeight m M.q :=
    add_pos (pairPositionCorrectWeight_pos m M.q_pos)
      (pairPositionWrongWeight_pos m M.q_pos)
  field_simp [hscale_ne, ne_of_gt hden_pos]

/--
Actual Mallows pair-correct probabilities are monotone once the unnormalised
correct/wrong pair weights satisfy the cross-multiplied odds comparison.

This is the denominator-clearing algebra in Appendix F.1; the remaining
paper-specific work is to prove the cross inequality, e.g. by the
`PairPositionReduction` cancellation bridge.
-/
theorem pairCorrectProb_lt_of_pairWeight_cross
    {n : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hcd_less : rankOf Mless.center c < rankOf Mless.center d)
    (hcross :
      0 <
        Mmore.pairCorrectWeight c d * Mless.pairWrongWeight c d -
          Mless.pairCorrectWeight c d * Mmore.pairWrongWeight c d) :
    Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d := by
  rw [Mless.pairCorrectProb_eq_pairCorrectWeight_div_correct_add_wrong hcd_less,
    Mmore.pairCorrectProb_eq_pairCorrectWeight_div_correct_add_wrong hcd_more]
  let A₁ : ℝ := Mless.pairCorrectWeight c d
  let B₁ : ℝ := Mless.pairWrongWeight c d
  let A₂ : ℝ := Mmore.pairCorrectWeight c d
  let B₂ : ℝ := Mmore.pairWrongWeight c d
  change A₁ / (A₁ + B₁) < A₂ / (A₂ + B₂)
  have hden₁_pos : 0 < A₁ + B₁ := by
    simpa [A₁, B₁] using
      (by
        rw [Mless.pairCorrectWeight_add_pairWrongWeight_eq_partition hcd_less]
        exact Mless.partition_pos)
  have hden₂_pos : 0 < A₂ + B₂ := by
    simpa [A₂, B₂] using
      (by
        rw [Mmore.pairCorrectWeight_add_pairWrongWeight_eq_partition hcd_more]
        exact Mmore.partition_pos)
  rw [div_lt_div_iff₀ hden₁_pos hden₂_pos]
  have hcross' : 0 < A₂ * B₁ - A₁ * B₂ := by
    simpa [A₁, B₁, A₂, B₂, mul_comm, mul_left_comm, mul_assoc] using hcross
  nlinarith

/-- A pair-position reduction supplies the actual correct/wrong weight cross
inequality used by the normalized probability bridge. -/
theorem pairWeight_cross_pos_of_pairPositionReduction
    {n m : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (red_more : PairPositionReduction Mmore c d m)
    (red_less : PairPositionReduction Mless c d m)
    (hq_lt : Mmore.q < Mless.q) :
    0 <
      Mmore.pairCorrectWeight c d * Mless.pairWrongWeight c d -
        Mless.pairCorrectWeight c d * Mmore.pairWrongWeight c d := by
  have hpos_scale : 0 < red_more.scale * red_less.scale :=
    mul_pos red_more.scale_pos red_less.scale_pos
  have hcore :
      0 <
        pairPositionCorrectWeight m Mmore.q *
            pairPositionWrongWeight m Mless.q -
          pairPositionCorrectWeight m Mless.q *
            pairPositionWrongWeight m Mmore.q :=
    pairPositionCorrectWrong_cross_pos m Mmore.q_pos hq_lt
  rw [red_more.correct_eq, red_more.wrong_eq,
    red_less.correct_eq, red_less.wrong_eq]
  have hfactor :
      red_more.scale * pairPositionCorrectWeight m Mmore.q *
            (red_less.scale * pairPositionWrongWeight m Mless.q) -
          red_less.scale * pairPositionCorrectWeight m Mless.q *
            (red_more.scale * pairPositionWrongWeight m Mmore.q) =
        (red_more.scale * red_less.scale) *
          (pairPositionCorrectWeight m Mmore.q *
              pairPositionWrongWeight m Mless.q -
            pairPositionCorrectWeight m Mless.q *
              pairPositionWrongWeight m Mmore.q) := by
    ring
  rw [hfactor]
  exact mul_pos hpos_scale hcore

theorem pairCorrectProb_lt_of_pairPositionReduction
    {n m : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hcd_less : rankOf Mless.center c < rankOf Mless.center d)
    (red_more : PairPositionReduction Mmore c d m)
    (red_less : PairPositionReduction Mless c d m)
    (hq_lt : Mmore.q < Mless.q) :
    Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d :=
   pairCorrectProb_lt_of_pairWeight_cross hcd_more hcd_less
    (pairWeight_cross_pos_of_pairPositionReduction red_more red_less hq_lt)

theorem weightedRankPower_pair_add_pos
    {n : ℕ} {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    {i j : Candidate n} (hij : i < j) :
    0 <
      q₂ ^ (i : ℕ) *
          (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) +
        q₂ ^ (j : ℕ) *
          (q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) -
            q₂ ^ (j : ℕ) * q₁ ^ (i : ℕ)) := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  obtain ⟨d, hd_pos, hd_eq⟩ :
      ∃ d : ℕ, 0 < d ∧ (j : ℕ) = (i : ℕ) + d := by
    refine ⟨(j : ℕ) - (i : ℕ), Nat.sub_pos_of_lt hij, ?_⟩
    exact (Nat.add_sub_of_le (le_of_lt hij)).symm
  have hpow_lt : q₁ ^ d < q₂ ^ d :=
    pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (Nat.ne_of_gt hd_pos)
  have hpow_one : q₂ ^ d < 1 :=
    pow_lt_one₀ (le_of_lt hq₂_pos) hq₂_lt_one (Nat.ne_of_gt hd_pos)
  have hfactor :
      q₂ ^ (i : ℕ) *
          (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) +
        q₂ ^ (j : ℕ) *
          (q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) -
            q₂ ^ (j : ℕ) * q₁ ^ (i : ℕ)) =
        q₁ ^ (i : ℕ) * q₂ ^ (i : ℕ) * q₂ ^ (i : ℕ) *
          ((q₂ ^ d - q₁ ^ d) * (1 - q₂ ^ d)) := by
    rw [hd_eq, pow_add, pow_add]
    ring
  rw [hfactor]
  exact mul_pos
    (mul_pos (mul_pos (pow_pos hq₁_pos (i : ℕ))
      (pow_pos hq₂_pos (i : ℕ))) (pow_pos hq₂_pos (i : ℕ)))
    (mul_pos (sub_pos.mpr hpow_lt) (sub_pos.mpr hpow_one))

theorem weightedRankPower_pair_add_nonneg
    {n : ℕ} {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    {i j : Candidate n} (hij : i < j) :
    0 ≤
      q₂ ^ (i : ℕ) *
          (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) +
        q₂ ^ (j : ℕ) *
          (q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) -
            q₂ ^ (j : ℕ) * q₁ ^ (i : ℕ)) := le_of_lt (weightedRankPower_pair_add_pos hq₁_pos hq_lt hq₂_lt_one hij)

/-- Adjacent value gap between center positions `k` and `k+1`. -/
noncomputable def centerAdjacentGapAt {n : ℕ}
    (ρ : Ranking n) (value : Candidate n → ℝ) (k : ℕ) : ℝ :=
  if hk : k + 1 < n + 2 then
    value (ρ ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩) -
      value (ρ ⟨k + 1, hk⟩)
  else
    0

theorem centerAdjacentGapAt_pos_of_strictlyOrderedBy
    {n : ℕ} {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) {k : ℕ} (hk : k + 1 < n + 2) :
    0 < centerAdjacentGapAt ρ value k := by
  unfold centerAdjacentGapAt
  simp [hk]
  exact hvalue
    (show rankOf ρ (ρ ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩) <
        rankOf ρ (ρ ⟨k + 1, hk⟩) by
      simp [rankOf])

theorem value_sub_eq_sum_centerAdjacentGapAt
    {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ)
    {c d : Candidate n} (hlt : rankOf ρ c < rankOf ρ d) :
    value c - value d =
      ∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        centerAdjacentGapAt ρ value k := by
  classical
  let f : ℕ → ℝ := fun k =>
    if hk : k < n + 2 then value (ρ ⟨k, hk⟩) else 0
  have hle : (rankOf ρ c).val ≤ (rankOf ρ d).val := le_of_lt hlt
  have htel :
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        (f k - f (k + 1))) =
        f (rankOf ρ c).val - f (rankOf ρ d).val := by
    let a := (rankOf ρ c).val
    let b := (rankOf ρ d).val
    have hle' : a ≤ b := hle
    have hshift :
        (∑ k ∈ Finset.Ico a b, f (k + 1)) =
          ∑ k ∈ Finset.Ico (a + 1) (b + 1), f k := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Finset.sum_Ico_add' f a b 1)
    have hb :
        (∑ k ∈ Finset.range (b + 1), f k) -
            (∑ k ∈ Finset.range b, f k) = f b :=
      Finset.sum_range_succ_sub_sum f
    have ha :
        (∑ k ∈ Finset.range (a + 1), f k) -
            (∑ k ∈ Finset.range a, f k) = f a :=
      Finset.sum_range_succ_sub_sum f
    calc
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        (f k - f (k + 1)))
          = (∑ k ∈ Finset.Ico a b, f k) -
              (∑ k ∈ Finset.Ico a b, f (k + 1)) := by
                simp [a, b, Finset.sum_sub_distrib]
      _ = (∑ k ∈ Finset.range b, f k) - (∑ k ∈ Finset.range a, f k) -
              ((∑ k ∈ Finset.range (b + 1), f k) -
                (∑ k ∈ Finset.range (a + 1), f k)) := by
                rw [Finset.sum_Ico_eq_sub f hle', hshift,
                  Finset.sum_Ico_eq_sub f (Nat.succ_le_succ hle')]
      _ = f a - f b := by
                linarith
      _ = f (rankOf ρ c).val - f (rankOf ρ d).val := by
                simp [a, b]
  have hsum :
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        centerAdjacentGapAt ρ value k) =
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        (f k - f (k + 1))) := by
    refine Finset.sum_congr rfl ?_
    intro k hk_mem
    have hk_lt_s : k < (rankOf ρ d).val := (Finset.mem_Ico.mp hk_mem).2
    have hk1 : k + 1 < n + 2 := by
      omega
    have hk0 : k < n + 2 := Nat.lt_trans (Nat.lt_succ_self k) hk1
    simp [centerAdjacentGapAt, f, hk1, hk0]
  rw [hsum, htel]
  simp [f, rankOf]

theorem candidateRankConditionalGap_succ_lt
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) {value : Candidate n → ℝ}
    (hvalue : ∀ i j : Candidate n, i < j → value j < value i)
    (k : Fin (n + 1)) :
    candidateRankConditionalGap n q value k.succ <
      candidateRankConditionalGap n q value (Fin.castSucc k) := by
  classical
  let r0 : Candidate n := Fin.castSucc k
  let r1 : Candidate n := k.succ
  have hr01 : r0 < r1 := by
    change k.val < k.val + 1
    omega
  have hgap : 0 < value r0 - value r1 := sub_pos.mpr (hvalue r0 r1 hr01)
  rw [← sub_pos]
  unfold candidateRankConditionalGap
  rw [← Finset.sum_sub_distrib]
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := r0)
  · have hr1_not_lt_r0 : ¬r1 < r0 := not_lt_of_gt hr01
    have hneg : q ^ (r0 : ℕ) * (value r1 - value r0) < 0 := by
      nlinarith [mul_pos (pow_pos hq_pos (r0 : ℕ)) hgap]
    simpa [candidateRankConditionalGapTerm, r0, r1, hr01, hr1_not_lt_r0] using hneg
  · intro s
    have hcases : s < r0 ∨ s = r0 ∨ s = r1 ∨ r1 < s := by
      by_cases hs_lt : (s : ℕ) < k.val
      · exact Or.inl (by simpa [r0] using hs_lt)
      · by_cases hs_eq0 : (s : ℕ) = k.val
        · exact Or.inr (Or.inl (Fin.ext (by simpa [r0] using hs_eq0)))
        · by_cases hs_eq1 : (s : ℕ) = k.val + 1
          · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [r1] using hs_eq1))))
          · have hs_gt : k.val + 1 < (s : ℕ) := by omega
            exact Or.inr (Or.inr (Or.inr (by simpa [r1] using hs_gt)))
    rcases hcases with hs_lt | hs_eq0 | hs_eq1 | hr1_lt_s
    · have hr0_not_lt_s : ¬r0 < s := not_lt_of_gt hs_lt
      have hr1_not_lt_s : ¬r1 < s := by
        intro h
        exact not_lt_of_gt (lt_trans hs_lt hr01) h
      have hs_lt_r1 : s < r1 := lt_trans hs_lt hr01
      have hcoeff : 0 ≤ q ^ (s : ℕ) := pow_nonneg (le_of_lt hq_pos) (s : ℕ)
      have hterm :
          candidateRankConditionalGapTerm q value r0 s -
              candidateRankConditionalGapTerm q value r1 s =
            q ^ (s : ℕ) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hs_lt, hs_lt_r1,
          hr0_not_lt_s, hr1_not_lt_s]
        ring
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)
    · subst s
      have hr1_not_lt_r0 : ¬r1 < r0 := not_lt_of_gt hr01
      have hcoeff : 0 ≤ q ^ (r0 : ℕ) := pow_nonneg (le_of_lt hq_pos) (r0 : ℕ)
      have hterm :
          candidateRankConditionalGapTerm q value r0 r0 -
              candidateRankConditionalGapTerm q value r1 r0 =
            q ^ (r0 : ℕ) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hr01, hr1_not_lt_r0]
        ring
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)
    · subst s
      have hr1_not_lt_r0 : ¬r1 < r0 := not_lt_of_gt hr01
      have hr1_pred : (r1 : ℕ) - 1 = (r0 : ℕ) := by
        simp [r0, r1]
      have hcoeff : 0 ≤ q ^ ((r1 : ℕ) - 1) :=
        pow_nonneg (le_of_lt hq_pos) ((r1 : ℕ) - 1)
      have hterm :
          candidateRankConditionalGapTerm q value r0 r1 -
              candidateRankConditionalGapTerm q value r1 r1 =
            q ^ ((r1 : ℕ) - 1) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hr01, hr1_pred]
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)
    · have hr0_lt_s : r0 < s := lt_trans hr01 hr1_lt_s
      have hs_not_lt_r0 : ¬s < r0 := not_lt_of_gt hr0_lt_s
      have hs_not_lt_r1 : ¬s < r1 := not_lt_of_gt hr1_lt_s
      have hcoeff : 0 ≤ q ^ ((s : ℕ) - 1) :=
        pow_nonneg (le_of_lt hq_pos) ((s : ℕ) - 1)
      have hterm :
          candidateRankConditionalGapTerm q value r0 s -
              candidateRankConditionalGapTerm q value r1 s =
            q ^ ((s : ℕ) - 1) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hr0_lt_s, hr1_lt_s]
        ring
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)

theorem candidateRankConditionalGap_strictAnti
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) {value : Candidate n → ℝ}
    (hvalue : ∀ i j : Candidate n, i < j → value j < value i) :
    StrictAnti (candidateRankConditionalGap n q value) :=
   Fin.strictAnti_iff_succ_lt.mpr
    (candidateRankConditionalGap_succ_lt n hq_pos hvalue)

theorem candidateRankPowerSum_mul_one_sub (n : ℕ) (q : ℝ) :
    candidateRankPowerSum n q * (1 - q) = 1 - q ^ (n + 2) := by
  simpa [candidateRankPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum_mul_one_sub n q

theorem candidateRankPowerSum_inner_nonneg
    {n : ℕ} {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    {r s : Candidate n} (hrs : r < s) :
    0 ≤ (candidateRankPowerSum n q - q ^ (r : ℕ)) -
      q * (candidateRankPowerSum n q - q ^ (s : ℕ)) := by
  simpa [candidateRankPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum_inner_nonneg
      hq_nonneg hq_le_one hrs

theorem candidateRankPowerSum_inner_pos_zero_one
    {n : ℕ} (hn : 0 < n) {q : ℝ} (hq_pos : 0 < q) (hq_lt_one : q < 1) :
    0 < (candidateRankPowerSum n q - q ^ (0 : ℕ)) -
      q * (candidateRankPowerSum n q - q ^ (1 : ℕ)) := by
  simpa [candidateRankPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum] using
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum_inner_pos_zero_one
      (n := n) hn hq_pos hq_lt_one

/-- The fiber of rankings whose first center-rank is `r`, for the identity center. -/
noncomputable def reflFirstChoiceFiber (n : ℕ) (r : Candidate n) :
    Finset (Ranking n) := by
  classical
  exact Finset.univ.filter (fun τ => r = firstChoice τ)

/-- Unnormalised identity-center first-choice Mallows mass. -/
noncomputable def reflFirstWeight (n : ℕ) (q : ℝ) (r : Candidate n) : ℝ :=
  ∑ τ ∈ reflFirstChoiceFiber n r,
    q ^ kendallTau (Equiv.refl (Candidate n)) τ

theorem reflFirstWeight_eq_rank_mul_zero
    (n : ℕ) (q : ℝ) (r : Candidate n) :
    reflFirstWeight n q r =
      q ^ (r : ℕ) * reflFirstWeight n q 0 := by
  classical
  let E : Ranking n := Fin.cycleRange r
  unfold reflFirstWeight
  calc
    ∑ τ ∈ reflFirstChoiceFiber n r,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ
        = ∑ σ ∈ reflFirstChoiceFiber n 0,
            q ^ (r : ℕ) *
              q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          refine Finset.sum_bij
            (i := fun τ _ => τ.trans E) ?hi ?hinj ?hsurj ?hweight
          · intro τ hτ
            have hfirst : firstChoice τ = r :=
              (Finset.mem_filter.mp hτ).2.symm
            unfold reflFirstChoiceFiber
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [firstChoice_trans, hfirst]
            simp [E, Fin.cycleRange_self]
          · intro τ₁ _ τ₂ _ h
            apply Equiv.ext
            intro x
            exact E.injective (Equiv.ext_iff.mp h x)
          · intro σ hσ
            refine ⟨σ.trans E.symm, ?_, ?_⟩
            · have hfirst : firstChoice σ = 0 :=
                (Finset.mem_filter.mp hσ).2.symm
              have hcycle : E.symm 0 = r := by
                change (Fin.cycleRange r).symm 0 = r
                exact Fin.cycleRange_symm_zero r
              unfold reflFirstChoiceFiber
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [firstChoice_trans, hfirst, hcycle]
            · ext x
              simp [E]
          · intro τ hτ
            have hfirst : firstChoice τ = r :=
              (Finset.mem_filter.mp hτ).2.symm
            have hfirst_apply : τ 0 = r := by
              simpa [firstChoice] using hfirst
            have hkend :
                kendallTau (Equiv.refl (Candidate n)) τ =
                  (r : ℕ) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E) := by
              simpa [E, firstChoice, hfirst_apply] using
                kendallTau_eq_firstChoice_add_cycleRange τ
            rw [hkend, pow_add]
    _ = q ^ (r : ℕ) *
        ∑ σ ∈ reflFirstChoiceFiber n 0,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          rw [Finset.mul_sum]

/-- The fiber of rankings whose first two center-ranks are `(r,s)`, for the identity center. -/
noncomputable def reflFirstSecondChoiceFiber
    (n : ℕ) (r s : Candidate n) : Finset (Ranking n) := by
  classical
  exact Finset.univ.filter (fun τ => r = firstChoice τ ∧ s = secondChoice τ)

/-- Unnormalised identity-center top-two Mallows mass. -/
noncomputable def reflFirstSecondWeight
    (n : ℕ) (q : ℝ) (r s : Candidate n) : ℝ :=
  ∑ τ ∈ reflFirstSecondChoiceFiber n r s,
    q ^ kendallTau (Equiv.refl (Candidate n)) τ

/-- Identity-center unnormalised mass of rankings that correctly order a
center-ordered pair of ranks. -/
noncomputable def reflPairCorrectWeight
    (n : ℕ) (q : ℝ) (r s : Candidate n) : ℝ :=
  ∑ τ : Ranking n,
    if r < s ∧ rankOf τ r < rankOf τ s then
      q ^ kendallTau (Equiv.refl (Candidate n)) τ
    else
      0

/-- Identity-center unnormalised mass of rankings that incorrectly order a
center-ordered pair of ranks. -/
noncomputable def reflPairWrongWeight
    (n : ℕ) (q : ℝ) (r s : Candidate n) : ℝ :=
  ∑ τ : Ranking n,
    if r < s ∧ rankOf τ s < rankOf τ r then
      q ^ kendallTau (Equiv.refl (Candidate n)) τ
    else
      0

/-- Last candidate in the identity-center interval. -/
def reflLastCandidate (n : ℕ) : Candidate n := ⟨n + 1, by omega⟩

/-- The middle candidates between identity-center endpoints `0` and `last`,
indexed in their center order. -/
def reflMiddleCandidateEquiv
    (n : ℕ) :
    Fin n ≃ {c : Candidate n // c ≠ (0 : Candidate n) ∧ c ≠ reflLastCandidate n} where
  toFun i :=
    ⟨⟨i.val + 1, by omega⟩,
      by
        constructor
        · intro h
          have hval := congrArg Fin.val h
          simp at hval
        · intro h
          have hval := congrArg Fin.val h
          simp [reflLastCandidate] at hval
          omega⟩
  invFun c :=
    ⟨c.1.val - 1,
      by
        have hc_lt : c.1.val < n + 2 := c.1.isLt
        have hc_ne_zero : c.1.val ≠ 0 := by
          intro hval
          exact c.2.1 (Fin.ext hval)
        have hc_ne_last : c.1.val ≠ n + 1 := by
          intro hval
          exact c.2.2 (Fin.ext hval)
        omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv c := by
    apply Subtype.ext
    apply Fin.ext
    have hc_ne_zero : c.1.val ≠ 0 := by
      intro hval
      exact c.2.1 (Fin.ext hval)
    simp
    omega

@[simp] theorem reflMiddleCandidateEquiv_apply_val
    (n : ℕ) (i : Fin n) :
    ((reflMiddleCandidateEquiv n i).1 : ℕ) = i.val + 1 := rfl

theorem reflMiddleCandidateEquiv_apply_lt_iff
    (n : ℕ) (i j : Fin n) :
    (reflMiddleCandidateEquiv n i).1 <
        (reflMiddleCandidateEquiv n j).1 ↔ i < j := by
  change i.val + 1 < j.val + 1 ↔ i.val < j.val
  omega

theorem reflMiddleCandidateEquiv_symm_lt_iff
    (n : ℕ)
    (c d : {x : Candidate n // x ≠ (0 : Candidate n) ∧ x ≠ reflLastCandidate n}) :
    (reflMiddleCandidateEquiv n).symm c <
        (reflMiddleCandidateEquiv n).symm d ↔ c.1 < d.1 := by
  constructor
  · intro h
    have h' := (reflMiddleCandidateEquiv_apply_lt_iff n
      ((reflMiddleCandidateEquiv n).symm c)
      ((reflMiddleCandidateEquiv n).symm d)).mpr h
    simpa using h'
  · intro h
    have h' := (reflMiddleCandidateEquiv_apply_lt_iff n
      ((reflMiddleCandidateEquiv n).symm c)
      ((reflMiddleCandidateEquiv n).symm d)).mp (by simpa using h)
    simpa using h'

/-- Positions other than the two fixed endpoint positions. -/
noncomputable def reflEndpointPositionComplement
    (n : ℕ) (betterPos worsePos : Candidate n) : Finset (Candidate n) := ((Finset.univ : Finset (Candidate n)).erase betterPos).erase worsePos

theorem mem_reflEndpointPositionComplement
    (n : ℕ) (betterPos worsePos x : Candidate n) :
    x ∈ reflEndpointPositionComplement n betterPos worsePos ↔
      x ≠ betterPos ∧ x ≠ worsePos := by
  classical
  simp [reflEndpointPositionComplement, and_comm]

theorem reflEndpointPositionComplement_card_of_ne
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    (reflEndpointPositionComplement n betterPos worsePos).card = n := by
  classical
  have hworse_mem :
      worsePos ∈ (Finset.univ : Finset (Candidate n)).erase betterPos := by
    simp [hne.symm]
  rw [reflEndpointPositionComplement]
  rw [Finset.card_erase_of_mem hworse_mem]
  rw [Finset.card_erase_of_mem (by simp : betterPos ∈ (Finset.univ : Finset (Candidate n)))]
  simp

/-- Increasing enumeration of the positions not occupied by the two endpoints. -/
noncomputable def reflEndpointPositionOrderIso
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    Fin n ≃o reflEndpointPositionComplement n betterPos worsePos :=
  (reflEndpointPositionComplement n betterPos worsePos).orderIsoOfFin
    (reflEndpointPositionComplement_card_of_ne n hne)

/-- Increasing embedding of the positions not occupied by the two endpoints. -/
noncomputable def reflEndpointPositionOrderEmb
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) : Fin n ↪o Candidate n :=
  (reflEndpointPositionOrderIso n hne).toOrderEmbedding.trans
    (OrderEmbedding.subtype _)

theorem reflEndpointPositionOrderEmb_mem
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) (i : Fin n) :
    reflEndpointPositionOrderEmb n hne i ∈
      reflEndpointPositionComplement n betterPos worsePos :=
   Finset.orderEmbOfFin_mem
    (reflEndpointPositionComplement n betterPos worsePos)
    (reflEndpointPositionComplement_card_of_ne n hne) i

theorem reflEndpointPositionOrderEmb_ne_better
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) (i : Fin n) :
    reflEndpointPositionOrderEmb n hne i ≠ betterPos := by
  have hmem := reflEndpointPositionOrderEmb_mem n hne i
  exact (mem_reflEndpointPositionComplement n betterPos worsePos
    (reflEndpointPositionOrderEmb n hne i)).mp hmem |>.1

theorem reflEndpointPositionOrderEmb_ne_worse
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) (i : Fin n) :
    reflEndpointPositionOrderEmb n hne i ≠ worsePos := by
  have hmem := reflEndpointPositionOrderEmb_mem n hne i
  exact (mem_reflEndpointPositionComplement n betterPos worsePos
    (reflEndpointPositionOrderEmb n hne i)).mp hmem |>.2

/-- The middle-candidate order induced by a ranking in a fixed endpoint-position
fiber, as a function on the center-ordered middle indices. -/
noncomputable def reflEndpointMiddleOrderFun
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos) :
    Fin n → Fin n :=
  fun i =>
    (reflMiddleCandidateEquiv n).symm
      ⟨τ (reflEndpointPositionOrderEmb n hne i),
        by
          constructor
          · intro hzero
            have hpos_eq : reflEndpointPositionOrderEmb n hne i = betterPos := by
              have hpos_rank :
                  reflEndpointPositionOrderEmb n hne i =
                    rankOf τ (0 : Candidate n) := by
                apply τ.injective
                simp [rankOf, hzero]
              exact hpos_rank.trans hbetter
            exact reflEndpointPositionOrderEmb_ne_better n hne i hpos_eq
          · intro hlast
            have hpos_eq : reflEndpointPositionOrderEmb n hne i = worsePos := by
              have hpos_rank :
                  reflEndpointPositionOrderEmb n hne i =
                    rankOf τ (reflLastCandidate n) := by
                apply τ.injective
                simp [rankOf, hlast]
              exact hpos_rank.trans hworse
            exact reflEndpointPositionOrderEmb_ne_worse n hne i hpos_eq⟩

theorem reflEndpointMiddleOrderFun_candidate
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos)
    (i : Fin n) :
    (reflMiddleCandidateEquiv n
        (reflEndpointMiddleOrderFun n hne τ hbetter hworse i)).1 =
      τ (reflEndpointPositionOrderEmb n hne i) := by
  unfold reflEndpointMiddleOrderFun
  simp

theorem reflEndpointMiddleOrderFun_injective
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos) :
    Function.Injective
      (reflEndpointMiddleOrderFun n hne τ hbetter hworse) := by
  intro i j hij
  have hsub :
      (⟨τ (reflEndpointPositionOrderEmb n hne i), by
          constructor
          · intro hzero
            have hpos_eq : reflEndpointPositionOrderEmb n hne i = betterPos := by
              have hpos_rank :
                  reflEndpointPositionOrderEmb n hne i =
                    rankOf τ (0 : Candidate n) := by
                apply τ.injective
                simp [rankOf, hzero]
              exact hpos_rank.trans hbetter
            exact reflEndpointPositionOrderEmb_ne_better n hne i hpos_eq
          · intro hlast
            have hpos_eq : reflEndpointPositionOrderEmb n hne i = worsePos := by
              have hpos_rank :
                  reflEndpointPositionOrderEmb n hne i =
                    rankOf τ (reflLastCandidate n) := by
                apply τ.injective
                simp [rankOf, hlast]
              exact hpos_rank.trans hworse
            exact reflEndpointPositionOrderEmb_ne_worse n hne i hpos_eq⟩ :
          {c : Candidate n // c ≠ (0 : Candidate n) ∧ c ≠ reflLastCandidate n}) =
        ⟨τ (reflEndpointPositionOrderEmb n hne j), by
          constructor
          · intro hzero
            have hpos_eq : reflEndpointPositionOrderEmb n hne j = betterPos := by
              have hpos_rank :
                  reflEndpointPositionOrderEmb n hne j =
                    rankOf τ (0 : Candidate n) := by
                apply τ.injective
                simp [rankOf, hzero]
              exact hpos_rank.trans hbetter
            exact reflEndpointPositionOrderEmb_ne_better n hne j hpos_eq
          · intro hlast
            have hpos_eq : reflEndpointPositionOrderEmb n hne j = worsePos := by
              have hpos_rank :
                  reflEndpointPositionOrderEmb n hne j =
                    rankOf τ (reflLastCandidate n) := by
                apply τ.injective
                simp [rankOf, hlast]
              exact hpos_rank.trans hworse
            exact reflEndpointPositionOrderEmb_ne_worse n hne j hpos_eq⟩ :=
    (reflMiddleCandidateEquiv n).symm.injective hij
  have hτ :
      τ (reflEndpointPositionOrderEmb n hne i) =
        τ (reflEndpointPositionOrderEmb n hne j) :=
    congrArg Subtype.val hsub
  have hpos :
      reflEndpointPositionOrderEmb n hne i =
        reflEndpointPositionOrderEmb n hne j :=
    τ.injective hτ
  exact (reflEndpointPositionOrderEmb n hne).injective hpos

/-- The induced middle-candidate order as an actual permutation of middle
indices. -/
noncomputable def reflEndpointMiddleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective
    (reflEndpointMiddleOrderFun n hne τ hbetter hworse)
    ((Fintype.bijective_iff_injective_and_card
      (reflEndpointMiddleOrderFun n hne τ hbetter hworse)).mpr
      ⟨reflEndpointMiddleOrderFun_injective n hne τ hbetter hworse, rfl⟩)

theorem reflEndpointMiddleOrder_candidate
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos)
    (i : Fin n) :
    (reflMiddleCandidateEquiv n
        (reflEndpointMiddleOrder n hne τ hbetter hworse i)).1 =
      τ (reflEndpointPositionOrderEmb n hne i) :=  reflEndpointMiddleOrderFun_candidate n hne τ hbetter hworse i

theorem rankOf_reflEndpointMiddleOrder_candidate
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos)
    (i : Fin n) :
    rankOf τ
        (reflMiddleCandidateEquiv n
          (reflEndpointMiddleOrder n hne τ hbetter hworse i)).1 =
      reflEndpointPositionOrderEmb n hne i := by
  apply τ.injective
  simp [rankOf, reflEndpointMiddleOrder_candidate n hne τ hbetter hworse i]

theorem rankOf_reflMiddleCandidate_eq_endpointPositionOrderEmb_rankOf_middleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos)
    (k : Fin n) :
    rankOf τ (reflMiddleCandidateEquiv n k).1 =
      reflEndpointPositionOrderEmb n hne
        ((reflEndpointMiddleOrder n hne τ hbetter hworse).symm k) := by
  let σ : Equiv.Perm (Fin n) :=
    reflEndpointMiddleOrder n hne τ hbetter hworse
  have h :=
    rankOf_reflEndpointMiddleOrder_candidate n hne τ hbetter hworse
      (σ.symm k)
  simpa [σ] using h

/-- Inversions of a permutation of the middle block, indexed by `Fin n`. -/
noncomputable def finInversionFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter
    (fun ab => ab.1 < ab.2 ∧ σ.symm ab.2 < σ.symm ab.1)

/-- Kendall-tau inversion count for a permutation of `Fin n`. -/
noncomputable def finKendallTau {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := (finInversionFinset σ).card

/-- Mallows partition of the middle block. -/
noncomputable def finMallowsPartition (n : ℕ) (q : ℝ) : ℝ := ∑ σ : Equiv.Perm (Fin n), q ^ finKendallTau σ

/-- Decompose a ranking on `n+3` candidates by removing the best identity-center
candidate `0`.  The first component is the position of `0`; the second is the
ranking induced on the remaining candidates after closing that gap. -/
noncomputable def rankingPeelBestEquiv (n : ℕ) :
    Candidate (n + 1) × Ranking n ≃ Ranking (n + 1) where
  toFun pe := (Equiv.Perm.decomposeFin.symm (pe.1, pe.2.symm)).symm
  invFun τ :=
    let pe := Equiv.Perm.decomposeFin τ.symm
    (pe.1, pe.2.symm)
  left_inv pe := by
    rcases pe with ⟨p, σ⟩
    simp
  right_inv τ := by
    ext x
    simp

/-- Correction cycle converting Mathlib's swap-based `decomposeFin` insertion
into the order-preserving insertion above a removed position. -/
noncomputable def peelBestPositionCycle
    (n : ℕ) (p : Candidate (n + 1)) : Ranking n :=
  if hp : p = 0 then
    Equiv.refl (Candidate n)
  else
    Fin.cycleRange (p.pred hp)

theorem succAbove_peelBestPositionCycle
    (n : ℕ) (p : Candidate (n + 1)) (i : Candidate n) :
    p.succAbove (peelBestPositionCycle n p i) =
      Equiv.swap (0 : Candidate (n + 1)) p i.succ := by
  by_cases hp : p = 0
  · subst p
    simp [peelBestPositionCycle]
  · let k : Candidate n := p.pred hp
    have hp_eq : p = k.succ := by
      dsimp [k]
      exact (Fin.succ_pred p hp).symm
    rw [hp_eq]
    simpa [peelBestPositionCycle] using Fin.succAbove_cycleRange k i

/-- Order-preserving version of `rankingPeelBestEquiv`: the second component is
the literal ranking induced after deleting candidate `0` and its position. -/
noncomputable def rankingPeelBestOrderEquiv (n : ℕ) :
    Candidate (n + 1) × Ranking n ≃ Ranking (n + 1) where
  toFun pe :=
    rankingPeelBestEquiv n (pe.1, (peelBestPositionCycle n pe.1).trans pe.2)
  invFun τ :=
    let pe := (rankingPeelBestEquiv n).symm τ
    (pe.1, (peelBestPositionCycle n pe.1).symm.trans pe.2)
  left_inv := by
    intro pe
    rcases pe with ⟨p, σ⟩
    simp only [Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · apply Equiv.ext
      intro x
      simp
  right_inv := by
    intro τ
    let pe := (rankingPeelBestEquiv n).symm τ
    change
      rankingPeelBestEquiv n
        (pe.1,
          (peelBestPositionCycle n pe.1).trans
            ((peelBestPositionCycle n pe.1).symm.trans pe.2)) = τ
    have hsecond :
        (peelBestPositionCycle n pe.1).trans
            ((peelBestPositionCycle n pe.1).symm.trans pe.2) =
          pe.2 := by
      apply Equiv.ext
      intro x
      simp
    rw [hsecond]
    simpa [pe] using Equiv.apply_symm_apply (rankingPeelBestEquiv n) τ

@[simp] theorem rankOf_rankingPeelBestOrderEquiv_zero
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    rankOf (rankingPeelBestOrderEquiv n (p, σ)) (0 : Candidate (n + 1)) =
      p := by
  simp [rankingPeelBestOrderEquiv, rankingPeelBestEquiv, rankOf]

theorem rankOf_rankingPeelBestOrderEquiv_succ
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n)
    (c : Candidate n) :
    rankOf (rankingPeelBestOrderEquiv n (p, σ)) c.succ =
      p.succAbove (rankOf σ c) := by
  let H : Ranking n := peelBestPositionCycle n p
  have h :=
    succAbove_peelBestPositionCycle n p (H.symm (rankOf σ c))
  change
    rankOf (rankingPeelBestEquiv n (p, H.trans σ)) c.succ =
      p.succAbove (rankOf σ c)
  simp [rankingPeelBestEquiv, rankOf, H] at h ⊢
  exact h.symm

theorem rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n)
    (c d : Candidate n) :
    rankOf (rankingPeelBestOrderEquiv n (p, σ)) c.succ <
        rankOf (rankingPeelBestOrderEquiv n (p, σ)) d.succ ↔
      rankOf σ c < rankOf σ d := by
  rw [rankOf_rankingPeelBestOrderEquiv_succ,
    rankOf_rankingPeelBestOrderEquiv_succ]
  exact p.succAbove_lt_succAbove_iff

/-- Insert the worst identity-center candidate at position `p`, preserving the
relative order of all smaller candidates according to `σ`. -/
noncomputable def rankingPeelWorstOrderFun
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    Candidate (n + 1) → Candidate (n + 1) :=
  Fin.insertNth p (reflLastCandidate (n + 1))
    (fun i : Candidate n => (σ i).castSucc)

theorem rankingPeelWorstOrderFun_injective
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    Function.Injective (rankingPeelWorstOrderFun n p σ) := by
  intro x y hxy
  unfold rankingPeelWorstOrderFun at hxy
  cases x using Fin.succAboveCases p with
  | x =>
      cases y using Fin.succAboveCases p with
      | x => rfl
      | p j =>
          exfalso
          have hlast :
              reflLastCandidate (n + 1) = (σ j).castSucc := by
            simpa [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
              using hxy
          have hval := congrArg Fin.val hlast
          simp [reflLastCandidate] at hval
          have hlt := (σ j).isLt
          omega
  | p i =>
      cases y using Fin.succAboveCases p with
      | x =>
          exfalso
          have hlast :
              (σ i).castSucc = reflLastCandidate (n + 1) := by
            simpa [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
              using hxy
          have hval := congrArg Fin.val hlast
          simp [reflLastCandidate] at hval
          have hlt := (σ i).isLt
          omega
      | p j =>
          have hcast : (σ i).castSucc = (σ j).castSucc := by
            simpa [Fin.insertNth_apply_succAbove] using hxy
          have hij : i = j := σ.injective (Fin.castSucc_injective _ hcast)
          subst j
          rfl

/-- Ranking obtained by inserting the worst identity-center candidate at `p`. -/
noncomputable def rankingPeelWorstOrderRanking
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    Ranking (n + 1) :=
  Equiv.ofBijective (rankingPeelWorstOrderFun n p σ)
    (by
      have hinj := rankingPeelWorstOrderFun_injective n p σ
      exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

@[simp] theorem rankOf_rankingPeelWorstOrderRanking_last
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    rankOf (rankingPeelWorstOrderRanking n p σ)
        (reflLastCandidate (n + 1)) = p := by
  apply (rankingPeelWorstOrderRanking n p σ).injective
  simp [rankOf, rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun]

theorem rankOf_rankingPeelWorstOrderRanking_castSucc
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n)
    (c : Candidate n) :
    rankOf (rankingPeelWorstOrderRanking n p σ) c.castSucc =
      p.succAbove (rankOf σ c) := by
  apply (rankingPeelWorstOrderRanking n p σ).injective
  simp [rankOf, rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun]

theorem rankingPeelWorstRemoved_ne_last
    (n : ℕ) (τ : Ranking (n + 1)) (i : Candidate n) :
    τ ((rankOf τ (reflLastCandidate (n + 1))).succAbove i) ≠
      reflLastCandidate (n + 1) := by
  intro hlast
  have hpos :
      (rankOf τ (reflLastCandidate (n + 1))).succAbove i =
        rankOf τ (reflLastCandidate (n + 1)) := by
    apply τ.injective
    simpa [rankOf, hlast]
  exact Fin.succAbove_ne _ _ hpos

/-- Delete the worst identity-center candidate from a ranking. -/
noncomputable def rankingPeelWorstRemovedRanking
    (n : ℕ) (τ : Ranking (n + 1)) : Ranking n :=
  Equiv.ofBijective
    (fun i : Candidate n =>
      (τ ((rankOf τ (reflLastCandidate (n + 1))).succAbove i)).castPred
        (by
          simpa [reflLastCandidate] using
            rankingPeelWorstRemoved_ne_last n τ i))
    (by
      have hinj : Function.Injective
          (fun i : Candidate n =>
            (τ ((rankOf τ (reflLastCandidate (n + 1))).succAbove i)).castPred
              (by
                simpa [reflLastCandidate] using
                  rankingPeelWorstRemoved_ne_last n τ i)) := by
        intro i j hij
        have hfull :
            τ ((rankOf τ (reflLastCandidate (n + 1))).succAbove i) =
              τ ((rankOf τ (reflLastCandidate (n + 1))).succAbove j) :=
          Fin.castPred_inj.mp hij
        exact (rankOf τ (reflLastCandidate (n + 1))).succAbove_right_injective
          (τ.injective hfull)
      exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

/-- Decompose a ranking by the position of the worst identity-center candidate
and the order induced on all smaller candidates. -/
noncomputable def rankingPeelWorstOrderEquiv (n : ℕ) :
    Candidate (n + 1) × Ranking n ≃ Ranking (n + 1) :=
  Equiv.ofBijective
    (fun pe : Candidate (n + 1) × Ranking n =>
      rankingPeelWorstOrderRanking n pe.1 pe.2)
    (by
      constructor
      · intro pe₁ pe₂ h
        rcases pe₁ with ⟨p₁, σ₁⟩
        rcases pe₂ with ⟨p₂, σ₂⟩
        have hp : p₁ = p₂ := by
          have hrank := congrArg
            (fun τ : Ranking (n + 1) =>
              rankOf τ (reflLastCandidate (n + 1))) h
          simpa using hrank
        subst p₂
        have hσ : σ₁ = σ₂ := by
          apply Equiv.ext
          intro i
          have happ := congrArg
            (fun τ : Ranking (n + 1) => τ (p₁.succAbove i)) h
          have hcast : (σ₁ i).castSucc = (σ₂ i).castSucc := by
            simpa [rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun,
              Fin.insertNth_apply_succAbove] using happ
          exact Fin.castSucc_injective _ hcast
        subst σ₂
        rfl
      · intro τ
        let p : Candidate (n + 1) := rankOf τ (reflLastCandidate (n + 1))
        let σ : Ranking n := rankingPeelWorstRemovedRanking n τ
        refine ⟨(p, σ), ?_⟩
        apply Equiv.ext
        intro x
        cases x using Fin.succAboveCases p with
        | x =>
            simp [rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun, p, rankOf]
        | p i =>
            have hne :
                τ (p.succAbove i) ≠ reflLastCandidate (n + 1) := by
              simpa [p] using rankingPeelWorstRemoved_ne_last n τ i
            simpa [rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun,
              rankingPeelWorstRemovedRanking, σ, p,
              Fin.insertNth_apply_succAbove] using
              (Fin.castSucc_castPred (τ (p.succAbove i)) hne)
    )

@[simp] theorem rankOf_rankingPeelWorstOrderEquiv_last
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    rankOf (rankingPeelWorstOrderEquiv n (p, σ))
        (reflLastCandidate (n + 1)) = p := by
  change rankOf (rankingPeelWorstOrderRanking n p σ)
      (reflLastCandidate (n + 1)) = p
  apply (rankingPeelWorstOrderRanking n p σ).injective
  simp [rankOf, rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun]

theorem rankOf_rankingPeelWorstOrderEquiv_castSucc
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n)
    (c : Candidate n) :
    rankOf (rankingPeelWorstOrderEquiv n (p, σ)) c.castSucc =
      p.succAbove (rankOf σ c) := by
  change rankOf (rankingPeelWorstOrderRanking n p σ) c.castSucc =
      p.succAbove (rankOf σ c)
  apply (rankingPeelWorstOrderRanking n p σ).injective
  simp [rankOf, rankingPeelWorstOrderRanking, rankingPeelWorstOrderFun]

theorem rankOf_rankingPeelWorstOrderEquiv_castSucc_lt_iff
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n)
    (c d : Candidate n) :
    rankOf (rankingPeelWorstOrderEquiv n (p, σ)) c.castSucc <
        rankOf (rankingPeelWorstOrderEquiv n (p, σ)) d.castSucc ↔
      rankOf σ c < rankOf σ d := by
  rw [rankOf_rankingPeelWorstOrderEquiv_castSucc,
    rankOf_rankingPeelWorstOrderEquiv_castSucc]
  exact p.succAbove_lt_succAbove_iff

theorem rankOf_reflMiddleCandidate_lt_iff_middleOrder_symm_lt
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos)
    (i j : Fin n) :
    rankOf τ (reflMiddleCandidateEquiv n i).1 <
        rankOf τ (reflMiddleCandidateEquiv n j).1 ↔
      (reflEndpointMiddleOrder n hne τ hbetter hworse).symm i <
        (reflEndpointMiddleOrder n hne τ hbetter hworse).symm j := by
  rw [rankOf_reflMiddleCandidate_eq_endpointPositionOrderEmb_rankOf_middleOrder
      n hne τ hbetter hworse i,
    rankOf_reflMiddleCandidate_eq_endpointPositionOrderEmb_rankOf_middleOrder
      n hne τ hbetter hworse j]
  exact (reflEndpointPositionOrderEmb n hne).lt_iff_lt

/-- Identity-center inversions involving the best endpoint `0`. -/
noncomputable def reflEndpointZeroInversions
    (n : ℕ) (τ : Ranking n) : Finset (Candidate n × Candidate n) :=
  (inversionFinset (Equiv.refl (Candidate n)) τ).filter
    (fun ab => ab.1 = (0 : Candidate n))

/-- Identity-center inversions involving the worst endpoint. -/
noncomputable def reflEndpointLastInversions
    (n : ℕ) (τ : Ranking n) : Finset (Candidate n × Candidate n) :=
  (inversionFinset (Equiv.refl (Candidate n)) τ).filter
    (fun ab => ab.2 = reflLastCandidate n)

/-- Identity-center inversions involving either endpoint. -/
noncomputable def reflEndpointInversions
    (n : ℕ) (τ : Ranking n) : Finset (Candidate n × Candidate n) :=
  (inversionFinset (Equiv.refl (Candidate n)) τ).filter
    (fun ab => ab.1 = (0 : Candidate n) ∨ ab.2 = reflLastCandidate n)

/-- Identity-center inversions among candidates strictly between the endpoints. -/
noncomputable def reflMiddleInversions
    (n : ℕ) (τ : Ranking n) : Finset (Candidate n × Candidate n) :=
  (inversionFinset (Equiv.refl (Candidate n)) τ).filter
    (fun ab => ab.1 ≠ (0 : Candidate n) ∧ ab.2 ≠ reflLastCandidate n)

theorem reflMiddleInversions_mem_invertedPair
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    invertedPair (Equiv.refl (Candidate n)) τ ab := by
  simpa [reflMiddleInversions, inversionFinset] using
    (Finset.mem_filter.mp hab).1

theorem reflMiddleInversions_mem_left_ne_zero
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    ab.1 ≠ (0 : Candidate n) := by
  simpa [reflMiddleInversions] using (Finset.mem_filter.mp hab).2.1

theorem reflMiddleInversions_mem_right_ne_last
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    ab.2 ≠ reflLastCandidate n := by
  simpa [reflMiddleInversions] using (Finset.mem_filter.mp hab).2.2

theorem reflMiddleInversions_mem_left_ne_last
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    ab.1 ≠ reflLastCandidate n := by
  intro hlast
  have hinv := reflMiddleInversions_mem_invertedPair hab
  have hlt : reflLastCandidate n < ab.2 := by
    simpa [rankOf, hlast] using hinv.1
  have hle : (ab.2 : ℕ) ≤ n + 1 := Nat.le_of_lt_succ ab.2.isLt
  have hlt' : n + 1 < (ab.2 : ℕ) := hlt
  omega

theorem reflMiddleInversions_mem_right_ne_zero
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    ab.2 ≠ (0 : Candidate n) := by
  intro hzero
  have hinv := reflMiddleInversions_mem_invertedPair hab
  have hlt : ab.1 < (0 : Candidate n) := by
    simpa [rankOf, hzero] using hinv.1
  exact not_lt_bot hlt

noncomputable def reflMiddleInversionToFinPair
    {n : ℕ} {τ : Ranking n} (ab : Candidate n × Candidate n)
    (hab : ab ∈ reflMiddleInversions n τ) : Fin n × Fin n :=
  ((reflMiddleCandidateEquiv n).symm
      ⟨ab.1,
        ⟨reflMiddleInversions_mem_left_ne_zero hab,
          reflMiddleInversions_mem_left_ne_last hab⟩⟩,
    (reflMiddleCandidateEquiv n).symm
      ⟨ab.2,
        ⟨reflMiddleInversions_mem_right_ne_zero hab,
          reflMiddleInversions_mem_right_ne_last hab⟩⟩)

theorem reflMiddleInversionToFinPair_left_candidate
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    (reflMiddleCandidateEquiv n
      (reflMiddleInversionToFinPair ab hab).1).1 = ab.1 := by
  unfold reflMiddleInversionToFinPair
  simp

theorem reflMiddleInversionToFinPair_right_candidate
    {n : ℕ} {τ : Ranking n} {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    (reflMiddleCandidateEquiv n
      (reflMiddleInversionToFinPair ab hab).2).1 = ab.2 := by
  unfold reflMiddleInversionToFinPair
  simp

theorem reflMiddleInversionToFinPair_mem_finInversionFinset
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos)
    {ab : Candidate n × Candidate n}
    (hab : ab ∈ reflMiddleInversions n τ) :
    reflMiddleInversionToFinPair ab hab ∈
      finInversionFinset
        (reflEndpointMiddleOrder n hne τ hbetter hworse) := by
  classical
  let ij := reflMiddleInversionToFinPair ab hab
  have hinv := reflMiddleInversions_mem_invertedPair hab
  have hcenter_candidates : ab.1 < ab.2 := by
    simpa [rankOf] using hinv.1
  have hcenter_idx : ij.1 < ij.2 := by
    have hsub :
        ((reflMiddleCandidateEquiv n).symm
            ⟨ab.1,
              ⟨reflMiddleInversions_mem_left_ne_zero hab,
                reflMiddleInversions_mem_left_ne_last hab⟩⟩) <
          ((reflMiddleCandidateEquiv n).symm
            ⟨ab.2,
              ⟨reflMiddleInversions_mem_right_ne_zero hab,
                reflMiddleInversions_mem_right_ne_last hab⟩⟩) :=
      (reflMiddleCandidateEquiv_symm_lt_iff n _ _).mpr
        hcenter_candidates
    simpa [ij, reflMiddleInversionToFinPair] using hsub
  have hrank_candidates : rankOf τ ab.2 < rankOf τ ab.1 := hinv.2
  have hrank_rewritten :
      rankOf τ (reflMiddleCandidateEquiv n ij.2).1 <
        rankOf τ (reflMiddleCandidateEquiv n ij.1).1 := by
    simpa [ij, reflMiddleInversionToFinPair_left_candidate hab,
      reflMiddleInversionToFinPair_right_candidate hab] using hrank_candidates
  have hrank_idx :
      (reflEndpointMiddleOrder n hne τ hbetter hworse).symm ij.2 <
        (reflEndpointMiddleOrder n hne τ hbetter hworse).symm ij.1 :=
    (rankOf_reflMiddleCandidate_lt_iff_middleOrder_symm_lt
      n hne τ hbetter hworse ij.2 ij.1).mp hrank_rewritten
  simp [finInversionFinset, ij, hcenter_idx, hrank_idx]

theorem reflMiddleInversions_card_eq_finKendallTau_middleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos) :
    (reflMiddleInversions n τ).card =
      finKendallTau
        (reflEndpointMiddleOrder n hne τ hbetter hworse) := by
  classical
  unfold finKendallTau
  refine Finset.card_bij
    (i := fun ab hab => reflMiddleInversionToFinPair ab hab) ?hi ?hinj ?hsurj
  · intro ab hab
    exact reflMiddleInversionToFinPair_mem_finInversionFinset
      n hne τ hbetter hworse hab
  · intro ab₁ hab₁ ab₂ hab₂ h
    have hleft : ab₁.1 = ab₂.1 := by
      have hc :=
        congrArg
          (fun p : Fin n × Fin n =>
            (reflMiddleCandidateEquiv n p.1).1) h
      simpa [reflMiddleInversionToFinPair_left_candidate hab₁,
        reflMiddleInversionToFinPair_left_candidate hab₂] using hc
    have hright : ab₁.2 = ab₂.2 := by
      have hc :=
        congrArg
          (fun p : Fin n × Fin n =>
            (reflMiddleCandidateEquiv n p.2).1) h
      simpa [reflMiddleInversionToFinPair_right_candidate hab₁,
        reflMiddleInversionToFinPair_right_candidate hab₂] using hc
    exact Prod.ext hleft hright
  · intro ij hij
    let σ : Equiv.Perm (Fin n) :=
      reflEndpointMiddleOrder n hne τ hbetter hworse
    let ab : Candidate n × Candidate n :=
      ((reflMiddleCandidateEquiv n ij.1).1,
        (reflMiddleCandidateEquiv n ij.2).1)
    have hij_props :
        ij.1 < ij.2 ∧ σ.symm ij.2 < σ.symm ij.1 := by
      simpa [finInversionFinset, σ] using hij
    have hcenter_candidates : ab.1 < ab.2 := by
      dsimp [ab]
      exact (reflMiddleCandidateEquiv_apply_lt_iff n ij.1 ij.2).mpr
        hij_props.1
    have hrank_candidates : rankOf τ ab.2 < rankOf τ ab.1 := by
      have hraw :=
        (rankOf_reflMiddleCandidate_lt_iff_middleOrder_symm_lt
          n hne τ hbetter hworse ij.2 ij.1).mpr hij_props.2
      simpa [ab] using hraw
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab :=
      ⟨by simpa [rankOf, ab] using hcenter_candidates,
        hrank_candidates⟩
    have hab : ab ∈ reflMiddleInversions n τ := by
      have hleft_ne_zero : ab.1 ≠ (0 : Candidate n) := by
        dsimp [ab]
        exact (reflMiddleCandidateEquiv n ij.1).2.1
      have hright_ne_last : ab.2 ≠ reflLastCandidate n := by
        dsimp [ab]
        exact (reflMiddleCandidateEquiv n ij.2).2.2
      simp [reflMiddleInversions, inversionFinset, hinv, hleft_ne_zero,
        hright_ne_last]
    refine ⟨ab, hab, ?_⟩
    apply Prod.ext
    · apply (reflMiddleCandidateEquiv n).injective
      apply Subtype.ext
      simpa [ab, reflMiddleInversionToFinPair_left_candidate hab]
    · apply (reflMiddleCandidateEquiv n).injective
      apply Subtype.ext
      simpa [ab, reflMiddleInversionToFinPair_right_candidate hab]

noncomputable def reflEndpointRankingOfMiddleOrderFun
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) (x : Candidate n) : Candidate n :=
  if hx : x = betterPos then
    (0 : Candidate n)
  else if hy : x = worsePos then
    reflLastCandidate n
  else
    (reflMiddleCandidateEquiv n
      (σ ((reflEndpointPositionOrderIso n hne).symm
        ⟨x, (mem_reflEndpointPositionComplement n betterPos worsePos x).mpr
          ⟨hx, hy⟩⟩))).1

noncomputable def reflEndpointRankingOfMiddleOrderInvFun
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) (c : Candidate n) : Candidate n :=
  if hc : c = (0 : Candidate n) then
    betterPos
  else if hd : c = reflLastCandidate n then
    worsePos
  else
    (reflEndpointPositionOrderIso n hne
      (σ.symm ((reflMiddleCandidateEquiv n).symm
        ⟨c, ⟨hc, hd⟩⟩))).1

@[simp] theorem reflEndpointRankingOfMiddleOrderFun_better
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    reflEndpointRankingOfMiddleOrderFun n hne σ betterPos =
      (0 : Candidate n) := by
  simp [reflEndpointRankingOfMiddleOrderFun]

@[simp] theorem reflEndpointRankingOfMiddleOrderFun_worse
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    reflEndpointRankingOfMiddleOrderFun n hne σ worsePos =
      reflLastCandidate n := by
  simp [reflEndpointRankingOfMiddleOrderFun, hne.symm]

theorem reflEndpointRankingOfMiddleOrderFun_middle
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reflEndpointRankingOfMiddleOrderFun n hne σ
        ((reflEndpointPositionOrderIso n hne i).1) =
      (reflMiddleCandidateEquiv n (σ i)).1 := by
  have hmem : ((reflEndpointPositionOrderIso n hne i).1) ∈
      reflEndpointPositionComplement n betterPos worsePos :=
    (reflEndpointPositionOrderIso n hne i).2
  have hne_better :
      ((reflEndpointPositionOrderIso n hne i).1) ≠ betterPos :=
    ((mem_reflEndpointPositionComplement n betterPos worsePos
      ((reflEndpointPositionOrderIso n hne i).1)).mp hmem).1
  have hne_worse :
      ((reflEndpointPositionOrderIso n hne i).1) ≠ worsePos :=
    ((mem_reflEndpointPositionComplement n betterPos worsePos
      ((reflEndpointPositionOrderIso n hne i).1)).mp hmem).2
  simp [reflEndpointRankingOfMiddleOrderFun, hne_better, hne_worse]

@[simp] theorem reflEndpointRankingOfMiddleOrderInvFun_zero
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    reflEndpointRankingOfMiddleOrderInvFun n hne σ (0 : Candidate n) =
      betterPos := by
  simp [reflEndpointRankingOfMiddleOrderInvFun]

@[simp] theorem reflEndpointRankingOfMiddleOrderInvFun_last
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    reflEndpointRankingOfMiddleOrderInvFun n hne σ (reflLastCandidate n) =
      worsePos := by
  have hlast_ne_zero : reflLastCandidate n ≠ (0 : Candidate n) := by
    intro h
    have hval := congrArg Fin.val h
    simp [reflLastCandidate] at hval
  simp [reflEndpointRankingOfMiddleOrderInvFun, hlast_ne_zero]

theorem reflEndpointRankingOfMiddleOrderInvFun_middle
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reflEndpointRankingOfMiddleOrderInvFun n hne σ
        (reflMiddleCandidateEquiv n i).1 =
      (reflEndpointPositionOrderIso n hne (σ.symm i)).1 := by
  have hne_zero : (reflMiddleCandidateEquiv n i).1 ≠ (0 : Candidate n) :=
    (reflMiddleCandidateEquiv n i).2.1
  have hne_last : (reflMiddleCandidateEquiv n i).1 ≠ reflLastCandidate n :=
    (reflMiddleCandidateEquiv n i).2.2
  simp [reflEndpointRankingOfMiddleOrderInvFun, hne_zero, hne_last]

theorem reflEndpointRankingOfMiddleOrder_leftInverse
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    Function.LeftInverse
      (reflEndpointRankingOfMiddleOrderInvFun n hne σ)
      (reflEndpointRankingOfMiddleOrderFun n hne σ) := by
  intro x
  by_cases hx : x = betterPos
  · subst x
    simp [reflEndpointRankingOfMiddleOrderFun_better,
      reflEndpointRankingOfMiddleOrderInvFun_zero]
  · by_cases hy : x = worsePos
    · subst x
      simp [reflEndpointRankingOfMiddleOrderFun_worse,
        reflEndpointRankingOfMiddleOrderInvFun_last]
    · have hmem : x ∈ reflEndpointPositionComplement n betterPos worsePos :=
        (mem_reflEndpointPositionComplement n betterPos worsePos x).mpr
          ⟨hx, hy⟩
      let i : Fin n :=
        (reflEndpointPositionOrderIso n hne).symm ⟨x, hmem⟩
      have hx_eq : x = (reflEndpointPositionOrderIso n hne i).1 := by
        dsimp [i]
        simp
      rw [hx_eq]
      rw [reflEndpointRankingOfMiddleOrderFun_middle]
      rw [reflEndpointRankingOfMiddleOrderInvFun_middle]
      simp

theorem reflEndpointRankingOfMiddleOrder_rightInverse
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    Function.RightInverse
      (reflEndpointRankingOfMiddleOrderInvFun n hne σ)
      (reflEndpointRankingOfMiddleOrderFun n hne σ) := by
  intro c
  by_cases hc : c = (0 : Candidate n)
  · subst c
    simp [reflEndpointRankingOfMiddleOrderInvFun_zero,
      reflEndpointRankingOfMiddleOrderFun_better]
  · by_cases hd : c = reflLastCandidate n
    · subst c
      simp [reflEndpointRankingOfMiddleOrderInvFun_last,
        reflEndpointRankingOfMiddleOrderFun_worse]
    · let i : Fin n :=
        (reflMiddleCandidateEquiv n).symm ⟨c, ⟨hc, hd⟩⟩
      have hc_eq : c = (reflMiddleCandidateEquiv n i).1 := by
        dsimp [i]
        simp
      rw [hc_eq]
      rw [reflEndpointRankingOfMiddleOrderInvFun_middle]
      rw [reflEndpointRankingOfMiddleOrderFun_middle]
      simp

noncomputable def reflEndpointRankingOfMiddleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) : Ranking n where
  toFun := reflEndpointRankingOfMiddleOrderFun n hne σ
  invFun := reflEndpointRankingOfMiddleOrderInvFun n hne σ
  left_inv := reflEndpointRankingOfMiddleOrder_leftInverse n hne σ
  right_inv := reflEndpointRankingOfMiddleOrder_rightInverse n hne σ

@[simp] theorem rankOf_reflEndpointRankingOfMiddleOrder_zero
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    rankOf (reflEndpointRankingOfMiddleOrder n hne σ) (0 : Candidate n) =
      betterPos := by
  let τ : Ranking n := reflEndpointRankingOfMiddleOrder n hne σ
  change rankOf τ (0 : Candidate n) = betterPos
  apply τ.injective
  simp [rankOf, τ, reflEndpointRankingOfMiddleOrder]

@[simp] theorem rankOf_reflEndpointRankingOfMiddleOrder_last
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    rankOf (reflEndpointRankingOfMiddleOrder n hne σ) (reflLastCandidate n) =
      worsePos := by
  let τ : Ranking n := reflEndpointRankingOfMiddleOrder n hne σ
  change rankOf τ (reflLastCandidate n) = worsePos
  apply τ.injective
  simp [rankOf, τ, reflEndpointRankingOfMiddleOrder]

theorem reflEndpointMiddleOrder_reflEndpointRankingOfMiddleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    reflEndpointMiddleOrder n hne
        (reflEndpointRankingOfMiddleOrder n hne σ)
        (rankOf_reflEndpointRankingOfMiddleOrder_zero n hne σ)
        (rankOf_reflEndpointRankingOfMiddleOrder_last n hne σ) =
      σ := by
  apply Equiv.ext
  intro i
  apply (reflMiddleCandidateEquiv n).injective
  apply Subtype.ext
  have hcandidate :=
    reflEndpointMiddleOrder_candidate n hne
      (reflEndpointRankingOfMiddleOrder n hne σ)
      (rankOf_reflEndpointRankingOfMiddleOrder_zero n hne σ)
      (rankOf_reflEndpointRankingOfMiddleOrder_last n hne σ) i
  have hfun :
      (reflEndpointRankingOfMiddleOrder n hne σ)
          (reflEndpointPositionOrderEmb n hne i) =
        (reflMiddleCandidateEquiv n (σ i)).1 := by
    simpa [reflEndpointRankingOfMiddleOrder, reflEndpointPositionOrderEmb] using
      reflEndpointRankingOfMiddleOrderFun_middle n hne σ i
  exact hcandidate.trans hfun

/-- Rankings whose endpoint candidates occupy fixed positions. -/
noncomputable def reflEndpointPositionFiber
    (n : ℕ) (betterPos worsePos : Candidate n) : Finset (Ranking n) := by
  classical
  exact Finset.univ.filter
    (fun τ : Ranking n =>
      rankOf τ (0 : Candidate n) = betterPos ∧
        rankOf τ (reflLastCandidate n) = worsePos)

theorem reflEndpointRankingOfMiddleOrder_mem_fiber
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    reflEndpointRankingOfMiddleOrder n hne σ ∈
      reflEndpointPositionFiber n betterPos worsePos := by
  simp [reflEndpointPositionFiber]

theorem reflEndpointRankingOfMiddleOrder_reflEndpointMiddleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (τ : Ranking n)
    (hbetter : rankOf τ (0 : Candidate n) = betterPos)
    (hworse : rankOf τ (reflLastCandidate n) = worsePos) :
    reflEndpointRankingOfMiddleOrder n hne
        (reflEndpointMiddleOrder n hne τ hbetter hworse) =
      τ := by
  apply Equiv.ext
  intro x
  by_cases hx : x = betterPos
  · subst x
    have hτ_better : τ betterPos = (0 : Candidate n) := by
      rw [← hbetter]
      simp [rankOf]
    simp [reflEndpointRankingOfMiddleOrder, hτ_better]
  · by_cases hy : x = worsePos
    · subst x
      have hτ_worse : τ worsePos = reflLastCandidate n := by
        rw [← hworse]
        simp [rankOf]
      simp [reflEndpointRankingOfMiddleOrder, hτ_worse]
    · have hmem :
          x ∈ reflEndpointPositionComplement n betterPos worsePos :=
        (mem_reflEndpointPositionComplement n betterPos worsePos x).mpr
          ⟨hx, hy⟩
      let i : Fin n :=
        (reflEndpointPositionOrderIso n hne).symm ⟨x, hmem⟩
      have hx_eq : x = (reflEndpointPositionOrderIso n hne i).1 := by
        dsimp [i]
        simp
      rw [hx_eq]
      change
        reflEndpointRankingOfMiddleOrderFun n hne
            (reflEndpointMiddleOrder n hne τ hbetter hworse)
            ((reflEndpointPositionOrderIso n hne i).1) =
          τ ((reflEndpointPositionOrderIso n hne i).1)
      rw [reflEndpointRankingOfMiddleOrderFun_middle]
      simpa [reflEndpointPositionOrderEmb] using
        reflEndpointMiddleOrder_candidate n hne τ hbetter hworse i

theorem reflMiddleInversions_card_reflEndpointRankingOfMiddleOrder
    (n : ℕ) {betterPos worsePos : Candidate n} (hne : betterPos ≠ worsePos)
    (σ : Equiv.Perm (Fin n)) :
    (reflMiddleInversions n (reflEndpointRankingOfMiddleOrder n hne σ)).card =
      finKendallTau σ := by
  rw [reflMiddleInversions_card_eq_finKendallTau_middleOrder n hne
      (reflEndpointRankingOfMiddleOrder n hne σ)
      (rankOf_reflEndpointRankingOfMiddleOrder_zero n hne σ)
      (rankOf_reflEndpointRankingOfMiddleOrder_last n hne σ)]
  rw [reflEndpointMiddleOrder_reflEndpointRankingOfMiddleOrder n hne σ]

/-- The middle-candidate Mallows weight inside a fixed endpoint-position fiber. -/
noncomputable def reflEndpointPositionMiddleWeight
    (n : ℕ) (q : ℝ) (betterPos worsePos : Candidate n) : ℝ :=
  ∑ τ ∈ reflEndpointPositionFiber n betterPos worsePos,
    q ^ (reflMiddleInversions n τ).card

/-- A concrete ranking putting the best endpoint at `betterPos` and the worst
endpoint at `worsePos`.  Used only as a finite-fiber nonemptiness witness. -/
noncomputable def reflEndpointPositionWitness
    (n : ℕ) (betterPos worsePos : Candidate n) : Ranking n :=
  let e₁ : Ranking n := Equiv.swap betterPos (0 : Candidate n)
  let e₂ : Ranking n := Equiv.swap (e₁ worsePos) (reflLastCandidate n)
  e₁.trans e₂

theorem reflEndpointPositionWitness_apply_better
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    reflEndpointPositionWitness n betterPos worsePos betterPos =
      (0 : Candidate n) := by
  unfold reflEndpointPositionWitness
  let e₁ : Ranking n := Equiv.swap betterPos (0 : Candidate n)
  let e₂ : Ranking n := Equiv.swap (e₁ worsePos) (reflLastCandidate n)
  have he₁_better : e₁ betterPos = (0 : Candidate n) := by
    simp [e₁]
  have he₁_worse_ne_zero : e₁ worsePos ≠ (0 : Candidate n) := by
    intro h
    have hworse_eq_better : worsePos = betterPos := by
      apply e₁.injective
      simpa [he₁_better] using h
    exact hne hworse_eq_better.symm
  have hlast_ne_zero : reflLastCandidate n ≠ (0 : Candidate n) := by
    intro h
    have hval := congrArg Fin.val h
    simp [reflLastCandidate] at hval
  have he₂_zero : e₂ (0 : Candidate n) = (0 : Candidate n) := by
    dsimp [e₂]
    rw [Equiv.swap_apply_of_ne_of_ne he₁_worse_ne_zero.symm
      hlast_ne_zero.symm]
  change e₂ (e₁ betterPos) = (0 : Candidate n)
  rw [he₁_better, he₂_zero]

theorem reflEndpointPositionWitness_apply_worse
    (n : ℕ) (betterPos worsePos : Candidate n) :
    reflEndpointPositionWitness n betterPos worsePos worsePos =
      reflLastCandidate n := by
  unfold reflEndpointPositionWitness
  let e₁ : Ranking n := Equiv.swap betterPos (0 : Candidate n)
  let e₂ : Ranking n := Equiv.swap (e₁ worsePos) (reflLastCandidate n)
  have he₂ : e₂ (e₁ worsePos) = reflLastCandidate n := by
    dsimp [e₂]
    exact Equiv.swap_apply_left (e₁ worsePos) (reflLastCandidate n)
  change e₂ (e₁ worsePos) = reflLastCandidate n
  exact he₂

theorem rankOf_reflEndpointPositionWitness_zero
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    rankOf (reflEndpointPositionWitness n betterPos worsePos)
        (0 : Candidate n) =
      betterPos := by
  let τ : Ranking n := reflEndpointPositionWitness n betterPos worsePos
  apply τ.injective
  simp [rankOf, τ, reflEndpointPositionWitness_apply_better n hne]

theorem rankOf_reflEndpointPositionWitness_last
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    rankOf (reflEndpointPositionWitness n betterPos worsePos)
        (reflLastCandidate n) =
      worsePos := by
  let τ : Ranking n := reflEndpointPositionWitness n betterPos worsePos
  apply τ.injective
  simp [rankOf, τ, reflEndpointPositionWitness_apply_worse]

theorem reflEndpointPositionWitness_mem_fiber
    (n : ℕ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    reflEndpointPositionWitness n betterPos worsePos ∈
      reflEndpointPositionFiber n betterPos worsePos := by
  simp [reflEndpointPositionFiber,
    rankOf_reflEndpointPositionWitness_zero n hne,
    rankOf_reflEndpointPositionWitness_last n hne]

theorem reflEndpointPositionMiddleWeight_pos
    (n : ℕ) {q : ℝ} (hq : 0 < q) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    0 < reflEndpointPositionMiddleWeight n q betterPos worsePos := by
  classical
  let τ : Ranking n := reflEndpointPositionWitness n betterPos worsePos
  unfold reflEndpointPositionMiddleWeight
  have hnonneg :
      ∀ σ ∈ reflEndpointPositionFiber n betterPos worsePos,
        0 ≤ q ^ (reflMiddleInversions n σ).card := by
    intro σ _
    exact pow_nonneg (le_of_lt hq) _
  have hle :
      q ^ (reflMiddleInversions n τ).card ≤
        ∑ σ ∈ reflEndpointPositionFiber n betterPos worsePos,
          q ^ (reflMiddleInversions n σ).card :=
    Finset.single_le_sum hnonneg
      (by
        dsimp [τ]
        exact reflEndpointPositionWitness_mem_fiber n hne)
  exact lt_of_lt_of_le (pow_pos hq _) hle

theorem reflEndpointPositionMiddleWeight_eq_finMallowsPartition_of_ne
    (n : ℕ) (q : ℝ) {betterPos worsePos : Candidate n}
    (hne : betterPos ≠ worsePos) :
    reflEndpointPositionMiddleWeight n q betterPos worsePos =
      finMallowsPartition n q := by
  classical
  unfold reflEndpointPositionMiddleWeight finMallowsPartition
  symm
  refine Finset.sum_bij
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := reflEndpointPositionFiber n betterPos worsePos)
    (i := fun σ _ => reflEndpointRankingOfMiddleOrder n hne σ)
    ?hi ?hinj ?hsurj ?hweight
  · intro σ _
    exact reflEndpointRankingOfMiddleOrder_mem_fiber n hne σ
  · intro σ₁ _ σ₂ _ hσ
    apply Equiv.ext
    intro i
    apply (reflMiddleCandidateEquiv n).injective
    apply Subtype.ext
    have happ := Equiv.ext_iff.mp hσ
        ((reflEndpointPositionOrderIso n hne i).1)
    change
      reflEndpointRankingOfMiddleOrderFun n hne σ₁
          ((reflEndpointPositionOrderIso n hne i).1) =
        reflEndpointRankingOfMiddleOrderFun n hne σ₂
          ((reflEndpointPositionOrderIso n hne i).1) at happ
    rw [reflEndpointRankingOfMiddleOrderFun_middle n hne σ₁ i,
      reflEndpointRankingOfMiddleOrderFun_middle n hne σ₂ i] at happ
    exact happ
  · intro τ hτ
    have hbetter : rankOf τ (0 : Candidate n) = betterPos :=
      (Finset.mem_filter.mp hτ).2.1
    have hworse : rankOf τ (reflLastCandidate n) = worsePos :=
      (Finset.mem_filter.mp hτ).2.2
    refine ⟨reflEndpointMiddleOrder n hne τ hbetter hworse, by simp, ?_⟩
    exact reflEndpointRankingOfMiddleOrder_reflEndpointMiddleOrder
      n hne τ hbetter hworse
  · intro σ _
    rw [reflMiddleInversions_card_reflEndpointRankingOfMiddleOrder n hne σ]

theorem finMallowsPartition_pos
    (n : ℕ) {q : ℝ} (hq : 0 < q) :
    0 < finMallowsPartition n q := by
  have hne : (0 : Candidate n) ≠ reflLastCandidate n := by
    intro h
    have hval := congrArg Fin.val h
    simp [reflLastCandidate] at hval
  have hpos :
      0 < reflEndpointPositionMiddleWeight n q
        (0 : Candidate n) (reflLastCandidate n) :=
    reflEndpointPositionMiddleWeight_pos n hq hne
  simpa [reflEndpointPositionMiddleWeight_eq_finMallowsPartition_of_ne
    n q hne] using hpos

/-- For the identity center, inversions involving the best endpoint are exactly
the candidates placed before it. -/
theorem reflEndpointZeroInversions_eq_map_Iio
    (n : ℕ) (τ : Ranking n) :
    reflEndpointZeroInversions n τ =
      (Finset.Iio (rankOf τ (0 : Candidate n))).map
        ⟨fun i : Candidate n => ((0 : Candidate n), τ i),
          by
            intro i j h
            exact τ.injective (Prod.ext_iff.mp h).2⟩ := by
  classical
  ext ab
  constructor
  · intro hab
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [reflEndpointZeroInversions, inversionFinset] using
        (Finset.mem_filter.mp hab).1
    have hab_left : ab.1 = (0 : Candidate n) := by
      simpa [reflEndpointZeroInversions] using (Finset.mem_filter.mp hab).2
    refine Finset.mem_map.mpr ?_
    refine ⟨rankOf τ ab.2, ?_, ?_⟩
    · simpa [hab_left] using hinv.2
    · ext <;> simp [hab_left, rankOf]
  · intro hab
    rcases Finset.mem_map.mp hab with ⟨i, hi, hab_eq⟩
    have hi_lt : i < rankOf τ (0 : Candidate n) := by
      simpa using hi
    have hτi_ne_zero : τ i ≠ (0 : Candidate n) := by
      intro hτi
      have hi_eq : i = rankOf τ (0 : Candidate n) := by
        apply τ.injective
        simp [rankOf, hτi]
      exact (lt_irrefl i) (hi_lt.trans_eq hi_eq.symm)
    have hcenter : (0 : Candidate n) < τ i := by
      change (0 : ℕ) < (τ i : ℕ)
      have hne : (τ i : ℕ) ≠ 0 := by
        intro hval
        exact hτi_ne_zero (Fin.ext hval)
      omega
    have hrank : rankOf τ (τ i) < rankOf τ (0 : Candidate n) := by
      simpa [rankOf] using hi_lt
    have hcenter_rank :
        rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) (τ i) := by
      simpa [rankOf] using hcenter
    rw [← hab_eq]
    simp [reflEndpointZeroInversions, inversionFinset, invertedPair,
      hcenter_rank, hrank]

/-- For the identity center, inversions involving the worst endpoint are exactly
the candidates placed after it. -/
theorem reflEndpointLastInversions_eq_map_Ioi
    (n : ℕ) (τ : Ranking n) :
    reflEndpointLastInversions n τ =
      (Finset.Ioi (rankOf τ (reflLastCandidate n))).map
        ⟨fun i : Candidate n => (τ i, reflLastCandidate n),
          by
            intro i j h
            exact τ.injective (Prod.ext_iff.mp h).1⟩ := by
  classical
  let last : Candidate n := reflLastCandidate n
  ext ab
  constructor
  · intro hab
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [reflEndpointLastInversions, inversionFinset, last] using
        (Finset.mem_filter.mp hab).1
    have hab_right : ab.2 = last := by
      simpa [reflEndpointLastInversions, last] using
        (Finset.mem_filter.mp hab).2
    refine Finset.mem_map.mpr ?_
    refine ⟨rankOf τ ab.1, ?_, ?_⟩
    · simpa [hab_right] using hinv.2
    · ext <;> simp [hab_right, rankOf, last]
  · intro hab
    rcases Finset.mem_map.mp hab with ⟨i, hi, hab_eq⟩
    have hlast_lt_i : rankOf τ last < i := by
      simpa [last] using hi
    have hτi_ne_last : τ i ≠ last := by
      intro hτi
      have hi_eq : i = rankOf τ last := by
        apply τ.injective
        simp [rankOf, hτi]
      exact (lt_irrefl i) (hi_eq ▸ hlast_lt_i)
    have hcenter : τ i < last := by
      change (τ i : ℕ) < n + 1
      have hle : (τ i : ℕ) ≤ n + 1 := Nat.le_of_lt_succ (τ i).isLt
      have hne : (τ i : ℕ) ≠ n + 1 := by
        intro hval
        exact hτi_ne_last (Fin.ext hval)
      omega
    have hrank : rankOf τ last < rankOf τ (τ i) := by
      simpa [rankOf] using hlast_lt_i
    have hcenter_rank :
        rankOf (Equiv.refl (Candidate n)) (τ i) <
          rankOf (Equiv.refl (Candidate n)) (reflLastCandidate n) := by
      simpa [rankOf, last] using hcenter
    rw [← hab_eq]
    simp [reflEndpointLastInversions, inversionFinset, invertedPair,
      hcenter_rank, hrank, last]

theorem reflEndpointZeroInversions_card
    (n : ℕ) (τ : Ranking n) :
    (reflEndpointZeroInversions n τ).card =
      (rankOf τ (0 : Candidate n) : ℕ) := by
  rw [reflEndpointZeroInversions_eq_map_Iio]
  simp

theorem reflEndpointLastInversions_card
    (n : ℕ) (τ : Ranking n) :
    (reflEndpointLastInversions n τ).card =
      n + 1 - (rankOf τ (reflLastCandidate n) : ℕ) := by
  rw [reflEndpointLastInversions_eq_map_Ioi]
  simp [reflLastCandidate]

theorem inversionFinsetInvolving_zero_eq_reflEndpointZeroInversions
    (n : ℕ) (τ : Ranking n) :
    inversionFinsetInvolving (Equiv.refl (Candidate n)) τ
        (0 : Candidate n) =
      reflEndpointZeroInversions n τ := by
  classical
  ext ab
  constructor
  · intro hab
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinsetInvolving, inversionFinset] using
        (Finset.mem_filter.mp hab).1
    have hinvolves : ab.1 = (0 : Candidate n) ∨ ab.2 = (0 : Candidate n) := by
      simpa [inversionFinsetInvolving] using (Finset.mem_filter.mp hab).2
    have hleft : ab.1 = (0 : Candidate n) := by
      rcases hinvolves with h | h
      · exact h
      · exfalso
        have hbad : ab.1 < (0 : Candidate n) := by
          simpa [rankOf, h] using hinv.1
        exact not_lt_bot hbad
    simp [reflEndpointZeroInversions, inversionFinset, hinv, hleft]
  · intro hab
    have hinv : ab ∈ inversionFinset (Equiv.refl (Candidate n)) τ := by
      simpa [reflEndpointZeroInversions] using
        (Finset.mem_filter.mp hab).1
    have hleft : ab.1 = (0 : Candidate n) := by
      simpa [reflEndpointZeroInversions] using (Finset.mem_filter.mp hab).2
    simp [inversionFinsetInvolving, hinv, hleft]

theorem inversionFinsetInvolving_last_eq_reflEndpointLastInversions
    (n : ℕ) (τ : Ranking n) :
    inversionFinsetInvolving (Equiv.refl (Candidate n)) τ
        (reflLastCandidate n) =
      reflEndpointLastInversions n τ := by
  classical
  ext ab
  constructor
  · intro hab
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinsetInvolving, inversionFinset] using
        (Finset.mem_filter.mp hab).1
    have hinvolves :
        ab.1 = reflLastCandidate n ∨ ab.2 = reflLastCandidate n := by
      simpa [inversionFinsetInvolving] using (Finset.mem_filter.mp hab).2
    have hright : ab.2 = reflLastCandidate n := by
      rcases hinvolves with h | h
      · exfalso
        have hbad : reflLastCandidate n < ab.2 := by
          simpa [rankOf, h] using hinv.1
        change n + 1 < (ab.2 : ℕ) at hbad
        have hle : (ab.2 : ℕ) ≤ n + 1 := Nat.le_of_lt_succ ab.2.isLt
        omega
      · exact h
    simp [reflEndpointLastInversions, inversionFinset, hinv, hright]
  · intro hab
    have hinv : ab ∈ inversionFinset (Equiv.refl (Candidate n)) τ := by
      simpa [reflEndpointLastInversions] using
        (Finset.mem_filter.mp hab).1
    have hright : ab.2 = reflLastCandidate n := by
      simpa [reflEndpointLastInversions] using (Finset.mem_filter.mp hab).2
    simp [inversionFinsetInvolving, hinv, hright]

theorem inversionFinsetNotInvolving_zero_card_rankingPeelBestOrderEquiv
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    (inversionFinsetNotInvolving
        (Equiv.refl (Candidate (n + 1)))
        (rankingPeelBestOrderEquiv n (p, σ))
        (0 : Candidate (n + 1))).card =
      kendallTau (Equiv.refl (Candidate n)) σ := by
  classical
  let τ : Ranking (n + 1) := rankingPeelBestOrderEquiv n (p, σ)
  have hcard :
      (inversionFinset (Equiv.refl (Candidate n)) σ).card =
        (inversionFinsetNotInvolving
          (Equiv.refl (Candidate (n + 1))) τ
          (0 : Candidate (n + 1))).card := by
    refine Finset.card_bij
      (i := fun ab _ => (ab.1.succ, ab.2.succ)) ?hi ?hinj ?hsurj
    · intro ab hab
      have hinv : invertedPair (Equiv.refl (Candidate n)) σ ab := by
        simpa [inversionFinset] using hab
      have hcenter : ab.1.succ < ab.2.succ := by
        change (ab.1 : ℕ) + 1 < (ab.2 : ℕ) + 1
        have hlt : (ab.1 : ℕ) < (ab.2 : ℕ) := hinv.1
        omega
      have hrank :
          rankOf τ ab.2.succ < rankOf τ ab.1.succ :=
        (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
          n p σ ab.2 ab.1).mpr hinv.2
      have hinv_full :
          invertedPair (Equiv.refl (Candidate (n + 1))) τ
            (ab.1.succ, ab.2.succ) :=
        ⟨by simpa [rankOf] using hcenter, hrank⟩
      simp [inversionFinsetNotInvolving, inversionFinset, hinv_full]
    · intro ab₁ _ ab₂ _ h
      exact Prod.ext
        (Fin.succ_injective _ (Prod.ext_iff.mp h).1)
        (Fin.succ_injective _ (Prod.ext_iff.mp h).2)
    · intro cd hcd
      have hinv_full : invertedPair (Equiv.refl (Candidate (n + 1))) τ cd := by
        simpa [inversionFinsetNotInvolving, inversionFinset] using
          (Finset.mem_filter.mp hcd).1
      have hnot : ¬(cd.1 = (0 : Candidate (n + 1)) ∨
          cd.2 = (0 : Candidate (n + 1))) := by
        simpa [inversionFinsetNotInvolving] using
          (Finset.mem_filter.mp hcd).2
      have hcd1_ne : cd.1 ≠ (0 : Candidate (n + 1)) := fun h => hnot (Or.inl h)
      have hcd2_ne : cd.2 ≠ (0 : Candidate (n + 1)) := fun h => hnot (Or.inr h)
      let pre : Candidate n × Candidate n :=
        (cd.1.pred hcd1_ne, cd.2.pred hcd2_ne)
      have hcd1 : pre.1.succ = cd.1 := by
        dsimp [pre]
        exact Fin.succ_pred cd.1 hcd1_ne
      have hcd2 : pre.2.succ = cd.2 := by
        dsimp [pre]
        exact Fin.succ_pred cd.2 hcd2_ne
      have hcenter : pre.1 < pre.2 := by
        change (pre.1 : ℕ) < (pre.2 : ℕ)
        have hlt : (cd.1 : ℕ) < (cd.2 : ℕ) := by
          simpa [rankOf] using hinv_full.1
        have h1pos : 0 < (cd.1 : ℕ) := by
          by_contra hle
          have hzero : (cd.1 : ℕ) = 0 := by omega
          exact hcd1_ne (Fin.ext hzero)
        have h2pos : 0 < (cd.2 : ℕ) := by
          by_contra hle
          have hzero : (cd.2 : ℕ) = 0 := by omega
          exact hcd2_ne (Fin.ext hzero)
        dsimp [pre]
        simp
        omega
      have hrank : rankOf σ pre.2 < rankOf σ pre.1 := by
        have hfull :
            rankOf τ pre.2.succ < rankOf τ pre.1.succ := by
          simpa [hcd1, hcd2] using hinv_full.2
        exact (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
          n p σ pre.2 pre.1).mp hfull
      have hpre : pre ∈ inversionFinset (Equiv.refl (Candidate n)) σ := by
        simp [inversionFinset, invertedPair, rankOf, hcenter]
        simpa [rankOf] using hrank
      refine ⟨pre, hpre, ?_⟩
      exact Prod.ext hcd1 hcd2
  simpa [kendallTau, τ] using hcard.symm

theorem inversionFinsetNotInvolving_last_card_rankingPeelWorstOrderEquiv
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    (inversionFinsetNotInvolving
        (Equiv.refl (Candidate (n + 1)))
        (rankingPeelWorstOrderEquiv n (p, σ))
        (reflLastCandidate (n + 1))).card =
      kendallTau (Equiv.refl (Candidate n)) σ := by
  classical
  let τ : Ranking (n + 1) := rankingPeelWorstOrderEquiv n (p, σ)
  have hcard :
      (inversionFinset (Equiv.refl (Candidate n)) σ).card =
        (inversionFinsetNotInvolving
          (Equiv.refl (Candidate (n + 1))) τ
          (reflLastCandidate (n + 1))).card := by
    refine Finset.card_bij
      (i := fun ab _ => (ab.1.castSucc, ab.2.castSucc)) ?hi ?hinj ?hsurj
    · intro ab hab
      have hinv : invertedPair (Equiv.refl (Candidate n)) σ ab := by
        simpa [inversionFinset] using hab
      have hcenter : ab.1.castSucc < ab.2.castSucc := by
        change (ab.1 : ℕ) < (ab.2 : ℕ)
        simpa [rankOf] using hinv.1
      have hrank :
          rankOf τ ab.2.castSucc < rankOf τ ab.1.castSucc :=
        (rankOf_rankingPeelWorstOrderEquiv_castSucc_lt_iff
          n p σ ab.2 ab.1).mpr hinv.2
      have hinv_full :
          invertedPair (Equiv.refl (Candidate (n + 1))) τ
            (ab.1.castSucc, ab.2.castSucc) :=
        ⟨by simpa [rankOf] using hcenter, hrank⟩
      have hleft_ne :
          ab.1.castSucc ≠ reflLastCandidate (n + 1) := by
        intro hlast
        have hval := congrArg Fin.val hlast
        simp [reflLastCandidate] at hval
        have hlt := ab.1.isLt
        omega
      have hright_ne :
          ab.2.castSucc ≠ reflLastCandidate (n + 1) := by
        intro hlast
        have hval := congrArg Fin.val hlast
        simp [reflLastCandidate] at hval
        have hlt := ab.2.isLt
        omega
      simp [inversionFinsetNotInvolving, inversionFinset, hinv_full,
        hleft_ne, hright_ne]
    · intro ab₁ _ ab₂ _ h
      exact Prod.ext
        (Fin.castSucc_injective _ (Prod.ext_iff.mp h).1)
        (Fin.castSucc_injective _ (Prod.ext_iff.mp h).2)
    · intro cd hcd
      have hinv_full : invertedPair (Equiv.refl (Candidate (n + 1))) τ cd := by
        simpa [inversionFinsetNotInvolving, inversionFinset] using
          (Finset.mem_filter.mp hcd).1
      have hnot : ¬(cd.1 = reflLastCandidate (n + 1) ∨
          cd.2 = reflLastCandidate (n + 1)) := by
        simpa [inversionFinsetNotInvolving] using
          (Finset.mem_filter.mp hcd).2
      have hcd1_ne : cd.1 ≠ reflLastCandidate (n + 1) :=
        fun h => hnot (Or.inl h)
      have hcd2_ne : cd.2 ≠ reflLastCandidate (n + 1) :=
        fun h => hnot (Or.inr h)
      let pre : Candidate n × Candidate n :=
        (cd.1.castPred (by simpa [reflLastCandidate] using hcd1_ne),
          cd.2.castPred (by simpa [reflLastCandidate] using hcd2_ne))
      have hcd1 : pre.1.castSucc = cd.1 := by
        dsimp [pre]
        exact Fin.castSucc_castPred cd.1
          (by simpa [reflLastCandidate] using hcd1_ne)
      have hcd2 : pre.2.castSucc = cd.2 := by
        dsimp [pre]
        exact Fin.castSucc_castPred cd.2
          (by simpa [reflLastCandidate] using hcd2_ne)
      have hcenter : pre.1 < pre.2 := by
        change (pre.1 : ℕ) < (pre.2 : ℕ)
        have hlt : (cd.1 : ℕ) < (cd.2 : ℕ) := by
          simpa [rankOf] using hinv_full.1
        dsimp [pre]
        simpa using hlt
      have hrank : rankOf σ pre.2 < rankOf σ pre.1 := by
        have hfull :
            rankOf τ pre.2.castSucc < rankOf τ pre.1.castSucc := by
          simpa [hcd1, hcd2] using hinv_full.2
        exact (rankOf_rankingPeelWorstOrderEquiv_castSucc_lt_iff
          n p σ pre.2 pre.1).mp hfull
      have hpre : pre ∈ inversionFinset (Equiv.refl (Candidate n)) σ := by
        simp [inversionFinset, invertedPair, rankOf, hcenter]
        simpa [rankOf] using hrank
      refine ⟨pre, hpre, ?_⟩
      exact Prod.ext hcd1 hcd2
  simpa [kendallTau, τ] using hcard.symm

theorem kendallTau_rankingPeelBestOrderEquiv
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    kendallTau (Equiv.refl (Candidate (n + 1)))
        (rankingPeelBestOrderEquiv n (p, σ)) =
      (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
  let τ : Ranking (n + 1) := rankingPeelBestOrderEquiv n (p, σ)
  have hsplit :=
    inversionFinsetInvolving_card_add_notInvolving_card
      (ρ := Equiv.refl (Candidate (n + 1))) (π := τ)
      (c := (0 : Candidate (n + 1)))
  have hzero :
      (inversionFinsetInvolving (Equiv.refl (Candidate (n + 1))) τ
          (0 : Candidate (n + 1))).card = (p : ℕ) := by
    rw [inversionFinsetInvolving_zero_eq_reflEndpointZeroInversions]
    rw [reflEndpointZeroInversions_card]
    simp [τ]
  have hnot :
      (inversionFinsetNotInvolving (Equiv.refl (Candidate (n + 1))) τ
          (0 : Candidate (n + 1))).card =
        kendallTau (Equiv.refl (Candidate n)) σ := by
    simpa [τ] using
      inversionFinsetNotInvolving_zero_card_rankingPeelBestOrderEquiv n p σ
  rw [hzero, hnot] at hsplit
  simpa [kendallTau, τ, Nat.add_comm] using hsplit.symm

theorem kendallTau_rankingPeelWorstOrderEquiv
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    kendallTau (Equiv.refl (Candidate (n + 1)))
        (rankingPeelWorstOrderEquiv n (p, σ)) =
      (n + 2 - (p : ℕ)) + kendallTau (Equiv.refl (Candidate n)) σ := by
  let τ : Ranking (n + 1) := rankingPeelWorstOrderEquiv n (p, σ)
  have hsplit :=
    inversionFinsetInvolving_card_add_notInvolving_card
      (ρ := Equiv.refl (Candidate (n + 1))) (π := τ)
      (c := reflLastCandidate (n + 1))
  have hlast :
      (inversionFinsetInvolving (Equiv.refl (Candidate (n + 1))) τ
          (reflLastCandidate (n + 1))).card =
        n + 2 - (p : ℕ) := by
    rw [inversionFinsetInvolving_last_eq_reflEndpointLastInversions]
    rw [reflEndpointLastInversions_card]
    simp [τ]
  have hnot :
      (inversionFinsetNotInvolving (Equiv.refl (Candidate (n + 1))) τ
          (reflLastCandidate (n + 1))).card =
        kendallTau (Equiv.refl (Candidate n)) σ := by
    simpa [τ] using
      inversionFinsetNotInvolving_last_card_rankingPeelWorstOrderEquiv n p σ
  rw [hlast, hnot] at hsplit
  simpa [kendallTau, τ] using hsplit.symm

theorem reflPairCorrectWeight_succ_succ
    (n : ℕ) (q : ℝ) (r s : Candidate n) :
    reflPairCorrectWeight (n + 1) q r.succ s.succ =
      candidateRankPowerSum (n + 1) q *
        reflPairCorrectWeight n q r s := by
  classical
  let e := rankingPeelBestOrderEquiv n
  unfold reflPairCorrectWeight
  calc
    ∑ τ : Ranking (n + 1),
        (if r.succ < s.succ ∧ rankOf τ r.succ < rankOf τ s.succ then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
        else
          0)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        (if r.succ < s.succ ∧
            rankOf (e pe) r.succ < rankOf (e pe) s.succ then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe)
        else
          0) := by
          simpa [e] using
            (Equiv.sum_comp e
              (fun τ : Ranking (n + 1) =>
                if r.succ < s.succ ∧ rankOf τ r.succ < rankOf τ s.succ then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
                else
                  0)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        (if r.succ < s.succ ∧
            rankOf (e (p, σ)) r.succ < rankOf (e (p, σ)) s.succ then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
        else
          0) := by
          simpa using
            (Finset.sum_product'
              (Finset.univ : Finset (Candidate (n + 1)))
              (Finset.univ : Finset (Ranking n))
              (fun p σ =>
                if r.succ < s.succ ∧
                    rankOf (e (p, σ)) r.succ < rankOf (e (p, σ)) s.succ then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
                else
                  0))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (p : ℕ) *
          (if r < s ∧ rankOf σ r < rankOf σ s then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hcenter_iff : r.succ < s.succ ↔ r < s := by
            constructor <;> intro h
            · change (r : ℕ) + 1 < (s : ℕ) + 1 at h
              change (r : ℕ) < (s : ℕ)
              omega
            · change (r : ℕ) + 1 < (s : ℕ) + 1
              have h' : (r : ℕ) < (s : ℕ) := h
              omega
          have hrank_iff :
              rankOf (e (p, σ)) r.succ < rankOf (e (p, σ)) s.succ ↔
                rankOf σ r < rankOf σ s := by
            simpa [e] using
              rankOf_rankingPeelBestOrderEquiv_succ_lt_iff n p σ r s
          have hkend :
              kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) =
                (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
            simpa [e] using kendallTau_rankingPeelBestOrderEquiv n p σ
          by_cases hcond : r < s ∧ rankOf σ r < rankOf σ s
          · have hcond_full :
                r.succ < s.succ ∧
                  rankOf (e (p, σ)) r.succ < rankOf (e (p, σ)) s.succ :=
              ⟨hcenter_iff.mpr hcond.1, hrank_iff.mpr hcond.2⟩
            rw [if_pos hcond_full, if_pos hcond, hkend, pow_add]
          · have hcond_full :
                ¬(r.succ < s.succ ∧
                  rankOf (e (p, σ)) r.succ < rankOf (e (p, σ)) s.succ) := by
              intro h
              exact hcond ⟨hcenter_iff.mp h.1, hrank_iff.mp h.2⟩
            rw [if_neg hcond_full, if_neg hcond]
            ring
    _ =
      ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          (∑ σ : Ranking n,
            if r < s ∧ rankOf σ r < rankOf σ s then
              q ^ kendallTau (Equiv.refl (Candidate n)) σ
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.mul_sum]
    _ =
      candidateRankPowerSum (n + 1) q *
        (∑ σ : Ranking n,
          if r < s ∧ rankOf σ r < rankOf σ s then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          unfold candidateRankPowerSum
          rw [Finset.sum_mul]

theorem reflPairWrongWeight_succ_succ
    (n : ℕ) (q : ℝ) (r s : Candidate n) :
    reflPairWrongWeight (n + 1) q r.succ s.succ =
      candidateRankPowerSum (n + 1) q *
        reflPairWrongWeight n q r s := by
  classical
  let e := rankingPeelBestOrderEquiv n
  unfold reflPairWrongWeight
  calc
    ∑ τ : Ranking (n + 1),
        (if r.succ < s.succ ∧ rankOf τ s.succ < rankOf τ r.succ then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
        else
          0)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        (if r.succ < s.succ ∧
            rankOf (e pe) s.succ < rankOf (e pe) r.succ then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe)
        else
          0) := by
          simpa [e] using
            (Equiv.sum_comp e
              (fun τ : Ranking (n + 1) =>
                if r.succ < s.succ ∧ rankOf τ s.succ < rankOf τ r.succ then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
                else
                  0)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        (if r.succ < s.succ ∧
            rankOf (e (p, σ)) s.succ < rankOf (e (p, σ)) r.succ then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
        else
          0) := by
          simpa using
            (Finset.sum_product'
              (Finset.univ : Finset (Candidate (n + 1)))
              (Finset.univ : Finset (Ranking n))
              (fun p σ =>
                if r.succ < s.succ ∧
                    rankOf (e (p, σ)) s.succ < rankOf (e (p, σ)) r.succ then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
                else
                  0))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (p : ℕ) *
          (if r < s ∧ rankOf σ s < rankOf σ r then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hcenter_iff : r.succ < s.succ ↔ r < s := by
            constructor <;> intro h
            · change (r : ℕ) + 1 < (s : ℕ) + 1 at h
              change (r : ℕ) < (s : ℕ)
              omega
            · change (r : ℕ) + 1 < (s : ℕ) + 1
              have h' : (r : ℕ) < (s : ℕ) := h
              omega
          have hrank_iff :
              rankOf (e (p, σ)) s.succ < rankOf (e (p, σ)) r.succ ↔
                rankOf σ s < rankOf σ r := by
            simpa [e] using
              rankOf_rankingPeelBestOrderEquiv_succ_lt_iff n p σ s r
          have hkend :
              kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) =
                (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
            simpa [e] using kendallTau_rankingPeelBestOrderEquiv n p σ
          by_cases hcond : r < s ∧ rankOf σ s < rankOf σ r
          · have hcond_full :
                r.succ < s.succ ∧
                  rankOf (e (p, σ)) s.succ < rankOf (e (p, σ)) r.succ :=
              ⟨hcenter_iff.mpr hcond.1, hrank_iff.mpr hcond.2⟩
            rw [if_pos hcond_full, if_pos hcond, hkend, pow_add]
          · have hcond_full :
                ¬(r.succ < s.succ ∧
                  rankOf (e (p, σ)) s.succ < rankOf (e (p, σ)) r.succ) := by
              intro h
              exact hcond ⟨hcenter_iff.mp h.1, hrank_iff.mp h.2⟩
            rw [if_neg hcond_full, if_neg hcond]
            ring
    _ =
      ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          (∑ σ : Ranking n,
            if r < s ∧ rankOf σ s < rankOf σ r then
              q ^ kendallTau (Equiv.refl (Candidate n)) σ
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.mul_sum]
    _ =
      candidateRankPowerSum (n + 1) q *
        (∑ σ : Ranking n,
          if r < s ∧ rankOf σ s < rankOf σ r then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          unfold candidateRankPowerSum
          rw [Finset.sum_mul]

theorem reflPairCorrectWeight_castSucc_castSucc
    (n : ℕ) (q : ℝ) (r s : Candidate n) :
    reflPairCorrectWeight (n + 1) q r.castSucc s.castSucc =
      candidateRankReversePowerSum (n + 1) q *
        reflPairCorrectWeight n q r s := by
  classical
  let e := rankingPeelWorstOrderEquiv n
  unfold reflPairCorrectWeight
  calc
    ∑ τ : Ranking (n + 1),
        (if r.castSucc < s.castSucc ∧
            rankOf τ r.castSucc < rankOf τ s.castSucc then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
        else
          0)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        (if r.castSucc < s.castSucc ∧
            rankOf (e pe) r.castSucc < rankOf (e pe) s.castSucc then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe)
        else
          0) := by
          simpa [e] using
            (Equiv.sum_comp e
              (fun τ : Ranking (n + 1) =>
                if r.castSucc < s.castSucc ∧
                    rankOf τ r.castSucc < rankOf τ s.castSucc then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
                else
                  0)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        (if r.castSucc < s.castSucc ∧
            rankOf (e (p, σ)) r.castSucc < rankOf (e (p, σ)) s.castSucc then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
        else
          0) := by
          simpa using
            (Finset.sum_product'
              (Finset.univ : Finset (Candidate (n + 1)))
              (Finset.univ : Finset (Ranking n))
              (fun p σ =>
                if r.castSucc < s.castSucc ∧
                    rankOf (e (p, σ)) r.castSucc < rankOf (e (p, σ)) s.castSucc then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
                else
                  0))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (n + 2 - (p : ℕ)) *
          (if r < s ∧ rankOf σ r < rankOf σ s then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hcenter_iff : r.castSucc < s.castSucc ↔ r < s := by
            change (r : ℕ) < (s : ℕ) ↔ (r : ℕ) < (s : ℕ)
            rfl
          have hrank_iff :
              rankOf (e (p, σ)) r.castSucc < rankOf (e (p, σ)) s.castSucc ↔
                rankOf σ r < rankOf σ s := by
            simpa [e] using
              rankOf_rankingPeelWorstOrderEquiv_castSucc_lt_iff n p σ r s
          have hkend :
              kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) =
                (n + 2 - (p : ℕ)) +
                  kendallTau (Equiv.refl (Candidate n)) σ := by
            simpa [e] using kendallTau_rankingPeelWorstOrderEquiv n p σ
          by_cases hcond : r < s ∧ rankOf σ r < rankOf σ s
          · have hcond_full :
                r.castSucc < s.castSucc ∧
                  rankOf (e (p, σ)) r.castSucc < rankOf (e (p, σ)) s.castSucc :=
              ⟨hcenter_iff.mpr hcond.1, hrank_iff.mpr hcond.2⟩
            rw [if_pos hcond_full, if_pos hcond, hkend, pow_add]
          · have hcond_full :
                ¬(r.castSucc < s.castSucc ∧
                  rankOf (e (p, σ)) r.castSucc < rankOf (e (p, σ)) s.castSucc) := by
              intro h
              exact hcond ⟨hcenter_iff.mp h.1, hrank_iff.mp h.2⟩
            rw [if_neg hcond_full, if_neg hcond]
            ring
    _ =
      ∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          (∑ σ : Ranking n,
            if r < s ∧ rankOf σ r < rankOf σ s then
              q ^ kendallTau (Equiv.refl (Candidate n)) σ
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.mul_sum]
    _ =
      candidateRankReversePowerSum (n + 1) q *
        (∑ σ : Ranking n,
          if r < s ∧ rankOf σ r < rankOf σ s then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          unfold candidateRankReversePowerSum
          rw [Finset.sum_mul]

theorem reflPairWrongWeight_castSucc_castSucc
    (n : ℕ) (q : ℝ) (r s : Candidate n) :
    reflPairWrongWeight (n + 1) q r.castSucc s.castSucc =
      candidateRankReversePowerSum (n + 1) q *
        reflPairWrongWeight n q r s := by
  classical
  let e := rankingPeelWorstOrderEquiv n
  unfold reflPairWrongWeight
  calc
    ∑ τ : Ranking (n + 1),
        (if r.castSucc < s.castSucc ∧
            rankOf τ s.castSucc < rankOf τ r.castSucc then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
        else
          0)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        (if r.castSucc < s.castSucc ∧
            rankOf (e pe) s.castSucc < rankOf (e pe) r.castSucc then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe)
        else
          0) := by
          simpa [e] using
            (Equiv.sum_comp e
              (fun τ : Ranking (n + 1) =>
                if r.castSucc < s.castSucc ∧
                    rankOf τ s.castSucc < rankOf τ r.castSucc then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ
                else
                  0)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        (if r.castSucc < s.castSucc ∧
            rankOf (e (p, σ)) s.castSucc < rankOf (e (p, σ)) r.castSucc then
          q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
        else
          0) := by
          simpa using
            (Finset.sum_product'
              (Finset.univ : Finset (Candidate (n + 1)))
              (Finset.univ : Finset (Ranking n))
              (fun p σ =>
                if r.castSucc < s.castSucc ∧
                    rankOf (e (p, σ)) s.castSucc < rankOf (e (p, σ)) r.castSucc then
                  q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ))
                else
                  0))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (n + 2 - (p : ℕ)) *
          (if r < s ∧ rankOf σ s < rankOf σ r then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hcenter_iff : r.castSucc < s.castSucc ↔ r < s := by
            change (r : ℕ) < (s : ℕ) ↔ (r : ℕ) < (s : ℕ)
            rfl
          have hrank_iff :
              rankOf (e (p, σ)) s.castSucc < rankOf (e (p, σ)) r.castSucc ↔
                rankOf σ s < rankOf σ r := by
            simpa [e] using
              rankOf_rankingPeelWorstOrderEquiv_castSucc_lt_iff n p σ s r
          have hkend :
              kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) =
                (n + 2 - (p : ℕ)) +
                  kendallTau (Equiv.refl (Candidate n)) σ := by
            simpa [e] using kendallTau_rankingPeelWorstOrderEquiv n p σ
          by_cases hcond : r < s ∧ rankOf σ s < rankOf σ r
          · have hcond_full :
                r.castSucc < s.castSucc ∧
                  rankOf (e (p, σ)) s.castSucc < rankOf (e (p, σ)) r.castSucc :=
              ⟨hcenter_iff.mpr hcond.1, hrank_iff.mpr hcond.2⟩
            rw [if_pos hcond_full, if_pos hcond, hkend, pow_add]
          · have hcond_full :
                ¬(r.castSucc < s.castSucc ∧
                  rankOf (e (p, σ)) s.castSucc < rankOf (e (p, σ)) r.castSucc) := by
              intro h
              exact hcond ⟨hcenter_iff.mp h.1, hrank_iff.mp h.2⟩
            rw [if_neg hcond_full, if_neg hcond]
            ring
    _ =
      ∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          (∑ σ : Ranking n,
            if r < s ∧ rankOf σ s < rankOf σ r then
              q ^ kendallTau (Equiv.refl (Candidate n)) σ
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.mul_sum]
    _ =
      candidateRankReversePowerSum (n + 1) q *
        (∑ σ : Ranking n,
          if r < s ∧ rankOf σ s < rankOf σ r then
            q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else
            0) := by
          unfold candidateRankReversePowerSum
          rw [Finset.sum_mul]

theorem reflEndpointInversions_eq_union
    (n : ℕ) (τ : Ranking n) :
    reflEndpointInversions n τ =
      reflEndpointZeroInversions n τ ∪ reflEndpointLastInversions n τ := by
  classical
  ext ab
  simp [reflEndpointInversions, reflEndpointZeroInversions,
    reflEndpointLastInversions, and_or_left]

theorem reflEndpointInversions_card_of_correct
    (n : ℕ) (τ : Ranking n)
    (hcorrect :
      rankOf τ (0 : Candidate n) < rankOf τ (reflLastCandidate n)) :
    (reflEndpointInversions n τ).card =
      pairPositionCorrectExp n
        (rankOf τ (0 : Candidate n))
        (rankOf τ (reflLastCandidate n)) := by
  classical
  rw [reflEndpointInversions_eq_union]
  have hdisj :
      Disjoint (reflEndpointZeroInversions n τ)
        (reflEndpointLastInversions n τ) := by
    rw [Finset.disjoint_left]
    intro ab hab0 hablast
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [reflEndpointZeroInversions, inversionFinset] using
        (Finset.mem_filter.mp hab0).1
    have hleft : ab.1 = (0 : Candidate n) := by
      simpa [reflEndpointZeroInversions] using (Finset.mem_filter.mp hab0).2
    have hright : ab.2 = reflLastCandidate n := by
      simpa [reflEndpointLastInversions] using
        (Finset.mem_filter.mp hablast).2
    have hwrong :
        rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n) := by
      simpa [hleft, hright] using hinv.2
    exact (not_lt_of_gt hcorrect) hwrong
  rw [Finset.card_union_of_disjoint hdisj]
  rw [reflEndpointZeroInversions_card, reflEndpointLastInversions_card]
  unfold pairPositionCorrectExp
  rfl

theorem reflEndpointInversions_inter_eq_singleton_of_wrong
    (n : ℕ) (τ : Ranking n)
    (hwrong :
      rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n)) :
    reflEndpointZeroInversions n τ ∩ reflEndpointLastInversions n τ =
      {((0 : Candidate n), reflLastCandidate n)} := by
  classical
  ext ab
  constructor
  · intro hab
    have hleft : ab.1 = (0 : Candidate n) := by
      simpa [reflEndpointZeroInversions] using
        (Finset.mem_filter.mp (Finset.mem_inter.mp hab).1).2
    have hright : ab.2 = reflLastCandidate n := by
      simpa [reflEndpointLastInversions] using
        (Finset.mem_filter.mp (Finset.mem_inter.mp hab).2).2
    exact Finset.mem_singleton.mpr (Prod.ext hleft hright)
  · intro hab
    have hab_eq : ab = ((0 : Candidate n), reflLastCandidate n) :=
      Finset.mem_singleton.mp hab
    subst ab
    have hcenter : (0 : Candidate n) < reflLastCandidate n := by
      change (0 : ℕ) < n + 1
      omega
    have hinv :
        invertedPair (Equiv.refl (Candidate n)) τ
          ((0 : Candidate n), reflLastCandidate n) :=
      ⟨by simpa [rankOf] using hcenter, hwrong⟩
    simp [reflEndpointZeroInversions, reflEndpointLastInversions,
      inversionFinset, hinv]

theorem reflEndpointInversions_card_of_wrong
    (n : ℕ) (τ : Ranking n)
    (hwrong :
      rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n)) :
    (reflEndpointInversions n τ).card =
      pairPositionWrongExp n
        (rankOf τ (0 : Candidate n))
        (rankOf τ (reflLastCandidate n)) := by
  classical
  rw [reflEndpointInversions_eq_union]
  have hcard_union := Finset.card_union
    (reflEndpointZeroInversions n τ) (reflEndpointLastInversions n τ)
  rw [hcard_union]
  rw [reflEndpointInversions_inter_eq_singleton_of_wrong n τ hwrong]
  rw [reflEndpointZeroInversions_card, reflEndpointLastInversions_card]
  simp
  unfold pairPositionWrongExp
  omega

theorem reflInversionFinset_eq_endpoint_union_middle
    (n : ℕ) (τ : Ranking n) :
    inversionFinset (Equiv.refl (Candidate n)) τ =
      reflEndpointInversions n τ ∪ reflMiddleInversions n τ := by
  classical
  ext ab
  by_cases hleft : ab.1 = (0 : Candidate n)
  · simp [reflEndpointInversions, reflMiddleInversions, hleft]
  · by_cases hright : ab.2 = reflLastCandidate n
    · simp [reflEndpointInversions, reflMiddleInversions, hleft, hright]
    · simp [reflEndpointInversions, reflMiddleInversions, hleft, hright]

theorem reflEndpointInversions_disjoint_middle
    (n : ℕ) (τ : Ranking n) :
    Disjoint (reflEndpointInversions n τ) (reflMiddleInversions n τ) := by
  classical
  rw [Finset.disjoint_left]
  intro ab hend hmid
  have hend' :
      ab.1 = (0 : Candidate n) ∨ ab.2 = reflLastCandidate n := by
    simpa [reflEndpointInversions] using (Finset.mem_filter.mp hend).2
  have hmid' :
      ab.1 ≠ (0 : Candidate n) ∧ ab.2 ≠ reflLastCandidate n := by
    simpa [reflMiddleInversions] using (Finset.mem_filter.mp hmid).2
  rcases hend' with hleft | hright
  · exact hmid'.1 hleft
  · exact hmid'.2 hright

theorem kendallTau_refl_eq_endpoint_add_middle
    (n : ℕ) (τ : Ranking n) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      (reflEndpointInversions n τ).card +
        (reflMiddleInversions n τ).card := by
  rw [kendallTau]
  rw [reflInversionFinset_eq_endpoint_union_middle]
  exact Finset.card_union_of_disjoint
    (reflEndpointInversions_disjoint_middle n τ)

theorem kendallTau_refl_eq_correct_endpointExp_add_middle
    (n : ℕ) (τ : Ranking n)
    (hcorrect :
      rankOf τ (0 : Candidate n) < rankOf τ (reflLastCandidate n)) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      pairPositionCorrectExp n
        (rankOf τ (0 : Candidate n))
        (rankOf τ (reflLastCandidate n)) +
        (reflMiddleInversions n τ).card := by
  rw [kendallTau_refl_eq_endpoint_add_middle]
  rw [reflEndpointInversions_card_of_correct n τ hcorrect]

theorem kendallTau_refl_eq_wrong_endpointExp_add_middle
    (n : ℕ) (τ : Ranking n)
    (hwrong :
      rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n)) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      pairPositionWrongExp n
        (rankOf τ (0 : Candidate n))
        (rankOf τ (reflLastCandidate n)) +
        (reflMiddleInversions n τ).card := by
  rw [kendallTau_refl_eq_endpoint_add_middle]
  rw [reflEndpointInversions_card_of_wrong n τ hwrong]

theorem reflPairCorrectWeight_zero_last_eq_endpointPosition_sum
    (n : ℕ) (q : ℝ) :
    reflPairCorrectWeight n q (0 : Candidate n) (reflLastCandidate n) =
      ∑ p : Candidate n × Candidate n,
        if p.1 < p.2 then
          q ^ pairPositionCorrectExp n p.1 p.2 *
            reflEndpointPositionMiddleWeight n q p.1 p.2
        else
          0 := by
  classical
  have hzero_last : (0 : Candidate n) < reflLastCandidate n := by
    change (0 : ℕ) < n + 1
    omega
  unfold reflPairCorrectWeight
  calc
    ∑ τ : Ranking n,
        (if (0 : Candidate n) < reflLastCandidate n ∧
            rankOf τ (0 : Candidate n) < rankOf τ (reflLastCandidate n) then
          q ^ kendallTau (Equiv.refl (Candidate n)) τ
        else
          0)
        =
      ∑ τ : Ranking n,
        if hpos :
            rankOf τ (0 : Candidate n) < rankOf τ (reflLastCandidate n) then
          q ^ (pairPositionCorrectExp n
              (rankOf τ (0 : Candidate n))
              (rankOf τ (reflLastCandidate n)) +
            (reflMiddleInversions n τ).card)
        else
          0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          by_cases hpos :
              rankOf τ (0 : Candidate n) < rankOf τ (reflLastCandidate n)
          · simp [hzero_last, hpos,
              kendallTau_refl_eq_correct_endpointExp_add_middle n τ hpos]
          · simp [hzero_last, hpos]
    _ =
      ∑ τ : Ranking n, ∑ p : Candidate n × Candidate n,
        if p = (rankOf τ (0 : Candidate n),
            rankOf τ (reflLastCandidate n)) then
          if p.1 < p.2 then
            q ^ (pairPositionCorrectExp n p.1 p.2 +
              (reflMiddleInversions n τ).card)
          else
            0
        else
          0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [Finset.sum_ite_eq']
          simp
    _ =
      ∑ p : Candidate n × Candidate n,
        if p.1 < p.2 then
          q ^ pairPositionCorrectExp n p.1 p.2 *
            reflEndpointPositionMiddleWeight n q p.1 p.2
        else
          0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hpos : p.1 < p.2
          · have hcond :
                ∀ τ : Ranking n,
                  (p = (rankOf τ (0 : Candidate n),
                      rankOf τ (reflLastCandidate n))) ↔
                    rankOf τ (0 : Candidate n) = p.1 ∧
                      rankOf τ (reflLastCandidate n) = p.2 := by
              intro τ
              constructor
              · intro hp
                constructor <;> simp [hp]
              · intro h
                ext <;> simp [h.1, h.2]
            simp_rw [hcond]
            rw [← Finset.sum_filter]
            simp [hpos, reflEndpointPositionMiddleWeight,
              reflEndpointPositionFiber, pow_add, Finset.mul_sum]
          · simp [hpos]

theorem reflPairWrongWeight_zero_last_eq_endpointPosition_sum
    (n : ℕ) (q : ℝ) :
    reflPairWrongWeight n q (0 : Candidate n) (reflLastCandidate n) =
      ∑ p : Candidate n × Candidate n,
        if p.2 < p.1 then
          q ^ pairPositionWrongExp n p.1 p.2 *
            reflEndpointPositionMiddleWeight n q p.1 p.2
        else
          0 := by
  classical
  have hzero_last : (0 : Candidate n) < reflLastCandidate n := by
    change (0 : ℕ) < n + 1
    omega
  unfold reflPairWrongWeight
  calc
    ∑ τ : Ranking n,
        (if (0 : Candidate n) < reflLastCandidate n ∧
            rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n) then
          q ^ kendallTau (Equiv.refl (Candidate n)) τ
        else
          0)
        =
      ∑ τ : Ranking n,
        if hpos :
            rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n) then
          q ^ (pairPositionWrongExp n
              (rankOf τ (0 : Candidate n))
              (rankOf τ (reflLastCandidate n)) +
            (reflMiddleInversions n τ).card)
        else
          0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          by_cases hpos :
              rankOf τ (reflLastCandidate n) < rankOf τ (0 : Candidate n)
          · simp [hzero_last, hpos,
              kendallTau_refl_eq_wrong_endpointExp_add_middle n τ hpos]
          · simp [hzero_last, hpos]
    _ =
      ∑ τ : Ranking n, ∑ p : Candidate n × Candidate n,
        if p = (rankOf τ (0 : Candidate n),
            rankOf τ (reflLastCandidate n)) then
          if p.2 < p.1 then
            q ^ (pairPositionWrongExp n p.1 p.2 +
              (reflMiddleInversions n τ).card)
          else
            0
        else
          0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [Finset.sum_ite_eq']
          simp
    _ =
      ∑ p : Candidate n × Candidate n,
        if p.2 < p.1 then
          q ^ pairPositionWrongExp n p.1 p.2 *
            reflEndpointPositionMiddleWeight n q p.1 p.2
        else
          0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hpos : p.2 < p.1
          · have hcond :
                ∀ τ : Ranking n,
                  (p = (rankOf τ (0 : Candidate n),
                      rankOf τ (reflLastCandidate n))) ↔
                    rankOf τ (0 : Candidate n) = p.1 ∧
                      rankOf τ (reflLastCandidate n) = p.2 := by
              intro τ
              constructor
              · intro hp
                constructor <;> simp [hp]
              · intro h
                ext <;> simp [h.1, h.2]
            simp_rw [hcond]
            rw [← Finset.sum_filter]
            simp [hpos, reflEndpointPositionMiddleWeight,
              reflEndpointPositionFiber, pow_add, Finset.mul_sum]
          · simp [hpos]

/--
Cancellation target for the endpoint case of Appendix F.1 Lemma 8.

After fixing the endpoint positions, the remaining middle-candidate inversion
generating function should not depend on those endpoint positions.  The paper
uses exactly this cancellation to factor out a common positive scale.
-/
structure ReflEndpointMiddleCancellation (n : ℕ) (q : ℝ) where
  scale : ℝ
  scale_pos : 0 < scale
  middle_eq_of_ne :
    ∀ betterPos worsePos : Candidate n, betterPos ≠ worsePos →
      reflEndpointPositionMiddleWeight n q betterPos worsePos = scale

noncomputable def reflEndpointMiddleCancellation
    (n : ℕ) {q : ℝ} (hq : 0 < q) :
    ReflEndpointMiddleCancellation n q where
  scale := finMallowsPartition n q
  scale_pos := finMallowsPartition_pos n hq
  middle_eq_of_ne := by
    intro betterPos worsePos hne
    exact reflEndpointPositionMiddleWeight_eq_finMallowsPartition_of_ne
      n q hne

theorem reflPairCorrectWeight_zero_last_eq_reduced_of_middleCancellation
    (n : ℕ) (q : ℝ) (cancel : ReflEndpointMiddleCancellation n q) :
    reflPairCorrectWeight n q (0 : Candidate n) (reflLastCandidate n) =
      cancel.scale * pairPositionCorrectWeight n q := by
  rw [reflPairCorrectWeight_zero_last_eq_endpointPosition_sum]
  unfold pairPositionCorrectWeight pairPositionCorrectTerm
  calc
    (∑ p : Candidate n × Candidate n,
        if p.1 < p.2 then
          q ^ pairPositionCorrectExp n p.1 p.2 *
            reflEndpointPositionMiddleWeight n q p.1 p.2
        else
          0)
        =
      ∑ p : Candidate n × Candidate n,
        if p.1 < p.2 then
          cancel.scale * q ^ pairPositionCorrectExp n p.1 p.2
        else
          0 := by
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hpos : p.1 < p.2
          · simp [hpos, cancel.middle_eq_of_ne p.1 p.2 (ne_of_lt hpos),
              mul_comm]
          · simp [hpos]
    _ =
      cancel.scale *
        ∑ p : Candidate n × Candidate n,
          if p.1 < p.2 then
            q ^ pairPositionCorrectExp n p.1 p.2
          else
            0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hpos : p.1 < p.2 <;> simp [hpos]

theorem reflPairWrongWeight_zero_last_eq_reduced_of_middleCancellation
    (n : ℕ) (q : ℝ) (cancel : ReflEndpointMiddleCancellation n q) :
    reflPairWrongWeight n q (0 : Candidate n) (reflLastCandidate n) =
      cancel.scale * pairPositionWrongWeight n q := by
  rw [reflPairWrongWeight_zero_last_eq_endpointPosition_sum]
  unfold pairPositionWrongWeight pairPositionWrongTerm
  calc
    (∑ p : Candidate n × Candidate n,
        if p.2 < p.1 then
          q ^ pairPositionWrongExp n p.1 p.2 *
            reflEndpointPositionMiddleWeight n q p.1 p.2
        else
          0)
        =
      ∑ p : Candidate n × Candidate n,
        if p.2 < p.1 then
          cancel.scale * q ^ pairPositionWrongExp n p.1 p.2
        else
          0 := by
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hpos : p.2 < p.1
          · simp [hpos, cancel.middle_eq_of_ne p.1 p.2 (Ne.symm (ne_of_lt hpos)),
              mul_comm]
          · simp [hpos]
    _ =
      cancel.scale *
        ∑ p : Candidate n × Candidate n,
          if p.2 < p.1 then
            q ^ pairPositionWrongExp n p.1 p.2
          else
            0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hpos : p.2 < p.1 <;> simp [hpos]

/--
Identity-center version of `PairPositionReduction`.

This isolates the remaining cancellation step in Appendix F.1 after relabeling
the center to the identity ranking: for a center-rank pair `r < s`, both
identity-center actual pair weights reduce to the same positive scale times the
endpoint-position weights on the interval.
-/
structure ReflPairPositionReduction
    (n : ℕ) (q : ℝ) (r s : Candidate n) (m : ℕ) where
  scale : ℝ
  scale_pos : 0 < scale
  correct_eq :
    reflPairCorrectWeight n q r s =
      scale * pairPositionCorrectWeight m q
  wrong_eq :
    reflPairWrongWeight n q r s =
      scale * pairPositionWrongWeight m q

/-- The endpoint middle-cancellation statement discharges the endpoint case of
the identity-center pair-position reduction. -/
def reflPairPositionReduction_zero_last_of_middleCancellation
    (n : ℕ) (q : ℝ) (cancel : ReflEndpointMiddleCancellation n q) :
    ReflPairPositionReduction n q
      (0 : Candidate n) (reflLastCandidate n) n where
  scale := cancel.scale
  scale_pos := cancel.scale_pos
  correct_eq :=
    reflPairCorrectWeight_zero_last_eq_reduced_of_middleCancellation n q cancel
  wrong_eq :=   reflPairWrongWeight_zero_last_eq_reduced_of_middleCancellation n q cancel

noncomputable def reflPairPositionReduction_zero_last
    (n : ℕ) {q : ℝ} (hq : 0 < q) :
    ReflPairPositionReduction n q
      (0 : Candidate n) (reflLastCandidate n) n :=
  reflPairPositionReduction_zero_last_of_middleCancellation n q
    (reflEndpointMiddleCancellation n hq)

noncomputable def reflPairPositionReduction_succ_succ
    (n m : ℕ) {q : ℝ} (hq : 0 < q) (r s : Candidate n)
    (red : ReflPairPositionReduction n q r s m) :
    ReflPairPositionReduction (n + 1) q r.succ s.succ m where
  scale := candidateRankPowerSum (n + 1) q * red.scale
  scale_pos :=
    mul_pos (candidateRankPowerSum_pos (n + 1) hq) red.scale_pos
  correct_eq := by
    rw [reflPairCorrectWeight_succ_succ, red.correct_eq]
    ring
  wrong_eq := by
    rw [reflPairWrongWeight_succ_succ, red.wrong_eq]
    ring

noncomputable def reflPairPositionReduction_castSucc_castSucc
    (n m : ℕ) {q : ℝ} (hq : 0 < q) (r s : Candidate n)
    (red : ReflPairPositionReduction n q r s m) :
    ReflPairPositionReduction (n + 1) q r.castSucc s.castSucc m where
  scale := candidateRankReversePowerSum (n + 1) q * red.scale
  scale_pos :=
    mul_pos (candidateRankReversePowerSum_pos (n + 1) hq) red.scale_pos
  correct_eq := by
    rw [reflPairCorrectWeight_castSucc_castSucc, red.correct_eq]
    ring
  wrong_eq := by
    rw [reflPairWrongWeight_castSucc_castSucc, red.wrong_eq]
    ring

noncomputable def reflPairPositionReduction_of_lt
    (n : ℕ) {q : ℝ} (hq : 0 < q) :
    ∀ (r s : Candidate n), r < s →
      ReflPairPositionReduction n q r s ((s : ℕ) - (r : ℕ) - 1) := by
  induction n with
  | zero =>
      intro r s hrs
      have hr : r = (0 : Candidate 0) := by
        fin_cases r <;> fin_cases s <;> simp at hrs ⊢
      have hs : s = reflLastCandidate 0 := by
        fin_cases r <;> fin_cases s <;> simp [reflLastCandidate] at hrs ⊢
      subst r
      subst s
      simpa [reflLastCandidate] using reflPairPositionReduction_zero_last 0 hq
  | succ n ih =>
      intro r s hrs
      by_cases hr0 : r = (0 : Candidate (n + 1))
      · by_cases hslast : s = reflLastCandidate (n + 1)
        · subst r
          subst s
          simpa [reflLastCandidate] using
            reflPairPositionReduction_zero_last (n + 1) hq
        · subst r
          let s' : Candidate n :=
            s.castPred (by simpa [reflLastCandidate] using hslast)
          have hs_cast : s'.castSucc = s := by
            dsimp [s']
            exact Fin.castSucc_castPred s
              (by simpa [reflLastCandidate] using hslast)
          have hrs' : (0 : Candidate n) < s' := by
            change (0 : ℕ) < (s' : ℕ)
            have hspos : 0 < (s : ℕ) := by
              have hlt : (0 : Candidate (n + 1)) < s := hrs
              exact hlt
            dsimp [s']
            simpa using hspos
          let m : ℕ := (s' : ℕ) - ((0 : Candidate n) : ℕ) - 1
          have redSmall :
              ReflPairPositionReduction n q (0 : Candidate n) s' m := by
            simpa [m] using ih (0 : Candidate n) s' hrs'
          have redFull :=
            reflPairPositionReduction_castSucc_castSucc n m hq
              (0 : Candidate n) s' redSmall
          have hm :
              m = (s : ℕ) - ((0 : Candidate (n + 1)) : ℕ) - 1 := by
            rfl
          simpa [hs_cast, hm] using redFull
      · have hs0 : s ≠ (0 : Candidate (n + 1)) := by
          intro hs
          subst s
          exact not_lt_bot hrs
        let r' : Candidate n := r.pred hr0
        let s' : Candidate n := s.pred hs0
        have hr_succ : r'.succ = r := by
          dsimp [r']
          exact Fin.succ_pred r hr0
        have hs_succ : s'.succ = s := by
          dsimp [s']
          exact Fin.succ_pred s hs0
        have hrs' : r' < s' := by
          change (r' : ℕ) < (s' : ℕ)
          have hlt : (r : ℕ) < (s : ℕ) := hrs
          have hrpos : 0 < (r : ℕ) := by
            by_contra hle
            have hzero : (r : ℕ) = 0 := by omega
            exact hr0 (Fin.ext hzero)
          have hspos : 0 < (s : ℕ) := lt_trans hrpos hlt
          dsimp [r', s']
          simp
          omega
        let m : ℕ := (s' : ℕ) - (r' : ℕ) - 1
        have redSmall : ReflPairPositionReduction n q r' s' m := by
          simpa [m] using ih r' s' hrs'
        have redFull :=
          reflPairPositionReduction_succ_succ n m hq r' s' redSmall
        have hm :
            m = (s : ℕ) - (r : ℕ) - 1 := by
          have hlt : (r : ℕ) < (s : ℕ) := hrs
          have hrpos : 0 < (r : ℕ) := by
            by_contra hle
            have hzero : (r : ℕ) = 0 := by omega
            exact hr0 (Fin.ext hzero)
          have hspos : 0 < (s : ℕ) := lt_trans hrpos hlt
          have hrpred : (r : ℕ) - 1 + 1 = (r : ℕ) :=
            Nat.sub_add_cancel (Nat.succ_le_of_lt hrpos)
          have hspred : (s : ℕ) - 1 + 1 = (s : ℕ) :=
            Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)
          dsimp [m, r', s']
          omega
        simpa [hr_succ, hs_succ, hm] using redFull

theorem reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt
    (n : ℕ) (q : ℝ) {r s : Candidate n} (hrs : r < s) :
    reflFirstSecondWeight n q r s =
      q ^ ((r : ℕ) + (s : ℕ) - 1) * reflFirstSecondWeight n q 0 1 := by
  classical
  let E₁ : Ranking n := Fin.cycleRange r
  let E₂ : Ranking n := Fin.cycleIcc (1 : Candidate n) s
  let E : Ranking n := E₁.trans E₂
  have hs_ne_zero : s ≠ 0 := by
    intro hs0
    rw [hs0] at hrs
    exact not_lt_bot hrs
  have hs1 : (1 : Candidate n) ≤ s := one_le_of_ne_zero hs_ne_zero
  have hE₁r : E₁ r = 0 := by
    simp [E₁, Fin.cycleRange_self]
  have hE₁s : E₁ s = s := by
    simpa [E₁] using Fin.cycleRange_of_gt hrs
  have hE₂0 : E₂ 0 = 0 := by
    have h01 : (0 : Candidate n) < 1 := by
      change (0 : ℕ) < 1
      omega
    simpa [E₂] using
      (Fin.cycleIcc_of_lt (i := (1 : Candidate n)) (j := s) h01)
  have hE₂s : E₂ s = 1 := by
    simp [E₂, Fin.cycleIcc_of_last hs1]
  unfold reflFirstSecondWeight
  calc
    ∑ τ ∈ reflFirstSecondChoiceFiber n r s,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ
        = ∑ σ ∈ reflFirstSecondChoiceFiber n 0 1,
            q ^ ((r : ℕ) + (s : ℕ) - 1) *
              q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          refine Finset.sum_bij
            (i := fun τ _ => τ.trans E) ?hi ?hinj ?hsurj ?hweight
          · intro τ hτ
            have htop := (Finset.mem_filter.mp hτ).2
            have hfirst : firstChoice τ = r := htop.1.symm
            have hsecond : secondChoice τ = s := htop.2.symm
            unfold reflFirstSecondChoiceFiber
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rw [firstChoice_trans, hfirst]
              simp [E, E₁, E₂, hE₁r, hE₂0]
            · rw [secondChoice_trans, hsecond]
              simp [E, E₁, E₂, hE₁s, hE₂s]
          · intro τ₁ _ τ₂ _ h
            apply Equiv.ext
            intro x
            exact E.injective (Equiv.ext_iff.mp h x)
          · intro σ hσ
            refine ⟨σ.trans E.symm, ?_, ?_⟩
            · have htop := (Finset.mem_filter.mp hσ).2
              have hfirst : firstChoice σ = 0 := htop.1.symm
              have hsecond : secondChoice σ = 1 := htop.2.symm
              have hEr : E r = 0 := by simp [E, hE₁r, hE₂0]
              have hEs : E s = 1 := by simp [E, hE₁s, hE₂s]
              unfold reflFirstSecondChoiceFiber
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rw [firstChoice_trans, hfirst]
                exact (Equiv.apply_eq_iff_eq_symm_apply E).mp hEr
              · rw [secondChoice_trans, hsecond]
                exact (Equiv.apply_eq_iff_eq_symm_apply E).mp hEs
            · ext x
              simp [E]
          · intro τ hτ
            have htop := (Finset.mem_filter.mp hτ).2
            have hfirst : firstChoice τ = r := htop.1.symm
            have hsecond : secondChoice τ = s := htop.2.symm
            have hfirst_apply : τ 0 = r := by
              simpa [firstChoice] using hfirst
            have hsecond_apply : τ 1 = s := by
              simpa [secondChoice] using hsecond
            have hkend₁ :
                kendallTau (Equiv.refl (Candidate n)) τ =
                  (r : ℕ) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E₁) := by
              simpa [E₁, firstChoice, hfirst_apply] using
                kendallTau_eq_firstChoice_add_cycleRange τ
            have hτ₁_first : firstChoice (τ.trans E₁) = 0 := by
              rw [firstChoice_trans, hfirst]
              exact hE₁r
            have hτ₁_second : secondChoice (τ.trans E₁) = s := by
              rw [secondChoice_trans, hsecond]
              exact hE₁s
            have hτ₁_second_apply : (τ.trans E₁) 1 = s := by
              simpa [secondChoice] using hτ₁_second
            have hassoc : (τ.trans E₁).trans E₂ = τ.trans E := rfl
            have hkend₂ :
                kendallTau (Equiv.refl (Candidate n)) (τ.trans E₁) =
                  ((s : ℕ) - 1) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E) := by
              simpa [E₂, secondChoice, hτ₁_second_apply, hassoc] using
                kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one
                  (τ.trans E₁) hτ₁_first
            have hnat :
                (r : ℕ) +
                    (((s : ℕ) - 1) +
                      kendallTau (Equiv.refl (Candidate n)) (τ.trans E)) =
                  ((r : ℕ) + (s : ℕ) - 1) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E) := by
              have hrs_nat : (r : ℕ) < (s : ℕ) := hrs
              omega
            rw [hkend₁, hkend₂, hnat, pow_add]
    _ = q ^ ((r : ℕ) + (s : ℕ) - 1) *
        ∑ σ ∈ reflFirstSecondChoiceFiber n 0 1,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          rw [Finset.mul_sum]

theorem reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt
    (n : ℕ) (q : ℝ) {r s : Candidate n} (hrs : r < s) :
    reflFirstSecondWeight n q s r =
      q ^ ((r : ℕ) + (s : ℕ)) * reflFirstSecondWeight n q 0 1 := by
  classical
  let t : Candidate n := r + 1
  let E₁ : Ranking n := Fin.cycleRange s
  let E₂ : Ranking n := Fin.cycleIcc (1 : Candidate n) t
  let E : Ranking n := E₁.trans E₂
  have ht_val : (t : ℕ) = (r : ℕ) + 1 := by
    simpa [t] using candidate_val_add_one_of_lt hrs
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    have hval : (t : ℕ) = 0 := by
      simpa using congrArg Fin.val ht0
    rw [ht_val] at hval
    omega
  have ht1 : (1 : Candidate n) ≤ t := one_le_of_ne_zero ht_ne_zero
  have hE₁s : E₁ s = 0 := by
    simp [E₁, Fin.cycleRange_self]
  have hE₁r : E₁ r = t := by
    simpa [E₁, t] using Fin.cycleRange_of_lt hrs
  have hE₂0 : E₂ 0 = 0 := by
    have h01 : (0 : Candidate n) < 1 := by
      change (0 : ℕ) < 1
      omega
    simpa [E₂] using
      (Fin.cycleIcc_of_lt (i := (1 : Candidate n)) (j := t) h01)
  have hE₂t : E₂ t = 1 := by
    simp [E₂, Fin.cycleIcc_of_last ht1]
  unfold reflFirstSecondWeight
  calc
    ∑ τ ∈ reflFirstSecondChoiceFiber n s r,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ
        = ∑ σ ∈ reflFirstSecondChoiceFiber n 0 1,
            q ^ ((r : ℕ) + (s : ℕ)) *
              q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          refine Finset.sum_bij
            (i := fun τ _ => τ.trans E) ?hi ?hinj ?hsurj ?hweight
          · intro τ hτ
            have htop := (Finset.mem_filter.mp hτ).2
            have hfirst : firstChoice τ = s := htop.1.symm
            have hsecond : secondChoice τ = r := htop.2.symm
            unfold reflFirstSecondChoiceFiber
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rw [firstChoice_trans, hfirst]
              simp [E, E₁, E₂, hE₁s, hE₂0]
            · rw [secondChoice_trans, hsecond]
              simp [E, E₁, E₂, hE₁r, hE₂t]
          · intro τ₁ _ τ₂ _ h
            apply Equiv.ext
            intro x
            exact E.injective (Equiv.ext_iff.mp h x)
          · intro σ hσ
            refine ⟨σ.trans E.symm, ?_, ?_⟩
            · have htop := (Finset.mem_filter.mp hσ).2
              have hfirst : firstChoice σ = 0 := htop.1.symm
              have hsecond : secondChoice σ = 1 := htop.2.symm
              have hEs : E s = 0 := by simp [E, hE₁s, hE₂0]
              have hEr : E r = 1 := by simp [E, hE₁r, hE₂t]
              unfold reflFirstSecondChoiceFiber
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rw [firstChoice_trans, hfirst]
                exact (Equiv.apply_eq_iff_eq_symm_apply E).mp hEs
              · rw [secondChoice_trans, hsecond]
                exact (Equiv.apply_eq_iff_eq_symm_apply E).mp hEr
            · ext x
              simp [E]
          · intro τ hτ
            have htop := (Finset.mem_filter.mp hτ).2
            have hfirst : firstChoice τ = s := htop.1.symm
            have hsecond : secondChoice τ = r := htop.2.symm
            have hfirst_apply : τ 0 = s := by
              simpa [firstChoice] using hfirst
            have hsecond_apply : τ 1 = r := by
              simpa [secondChoice] using hsecond
            have hkend₁ :
                kendallTau (Equiv.refl (Candidate n)) τ =
                  (s : ℕ) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E₁) := by
              simpa [E₁, firstChoice, hfirst_apply] using
                kendallTau_eq_firstChoice_add_cycleRange τ
            have hτ₁_first : firstChoice (τ.trans E₁) = 0 := by
              rw [firstChoice_trans, hfirst]
              exact hE₁s
            have hτ₁_second : secondChoice (τ.trans E₁) = t := by
              rw [secondChoice_trans, hsecond]
              exact hE₁r
            have hτ₁_second_apply : (τ.trans E₁) 1 = t := by
              simpa [secondChoice] using hτ₁_second
            have hassoc : (τ.trans E₁).trans E₂ = τ.trans E := rfl
            have hkend₂ :
                kendallTau (Equiv.refl (Candidate n)) (τ.trans E₁) =
                  ((t : ℕ) - 1) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E) := by
              simpa [E₂, secondChoice, hτ₁_second_apply, hassoc] using
                kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one
                  (τ.trans E₁) hτ₁_first
            have hnat :
                (s : ℕ) +
                    (((t : ℕ) - 1) +
                      kendallTau (Equiv.refl (Candidate n)) (τ.trans E)) =
                  ((r : ℕ) + (s : ℕ)) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E) := by
              omega
            rw [hkend₁, hkend₂, hnat, pow_add]
    _ = q ^ ((r : ℕ) + (s : ℕ)) *
        ∑ σ ∈ reflFirstSecondChoiceFiber n 0 1,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          rw [Finset.mul_sum]

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

theorem firstWeight_eq_reflFirstWeight (c : Candidate n) :
    M.firstWeight c =
      reflFirstWeight n M.q (rankOf M.center c) := by
  classical
  unfold firstWeight reflFirstWeight reflFirstChoiceFiber mallowsWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun π : Ranking n => c = firstChoice π))
    (t := Finset.univ.filter
      (fun τ : Ranking n => rankOf M.center c = firstChoice τ))
    (i := fun π _ => π.trans M.center.symm) ?hi ?hinj ?hsurj ?hweight
  · intro π hπ
    have hc : c = firstChoice π := (Finset.mem_filter.mp hπ).2
    simp [rankOf, firstChoice, hc]
  · intro π₁ _ π₂ _ h
    apply Equiv.ext
    intro x
    exact M.center.symm.injective (Equiv.ext_iff.mp h x)
  · intro τ hτ
    refine ⟨τ.trans M.center, ?_, ?_⟩
    · have hfirst :
          rankOf M.center c = firstChoice τ := (Finset.mem_filter.mp hτ).2
      have hc : c = M.center (firstChoice τ) := by
        rw [← hfirst]
        simp [rankOf]
      simp [firstChoice, hc]
    · ext x
      simp
  · intro π hπ
    have hkend :
        kendallTau M.center π =
          kendallTau (Equiv.refl (Candidate n)) (π.trans M.center.symm) := by
      have hπ : (π.trans M.center.symm).trans M.center = π := by
        ext x
        simp
      simpa [hπ] using
        kendallTau_center_trans M.center (π.trans M.center.symm)
    rw [hkend]

theorem firstWeight_eq_rank_mul_centerFirst (c : Candidate n) :
    M.firstWeight c =
      M.q ^ (rankOf M.center c : ℕ) * M.firstWeight M.centerFirst := by
  rw [M.firstWeight_eq_reflFirstWeight c]
  rw [reflFirstWeight_eq_rank_mul_zero]
  congr 1
  rw [M.firstWeight_eq_reflFirstWeight M.centerFirst]
  simp [centerFirst, firstChoice, rankOf]

theorem partition_eq_rankPowerSum_mul_centerFirstWeight :
    M.partition =
      candidateRankPowerSum n M.q * M.firstWeight M.centerFirst := by
  rw [← M.sum_firstWeight_eq_partition]
  calc
    ∑ c : Candidate n, M.firstWeight c
        = ∑ c : Candidate n,
            M.q ^ (rankOf M.center c : ℕ) * M.firstWeight M.centerFirst := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstWeight_eq_rank_mul_centerFirst c]
    _ = ∑ r : Candidate n,
          M.q ^ (r : ℕ) * M.firstWeight M.centerFirst := by
          simpa [rankOf] using
            (Equiv.sum_comp M.center.symm
              (fun r : Candidate n =>
                M.q ^ (r : ℕ) * M.firstWeight M.centerFirst))
    _ = candidateRankPowerSum n M.q * M.firstWeight M.centerFirst := by
          unfold candidateRankPowerSum
          rw [Finset.sum_mul]

theorem firstSecondWeight_eq_reflFirstSecondWeight
    (c d : Candidate n) :
    M.firstSecondWeight c d =
      reflFirstSecondWeight n M.q (rankOf M.center c) (rankOf M.center d) := by
  classical
  unfold firstSecondWeight reflFirstSecondWeight reflFirstSecondChoiceFiber mallowsWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (s := Finset.univ.filter
      (fun π : Ranking n => c = firstChoice π ∧ d = secondChoice π))
    (t := Finset.univ.filter
      (fun τ : Ranking n =>
        rankOf M.center c = firstChoice τ ∧
          rankOf M.center d = secondChoice τ))
    (i := fun π _ => π.trans M.center.symm) ?hi ?hinj ?hsurj ?hweight
  · intro π hπ
    have htop := (Finset.mem_filter.mp hπ).2
    simp [rankOf, firstChoice, secondChoice, htop.1, htop.2]
  · intro π₁ _ π₂ _ h
    apply Equiv.ext
    intro x
    exact M.center.symm.injective (Equiv.ext_iff.mp h x)
  · intro τ hτ
    refine ⟨τ.trans M.center, ?_, ?_⟩
    · have htop := (Finset.mem_filter.mp hτ).2
      have hc : c = M.center (firstChoice τ) := by
        rw [← htop.1]
        simp [rankOf]
      have hd : d = M.center (secondChoice τ) := by
        rw [← htop.2]
        simp [rankOf]
      simp [firstChoice, secondChoice, hc, hd]
    · ext x
      simp
  · intro π hπ
    have hkend :
        kendallTau M.center π =
        kendallTau (Equiv.refl (Candidate n)) (π.trans M.center.symm) := by
      have hπ : (π.trans M.center.symm).trans M.center = π := by
        ext x
        simp
      simpa [hπ] using
        kendallTau_center_trans M.center (π.trans M.center.symm)
    rw [hkend]

/-- Relabel an arbitrary-center pair-correct Mallows weight to the identity
center and the pair's center ranks. -/
theorem pairCorrectWeight_eq_reflPairCorrectWeight
    (c d : Candidate n) :
    M.pairCorrectWeight c d =
      reflPairCorrectWeight n M.q (rankOf M.center c) (rankOf M.center d) := by
  classical
  unfold pairCorrectWeight reflPairCorrectWeight mallowsWeight
  refine Finset.sum_bij
    (i := fun π _ => π.trans M.center.symm) ?hi ?hinj ?hsurj ?hweight
  · intro π hπ
    simp
  · intro π₁ _ π₂ _ h
    apply Equiv.ext
    intro x
    exact M.center.symm.injective (Equiv.ext_iff.mp h x)
  · intro τ hτ
    refine ⟨τ.trans M.center, Finset.mem_univ _, ?_⟩
    ext x
    simp
  · intro π hπ
    have hkend :
        kendallTau M.center π =
          kendallTau (Equiv.refl (Candidate n)) (π.trans M.center.symm) := by
      have hπ : (π.trans M.center.symm).trans M.center = π := by
        ext x
        simp
      simpa [hπ] using
        kendallTau_center_trans M.center (π.trans M.center.symm)
    simp [rankOf, hkend]

/-- Relabel an arbitrary-center pair-wrong Mallows weight to the identity center
and the pair's center ranks. -/
theorem pairWrongWeight_eq_reflPairWrongWeight
    (c d : Candidate n) :
    M.pairWrongWeight c d =
      reflPairWrongWeight n M.q (rankOf M.center c) (rankOf M.center d) := by
  classical
  unfold pairWrongWeight reflPairWrongWeight mallowsWeight
  refine Finset.sum_bij
    (i := fun π _ => π.trans M.center.symm) ?hi ?hinj ?hsurj ?hweight
  · intro π hπ
    simp
  · intro π₁ _ π₂ _ h
    apply Equiv.ext
    intro x
    exact M.center.symm.injective (Equiv.ext_iff.mp h x)
  · intro τ hτ
    refine ⟨τ.trans M.center, Finset.mem_univ _, ?_⟩
    ext x
    simp
  · intro π hπ
    have hkend :
        kendallTau M.center π =
          kendallTau (Equiv.refl (Candidate n)) (π.trans M.center.symm) := by
      have hπ : (π.trans M.center.symm).trans M.center = π := by
        ext x
        simp
      simpa [hπ] using
        kendallTau_center_trans M.center (π.trans M.center.symm)
    simp [rankOf, hkend]

/-- The identity-center interval reduction lifts to an arbitrary Mallows center
by relabeling candidates by their center ranks. -/
def pairPositionReduction_of_reflPairPositionReduction
    {m : ℕ} (c d : Candidate n)
    (red :
      ReflPairPositionReduction n M.q
        (rankOf M.center c) (rankOf M.center d) m) :
    PairPositionReduction M c d m where
  scale := red.scale
  scale_pos := red.scale_pos
  correct_eq := by
    rw [M.pairCorrectWeight_eq_reflPairCorrectWeight c d]
    exact red.correct_eq
  wrong_eq := by
    rw [M.pairWrongWeight_eq_reflPairWrongWeight c d]
    exact red.wrong_eq

noncomputable def pairPositionReduction_of_center_lt
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    PairPositionReduction M c d
      ((rankOf M.center d : ℕ) - (rankOf M.center c : ℕ) - 1) :=
  M.pairPositionReduction_of_reflPairPositionReduction c d
    (reflPairPositionReduction_of_lt n M.q_pos
      (rankOf M.center c) (rankOf M.center d) hcd)

theorem firstSecondWeight_eq_rank_mul_centerFirstSecond_of_lt
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.firstSecondWeight c d =
      M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
        M.firstSecondWeight M.centerFirst M.centerSecond := by
  rw [M.firstSecondWeight_eq_reflFirstSecondWeight c d]
  rw [reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt n M.q hcd]
  congr 1
  rw [M.firstSecondWeight_eq_reflFirstSecondWeight M.centerFirst M.centerSecond]
  simp [centerFirst, centerSecond, firstChoice, secondChoice, rankOf]

theorem firstSecondWeight_swap_eq_q_mul_rank_mul_centerFirstSecond_of_lt
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.firstSecondWeight d c =
      M.q *
        (M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
          M.firstSecondWeight M.centerFirst M.centerSecond) := by
  rw [M.firstSecondWeight_eq_reflFirstSecondWeight d c]
  rw [reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt n M.q hcd]
  rw [M.firstSecondWeight_eq_reflFirstSecondWeight M.centerFirst M.centerSecond]
  simp [centerFirst, centerSecond, firstChoice, secondChoice, rankOf]
  have hsum :
      ((M.center.symm c : Candidate n) : ℕ) +
          ((M.center.symm d : Candidate n) : ℕ) =
        (((M.center.symm c : Candidate n) : ℕ) +
            ((M.center.symm d : Candidate n) : ℕ) - 1) + 1 := by
    have hlt :
        ((M.center.symm c : Candidate n) : ℕ) <
          ((M.center.symm d : Candidate n) : ℕ) := by
      simpa [rankOf] using hcd
    omega
  rw [hsum, pow_succ']
  have hone :
      (((M.center.symm c : Candidate n) : ℕ) +
          ((M.center.symm d : Candidate n) : ℕ) - 1) + 1 - 1 =
        ((M.center.symm c : Candidate n) : ℕ) +
          ((M.center.symm d : Candidate n) : ℕ) - 1 := by
    omega
  rw [hone]
  ring

/--
Closed-form rank factorization for the first and top-two Mallows weights.

For a Mallows law centered at `M.center`, the top-candidate fiber at center rank
`r` has a factor `M.q^r`, and the ordered top-two fiber for center ranks
`r < s` has a factor `M.q^(r+s-1)` while the swapped order has one extra factor
of `M.q`.
-/
structure RankFactorization where
  firstTail : ℝ
  firstSecondTail : ℝ
  firstTail_pos : 0 < firstTail
  firstSecondTail_pos : 0 < firstSecondTail
  partition_eq :
    M.partition = candidateRankPowerSum n M.q * firstTail
  firstWeight_eq :
    ∀ c : Candidate n,
      M.firstWeight c = M.q ^ (rankOf M.center c : ℕ) * firstTail
  firstSecondWeight_eq_of_lt :
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      M.firstSecondWeight c d =
        M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
          firstSecondTail
  firstSecondWeight_swap_eq_of_lt :
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      M.firstSecondWeight d c =
        M.q *
          (M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
            firstSecondTail)

noncomputable def RankFactorization.toShared (fac : M.RankFactorization) :
    (M.toShared).RankFactorization where
  firstTail := fac.firstTail
  firstSecondTail := fac.firstSecondTail
  firstTail_pos := fac.firstTail_pos
  firstSecondTail_pos := fac.firstSecondTail_pos
  partition_eq := by
    simpa [candidateRankPowerSum,
      AppliedModelingLib.SocialChoice.Ranking.candidateRankPowerSum] using
      fac.partition_eq
  firstWeight_eq := by
    intro c
    simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
      fac.firstWeight_eq c
  firstSecondWeight_eq_of_lt := by
    intro c d hcd
    exact fac.firstSecondWeight_eq_of_lt c d
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd)
  firstSecondWeight_swap_eq_of_lt := by
    intro c d hcd
    exact fac.firstSecondWeight_swap_eq_of_lt c d
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd)

noncomputable def rankFactorization : M.RankFactorization where
  firstTail := M.firstWeight M.centerFirst
  firstSecondTail := M.firstSecondWeight M.centerFirst M.centerSecond
  firstTail_pos := lt_of_lt_of_le zero_lt_one M.one_le_centerFirstWeight
  firstSecondTail_pos := lt_of_lt_of_le zero_lt_one M.one_le_centerFirstSecondWeight
  partition_eq := M.partition_eq_rankPowerSum_mul_centerFirstWeight
  firstWeight_eq := fun c => M.firstWeight_eq_rank_mul_centerFirst c
  firstSecondWeight_eq_of_lt := fun c d hcd =>
    M.firstSecondWeight_eq_rank_mul_centerFirstSecond_of_lt hcd
  firstSecondWeight_swap_eq_of_lt := fun c d hcd =>
    M.firstSecondWeight_swap_eq_q_mul_rank_mul_centerFirstSecond_of_lt hcd

/--
Under the rank factorization, the first-choice tail is the top-two tail times
the rank-power partition of the remaining candidates after any fixed candidate
is removed from first position.
-/
theorem firstTail_eq_firstSecondTail_mul_removalPowerSum
    (fac : M.RankFactorization) (c : Candidate n) :
    fac.firstTail =
      fac.firstSecondTail *
        candidateRankRemovalPowerSum n M.q (rankOf M.center c) := by
  simpa [candidateRankRemovalPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankRemovalPowerSum,
    rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    (M.toShared).firstTail_eq_firstSecondTail_mul_removalPowerSum
      (RankFactorization.toShared (M := M) fac) c

/-- Unnormalised first-choice mass of a center-rank prefix. -/
noncomputable def firstWeightPrefix (k : Fin (n + 1)) : ℝ :=
  ∑ c : Candidate n,
    if (rankOf M.center c : ℕ) ≤ k.val then M.firstWeight c else 0

theorem firstWeightPrefix_eq_rankPrefixPowerSum_mul
    (fac : M.RankFactorization) (k : Fin (n + 1)) :
    M.firstWeightPrefix k = candidateRankPrefixPowerSum n M.q k * fac.firstTail := by
  simpa [firstWeightPrefix,
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.firstWeightPrefix,
    candidateRankPrefixPowerSum,
    AppliedModelingLib.SocialChoice.Ranking.candidateRankPrefixPowerSum,
    rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    (M.toShared).firstWeightPrefix_eq_rankPrefixPowerSum_mul
      (RankFactorization.toShared (M := M) fac) k

/-- The ordered-pair summand in the cleared independent-reranking numerator. -/
noncomputable def independentPairTerm
    (value : Candidate n → ℝ) (c d : Candidate n) : ℝ :=
  (M.partition - M.firstWeight c) *
    M.firstSecondWeight c d * (value c - value d)

/--
The antisymmetrized top-two bracket for the unordered pair `{c,d}`.

Appendix E compares the `(c,d)` and `(d,c)` top-two fibers through exactly this
quantity after clearing Mallows denominators.
-/
noncomputable def independentPairBracket (c d : Candidate n) : ℝ :=
  (M.partition - M.firstWeight c) * M.firstSecondWeight c d -
    (M.partition - M.firstWeight d) * M.firstSecondWeight d c

@[simp] theorem independentPairTerm_apply
    (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d =
      (M.partition - M.firstWeight c) *
        M.firstSecondWeight c d * (value c - value d) := rfl

@[simp] theorem independentPairBracket_apply (c d : Candidate n) :
    M.independentPairBracket c d =
      (M.partition - M.firstWeight c) * M.firstSecondWeight c d -
        (M.partition - M.firstWeight d) * M.firstSecondWeight d c := rfl

/-- No ranking has the same candidate as both first and second choice. -/
@[simp] theorem firstSecondWeight_self (c : Candidate n) :
    M.firstSecondWeight c c = 0 := by
  classical
  unfold firstSecondWeight
  apply Finset.sum_eq_zero
  intro π _
  have hnot : ¬(c = firstChoice π ∧ c = secondChoice π) := by
    intro h
    have hfs : firstChoice π = secondChoice π := h.1.symm.trans h.2
    exact firstChoice_ne_secondChoice π hfs
  have hraw : ¬(c = π 0 ∧ c = π 1) := by
    intro h
    apply hnot
    exact ⟨by simpa [firstChoice] using h.1,
      by simpa [secondChoice] using h.2⟩
  simp [firstChoice, secondChoice, hraw]

/--
Pairing the ordered top-two events `(c,d)` and `(d,c)` produces a single
bracket times the value difference.
-/
theorem independentPairTerm_add_swap
    (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d + M.independentPairTerm value d c =
      M.independentPairBracket c d * (value c - value d) := by
  unfold independentPairTerm independentPairBracket
  ring

/--
If a pair is ordered by value and its Mallows pair bracket is nonnegative, then
the paired `(c,d)`/`(d,c)` contribution is nonnegative.
-/
theorem independentPairTerm_add_swap_nonneg
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 ≤ M.independentPairBracket c d)
    (hvalue : value d ≤ value c) :
    0 ≤ M.independentPairTerm value c d + M.independentPairTerm value d c := by
  rw [M.independentPairTerm_add_swap value c d]
  exact mul_nonneg hbracket (sub_nonneg.mpr hvalue)

/--
If a pair is strictly ordered by value and its Mallows pair bracket is positive,
then the paired `(c,d)`/`(d,c)` contribution is positive.
-/
theorem independentPairTerm_add_swap_pos
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 < M.independentPairBracket c d)
    (hvalue : value d < value c) :
    0 < M.independentPairTerm value c d + M.independentPairTerm value d c := by
  rw [M.independentPairTerm_add_swap value c d]
  exact mul_pos hbracket (sub_pos.mpr hvalue)

/--
The closed-form rank factorization implies the nonnegative Appendix-E
independent-reranking bracket for every center-ordered pair.
-/
theorem independentPairBracket_nonneg_of_rankFactorization
    (fac : M.RankFactorization) (hq_le_one : M.q ≤ 1)
    {c d : Candidate n} (hlt : rankOf M.center c < rankOf M.center d) :
    0 ≤ M.independentPairBracket c d := by
  let k : ℕ := (rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1
  have hinner :
      0 ≤ (candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
        M.q * (candidateRankPowerSum n M.q -
          M.q ^ (rankOf M.center d : ℕ)) :=
    candidateRankPowerSum_inner_nonneg
      (le_of_lt M.q_pos) hq_le_one hlt
  have hqk_nonneg : 0 ≤ M.q ^ k := pow_nonneg (le_of_lt M.q_pos) k
  have heq :
      M.independentPairBracket c d =
        fac.firstTail * (M.q ^ k * fac.firstSecondTail) *
          ((candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
            M.q * (candidateRankPowerSum n M.q -
              M.q ^ (rankOf M.center d : ℕ))) := by
    unfold independentPairBracket
    rw [fac.partition_eq, fac.firstWeight_eq c, fac.firstWeight_eq d,
      fac.firstSecondWeight_eq_of_lt c d hlt,
      fac.firstSecondWeight_swap_eq_of_lt c d hlt]
    ring
  rw [heq]
  exact mul_nonneg
    (mul_nonneg (le_of_lt fac.firstTail_pos)
      (mul_nonneg hqk_nonneg (le_of_lt fac.firstSecondTail_pos)))
    hinner

/--
For at least three candidates and `0 < q < 1`, the center top-two pair has a
strictly positive independent-reranking bracket under the rank factorization.
-/
theorem independentPairBracket_centerTopTwo_pos_of_rankFactorization
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1) :
    0 < M.independentPairBracket M.centerFirst M.centerSecond := by
  let c : Candidate n := M.centerFirst
  let d : Candidate n := M.centerSecond
  have hlt : rankOf M.center c < rankOf M.center d := by
    simp [c, d, MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf]
  let k : ℕ := (rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1
  have hk : k = 0 := by
    simp [k, c, d, MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf]
  have hinner :
      0 < (candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
        M.q * (candidateRankPowerSum n M.q -
          M.q ^ (rankOf M.center d : ℕ)) := by
    simpa [c, d, MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf] using
      candidateRankPowerSum_inner_pos_zero_one hn M.q_pos hq_lt_one
  have hqk_pos : 0 < M.q ^ k := pow_pos M.q_pos k
  have heq :
      M.independentPairBracket c d =
        fac.firstTail * (M.q ^ k * fac.firstSecondTail) *
          ((candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
            M.q * (candidateRankPowerSum n M.q -
              M.q ^ (rankOf M.center d : ℕ))) := by
    unfold independentPairBracket
    rw [fac.partition_eq, fac.firstWeight_eq c, fac.firstWeight_eq d,
      fac.firstSecondWeight_eq_of_lt c d hlt,
      fac.firstSecondWeight_swap_eq_of_lt c d hlt]
    ring
  rw [heq]
  exact mul_pos
    (mul_pos fac.firstTail_pos (mul_pos hqk_pos fac.firstSecondTail_pos))
    hinner

theorem centerFirstGapWeight_pos_of_strictlyOrderedCenter
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < M.firstChoiceGapWeight value M.centerFirst := by
  have hmass := M.centerFirstGapMass_pos_of_strictlyOrderedCenter hvalue
  rw [M.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition] at hmass
  exact (div_pos_iff_of_pos_right M.partition_pos).mp hmass

/--
Top-two expansion of the unnormalised first-choice gap numerator.

This is the paper's Appendix-E decomposition step: a ranking whose first two
candidates are `(c,d)` contributes exactly `value c - value d` to the
first-choice gap attached to `c`.
-/
theorem firstChoiceGapWeight_eq_sum_firstSecondWeight
    (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      ∑ d : Candidate n, M.firstSecondWeight c d * (value c - value d) := by
  classical
  unfold firstChoiceGapWeight firstSecondWeight
  calc
    ∑ π : Ranking n,
        (if c = firstChoice π then
          mallowsWeight M.q M.center π * valueGap value π
        else
          0)
        = ∑ π : Ranking n,
            ∑ d : Candidate n,
              (if c = firstChoice π ∧ d = secondChoice π then
                mallowsWeight M.q M.center π * (value c - value d)
              else
                0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases hc : c = firstChoice π
          · have hraw : c = π 0 := by
              simpa [firstChoice] using hc
            have hsum :
                (∑ d : Candidate n,
                  if d = secondChoice π then
                    mallowsWeight M.q M.center π * (value c - value d)
                  else
                    0) =
                  mallowsWeight M.q M.center π *
                    (value c - value (secondChoice π)) := by
              simpa using
                (Finset.sum_ite_eq' Finset.univ (secondChoice π)
                  (fun d : Candidate n =>
                    mallowsWeight M.q M.center π * (value c - value d)))
            calc
              (if c = firstChoice π then
                  mallowsWeight M.q M.center π * valueGap value π
                else
                  0)
                  = mallowsWeight M.q M.center π *
                      (value c - value (secondChoice π)) := by
                    simp [hc, valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
                      firstChoice, secondChoice,
                      AppliedModelingLib.SocialChoice.Ranking.firstChoice,
                      AppliedModelingLib.SocialChoice.Ranking.secondChoice]
              _ = ∑ d : Candidate n,
                    (if c = firstChoice π ∧ d = secondChoice π then
                      mallowsWeight M.q M.center π * (value c - value d)
                    else
                      0) := by
                    rw [← hsum]
                    refine Finset.sum_congr rfl ?_
                    intro d _
                    by_cases hd : d = secondChoice π <;> simp [hc, hd]
          · have hraw : c ≠ π 0 := by
              simpa [firstChoice] using hc
            simp [hraw]
    _ = ∑ d : Candidate n,
          ∑ π : Ranking n,
            (if c = firstChoice π ∧ d = secondChoice π then
              mallowsWeight M.q M.center π * (value c - value d)
            else
              0) := by
          rw [Finset.sum_comm]
    _ = ∑ d : Candidate n,
          (∑ π : Ranking n,
            (if c = firstChoice π ∧ d = secondChoice π then
              mallowsWeight M.q M.center π
            else
              0)) * (value c - value d) := by
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π ∧ d = secondChoice π
          · simp [h]
          · have h' : ¬(c = π 0 ∧ d = π 1) := by
              intro hraw
              apply h
              exact ⟨by simpa [firstChoice] using hraw.1,
                by simpa [secondChoice] using hraw.2⟩
            simp [h']

/--
Rank-factorized form of the conditional first-choice gap.

After conditioning on a first-choice center rank `r`, the remaining top-two
Mallows fiber contributes the rank-only conditional gap used in Appendix E.
-/
theorem firstChoiceGapWeight_eq_rankConditionalGap
    (fac : M.RankFactorization) (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      M.q ^ (rankOf M.center c : ℕ) * fac.firstSecondTail *
        candidateRankConditionalGap n M.q
          (fun r : Candidate n => value (M.center r)) (rankOf M.center c) := by
  classical
  let r : Candidate n := rankOf M.center c
  have hc_center : M.center r = c := by
    simp [r, rankOf]
  rw [M.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
  calc
    (∑ d : Candidate n, M.firstSecondWeight c d * (value c - value d))
        = ∑ s : Candidate n,
            M.firstSecondWeight c (M.center s) *
              (value c - value (M.center s)) := by
          simpa using
            (Equiv.sum_comp M.center
              (fun d : Candidate n =>
                M.firstSecondWeight c d * (value c - value d))).symm
    _ = ∑ s : Candidate n,
          (M.q ^ (r : ℕ) * fac.firstSecondTail) *
            candidateRankConditionalGapTerm M.q
              (fun x : Candidate n => value (M.center x)) r s := by
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hrs : r < s
          · have hlt :
                rankOf M.center c < rankOf M.center (M.center s) := by
              simpa [r, rankOf] using hrs
            have hs_pos : 0 < (s : ℕ) :=
              lt_of_le_of_lt (Nat.zero_le (r : ℕ)) hrs
            have hsplit :
                (r : ℕ) + (s : ℕ) - 1 =
                  (r : ℕ) + ((s : ℕ) - 1) := by
              omega
            rw [fac.firstSecondWeight_eq_of_lt c (M.center s) hlt]
            rw [← hc_center]
            simp [candidateRankConditionalGapTerm, hrs, rankOf]
            rw [hsplit, pow_add]
            ring
          · by_cases hsr : s < r
            · have hlt :
                  rankOf M.center (M.center s) < rankOf M.center c := by
                simpa [r, rankOf] using hsr
              have hnot : ¬r < s := hrs
              have hsucc :
                  ((s : ℕ) + (r : ℕ) - 1) + 1 =
                    (r : ℕ) + (s : ℕ) := by
                have hsr_nat : (s : ℕ) < (r : ℕ) := hsr
                omega
              rw [fac.firstSecondWeight_swap_eq_of_lt (M.center s) c hlt]
              rw [← hc_center]
              simp [candidateRankConditionalGapTerm, hnot, hsr, rankOf]
              rw [← mul_assoc M.q (M.q ^ ((s : ℕ) + (r : ℕ) - 1)) fac.firstSecondTail]
              rw [← pow_succ', hsucc, pow_add]
              ring
            · have hsr_eq : s = r :=
                le_antisymm (le_of_not_gt hrs) (le_of_not_gt hsr)
              subst s
              simp [candidateRankConditionalGapTerm, hc_center]
    _ = M.q ^ (rankOf M.center c : ℕ) * fac.firstSecondTail *
          candidateRankConditionalGap n M.q
            (fun r : Candidate n => value (M.center r)) (rankOf M.center c) := by
          unfold candidateRankConditionalGap
          rw [← Finset.mul_sum]

/--
The denominator-cleared independent-reranking sum can be written as a sum over
ordered top-two candidate pairs.
-/
theorem independent_weight_sum_eq_pair_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d := by
  classical
  calc
    ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c
        = ∑ c : Candidate n,
            (M.partition - M.firstWeight c) *
              (∑ d : Candidate n,
                M.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        (M.partition - M.firstWeight c) *
          (M.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          unfold independentPairTerm
          ring

theorem pair_sum_eq_ordered_swap_sum
    {n : ℕ} (ρ : Ranking n) (t : Candidate n → Candidate n → ℝ)
    (hdiag : ∀ c : Candidate n, t c c = 0) :
    (∑ c : Candidate n, ∑ d : Candidate n, t c d) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        if rankOf ρ c < rankOf ρ d then t c d + t d c else 0 :=
    AppliedModelingLib.FiniteSum.pair_sum_eq_ordered_swap_sum_of_injective_key
      (fun c : Candidate n => rankOf ρ c)
      (by
        intro c d h
        exact ρ.symm.injective h)
      t hdiag

/--
The ordered top-two pair sum can be regrouped over center-ordered unordered
pairs. This is the finite-sum form of the Appendix-E `(c,d)`/`(d,c)` pairing.
-/
theorem independent_pair_sum_eq_ordered_swap_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        if rankOf M.center c < rankOf M.center d then
          M.independentPairTerm value c d + M.independentPairTerm value d c
        else 0 := by
  refine pair_sum_eq_ordered_swap_sum M.center (M.independentPairTerm value) ?_
  intro c
  unfold independentPairTerm
  ring

/--
Appendix-E pair-bracket signs imply positivity of the cleared
independent-reranking numerator.

This reduces the total finite Mallows inequality to the local pairwise bracket
comparisons for center-ordered candidate pairs.
-/
theorem independent_weight_sum_pos_of_pair_brackets
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value)
    (hbracket_nonneg :
      ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
        0 ≤ M.independentPairBracket c d)
    (hbracket_pos :
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        0 < M.independentPairBracket c d) :
    0 < ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c := by
  classical
  rw [M.independent_weight_sum_eq_pair_sum value]
  rw [M.independent_pair_sum_eq_ordered_swap_sum value]
  rcases hbracket_pos with ⟨c₀, d₀, hlt₀, hbracket₀⟩
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun c : Candidate n =>
      ∑ d : Candidate n,
        if rankOf M.center c < rankOf M.center d then
          M.independentPairTerm value c d + M.independentPairTerm value d c
        else 0)
    (a₀ := c₀)
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun d : Candidate n =>
        if rankOf M.center c₀ < rankOf M.center d then
          M.independentPairTerm value c₀ d + M.independentPairTerm value d c₀
        else 0)
      (a₀ := d₀)
    · have hpos := M.independentPairTerm_add_swap_pos
          (value := value) hbracket₀ (hvalue hlt₀)
      simpa [hlt₀, independentPairTerm] using hpos
    · intro d
      by_cases hlt : rankOf M.center c₀ < rankOf M.center d
      · exact if_pos hlt ▸
          M.independentPairTerm_add_swap_nonneg
            (value := value) (hbracket_nonneg c₀ d hlt)
            (le_of_lt (hvalue hlt))
      · simp [hlt]
  · intro c
    apply Finset.sum_nonneg
    intro d _
    by_cases hlt : rankOf M.center c < rankOf M.center d
    · exact if_pos hlt ▸
        M.independentPairTerm_add_swap_nonneg
          (value := value) (hbracket_nonneg c d hlt)
          (le_of_lt (hvalue hlt))
    · simp [hlt]

/--
Closed-form Mallows rank factorization proves the cleared
independent-reranking finite-sum inequality for any strictly center-ordered value
profile, provided there are at least three candidates and `0 < q < 1`.
-/
theorem independent_weight_sum_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1)
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c := by
  refine M.independent_weight_sum_pos_of_pair_brackets hvalue ?nonneg ?pos
  · intro c d hlt
    exact M.independentPairBracket_nonneg_of_rankFactorization
      fac (le_of_lt hq_lt_one) hlt
  · exact ⟨M.centerFirst, M.centerSecond,
      by
        simp [MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf],
      M.independentPairBracket_centerTopTwo_pos_of_rankFactorization
        fac hn hq_lt_one⟩

end MallowsSpec

theorem candidateRankWeightedAverage_strictAnti
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {B : Candidate n → ℝ} (hB : StrictAnti B) :
    0 <
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    q₁ ^ (i : ℕ) * B i * q₂ ^ (j : ℕ) -
      q₂ ^ (i : ℕ) * B i * q₁ ^ (j : ℕ)
  have hdouble :
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankPowerSum
    calc
      (∑ j : Candidate n, q₂ ^ (j : ℕ)) *
            (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
          (∑ j : Candidate n, q₁ ^ (j : ℕ)) *
            (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i)
          =
          (∑ i : Candidate n, ∑ j : Candidate n,
              q₁ ^ (i : ℕ) * B i * q₂ ^ (j : ℕ)) -
            (∑ i : Candidate n, ∑ j : Candidate n,
              q₂ ^ (i : ℕ) * B i * q₁ ^ (j : ℕ)) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro i
      simp [t]
      ring)]
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun i : Candidate n =>
      ∑ j : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) i <
            rankOf (Equiv.refl (Candidate n)) j then
          t i j + t j i
        else 0)
    (a₀ := (0 : Candidate n))
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun j : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) j then
          t (0 : Candidate n) j + t j (0 : Candidate n)
        else 0)
      (a₀ := (1 : Candidate n))
    · have hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) (1 : Candidate n) := by
        change (0 : ℕ) < 1
        omega
      have hweight :
          0 < q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ ((1 : Candidate n) : ℕ) -
            q₁ ^ ((1 : Candidate n) : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ) := by
        have hpow := rankPower_mul_lt_mul_rankPower
          hq₁_pos hq_lt (show (0 : Candidate n) < (1 : Candidate n) by
            change (0 : ℕ) < 1
            omega)
        exact sub_pos.mpr (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow)
      have hgap :
          0 < B (0 : Candidate n) - B (1 : Candidate n) :=
        sub_pos.mpr (hB (show (0 : Candidate n) < (1 : Candidate n) by
          change (0 : ℕ) < 1
          omega))
      have hterm :
          0 < t (0 : Candidate n) (1 : Candidate n) +
              t (1 : Candidate n) (0 : Candidate n) := by
        have heq :
            t (0 : Candidate n) (1 : Candidate n) +
                t (1 : Candidate n) (0 : Candidate n) =
              (q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ ((1 : Candidate n) : ℕ) -
                q₁ ^ ((1 : Candidate n) : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ)) *
                (B (0 : Candidate n) - B (1 : Candidate n)) := by
          simp [t]
          ring
        rw [heq]
        exact mul_pos hweight hgap
      simpa [hlt] using hterm
    · intro j
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j
      · have hnonneg :
            0 ≤ t (0 : Candidate n) j + t j (0 : Candidate n) := by
          have h0j : (0 : Candidate n) < j := by
            simpa [rankOf] using hlt
          have hweight :
              0 ≤ q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ (j : ℕ) -
                q₁ ^ (j : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ) := by
            have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt h0j
            exact sub_nonneg.mpr (le_of_lt (by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hpow))
          have hgap : 0 ≤ B (0 : Candidate n) - B j :=
            le_of_lt (sub_pos.mpr (hB h0j))
          have heq :
              t (0 : Candidate n) j + t j (0 : Candidate n) =
                (q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ (j : ℕ) -
                  q₁ ^ (j : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ)) *
                  (B (0 : Candidate n) - B j) := by
            simp [t]
            ring
          rw [heq]
          exact mul_nonneg hweight hgap
        exact if_pos hlt ▸ hnonneg
      · simp [hlt]
  · intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) i <
        rankOf (Equiv.refl (Candidate n)) j
    · have hij : i < j := by
        simpa [rankOf] using hlt
      have hweight :
          0 ≤ q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) := by
        have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
        exact sub_nonneg.mpr (le_of_lt (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow))
      have hgap : 0 ≤ B i - B j := le_of_lt (sub_pos.mpr (hB hij))
      have heq :
          t i j + t j i =
            (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
              q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ)) * (B i - B j) := by
        simp [t]
        ring
      exact if_pos hlt ▸ by
        rw [heq]
        exact mul_nonneg hweight hgap
    · simp [hlt]

/--
Generic finite weighted-average comparison from pairwise cross-ratio
dominance.  If `wA i * wH j >= wA j * wH i` for every better rank `i < j`,
then every weakly decreasing rank payoff has weakly larger `wA` average after
clearing denominators.
-/
theorem candidateWeightedAverage_cross_nonneg_of_pairwise
    (n : ℕ) {wA wH B : Candidate n → ℝ}
    (hpair :
      ∀ i j : Candidate n, i < j →
        0 ≤ wA i * wH j - wA j * wH i)
    (hB : ∀ i j : Candidate n, i < j → B j ≤ B i) :
    0 ≤
      (∑ j : Candidate n, wH j) *
          (∑ i : Candidate n, wA i * B i) -
        (∑ j : Candidate n, wA j) *
          (∑ i : Candidate n, wH i * B i) :=
    AppliedModelingLib.FiniteSum.weighted_average_cross_nonneg_of_pairwise
      (α := Candidate n) hpair hB

/--
Strict finite weighted-average comparison from pairwise cross-ratio dominance.
This is the strict companion to `candidateWeightedAverage_cross_nonneg_of_pairwise`:
one strictly positive pairwise cross-ratio bracket and a strictly decreasing
rank payoff make the cleared weighted-average comparison strict.
-/
theorem candidateWeightedAverage_cross_pos_of_pairwise
    (n : ℕ) {wA wH B : Candidate n → ℝ}
    (hpair_nonneg :
      ∀ i j : Candidate n, i < j →
        0 ≤ wA i * wH j - wA j * wH i)
    (hpair_pos :
      ∃ i j : Candidate n, i < j ∧
        0 < wA i * wH j - wA j * wH i)
    (hB : StrictAnti B) :
    0 <
      (∑ j : Candidate n, wH j) *
          (∑ i : Candidate n, wA i * B i) -
        (∑ j : Candidate n, wA j) *
          (∑ i : Candidate n, wH i * B i) :=
    AppliedModelingLib.FiniteSum.weighted_average_cross_pos_of_pairwise
      (α := Candidate n) hpair_nonneg hpair_pos hB

theorem candidateRankCollisionWeight_cross_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    (hq₂_lt_one : q₂ < 1) :
    0 <
      candidateRankPowerSum n q₂ * candidateRankPowerSum n (q₁ * q₂) -
        candidateRankPowerSum n q₁ * candidateRankPowerSum n (q₂ * q₂) := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  let B : Candidate n → ℝ := fun i => q₂ ^ (i : ℕ)
  have hB : StrictAnti B := by
    intro i j hij
    exact pow_lt_pow_right_of_lt_one₀ hq₂_pos hq₂_lt_one hij
  have hmain := candidateRankWeightedAverage_strictAnti n hq₁_pos hq_lt hB
  have hleft :
      (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) =
        candidateRankPowerSum n (q₁ * q₂) := by
    unfold candidateRankPowerSum B
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [mul_pow]
  have hright :
      (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) =
        candidateRankPowerSum n (q₂ * q₂) := by
    unfold candidateRankPowerSum B
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [mul_pow]
  simpa [hleft, hright] using hmain

theorem candidateRankSquareWeightedConditionalGap_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (hq_lt_one : q < 1)
    {value : Candidate n → ℝ}
    (hvalue : ∀ i j : Candidate n, i < j → value j < value i) :
    0 < ∑ r : Candidate n,
      (q * q) ^ (r : ℕ) * candidateRankConditionalGap n q value r := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun r s =>
    (q * q) ^ (r : ℕ) * candidateRankConditionalGapTerm q value r s
  have hdouble :
      (∑ r : Candidate n,
        (q * q) ^ (r : ℕ) * candidateRankConditionalGap n q value r) =
        ∑ r : Candidate n, ∑ s : Candidate n, t r s := by
    unfold candidateRankConditionalGap
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.mul_sum]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro r
      simp [t, candidateRankConditionalGapTerm])]
  have hq_sq_pos : 0 < q * q := mul_pos hq_pos hq_pos
  have hq_sq_lt_q : q * q < q := by
    nlinarith [mul_lt_mul_of_pos_left hq_lt_one hq_pos]
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun r : Candidate n =>
      ∑ s : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) r <
            rankOf (Equiv.refl (Candidate n)) s then
          t r s + t s r
        else 0)
    (a₀ := (0 : Candidate n))
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun s : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) s then
          t (0 : Candidate n) s + t s (0 : Candidate n)
        else 0)
      (a₀ := (1 : Candidate n))
    · have hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) (1 : Candidate n) := by
        change (0 : ℕ) < 1
        omega
      have hpair : (0 : Candidate n) < (1 : Candidate n) := by
        change (0 : ℕ) < 1
        omega
      have hcoeff :
          0 < (q * q) ^ ((0 : Candidate n) : ℕ) *
                q ^ (((1 : Candidate n) : ℕ) - 1) -
              (q * q) ^ ((1 : Candidate n) : ℕ) *
                q ^ ((0 : Candidate n) : ℕ) := by
        have hpow₁ := rankPower_mul_lt_mul_rankPower
          hq_sq_pos hq_sq_lt_q hpair
        have hpred :
            q ^ (((1 : Candidate n) : ℕ)) <
              q ^ (((1 : Candidate n) : ℕ) - 1) := by
          have hpred_exp :
              (((1 : Candidate n) : ℕ) - 1) < ((1 : Candidate n) : ℕ) := by
            change (1 : ℕ) - 1 < 1
            omega
          exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one hpred_exp
        have hpow₂ :
            (q * q) ^ ((0 : Candidate n) : ℕ) *
                q ^ (((1 : Candidate n) : ℕ)) <
              (q * q) ^ ((0 : Candidate n) : ℕ) *
                q ^ (((1 : Candidate n) : ℕ) - 1) :=
          mul_lt_mul_of_pos_left hpred
            (pow_pos hq_sq_pos ((0 : Candidate n) : ℕ))
        exact sub_pos.mpr (lt_trans (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow₁) hpow₂)
      have hgap :
          0 < value (0 : Candidate n) - value (1 : Candidate n) :=
        sub_pos.mpr (hvalue (0 : Candidate n) (1 : Candidate n) hpair)
      have hterm :
          0 < t (0 : Candidate n) (1 : Candidate n) +
              t (1 : Candidate n) (0 : Candidate n) := by
        have hnot : ¬(1 : Candidate n) < (0 : Candidate n) := not_lt_of_gt hpair
        have heq :
            t (0 : Candidate n) (1 : Candidate n) +
                t (1 : Candidate n) (0 : Candidate n) =
              ((q * q) ^ ((0 : Candidate n) : ℕ) *
                  q ^ (((1 : Candidate n) : ℕ) - 1) -
                (q * q) ^ ((1 : Candidate n) : ℕ) *
                  q ^ ((0 : Candidate n) : ℕ)) *
                (value (0 : Candidate n) - value (1 : Candidate n)) := by
          simp [t, candidateRankConditionalGapTerm, hpair, hnot]
          ring
        rw [heq]
        exact mul_pos hcoeff hgap
      simpa [hlt] using hterm
    · intro s
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) s
      · have h0s : (0 : Candidate n) < s := by
          simpa [rankOf] using hlt
        have hcoeff :
            0 ≤ (q * q) ^ ((0 : Candidate n) : ℕ) *
                  q ^ ((s : ℕ) - 1) -
                (q * q) ^ (s : ℕ) *
                  q ^ ((0 : Candidate n) : ℕ) := by
          have hpow₁ := rankPower_mul_lt_mul_rankPower
            hq_sq_pos hq_sq_lt_q h0s
          have hpred : q ^ (s : ℕ) < q ^ ((s : ℕ) - 1) := by
            have hs_pos : 0 < (s : ℕ) := by
              simpa using h0s
            have hpred_exp : (s : ℕ) - 1 < (s : ℕ) := by omega
            exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one hpred_exp
          have hpow₂ :
              (q * q) ^ ((0 : Candidate n) : ℕ) * q ^ (s : ℕ) <
                (q * q) ^ ((0 : Candidate n) : ℕ) *
                  q ^ ((s : ℕ) - 1) :=
            mul_lt_mul_of_pos_left hpred
              (pow_pos hq_sq_pos ((0 : Candidate n) : ℕ))
          exact le_of_lt (sub_pos.mpr (lt_trans (by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hpow₁) hpow₂))
        have hgap : 0 ≤ value (0 : Candidate n) - value s :=
          le_of_lt (sub_pos.mpr (hvalue (0 : Candidate n) s h0s))
        have hnot : ¬s < (0 : Candidate n) := not_lt_of_gt h0s
        have heq :
            t (0 : Candidate n) s + t s (0 : Candidate n) =
              ((q * q) ^ ((0 : Candidate n) : ℕ) * q ^ ((s : ℕ) - 1) -
                (q * q) ^ (s : ℕ) * q ^ ((0 : Candidate n) : ℕ)) *
                (value (0 : Candidate n) - value s) := by
          simp [t, candidateRankConditionalGapTerm, h0s, hnot]
          ring
        exact if_pos hlt ▸ by
          rw [heq]
          exact mul_nonneg hcoeff hgap
      · simp [hlt]
  · intro r
    apply Finset.sum_nonneg
    intro s _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) r <
        rankOf (Equiv.refl (Candidate n)) s
    · have hrs : r < s := by
        simpa [rankOf] using hlt
      have hcoeff :
          0 ≤ (q * q) ^ (r : ℕ) * q ^ ((s : ℕ) - 1) -
            (q * q) ^ (s : ℕ) * q ^ (r : ℕ) := by
        have hpow₁ := rankPower_mul_lt_mul_rankPower
          hq_sq_pos hq_sq_lt_q hrs
        have hpred : q ^ (s : ℕ) < q ^ ((s : ℕ) - 1) := by
          have hs_pos : 0 < (s : ℕ) :=
            lt_of_le_of_lt (Nat.zero_le (r : ℕ)) hrs
          have hpred_exp : (s : ℕ) - 1 < (s : ℕ) := by omega
          exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one hpred_exp
        have hpow₂ :
            (q * q) ^ (r : ℕ) * q ^ (s : ℕ) <
              (q * q) ^ (r : ℕ) * q ^ ((s : ℕ) - 1) :=
          mul_lt_mul_of_pos_left hpred (pow_pos hq_sq_pos (r : ℕ))
        exact le_of_lt (sub_pos.mpr (lt_trans (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow₁) hpow₂))
      have hgap : 0 ≤ value r - value s :=
        le_of_lt (sub_pos.mpr (hvalue r s hrs))
      have hnot : ¬s < r := not_lt_of_gt hrs
      have heq :
          t r s + t s r =
            ((q * q) ^ (r : ℕ) * q ^ ((s : ℕ) - 1) -
              (q * q) ^ (s : ℕ) * q ^ (r : ℕ)) *
              (value r - value s) := by
        simp [t, candidateRankConditionalGapTerm, hrs, hnot]
        ring
      exact if_pos hlt ▸ by
        rw [heq]
        exact mul_nonneg hcoeff hgap
    · simp [hlt]

theorem candidateRankCrossConditionalGapSum_pos
    (n : ℕ) {qA qH : ℝ} (hqA_pos : 0 < qA) (hq_lt : qA < qH)
    (hqH_lt_one : qH < 1) {B : Candidate n → ℝ} (hB : StrictAnti B)
    (hH :
      0 < ∑ r : Candidate n, (qH * qH) ^ (r : ℕ) * B r) :
    0 < ∑ r : Candidate n,
      qH ^ (r : ℕ) * candidateRankCrossDelta n qA qH r * B r := by
  classical
  let A : ℝ := ∑ r : Candidate n, (qA * qH) ^ (r : ℕ) * B r
  let H : ℝ := ∑ r : Candidate n, (qH * qH) ^ (r : ℕ) * B r
  let P : ℝ := candidateRankPowerSum n (qA * qH)
  let Q : ℝ := candidateRankPowerSum n (qH * qH)
  let SA : ℝ := candidateRankPowerSum n qA
  let SH : ℝ := candidateRankPowerSum n qH
  have hqH_pos : 0 < qH := lt_trans hqA_pos hq_lt
  have hqAH_pos : 0 < qA * qH := mul_pos hqA_pos hqH_pos
  have hqHH_pos : 0 < qH * qH := mul_pos hqH_pos hqH_pos
  have hqAH_lt_qHH : qA * qH < qH * qH :=
    mul_lt_mul_of_pos_right hq_lt hqH_pos
  have hQ_pos : 0 < Q :=
    candidateRankPowerSum_pos n hqHH_pos
  have hSH_pos : 0 < SH :=
    candidateRankPowerSum_pos n hqH_pos
  have hE : 0 < Q * A - P * H := by
    simpa [A, H, P, Q] using
      candidateRankWeightedAverage_strictAnti n hqAH_pos hqAH_lt_qHH hB
  have hcoll : 0 < SH * P - SA * Q := by
    simpa [P, Q, SA, SH] using
      candidateRankCollisionWeight_cross_pos n hqA_pos hq_lt hqH_lt_one
  have hH' : 0 < H := by
    simpa [H] using hH
  have htarget : 0 < SH * A - SA * H := by
    have hE_lt : P * H < Q * A := sub_pos.mp hE
    have hcoll_lt : SA * Q < SH * P := sub_pos.mp hcoll
    have h1 : SH * (P * H) < SH * (Q * A) :=
      mul_lt_mul_of_pos_left hE_lt hSH_pos
    have h2 : SA * Q * H < SH * P * H :=
      mul_lt_mul_of_pos_right hcoll_lt hH'
    have h1' : SH * P * H < SH * (Q * A) := by
      nlinarith [h1]
    have hchain : SA * Q * H < SH * (Q * A) :=
      lt_trans h2 h1'
    have hQtarget : 0 < Q * (SH * A - SA * H) := by
      have heq : Q * (SH * A - SA * H) = SH * (Q * A) - SA * Q * H := by
        ring
      rw [heq]
      exact sub_pos.mpr hchain
    exact (mul_pos_iff_of_pos_left hQ_pos).mp hQtarget
  have hsum_eq :
      (∑ r : Candidate n,
        qH ^ (r : ℕ) * candidateRankCrossDelta n qA qH r * B r) =
        SH * A - SA * H := by
    unfold A H SA SH
    unfold candidateRankCrossDelta
    calc
      (∑ r : Candidate n,
        qH ^ (r : ℕ) *
            (qA ^ (r : ℕ) * candidateRankPowerSum n qH -
              qH ^ (r : ℕ) * candidateRankPowerSum n qA) * B r)
          =
          ∑ r : Candidate n,
            (candidateRankPowerSum n qH * ((qA * qH) ^ (r : ℕ) * B r) -
              candidateRankPowerSum n qA * ((qH * qH) ^ (r : ℕ) * B r)) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [mul_pow, mul_pow]
            ring
      _ =
          candidateRankPowerSum n qH *
              (∑ r : Candidate n, (qA * qH) ^ (r : ℕ) * B r) -
            candidateRankPowerSum n qA *
              (∑ r : Candidate n, (qH * qH) ^ (r : ℕ) * B r) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsum_eq]
  exact htarget

theorem candidateRankPrefix_cross_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    (k : Fin (n + 1)) :
    0 < candidateRankPrefixPowerSum n q₁ k * candidateRankPowerSum n q₂ -
      candidateRankPrefixPowerSum n q₂ k * candidateRankPowerSum n q₁ := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    if (i : ℕ) ≤ k.val then
      q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
        q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)
    else
      0
  have hdouble :
      candidateRankPrefixPowerSum n q₁ k * candidateRankPowerSum n q₂ -
        candidateRankPrefixPowerSum n q₂ k * candidateRankPowerSum n q₁ =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankPrefixPowerSum candidateRankPowerSum
    rw [Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hi : (i : ℕ) ≤ k.val
    · simp [t, hi]
    · simp [t, hi]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro i
      by_cases hi : (i : ℕ) ≤ k.val
      · simp [t, hi]
        ring
      · simp [t, hi])]
  let j₀ : Candidate n := ⟨k.val + 1, by omega⟩
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun i : Candidate n =>
      ∑ j : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) i <
            rankOf (Equiv.refl (Candidate n)) j then
          t i j + t j i
        else 0)
    (a₀ := (0 : Candidate n))
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun j : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) j then
          t (0 : Candidate n) j + t j (0 : Candidate n)
        else 0)
      (a₀ := j₀)
    · have hj₀_lt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j₀ := by
        change (0 : ℕ) < k.val + 1
        omega
      have h0_prefix : ((0 : Candidate n) : ℕ) ≤ k.val := Nat.zero_le k.val
      have hj₀_not_prefix : ¬((j₀ : Candidate n) : ℕ) ≤ k.val := by
        intro h
        exact Nat.not_succ_le_self k.val h
      have hterm :
          0 < t (0 : Candidate n) j₀ + t j₀ (0 : Candidate n) := by
        have hpow : q₁ ^ (j₀ : ℕ) < q₂ ^ (j₀ : ℕ) :=
          pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos)
            (by simp [j₀])
        simp [t, hj₀_not_prefix]
        exact hpow
      simpa [hj₀_lt] using hterm
    · intro j
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j
      · have hnonneg : 0 ≤ t (0 : Candidate n) j + t j (0 : Candidate n) := by
          by_cases hj : (j : ℕ) ≤ k.val
          · have h0 : ((0 : Candidate n) : ℕ) ≤ k.val := Nat.zero_le k.val
            simp [t, hj]
          · have h0 : ((0 : Candidate n) : ℕ) ≤ k.val := Nat.zero_le k.val
            have hpow : q₁ ^ (j : ℕ) ≤ q₂ ^ (j : ℕ) :=
              pow_le_pow_left₀ (le_of_lt hq₁_pos) (le_of_lt hq_lt) (j : ℕ)
            simp [t, hj]
            exact hpow
        exact if_pos hlt ▸ hnonneg
      · simp [hlt]
  · intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) i <
        rankOf (Equiv.refl (Candidate n)) j
    · have hnonneg : 0 ≤ t i j + t j i := by
        by_cases hi : (i : ℕ) ≤ k.val
        · by_cases hj : (j : ℕ) ≤ k.val
          · simp [t, hi, hj]
            ring_nf
            exact (show (0 : ℝ) ≤ 0 from le_rfl)
          · simp [t, hi, hj]
            have hij : i < j := by
              simpa [rankOf] using hlt
            have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
            have hpow' :
                q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ) <
                  q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
            exact le_of_lt hpow'
        · have hj : ¬(j : ℕ) ≤ k.val := by
            intro hj
            exact hi (le_trans (le_of_lt hlt) hj)
          simp [t, hi, hj]
      exact if_pos hlt ▸ hnonneg
    · simp [hlt]

theorem candidateRankWeightedPrefix_cross_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    (k : Fin (n + 1)) :
    0 < ∑ i : Candidate n,
      if (i : ℕ) ≤ k.val then
        q₂ ^ (i : ℕ) * candidateRankCrossDelta n q₁ q₂ i
      else
        0 := by
  classical
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    if (i : ℕ) ≤ k.val then
      q₂ ^ (i : ℕ) *
        (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
          q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ))
    else
      0
  have hdouble :
      (∑ i : Candidate n,
        if (i : ℕ) ≤ k.val then
          q₂ ^ (i : ℕ) * candidateRankCrossDelta n q₁ q₂ i
        else
          0) =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankCrossDelta candidateRankPowerSum
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hi : (i : ℕ) ≤ k.val
    · simp [t, hi]
      rw [mul_sub]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      calc
        q₂ ^ (i : ℕ) * (q₂ ^ (i : ℕ) * ∑ j : Candidate n, q₁ ^ (j : ℕ))
            = q₂ ^ (i : ℕ) *
                (∑ j : Candidate n, q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) := by
              rw [Finset.mul_sum]
        _ = ∑ j : Candidate n,
              q₂ ^ (i : ℕ) * (q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) := by
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (Candidate n)))
                  (f := fun j : Candidate n => q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ))
                  (a := q₂ ^ (i : ℕ)))
    · simp [t, hi]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro i
      by_cases hi : (i : ℕ) ≤ k.val
      · have hzero :
            q₁ ^ (i : ℕ) * q₂ ^ (i : ℕ) -
              q₂ ^ (i : ℕ) * q₁ ^ (i : ℕ) = 0 := by
          ring
        simp [t, hi, hzero]
      · simp [t, hi])]
  let j₀ : Candidate n := ⟨k.val + 1, by omega⟩
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun i : Candidate n =>
      ∑ j : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) i <
            rankOf (Equiv.refl (Candidate n)) j then
          t i j + t j i
        else 0)
    (a₀ := (0 : Candidate n))
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun j : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) j then
          t (0 : Candidate n) j + t j (0 : Candidate n)
        else 0)
      (a₀ := j₀)
    · have hj₀_lt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j₀ := by
        change (0 : ℕ) < k.val + 1
        omega
      have hj₀_not_prefix : ¬((j₀ : Candidate n) : ℕ) ≤ k.val := by
        intro h
        exact Nat.not_succ_le_self k.val h
      have hpow : q₁ ^ (j₀ : ℕ) < q₂ ^ (j₀ : ℕ) :=
        pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (by simp [j₀])
      have hterm :
          0 < t (0 : Candidate n) j₀ + t j₀ (0 : Candidate n) := by
        simp [t, hj₀_not_prefix]
        exact hpow
      simpa [hj₀_lt] using hterm
    · intro j
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j
      · have hnonneg :
            0 ≤ t (0 : Candidate n) j + t j (0 : Candidate n) := by
          by_cases hj : (j : ℕ) ≤ k.val
          · have h0j : (0 : Candidate n) < j := by
              simpa [rankOf] using hlt
            simpa [t, hj] using
              weightedRankPower_pair_add_nonneg
                hq₁_pos hq_lt hq₂_lt_one h0j
          · have hpow : q₁ ^ (j : ℕ) ≤ q₂ ^ (j : ℕ) :=
              pow_le_pow_left₀ (le_of_lt hq₁_pos) (le_of_lt hq_lt) (j : ℕ)
            simp [t, hj]
            exact hpow
        exact if_pos hlt ▸ hnonneg
      · simp [hlt]
  · intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) i <
        rankOf (Equiv.refl (Candidate n)) j
    · have hij : i < j := by
        simpa [rankOf] using hlt
      have hnonneg : 0 ≤ t i j + t j i := by
        by_cases hi : (i : ℕ) ≤ k.val
        · by_cases hj : (j : ℕ) ≤ k.val
          · simpa [t, hi, hj] using
              weightedRankPower_pair_add_nonneg
                hq₁_pos hq_lt hq₂_lt_one hij
          · have hpow :=
              rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
            have hinner :
                0 ≤ q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
                    q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ) :=
              sub_nonneg.mpr (le_of_lt (by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hpow))
            have hscale : 0 ≤ q₂ ^ (i : ℕ) :=
              pow_nonneg (le_of_lt hq₂_pos) (i : ℕ)
            simp [t, hi, hj]
            exact mul_nonneg hscale hinner
        · have hj : ¬(j : ℕ) ≤ k.val := by
            intro hj
            exact hi (le_trans (le_of_lt hlt) hj)
          simp [t, hi, hj]
      exact if_pos hlt ▸ hnonneg
    · simp [hlt]

theorem candidateRankWeightedPrefixCrossDeltaSum_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    {k : ℕ} (hk : k < n + 1) :
    0 < candidateRankWeightedPrefixCrossDeltaSum n q₁ q₂ k := by
  simpa [candidateRankWeightedPrefixCrossDeltaSum] using
    candidateRankWeightedPrefix_cross_pos n hq₁_pos hq_lt hq₂_lt_one
      (⟨k, hk⟩ : Fin (n + 1))

theorem candidateRankCrossDelta_scaled_strictAnti
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : Candidate n} (hij : i < j) :
    q₂ ^ (i : ℕ) * candidateRankCrossDelta n q₁ q₂ j <
      q₂ ^ (j : ℕ) * candidateRankCrossDelta n q₁ q₂ i := by
  have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
  unfold candidateRankCrossDelta
  have hsum_pos : 0 < candidateRankPowerSum n q₂ :=
    candidateRankPowerSum_pos n (lt_trans hq₁_pos hq_lt)
  have hcore :
      q₂ ^ (i : ℕ) * (q₁ ^ (j : ℕ) * candidateRankPowerSum n q₂) <
        q₂ ^ (j : ℕ) * (q₁ ^ (i : ℕ) * candidateRankPowerSum n q₂) := by
    nlinarith [mul_lt_mul_of_pos_right hpow hsum_pos]
  nlinarith

theorem candidateRankCrossDelta_last_neg
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂) :
    candidateRankCrossDelta n q₁ q₂ (⟨n + 1, by omega⟩ : Candidate n) < 0 := by
  classical
  let last : Candidate n := ⟨n + 1, by omega⟩
  have hpos :
      0 < q₂ ^ (last : ℕ) * candidateRankPowerSum n q₁ -
        q₁ ^ (last : ℕ) * candidateRankPowerSum n q₂ := by
    have hsum :
        q₂ ^ (last : ℕ) * candidateRankPowerSum n q₁ -
          q₁ ^ (last : ℕ) * candidateRankPowerSum n q₂ =
          ∑ j : Candidate n,
            (q₂ ^ (last : ℕ) * q₁ ^ (j : ℕ) -
              q₁ ^ (last : ℕ) * q₂ ^ (j : ℕ)) := by
      unfold candidateRankPowerSum
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hsum]
    apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
    · have hlt : (0 : Candidate n) < last := by
        change (0 : ℕ) < n + 1
        omega
      have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hlt
      exact sub_pos.mpr (by
        simpa [last, mul_comm, mul_left_comm, mul_assoc] using hpow)
    · intro j
      by_cases hj : j = last
      · subst j
        have hzero :
            q₂ ^ (last : ℕ) * q₁ ^ (last : ℕ) -
              q₁ ^ (last : ℕ) * q₂ ^ (last : ℕ) = 0 := by
          ring
        rw [hzero]
      · have hlt : j < last := by
          change (j : ℕ) < n + 1
          have hj_le : (j : ℕ) ≤ n + 1 := Nat.le_of_lt_succ j.isLt
          have hj_ne : (j : ℕ) ≠ n + 1 := by
            intro h
            exact hj (Fin.ext h)
          omega
        have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hlt
        exact sub_nonneg.mpr (le_of_lt (by
          simpa [last, mul_comm, mul_left_comm, mul_assoc] using hpow))
  unfold candidateRankCrossDelta
  nlinarith

theorem candidateRankWeightedSuffixCrossDeltaSum_last_neg
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂) :
    candidateRankWeightedSuffixCrossDeltaSum n q₁ q₂ n < 0 := by
  classical
  let last : Candidate n := ⟨n + 1, by omega⟩
  have hsum :
      candidateRankWeightedSuffixCrossDeltaSum n q₁ q₂ n =
        q₂ ^ (last : ℕ) * candidateRankCrossDelta n q₁ q₂ last := by
    unfold candidateRankWeightedSuffixCrossDeltaSum
    rw [Finset.sum_eq_single last]
    · simp [last]
    · intro s _ hs_ne
      have hs_not : ¬n < (s : ℕ) := by
        intro hs
        have hs_eq : (s : ℕ) = n + 1 := by
          have hs_le : (s : ℕ) ≤ n + 1 := Nat.le_of_lt_succ s.isLt
          omega
        exact hs_ne (Fin.ext hs_eq)
      simp [hs_not]
    · intro hlast
      exact False.elim (hlast (Finset.mem_univ last))
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  rw [hsum]
  exact mul_neg_of_pos_of_neg (pow_pos hq₂_pos (last : ℕ))
    (candidateRankCrossDelta_last_neg n hq₁_pos hq_lt)

theorem candidateRankPrefixWeightSum_nonneg
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q) (k : ℕ) :
    0 ≤ candidateRankPrefixWeightSum n q k := by
  classical
  unfold candidateRankPrefixWeightSum
  apply Finset.sum_nonneg
  intro r _
  by_cases hr : (r : ℕ) ≤ k
  · exact if_pos hr ▸ pow_nonneg hq_nonneg (r : ℕ)
  · simp [hr]

theorem candidateRankShiftedSuffixWeightSum_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) {k : ℕ} (hk : k < n + 1) :
    0 < candidateRankShiftedSuffixWeightSum n q k := by
  classical
  unfold candidateRankShiftedSuffixWeightSum
  let s₀ : Candidate n := ⟨k + 1, by omega⟩
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := s₀)
  · have hs₀ : k < (s₀ : ℕ) := by
      simp [s₀]
    have hpow : 0 < q ^ ((s₀ : ℕ) - 1) :=
      pow_pos hq_pos ((s₀ : ℕ) - 1)
    simpa [hs₀] using hpow
  · intro s
    by_cases hs : k < (s : ℕ)
    · exact if_pos hs ▸ le_of_lt (pow_pos hq_pos ((s : ℕ) - 1))
    · simp [hs]

theorem candidateRankAdjacentCoeff_eq_prefix_suffix
    (n : ℕ) (qA qH : ℝ) (k : ℕ) :
    candidateRankAdjacentCoeff n qA qH k =
      candidateRankShiftedSuffixWeightSum n qH k *
          candidateRankWeightedPrefixCrossDeltaSum n qA qH k -
        candidateRankPrefixWeightSum n qH k *
          candidateRankWeightedSuffixCrossDeltaSum n qA qH k := by
  classical
  let Δ : Candidate n → ℝ := fun r =>
    candidateRankCrossDelta n qA qH r
  let U : Candidate n → ℝ := fun s =>
    if k < (s : ℕ) then qH ^ ((s : ℕ) - 1) else 0
  let P : Candidate n → ℝ := fun r =>
    if (r : ℕ) ≤ k then qH ^ (r : ℕ) * Δ r else 0
  let Q : Candidate n → ℝ := fun r =>
    if (r : ℕ) ≤ k then qH ^ (r : ℕ) else 0
  let T : Candidate n → ℝ := fun s =>
    if k < (s : ℕ) then qH ^ (s : ℕ) * Δ s else 0
  unfold candidateRankAdjacentCoeff candidateRankShiftedSuffixWeightSum
    candidateRankWeightedPrefixCrossDeltaSum candidateRankPrefixWeightSum
    candidateRankWeightedSuffixCrossDeltaSum
  change (∑ r : Candidate n, ∑ s : Candidate n,
      if (r : ℕ) ≤ k ∧ k < (s : ℕ) then
        qH ^ ((r : ℕ) + (s : ℕ) - 1) *
          (Δ r - qH * Δ s)
      else
        0) =
    (∑ s : Candidate n, U s) * (∑ r : Candidate n, P r) -
      (∑ r : Candidate n, Q r) * (∑ s : Candidate n, T s)
  symm
  calc
    (∑ s : Candidate n, U s) * (∑ r : Candidate n, P r) -
        (∑ r : Candidate n, Q r) * (∑ s : Candidate n, T s)
        = ∑ r : Candidate n, ∑ s : Candidate n,
            (U s * P r - Q r * T s) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [← Finset.sum_sub_distrib]
    _ = ∑ r : Candidate n, ∑ s : Candidate n,
          if (r : ℕ) ≤ k ∧ k < (s : ℕ) then
            qH ^ ((r : ℕ) + (s : ℕ) - 1) *
              (Δ r - qH * Δ s)
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hr : (r : ℕ) ≤ k
          · by_cases hs : k < (s : ℕ)
            · have hs_pos : 0 < (s : ℕ) := lt_of_le_of_lt (Nat.zero_le k) hs
              have hsplit :
                  (r : ℕ) + (s : ℕ) - 1 =
                    (r : ℕ) + ((s : ℕ) - 1) := by
                omega
              have hs_pred : (s : ℕ) - 1 + 1 = (s : ℕ) := by
                omega
              have hpow_s : qH ^ (s : ℕ) =
                  qH ^ ((s : ℕ) - 1) * qH := by
                rw [← pow_succ, hs_pred]
              simp [U, P, Q, T, hr, hs]
              rw [hsplit, pow_add]
              rw [hpow_s]
              ring
            · have hspan : ¬((r : ℕ) ≤ k ∧ k < (s : ℕ)) := by
                intro h
                exact hs h.2
              simp [U, P, Q, T, hr, hs]
          · simp [U, P, Q, T, hr]

theorem candidateRankAdjacentCoeff_pos_of_suffix_nonpos
    (n : ℕ) {qA qH : ℝ} (hqA_pos : 0 < qA)
    (hq_lt : qA < qH) (hqH_lt_one : qH < 1)
    {k : ℕ} (hk : k < n + 1)
    (hsuffix :
      candidateRankWeightedSuffixCrossDeltaSum n qA qH k ≤ 0) :
    0 < candidateRankAdjacentCoeff n qA qH k := by
  have hqH_pos : 0 < qH := lt_trans hqA_pos hq_lt
  have hprefix :
      0 < candidateRankWeightedPrefixCrossDeltaSum n qA qH k :=
    candidateRankWeightedPrefixCrossDeltaSum_pos n hqA_pos hq_lt hqH_lt_one hk
  have hsuffixWeight :
      0 < candidateRankShiftedSuffixWeightSum n qH k :=
    candidateRankShiftedSuffixWeightSum_pos n hqH_pos hk
  have hprefixWeight :
      0 ≤ candidateRankPrefixWeightSum n qH k :=
    candidateRankPrefixWeightSum_nonneg n (le_of_lt hqH_pos) k
  rw [candidateRankAdjacentCoeff_eq_prefix_suffix]
  nlinarith [mul_pos hsuffixWeight hprefix,
    mul_nonpos_of_nonneg_of_nonpos hprefixWeight hsuffix]

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

theorem centerFirstWeight_cross_lt_of_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition := by
  have hsum_lt :
      candidateRankPowerSum n C.algorithm.q <
        candidateRankPowerSum n C.human.q :=
    candidateRankPowerSum_strict_mono n
      (le_of_lt C.algorithm.q_pos) hq_lt
  have halg_first :
      C.algorithm.firstWeight C.algorithm.centerFirst = halg_rank.firstTail := by
    rw [halg_rank.firstWeight_eq]
    simp [MallowsSpec.centerFirst, rankOf]
  have hhuman_first :
      C.human.firstWeight C.human.centerFirst = hhuman_rank.firstTail := by
    rw [hhuman_rank.firstWeight_eq]
    simp [MallowsSpec.centerFirst, rankOf]
  rw [halg_rank.partition_eq, hhuman_rank.partition_eq, halg_first, hhuman_first]
  calc
    hhuman_rank.firstTail *
          (candidateRankPowerSum n C.algorithm.q * halg_rank.firstTail)
        = halg_rank.firstTail * hhuman_rank.firstTail *
            candidateRankPowerSum n C.algorithm.q := by ring
    _ < halg_rank.firstTail * hhuman_rank.firstTail *
            candidateRankPowerSum n C.human.q :=
          mul_lt_mul_of_pos_left hsum_lt
            (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
    _ = halg_rank.firstTail *
          (candidateRankPowerSum n C.human.q * hhuman_rank.firstTail) := by ring

theorem centerFirstProb_lt_of_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    firstChoiceProb C.human.law C.human.centerFirst <
      firstChoiceProb C.algorithm.law C.human.centerFirst :=
   C.centerFirstProb_lt_of_centerFirstWeight_div_lt
    (C.centerFirstWeight_div_lt_of_cross_mul_lt
      (C.centerFirstWeight_cross_lt_of_rankFactorization
        halg_rank hhuman_rank hq_lt))

theorem firstWeightPrefix_cross_lt_of_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (k : Fin (n + 1)) :
    C.human.firstWeightPrefix k * C.algorithm.partition <
      C.algorithm.firstWeightPrefix k * C.human.partition := by
  have hprefix :
      0 < candidateRankPrefixPowerSum n C.algorithm.q k *
            candidateRankPowerSum n C.human.q -
          candidateRankPrefixPowerSum n C.human.q k *
            candidateRankPowerSum n C.algorithm.q :=
    candidateRankPrefix_cross_pos n C.algorithm.q_pos hq_lt k
  have hprefix_lt :
      candidateRankPrefixPowerSum n C.human.q k *
          candidateRankPowerSum n C.algorithm.q <
        candidateRankPrefixPowerSum n C.algorithm.q k *
          candidateRankPowerSum n C.human.q :=
    sub_pos.mp hprefix
  rw [C.algorithm.firstWeightPrefix_eq_rankPrefixPowerSum_mul halg_rank k,
    C.human.firstWeightPrefix_eq_rankPrefixPowerSum_mul hhuman_rank k,
    halg_rank.partition_eq, hhuman_rank.partition_eq]
  calc
    (candidateRankPrefixPowerSum n C.human.q k * hhuman_rank.firstTail) *
          (candidateRankPowerSum n C.algorithm.q * halg_rank.firstTail)
        = halg_rank.firstTail * hhuman_rank.firstTail *
            (candidateRankPrefixPowerSum n C.human.q k *
              candidateRankPowerSum n C.algorithm.q) := by ring
    _ < halg_rank.firstTail * hhuman_rank.firstTail *
            (candidateRankPrefixPowerSum n C.algorithm.q k *
              candidateRankPowerSum n C.human.q) :=
          mul_lt_mul_of_pos_left hprefix_lt
            (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
    _ = (candidateRankPrefixPowerSum n C.algorithm.q k * halg_rank.firstTail) *
          (candidateRankPowerSum n C.human.q * hhuman_rank.firstTail) := by ring

theorem weaker_center_cross_product_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      firstChoiceGapMass C.human.law value C.human.centerFirst :=
   C.weaker_center_cross_product_pos_of_strictlyCenterOrdered hvalue
    (C.centerFirstWeight_cross_lt_of_rankFactorization
      halg_rank hhuman_rank hq_lt)

theorem weaker_center_cross_weight_summand_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      C.human.firstChoiceGapWeight value C.human.centerFirst := by
  have hcross :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.human.centerFirst * C.human.partition := by
    simpa [C.algorithm_centerFirst_eq_human_centerFirst] using
      C.centerFirstWeight_cross_lt_of_rankFactorization
        halg_rank hhuman_rank hq_lt
  have hdiff :
      0 < C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition :=
    sub_pos.mpr hcross
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hvalue
  exact mul_pos hdiff
    (C.human.centerFirstGapWeight_pos_of_strictlyOrderedCenter hhuman_value)

/-- The ordered-pair summand in the cleared weaker-competition numerator. -/
noncomputable def crossPairTerm
    (value : Candidate n → ℝ) (c d : Candidate n) : ℝ :=
  (C.algorithm.firstWeight c * C.human.partition -
      C.human.firstWeight c * C.algorithm.partition) *
    C.human.firstSecondWeight c d * (value c - value d)

/--
The antisymmetrized ordered-pair bracket for the cleared weaker-competition
numerator.
-/
noncomputable def crossPairBracket (c d : Candidate n) : ℝ :=
  (C.algorithm.firstWeight c * C.human.partition -
      C.human.firstWeight c * C.algorithm.partition) *
    C.human.firstSecondWeight c d -
  (C.algorithm.firstWeight d * C.human.partition -
      C.human.firstWeight d * C.algorithm.partition) *
    C.human.firstSecondWeight d c

@[simp] theorem crossPairTerm_apply
    (value : Candidate n → ℝ) (c d : Candidate n) :
    C.crossPairTerm value c d =
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstSecondWeight c d * (value c - value d) := rfl

@[simp] theorem crossPairBracket_apply (c d : Candidate n) :
    C.crossPairBracket c d =
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstSecondWeight c d -
      (C.algorithm.firstWeight d * C.human.partition -
          C.human.firstWeight d * C.algorithm.partition) *
        C.human.firstSecondWeight d c := rfl

/--
Top-two expansion of the cleared weaker-competition numerator.
-/
theorem cross_weight_sum_eq_pair_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        C.crossPairTerm value c d := by
  classical
  calc
    ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c
        = ∑ c : Candidate n,
            (C.algorithm.firstWeight c * C.human.partition -
                C.human.firstWeight c * C.algorithm.partition) *
              (∑ d : Candidate n,
                C.human.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [C.human.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          (C.human.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        C.crossPairTerm value c d := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          unfold crossPairTerm
          ring

/--
Pairing the ordered weaker-competition top-two events `(c,d)` and `(d,c)`
produces one cross bracket times the value difference.
-/
theorem crossPairTerm_add_swap
    (value : Candidate n → ℝ) (c d : Candidate n) :
    C.crossPairTerm value c d + C.crossPairTerm value d c =
      C.crossPairBracket c d * (value c - value d) := by
  unfold crossPairTerm crossPairBracket
  ring

/-- Coefficient on the adjacent center-rank gap between positions `k` and `k+1`. -/
noncomputable def crossAdjacentCoeff (k : ℕ) : ℝ :=
  ∑ c : Candidate n, ∑ d : Candidate n,
    if (rankOf C.human.center c).val ≤ k ∧
        k < (rankOf C.human.center d).val then
      C.crossPairBracket c d
    else
      0

theorem crossAdjacentCoeff_eq_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (k : ℕ) :
    C.crossAdjacentCoeff k =
      halg_rank.firstTail * hhuman_rank.firstTail * hhuman_rank.firstSecondTail *
        candidateRankAdjacentCoeff n C.algorithm.q C.human.q k := by
  classical
  unfold crossAdjacentCoeff candidateRankAdjacentCoeff
  let scale : ℝ :=
    halg_rank.firstTail * hhuman_rank.firstTail * hhuman_rank.firstSecondTail
  let R : Candidate n → Candidate n → ℝ := fun r s =>
    C.human.q ^ ((r : ℕ) + (s : ℕ) - 1) *
      (candidateRankCrossDelta n C.algorithm.q C.human.q r -
        C.human.q * candidateRankCrossDelta n C.algorithm.q C.human.q s)
  let G : Candidate n → Candidate n → ℝ := fun c d =>
    if (rankOf C.human.center c).val ≤ k ∧
        k < (rankOf C.human.center d).val then
      C.crossPairBracket c d
    else
      0
  change (∑ c : Candidate n, ∑ d : Candidate n, G c d) =
    scale * (∑ r : Candidate n, ∑ s : Candidate n,
      if (r : ℕ) ≤ k ∧ k < (s : ℕ) then R r s else 0)
  have hreindex :
      (∑ c : Candidate n, ∑ d : Candidate n, G c d) =
        ∑ r : Candidate n, ∑ s : Candidate n,
          G (C.human.center r) (C.human.center s) := by
    calc
      (∑ c : Candidate n, ∑ d : Candidate n, G c d)
          = ∑ r : Candidate n, ∑ d : Candidate n,
              G (C.human.center r) d := by
            simpa using
              (Equiv.sum_comp C.human.center.symm
                (fun r : Candidate n =>
                  ∑ d : Candidate n, G (C.human.center r) d))
      _ = ∑ r : Candidate n, ∑ s : Candidate n,
              G (C.human.center r) (C.human.center s) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            simpa using
              (Equiv.sum_comp C.human.center.symm
                (fun s : Candidate n =>
                  G (C.human.center r) (C.human.center s)))
  calc
    (∑ c : Candidate n, ∑ d : Candidate n, G c d)
        = ∑ r : Candidate n, ∑ s : Candidate n,
            G (C.human.center r) (C.human.center s) := hreindex
    _ = ∑ r : Candidate n, ∑ s : Candidate n,
          if (r : ℕ) ≤ k ∧ k < (s : ℕ) then scale * R r s else 0 := by
        refine Finset.sum_congr rfl ?_
        intro r _
        refine Finset.sum_congr rfl ?_
        intro s _
        by_cases hspan : (r : ℕ) ≤ k ∧ k < (s : ℕ)
        · have hrs : r < s := by
            change (r : ℕ) < (s : ℕ)
            exact lt_of_le_of_lt hspan.1 hspan.2
          have hspan_center :
              (rankOf C.human.center (C.human.center r)).val ≤ k ∧
                k < (rankOf C.human.center (C.human.center s)).val := by
            simpa [rankOf] using hspan
          have halg_first_r :
              C.algorithm.firstWeight (C.human.center r) =
                C.algorithm.q ^ (r : ℕ) * halg_rank.firstTail := by
            rw [halg_rank.firstWeight_eq]
            simp [rankOf, C.same_center]
          have halg_first_s :
              C.algorithm.firstWeight (C.human.center s) =
                C.algorithm.q ^ (s : ℕ) * halg_rank.firstTail := by
            rw [halg_rank.firstWeight_eq]
            simp [rankOf, C.same_center]
          have hhuman_first_r :
              C.human.firstWeight (C.human.center r) =
                C.human.q ^ (r : ℕ) * hhuman_rank.firstTail := by
            rw [hhuman_rank.firstWeight_eq]
            simp [rankOf]
          have hhuman_first_s :
              C.human.firstWeight (C.human.center s) =
                C.human.q ^ (s : ℕ) * hhuman_rank.firstTail := by
            rw [hhuman_rank.firstWeight_eq]
            simp [rankOf]
          have hhuman_second_rs :
              C.human.firstSecondWeight (C.human.center r) (C.human.center s) =
                C.human.q ^ ((r : ℕ) + (s : ℕ) - 1) *
                  hhuman_rank.firstSecondTail := by
            rw [hhuman_rank.firstSecondWeight_eq_of_lt]
            · simp [rankOf]
            · simpa [rankOf] using hrs
          have hhuman_second_sr :
              C.human.firstSecondWeight (C.human.center s) (C.human.center r) =
                C.human.q *
                  (C.human.q ^ ((r : ℕ) + (s : ℕ) - 1) *
                    hhuman_rank.firstSecondTail) := by
            rw [hhuman_rank.firstSecondWeight_swap_eq_of_lt]
            · simp [rankOf]
            · simpa [rankOf] using hrs
          simp [G, hspan_center, hspan]
          rw [halg_first_r, halg_first_s, hhuman_first_r, hhuman_first_s,
            halg_rank.partition_eq, hhuman_rank.partition_eq,
            hhuman_second_rs, hhuman_second_sr]
          dsimp [scale, R, candidateRankCrossDelta]
          ring
        · have hspan_center :
              ¬((rankOf C.human.center (C.human.center r)).val ≤ k ∧
                k < (rankOf C.human.center (C.human.center s)).val) := by
            simpa [rankOf] using hspan
          simp [G, hspan_center, hspan]
    _ = scale * (∑ r : Candidate n, ∑ s : Candidate n,
          if (r : ℕ) ≤ k ∧ k < (s : ℕ) then R r s else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro s _
        by_cases hspan : (r : ℕ) ≤ k ∧ k < (s : ℕ) <;>
          simp [hspan]

theorem crossAdjacentCoeff_pos_of_rankFactorization_and_suffix_nonpos
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1)
    {k : ℕ} (hk : k ∈ Finset.range (n + 1))
    (hsuffix :
      candidateRankWeightedSuffixCrossDeltaSum n C.algorithm.q C.human.q k ≤ 0) :
    0 < C.crossAdjacentCoeff k := by
  have hcoeff :
      0 < candidateRankAdjacentCoeff n C.algorithm.q C.human.q k :=
    candidateRankAdjacentCoeff_pos_of_suffix_nonpos n
      C.algorithm.q_pos hq_lt hhuman_q_lt_one (Finset.mem_range.mp hk) hsuffix
  rw [C.crossAdjacentCoeff_eq_rankFactorization halg_rank hhuman_rank k]
  exact mul_pos
    (mul_pos (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
      hhuman_rank.firstSecondTail_pos)
    hcoeff

theorem cross_ordered_bracket_sum_eq_adjacent_coeff_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n, ∑ d : Candidate n,
      if rankOf C.human.center c < rankOf C.human.center d then
        C.crossPairBracket c d * (value c - value d)
      else 0) =
      ∑ k ∈ Finset.range (n + 1),
        C.crossAdjacentCoeff k *
          centerAdjacentGapAt C.human.center value k := by
  classical
  calc
    (∑ c : Candidate n, ∑ d : Candidate n,
      if rankOf C.human.center c < rankOf C.human.center d then
        C.crossPairBracket c d * (value c - value d)
      else 0)
        = ∑ c : Candidate n, ∑ d : Candidate n,
            ∑ k ∈ Finset.range (n + 1),
              if (rankOf C.human.center c).val ≤ k ∧
                  k < (rankOf C.human.center d).val then
                C.crossPairBracket c d *
                  centerAdjacentGapAt C.human.center value k
              else
                0 := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hlt : rankOf C.human.center c < rankOf C.human.center d
          · have hgap := value_sub_eq_sum_centerAdjacentGapAt
              C.human.center value hlt
            have hrange :
                (Finset.range (n + 1)).filter
                    (fun k =>
                      (rankOf C.human.center c).val ≤ k ∧
                        k < (rankOf C.human.center d).val) =
                  Finset.Ico (rankOf C.human.center c).val
                    (rankOf C.human.center d).val := by
              ext k
              constructor
              · intro hk
                have hk' := Finset.mem_filter.mp hk
                exact Finset.mem_Ico.mpr hk'.2
              · intro hk
                have hk' := Finset.mem_Ico.mp hk
                have hd_le : (rankOf C.human.center d).val ≤ n + 1 := by
                  omega
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_range.mpr (lt_of_lt_of_le hk'.2 hd_le), hk'⟩
            calc
              (if rankOf C.human.center c < rankOf C.human.center d then
                  C.crossPairBracket c d * (value c - value d)
                else 0)
                  = C.crossPairBracket c d * (value c - value d) := by
                    simp [hlt]
              _ = C.crossPairBracket c d *
                    (∑ k ∈ Finset.Ico (rankOf C.human.center c).val
                      (rankOf C.human.center d).val,
                      centerAdjacentGapAt C.human.center value k) := by
                    rw [hgap]
              _ = ∑ k ∈ Finset.Ico (rankOf C.human.center c).val
                    (rankOf C.human.center d).val,
                    C.crossPairBracket c d *
                      centerAdjacentGapAt C.human.center value k := by
                    rw [Finset.mul_sum]
              _ = ∑ k ∈ Finset.range (n + 1),
                    if (rankOf C.human.center c).val ≤ k ∧
                        k < (rankOf C.human.center d).val then
                      C.crossPairBracket c d *
                        centerAdjacentGapAt C.human.center value k
                    else
                      0 := by
                    rw [← hrange]
                    rw [Finset.sum_filter]
          · have hempty :
                (Finset.range (n + 1)).filter
                    (fun k =>
                      (rankOf C.human.center c).val ≤ k ∧
                        k < (rankOf C.human.center d).val) = ∅ := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_range]
              constructor
              · intro hk
                exfalso
                apply hlt
                change (rankOf C.human.center c).val <
                  (rankOf C.human.center d).val
                exact lt_of_le_of_lt hk.2.1 hk.2.2
              · intro h
                simpa using h
            simp [hlt, ← Finset.sum_filter, hempty]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ c : Candidate n, ∑ d : Candidate n,
          if (rankOf C.human.center c).val ≤ k ∧
              k < (rankOf C.human.center d).val then
            C.crossPairBracket c d *
              centerAdjacentGapAt C.human.center value k
          else
            0 := by
          calc
            (∑ c : Candidate n, ∑ d : Candidate n,
                ∑ k ∈ Finset.range (n + 1),
                  if (rankOf C.human.center c).val ≤ k ∧
                      k < (rankOf C.human.center d).val then
                    C.crossPairBracket c d *
                      centerAdjacentGapAt C.human.center value k
                  else
                    0)
                = ∑ c : Candidate n, ∑ k ∈ Finset.range (n + 1),
                    ∑ d : Candidate n,
                      if (rankOf C.human.center c).val ≤ k ∧
                          k < (rankOf C.human.center d).val then
                        C.crossPairBracket c d *
                          centerAdjacentGapAt C.human.center value k
                      else
                        0 := by
                  refine Finset.sum_congr rfl ?_
                  intro c _
                  rw [Finset.sum_comm]
            _ = ∑ k ∈ Finset.range (n + 1), ∑ c : Candidate n, ∑ d : Candidate n,
                  if (rankOf C.human.center c).val ≤ k ∧
                      k < (rankOf C.human.center d).val then
                    C.crossPairBracket c d *
                      centerAdjacentGapAt C.human.center value k
                  else
                    0 := by
                  rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (n + 1),
          C.crossAdjacentCoeff k *
            centerAdjacentGapAt C.human.center value k := by
          refine Finset.sum_congr rfl ?_
          intro k _
          unfold crossAdjacentCoeff
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hspan :
              (rankOf C.human.center c).val ≤ k ∧
                k < (rankOf C.human.center d).val <;>
            simp [hspan]

theorem crossPairTerm_add_swap_nonneg
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 ≤ C.crossPairBracket c d)
    (hvalue : value d ≤ value c) :
    0 ≤ C.crossPairTerm value c d + C.crossPairTerm value d c := by
  rw [C.crossPairTerm_add_swap value c d]
  exact mul_nonneg hbracket (sub_nonneg.mpr hvalue)

theorem crossPairTerm_add_swap_pos
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 < C.crossPairBracket c d)
    (hvalue : value d < value c) :
    0 < C.crossPairTerm value c d + C.crossPairTerm value d c := by
  rw [C.crossPairTerm_add_swap value c d]
  exact mul_pos hbracket (sub_pos.mpr hvalue)

/--
The cleared weaker-competition pair sum regrouped over center-ordered unordered
pairs for the human Mallows center.
-/
theorem cross_pair_sum_eq_ordered_swap_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n, ∑ d : Candidate n,
        C.crossPairTerm value c d) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        if rankOf C.human.center c < rankOf C.human.center d then
          C.crossPairTerm value c d + C.crossPairTerm value d c
        else 0 := by
  refine MallowsSpec.pair_sum_eq_ordered_swap_sum C.human.center (C.crossPairTerm value) ?_
  intro c
  unfold crossPairTerm
  ring

theorem cross_weight_sum_eq_adjacent_coeff_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) =
      ∑ k ∈ Finset.range (n + 1),
        C.crossAdjacentCoeff k *
          centerAdjacentGapAt C.human.center value k := by
  calc
    (∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c)
        = ∑ c : Candidate n, ∑ d : Candidate n,
            C.crossPairTerm value c d := by
          rw [C.cross_weight_sum_eq_pair_sum value]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
          if rankOf C.human.center c < rankOf C.human.center d then
            C.crossPairTerm value c d + C.crossPairTerm value d c
          else 0 := by
          rw [C.cross_pair_sum_eq_ordered_swap_sum value]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
          if rankOf C.human.center c < rankOf C.human.center d then
            C.crossPairBracket c d * (value c - value d)
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hlt : rankOf C.human.center c < rankOf C.human.center d
          · rw [if_pos hlt, if_pos hlt]
            exact C.crossPairTerm_add_swap value c d
          · simp [hlt]
    _ = ∑ k ∈ Finset.range (n + 1),
          C.crossAdjacentCoeff k *
            centerAdjacentGapAt C.human.center value k := by
          rw [C.cross_ordered_bracket_sum_eq_adjacent_coeff_sum value]

theorem cross_weight_sum_pos_of_adjacent_coeff_pos
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (hcoeff : ∀ k ∈ Finset.range (n + 1), 0 < C.crossAdjacentCoeff k) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  rw [C.cross_weight_sum_eq_adjacent_coeff_sum value]
  refine Finset.sum_pos ?hpos ?hne
  · intro k hk
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    have hk1 : k + 1 < n + 2 := by
      omega
    exact mul_pos (hcoeff k hk)
      (centerAdjacentGapAt_pos_of_strictlyOrderedBy hvalue hk1)
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

theorem cross_weight_sum_pos_of_rankFactorization_and_suffix_nonpos
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1)
    (hsuffix :
      ∀ k ∈ Finset.range (n + 1),
        candidateRankWeightedSuffixCrossDeltaSum n C.algorithm.q C.human.q k ≤ 0) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c :=
   C.cross_weight_sum_pos_of_adjacent_coeff_pos hvalue
    (fun k hk =>
      C.crossAdjacentCoeff_pos_of_rankFactorization_and_suffix_nonpos
        halg_rank hhuman_rank hq_lt hhuman_q_lt_one hk (hsuffix k hk))

theorem cross_weight_sum_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  classical
  let B : Candidate n → ℝ := fun r =>
    candidateRankConditionalGap n C.human.q
      (fun s : Candidate n => value (C.human.center s)) r
  have hvalue_rank :
      ∀ i j : Candidate n, i < j →
        value (C.human.center j) < value (C.human.center i) := by
    intro i j hij
    exact hvalue (by simpa [rankOf] using hij)
  have hB : StrictAnti B := by
    dsimp [B]
    exact candidateRankConditionalGap_strictAnti n C.human.q_pos hvalue_rank
  have hH :
      0 < ∑ r : Candidate n,
        (C.human.q * C.human.q) ^ (r : ℕ) * B r := by
    simpa [B] using
      candidateRankSquareWeightedConditionalGap_pos n
        C.human.q_pos hhuman_q_lt_one hvalue_rank
  have hpure :
      0 < ∑ r : Candidate n,
        C.human.q ^ (r : ℕ) *
          candidateRankCrossDelta n C.algorithm.q C.human.q r * B r :=
    candidateRankCrossConditionalGapSum_pos n
      C.algorithm.q_pos hq_lt hhuman_q_lt_one hB hH
  let scale : ℝ :=
    halg_rank.firstTail * hhuman_rank.firstTail * hhuman_rank.firstSecondTail
  have hscale_pos : 0 < scale :=
    mul_pos (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
      hhuman_rank.firstSecondTail_pos
  have hsum_eq :
      (∑ c : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          C.human.firstChoiceGapWeight value c) =
        scale * ∑ r : Candidate n,
          C.human.q ^ (r : ℕ) *
            candidateRankCrossDelta n C.algorithm.q C.human.q r * B r := by
    let F : Candidate n → ℝ := fun c =>
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c
    calc
      (∑ c : Candidate n, F c)
          = ∑ r : Candidate n, F (C.human.center r) := by
            simpa using
              (Equiv.sum_comp C.human.center (fun c : Candidate n => F c)).symm
      _ = ∑ r : Candidate n,
            scale *
              (C.human.q ^ (r : ℕ) *
                candidateRankCrossDelta n C.algorithm.q C.human.q r * B r) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            have halg_first :
                C.algorithm.firstWeight (C.human.center r) =
                  C.algorithm.q ^ (r : ℕ) * halg_rank.firstTail := by
              rw [halg_rank.firstWeight_eq]
              simp [rankOf, C.same_center]
            have hhuman_first :
                C.human.firstWeight (C.human.center r) =
                  C.human.q ^ (r : ℕ) * hhuman_rank.firstTail := by
              rw [hhuman_rank.firstWeight_eq]
              simp [rankOf]
            have hgap :
                C.human.firstChoiceGapWeight value (C.human.center r) =
                  C.human.q ^ (r : ℕ) * hhuman_rank.firstSecondTail * B r := by
              rw [C.human.firstChoiceGapWeight_eq_rankConditionalGap
                hhuman_rank value (C.human.center r)]
              simp [B, rankOf]
            simp [F, scale, candidateRankCrossDelta]
            rw [halg_first, hhuman_first, halg_rank.partition_eq,
              hhuman_rank.partition_eq, hgap]
            ring
      _ = scale * ∑ r : Candidate n,
            C.human.q ^ (r : ℕ) *
              candidateRankCrossDelta n C.algorithm.q C.human.q r * B r := by
            rw [Finset.mul_sum]
  rw [hsum_eq]
  exact mul_pos hscale_pos hpure

/--
Pairwise cross-bracket signs imply positivity of the cleared
weaker-competition numerator.
-/
theorem cross_weight_sum_pos_of_pair_brackets
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (hbracket_nonneg :
      ∀ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d →
        0 ≤ C.crossPairBracket c d)
    (hbracket_pos :
      ∃ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d ∧
        0 < C.crossPairBracket c d) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  classical
  rw [C.cross_weight_sum_eq_pair_sum value]
  rw [C.cross_pair_sum_eq_ordered_swap_sum value]
  rcases hbracket_pos with ⟨c₀, d₀, hlt₀, hbracket₀⟩
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun c : Candidate n =>
      ∑ d : Candidate n,
        if rankOf C.human.center c < rankOf C.human.center d then
          C.crossPairTerm value c d + C.crossPairTerm value d c
        else 0)
    (a₀ := c₀)
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun d : Candidate n =>
        if rankOf C.human.center c₀ < rankOf C.human.center d then
          C.crossPairTerm value c₀ d + C.crossPairTerm value d c₀
        else 0)
      (a₀ := d₀)
    · have hpos := C.crossPairTerm_add_swap_pos
          (value := value) hbracket₀ (hvalue hlt₀)
      simpa [hlt₀, crossPairTerm] using hpos
    · intro d
      by_cases hlt : rankOf C.human.center c₀ < rankOf C.human.center d
      · exact if_pos hlt ▸
          C.crossPairTerm_add_swap_nonneg
            (value := value) (hbracket_nonneg c₀ d hlt)
            (le_of_lt (hvalue hlt))
      · simp [hlt]
  · intro c
    apply Finset.sum_nonneg
    intro d _
    by_cases hlt : rankOf C.human.center c < rankOf C.human.center d
    · exact if_pos hlt ▸
        C.crossPairTerm_add_swap_nonneg
          (value := value) (hbracket_nonneg c d hlt)
          (le_of_lt (hvalue hlt))
    · simp [hlt]

/--
Appendix-E/F pair-bracket certificate for the finite Mallows sums.

This replaces the three total finite-sum assumptions by local ordered-pair
bracket inequalities.
-/
structure CenterMallowsPairBracketCertificate
    (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_bracket_nonneg :
    ∀ c d : Candidate n, rankOf C.algorithm.center c < rankOf C.algorithm.center d →
      0 ≤ C.algorithm.independentPairBracket c d
  algorithm_bracket_pos :
    ∃ c d : Candidate n, rankOf C.algorithm.center c < rankOf C.algorithm.center d ∧
      0 < C.algorithm.independentPairBracket c d
  human_bracket_nonneg :
    ∀ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d →
      0 ≤ C.human.independentPairBracket c d
  human_bracket_pos :
    ∃ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d ∧
      0 < C.human.independentPairBracket c d
  cross_bracket_nonneg :
    ∀ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d →
      0 ≤ C.crossPairBracket c d
  cross_bracket_pos :
    ∃ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d ∧
      0 < C.crossPairBracket c d

/--
Pair-bracket signs instantiate the existing cleared finite-sum Mallows
certificate.
-/
theorem centerMallowsFiniteSumCertificate_of_pairBracketCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsPairBracketCertificate value) :
    C.CenterMallowsFiniteSumCertificate value := by
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact cert.strictly_center_ordered
  constructor
  · exact cert.strictly_center_ordered
  · exact C.algorithm.independent_weight_sum_pos_of_pair_brackets
      cert.strictly_center_ordered
      cert.algorithm_bracket_nonneg
      cert.algorithm_bracket_pos
  · exact C.human.independent_weight_sum_pos_of_pair_brackets
      hhuman_value
      cert.human_bracket_nonneg
      cert.human_bracket_pos
  · exact C.cross_weight_sum_pos_of_pair_brackets
      hhuman_value
      cert.cross_bracket_nonneg
      cert.cross_bracket_pos

/--
Pair-bracket signs imply the pointwise Mallows paper hypotheses.
-/
theorem theorem3_pointwise_of_centerMallowsPairBracketCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsPairBracketCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    (C.centerMallowsFiniteSumCertificate_of_pairBracketCertificate cert)

/--
Rank-factorized Mallows first/top-two formulas discharge the two
independent-reranking finite sums. The weaker-competition cleared finite sum is
kept explicit because its proof needs the separate Mallows majorization
argument.
-/
theorem centerMallowsFiniteSumCertificate_of_rankFactorization_and_crossWeight
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hweaker : 0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) :
    C.CenterMallowsFiniteSumCertificate value := by
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hstrict
  constructor
  · exact hstrict
  · exact C.algorithm.independent_weight_sum_pos_of_rankFactorization
      halg_rank hn halg_q_lt_one hstrict
  · exact C.human.independent_weight_sum_pos_of_rankFactorization
      hhuman_rank hn hhuman_q_lt_one hhuman_value
  · exact hweaker

/--
Rank-factorized Mallows first/top-two formulas discharge all three cleared
finite Mallows sums, including the weaker-competition sum via the paper's
conditional-gap/MLR argument.
-/
theorem centerMallowsFiniteSumCertificate_of_rankFactorization
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    C.CenterMallowsFiniteSumCertificate value := by
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hstrict
  exact C.centerMallowsFiniteSumCertificate_of_rankFactorization_and_crossWeight
    hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one
    (C.cross_weight_sum_pos_of_rankFactorization
      hhuman_value halg_rank hhuman_rank hq_lt hhuman_q_lt_one)

/--
Paper-hypothesis theorem with independent-reranking finite sums proved from
rank factorization; only the weaker-competition finite Mallows inequality
remains explicit.
-/
theorem theorem3_pointwise_of_rankFactorization_and_crossWeight
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hweaker : 0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) :
    Model.PaperHypotheses (C.toModel value) :=
   C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    (C.centerMallowsFiniteSumCertificate_of_rankFactorization_and_crossWeight
      hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one hweaker)

/--
Paper-hypothesis theorem with all three finite Mallows inequalities proved from
rank factorization.
-/
theorem theorem3_pointwise_of_rankFactorization
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    Model.PaperHypotheses (C.toModel value) :=
   C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    (C.centerMallowsFiniteSumCertificate_of_rankFactorization
      hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one hq_lt)

end MallowsComparison

end KR21Monoculture

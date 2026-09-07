import KR21Monoculture.MallowsPairwise
import KR21Monoculture.Theorem1

open scoped BigOperators
open AppliedModelingLib

/-!
# Parameterized Mallows Families

This file connects the fixed-parameter Mallows theorem to the family-level
Theorem 1 interface.  It packages the remaining Definition 1 analytic facts
separately from the fixed-parameter Mallows finite-sum proof of Definitions 2
and 3.
-/

namespace KR21Monoculture

/-- Inverse Mallows parameter for the paper convention `θ = φ - 1`. -/
noncomputable def mallowsInverseAccuracyQ (θ : ℝ) : ℝ := (θ + 1)⁻¹

theorem mallowsInverseAccuracyQ_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < mallowsInverseAccuracyQ θ := by
  unfold mallowsInverseAccuracyQ
  exact inv_pos.mpr (by linarith)

theorem mallowsInverseAccuracyQ_lt_one {θ : ℝ} (hθ : 0 < θ) :
    mallowsInverseAccuracyQ θ < 1 := by
  unfold mallowsInverseAccuracyQ
  exact inv_lt_one_of_one_lt₀ (by linarith)

theorem mallowsInverseAccuracyQ_strictAnti {θA θH : ℝ}
    (hθH : 0 < θH) (hθ : θH < θA) :
    mallowsInverseAccuracyQ θA < mallowsInverseAccuracyQ θH := by
  unfold mallowsInverseAccuracyQ
  have hA : 0 < θA + 1 := by linarith
  have hH : 0 < θH + 1 := by linarith
  exact (inv_lt_inv₀ hA hH).2 (by linarith)

/--
Totalized inverse Mallows accuracy parameter.

The paper only uses positive `θ`; outside that domain this definition returns
`1` so that `θ ↦ MallowsSpec.ofQ ...` is a total Lean function.
-/
noncomputable def mallowsAccuracyQ (θ : ℝ) : ℝ := if 0 < θ then mallowsInverseAccuracyQ θ else 1

theorem mallowsAccuracyQ_eq_of_pos {θ : ℝ} (hθ : 0 < θ) :
    mallowsAccuracyQ θ = mallowsInverseAccuracyQ θ := by
  simp [mallowsAccuracyQ, hθ]

theorem mallowsAccuracyQ_pos (θ : ℝ) :
    0 < mallowsAccuracyQ θ := by
  unfold mallowsAccuracyQ
  by_cases hθ : 0 < θ
  · simp [hθ, mallowsInverseAccuracyQ_pos hθ]
  · simp [hθ]

theorem mallowsAccuracyQ_lt_one {θ : ℝ} (hθ : 0 < θ) :
    mallowsAccuracyQ θ < 1 := by
  rw [mallowsAccuracyQ_eq_of_pos hθ]
  exact mallowsInverseAccuracyQ_lt_one hθ

theorem mallowsAccuracyQ_strictAnti {θA θH : ℝ}
    (hθH : 0 < θH) (hθ : θH < θA) :
    mallowsAccuracyQ θA < mallowsAccuracyQ θH := by
  rw [mallowsAccuracyQ_eq_of_pos (lt_trans hθH hθ),
    mallowsAccuracyQ_eq_of_pos hθH]
  exact mallowsInverseAccuracyQ_strictAnti hθH hθ

theorem exists_gt_mallowsAccuracyQ_lt (lower δ : ℝ) (hδ : 0 < δ) :
    ∃ hi : ℝ, lower < hi ∧ mallowsAccuracyQ hi < δ := by
  let hi : ℝ := max lower 0 + δ⁻¹ + 1
  have hmax_lower : lower ≤ max lower 0 := le_max_left lower 0
  have hmax_nonneg : 0 ≤ max lower 0 := le_max_right lower 0
  have hinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hlower_hi : lower < hi := by
    dsimp [hi]
    linarith
  have hhi_pos : 0 < hi := by
    dsimp [hi]
    linarith
  refine ⟨hi, hlower_hi, ?_⟩
  rw [mallowsAccuracyQ_eq_of_pos hhi_pos]
  unfold mallowsInverseAccuracyQ
  have hden_pos : 0 < hi + 1 := by linarith
  have h_inv_lt_den : δ⁻¹ < hi + 1 := by
    dsimp [hi]
    linarith
  exact (inv_lt_comm₀ hden_pos hδ).2 h_inv_lt_den

/-- Concrete Mallows specification for the paper's `θ = φ - 1` convention. -/
noncomputable def concreteMallowsSpec {n : ℕ}
    (center : Ranking n) (θ : ℝ) : MallowsSpec n := MallowsSpec.ofQ center (mallowsAccuracyQ θ) (mallowsAccuracyQ_pos θ)

theorem mallowsAccuracyQ_continuousAt_of_pos {θ : ℝ} (hθ : 0 < θ) :
    ContinuousAt mallowsAccuracyQ θ := by
  have hlocal : mallowsInverseAccuracyQ =ᶠ[nhds θ] mallowsAccuracyQ := by
    filter_upwards [eventually_gt_nhds hθ] with y hy
    simp [mallowsAccuracyQ, hy]
  have hcont : ContinuousAt mallowsInverseAccuracyQ θ := by
    unfold mallowsInverseAccuracyQ
    exact (continuousAt_id.add_const 1).inv₀
      (by
        change θ + 1 ≠ 0
        linarith)
  exact hcont.congr hlocal

/--
Atomwise continuity of the concrete finite Mallows law at every positive
accuracy parameter. This is the continuity part of the paper's Definition 1 in
the finite epsilon-delta interface used by Theorem 1.
-/
theorem concreteMallowsSpec_atom_continuity
    {n : ℕ} (center : Ranking n) {θ : ℝ} (hθ : 0 < θ)
    (π : Ranking n) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun θ' => (((concreteMallowsSpec center θ').law) π).toReal) θ := by
  have hq_cont : ContinuousAt mallowsAccuracyQ θ :=
    mallowsAccuracyQ_continuousAt_of_pos hθ
  have hnum_cont :
      ContinuousAt
        (fun θ' => mallowsWeight (mallowsAccuracyQ θ') center π) θ := by
    unfold mallowsWeight
    exact hq_cont.pow _
  have hden_cont :
      ContinuousAt
        (fun θ' => mallowsPartition (mallowsAccuracyQ θ') center) θ := by
    unfold mallowsPartition
    exact AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Ranking n)))
      (f := fun τ θ' => mallowsWeight (mallowsAccuracyQ θ') center τ)
      (fun τ _ => by
        unfold mallowsWeight
        exact hq_cont.pow _)
  have hden_ne :
      mallowsPartition (mallowsAccuracyQ θ) center ≠ 0 :=
    ne_of_gt (mallowsPartition_pos (hq := mallowsAccuracyQ_pos θ) center)
  have hratio :
      ContinuousAt
        (fun θ' =>
          mallowsWeight (mallowsAccuracyQ θ') center π /
            mallowsPartition (mallowsAccuracyQ θ') center) θ :=
    hnum_cont.div hden_cont hden_ne
  exact AppliedModelingLib.epsilonContinuousAt_of_continuousAt
    (by
      simpa [concreteMallowsSpec, MallowsSpec.ofQ] using hratio)

theorem candidateRankPowerWeightedSum_zero
    {n : ℕ} (B : Candidate n → ℝ) :
    (∑ r : Candidate n, (0 : ℝ) ^ (r : ℕ) * B r) = B 0 := by
  classical
  calc
    (∑ r : Candidate n, (0 : ℝ) ^ (r : ℕ) * B r) =
        (0 : ℝ) ^ ((0 : Candidate n) : ℕ) * B 0 := by
      refine Finset.sum_eq_single
        (s := (Finset.univ : Finset (Candidate n)))
        (a := (0 : Candidate n))
        (f := fun r : Candidate n => (0 : ℝ) ^ (r : ℕ) * B r)
        ?hzero ?hnotmem
      · intro r _ hr
        have hrval_ne : (r : ℕ) ≠ 0 := by
          intro h
          exact hr (Fin.ext h)
        have hrpos : 0 < (r : ℕ) := Nat.pos_of_ne_zero hrval_ne
        have hpow : (0 : ℝ) ^ (r : ℕ) = 0 :=
          zero_pow hrval_ne
        simp [hpow]
      · intro h
        simp at h
    _ = B 0 := by
      simp

theorem candidateRankPowerSum_zero (n : ℕ) :
    candidateRankPowerSum n 0 = 1 := by
  simpa [candidateRankPowerSum] using
    (candidateRankPowerWeightedSum_zero
      (n := n) (fun _ : Candidate n => (1 : ℝ)))

theorem candidateRankWeightedAverage_zero
    {n : ℕ} (B : Candidate n → ℝ) :
    ((∑ r : Candidate n, (0 : ℝ) ^ (r : ℕ) * B r) /
        candidateRankPowerSum n 0) = B 0 := by
  rw [candidateRankPowerWeightedSum_zero, candidateRankPowerSum_zero]
  simp

theorem candidateRankWeightedAverage_continuousAt_zero
    {n : ℕ} (B : Candidate n → ℝ) :
    ContinuousAt
      (fun q =>
        (∑ r : Candidate n, q ^ (r : ℕ) * B r) /
          candidateRankPowerSum n q)
      0 := by
  classical
  have hnum :
      ContinuousAt
        (fun q => ∑ r : Candidate n, q ^ (r : ℕ) * B r) 0 :=
    AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Candidate n)))
      (f := fun r q => q ^ (r : ℕ) * B r)
      (fun r _ => (continuousAt_id.pow (r : ℕ)).mul continuousAt_const)
  have hden :
      ContinuousAt (fun q => candidateRankPowerSum n q) 0 := by
    unfold candidateRankPowerSum
    exact AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Candidate n)))
      (f := fun r q => q ^ (r : ℕ))
      (fun r _ => continuousAt_id.pow (r : ℕ))
  have hden_ne : candidateRankPowerSum n 0 ≠ 0 := by
    rw [candidateRankPowerSum_zero]
    norm_num
  exact hnum.div hden hden_ne

/-- Rank-only unnormalised weight for appearing in the second position. -/
noncomputable def candidateRankSecondChoiceWeight
    (n : ℕ) (q : ℝ) (s : Candidate n) : ℝ :=
  ∑ r : Candidate n,
    if r < s then q ^ ((r : ℕ) + (s : ℕ) - 1)
    else if s < r then q ^ ((s : ℕ) + (r : ℕ))
    else 0

theorem candidateRankSecondChoiceWeight_zero_one
    (n : ℕ) :
    candidateRankSecondChoiceWeight n 0 (1 : Candidate n) = 1 := by
  classical
  unfold candidateRankSecondChoiceWeight
  calc
    (∑ r : Candidate n,
      if r < (1 : Candidate n) then
        (0 : ℝ) ^ ((r : ℕ) + ((1 : Candidate n) : ℕ) - 1)
      else if (1 : Candidate n) < r then
        (0 : ℝ) ^ (((1 : Candidate n) : ℕ) + (r : ℕ))
      else 0) =
        (0 : ℝ) ^ (((0 : Candidate n) : ℕ) + ((1 : Candidate n) : ℕ) - 1) := by
      refine Finset.sum_eq_single
        (s := (Finset.univ : Finset (Candidate n)))
        (a := (0 : Candidate n))
        (f := fun r : Candidate n =>
          if r < (1 : Candidate n) then
            (0 : ℝ) ^ ((r : ℕ) + ((1 : Candidate n) : ℕ) - 1)
          else if (1 : Candidate n) < r then
            (0 : ℝ) ^ (((1 : Candidate n) : ℕ) + (r : ℕ))
          else 0)
        ?hzero ?hnotmem
      · intro r _ hr
        have hnot_lt : ¬r < (1 : Candidate n) := by
          intro hlt
          have hr0 : r = (0 : Candidate n) := by
            apply Fin.ext
            have hval : (r : ℕ) < 1 := hlt
            exact Nat.lt_one_iff.mp hval
          exact hr hr0
        by_cases hgt : (1 : Candidate n) < r
        · have hexp_pos : 0 < ((1 : Candidate n) : ℕ) + (r : ℕ) := by
            change 0 < 1 + (r : ℕ)
            omega
          have hpow :
              (0 : ℝ) ^ (((1 : Candidate n) : ℕ) + (r : ℕ)) = 0 :=
            zero_pow (ne_of_gt hexp_pos)
          simp [hnot_lt, hgt]
        · simp [hnot_lt, hgt]
      · intro h
        simp at h
    _ = 1 := by
      norm_num

theorem candidateRankSecondChoiceWeight_zero_of_ne_one
    {n : ℕ} {s : Candidate n} (hs : s ≠ (1 : Candidate n)) :
    candidateRankSecondChoiceWeight n 0 s = 0 := by
  classical
  unfold candidateRankSecondChoiceWeight
  apply Finset.sum_eq_zero
  intro r _
  by_cases hrs : r < s
  · have hexp_pos : 0 < (r : ℕ) + (s : ℕ) - 1 := by
      have hs_pos : 0 < (s : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hrs
      have hs_ne_one : (s : ℕ) ≠ 1 := by
        intro h
        exact hs (Fin.ext h)
      omega
    have hpow :
        (0 : ℝ) ^ ((r : ℕ) + (s : ℕ) - 1) = 0 :=
      zero_pow (ne_of_gt hexp_pos)
    simp [hrs, hpow]
  · by_cases hsr : s < r
    · have hexp_pos : 0 < (s : ℕ) + (r : ℕ) := by
        have hr_pos : 0 < (r : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hsr
        omega
      have hpow : (0 : ℝ) ^ ((s : ℕ) + (r : ℕ)) = 0 :=
        zero_pow (ne_of_gt hexp_pos)
      simp [hrs, hsr, hpow]
    · simp [hrs, hsr]

theorem candidateRankSecondChoiceWeightedSum_zero
    {n : ℕ} (B : Candidate n → ℝ) :
    (∑ s : Candidate n,
        candidateRankSecondChoiceWeight n 0 s * B s) = B 1 := by
  classical
  calc
    (∑ s : Candidate n,
        candidateRankSecondChoiceWeight n 0 s * B s) =
        candidateRankSecondChoiceWeight n 0 (1 : Candidate n) * B 1 := by
      refine Finset.sum_eq_single
        (s := (Finset.univ : Finset (Candidate n)))
        (a := (1 : Candidate n))
        (f := fun s : Candidate n =>
          candidateRankSecondChoiceWeight n 0 s * B s)
        ?hzero ?hnotmem
      · intro s _ hs
        have hw := candidateRankSecondChoiceWeight_zero_of_ne_one (n := n) hs
        simp [hw]
      · intro h
        simp at h
    _ = B 1 := by
      rw [candidateRankSecondChoiceWeight_zero_one]
      simp

theorem candidateRankRemovalPowerSum_zero (n : ℕ) (k : Candidate n) :
    candidateRankRemovalPowerSum n 0 k = 1 := by
  rw [candidateRankRemovalPowerSum_eq_range]
  calc
    (∑ m ∈ Finset.range (n + 1), (0 : ℝ) ^ m) =
        (0 : ℝ) ^ 0 := by
      refine Finset.sum_eq_single (s := Finset.range (n + 1)) (a := 0)
        (f := fun m : ℕ => (0 : ℝ) ^ m) ?hzero ?hnotmem
      · intro m hm hm0
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hpow : (0 : ℝ) ^ m = 0 := zero_pow hm0
        simpa [hpow]
      · intro h
        simp at h
    _ = 1 := by norm_num

theorem candidateRankSecondChoiceWeightedAverage_zero
    {n : ℕ} (B : Candidate n → ℝ) :
    ((∑ s : Candidate n,
        candidateRankSecondChoiceWeight n 0 s * B s) /
        (candidateRankPowerSum n 0 *
          candidateRankRemovalPowerSum n 0 (0 : Candidate n))) = B 1 := by
  rw [candidateRankSecondChoiceWeightedSum_zero,
    candidateRankPowerSum_zero, candidateRankRemovalPowerSum_zero]
  simp

theorem candidateRankSecondChoiceWeightedAverage_continuousAt_zero
    {n : ℕ} (B : Candidate n → ℝ) :
    ContinuousAt
      (fun q =>
        (∑ s : Candidate n,
          candidateRankSecondChoiceWeight n q s * B s) /
          (candidateRankPowerSum n q *
            candidateRankRemovalPowerSum n q (0 : Candidate n)))
      0 := by
  classical
  have hweight :
      ∀ s : Candidate n,
        ContinuousAt (fun q => candidateRankSecondChoiceWeight n q s) 0 := by
    intro s
    unfold candidateRankSecondChoiceWeight
    exact AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Candidate n)))
      (f := fun r q =>
        if r < s then q ^ ((r : ℕ) + (s : ℕ) - 1)
        else if s < r then q ^ ((s : ℕ) + (r : ℕ))
        else 0)
      (fun r _ => by
        by_cases hrs : r < s
        · simpa [hrs] using
            (continuousAt_id.pow ((r : ℕ) + (s : ℕ) - 1) :
              ContinuousAt
                (fun q : ℝ => q ^ ((r : ℕ) + (s : ℕ) - 1)) 0)
        · by_cases hsr : s < r
          · simpa [hrs, hsr] using
              (continuousAt_id.pow ((s : ℕ) + (r : ℕ)) :
                ContinuousAt
                  (fun q : ℝ => q ^ ((s : ℕ) + (r : ℕ))) 0)
          · simpa [hrs, hsr] using
              (continuousAt_const :
                ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0))
  have hnum :
      ContinuousAt
        (fun q =>
          ∑ s : Candidate n,
            candidateRankSecondChoiceWeight n q s * B s) 0 :=
    AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Candidate n)))
      (f := fun s q => candidateRankSecondChoiceWeight n q s * B s)
      (fun s _ => (hweight s).mul continuousAt_const)
  have hpow :
      ContinuousAt (fun q => candidateRankPowerSum n q) 0 := by
    unfold candidateRankPowerSum
    exact AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Candidate n)))
      (f := fun r q => q ^ (r : ℕ))
      (fun r _ => continuousAt_id.pow (r : ℕ))
  have hrem :
      ContinuousAt
        (fun q => candidateRankRemovalPowerSum n q (0 : Candidate n)) 0 := by
    have hfun :
        (fun q => candidateRankRemovalPowerSum n q (0 : Candidate n)) =
          (fun q => ∑ m ∈ Finset.range (n + 1), q ^ m) := by
      funext q
      rw [candidateRankRemovalPowerSum_eq_range]
    rw [hfun]
    exact AppliedModelingLib.continuousAt_finset_sum
      (s := Finset.range (n + 1))
      (f := fun m q => q ^ m)
      (fun m _ => continuousAt_id.pow m)
  have hden_ne :
      candidateRankPowerSum n 0 *
          candidateRankRemovalPowerSum n 0 (0 : Candidate n) ≠ 0 := by
    rw [candidateRankPowerSum_zero, candidateRankRemovalPowerSum_zero]
    norm_num
  exact hnum.div (hpow.mul hrem) hden_ne

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
The mixed payoff expression when the human law is fixed and the algorithm's
first-choice distribution is represented only by its center-rank power weights.
-/
noncomputable def humanAgainstRankAverage
    (value : Candidate n → ℝ) (q : ℝ) : ℝ :=
  expectedFirstMoverUtility M.law value +
    (∑ r : Candidate n,
        q ^ (r : ℕ) *
          AccuracyFamily.expectedBestAfterRemoval M.law value (M.center r)) /
      candidateRankPowerSum n q

theorem humanAgainstRankAverage_zero
    (value : Candidate n → ℝ) :
    M.humanAgainstRankAverage value 0 =
      expectedFirstMoverUtility M.law value +
        AccuracyFamily.expectedBestAfterRemoval M.law value M.centerFirst := by
  simp [humanAgainstRankAverage, candidateRankWeightedAverage_zero, centerFirst]

theorem humanAgainstRankAverage_continuousAt_zero
    (value : Candidate n → ℝ) :
    ContinuousAt (fun q => M.humanAgainstRankAverage value q) 0 := by
  unfold humanAgainstRankAverage
  exact continuousAt_const.add
    (candidateRankWeightedAverage_continuousAt_zero
      (n := n)
      (fun r : Candidate n =>
        AccuracyFamily.expectedBestAfterRemoval M.law value (M.center r)))

/--
Limit-side payoff gap for Theorem 1: if the algorithm is perfectly concentrated
on the Mallows center, then the human-against-perfect payoff is strictly below
the all-perfect payoff.  Mallows full support supplies the positive-mass swapped
ranking needed for the generic finite proof.
-/
theorem expected_human_against_pureCenter_lt_pureCenter_payoff
    (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy M.center value) :
    expectedFirstMoverUtility M.law value +
        expectedSecondMoverIndependent M.law (PMF.pure M.center) value <
      expectedFirstMoverUtility (PMF.pure M.center) value +
        expectedSecondMoverShared (PMF.pure M.center) value :=
  AccuracyFamily.expected_human_against_pureCenter_lt_pureCenter_payoff
    M.law M.center value hvalue
    (M.law_apply_toReal_pos (swapTopTwo M.center))

theorem humanAgainstRankAverage_zero_lt_pureCenter_payoff
    (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy M.center value) :
    M.humanAgainstRankAverage value 0 <
      expectedFirstMoverUtility (PMF.pure M.center) value +
        expectedSecondMoverShared (PMF.pure M.center) value := by
  rw [M.humanAgainstRankAverage_zero]
  have hsecond :
      expectedSecondMoverIndependent M.law (PMF.pure M.center) value =
        AccuracyFamily.expectedBestAfterRemoval M.law value M.centerFirst := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    simp [centerFirst]
  rw [← hsecond]
  simpa using M.expected_human_against_pureCenter_lt_pureCenter_payoff value hvalue

theorem exists_pos_radius_humanAgainstRankAverage_lt_pureCenter_payoff
    (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy M.center value) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℝ, 0 < q → q < δ →
        M.humanAgainstRankAverage value q <
          expectedFirstMoverUtility (PMF.pure M.center) value +
            expectedSecondMoverShared (PMF.pure M.center) value := by
  let purePayoff : ℝ :=
    expectedFirstMoverUtility (PMF.pure M.center) value +
      expectedSecondMoverShared (PMF.pure M.center) value
  have hcont :
      AppliedModelingLib.EpsilonContinuousAt
        (fun q => M.humanAgainstRankAverage value q) 0 :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (M.humanAgainstRankAverage_continuousAt_zero value)
  have hpure_cont :
      AppliedModelingLib.EpsilonContinuousAt (fun _ : ℝ => purePayoff) 0 :=
    AppliedModelingLib.epsilonContinuousAt_const purePayoff 0
  have hlt :
      M.humanAgainstRankAverage value 0 < purePayoff :=
    M.humanAgainstRankAverage_zero_lt_pureCenter_payoff value hvalue
  rcases AppliedModelingLib.exists_right_radius_lt_of_epsilonContinuousAt
      hcont hpure_cont hlt with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro q hq_pos hq_lt
  simpa [purePayoff] using hδ q hq_pos (by simpa using hq_lt)

/--
The all-algorithm shared-ranking payoff expressed using center-rank weights for
the first and second positions.
-/
noncomputable def sharedRankPayoffAverage
    (value : Candidate n → ℝ) (q : ℝ) : ℝ :=
  (∑ r : Candidate n, q ^ (r : ℕ) * value (M.center r)) /
      candidateRankPowerSum n q +
    (∑ s : Candidate n,
        candidateRankSecondChoiceWeight n q s * value (M.center s)) /
      (candidateRankPowerSum n q *
        candidateRankRemovalPowerSum n q (0 : Candidate n))

theorem sharedRankPayoffAverage_zero
    (value : Candidate n → ℝ) :
    M.sharedRankPayoffAverage value 0 =
      expectedFirstMoverUtility (PMF.pure M.center) value +
        expectedSecondMoverShared (PMF.pure M.center) value := by
  simp [sharedRankPayoffAverage, candidateRankWeightedAverage_zero,
    candidateRankSecondChoiceWeightedAverage_zero, expectedFirstMoverUtility,
    expectedSecondMoverShared, firstChoice, secondChoice]

theorem sharedRankPayoffAverage_continuousAt_zero
    (value : Candidate n → ℝ) :
    ContinuousAt (fun q => M.sharedRankPayoffAverage value q) 0 := by
  unfold sharedRankPayoffAverage
  exact
    (candidateRankWeightedAverage_continuousAt_zero
      (n := n) (fun r : Candidate n => value (M.center r))).add
    (candidateRankSecondChoiceWeightedAverage_continuousAt_zero
      (n := n) (fun s : Candidate n => value (M.center s)))

theorem secondChoiceProb_eq_sum_firstSecondWeight_div_partition
    (d : Candidate n) :
    secondChoiceProb M.law d =
      (∑ c : Candidate n, M.firstSecondWeight c d) / M.partition := by
  classical
  unfold secondChoiceProb pmfProb pmfExp firstSecondWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if d = secondChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if d = secondChoice π then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (∑ c : Candidate n,
            if c = firstChoice π ∧ d = secondChoice π
            then mallowsWeight M.q M.center π
            else 0) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hinner :
              (∑ c : Candidate n,
                if c = firstChoice π ∧ d = secondChoice π
                then mallowsWeight M.q M.center π
                else 0) =
                if d = secondChoice π then
                  mallowsWeight M.q M.center π
                else 0 := by
            by_cases hd : d = secondChoice π
            · simpa [hd] using
                (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                  (fun _ : Candidate n => mallowsWeight M.q M.center π))
            · have hdraw : d ≠ π 1 := by simpa [secondChoice] using hd
              simp [firstChoice, secondChoice, hdraw]
          rw [hinner]
          by_cases hd : d = secondChoice π
          · have hdraw : d = π 1 := by simpa [secondChoice] using hd
            simp [secondChoice, hdraw]
          · have hdraw : d ≠ π 1 := by simpa [secondChoice] using hd
            simp [secondChoice, hdraw]
    _ = (∑ π : Ranking n, ∑ c : Candidate n,
          if c = firstChoice π ∧ d = secondChoice π
          then mallowsWeight M.q M.center π
          else 0) / M.partition := by
          rw [Finset.sum_div]
    _ = (∑ c : Candidate n, ∑ π : Ranking n,
          if c = firstChoice π ∧ d = secondChoice π
          then mallowsWeight M.q M.center π
          else 0) / M.partition := by
          rw [Finset.sum_comm]

theorem expectedSecondMoverShared_eq_rankSecondChoiceAverage
    (fac : M.RankFactorization) (value : Candidate n → ℝ) :
    expectedSecondMoverShared M.law value =
      (∑ s : Candidate n,
          candidateRankSecondChoiceWeight n M.q s * value (M.center s)) /
        (candidateRankPowerSum n M.q *
          candidateRankRemovalPowerSum n M.q (0 : Candidate n)) := by
  classical
  rw [expectedSecondMoverShared_eq_sum_secondChoiceProb]
  have hprob :
      ∀ d : Candidate n,
        secondChoiceProb M.law d =
          (∑ c : Candidate n, M.firstSecondWeight c d) / M.partition :=
    fun d => M.secondChoiceProb_eq_sum_firstSecondWeight_div_partition d
  calc
    (∑ d : Candidate n, secondChoiceProb M.law d * value d)
        = ∑ d : Candidate n,
            ((∑ c : Candidate n, M.firstSecondWeight c d) / M.partition) *
              value d := by
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [hprob d]
    _ = (∑ d : Candidate n,
          (∑ c : Candidate n, M.firstSecondWeight c d) * value d) /
          M.partition := by
          calc
            (∑ d : Candidate n,
              (∑ c : Candidate n, M.firstSecondWeight c d) / M.partition *
                value d)
                = ∑ d : Candidate n,
                    ((∑ c : Candidate n, M.firstSecondWeight c d) *
                      value d) / M.partition := by
                    refine Finset.sum_congr rfl ?_
                    intro d _
                    ring
            _ = (∑ d : Candidate n,
                  (∑ c : Candidate n, M.firstSecondWeight c d) * value d) /
                M.partition := by
                  rw [Finset.sum_div]
    _ = (∑ s : Candidate n,
          (fac.firstSecondTail * candidateRankSecondChoiceWeight n M.q s) *
            value (M.center s)) / M.partition := by
          congr 1
          calc
            (∑ d : Candidate n,
              (∑ c : Candidate n, M.firstSecondWeight c d) * value d)
                = ∑ s : Candidate n,
                    (∑ c : Candidate n, M.firstSecondWeight c (M.center s)) *
                      value (M.center s) := by
                    simpa using
                      (Equiv.sum_comp M.center
                        (fun d : Candidate n =>
                          (∑ c : Candidate n, M.firstSecondWeight c d) *
                            value d)).symm
            _ = ∑ s : Candidate n,
                (fac.firstSecondTail * candidateRankSecondChoiceWeight n M.q s) *
                  value (M.center s) := by
                refine Finset.sum_congr rfl ?_
                intro s _
                congr 1
                unfold candidateRankSecondChoiceWeight
                calc
                  (∑ c : Candidate n, M.firstSecondWeight c (M.center s))
                      = ∑ r : Candidate n,
                          M.firstSecondWeight (M.center r) (M.center s) := by
                          simpa using
                            (Equiv.sum_comp M.center
                              (fun c : Candidate n =>
                                M.firstSecondWeight c (M.center s))).symm
                  _ = ∑ r : Candidate n,
                        fac.firstSecondTail *
                          (if r < s then M.q ^ ((r : ℕ) + (s : ℕ) - 1)
                          else if s < r then M.q ^ ((s : ℕ) + (r : ℕ))
                          else 0) := by
                        refine Finset.sum_congr rfl ?_
                        intro r _
                        by_cases hrs : r < s
                        · have hlt : rankOf M.center (M.center r) <
                              rankOf M.center (M.center s) := by
                            simpa [rankOf] using hrs
                          rw [fac.firstSecondWeight_eq_of_lt (M.center r) (M.center s) hlt]
                          simp [rankOf, hrs]
                          ring
                        · by_cases hsr : s < r
                          · have hlt : rankOf M.center (M.center s) <
                                rankOf M.center (M.center r) := by
                              simpa [rankOf] using hsr
                            rw [fac.firstSecondWeight_swap_eq_of_lt
                              (M.center s) (M.center r) hlt]
                            simp [rankOf, hrs, hsr]
                            have hsum :
                                ((s : ℕ) + (r : ℕ) - 1) + 1 =
                                  (s : ℕ) + (r : ℕ) := by
                              have hlt_nat : (s : ℕ) < (r : ℕ) := hsr
                              omega
                            rw [← mul_assoc, ← pow_succ', hsum]
                            ring
                          · have hre : r = s := le_antisymm
                              (le_of_not_gt hsr) (le_of_not_gt hrs)
                            subst r
                            rw [M.firstSecondWeight_self]
                            simp
                  _ = fac.firstSecondTail *
                        (∑ r : Candidate n,
                          if r < s then M.q ^ ((r : ℕ) + (s : ℕ) - 1)
                          else if s < r then M.q ^ ((s : ℕ) + (r : ℕ))
                          else 0) := by
                        rw [Finset.mul_sum]
    _ = (fac.firstSecondTail *
          (∑ s : Candidate n,
            candidateRankSecondChoiceWeight n M.q s * value (M.center s))) /
          M.partition := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro s _
          ring
    _ = (∑ s : Candidate n,
          candidateRankSecondChoiceWeight n M.q s * value (M.center s)) /
        (candidateRankPowerSum n M.q *
          candidateRankRemovalPowerSum n M.q (0 : Candidate n)) := by
          have hpart :
              M.partition =
                candidateRankPowerSum n M.q *
                  (fac.firstSecondTail *
                    candidateRankRemovalPowerSum n M.q (0 : Candidate n)) := by
            rw [fac.partition_eq]
            rw [M.firstTail_eq_firstSecondTail_mul_removalPowerSum fac M.centerFirst]
            simp [centerFirst, rankOf]
          rw [hpart]
          field_simp [ne_of_gt fac.firstSecondTail_pos]

/--
Appendix F / Lemma 7 in fixed-parameter Mallows form: under a strictly
center-ordered value profile, a first mover using the Mallows law has strictly
higher expected utility than an independent second mover facing another draw
from the same Mallows law.
-/
theorem firstMoverUtility_gt_secondMoverIndependent_same_of_rankFactorization
    (fac : M.RankFactorization) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy M.center value) (hq_lt_one : M.q < 1) :
    expectedSecondMoverIndependent M.law M.law value <
      expectedFirstMoverUtility M.law value := by
  classical
  let B : Candidate n → ℝ := fun r =>
    candidateRankConditionalGap n M.q
      (fun s : Candidate n => value (M.center s)) r
  have hvalue_rank :
      ∀ i j : Candidate n, i < j →
        value (M.center j) < value (M.center i) := by
    intro i j hij
    exact hvalue (by simpa [rankOf] using hij)
  have hcore_raw :
      0 < ∑ r : Candidate n,
        (M.q * M.q) ^ (r : ℕ) * B r := by
    simpa [B] using
      candidateRankSquareWeightedConditionalGap_pos n
        M.q_pos hq_lt_one hvalue_rank
  have hcore :
      0 < ∑ r : Candidate n,
        (M.q ^ (r : ℕ) * M.q ^ (r : ℕ)) * B r := by
    simpa [mul_pow, mul_assoc] using hcore_raw
  let scale : ℝ := (fac.firstTail * fac.firstSecondTail) /
    (M.partition * M.partition)
  have hscale_pos : 0 < scale :=
    div_pos (mul_pos fac.firstTail_pos fac.firstSecondTail_pos)
      (mul_pos M.partition_pos M.partition_pos)
  have hsum_eq :
      (∑ c : Candidate n,
        firstChoiceProb M.law c * firstChoiceGapMass M.law value c) =
        scale *
          ∑ r : Candidate n,
            (M.q ^ (r : ℕ) * M.q ^ (r : ℕ)) * B r := by
    let F : Candidate n → ℝ := fun c =>
      firstChoiceProb M.law c * firstChoiceGapMass M.law value c
    calc
      (∑ c : Candidate n, F c)
          = ∑ r : Candidate n, F (M.center r) := by
            simpa using
              (Equiv.sum_comp M.center (fun c : Candidate n => F c)).symm
      _ = ∑ r : Candidate n,
            scale * ((M.q ^ (r : ℕ) * M.q ^ (r : ℕ)) * B r) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            have hfirst :
                M.firstWeight (M.center r) =
                  M.q ^ (r : ℕ) * fac.firstTail := by
              rw [fac.firstWeight_eq]
              simp [rankOf]
            have hgap :
                M.firstChoiceGapWeight value (M.center r) =
                  M.q ^ (r : ℕ) * fac.firstSecondTail * B r := by
              rw [M.firstChoiceGapWeight_eq_rankConditionalGap
                fac value (M.center r)]
              simp [B, rankOf]
            have hpart_ne : M.partition ≠ 0 := ne_of_gt M.partition_pos
            simp [F, scale]
            rw [M.firstChoiceProb_eq_firstWeight_div_partition]
            rw [M.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition]
            rw [hfirst, hgap]
            field_simp [hpart_ne]
      _ = scale *
          ∑ r : Candidate n,
            (M.q ^ (r : ℕ) * M.q ^ (r : ℕ)) * B r := by
            rw [Finset.mul_sum]
  have hcollision_pos :
      0 < ∑ c : Candidate n,
        firstChoiceProb M.law c * firstChoiceGapMass M.law value c := by
    rw [hsum_eq]
    exact mul_pos hscale_pos hcore
  have hdiff :=
    expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass
      (μ := M.law) (value := value)
  linarith

/-- Unnormalised Mallows mass of rankings whose best candidate after removing
`c` is `d`. -/
noncomputable def bestAfterRemovalWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if d = bestRemainingAfter π c then mallowsWeight M.q M.center π else 0

/--
First-mover utility under a Mallows law is the rank-power weighted average of
candidate values in the center order.
-/
theorem expectedFirstMoverUtility_eq_rankAverage
    (fac : M.RankFactorization) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility M.law value =
      (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) /
        candidateRankPowerSum n M.q := by
  classical
  rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb]
  have hweight :
      (∑ c : Candidate n, M.firstWeight c * value c) =
        fac.firstTail *
          (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) := by
    calc
      ∑ c : Candidate n, M.firstWeight c * value c
          = ∑ c : Candidate n,
              (M.q ^ (rankOf M.center c : ℕ) * fac.firstTail) * value c := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [fac.firstWeight_eq c]
      _ = ∑ c : Candidate n,
              fac.firstTail * (M.q ^ (rankOf M.center c : ℕ) * value c) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            ring
      _ = fac.firstTail *
            (∑ c : Candidate n, M.q ^ (rankOf M.center c : ℕ) * value c) := by
            rw [Finset.mul_sum]
      _ = fac.firstTail *
            (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) := by
            congr 1
            simpa [rankOf] using
              (Equiv.sum_comp M.center
                (fun c : Candidate n =>
                  M.q ^ (rankOf M.center c : ℕ) * value c)).symm
  calc
    ∑ c : Candidate n, firstChoiceProb M.law c * value c
        = ∑ c : Candidate n, (M.firstWeight c / M.partition) * value c := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [M.firstChoiceProb_eq_firstWeight_div_partition c]
    _ = (∑ c : Candidate n, M.firstWeight c * value c) / M.partition := by
            calc
              ∑ c : Candidate n, (M.firstWeight c / M.partition) * value c
                  = ∑ c : Candidate n, (M.firstWeight c * value c) / M.partition := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    ring
              _ = (∑ c : Candidate n, M.firstWeight c * value c) / M.partition := by
                    rw [Finset.sum_div]
    _ = (fac.firstTail *
            (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r))) /
          (candidateRankPowerSum n M.q * fac.firstTail) := by
            rw [hweight, fac.partition_eq]
    _ = (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) /
          candidateRankPowerSum n M.q := by
            field_simp [ne_of_gt fac.firstTail_pos]

theorem shared_payoff_eq_sharedRankPayoffAverage
    (fac : M.RankFactorization) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility M.law value +
        expectedSecondMoverShared M.law value =
      M.sharedRankPayoffAverage value M.q := by
  unfold sharedRankPayoffAverage
  rw [M.expectedFirstMoverUtility_eq_rankAverage fac value]
  rw [M.expectedSecondMoverShared_eq_rankSecondChoiceAverage fac value]

theorem exists_pos_radius_humanAgainstRankAverage_lt_sharedRankPayoffAverage
    (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy M.center value) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℝ, 0 < q → q < δ →
        M.humanAgainstRankAverage value q <
          M.sharedRankPayoffAverage value q := by
  have hh_cont :
      AppliedModelingLib.EpsilonContinuousAt
        (fun q => M.humanAgainstRankAverage value q) 0 :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (M.humanAgainstRankAverage_continuousAt_zero value)
  have hs_cont :
      AppliedModelingLib.EpsilonContinuousAt
        (fun q => M.sharedRankPayoffAverage value q) 0 :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (M.sharedRankPayoffAverage_continuousAt_zero value)
  have hlt :
      M.humanAgainstRankAverage value 0 <
        M.sharedRankPayoffAverage value 0 := by
    rw [M.sharedRankPayoffAverage_zero]
    exact M.humanAgainstRankAverage_zero_lt_pureCenter_payoff value hvalue
  rcases AppliedModelingLib.exists_right_radius_lt_of_epsilonContinuousAt
      hh_cont hs_cont hlt with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro q hq_pos hq_lt
  exact hδ q hq_pos (by simpa using hq_lt)

/--
For a Mallows law, expected best-after-removal is the first-choice rank average
minus the normalized first-choice gap fiber of the removed candidate.
-/
theorem expectedBestAfterRemoval_eq_rankAverage_sub_gapWeight
    (fac : M.RankFactorization) (value : Candidate n → ℝ) (c : Candidate n) :
    AccuracyFamily.expectedBestAfterRemoval M.law value c =
      (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) /
        candidateRankPowerSum n M.q -
      M.firstChoiceGapWeight value c / M.partition := by
  rw [AccuracyFamily.expectedBestAfterRemoval_eq_firstMover_sub_firstChoiceGapMass]
  rw [M.expectedFirstMoverUtility_eq_rankAverage fac value]
  rw [M.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition value c]

/-- Expected best-after-removal as an unnormalised Mallows fiber sum. -/
theorem expectedBestAfterRemoval_eq_sum_bestAfterRemovalWeight
    (value : Candidate n → ℝ) (c : Candidate n) :
    AccuracyFamily.expectedBestAfterRemoval M.law value c =
      (∑ d : Candidate n, M.bestAfterRemovalWeight c d * value d) /
        M.partition := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval bestAfterRemovalWeight pmfExp
  calc
    ∑ π : Ranking n, (M.law π).toReal * value (bestRemainingAfter π c)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              value (bestRemainingAfter π c) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (∑ d : Candidate n,
            (if d = bestRemainingAfter π c then
              mallowsWeight M.q M.center π * value d
            else 0)) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ d : Candidate n,
                if d = bestRemainingAfter π c then
                  mallowsWeight M.q M.center π * value d
                else 0) =
                mallowsWeight M.q M.center π *
                  value (bestRemainingAfter π c) := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (bestRemainingAfter π c)
                (fun d : Candidate n => mallowsWeight M.q M.center π * value d))
          rw [hsum]
          ring
    _ = (∑ π : Ranking n, ∑ d : Candidate n,
          if d = bestRemainingAfter π c then
            mallowsWeight M.q M.center π * value d
          else 0) / M.partition := by
          rw [Finset.sum_div]
    _ = (∑ d : Candidate n, ∑ π : Ranking n,
          if d = bestRemainingAfter π c then
            mallowsWeight M.q M.center π * value d
          else 0) / M.partition := by
          rw [Finset.sum_comm]
    _ = (∑ d : Candidate n,
          M.bestAfterRemovalWeight c d * value d) / M.partition := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro d _
          unfold bestAfterRemovalWeight
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : d = bestRemainingAfter π c
          · simp [h]
          · simp [h]

/--
Best-after-removal fibers split into ordinary first-choice fibers plus the
top-two fiber where the removed candidate was first.
-/
theorem bestAfterRemovalWeight_eq_firstWeight_add_firstSecondWeight
    (c d : Candidate n) :
    M.bestAfterRemovalWeight c d =
      (if d = c then 0 else M.firstWeight d) + M.firstSecondWeight c d := by
  classical
  by_cases hdc : d = c
  · subst d
    have hbest : M.bestAfterRemovalWeight c c = 0 := by
      unfold bestAfterRemovalWeight
      apply Finset.sum_eq_zero
      intro π _
      have hne : c ≠ bestRemainingAfter π c :=
        (bestRemainingAfter_ne_removed π c).symm
      simp [hne]
    rw [hbest, if_pos rfl, M.firstSecondWeight_self c]
    ring
  · rw [if_neg hdc]
    unfold bestAfterRemovalWeight firstWeight firstSecondWeight
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro π _
    by_cases hc : firstChoice π = c
    · have hbest : bestRemainingAfter π c = secondChoice π := by
        rw [← hc]
        exact bestRemainingAfter_of_eq π
      have hdfirst : d ≠ firstChoice π := by
        intro h
        exact hdc (h.trans hc)
      have hcraw : c = π 0 := by
        simpa [firstChoice] using hc.symm
      have hdfirstRaw : d ≠ π 0 := by
        simpa [firstChoice] using hdfirst
      have hbestRaw : bestRemainingAfter π (π 0) = π 1 := by
        simpa [firstChoice, secondChoice] using bestRemainingAfter_of_eq π
      simp [firstChoice, secondChoice, hcraw, hdfirstRaw, hbestRaw]
    · have hbest : bestRemainingAfter π c = firstChoice π :=
        bestRemainingAfter_of_ne π hc
      have hc' : ¬c = firstChoice π := by
        intro h
        exact hc h.symm
      have hcraw : c ≠ π 0 := by
        simpa [firstChoice] using hc'
      simp [hbest, firstChoice, secondChoice, hcraw]

/-- Rank-factorized closed form for best-after-removal fiber weights. -/
theorem bestAfterRemovalWeight_eq_rankBestAfterRemovalWeight
    (fac : M.RankFactorization) (c d : Candidate n) :
    M.bestAfterRemovalWeight c d =
      fac.firstSecondTail *
        candidateRankBestAfterRemovalWeight n M.q
          (rankOf M.center c) (rankOf M.center d) := by
  classical
  let k : Candidate n := rankOf M.center c
  let r : Candidate n := rankOf M.center d
  have htail := M.firstTail_eq_firstSecondTail_mul_removalPowerSum fac c
  by_cases hrk : r < k
  · have hdc : d ≠ c := by
      intro hdc
      have : r = k := by
        simp [r, k, hdc]
      exact (lt_irrefl r) (hrk.trans_eq this.symm)
    have hlt : rankOf M.center d < rankOf M.center c := by
      simpa [r, k] using hrk
    rw [M.bestAfterRemovalWeight_eq_firstWeight_add_firstSecondWeight c d]
    rw [if_neg hdc]
    rw [fac.firstWeight_eq d]
    rw [fac.firstSecondWeight_swap_eq_of_lt d c hlt]
    rw [htail]
    unfold candidateRankBestAfterRemovalWeight
    have hrk' : rankOf M.center d < rankOf M.center c := hlt
    rw [if_pos hrk']
    have hpow :
        M.q * (M.q ^ ((rankOf M.center d : ℕ) + (rankOf M.center c : ℕ) - 1) *
            fac.firstSecondTail) =
          M.q ^ (rankOf M.center d : ℕ) *
              M.q ^ (rankOf M.center c : ℕ) * fac.firstSecondTail := by
      have hsum :
          ((rankOf M.center d : ℕ) + (rankOf M.center c : ℕ) - 1) + 1 =
            (rankOf M.center d : ℕ) + (rankOf M.center c : ℕ) := by
        have hlt_nat :
            (rankOf M.center d : ℕ) < (rankOf M.center c : ℕ) := hlt
        omega
      rw [← mul_assoc M.q
        (M.q ^ ((rankOf M.center d : ℕ) + (rankOf M.center c : ℕ) - 1))
        fac.firstSecondTail]
      rw [← pow_succ', hsum, pow_add]
    rw [hpow]
    ring
  · by_cases hkr : k < r
    · have hdc : d ≠ c := by
        intro hdc
        have : r = k := by
          simp [r, k, hdc]
        exact (lt_irrefl k) (hkr.trans_eq this)
      have hlt : rankOf M.center c < rankOf M.center d := by
        simpa [r, k] using hkr
      rw [M.bestAfterRemovalWeight_eq_firstWeight_add_firstSecondWeight c d]
      rw [if_neg hdc]
      rw [fac.firstWeight_eq d]
      rw [fac.firstSecondWeight_eq_of_lt c d hlt]
      rw [htail]
      unfold candidateRankBestAfterRemovalWeight
      have hrk' : ¬rankOf M.center d < rankOf M.center c := by
        simpa [r, k] using hrk
      rw [if_neg hrk', if_pos hlt]
      ring
    · have hr_eq : r = k := le_antisymm (le_of_not_gt hkr) (le_of_not_gt hrk)
      have hdc : d = c := by
        have : rankOf M.center d = rankOf M.center c := by
          simpa [r, k] using hr_eq
        exact M.center.injective (by
          simpa [rankOf] using congrArg M.center this)
      subst d
      rw [M.bestAfterRemovalWeight_eq_firstWeight_add_firstSecondWeight c c]
      rw [if_pos rfl, M.firstSecondWeight_self c]
      unfold candidateRankBestAfterRemovalWeight
      simp

/-- Expected best-after-removal as a pure rank-weighted average. -/
theorem expectedBestAfterRemoval_eq_rankBestAfterRemovalAverage
    (fac : M.RankFactorization) (value : Candidate n → ℝ) (c : Candidate n) :
    AccuracyFamily.expectedBestAfterRemoval M.law value c =
      (∑ r : Candidate n,
          candidateRankBestAfterRemovalWeight n M.q
            (rankOf M.center c) r * value (M.center r)) /
        (candidateRankPowerSum n M.q *
          candidateRankRemovalPowerSum n M.q (rankOf M.center c)) := by
  classical
  rw [M.expectedBestAfterRemoval_eq_sum_bestAfterRemovalWeight value c]
  have hnum :
      (∑ d : Candidate n, M.bestAfterRemovalWeight c d * value d) =
        fac.firstSecondTail *
          (∑ r : Candidate n,
            candidateRankBestAfterRemovalWeight n M.q
              (rankOf M.center c) r * value (M.center r)) := by
    calc
      (∑ d : Candidate n, M.bestAfterRemovalWeight c d * value d)
          = ∑ r : Candidate n,
              M.bestAfterRemovalWeight c (M.center r) *
                value (M.center r) := by
            simpa using
              (Equiv.sum_comp M.center
                (fun d : Candidate n => M.bestAfterRemovalWeight c d * value d)).symm
      _ = ∑ r : Candidate n,
            (fac.firstSecondTail *
              candidateRankBestAfterRemovalWeight n M.q
                (rankOf M.center c) r) * value (M.center r) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [M.bestAfterRemovalWeight_eq_rankBestAfterRemovalWeight fac c (M.center r)]
            simp [rankOf]
      _ = fac.firstSecondTail *
            (∑ r : Candidate n,
              candidateRankBestAfterRemovalWeight n M.q
                (rankOf M.center c) r * value (M.center r)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro r _
            ring
  have hpart :
      M.partition =
        candidateRankPowerSum n M.q *
          (fac.firstSecondTail *
            candidateRankRemovalPowerSum n M.q (rankOf M.center c)) := by
    rw [fac.partition_eq]
    rw [M.firstTail_eq_firstSecondTail_mul_removalPowerSum fac c]
  rw [hnum, hpart]
  field_simp [ne_of_gt fac.firstSecondTail_pos]

/-- The rank-only best-after-removal weights have the expected denominator. -/
theorem sum_rankBestAfterRemovalWeight_eq
    (fac : M.RankFactorization) (c : Candidate n) :
    (∑ r : Candidate n,
      candidateRankBestAfterRemovalWeight n M.q (rankOf M.center c) r) =
      candidateRankPowerSum n M.q *
        candidateRankRemovalPowerSum n M.q (rankOf M.center c) := by
  have h :=
    M.expectedBestAfterRemoval_eq_rankBestAfterRemovalAverage
      fac (fun _ : Candidate n => (1 : ℝ)) c
  have hleft :
      AccuracyFamily.expectedBestAfterRemoval M.law
          (fun _ : Candidate n => (1 : ℝ)) c = 1 := by
    simp [AccuracyFamily.expectedBestAfterRemoval]
  rw [hleft] at h
  simp only [mul_one] at h
  have hden_pos :
      0 <
        candidateRankPowerSum n M.q *
          candidateRankRemovalPowerSum n M.q (rankOf M.center c) :=
    mul_pos (candidateRankPowerSum_pos n M.q_pos)
      (candidateRankRemovalPowerSum_pos n M.q_pos (rankOf M.center c))
  have hden_ne :
      candidateRankPowerSum n M.q *
          candidateRankRemovalPowerSum n M.q (rankOf M.center c) ≠ 0 :=
    ne_of_gt hden_pos
  have hfrac :
      (∑ r : Candidate n,
        candidateRankBestAfterRemovalWeight n M.q (rankOf M.center c) r) /
        (candidateRankPowerSum n M.q *
          candidateRankRemovalPowerSum n M.q (rankOf M.center c)) = 1 := h.symm
  have hsum := (div_eq_iff hden_ne).mp hfrac
  simpa using hsum

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/--
The mixed payoff `g` with a fixed Mallows human law depends on the algorithm law
only through the algorithm's rank-power first-choice distribution.
-/
theorem theorem1_g_eq_humanAgainstRankAverage
    (facA : C.algorithm.RankFactorization) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility C.human.law value +
        expectedSecondMoverIndependent C.human.law C.algorithm.law value =
      C.human.humanAgainstRankAverage value C.algorithm.q := by
  classical
  rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
  unfold MallowsSpec.humanAgainstRankAverage
  congr 1
  let B : Candidate n → ℝ :=
    fun c => AccuracyFamily.expectedBestAfterRemoval C.human.law value c
  have h :=
    C.algorithm.expectedFirstMoverUtility_eq_rankAverage facA B
  rw [← C.same_center]
  simpa [expectedFirstMoverUtility, B] using h

theorem first_dominance_of_algorithm_q_small
    (facA : C.algorithm.RankFactorization)
    (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy C.human.center value) :
    ∃ δ : ℝ, 0 < δ ∧
      (C.algorithm.q < δ →
        expectedFirstMoverUtility C.human.law value +
            expectedSecondMoverIndependent C.human.law C.algorithm.law value <
          expectedFirstMoverUtility C.algorithm.law value +
            expectedSecondMoverShared C.algorithm.law value) := by
  rcases C.human.exists_pos_radius_humanAgainstRankAverage_lt_sharedRankPayoffAverage
      value hvalue with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro hq_lt
  have hrank :
      C.human.humanAgainstRankAverage value C.algorithm.q <
        C.human.sharedRankPayoffAverage value C.algorithm.q :=
    hδ C.algorithm.q C.algorithm.q_pos hq_lt
  have hg :=
    C.theorem1_g_eq_humanAgainstRankAverage facA value
  have hf :=
    C.algorithm.shared_payoff_eq_sharedRankPayoffAverage
      C.algorithm.rankFactorization value
  have hshared :
      C.algorithm.sharedRankPayoffAverage value C.algorithm.q =
        C.human.sharedRankPayoffAverage value C.algorithm.q := by
    simp [MallowsSpec.sharedRankPayoffAverage, C.same_center]
  calc
    expectedFirstMoverUtility C.human.law value +
        expectedSecondMoverIndependent C.human.law C.algorithm.law value
        = C.human.humanAgainstRankAverage value C.algorithm.q := hg
    _ < C.human.sharedRankPayoffAverage value C.algorithm.q := hrank
    _ = C.algorithm.sharedRankPayoffAverage value C.algorithm.q := hshared.symm
    _ = expectedFirstMoverUtility C.algorithm.law value +
        expectedSecondMoverShared C.algorithm.law value := hf.symm

/--
If the rank-only best-after-removal weights satisfy pairwise cross-ratio
dominance, then the actual Mallows best-after-removal expectation is weakly
higher under the algorithm/lower-`q` law.
-/
theorem expectedBestAfterRemoval_le_of_rankBestAfterRemoval_pairwise
    {value : Candidate n → ℝ} (c : Candidate n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hvalue : C.StrictlyCenterOrdered value)
    (hpair :
      ∀ i j : Candidate n, i < j →
        0 ≤
          candidateRankBestAfterRemovalWeight n C.algorithm.q
              (rankOf C.human.center c) i *
            candidateRankBestAfterRemovalWeight n C.human.q
              (rankOf C.human.center c) j -
          candidateRankBestAfterRemovalWeight n C.algorithm.q
              (rankOf C.human.center c) j *
            candidateRankBestAfterRemovalWeight n C.human.q
              (rankOf C.human.center c) i) :
    AccuracyFamily.expectedBestAfterRemoval C.human.law value c ≤
      AccuracyFamily.expectedBestAfterRemoval C.algorithm.law value c := by
  classical
  let k : Candidate n := rankOf C.human.center c
  let wA : Candidate n → ℝ := fun r =>
    candidateRankBestAfterRemovalWeight n C.algorithm.q k r
  let wH : Candidate n → ℝ := fun r =>
    candidateRankBestAfterRemovalWeight n C.human.q k r
  let B : Candidate n → ℝ := fun r => value (C.human.center r)
  have hB : ∀ i j : Candidate n, i < j → B j ≤ B i := by
    intro i j hij
    exact le_of_lt (hvalue (by simpa [B, rankOf, C.same_center] using hij))
  have hcross :
      0 ≤
        (∑ j : Candidate n, wH j) *
            (∑ i : Candidate n, wA i * B i) -
          (∑ j : Candidate n, wA j) *
            (∑ i : Candidate n, wH i * B i) :=
    candidateWeightedAverage_cross_nonneg_of_pairwise n
      (wA := wA) (wH := wH) (B := B)
      (by
        intro i j hij
        simpa [wA, wH, k] using hpair i j hij)
      hB
  have hdenA_pos :
      0 < ∑ r : Candidate n, wA r := by
    change 0 <
      ∑ r : Candidate n,
        candidateRankBestAfterRemovalWeight n C.algorithm.q k r
    have hsum := C.algorithm.sum_rankBestAfterRemovalWeight_eq
      halg_rank (C.algorithm.center k)
    simp [rankOf] at hsum
    rw [hsum]
    exact mul_pos (candidateRankPowerSum_pos n C.algorithm.q_pos)
      (candidateRankRemovalPowerSum_pos n C.algorithm.q_pos k)
  have hdenH_pos :
      0 < ∑ r : Candidate n, wH r := by
    change 0 <
      ∑ r : Candidate n,
        candidateRankBestAfterRemovalWeight n C.human.q k r
    rw [C.human.sum_rankBestAfterRemovalWeight_eq hhuman_rank c]
    exact mul_pos (candidateRankPowerSum_pos n C.human.q_pos)
      (candidateRankRemovalPowerSum_pos n C.human.q_pos k)
  rw [C.algorithm.expectedBestAfterRemoval_eq_rankBestAfterRemovalAverage
    halg_rank value c]
  rw [C.human.expectedBestAfterRemoval_eq_rankBestAfterRemovalAverage
    hhuman_rank value c]
  have halg_den :
      candidateRankPowerSum n C.algorithm.q *
          candidateRankRemovalPowerSum n C.algorithm.q
            (rankOf C.algorithm.center c) =
        ∑ r : Candidate n, wA r := by
    have hk_alg : rankOf C.algorithm.center c = k := by
      simp [k, rankOf, C.same_center]
    rw [hk_alg]
    change candidateRankPowerSum n C.algorithm.q *
        candidateRankRemovalPowerSum n C.algorithm.q k =
      ∑ r : Candidate n,
        candidateRankBestAfterRemovalWeight n C.algorithm.q k r
    have hsum := C.algorithm.sum_rankBestAfterRemovalWeight_eq
      halg_rank (C.algorithm.center k)
    simp [rankOf] at hsum
    exact hsum.symm
  have hhuman_den :
      candidateRankPowerSum n C.human.q *
          candidateRankRemovalPowerSum n C.human.q
            (rankOf C.human.center c) =
        ∑ r : Candidate n, wH r := by
    rw [C.human.sum_rankBestAfterRemovalWeight_eq hhuman_rank c]
  have halg_num :
      (∑ r : Candidate n,
        candidateRankBestAfterRemovalWeight n C.algorithm.q
            (rankOf C.algorithm.center c) r *
          value (C.algorithm.center r)) =
        ∑ r : Candidate n, wA r * B r := by
    refine Finset.sum_congr rfl ?_
    intro r _
    simp [wA, B, k, C.same_center]
  have hhuman_num :
      (∑ r : Candidate n,
        candidateRankBestAfterRemovalWeight n C.human.q
            (rankOf C.human.center c) r *
          value (C.human.center r)) =
        ∑ r : Candidate n, wH r * B r := by
    rfl
  rw [halg_den, hhuman_den, halg_num, hhuman_num]
  exact AppliedModelingLib.PositiveDenominator.div_le_div_of_cross_mul_le
    hdenH_pos hdenA_pos (by linarith)

/--
The rank-only best-after-removal MLR inequality proves singleton-removal
monotonicity for rank-factorized Mallows comparisons.
-/
theorem expectedBestAfterRemoval_le_of_rankFactorization
    {value : Candidate n → ℝ} (c : Candidate n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hvalue : C.StrictlyCenterOrdered value)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1) :
    AccuracyFamily.expectedBestAfterRemoval C.human.law value c ≤
      AccuracyFamily.expectedBestAfterRemoval C.algorithm.law value c :=
   C.expectedBestAfterRemoval_le_of_rankBestAfterRemoval_pairwise
    c halg_rank hhuman_rank hvalue
    (candidateRankBestAfterRemovalWeight_pairwise_cross_nonneg
      n C.algorithm.q_pos hq_lt hhuman_q_lt_one (rankOf C.human.center c))

/--
The Mallows rank-power MLR inequality proves the strict `S = ∅` part of
Definition 1 monotonicity: the more concentrated/lower-`q` law has higher
expected first choice when values strictly decrease down the common center.
-/
theorem firstMoverUtility_strict_of_rankFactorization
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    expectedFirstMoverUtility C.human.law value <
      expectedFirstMoverUtility C.algorithm.law value := by
  classical
  let A : ℝ :=
    ∑ r : Candidate n, C.algorithm.q ^ (r : ℕ) * value (C.human.center r)
  let H : ℝ :=
    ∑ r : Candidate n, C.human.q ^ (r : ℕ) * value (C.human.center r)
  let SA : ℝ := candidateRankPowerSum n C.algorithm.q
  let SH : ℝ := candidateRankPowerSum n C.human.q
  have hB : StrictAnti (fun r : Candidate n => value (C.human.center r)) := by
    intro i j hij
    exact hstrict (by
      simpa [MallowsComparison.StrictlyCenterOrdered, rankOf, C.same_center] using hij)
  have hmain : 0 < SH * A - SA * H := by
    simpa [A, H, SA, SH] using
      candidateRankWeightedAverage_strictAnti
        n C.algorithm.q_pos hq_lt hB
  have hSA_pos : 0 < SA :=
    candidateRankPowerSum_pos n C.algorithm.q_pos
  have hSH_pos : 0 < SH :=
    candidateRankPowerSum_pos n C.human.q_pos
  have havg : H / SH < A / SA := by
    field_simp [ne_of_gt hSA_pos, ne_of_gt hSH_pos]
    nlinarith [hmain]
  rw [C.algorithm.expectedFirstMoverUtility_eq_rankAverage halg_rank value]
  rw [C.human.expectedFirstMoverUtility_eq_rankAverage hhuman_rank value]
  have halg_sum :
      (∑ r : Candidate n,
        C.algorithm.q ^ (r : ℕ) * value (C.algorithm.center r)) = A := by
    simp [A, C.same_center]
  have hhuman_sum :
      (∑ r : Candidate n,
        C.human.q ^ (r : ℕ) * value (C.human.center r)) = H := by
    simp [H]
  simpa [halg_sum, hhuman_sum, SA, SH] using havg

end MallowsComparison

theorem concreteMallowsSpec_asymptotic_first_dominance
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    ∀ θH lower, 0 < θH → θH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun θ => (concreteMallowsSpec center θ).law,
                value := value } : AccuracyFamily n)
            hi θH <
          AccuracyFamily.theorem1_f
            ({ dist := fun θ => (concreteMallowsSpec center θ).law,
                value := value } : AccuracyFamily n)
            hi θH := by
  intro θH lower hθH hθH_lower
  let human : MallowsSpec n := concreteMallowsSpec center θH
  let baseC : ℝ → MallowsComparison n := fun θA =>
    { algorithm := concreteMallowsSpec center θA
      human := human
      same_center := by simp [human, concreteMallowsSpec, MallowsSpec.ofQ] }
  have hhuman_value : StrictlyOrderedBy human.center value := by
    intro a b hab
    exact hvalue (by
      simpa [human, concreteMallowsSpec, MallowsSpec.ofQ] using hab)
  rcases human.exists_pos_radius_humanAgainstRankAverage_lt_sharedRankPayoffAverage
      value hhuman_value with ⟨δ, hδ_pos, hδ⟩
  rcases exists_gt_mallowsAccuracyQ_lt lower δ hδ_pos with ⟨hi, hhi_lower, hq_hi⟩
  refine ⟨hi, hhi_lower, ?_⟩
  let C := baseC hi
  have hsmall : C.algorithm.q < δ := by
    simpa [C, baseC, concreteMallowsSpec, MallowsSpec.ofQ] using hq_hi
  have hrank :
      C.human.humanAgainstRankAverage value C.algorithm.q <
        C.human.sharedRankPayoffAverage value C.algorithm.q :=
    hδ C.algorithm.q C.algorithm.q_pos hsmall
  have hineq :
      expectedFirstMoverUtility C.human.law value +
          expectedSecondMoverIndependent C.human.law C.algorithm.law value <
        expectedFirstMoverUtility C.algorithm.law value +
          expectedSecondMoverShared C.algorithm.law value := by
    have hg := C.theorem1_g_eq_humanAgainstRankAverage
      C.algorithm.rankFactorization value
    have hf := C.algorithm.shared_payoff_eq_sharedRankPayoffAverage
      C.algorithm.rankFactorization value
    have hshared :
        C.algorithm.sharedRankPayoffAverage value C.algorithm.q =
          C.human.sharedRankPayoffAverage value C.algorithm.q := by
      simp [MallowsSpec.sharedRankPayoffAverage, C, baseC, human,
        concreteMallowsSpec, MallowsSpec.ofQ]
    calc
      expectedFirstMoverUtility C.human.law value +
          expectedSecondMoverIndependent C.human.law C.algorithm.law value
          = C.human.humanAgainstRankAverage value C.algorithm.q := hg
      _ < C.human.sharedRankPayoffAverage value C.algorithm.q := hrank
      _ = C.algorithm.sharedRankPayoffAverage value C.algorithm.q := hshared.symm
      _ = expectedFirstMoverUtility C.algorithm.law value +
          expectedSecondMoverShared C.algorithm.law value := hf.symm
  simpa [AccuracyFamily.theorem1_g, AccuracyFamily.theorem1_f,
    AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist, C, baseC, human] using hineq

/--
A one-parameter Mallows accuracy family with a common center ranking and a fixed
value vector.

The finite Mallows algebra in `MallowsPairwise` proves Definitions 2 and 3 from
the common-center ordering and `qA < qH`.  The fields here that remain are the
Definition 1 analytic/family facts used by Theorem 1: atomwise continuity and
asymptotic first-dominance in the proof's payoff notation.  The strict `S = ∅`
first-mover monotonicity and singleton-removal weak monotonicity are proved
below from Mallows rank-power MLR inequalities.
-/
structure MallowsAccuracyFamilySpec (n : ℕ) where
  value : Candidate n → ℝ
  center : Ranking n
  value_strict : StrictlyOrderedBy center value
  spec : ℝ → MallowsSpec n
  same_center : ∀ θ, (spec θ).center = center
  q_lt_one : ∀ θ, 0 < θ → (spec θ).q < 1
  q_strictAnti : ∀ θA θH, 0 < θH → θH < θA → (spec θA).q < (spec θH).q
  dist_atom_continuity :
    ∀ θ, 0 < θ →
      ∀ π : Ranking n, AppliedModelingLib.EpsilonContinuousAt
        (fun θ' => (((spec θ').law) π).toReal) θ
  asymptotic_first_dominance :
    ∀ θH lower, 0 < θH → θH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun θ => (spec θ).law, value := value } : AccuracyFamily n)
            hi θH <
          AccuracyFamily.theorem1_f
            ({ dist := fun θ => (spec θ).law, value := value } : AccuracyFamily n)
            hi θH

namespace MallowsAccuracyFamilySpec

variable {n : ℕ} (MF : MallowsAccuracyFamilySpec n)

/-- The `AccuracyFamily` induced by a parameterized Mallows family. -/
noncomputable def toAccuracyFamily : AccuracyFamily n where
  dist := fun θ => (MF.spec θ).law
  value := MF.value

/-- The fixed-parameter Mallows comparison induced by two accuracy parameters. -/
noncomputable def comparisonAt (θA θH : ℝ) : MallowsComparison n where
  algorithm := MF.spec θA
  human := MF.spec θH
  same_center := by
    rw [MF.same_center θA, MF.same_center θH]

@[simp] theorem comparisonAt_toModel (θA θH : ℝ) :
    (MF.comparisonAt θA θH).toModel MF.value =
      (MF.toAccuracyFamily).modelAt θA θH := by
  rfl

/-- The common center ordering gives the fixed-parameter Mallows ordering field. -/
theorem comparisonAt_strictlyCenterOrdered (θA θH : ℝ) :
    (MF.comparisonAt θA θH).StrictlyCenterOrdered MF.value := by
  unfold MallowsComparison.StrictlyCenterOrdered StrictlyOrderedBy
  intro a b h
  exact MF.value_strict (by
    simpa [comparisonAt, MF.same_center θA] using h)

/--
Mallows finite-sum algebra proves Definition 2 at every positive parameter.
-/
theorem prefersIndependentReranking
    (hn : 0 < n) (θ : ℝ) (hθ : 0 < θ) :
    Model.PrefersIndependentReranking ((MF.toAccuracyFamily).dist θ) MF.value := by
  let M := MF.spec θ
  have hvalue : StrictlyOrderedBy M.center MF.value := by
    intro a b h
    exact MF.value_strict (by
      simpa [M, MF.same_center θ] using h)
  have hcleared :
      0 < ∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight MF.value c :=
    M.independent_weight_sum_pos_of_rankFactorization
      M.rankFactorization hn (MF.q_lt_one θ hθ) hvalue
  have hsum :
      0 < ∑ c : Candidate n,
        firstChoiceMissProb M.law c * firstChoiceGapMass M.law MF.value c :=
    M.firstChoice_miss_gap_sum_pos_of_weight_sum_pos hcleared
  exact (prefersIndependentReranking_iff_firstChoiceGapMassSum_pos
    (μ := M.law) (value := MF.value)).2 hsum

/--
The rank-factorized Mallows theorem proves Definition 3 for every
`θA > θH > 0`.
-/
theorem prefersWeakerCompetition
    (hn : 0 < n) (θA θH : ℝ) (hθH : 0 < θH) (hθ : θH < θA) :
    Model.PrefersWeakerCompetition
      ((MF.toAccuracyFamily).dist θA) ((MF.toAccuracyFamily).dist θH) MF.value := by
  let C := MF.comparisonAt θA θH
  have hstrict : C.StrictlyCenterOrdered MF.value := by
    intro a b h
    exact (MF.comparisonAt_strictlyCenterOrdered θA θH)
      (by simpa [C] using h)
  have hpaper : Model.PaperHypotheses (C.toModel MF.value) :=
    C.theorem3_pointwise_of_rankFactorization
      hstrict
      hn
      C.algorithm.rankFactorization
      C.human.rankFactorization
      (MF.q_lt_one θA (lt_trans hθH hθ))
      (MF.q_lt_one θH hθH)
      (MF.q_strictAnti θA θH hθH hθ)
  simpa [C, toAccuracyFamily, comparisonAt] using hpaper.2

/--
Mallows rank-power MLR proves the strict first-mover part of Definition 1
monotonicity for every `θA > θH > 0`.
-/
theorem firstMoverUtility_strict
    (hn : 0 < n) (θA θH : ℝ) (hθH : 0 < θH) (hθ : θH < θA) :
    expectedFirstMoverUtility (MF.spec θH).law MF.value <
      expectedFirstMoverUtility (MF.spec θA).law MF.value := by
  let C := MF.comparisonAt θA θH
  have hstrict : C.StrictlyCenterOrdered MF.value := by
    intro a b h
    exact (MF.comparisonAt_strictlyCenterOrdered θA θH)
      (by simpa [C] using h)
  have hmain := C.firstMoverUtility_strict_of_rankFactorization
    hstrict
    C.algorithm.rankFactorization
    C.human.rankFactorization
    (MF.q_strictAnti θA θH hθH hθ)
  simpa [C, comparisonAt] using hmain

/--
The proved Mallows first-mover and singleton-removal MLR inequalities give the
Theorem 1 removal monotonicity certificate.
-/
theorem theorem1RemovalMonotonicityAt
    (hn : 0 < n) (θA θH : ℝ) (hθH : 0 < θH) (hθ : θH < θA) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt MF.toAccuracyFamily θA θH where
  firstMover_strict := by
    simpa [toAccuracyFamily] using
      MF.firstMoverUtility_strict hn θA θH hθH hθ
  bestRemaining_weak := by
    intro c
    let C := MF.comparisonAt θA θH
    have hstrict : C.StrictlyCenterOrdered MF.value := by
      intro a b h
      exact (MF.comparisonAt_strictlyCenterOrdered θA θH)
        (by simpa [C] using h)
    have hmain := C.expectedBestAfterRemoval_le_of_rankFactorization
      c
      C.algorithm.rankFactorization
      C.human.rankFactorization
      hstrict
      (MF.q_strictAnti θA θH hθH hθ)
      (MF.q_lt_one θH hθH)
    simpa [C, comparisonAt, toAccuracyFamily] using hmain

/--
The parameterized Mallows fields instantiate the paper-level assumptions for
Theorem 1. Definitions 2 and 3 are filled by the proved finite Mallows route;
the remaining fields are exactly the analytic obligations recorded in
`MallowsAccuracyFamilySpec`.
-/
noncomputable def theorem1PaperAssumptions
    (hn : 0 < n) :
    AccuracyFamily.Theorem1PaperAssumptions MF.toAccuracyFamily where
  prefers_independent := fun θ hθ =>
    MF.prefersIndependentReranking hn θ hθ
  prefers_weaker_competition := fun θA θH hθH hθ =>
    MF.prefersWeakerCompetition hn θA θH hθH hθ
  dist_atom_continuity := fun θ hθ π => by
    simpa [toAccuracyFamily] using MF.dist_atom_continuity θ hθ π
  asymptotic_first_dominance := fun θH lower hθH hθ =>
    MF.asymptotic_first_dominance θH lower hθH hθ
  removal_monotonicity := fun θA θH hθH hθ =>
    MF.theorem1RemovalMonotonicityAt hn θA θH hθH hθ

/--
Family-level Mallows Theorem 1 bridge.
-/
theorem theorem1Target
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target MF.toAccuracyFamily θH :=
  AccuracyFamily.theorem1Target_of_paperAssumptions
    hθH (MF.theorem1PaperAssumptions hn)

end MallowsAccuracyFamilySpec

/--
The concrete Mallows family for the paper's `θ = φ - 1` convention satisfies
all finite Definition 1 fields used by Theorem 1.
-/
noncomputable def concreteMallowsAccuracyFamilySpec
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    MallowsAccuracyFamilySpec n where
  value := value
  center := center
  value_strict := hvalue
  spec := concreteMallowsSpec center
  same_center := by
    intro θ
    simp [concreteMallowsSpec, MallowsSpec.ofQ]
  q_lt_one := by
    intro θ hθ
    simpa [concreteMallowsSpec, MallowsSpec.ofQ] using
      mallowsAccuracyQ_lt_one hθ
  q_strictAnti := by
    intro θA θH hθH hθ
    simpa [concreteMallowsSpec, MallowsSpec.ofQ] using
      mallowsAccuracyQ_strictAnti hθH hθ
  dist_atom_continuity := by
    intro θ hθ π
    simpa [concreteMallowsSpec] using
      concreteMallowsSpec_atom_continuity center hθ π
  asymptotic_first_dominance :=
    concreteMallowsSpec_asymptotic_first_dominance center value hvalue

theorem concreteMallows_theorem1Target
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue))
      θH :=
  (concreteMallowsAccuracyFamilySpec center value hvalue).theorem1Target
    hn θH hθH

end KR21Monoculture

import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.Foundations.Math.PositiveDenominator
import AppliedModelingLib.SocialChoice.Ranking.Mallows
import AppliedModelingLib.SocialChoice.Ranking.SequentialPayoff

/-!
# Mallows Best-in-Set Payoffs

Paper-neutral finite-sum identities for the candidate selected by a Mallows
ranking law from a remaining feasible set.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

theorem expectedBestInSet_pair_eq_pairCorrectProb
    (value : Candidate n → ℝ) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    expectedBestInSet M.law value ({c, d} : Finset (Candidate n)) =
      M.pairCorrectProb c d * value c +
        (1 - M.pairCorrectProb c d) * value d := by
  classical
  have hne : c ≠ d := by
    intro h
    rw [h] at hcd
    exact (lt_irrefl _) hcd
  unfold expectedBestInSet
  refine
    pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
      M.law
      (fun π : Ranking n =>
        rankOf M.center c < rankOf M.center d ∧
          rankOf π c < rankOf π d)
      (fun π : Ranking n =>
        value (bestInSet π ({c, d} : Finset (Candidate n))))
      (value c) (value d) ?_
  intro π
  change
    value (bestInSet π ({c, d} : Finset (Candidate n))) =
      if rankOf M.center c < rankOf M.center d ∧ rankOf π c < rankOf π d
      then value c else value d
  rw [bestInSet_pair_eq_if_rank_lt π hne]
  by_cases hπ : rankOf π c < rankOf π d
  · simp [hcd, hπ]
  · simp [hcd, hπ]

theorem expectedBestInSet_pair_le_of_pairCorrectProb_le
    {Mmore Mless : MallowsSpec n} (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hcd : rankOf Mmore.center c < rankOf Mmore.center d)
    (hvalue : WeaklyOrderedBy Mmore.center value)
    (hprob : Mless.pairCorrectProb c d ≤ Mmore.pairCorrectProb c d) :
    expectedBestInSet Mless.law value ({c, d} : Finset (Candidate n)) ≤
      expectedBestInSet Mmore.law value ({c, d} : Finset (Candidate n)) := by
  classical
  have hcd_less : rankOf Mless.center c < rankOf Mless.center d := by
    simpa [← hcenter] using hcd
  rw [Mless.expectedBestInSet_pair_eq_pairCorrectProb value hcd_less,
    Mmore.expectedBestInSet_pair_eq_pairCorrectProb value hcd]
  have hgap : 0 ≤ value c - value d := by
    have hv := hvalue hcd
    linarith
  nlinarith

theorem expectedBestInSet_pair_lt_of_pairCorrectProb_lt
    {Mmore Mless : MallowsSpec n} (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hcd : rankOf Mmore.center c < rankOf Mmore.center d)
    (hvalue : StrictlyOrderedBy Mmore.center value)
    (hprob : Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d) :
    expectedBestInSet Mless.law value ({c, d} : Finset (Candidate n)) <
      expectedBestInSet Mmore.law value ({c, d} : Finset (Candidate n)) := by
  classical
  have hcd_less : rankOf Mless.center c < rankOf Mless.center d := by
    simpa [← hcenter] using hcd
  rw [Mless.expectedBestInSet_pair_eq_pairCorrectProb value hcd_less,
    Mmore.expectedBestInSet_pair_eq_pairCorrectProb value hcd]
  have hgap : 0 < value c - value d := by
    have hv := hvalue hcd
    linarith
  nlinarith

/-- Unnormalized Mallows weight of rankings whose best candidate in `remaining`
is `c`. -/
def bestInSetWeight
    (remaining : Finset (Candidate n)) (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = bestInSet π remaining then mallowsWeight M.q M.center π else 0

/-- On a center-ordered pair, the better candidate's best-in-set fiber is the
usual pair-correct Mallows weight. -/
theorem bestInSetWeight_pair_eq_pairCorrectWeight
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.bestInSetWeight ({c, d} : Finset (Candidate n)) c =
      M.pairCorrectWeight c d := by
  classical
  have hne : c ≠ d := by
    intro h
    rw [h] at hcd
    exact (lt_irrefl _) hcd
  unfold bestInSetWeight pairCorrectWeight
  refine Finset.sum_congr rfl ?_
  intro π _
  rw [bestInSet_pair_eq_if_rank_lt π hne]
  by_cases hπ : rankOf π c < rankOf π d
  · simp [hcd, hπ]
  · simp [hcd, hπ, hne]

/-- On a center-ordered pair, the worse candidate's best-in-set fiber is the
usual pair-wrong Mallows weight. -/
theorem bestInSetWeight_pair_eq_pairWrongWeight
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.bestInSetWeight ({c, d} : Finset (Candidate n)) d =
      M.pairWrongWeight c d := by
  classical
  have hne : c ≠ d := by
    intro h
    rw [h] at hcd
    exact (lt_irrefl _) hcd
  unfold bestInSetWeight pairWrongWeight
  refine Finset.sum_congr rfl ?_
  intro π _
  rw [bestInSet_pair_eq_if_rank_lt π hne]
  by_cases hπ : rankOf π c < rankOf π d
  · have hnot : ¬ rankOf π d < rankOf π c := not_lt_of_gt hπ
    simp [hcd, hπ, hne.symm, hnot]
  · have hdc : rankOf π d < rankOf π c := by
      have hle : rankOf π d ≤ rankOf π c := le_of_not_gt hπ
      have hrank_ne : rankOf π d ≠ rankOf π c := by
        intro hrank
        exact hne (by
          simpa [rankOf] using congrArg π hrank.symm)
      exact lt_of_le_of_ne hle hrank_ne
    simp [hcd, hπ, hdc]

/--
Reindex a best-in-set fiber by swapping two remaining candidates.  This is the
finite-sum normal form for swap-based Mallows MLR arguments.
-/
theorem bestInSetWeight_eq_sum_swapCandidatePositions
    (remaining : Finset (Candidate n)) {c d : Candidate n}
    (hc : c ∈ remaining) (hd : d ∈ remaining) :
    M.bestInSetWeight remaining c =
      ∑ π : Ranking n,
        if d = bestInSet π remaining then
          mallowsWeight M.q M.center (swapCandidatePositions π c d)
        else
          0 := by
  classical
  unfold bestInSetWeight
  calc
    (∑ π : Ranking n,
        if c = bestInSet π remaining then mallowsWeight M.q M.center π else 0)
        =
        ∑ π : Ranking n,
          if c = bestInSet (swapCandidatePositions π c d) remaining then
            mallowsWeight M.q M.center (swapCandidatePositions π c d)
          else
            0 := by
          simpa [swapCandidatePositionsEquiv] using
            (Equiv.sum_comp (swapCandidatePositionsEquiv c d)
              (fun π : Ranking n =>
                if c = bestInSet π remaining then
                  mallowsWeight M.q M.center π
                else
                  0)).symm
    _ =
        ∑ π : Ranking n,
          if d = bestInSet π remaining then
            mallowsWeight M.q M.center (swapCandidatePositions π c d)
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hiff := bestInSet_swapCandidatePositions_eq_iff
            (π := π) hc hd
          by_cases hbest : d = bestInSet π remaining
          · have hbest_swap :
                c = bestInSet (swapCandidatePositions π c d) remaining :=
              hiff.mpr hbest
            rw [if_pos hbest_swap, if_pos hbest]
          · have hbest_swap :
                c ≠ bestInSet (swapCandidatePositions π c d) remaining := by
              intro hc_best
              exact hbest (hiff.mp hc_best)
            rw [if_neg hbest_swap, if_neg hbest]

/-- Best-in-set fiber weights are nonnegative. -/
theorem bestInSetWeight_nonneg
    (remaining : Finset (Candidate n)) (c : Candidate n) :
    0 ≤ M.bestInSetWeight remaining c := by
  classical
  unfold bestInSetWeight
  exact Finset.sum_nonneg (by
    intro π _
    by_cases h : c = bestInSet π remaining
    · simp [h, mallowsWeight, pow_nonneg (le_of_lt M.q_pos)]
    · simp [h])

/-- A candidate outside a nonempty remaining set has zero best-in-set mass. -/
theorem bestInSetWeight_eq_zero_of_not_mem
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    {c : Candidate n} (hc : c ∉ remaining) :
    M.bestInSetWeight remaining c = 0 := by
  classical
  unfold bestInSetWeight
  apply Finset.sum_eq_zero
  intro π _
  have hnot : c ≠ bestInSet π remaining := by
    intro h
    exact hc (by simpa [h] using bestInSet_mem π hremaining)
  simp [hnot]

/--
Double-sum reduction for the best-in-set fiber cross-ratio.

After reindexing the `c`-best fibers by the `c`/`d` position swap, the whole
cross-ratio is a sum over two rankings in the `d`-best fiber.
-/
theorem bestInSetWeight_cross_nonneg_of_swap_pairwise_cross
    {Mmore Mless : MallowsSpec n} (remaining : Finset (Candidate n))
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hpair :
      ∀ π σ : Ranking n,
        d = bestInSet π remaining →
        d = bestInSet σ remaining →
        0 ≤
          mallowsWeight Mmore.q Mmore.center
              (swapCandidatePositions π c d) *
            mallowsWeight Mless.q Mless.center σ -
          mallowsWeight Mmore.q Mmore.center π *
            mallowsWeight Mless.q Mless.center
              (swapCandidatePositions σ c d)) :
    0 ≤
      Mmore.bestInSetWeight remaining c *
          Mless.bestInSetWeight remaining d -
        Mmore.bestInSetWeight remaining d *
          Mless.bestInSetWeight remaining c := by
  classical
  rw [Mmore.bestInSetWeight_eq_sum_swapCandidatePositions remaining hc hd]
  rw [Mless.bestInSetWeight_eq_sum_swapCandidatePositions remaining hc hd]
  unfold MallowsSpec.bestInSetWeight
  rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg ?_
  intro π _
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg ?_
  intro σ _
  by_cases hπ : d = bestInSet π remaining
  · by_cases hσ : d = bestInSet σ remaining
    · have hbest_eq : bestInSet π remaining = bestInSet σ remaining :=
        hπ.symm.trans hσ
      simpa [hπ, hσ, hbest_eq] using hpair π σ hπ hσ
    · simp [hσ]
  · simp [hπ]

/-- The best-in-set fibers partition the Mallows partition. -/
theorem sum_bestInSetWeight_eq_partition
    (remaining : Finset (Candidate n)) :
    (∑ c : Candidate n, M.bestInSetWeight remaining c) = M.partition := by
  classical
  unfold bestInSetWeight
  calc
    (∑ c : Candidate n, ∑ π : Ranking n,
        if c = bestInSet π remaining then mallowsWeight M.q M.center π else 0)
        = (∑ π : Ranking n, ∑ c : Candidate n,
            if c = bestInSet π remaining then mallowsWeight M.q M.center π else 0) := by
          exact Finset.sum_comm
    _ = ∑ π : Ranking n, mallowsWeight M.q M.center π := by
          refine Finset.sum_congr rfl ?_
          intro π _
          simpa using
            (Finset.sum_ite_eq' Finset.univ (bestInSet π remaining)
              (fun _ : Candidate n => mallowsWeight M.q M.center π))
    _ = M.partition := by
          rw [M.partition_eq_sum]
          rfl

/-- Expected best-in-set value in terms of unnormalized Mallows fibers. -/
theorem expectedBestInSet_eq_sum_bestInSetWeight_div_partition
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n)) :
    expectedBestInSet M.law value remaining =
      (∑ c : Candidate n, M.bestInSetWeight remaining c * value c) /
        M.partition := by
  classical
  unfold expectedBestInSet bestInSetWeight pmfExp
  calc
    ∑ π : Ranking n, (M.law π).toReal * value (bestInSet π remaining)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              value (bestInSet π remaining) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (∑ c : Candidate n,
            (if c = bestInSet π remaining then
              mallowsWeight M.q M.center π * value c
            else 0)) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = bestInSet π remaining then
                  mallowsWeight M.q M.center π * value c
                else 0) =
                mallowsWeight M.q M.center π *
                  value (bestInSet π remaining) := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (bestInSet π remaining)
                (fun c : Candidate n => mallowsWeight M.q M.center π * value c))
          rw [hsum]
          ring
    _ = (∑ π : Ranking n, ∑ c : Candidate n,
          if c = bestInSet π remaining then
            mallowsWeight M.q M.center π * value c
          else 0) / M.partition := by
          rw [Finset.sum_div]
    _ = (∑ c : Candidate n, ∑ π : Ranking n,
          if c = bestInSet π remaining then
            mallowsWeight M.q M.center π * value c
          else 0) / M.partition := by
          rw [Finset.sum_comm]
    _ = (∑ c : Candidate n,
          M.bestInSetWeight remaining c * value c) / M.partition := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro c _
          unfold bestInSetWeight
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = bestInSet π remaining
          · simp [h]
          · simp [h]

end MallowsSpec

/--
Cross-ratio dominance of best-in-set Mallows fibers lifts to expected
best-of-remaining-set utility dominance.
-/
theorem expectedBestInSet_le_of_bestInSetWeight_cross
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (remaining : Finset (Candidate n)) {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy Mmore.center value)
    (hcross :
      ∀ c d : Candidate n, rankOf Mmore.center c < rankOf Mmore.center d →
        0 ≤
          Mmore.bestInSetWeight remaining c *
              Mless.bestInSetWeight remaining d -
            Mmore.bestInSetWeight remaining d *
              Mless.bestInSetWeight remaining c) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  classical
  let wMore : Candidate n → ℝ := fun r =>
    Mmore.bestInSetWeight remaining (Mmore.center r)
  let wLess : Candidate n → ℝ := fun r =>
    Mless.bestInSetWeight remaining (Mmore.center r)
  let B : Candidate n → ℝ := fun r => value (Mmore.center r)
  have hB : ∀ i j : Candidate n, i < j → B j ≤ B i := by
    intro i j hij
    exact hvalue (by simpa [B, rankOf] using hij)
  have hpair :
      ∀ i j : Candidate n, i < j →
        0 ≤ wMore i * wLess j - wMore j * wLess i := by
    intro i j hij
    simpa [wMore, wLess, rankOf] using
      hcross (Mmore.center i) (Mmore.center j)
        (by simpa [rankOf] using hij)
  have hcore :
      0 ≤
        (∑ j : Candidate n, wLess j) *
            (∑ i : Candidate n, wMore i * B i) -
          (∑ j : Candidate n, wMore j) *
            (∑ i : Candidate n, wLess i * B i) :=
    AppliedModelingLib.FiniteSum.weighted_average_cross_nonneg_of_pairwise hpair hB
  have hmore_num :
      (∑ c : Candidate n,
        Mmore.bestInSetWeight remaining c * value c) =
        ∑ r : Candidate n, wMore r * B r := by
    simpa [wMore, B] using
      (Equiv.sum_comp Mmore.center
        (fun c : Candidate n =>
          Mmore.bestInSetWeight remaining c * value c)).symm
  have hless_num :
      (∑ c : Candidate n,
        Mless.bestInSetWeight remaining c * value c) =
        ∑ r : Candidate n, wLess r * B r := by
    simpa [wLess, B] using
      (Equiv.sum_comp Mmore.center
        (fun c : Candidate n =>
          Mless.bestInSetWeight remaining c * value c)).symm
  have hmore_den :
      Mmore.partition = ∑ r : Candidate n, wMore r := by
    rw [← Mmore.sum_bestInSetWeight_eq_partition remaining]
    simpa [wMore] using
      (Equiv.sum_comp Mmore.center
        (fun c : Candidate n => Mmore.bestInSetWeight remaining c)).symm
  have hless_den :
      Mless.partition = ∑ r : Candidate n, wLess r := by
    rw [← Mless.sum_bestInSetWeight_eq_partition remaining]
    simpa [wLess] using
      (Equiv.sum_comp Mmore.center
        (fun c : Candidate n => Mless.bestInSetWeight remaining c)).symm
  have hmore_den_pos : 0 < ∑ r : Candidate n, wMore r := by
    rw [← hmore_den]
    exact Mmore.partition_pos
  have hless_den_pos : 0 < ∑ r : Candidate n, wLess r := by
    rw [← hless_den]
    exact Mless.partition_pos
  rw [Mless.expectedBestInSet_eq_sum_bestInSetWeight_div_partition,
    Mmore.expectedBestInSet_eq_sum_bestInSetWeight_div_partition]
  rw [hless_num, hmore_num, hless_den, hmore_den]
  exact PositiveDenominator.div_le_div_of_cross_mul_le
    hless_den_pos hmore_den_pos (by linarith)

end

end Ranking
end SocialChoice
end AppliedModelingLib

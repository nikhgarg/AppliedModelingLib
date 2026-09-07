import KR21Monoculture.Theorem1

open AppliedModelingLib

namespace KR21Monoculture
namespace AccuracyFamily

/-!
# Definition 2 supplies the strict high-accuracy gap

The source proof of Theorem 1 invokes asymptotic optimality to obtain a strict
`g < f` endpoint.  The strictness does not require a special swapped-ranking
atom.  At the human accuracy, Definition 2 already forces positive mass on a
ranking whose top choice differs from the true top candidate; that error is
enough to make the pure-algorithm limit strictly better for the algorithm.
-/

/-- A strict Definition-2 preference cannot hold if every positive-mass human
ranking has the true top candidate first. -/
theorem exists_positive_mass_firstChoice_ne_centerFirst_of_prefersIndependent
    {n : ℕ} (mu : PMF (Ranking n)) (center : Ranking n)
    (value : Candidate n -> ℝ)
    (hpref : Model.PrefersIndependentReranking mu value) :
    ∃ pi : Ranking n, 0 < (mu pi).toReal ∧
      firstChoice pi ≠ firstChoice center := by
  classical
  by_cases hexists : ∃ pi : Ranking n, 0 < (mu pi).toReal ∧
      firstChoice pi ≠ firstChoice center
  · exact hexists
  exfalso
  have hsupport : ∀ pi : Ranking n, 0 < (mu pi).toReal ->
      firstChoice pi = firstChoice center := by
    intro pi hmass
    by_contra hne
    exact hexists ⟨pi, hmass, hne⟩
  have hmiss_center : firstChoiceMissProb mu (firstChoice center) = 0 := by
    rw [firstChoiceMissProb_eq_pmfProb_ne]
    apply AppliedModelingLib.pmfProb_eq_zero_of_no_mass
    intro pi hpi
    by_cases hmass : 0 < (mu pi).toReal
    · exact False.elim (hpi (hsupport pi hmass).symm)
    · exact le_antisymm (le_of_not_gt hmass) ENNReal.toReal_nonneg
  have hgain_zero : expectedRerankingGain mu value = 0 := by
    rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
    unfold AppliedModelingLib.pmfExp
    refine Finset.sum_eq_zero ?_
    intro pi _
    by_cases hmass : (mu pi).toReal = 0
    · simp [hmass]
    · have hmass_pos : 0 < (mu pi).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmass)
      have htop : firstChoice pi = firstChoice center := hsupport pi hmass_pos
      have hmiss_pi : firstChoiceMissProb mu (firstChoice pi) = 0 := by
        rw [htop]
        exact hmiss_center
      change (mu pi).toReal *
        (firstChoiceMissProb mu (firstChoice pi) * valueGap value pi) = 0
      rw [hmiss_pi]
      ring
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos] at hpref
  linarith

/-- Any positive-mass human ranking with a nonoptimal first choice makes the
pure-algorithm limiting payoff strictly larger than the human payoff numerator.
-/
theorem expected_human_against_pureCenter_lt_pureCenter_payoff_of_positive_top_error
    {n : ℕ} (mu : PMF (Ranking n)) (center : Ranking n)
    (value : Candidate n -> ℝ)
    (hvalue : StrictlyOrderedBy center value)
    {pi : Ranking n} (hmass : 0 < (mu pi).toReal)
    (htop_error : firstChoice pi ≠ firstChoice center) :
    expectedFirstMoverUtility mu value +
        expectedSecondMoverIndependent mu (PMF.pure center) value <
      expectedFirstMoverUtility (PMF.pure center) value +
        expectedSecondMoverShared (PMF.pure center) value := by
  classical
  have hpoint :
      pmfExp mu
          (fun sigma =>
            value (firstChoice sigma) +
              value (bestRemainingAfter sigma (firstChoice center))) <
        value (firstChoice center) + value (secondChoice center) := by
    refine AppliedModelingLib.pmfExp_lt_of_forall_le_exists_lt mu
      (fun sigma =>
        value (firstChoice sigma) +
          value (bestRemainingAfter sigma (firstChoice center)))
      (value (firstChoice center) + value (secondChoice center)) ?_ ?_
    · intro sigma
      exact add_le_add
        (value_le_centerFirst_of_strictlyOrderedBy hvalue (firstChoice sigma))
        (value_le_centerSecond_of_strictlyOrderedBy_of_ne_centerFirst
          hvalue (bestRemainingAfter_ne_removed sigma (firstChoice center)))
    · refine ⟨pi, hmass, ?_⟩
      have hbest :
          bestRemainingAfter pi (firstChoice center) = firstChoice pi :=
        bestRemainingAfter_of_ne pi htop_error
      have htop_lt : value (firstChoice pi) < value (firstChoice center) :=
        hvalue (rankOf_firstChoice_lt_rankOf_of_ne center htop_error)
      have htop_le_second : value (firstChoice pi) ≤ value (secondChoice center) :=
        value_le_centerSecond_of_strictlyOrderedBy_of_ne_centerFirst
          hvalue htop_error
      change value (firstChoice pi) +
          value (bestRemainingAfter pi (firstChoice center)) <
        value (firstChoice center) + value (secondChoice center)
      rw [hbest]
      linarith
  have hleft :
      expectedFirstMoverUtility mu value +
          expectedSecondMoverIndependent mu (PMF.pure center) value =
        pmfExp mu
          (fun sigma =>
            value (firstChoice sigma) +
              value (bestRemainingAfter sigma (firstChoice center))) := by
    rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    simp [expectedFirstMoverUtility, expectedBestAfterRemoval, pmfExp_add]
  have hright :
      expectedFirstMoverUtility (PMF.pure center) value +
          expectedSecondMoverShared (PMF.pure center) value =
        value (firstChoice center) + value (secondChoice center) := by
    simp [expectedFirstMoverUtility, expectedSecondMoverShared]
  simpa [hleft, hright] using hpoint

/-- Definition 2 itself supplies the strict pure-algorithm limiting gap used
by the source crossing proof. -/
theorem expected_human_against_pureCenter_lt_pureCenter_payoff_of_prefersIndependent
    {n : ℕ} (mu : PMF (Ranking n)) (center : Ranking n)
    (value : Candidate n -> ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hpref : Model.PrefersIndependentReranking mu value) :
    expectedFirstMoverUtility mu value +
        expectedSecondMoverIndependent mu (PMF.pure center) value <
      expectedFirstMoverUtility (PMF.pure center) value +
        expectedSecondMoverShared (PMF.pure center) value := by
  rcases exists_positive_mass_firstChoice_ne_centerFirst_of_prefersIndependent
      mu center value hpref with ⟨pi, hmass, htop_error⟩
  exact
    expected_human_against_pureCenter_lt_pureCenter_payoff_of_positive_top_error
      mu center value hvalue hmass htop_error

end AccuracyFamily
end KR21Monoculture

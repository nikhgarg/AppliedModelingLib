import KR21Monoculture.MallowsSupport
import KR21Monoculture.ConditionalForm
import Mathlib.Tactic

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Two-candidate obstruction to the strict Mallows Theorem-3 claim

The source states Theorem 3 for any candidate distribution.  Appendix E.1
obtains strictness from a pair of distinct non-extreme ranks; that step has no
such pair when there are exactly two candidates.  This file records the
resulting concrete obstruction using the actual finite Mallows PMF.

The library convention is `Candidate 0 = Fin 2`.
-/

/-- The source's identity true ranking on exactly two candidates. -/
def theorem3TwoCandidateCenter : Ranking 0 := Equiv.refl (Candidate 0)

/-- The only ranking other than the identity on two candidates. -/
def theorem3TwoCandidateReverse : Ranking 0 := Equiv.swap (0 : Candidate 0) 1

/-- A strict source value profile: candidate `0` has value `1`, candidate `1` value `0`. -/
def theorem3TwoCandidateValue (c : Candidate 0) : ℝ :=
  if c = 0 then 1 else 0

private theorem candidate_zero_eq_zero_or_one (c : Candidate 0) :
    c = 0 ∨ c = 1 := by
  rcases Fin.eq_zero_or_eq_succ c with h | ⟨i, h⟩
  · exact Or.inl h
  · have hi : i = 0 := Fin.eq_zero i
    subst i
    exact Or.inr h

private theorem ranking_zero_eq_center_or_reverse (pi : Ranking 0) :
    pi = theorem3TwoCandidateCenter ∨ pi = theorem3TwoCandidateReverse := by
  have hfirst : pi 0 = 0 ∨ pi 0 = 1 :=
    candidate_zero_eq_zero_or_one (pi 0)
  rcases hfirst with hfirst | hfirst
  · left
    apply Equiv.ext
    intro i
    rcases candidate_zero_eq_zero_or_one i with hi | hi
    · subst i
      simpa [theorem3TwoCandidateCenter] using hfirst
    · subst i
      have hne : pi 1 ≠ (0 : Candidate 0) := by
        intro hsecond
        have h10 : (1 : Candidate 0) = 0 :=
          pi.injective (hsecond.trans hfirst.symm)
        exact Fin.zero_ne_one h10.symm
      have hsecond : pi 1 = 1 := by
        rcases candidate_zero_eq_zero_or_one (pi 1) with hzero | hone
        · exact (hne hzero).elim
        · exact hone
      simpa [theorem3TwoCandidateCenter] using hsecond
  · right
    apply Equiv.ext
    intro i
    rcases candidate_zero_eq_zero_or_one i with hi | hi
    · subst i
      simpa [theorem3TwoCandidateReverse] using hfirst
    · subst i
      have hne : pi 1 ≠ (1 : Candidate 0) := by
        intro hsecond
        have h10 : (1 : Candidate 0) = 0 :=
          pi.injective (hsecond.trans hfirst.symm)
        exact Fin.zero_ne_one h10.symm
      have hsecond : pi 1 = 0 := by
        rcases candidate_zero_eq_zero_or_one (pi 1) with hzero | hone
        · exact hzero
        · exact (hne hone).elim
      simpa [theorem3TwoCandidateReverse] using hsecond

private theorem theorem3TwoCandidateCenter_ne_reverse :
    theorem3TwoCandidateCenter ≠ theorem3TwoCandidateReverse := by
  intro h
  have hzero := congrArg (fun pi : Ranking 0 => pi 0) h
  norm_num [theorem3TwoCandidateCenter, theorem3TwoCandidateReverse] at hzero

private theorem sum_rankings_two (f : Ranking 0 -> ℝ) :
    (∑ pi : Ranking 0, f pi) =
      f theorem3TwoCandidateCenter + f theorem3TwoCandidateReverse := by
  have huniv : (Finset.univ : Finset (Ranking 0)) =
      {theorem3TwoCandidateCenter, theorem3TwoCandidateReverse} := by
    ext pi
    simp only [Finset.mem_univ]
    rcases ranking_zero_eq_center_or_reverse pi with hpi | hpi
    · subst pi
      simp [theorem3TwoCandidateCenter_ne_reverse]
    · subst pi
      simp
  rw [huniv]
  rw [Finset.sum_insert]
  · simp
  · simp [theorem3TwoCandidateCenter_ne_reverse]

/-- With exactly two candidates, swapping the two independent ranking draws
negates the reranking gain.  This is the symmetry that removes Definition 2's
strictness. -/
theorem rerankingGainOnPair_swap_neg_twoCandidates
    (value : Candidate 0 -> ℝ) (pi sigma : Ranking 0) :
    rerankingGainOnPair value pi sigma =
      -rerankingGainOnPair value sigma pi := by
  rcases ranking_zero_eq_center_or_reverse pi with hpi | hpi <;>
    rcases ranking_zero_eq_center_or_reverse sigma with hsigma | hsigma <;>
    subst pi <;> subst sigma <;>
    simp [rerankingGainOnPair, firstChoice, secondChoice,
      theorem3TwoCandidateCenter, theorem3TwoCandidateReverse]

/-- No two-candidate ranking PMF can satisfy the source's strict Definition 2.
The argument is law-independent: the IID product law is invariant under
swapping the two draws, while the gain is antisymmetric. -/
theorem expectedRerankingGain_eq_zero_twoCandidates
    (mu : PMF (Ranking 0)) (value : Candidate 0 -> ℝ) :
    expectedRerankingGain mu value = 0 := by
  let gain : Ranking 0 -> Ranking 0 -> ℝ :=
    fun pi sigma => rerankingGainOnPair value pi sigma
  have hswap :
      pmfPairExp mu mu gain =
        pmfPairExp mu mu (fun pi sigma => gain sigma pi) := by
    simpa [gain] using (pmfPairExp_swap mu mu gain)
  have hneg :
      pmfPairExp mu mu (fun pi sigma => gain sigma pi) =
        -pmfPairExp mu mu gain := by
    calc
      pmfPairExp mu mu (fun pi sigma => gain sigma pi) =
          pmfPairExp mu mu (fun pi sigma => -gain pi sigma) := by
        congr 1
        funext pi sigma
        exact rerankingGainOnPair_swap_neg_twoCandidates value sigma pi
      _ = -pmfPairExp mu mu gain := by
        unfold pmfPairExp
        simp only [pmfExp_neg]
  change pmfPairExp mu mu gain = 0
  rw [hswap, hneg]
  linarith

/-- The two off-diagonal ranking pairs are exactly the first-choice
disagreement event on two candidates. -/
theorem disagreementProb_eq_two_mul_mass_product_twoCandidates
    (mu : PMF (Ranking 0)) :
    disagreementProb mu =
      2 * (mu theorem3TwoCandidateCenter).toReal *
        (mu theorem3TwoCandidateReverse).toReal := by
  unfold disagreementProb AppliedModelingLib.SocialChoice.Ranking.disagreementProb
    pmfPairProb pmfPairExp pmfExp
    AppliedModelingLib.SocialChoice.Ranking.disagreementEvent
  simp_rw [sum_rankings_two]
  simp [firstChoice, theorem3TwoCandidateCenter,
    theorem3TwoCandidateReverse]
  ring

/-- The concrete inverse Mallows parameter used for the two-candidate
counterexample.  It lies strictly in the source range `(0,1)`. -/
noncomputable def theorem3TwoCandidateQ : ℝ := 1 / 2

theorem theorem3TwoCandidateQ_pos : 0 < theorem3TwoCandidateQ := by
  norm_num [theorem3TwoCandidateQ]

theorem theorem3TwoCandidateQ_lt_one : theorem3TwoCandidateQ < 1 := by
  norm_num [theorem3TwoCandidateQ]

/-- A genuine finite Mallows law centered at the source identity order. -/
noncomputable def theorem3TwoCandidateMallows : MallowsSpec 0 :=
  MallowsSpec.ofQ theorem3TwoCandidateCenter theorem3TwoCandidateQ
    theorem3TwoCandidateQ_pos

theorem theorem3TwoCandidateValue_strict_gap :
    theorem3TwoCandidateValue (1 : Candidate 0) <
      theorem3TwoCandidateValue (0 : Candidate 0) := by
  norm_num [theorem3TwoCandidateValue]

/-- Both rankings have positive mass under the concrete Mallows law. -/
theorem theorem3TwoCandidateMallows_center_mass_pos :
    0 < (theorem3TwoCandidateMallows.law theorem3TwoCandidateCenter).toReal :=
  theorem3TwoCandidateMallows.law_apply_toReal_pos theorem3TwoCandidateCenter

/-- Both rankings have positive mass under the concrete Mallows law. -/
theorem theorem3TwoCandidateMallows_reverse_mass_pos :
    0 < (theorem3TwoCandidateMallows.law theorem3TwoCandidateReverse).toReal :=
  theorem3TwoCandidateMallows.law_apply_toReal_pos theorem3TwoCandidateReverse

/-- The source conditioning event has genuinely positive probability in the
concrete two-candidate Mallows counterexample. -/
theorem theorem3TwoCandidateMallows_disagreementProb_pos :
    0 < disagreementProb theorem3TwoCandidateMallows.law := by
  rw [disagreementProb_eq_two_mul_mass_product_twoCandidates]
  exact mul_pos
    (mul_pos (by norm_num) theorem3TwoCandidateMallows_center_mass_pos)
    theorem3TwoCandidateMallows_reverse_mass_pos

/-- Exact source-Definition-2 failure: even with a strict value gap and a
nondegenerate Mallows law with `0 < q < 1`, the conditional top-disagreement
gain is zero, not strictly positive. -/
theorem theorem3TwoCandidateMallows_conditionalGain_eq_zero :
    disagreementConditionalGain theorem3TwoCandidateMallows.law
      theorem3TwoCandidateValue = 0 := by
  rw [disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos]
  · rw [expectedRerankingGain_eq_zero_twoCandidates]
    simp
  · exact theorem3TwoCandidateMallows_disagreementProb_pos

/-- Consequently this actual Mallows instance does not satisfy the strict
preference-for-the-first-position predicate used for source Definition 2. -/
theorem theorem3TwoCandidateMallows_not_prefersIndependentReranking :
    ¬ Model.PrefersIndependentReranking theorem3TwoCandidateMallows.law
      theorem3TwoCandidateValue := by
  rw [prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos]
  · rw [theorem3TwoCandidateMallows_conditionalGain_eq_zero]
    norm_num
  · exact theorem3TwoCandidateMallows_disagreementProb_pos

end KR21Monoculture

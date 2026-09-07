import KR21Monoculture.AppendixBGaussianMixtureW11

open AppliedModelingLib
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/-!
# Appendix B source Definition 1 finite-set monotonicity

The paper's Definition 1 quantifies over an arbitrary set of candidates removed
after a ranking is drawn.  For three candidates, every nonempty remaining set
is a singleton, a co-singleton, or the full set.  This module lifts the
existing strict full-set and weak one-removal fields to that literal finite-set
quantifier without changing the already proved source families.
-/

/-- The monotonicity clause of source Definition 1, written using the remaining
candidate set rather than its removed complement.  The strict field is the
source's `S = ∅` case. -/
structure SourceDefinition1FiniteSetMonotonicityAt {n : ℕ}
    (F : AccuracyFamily n) (thetaA thetaH : ℝ) : Prop where
  full_set_strict :
    expectedBestInSet (F.dist thetaH) F.value Finset.univ <
      expectedBestInSet (F.dist thetaA) F.value Finset.univ
  remaining_set_weak : ∀ remaining : Finset (Candidate n), remaining.Nonempty →
    expectedBestInSet (F.dist thetaH) F.value remaining ≤
      expectedBestInSet (F.dist thetaA) F.value remaining

/-- In the three-candidate universe, the current strict full-set and weak
one-removal certificate already covers every nonempty source remaining set.
Singleton sets have a law-independent payoff; two-element sets are exactly the
complements of the current singleton removals. -/
theorem sourceDefinition1FiniteSetMonotonicityAt_of_theorem1RemovalMonotonicityAt_three
    {F : AccuracyFamily 1} {thetaA thetaH : ℝ}
    (hmono : AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH) :
    SourceDefinition1FiniteSetMonotonicityAt F thetaA thetaH := by
  classical
  have hfull_strict :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ := by
    simpa using hmono.firstMover_strict
  have hfull_weak :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ ≤
        expectedBestInSet (F.dist thetaA) F.value Finset.univ :=
    le_of_lt hfull_strict
  have hsingleton : ∀ c : Candidate 1,
      expectedBestInSet (F.dist thetaH) F.value ({c} : Finset (Candidate 1)) ≤
        expectedBestInSet (F.dist thetaA) F.value ({c} : Finset (Candidate 1)) := by
    intro c
    simp
  have hcosingleton : ∀ c : Candidate 1,
      expectedBestInSet (F.dist thetaH) F.value
          (Finset.univ \ ({c} : Finset (Candidate 1))) ≤
        expectedBestInSet (F.dist thetaA) F.value
          (Finset.univ \ ({c} : Finset (Candidate 1))) := by
    intro c
    rw [KR21Monoculture.expectedBestInSet_univ_sdiff_singleton,
      KR21Monoculture.expectedBestInSet_univ_sdiff_singleton]
    exact hmono.bestRemaining_weak c
  refine ⟨hfull_strict, ?_⟩
  intro remaining hremaining
  by_cases h0 : (0 : Candidate 1) ∈ remaining
  · by_cases h1 : (1 : Candidate 1) ∈ remaining
    · by_cases h2 : (2 : Candidate 1) ∈ remaining
      · have hset : remaining = Finset.univ := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        rw [hset]
        exact hfull_weak
      · have hset : remaining =
            ({(0 : Candidate 1), (1 : Candidate 1)} : Finset (Candidate 1)) := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        have hpair :
            expectedBestInSet (F.dist thetaH) F.value
                ({(0 : Candidate 1), (1 : Candidate 1)} : Finset (Candidate 1)) ≤
              expectedBestInSet (F.dist thetaA) F.value
                ({(0 : Candidate 1), (1 : Candidate 1)} : Finset (Candidate 1)) := by
          simpa using hcosingleton (2 : Candidate 1)
        rw [hset]
        exact hpair
    · by_cases h2 : (2 : Candidate 1) ∈ remaining
      · have hset : remaining =
            ({(0 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1)) := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        have hpair :
            expectedBestInSet (F.dist thetaH) F.value
                ({(0 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1)) ≤
              expectedBestInSet (F.dist thetaA) F.value
                ({(0 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1)) := by
          simpa using hcosingleton (1 : Candidate 1)
        rw [hset]
        exact hpair
      · have hset : remaining = ({(0 : Candidate 1)} : Finset (Candidate 1)) := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        rw [hset]
        exact hsingleton (0 : Candidate 1)
  · by_cases h1 : (1 : Candidate 1) ∈ remaining
    · by_cases h2 : (2 : Candidate 1) ∈ remaining
      · have hset : remaining =
            ({(1 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1)) := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        have hpair :
            expectedBestInSet (F.dist thetaH) F.value
                ({(1 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1)) ≤
              expectedBestInSet (F.dist thetaA) F.value
                ({(1 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1)) := by
          simpa using hcosingleton (0 : Candidate 1)
        rw [hset]
        exact hpair
      · have hset : remaining = ({(1 : Candidate 1)} : Finset (Candidate 1)) := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        rw [hset]
        exact hsingleton (1 : Candidate 1)
    · by_cases h2 : (2 : Candidate 1) ∈ remaining
      · have hset : remaining = ({(2 : Candidate 1)} : Finset (Candidate 1)) := by
          ext c
          fin_cases c <;> simp [h0, h1, h2]
        rw [hset]
        exact hsingleton (2 : Candidate 1)
      · exfalso
        rcases hremaining with ⟨c, hc⟩
        fin_cases c <;> simp [h0, h1, h2] at hc

/-- The literal Appendix B.1 source Gaussian-mixture family satisfies the
source Definition 1 monotonicity clause for every nonempty remaining set. -/
theorem appendixB1SourceGaussianMixture_sourceDefinition1FiniteSetMonotonicity
    (s : ℝ) (hs : 0 < s) :
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      SourceDefinition1FiniteSetMonotonicityAt
        (appendixB1SourceGaussianMixtureFamily s) thetaA thetaH := by
  intro thetaA thetaH hthetaH hthetaHA
  let certificate := appendixB1SourceGaussianMixture_correctedW11Definition1 s hs
  exact
    sourceDefinition1FiniteSetMonotonicityAt_of_theorem1RemovalMonotonicityAt_three
      (certificate.toPaperAppendixAScaledNoiseDefinition1Consequence.removal_monotonicity
        thetaA thetaH hthetaH hthetaHA)

/-- Proposition-level B.1 finite-set monotonicity endpoint for source review.
It exposes the arbitrary-remaining-set quantifier and the strict full-set case
rather than hiding them in `SourceDefinition1FiniteSetMonotonicityAt`. -/
theorem appendixB1SourceGaussianMixture_sourceDefinition1FiniteSetMonotonicity_fields
    (s : ℝ) (hs : 0 < s) :
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
            appendixB1Value remaining ≤
          expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
            appendixB1Value remaining) ∧
        expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
            appendixB1Value Finset.univ <
          expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
            appendixB1Value Finset.univ := by
  intro thetaA thetaH hthetaH hthetaHA
  let certificate :=
    appendixB1SourceGaussianMixture_sourceDefinition1FiniteSetMonotonicity
      s hs thetaA thetaH hthetaH hthetaHA
  exact ⟨certificate.remaining_set_weak, certificate.full_set_strict⟩

/-- The literal Appendix B.2 source Gaussian-mixture family satisfies the
source Definition 1 monotonicity clause for every nonempty remaining set. -/
theorem appendixB2SourceGaussianMixture_sourceDefinition1FiniteSetMonotonicity
    (s : ℝ) (hs : 0 < s) :
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      SourceDefinition1FiniteSetMonotonicityAt
        (appendixB2SourceGaussianMixtureFamily s) thetaA thetaH := by
  intro thetaA thetaH hthetaH hthetaHA
  let certificate := appendixB2SourceGaussianMixture_correctedW11Definition1 s hs
  exact
    sourceDefinition1FiniteSetMonotonicityAt_of_theorem1RemovalMonotonicityAt_three
      (certificate.toPaperAppendixAScaledNoiseDefinition1Consequence.removal_monotonicity
        thetaA thetaH hthetaH hthetaHA)

/-- Proposition-level B.2 finite-set monotonicity endpoint for source review.
It exposes the arbitrary-remaining-set quantifier and the strict full-set case
rather than hiding them in `SourceDefinition1FiniteSetMonotonicityAt`. -/
theorem appendixB2SourceGaussianMixture_sourceDefinition1FiniteSetMonotonicity_fields
    (s : ℝ) (hs : 0 < s) :
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
            appendixB2Value remaining ≤
          expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
            appendixB2Value remaining) ∧
        expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
            appendixB2Value Finset.univ <
          expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
            appendixB2Value Finset.univ := by
  intro thetaA thetaH hthetaH hthetaHA
  let certificate :=
    appendixB2SourceGaussianMixture_sourceDefinition1FiniteSetMonotonicity
      s hs thetaA thetaH hthetaH hthetaHA
  exact ⟨certificate.remaining_set_weak, certificate.full_set_strict⟩

end KR21Monoculture

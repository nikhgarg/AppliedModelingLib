import KR21Monoculture.Theorem1
import AppliedModelingLib.Foundations.Probability.WithoutReplacement

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Plackett--Luce, source equation (7), and the zero reranking effect

The source's excluded example is the sequential Plackett--Luce law.  At every
stage it chooses `i` from the remaining set `S` with probability
`exp(theta * value i) / sum_{j in S} exp(theta * value j)`.  The recursive
without-replacement PMF below is an actual finite sampler for that law.

Its key IIA feature is visible in `plackettLuceRemainingUtility`: after the
first candidate is removed, the next-choice law depends only on the remaining
set, not on whether the first ranking was shared or independently redrawn.
Consequently the two second-mover utilities are equal and Definition 2's
strict independent-reranking effect is exactly zero.
-/

/-- Positive Plackett--Luce weight of a candidate. -/
noncomputable def plackettLuceWeight {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) (i : Candidate n) : ℝ :=
  Real.exp (theta * value i)

theorem plackettLuceWeight_pos {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) (i : Candidate n) :
    0 < plackettLuceWeight theta value i := by
  exact Real.exp_pos _

/-- Equation (7), including its zero value outside the remaining set. -/
noncomputable def plackettLuceChoiceProb {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n))
    (i : Candidate n) : ℝ :=
  if i ∈ remaining then
    Real.exp (theta * value i) /
      ∑ j ∈ remaining, Real.exp (theta * value j)
  else 0

/-- Source equation (7) on an available candidate. -/
theorem plackettLuceChoiceProb_eq_equation7 {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n))
    {i : Candidate n} (hi : i ∈ remaining) :
    plackettLuceChoiceProb theta value remaining i =
      Real.exp (theta * value i) /
        ∑ j ∈ remaining, Real.exp (theta * value j) := by
  simp [plackettLuceChoiceProb, hi]

/-- Every non-full remaining-state denominator in the recursive sampler is positive. -/
theorem plackettLuceAvailableWeight_pos {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) (forbidden : Finset (Candidate n))
    (hcard : forbidden.card < Fintype.card (Candidate n)) :
    0 < finiteAvailableWeight (plackettLuceWeight theta value) forbidden :=
  finiteAvailableWeight_pos_of_full_support_of_card_lt
    (plackettLuceWeight theta value) forbidden
    (fun i => (plackettLuceWeight_pos theta value i).le)
    (plackettLuceWeight_pos theta value) hcard

/-- The source's full sequential Plackett--Luce draw, before converting the full list to a permutation. -/
noncomputable def plackettLuceFreshRankingPMF {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) :
    PMF (finiteFreshList (Candidate n) (n + 2) ∅) :=
  finiteWithoutReplacementPMF
    (plackettLuceWeight theta value)
    (fun i => (plackettLuceWeight_pos theta value i).le)
    (plackettLuceAvailableWeight_pos theta value)
    (n + 2) ∅ (by simp [Candidate])

/-- A full fresh list on the candidate set is a ranking permutation. -/
noncomputable def fullFreshListToRanking {n : ℕ}
    (sample : finiteFreshList (Candidate n) (n + 2) ∅) : Ranking n :=
  Equiv.ofBijective sample.1 sample.2.1.bijective_of_finite

@[simp]
theorem fullFreshListToRanking_apply {n : ℕ}
    (sample : finiteFreshList (Candidate n) (n + 2) ∅)
    (slot : Candidate n) :
    fullFreshListToRanking sample slot = sample.1 slot :=
  rfl

/-- The corresponding PMF on the paper's ranking type. -/
noncomputable def plackettLuceRankingPMF {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) : PMF (Ranking n) :=
  (plackettLuceFreshRankingPMF theta value).map fullFreshListToRanking

/-- Probability that a ranking begins with the ordered pair `(first, second)`. -/
noncomputable def firstSecondChoiceProb {n : ℕ}
    (mu : PMF (Ranking n)) (first second : Candidate n) : ℝ :=
  pmfProb mu fun pi =>
    first = AppliedModelingLib.SocialChoice.Ranking.firstChoice pi ∧
      second = AppliedModelingLib.SocialChoice.Ranking.secondChoice pi

/-- A second-position marginal is the sum of its first/second joint atoms. -/
theorem secondChoiceProb_eq_sum_firstSecondChoiceProb {n : ℕ}
    (mu : PMF (Ranking n)) (second : Candidate n) :
    secondChoiceProb mu second =
      ∑ first : Candidate n, firstSecondChoiceProb mu first second := by
  classical
  unfold secondChoiceProb firstSecondChoiceProb pmfProb pmfExp
  calc
    ∑ pi : Ranking n, (mu pi).toReal *
        (if second = AppliedModelingLib.SocialChoice.Ranking.secondChoice pi then 1 else 0)
        = ∑ pi : Ranking n, ∑ first : Candidate n,
            (mu pi).toReal *
              (if first = AppliedModelingLib.SocialChoice.Ranking.firstChoice pi ∧
                  second = AppliedModelingLib.SocialChoice.Ranking.secondChoice pi
                then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro pi _
          by_cases hsecond :
              second = AppliedModelingLib.SocialChoice.Ranking.secondChoice pi
          · simp [hsecond]
          · have hsecond' : second ≠ pi 1 := by
              simpa [AppliedModelingLib.SocialChoice.Ranking.secondChoice] using hsecond
            simp [hsecond']
    _ = ∑ first : Candidate n, ∑ pi : Ranking n,
          (mu pi).toReal *
            (if first = AppliedModelingLib.SocialChoice.Ranking.firstChoice pi ∧
                second = AppliedModelingLib.SocialChoice.Ranking.secondChoice pi
              then 1 else 0) := by
          exact Finset.sum_comm

/-- Expected best remaining value regrouped by the selected surviving candidate. -/
theorem expectedBestAfterRemoval_eq_sum_bestRemainingProb {n : ℕ}
    (mu : PMF (Ranking n)) (value : Candidate n → ℝ)
    (removed : Candidate n) :
    AccuracyFamily.expectedBestAfterRemoval mu value removed =
      ∑ i : Candidate n,
        pmfProb mu (fun pi =>
          i = bestRemainingAfter pi removed) * value i := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval pmfProb pmfExp
  calc
    ∑ pi : Ranking n,
        (mu pi).toReal * value (bestRemainingAfter pi removed)
        = ∑ pi : Ranking n, ∑ i : Candidate n,
            if i = bestRemainingAfter pi removed then
              (mu pi).toReal * value i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro pi _
          simpa using
            (Finset.sum_ite_eq' Finset.univ (bestRemainingAfter pi removed)
              (fun i : Candidate n => (mu pi).toReal * value i))
    _ = ∑ i : Candidate n, ∑ pi : Ranking n,
          if i = bestRemainingAfter pi removed then
            (mu pi).toReal * value i else 0 := by
          exact Finset.sum_comm
    _ = ∑ i : Candidate n, ∑ pi : Ranking n,
          ((mu pi).toReal *
            (if i = bestRemainingAfter pi removed then (1 : ℝ) else 0)) *
              value i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro pi _
          by_cases h : i = bestRemainingAfter pi removed <;> simp [h]
    _ = ∑ i : Candidate n,
          (∑ pi : Ranking n, (mu pi).toReal *
            (if i = bestRemainingAfter pi removed then (1 : ℝ) else 0)) *
              value i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]

/--
For `i ≠ removed`, the best-surviving event has exactly two disjoint routes:
`i` is first, or `removed` is first and `i` is second.
-/
theorem bestRemainingProb_eq_first_add_firstSecond {n : ℕ}
    (mu : PMF (Ranking n)) (removed i : Candidate n)
    (hi : i ≠ removed) :
    pmfProb mu (fun pi => i = bestRemainingAfter pi removed) =
      firstChoiceProb mu i + firstSecondChoiceProb mu removed i := by
  classical
  have hevent : ∀ pi : Ranking n,
      (i = bestRemainingAfter pi removed) ↔
        (i = AppliedModelingLib.SocialChoice.Ranking.firstChoice pi) ∨
          (removed = AppliedModelingLib.SocialChoice.Ranking.firstChoice pi ∧
            i = AppliedModelingLib.SocialChoice.Ranking.secondChoice pi) := by
    intro pi
    by_cases hfirst :
        AppliedModelingLib.SocialChoice.Ranking.firstChoice pi = removed
    · constructor
      · intro hbest
        right
        refine ⟨hfirst.symm, ?_⟩
        have hremaining :
            bestRemainingAfter pi removed =
              AppliedModelingLib.SocialChoice.Ranking.secondChoice pi := by
          rw [← hfirst]
          exact bestRemainingAfter_of_eq pi
        exact hbest.trans hremaining
      · rintro (hfirst_i | ⟨_removed_first, hsecond⟩)
        · exact False.elim (hi (hfirst_i.trans hfirst))
        · have hremaining :
              bestRemainingAfter pi removed =
                AppliedModelingLib.SocialChoice.Ranking.secondChoice pi := by
            rw [← hfirst]
            exact bestRemainingAfter_of_eq pi
          exact hsecond.trans hremaining.symm
    · constructor
      · intro hbest
        left
        simpa [bestRemainingAfter_of_ne pi hfirst] using hbest
      · rintro (hfirst_i | ⟨hremoved, _hsecond⟩)
        · simpa [bestRemainingAfter_of_ne pi hfirst] using hfirst_i
        · exact False.elim (hfirst hremoved.symm)
  rw [pmfProb_congr mu hevent]
  rw [pmfProb_or_eq_add_of_disjoint]
  · rfl
  · intro pi hfirst_i hremoved
    exact hi (hfirst_i.trans hremoved.1.symm)

/-- The first draw of the recursive law is exactly source equation (7) with `S` equal to all candidates. -/
theorem plackettLuceFreshRankingPMF_firstChoiceProb_eq_equation7
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (i : Candidate n) :
    pmfProb (plackettLuceFreshRankingPMF theta value)
        (fun sample => sample.1 (0 : Candidate n) = i) =
      Real.exp (theta * value i) /
        ∑ j : Candidate n, Real.exp (theta * value j) := by
  let head : {j : Candidate n // j ∉ (∅ : Finset (Candidate n))} :=
    ⟨i, by simp⟩
  have hsource :=
    finiteWithoutReplacementPMF_head_prob
      (plackettLuceWeight theta value)
      (fun j => (plackettLuceWeight_pos theta value j).le)
      (plackettLuceAvailableWeight_pos theta value)
      (k := n + 1) (∅ : Finset (Candidate n))
      (by simp [Candidate]) head
  simpa [plackettLuceFreshRankingPMF, plackettLuceWeight,
    finiteAvailableWeight, head] using hsource

/-- The constructed ranking PMF has source equation (7) as its first-choice marginal. -/
theorem plackettLuceRankingPMF_firstChoiceProb_eq_equation7
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (i : Candidate n) :
    firstChoiceProb (plackettLuceRankingPMF theta value) i =
      plackettLuceChoiceProb theta value Finset.univ i := by
  unfold firstChoiceProb AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
    plackettLuceRankingPMF
  rw [pmfProb_map]
  simpa [AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    plackettLuceChoiceProb, eq_comm] using
      plackettLuceFreshRankingPMF_firstChoiceProb_eq_equation7
        theta value i

/--
The first two draws of the recursive sampler have the product law prescribed by
equation (7): first choose from the full set, then choose from the set with that
first candidate removed.
-/
theorem plackettLuceFreshRankingPMF_firstSecondProb_eq_equation7
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (first second : Candidate n) (hne : second ≠ first) :
    pmfProb (plackettLuceFreshRankingPMF theta value)
        (fun sample =>
          sample.1 (0 : Candidate n) = first ∧
            sample.1 (1 : Candidate n) = second) =
      plackettLuceChoiceProb theta value Finset.univ first *
        plackettLuceChoiceProb theta value
          ((Finset.univ : Finset (Candidate n)).erase first) second := by
  classical
  let head : {i : Candidate n // i ∉ (∅ : Finset (Candidate n))} :=
    ⟨first, by simp⟩
  let next :
      {i : Candidate n // i ∉ insert head.1 (∅ : Finset (Candidate n))} :=
    ⟨second, by simp [head, hne]⟩
  let tailLaw :=
    finiteWithoutReplacementPMF
      (plackettLuceWeight theta value)
      (fun i => (plackettLuceWeight_pos theta value i).le)
      (plackettLuceAvailableWeight_pos theta value)
      (n + 1) (insert head.1 (∅ : Finset (Candidate n)))
      (by simp [Candidate, head]; omega)
  have htail :
      pmfProb tailLaw
          (fun tail => tail.1 (0 : Fin (n + 1)) = next.1) =
        (finiteWeightedPMFAvailable
          (plackettLuceWeight theta value)
          (insert head.1 (∅ : Finset (Candidate n)))
          (fun i => (plackettLuceWeight_pos theta value i).le)
          (plackettLuceAvailableWeight_pos theta value
            (insert head.1 (∅ : Finset (Candidate n)))
            (by simp [Candidate, head])) next).toReal := by
    simpa [tailLaw] using
      (finiteWithoutReplacementPMF_head_prob
        (plackettLuceWeight theta value)
        (fun i => (plackettLuceWeight_pos theta value i).le)
        (plackettLuceAvailableWeight_pos theta value)
        (k := n) (insert head.1 (∅ : Finset (Candidate n)))
        (by simp [Candidate, head]; omega) next)
  have hjoint :=
    finiteWithoutReplacementPMF_head_tail_prob
      (plackettLuceWeight theta value)
      (fun i => (plackettLuceWeight_pos theta value i).le)
      (plackettLuceAvailableWeight_pos theta value)
      (k := n + 1) (∅ : Finset (Candidate n))
      (by simp [Candidate]) head
      (fun tail => tail.1 (0 : Fin (n + 1)) = next.1)
  rw [htail] at hjoint
  simp only [finiteWeightedPMFAvailable_apply_toReal] at hjoint
  have hdenominator :
      (∑ x : Candidate n,
          if x = first then 0 else Real.exp (theta * value x)) =
        (∑ x : Candidate n, Real.exp (theta * value x)) -
          Real.exp (theta * value first) := by
    calc
      (∑ x : Candidate n,
          if x = first then 0 else Real.exp (theta * value x)) =
          finiteAvailableWeight
            (plackettLuceWeight theta value) {first} := by
        unfold finiteAvailableWeight plackettLuceWeight
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = first <;> simp [hx]
      _ = (∑ x : Candidate n, Real.exp (theta * value x)) -
          Real.exp (theta * value first) := by
        have hsplit := finiteAvailableWeight_add_forbidden_sum
          (plackettLuceWeight theta value) {first}
        simp [plackettLuceWeight] at hsplit
        linarith
  have hlength : n + 1 + 1 = n + 2 := by omega
  simpa [plackettLuceFreshRankingPMF, tailLaw, head, next,
    finiteFreshListTailOfHead, finTail,
    finiteAvailableWeight, plackettLuceWeight,
    plackettLuceChoiceProb, hne, hdenominator, hlength] using hjoint

/-- The first/second joint law of the constructed ranking PMF is equation (7). -/
theorem plackettLuceRankingPMF_firstSecondChoiceProb_eq_equation7
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (first second : Candidate n) :
    firstSecondChoiceProb (plackettLuceRankingPMF theta value) first second =
      plackettLuceChoiceProb theta value Finset.univ first *
        plackettLuceChoiceProb theta value
          ((Finset.univ : Finset (Candidate n)).erase first) second := by
  classical
  by_cases hne : second = first
  · subst second
    have hzero :
        firstSecondChoiceProb (plackettLuceRankingPMF theta value) first first = 0 := by
      unfold firstSecondChoiceProb
      exact pmfProb_eq_zero_of_no_mass _ _ (by
        intro pi hpi
        exact False.elim
          (AppliedModelingLib.SocialChoice.Ranking.firstChoice_ne_secondChoice pi
            (hpi.1.symm.trans hpi.2)))
    rw [hzero]
    simp [plackettLuceChoiceProb]
  · unfold firstSecondChoiceProb plackettLuceRankingPMF
    rw [pmfProb_map]
    simpa [AppliedModelingLib.SocialChoice.Ranking.firstChoice,
      AppliedModelingLib.SocialChoice.Ranking.secondChoice, eq_comm] using
      plackettLuceFreshRankingPMF_firstSecondProb_eq_equation7
        theta value first second hne

/-- Expected value of the next Plackett--Luce choice after `removed` is unavailable. -/
noncomputable def plackettLuceRemainingUtility {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) (removed : Candidate n) : ℝ :=
  ∑ i : Candidate n,
    plackettLuceChoiceProb theta value
      ((Finset.univ : Finset (Candidate n)).erase removed) i * value i

/-- Shared-ranking interpretation of the source's second-mover utility. -/
noncomputable def plackettLuceSecondMoverShared {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) : ℝ :=
  ∑ first : Candidate n,
    plackettLuceChoiceProb theta value Finset.univ first *
      plackettLuceRemainingUtility theta value first

/--
Probability that an independent Plackett--Luce ranking supplies `i` as its best
candidate after `removed` is unavailable.  Either `i` was its first choice, or
it first chose `removed` and then chose `i` from the remaining set.
-/
noncomputable def plackettLuceIndependentBestRemainingProb {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (removed i : Candidate n) : ℝ :=
  if i = removed then 0 else
    plackettLuceChoiceProb theta value Finset.univ i +
      plackettLuceChoiceProb theta value Finset.univ removed *
        plackettLuceChoiceProb theta value
          ((Finset.univ : Finset (Candidate n)).erase removed) i

/-- Plackett--Luce IIA: the two routes to the best surviving candidate collapse to equation (7). -/
theorem plackettLuceIndependentBestRemainingProb_eq_remainingChoice
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (removed i : Candidate n) :
    plackettLuceIndependentBestRemainingProb theta value removed i =
      plackettLuceChoiceProb theta value
        ((Finset.univ : Finset (Candidate n)).erase removed) i := by
  classical
  by_cases hi : i = removed
  · subst i
    simp [plackettLuceIndependentBestRemainingProb,
      plackettLuceChoiceProb]
  · have hiRemaining :
        i ∈ (Finset.univ : Finset (Candidate n)).erase removed := by
      simp [hi]
    have htotal :
        0 < ∑ j : Candidate n, Real.exp (theta * value j) := by
      exact Finset.sum_pos' (fun j _ => (Real.exp_pos _).le)
        ⟨removed, Finset.mem_univ _, Real.exp_pos _⟩
    have hremainingNonempty :
        ((Finset.univ : Finset (Candidate n)).erase removed).Nonempty := by
      have hcard :
          ((Finset.univ : Finset (Candidate n)).erase removed).card = n + 1 := by
        simp [Candidate]
      exact Finset.card_pos.mp (by omega)
    have hremaining :
        0 < ∑ j ∈ (Finset.univ : Finset (Candidate n)).erase removed,
          Real.exp (theta * value j) := by
      rcases hremainingNonempty with ⟨j, hj⟩
      exact Finset.sum_pos'
        (fun k hk => (Real.exp_pos (theta * value k)).le)
        ⟨j, hj, Real.exp_pos _⟩
    have hsplit :
        (∑ j ∈ (Finset.univ : Finset (Candidate n)).erase removed,
            Real.exp (theta * value j)) +
          Real.exp (theta * value removed) =
            ∑ j : Candidate n, Real.exp (theta * value j) := by
      simpa using
        (Finset.sum_erase_add
          (s := (Finset.univ : Finset (Candidate n)))
          (f := fun j => Real.exp (theta * value j))
          (Finset.mem_univ removed))
    simp only [plackettLuceIndependentBestRemainingProb, if_neg hi]
    rw [plackettLuceChoiceProb_eq_equation7 theta value Finset.univ
      (Finset.mem_univ i)]
    rw [plackettLuceChoiceProb_eq_equation7 theta value Finset.univ
      (Finset.mem_univ removed)]
    rw [plackettLuceChoiceProb_eq_equation7 theta value
      ((Finset.univ : Finset (Candidate n)).erase removed) hiRemaining]
    have htotal' :
        0 < (∑ j ∈ (Finset.univ : Finset (Candidate n)).erase removed,
          Real.exp (theta * value j)) + Real.exp (theta * value removed) := by
      exact add_pos hremaining (Real.exp_pos _)
    rw [← hsplit]
    field_simp [ne_of_gt htotal', ne_of_gt hremaining]

/--
The expected best surviving candidate under the constructed full ranking law
is exactly equation (7) on the remaining set.
-/
theorem plackettLuceRankingPMF_expectedBestAfterRemoval_eq
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (removed : Candidate n) :
    AccuracyFamily.expectedBestAfterRemoval
        (plackettLuceRankingPMF theta value) value removed =
      plackettLuceRemainingUtility theta value removed := by
  rw [expectedBestAfterRemoval_eq_sum_bestRemainingProb]
  unfold plackettLuceRemainingUtility
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = removed
  · subst i
    have hprob :
        pmfProb (plackettLuceRankingPMF theta value)
          (fun pi => removed = bestRemainingAfter pi removed) = 0 :=
      pmfProb_eq_zero_of_no_mass _ _ (by
        intro pi hpi
        exact False.elim
          (bestRemainingAfter_ne_removed pi removed hpi.symm))
    rw [hprob]
    simp [plackettLuceChoiceProb]
  · have hroute :
        pmfProb (plackettLuceRankingPMF theta value)
            (fun pi => i = bestRemainingAfter pi removed) =
          plackettLuceIndependentBestRemainingProb
            theta value removed i := by
      rw [bestRemainingProb_eq_first_add_firstSecond
        (plackettLuceRankingPMF theta value) removed i hi]
      rw [plackettLuceRankingPMF_firstChoiceProb_eq_equation7]
      rw [plackettLuceRankingPMF_firstSecondChoiceProb_eq_equation7]
      simp [plackettLuceIndependentBestRemainingProb, hi]
    rw [hroute]
    rw [plackettLuceIndependentBestRemainingProb_eq_remainingChoice]

/-- Shared second-mover utility of the constructed ranking PMF is the equation-(7) formula. -/
theorem plackettLuceRankingPMF_expectedSecondMoverShared_eq
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    expectedSecondMoverShared (plackettLuceRankingPMF theta value) value =
      plackettLuceSecondMoverShared theta value := by
  rw [expectedSecondMoverShared_eq_sum_secondChoiceProb]
  simp_rw [secondChoiceProb_eq_sum_firstSecondChoiceProb]
  simp_rw [plackettLuceRankingPMF_firstSecondChoiceProb_eq_equation7]
  unfold plackettLuceSecondMoverShared plackettLuceRemainingUtility
  calc
    ∑ second : Candidate n,
        (∑ first : Candidate n,
          plackettLuceChoiceProb theta value Finset.univ first *
            plackettLuceChoiceProb theta value
              ((Finset.univ : Finset (Candidate n)).erase first) second) *
          value second
        = ∑ second : Candidate n, ∑ first : Candidate n,
            (plackettLuceChoiceProb theta value Finset.univ first *
              plackettLuceChoiceProb theta value
                ((Finset.univ : Finset (Candidate n)).erase first) second) *
              value second := by
            refine Finset.sum_congr rfl ?_
            intro second _
            rw [Finset.sum_mul]
    _ = ∑ first : Candidate n, ∑ second : Candidate n,
          (plackettLuceChoiceProb theta value Finset.univ first *
            plackettLuceChoiceProb theta value
              ((Finset.univ : Finset (Candidate n)).erase first) second) *
            value second := by
          exact Finset.sum_comm
    _ = ∑ first : Candidate n,
          plackettLuceChoiceProb theta value Finset.univ first *
            ∑ second : Candidate n,
              plackettLuceChoiceProb theta value
                ((Finset.univ : Finset (Candidate n)).erase first) second *
                value second := by
          refine Finset.sum_congr rfl ?_
          intro first _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro second _
          ring

/-- Independent second-mover utility of the constructed ranking PMF is the same formula. -/
theorem plackettLuceRankingPMF_expectedSecondMoverIndependent_eq
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent
        (plackettLuceRankingPMF theta value)
        (plackettLuceRankingPMF theta value) value =
      plackettLuceSecondMoverShared theta value := by
  rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
  change expectedFirstMoverUtility (plackettLuceRankingPMF theta value)
      (fun removed => AccuracyFamily.expectedBestAfterRemoval
        (plackettLuceRankingPMF theta value) value removed) = _
  rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb]
  simp_rw [plackettLuceRankingPMF_firstChoiceProb_eq_equation7]
  simp_rw [plackettLuceRankingPMF_expectedBestAfterRemoval_eq]
  rfl

/--
The paper's actual `U_AH(theta,theta)=U_AA(theta,theta)` equality for the
constructed full Plackett--Luce ranking PMF.
-/
theorem plackettLuceRankingPMF_independent_eq_shared
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent
        (plackettLuceRankingPMF theta value)
        (plackettLuceRankingPMF theta value) value =
      expectedSecondMoverShared
        (plackettLuceRankingPMF theta value) value := by
  rw [plackettLuceRankingPMF_expectedSecondMoverIndependent_eq]
  rw [plackettLuceRankingPMF_expectedSecondMoverShared_eq]

/-- The actual full-ranking independent-reranking effect is zero. -/
theorem plackettLuceRankingPMF_independentRerankingEffect_eq_zero
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent
          (plackettLuceRankingPMF theta value)
          (plackettLuceRankingPMF theta value) value -
        expectedSecondMoverShared
          (plackettLuceRankingPMF theta value) value = 0 := by
  rw [plackettLuceRankingPMF_independent_eq_shared]
  ring

/-- Independent-reranking utility computed from the two disjoint first-choice routes above. -/
noncomputable def plackettLuceSecondMoverIndependent {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) : ℝ :=
  ∑ first : Candidate n,
    plackettLuceChoiceProb theta value Finset.univ first *
      (∑ i : Candidate n,
        plackettLuceIndependentBestRemainingProb
          theta value first i * value i)

/-- Under Plackett--Luce IIA, shared and independent second-mover utility coincide. -/
theorem plackettLuceSecondMoverIndependent_eq_shared {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) :
    plackettLuceSecondMoverIndependent theta value =
      plackettLuceSecondMoverShared theta value := by
  unfold plackettLuceSecondMoverIndependent plackettLuceSecondMoverShared
    plackettLuceRemainingUtility
  apply Finset.sum_congr rfl
  intro first _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [plackettLuceIndependentBestRemainingProb_eq_remainingChoice]

/-- The paper's independent-reranking effect is exactly zero for Plackett--Luce. -/
theorem plackettLuce_independentRerankingEffect_eq_zero {n : ℕ} (theta : ℝ)
    (value : Candidate n → ℝ) :
    plackettLuceSecondMoverIndependent theta value -
      plackettLuceSecondMoverShared theta value = 0 := by
  rw [plackettLuceSecondMoverIndependent_eq_shared]
  ring

end KR21Monoculture

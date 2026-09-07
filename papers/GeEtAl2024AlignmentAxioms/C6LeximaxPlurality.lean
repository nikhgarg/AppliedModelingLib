import GeEtAl2024AlignmentAxioms.C5ParetoKemeny
import GeEtAl2024AlignmentAxioms.LCPO

/-!
# Theorem C.6 source interface: fixed-tie Leximax Plurality

The source's sequential rule chooses, at each position, a feasible extension
whose candidate has the largest plurality score.  The paper leaves score ties
implicit.  A profile-independent lower-candidate-index tie break makes this a
genuine rule and is necessary for the winner-monotonicity conclusion.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking
open scoped BigOperators

/-- Number of voters who put a candidate in first position. -/
noncomputable def pluralityScore {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (candidate : Candidate n) : ℕ :=
  ∑ voter, if firstChoice (profile voter) = candidate then 1 else 0

/-- The plurality sum is the cardinality of the voters naming that candidate first. -/
theorem pluralityScore_eq_votersSatisfying_card {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (candidate : Candidate n) :
    pluralityScore profile candidate =
      (votersSatisfying (fun voter => firstChoice (profile voter) = candidate)).card := by
  unfold pluralityScore votersSatisfying
  simp only [Finset.sum_boole, Nat.cast_id]

/-- The source's plurality comparison with a fixed lower-index-first tie break. -/
def PluralityBetter {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) : Prop :=
  pluralityScore profile second < pluralityScore profile first ∨
    (pluralityScore profile first = pluralityScore profile second ∧ first < second)

/-- A feasible ranking can put a candidate at a position while retaining a selected prefix. -/
def CanFeasiblyPlaceAt {n : ℕ} (feasible : Ranking n → Prop)
    (selectedPrefix : Ranking n) (position candidate : Candidate n) : Prop :=
  ∃ contender, feasible contender ∧ AgreesBefore selectedPrefix contender position ∧
    contender position = candidate

/-- A fixed-tie sequential Leximax-Plurality outcome. -/
def IsFixedTieLeximaxPluralityOutcome {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n)
    (outcome : Ranking n) : Prop :=
  feasible outcome ∧
    ∀ position candidate,
      CanFeasiblyPlaceAt feasible outcome position candidate →
        ¬ PluralityBetter profile candidate (outcome position)

/-- A rule follows the fixed-tie sequential plurality condition on each feasible profile. -/
def IsFixedTieLeximaxPluralitySelector {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ profile, IsFixedTieLeximaxPluralityOutcome feasible profile (rule.run profile)

/-- Plurality comparison is a strict total order on distinct candidates. -/
theorem pluralityBetter_or_reverse_of_ne {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) {first second : Candidate n} (hdistinct : first ≠ second) :
    PluralityBetter profile first second ∨ PluralityBetter profile second first := by
  unfold PluralityBetter
  rcases lt_trichotomy (pluralityScore profile first) (pluralityScore profile second) with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · rcases lt_or_gt_of_ne (by simpa [heq] using hdistinct) with hfirst | hsecond
    · exact Or.inl (Or.inr ⟨heq, hfirst⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hsecond⟩)
  · exact Or.inl (Or.inl hgt)

/-- The fixed plurality comparison cannot hold in both directions. -/
theorem not_pluralityBetter_reverse {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) :
    ¬ (PluralityBetter profile first second ∧ PluralityBetter profile second first) := by
  intro hboth
  rcases hboth.1 with hscore | ⟨heq, hindex⟩
  · rcases hboth.2 with hreverse | ⟨hreverse, _⟩
    · exact (lt_asymm hscore) hreverse
    · exact (ne_of_lt hscore) hreverse
  · rcases hboth.2 with hreverse | ⟨hreverse, hreverseIndex⟩
    · exact (ne_of_lt hreverse) heq
    · exact (lt_asymm hindex) hreverseIndex

/-- A submitted first-place vote can be used as a feasible first-position extension. -/
theorem canFeasiblyPlaceAt_zero_of_submittedRanking
    {Voter : Type*} {n : ℕ} (feasible : Ranking n → Prop)
    (profile : RankingProfile Voter n) (hprofile : FeasibleProfile feasible profile)
    (selectedPrefix : Ranking n) (voter : Voter) (candidate : Candidate n)
    (hfirst : firstChoice (profile voter) = candidate) :
    CanFeasiblyPlaceAt feasible selectedPrefix 0 candidate := by
  refine ⟨profile voter, hprofile voter, ?_, ?_⟩
  · intro earlier hearlier
    exact False.elim ((Nat.not_lt_zero earlier.val) hearlier)
  · simpa [firstChoice] using hfirst

/-- Strict-majority first-place support gives a strictly larger plurality score. -/
theorem pluralityScore_lt_of_majorityTopChoice
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) {candidate other : Candidate n}
    (hmajority : MajorityTopChoice profile candidate) (hother : other ≠ candidate) :
    pluralityScore profile other < pluralityScore profile candidate := by
  classical
  rw [pluralityScore_eq_votersSatisfying_card,
    pluralityScore_eq_votersSatisfying_card]
  change (Finset.univ.filter (fun voter => firstChoice (profile voter) = other)).card <
    (Finset.univ.filter (fun voter => firstChoice (profile voter) = candidate)).card
  change Fintype.card Voter <
    2 * (Finset.univ.filter (fun voter => firstChoice (profile voter) = candidate)).card at hmajority
  have hsubset :
      Finset.univ.filter (fun voter => firstChoice (profile voter) = other) ⊆
        Finset.univ.filter (fun voter => ¬ firstChoice (profile voter) = candidate) := by
    intro voter hvoter
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvoter ⊢
    intro hcandidate
    exact hother (hvoter.symm.trans hcandidate)
  have hother_le :
      (Finset.univ.filter (fun voter => firstChoice (profile voter) = other)).card ≤
        (Finset.univ.filter (fun voter => ¬ firstChoice (profile voter) = candidate)).card :=
    Finset.card_le_card hsubset
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Voter)) (fun voter => firstChoice (profile voter) = candidate)
  rw [Finset.card_univ] at hpartition
  omega

/-- Plurality scores add under literal concatenation of voter profiles. -/
theorem pluralityScore_append {n leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n) (candidate : Candidate n) :
    pluralityScore (rankingProfileAppend left right) candidate =
      pluralityScore left candidate + pluralityScore right candidate := by
  unfold pluralityScore rankingProfileAppend
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]

/-- The sequential fixed-tie condition determines a unique complete ranking. -/
theorem isFixedTieLeximaxPluralityOutcome_unique
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n)
    (outcome reference : Ranking n)
    (houtcome : IsFixedTieLeximaxPluralityOutcome feasible profile outcome)
    (hreference : IsFixedTieLeximaxPluralityOutcome feasible profile reference) :
    outcome = reference := by
  classical
  by_contra hne
  let differing : Finset (Candidate n) :=
    Finset.univ.filter (fun position => outcome position ≠ reference position)
  have hexists : ∃ position, outcome position ≠ reference position := by
    by_contra hnone
    push Not at hnone
    apply hne
    ext position
    exact congrArg Fin.val (hnone position)
  obtain ⟨witness, hwitness⟩ := hexists
  have hdiffering : differing.Nonempty := by
    refine ⟨witness, ?_⟩
    simp only [differing, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hwitness
  let position : Candidate n := differing.min' hdiffering
  have hpositionMem : position ∈ differing := Finset.min'_mem differing hdiffering
  have hpositionDiff : outcome position ≠ reference position := by
    simpa only [differing, Finset.mem_filter, Finset.mem_univ, true_and] using hpositionMem
  have hprefix : ∀ earlier : Candidate n, earlier < position →
      outcome earlier = reference earlier := by
    intro earlier hearlier
    by_contra hdiff
    have hearlierMem : earlier ∈ differing := by
      simp only [differing, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdiff
    have hposition_le : position ≤ earlier := Finset.min'_le differing earlier hearlierMem
    exact (not_le_of_gt hearlier) hposition_le
  have hreferenceCanPlace :
      CanFeasiblyPlaceAt feasible outcome position (reference position) :=
    ⟨reference, hreference.1, fun earlier hearlier => (hprefix earlier hearlier).symm, rfl⟩
  have houtcomeCanPlace :
      CanFeasiblyPlaceAt feasible reference position (outcome position) :=
    ⟨outcome, houtcome.1, hprefix, rfl⟩
  rcases pluralityBetter_or_reverse_of_ne profile hpositionDiff with hreferenceBetter | houtcomeBetter
  · exact hreference.2 position (outcome position) houtcomeCanPlace hreferenceBetter
  · exact houtcome.2 position (reference position) hreferenceCanPlace houtcomeBetter

/-- If neither component profile prefers a candidate under plurality, neither does their sum. -/
theorem not_pluralityBetter_append_of_not_component
    {n leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n)
    (candidate selected : Candidate n)
    (hleft : ¬ PluralityBetter left candidate selected)
    (hright : ¬ PluralityBetter right candidate selected) :
    ¬ PluralityBetter (rankingProfileAppend left right) candidate selected := by
  intro hcombined
  have hleftScore : pluralityScore left candidate ≤ pluralityScore left selected := by
    exact Nat.le_of_not_gt (fun hgt => hleft (Or.inl hgt))
  have hrightScore : pluralityScore right candidate ≤ pluralityScore right selected := by
    exact Nat.le_of_not_gt (fun hgt => hright (Or.inl hgt))
  unfold PluralityBetter at hcombined
  rw [pluralityScore_append, pluralityScore_append] at hcombined
  rcases hcombined with hstrict | ⟨hequal, hindex⟩
  · exact (not_lt_of_ge (Nat.add_le_add hleftScore hrightScore)) hstrict
  · apply hleft
    right
    refine ⟨?_, hindex⟩
    omega

/-- The fixed-tie sequential plurality rule satisfies ranking separability. -/
theorem fixedTieLeximaxPluralitySelector_rankingSeparability {n : ℕ}
    (feasible : Ranking n → Prop)
    (rule : ∀ voterCount : ℕ, LinearRankAggregationRule (Fin voterCount) n feasible)
    (hselector : ∀ voterCount : ℕ,
      IsFixedTieLeximaxPluralitySelector feasible (rule voterCount)) :
    RankingSeparability feasible rule := by
  intro leftCount rightCount left right hequal
  let output := (rule leftCount).run left
  let combinedOutput := (rule (leftCount + rightCount)).run
    (rankingProfileAppend left right)
  have hleft := hselector leftCount left
  have hright := hselector rightCount right
  have hrightOutput : IsFixedTieLeximaxPluralityOutcome feasible right output := by
    simpa only [output] using hequal ▸ hright
  have hcombined := hselector (leftCount + rightCount) (rankingProfileAppend left right)
  have houtputCombined : IsFixedTieLeximaxPluralityOutcome feasible
      (rankingProfileAppend left right) output := by
    refine ⟨hleft.1, ?_⟩
    intro position candidate hcanPlace
    exact not_pluralityBetter_append_of_not_component left right candidate (output position)
      (hleft.2 position candidate hcanPlace) (hrightOutput.2 position candidate hcanPlace)
  have houtput_eq_combined : output = combinedOutput :=
    isFixedTieLeximaxPluralityOutcome_unique feasible
      (rankingProfileAppend left right) output combinedOutput houtputCombined hcombined
  simpa only [output, combinedOutput] using houtput_eq_combined.symm

/-- A candidate at rank zero is exactly the first choice. -/
theorem firstChoice_eq_of_rankOf_eq_zero {n : ℕ}
    (ranking : Ranking n) (candidate : Candidate n)
    (hrank : rankOf ranking candidate = 0) :
    firstChoice ranking = candidate := by
  change ranking 0 = candidate
  calc
    ranking 0 = ranking (rankOf ranking candidate) := congrArg ranking hrank.symm
    _ = candidate := ranking.apply_symm_apply _

/-- Elevating a candidate preserves its first-place votes. -/
theorem firstChoice_eq_candidate_of_profileElevatesCandidate
    {n : ℕ} (original updated : Ranking n) (candidate : Candidate n)
    (helevates : ElevatesCandidate original updated candidate)
    (hfirst : firstChoice original = candidate) :
    firstChoice updated = candidate := by
  have horiginalRank : rankOf original candidate = 0 := by
    rw [← hfirst]
    exact rankOf_firstChoice original
  have hupdatedRank : rankOf updated candidate = 0 := by
    have hle : rankOf updated candidate ≤ 0 := by
      rw [← horiginalRank]
      exact helevates.1
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero hle
  exact firstChoice_eq_of_rankOf_eq_zero updated candidate hupdatedRank

/-- An elevation cannot create a first-place vote for a distinct candidate. -/
theorem firstChoice_eq_of_profileElevatesCandidate_other
    {n : ℕ} (original updated : Ranking n) (candidate other : Candidate n)
    (helevates : ElevatesCandidate original updated candidate)
    (hother : other ≠ candidate)
    (hupdated : firstChoice updated = other) :
    firstChoice original = other := by
  by_contra hnot
  let prior := firstChoice original
  have hprior_ne_other : prior ≠ other := by
    intro heq
    apply hnot
    simpa [prior] using heq
  by_cases hprior_candidate : prior = candidate
  · have hpriorFirst : firstChoice original = candidate := by
      simpa [prior] using hprior_candidate
    have hupdatedFirst : firstChoice updated = candidate :=
      firstChoice_eq_candidate_of_profileElevatesCandidate original updated candidate helevates hpriorFirst
    exact hother (hupdated.symm.trans hupdatedFirst)
  · have hstrictOriginal : StrictlyPrefers original prior other := by
      apply strictlyPrefers_firstChoice_of_ne original
      simpa [prior] using hprior_ne_other.symm
    have hstrictUpdated : StrictlyPrefers updated prior other :=
      (helevates.2 prior other hprior_candidate hother).mp hstrictOriginal
    have hreverseUpdated : StrictlyPrefers updated other prior := by
      rw [← hupdated]
      have hprior_ne_updatedFirst : prior ≠ firstChoice updated := by
        rw [hupdated]
        exact hprior_ne_other
      exact strictlyPrefers_firstChoice_of_ne updated hprior_ne_updatedFirst
    exact (lt_asymm hstrictUpdated) hreverseUpdated

/-- Elevating a candidate weakly increases its plurality score. -/
theorem pluralityScore_le_of_profileElevatesCandidate
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (original updated : RankingProfile Voter n) (voter : Voter) (candidate : Candidate n)
    (helevates : ProfileElevatesCandidate original updated voter candidate) :
    pluralityScore original candidate ≤ pluralityScore updated candidate := by
  classical
  rw [pluralityScore_eq_votersSatisfying_card, pluralityScore_eq_votersSatisfying_card]
  apply Finset.card_le_card
  intro individual hindividual
  simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and] at hindividual ⊢
  by_cases hsame : individual = voter
  · subst individual
    exact firstChoice_eq_candidate_of_profileElevatesCandidate
      (original voter) (updated voter) candidate helevates.1 hindividual
  · rw [helevates.2 individual hsame]
    exact hindividual

/-- Elevating a candidate weakly decreases every distinct candidate's plurality score. -/
theorem pluralityScore_after_le_of_profileElevatesCandidate_other
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (original updated : RankingProfile Voter n) (voter : Voter)
    (candidate other : Candidate n)
    (helevates : ProfileElevatesCandidate original updated voter candidate)
    (hother : other ≠ candidate) :
    pluralityScore updated other ≤ pluralityScore original other := by
  classical
  rw [pluralityScore_eq_votersSatisfying_card, pluralityScore_eq_votersSatisfying_card]
  apply Finset.card_le_card
  intro individual hindividual
  simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and] at hindividual ⊢
  by_cases hsame : individual = voter
  · subst individual
    exact firstChoice_eq_of_profileElevatesCandidate_other
      (original voter) (updated voter) candidate other helevates.1 hother hindividual
  · rw [← helevates.2 individual hsame]
    exact hindividual

/-- A plurality advantage after an elevation was already an advantage before it. -/
theorem pluralityBetter_original_of_profileElevatesCandidate
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (original updated : RankingProfile Voter n) (voter : Voter)
    (candidate other : Candidate n)
    (helevates : ProfileElevatesCandidate original updated voter candidate)
    (hother : other ≠ candidate)
    (hbetter : PluralityBetter updated other candidate) :
    PluralityBetter original other candidate := by
  have hcandidateScore : pluralityScore original candidate ≤ pluralityScore updated candidate :=
    pluralityScore_le_of_profileElevatesCandidate original updated voter candidate helevates
  have hotherScore : pluralityScore updated other ≤ pluralityScore original other :=
    pluralityScore_after_le_of_profileElevatesCandidate_other
      original updated voter candidate other helevates hother
  unfold PluralityBetter at hbetter ⊢
  rcases hbetter with hstrict | ⟨hequal, hindex⟩
  · exact Or.inl (lt_of_lt_of_le (lt_of_le_of_lt hcandidateScore hstrict) hotherScore)
  · have hweak : pluralityScore original candidate ≤ pluralityScore original other := by
      calc
        pluralityScore original candidate ≤ pluralityScore updated candidate := hcandidateScore
        _ = pluralityScore updated other := hequal.symm
        _ ≤ pluralityScore original other := hotherScore
    rcases lt_or_eq_of_le hweak with hstrict | hequal
    · exact Or.inl hstrict
    · exact Or.inr ⟨hequal.symm, hindex⟩

/-- The fixed-tie sequential plurality rule is majority consistent. -/
theorem fixedTieLeximaxPluralitySelector_majorityConsistent
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible)
    (hselector : IsFixedTieLeximaxPluralitySelector feasible rule) :
    MajorityConsistent feasible rule := by
  intro profile candidate hprofile hmajority
  have houtcome := hselector profile
  obtain ⟨voter, hvoter⟩ :=
    exists_submittedRanking_firstChoice_of_majorityTopChoice profile candidate hmajority
  have hcanPlace : CanFeasiblyPlaceAt feasible (rule.run profile) 0 candidate :=
    canFeasiblyPlaceAt_zero_of_submittedRanking feasible profile hprofile
      (rule.run profile) voter candidate hvoter
  by_contra hnot
  let other := firstChoice (rule.run profile)
  have hother : other ≠ candidate := by
    intro heq
    apply hnot
    simpa [other] using heq
  have hbetter : PluralityBetter profile candidate other :=
    Or.inl (pluralityScore_lt_of_majorityTopChoice profile hmajority hother)
  exact houtcome.2 0 candidate hcanPlace (by simpa [other, firstChoice] using hbetter)

/-- The fixed-tie sequential plurality rule is winner monotonic. -/
theorem fixedTieLeximaxPluralitySelector_winnerMonotonic
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible)
    (hselector : IsFixedTieLeximaxPluralitySelector feasible rule) :
    WinnerMonotonic feasible rule := by
  intro original updated voter candidate horiginal hupdated hfirst helevates
  have horiginalOutcome := hselector original
  have hupdatedOutcome := hselector updated
  by_contra hnot
  let other := firstChoice (rule.run updated)
  have hother : other ≠ candidate := by
    intro heq
    apply hnot
    simpa [other] using heq
  have hcandidateCanPlaceUpdated :
      CanFeasiblyPlaceAt feasible (rule.run updated) 0 candidate :=
    ⟨rule.run original, horiginalOutcome.1, by
      intro earlier hearlier
      exact False.elim ((Nat.not_lt_zero earlier.val) hearlier), by
      simpa [firstChoice] using hfirst⟩
  have hbetterUpdated : PluralityBetter updated other candidate := by
    rcases pluralityBetter_or_reverse_of_ne updated hother with hotherBetter | hcandidateBetter
    · exact hotherBetter
    · exact False.elim (hupdatedOutcome.2 0 candidate hcandidateCanPlaceUpdated
        (by simpa [other, firstChoice] using hcandidateBetter))
  have hbetterOriginal : PluralityBetter original other candidate :=
    pluralityBetter_original_of_profileElevatesCandidate
      original updated voter candidate other helevates hother hbetterUpdated
  have hotherCanPlaceOriginal :
      CanFeasiblyPlaceAt feasible (rule.run original) 0 other :=
    ⟨rule.run updated, hupdatedOutcome.1, by
      intro earlier hearlier
      exact False.elim ((Nat.not_lt_zero earlier.val) hearlier), by
      simp [other]⟩
  exact horiginalOutcome.2 0 other hotherCanPlaceOriginal
    (by
      change PluralityBetter original other (firstChoice (rule.run original))
      rw [hfirst]
      exact hbetterOriginal)

end GeEtAl2024AlignmentAxioms

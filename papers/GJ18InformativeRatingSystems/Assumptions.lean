import GJ18InformativeRatingSystems.MainTheorems

/-!
# Paper Assumptions: GJ18 Informative Rating Systems

This file separates predicates stated by the source model from additional
regularity conditions needed by a finite-support large-deviation proof.  In
particular, the displayed strict decrease of cumulative tails is recorded only
between adjacent displayed rating cutoffs; it does not fabricate a cutoff above
the terminal rating.
-/

namespace GJ18InformativeRatingSystems

open AppliedModelingLib.Probability

/-- Sellers receive positive asymptotic match/sample rates. -/
-- audit-premise: hgHi : 0 < sampleRate hi
-- audit-premise: hgLo : 0 < sampleRate lo
-- audit-premise: hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ
abbrev assumption_positive_match_rates {Seller : Type*}
    (sampleRate : Seller → ℝ) : Prop :=
  ∀ θ : Seller, 0 < sampleRate θ

/-- Source model: every seller's match rate is nonnegative. -/
abbrev source_nonnegative_match_rates {Seller : Type*}
    (sampleRate : Seller → ℝ) : Prop :=
  ∀ θ : Seller, 0 ≤ sampleRate θ

/-- Source model: match rates are nondecreasing in the ordered seller type. -/
abbrev source_monotone_match_rates {n : ℕ}
    (sampleRate : Fin n → ℝ) : Prop :=
  Monotone sampleRate

/--
Source schedule condition: a seller has at most one new match in each unit
period.  The count itself remains the source formula
`floorSampleCount sampleRate theta k = floor (k * sampleRate theta)`.
-/
abbrev source_at_most_one_match_per_period {Seller : Type*}
    (sampleRate : Seller → ℝ) : Prop :=
  ∀ θ : Seller, ∀ k : ℕ,
    floorSampleCount sampleRate θ (k + 1) = floorSampleCount sampleRate θ k ∨
      floorSampleCount sampleRate θ (k + 1) = floorSampleCount sampleRate θ k + 1

/-- The source's ordered finite-chain match-rate and one-match schedule model. -/
abbrev source_match_schedule_coherence {n : ℕ}
    (sampleRate : Fin n → ℝ) : Prop :=
  source_nonnegative_match_rates sampleRate ∧
    source_monotone_match_rates sampleRate ∧
      source_at_most_one_match_per_period sampleRate

/-- Source model: rating scores take values in the displayed interval `[0, 1]`. -/
abbrev source_rating_scores_in_unit_interval {Rating : Type*}
    (score : Rating → ℝ) : Prop :=
  ∀ r : Rating, 0 ≤ score r ∧ score r ≤ 1

/-- Source model: the displayed rating score is strictly increasing. -/
abbrev source_strictly_increasing_rating_scores {Rating : Type*} [Preorder Rating]
    (score : Rating → ℝ) : Prop :=
  StrictMono score

/-- Proof-route consequence of a strictly increasing score on a linear rating order. -/
theorem assumption_monotone_rating_scores_of_source_strictly_increasing
    {Rating : Type*} [LinearOrder Rating] (score : Rating → ℝ)
    (hstrict : source_strictly_increasing_rating_scores score) :
    Monotone score :=
  hstrict.monotone

/-- A weak score-order condition used by finite comparison lemmas. -/
-- audit-premise: hscore_mono : Monotone M.score
abbrev assumption_monotone_rating_scores {Rating : Type*} [Preorder Rating]
    (score : Rating → ℝ) : Prop :=
  Monotone score

/--
Higher seller types weakly dominate lower types at every upper-tail cutoff.
This is the finite ordinal form of the source condition that the cumulative
rating mass `R(theta, y | Y)` increases with seller quality.
-/
-- audit-premise: htail : ∀ p : finiteChainOrderedPair n, ∀ t : Fin (m + 1), AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairLo p)) (fun r => t ≤ r) ≤ AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairHi p)) (fun r => t ≤ r)
abbrev assumption_ordinal_rating_tail_dominance
    {n m : ℕ}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))) : Prop :=
  ∀ p : finiteChainOrderedPair n, ∀ t : Fin (m + 1),
    AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairLo p))
        (fun r => t ≤ r) ≤
      AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairHi p))
        (fun r => t ≤ r)

/--
The upper-tail probability at a displayed finite ordinal cutoff.  This name is
used so source-tail predicates remain semantic rather than depending on the
names of downstream proof functions.
-/
noncomputable def sourceOrdinalUpperTail
    {Seller : Type*} {m : ℕ}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1)))
    (θ : Seller) (t : Fin (m + 1)) : ℝ :=
  AppliedModelingLib.pmfProb (M.typeLaw θ) (fun y => t ≤ y)

/--
Literal source-tail contract: for each pair of adjacent *displayed* cutoffs,
the cumulative tail strictly decreases.  Its index `r : Fin m` deliberately
omits the terminal rating, because the source has no displayed cutoff above it.
-/
abbrev source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
    {Seller : Type*} {m : ℕ}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1)))
    : Prop :=
  ∀ θ : Seller, ∀ r : Fin m,
    sourceOrdinalUpperTail M θ (Fin.succ r) <
      sourceOrdinalUpperTail M θ (Fin.castSucc r)

/-- The source's strict adjacent-tail condition gives positive mass at each nonterminal rating. -/
theorem mass_pos_of_source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
    {Seller : Type*} {m : ℕ}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1)))
    (hstrict : source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs M)
    (θ : Seller) (r : Fin m) :
    0 < (M.typeLaw θ (Fin.castSucc r)).toReal := by
  classical
  have htail := hstrict θ r
  unfold sourceOrdinalUpperTail at htail
  have hsubset :
      ∀ y : Fin (m + 1), Fin.succ r ≤ y → Fin.castSucc r ≤ y := by
    intro y hy
    exact (Fin.castSucc_le_succ r).trans hy
  have hsplit :=
    AppliedModelingLib.pmfProb_eq_add_diff_of_imp (M.typeLaw θ)
      (fun y : Fin (m + 1) => Fin.succ r ≤ y)
      (fun y : Fin (m + 1) => Fin.castSucc r ≤ y)
      hsubset
  have hresidual :
      AppliedModelingLib.pmfProb (M.typeLaw θ)
          (fun y : Fin (m + 1) =>
            Fin.castSucc r ≤ y ∧ ¬ (Fin.succ r ≤ y)) =
        AppliedModelingLib.pmfProb (M.typeLaw θ) (fun y => y = Fin.castSucc r) := by
    apply AppliedModelingLib.pmfProb_congr
    intro y
    constructor
    · intro hy
      apply le_antisymm
      · rcases Fin.succ_le_or_le_castSucc y r with hsucc | hle
        · exact False.elim (hy.2 hsucc)
        · exact hle
      · exact hy.1
    · intro hy
      subst y
      constructor
      · exact le_rfl
      · exact not_le_of_gt r.castSucc_lt_succ
  have hresidual_pos :
      0 < AppliedModelingLib.pmfProb (M.typeLaw θ)
        (fun y : Fin (m + 1) =>
          Fin.castSucc r ≤ y ∧ ¬ (Fin.succ r ≤ y)) := by
    rw [hsplit] at htail
    linarith
  rw [hresidual, AppliedModelingLib.pmfProb_singleton] at hresidual_pos
  exact hresidual_pos

/-- The bottom displayed cutoff has upper-tail probability one for every finite rating law. -/
theorem sourceOrdinalUpperTail_zero
    {Seller : Type*} {m : ℕ}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1))) (θ : Seller) :
    sourceOrdinalUpperTail M θ 0 = 1 := by
  calc
    sourceOrdinalUpperTail M θ 0 =
        AppliedModelingLib.pmfProb (M.typeLaw θ) (fun _ : Fin (m + 1) => True) := by
      unfold sourceOrdinalUpperTail
      apply AppliedModelingLib.pmfProb_congr
      intro y
      simp
    _ = 1 := by
      unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp
      simpa using AppliedModelingLib.pmfToRealSum (M.typeLaw θ)

/--
Author-approved corrected ordinal quality condition: a higher seller has a
strictly larger upper tail at every nonbottom displayed cutoff. Strictness at
cutoff zero is intentionally excluded, since that tail is always one; the
pinned archive's all-cutoff wording is recorded separately as a fidelity delta.
-/
abbrev source_strict_ordinal_quality_tail_increase_above_bottom
    {n m : ℕ}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))) : Prop :=
  ∀ p : finiteChainOrderedPair n, ∀ t : Fin (m + 1), 0 < t.val →
    sourceOrdinalUpperTail M (finiteChainOrderedPairLo p) t <
      sourceOrdinalUpperTail M (finiteChainOrderedPairHi p) t

/-- The strict source-quality tails above zero entail the weak tail FOSD used downstream. -/
theorem assumption_ordinal_rating_tail_dominance_of_source_strict_quality_tails
    {n m : ℕ}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (hstrict : source_strict_ordinal_quality_tail_increase_above_bottom M) :
    assumption_ordinal_rating_tail_dominance M := by
  intro p t
  change
    sourceOrdinalUpperTail M (finiteChainOrderedPairLo p) t ≤
      sourceOrdinalUpperTail M (finiteChainOrderedPairHi p) t
  by_cases ht : t = 0
  · subst t
    rw [sourceOrdinalUpperTail_zero, sourceOrdinalUpperTail_zero]
  · have htval : t.val ≠ 0 := by
      intro hval
      apply ht
      apply Fin.ext
      simpa using hval
    exact (hstrict p t (Nat.pos_of_ne_zero htval)).le

/--
At the terminal displayed cutoff, the strict cross-type source tail condition
forces the higher seller's terminal atom to be positive.  A nontrivial rating
scale is necessary because `Fin.last 0` is the bottom cutoff.
-/
theorem mass_pos_last_of_source_strict_ordinal_quality_tail_increase_above_bottom
    {n m : ℕ}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (hstrict : source_strict_ordinal_quality_tail_increase_above_bottom M)
    (p : finiteChainOrderedPair n) (hm : 0 < m) :
    0 < (M.typeLaw (finiteChainOrderedPairHi p) (Fin.last m)).toReal := by
  classical
  have hlast_pos : 0 < (Fin.last m).val := by
    simpa using hm
  have htail := hstrict p (Fin.last m) hlast_pos
  unfold sourceOrdinalUpperTail at htail
  have hlast_event (θ : Fin n) :
      AppliedModelingLib.pmfProb (M.typeLaw θ) (fun y => Fin.last m ≤ y) =
        AppliedModelingLib.pmfProb (M.typeLaw θ) (fun y => y = Fin.last m) := by
    apply AppliedModelingLib.pmfProb_congr
    intro y
    constructor
    · intro hy
      exact le_antisymm (Fin.le_last y) hy
    · intro hy
      subst y
      exact le_rfl
  rw [hlast_event, hlast_event,
    AppliedModelingLib.pmfProb_singleton, AppliedModelingLib.pmfProb_singleton] at htail
  exact lt_of_le_of_lt ENNReal.toReal_nonneg htail

/--
Additional non-source regularity for the finite-support LDP route.  The source
adjacent-tail display does not imply mass at the terminal rating, so this must
never be presented as a source-derived condition.
-/
abbrev additional_full_support_regularization
    {Seller : Type*} {m : ℕ}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1))) : Prop :=
  M.fullSupport

/-- Eliminate the explicitly additional full-support regularity into atom positivity. -/
theorem mass_pos_of_additional_full_support_regularization
    {Seller : Type*} {m : ℕ}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1)))
    (hfull : additional_full_support_regularization M)
    (θ : Seller) (r : Fin (m + 1)) :
    0 < (M.typeLaw θ r).toReal :=
  M.mass_pos_of_fullSupport hfull θ r

/--
Proof-route score bounds with chosen extrema.  This is a convenient downstream
lemma interface, not the source's literal `[0,1]` and strict-order contract.
-/
-- audit-premise: hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r
-- audit-premise: hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh
-- audit-premise: hscore_lt : M.score rLow < M.score rHigh
abbrev assumption_score_range_and_strict_span {Rating : Type*}
    (score : Rating → ℝ) (rLow rHigh : Rating) : Prop :=
  (∀ r : Rating, score rLow ≤ score r) ∧
    (∀ r : Rating, score r ≤ score rHigh) ∧
      score rLow < score rHigh

end GJ18InformativeRatingSystems

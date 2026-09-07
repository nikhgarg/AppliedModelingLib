import FalahatgarEtAl2017MaxingRanking.CanonicalFreshPickAnchor

/-!
# Source-ranked top set for Pick-Anchor

Lemma 3 samples uniformly and needs a set of exactly `n'` arms such that each
of its members has at most `n'` strictly preferable arms.  The paper obtains
that set from the finite preference order assumed in its model.  This module
makes that construction explicit instead of accepting a top-set certificate.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The first `cutoff` slots of a source preference ranking. -/
noncomputable def pickAnchorRankingTop {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (ranking : Fin (Fintype.card Arm) → Arm) (cutoff : ℕ) : Finset Arm :=
  ((Finset.univ : Finset (Fin (Fintype.card Arm))).filter fun slot => slot.val < cutoff).image
    ranking

/-- A source preference ranking makes its finite top prefix have exactly the requested size. -/
theorem pickAnchorRankingTop_card {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking) (cutoff : ℕ)
    (hcutoff : cutoff ≤ Fintype.card Arm) :
    (pickAnchorRankingTop ranking cutoff).card = cutoff := by
  classical
  unfold pickAnchorRankingTop
  rw [Finset.card_image_of_injective _ hranking.1.1]
  simpa [Nat.min_eq_right hcutoff] using
    (Fin.card_filter_val_lt (n := Fintype.card Arm) (m := cutoff))

/--
Every arm in the source-ranked top prefix has at most `cutoff` strictly better
arms.  Strictly better arms must occupy an earlier ranking slot: otherwise
the ranking's weak order and antisymmetry contradict strict preference.
-/
theorem pickAnchorRankingTop_strictlyBetter_card_le {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (preferenceGap : Arm → Arm → ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (cutoff : ℕ) (hcutoff : cutoff ≤ Fintype.card Arm)
    (pivot : Arm) (hpivot : pivot ∈ pickAnchorRankingTop ranking cutoff) :
    (strictlyBetterArms preferenceGap pivot).card ≤ cutoff := by
  classical
  have hsubset : strictlyBetterArms preferenceGap pivot ⊆ pickAnchorRankingTop ranking cutoff := by
    intro better hbetter
    rcases Finset.mem_image.mp hpivot with ⟨pivotSlot, hpivotSlot, hpivotEq⟩
    rcases hranking.1.2 better with ⟨betterSlot, hbetterEq⟩
    have hpivotLt : pivotSlot.val < cutoff := (Finset.mem_filter.mp hpivotSlot).2
    have hbetterLt : betterSlot.val < cutoff := by
      have hslotLe : betterSlot.val ≤ pivotSlot.val := by
        by_contra hnotLe
        have hpivotBefore : pivotSlot.val ≤ betterSlot.val :=
          Nat.le_of_lt (Nat.lt_of_not_ge hnotLe)
        have hpivotWeak : 0 ≤ preferenceGap (ranking pivotSlot) (ranking betterSlot) :=
          hranking.2 pivotSlot betterSlot hpivotBefore
        have hbetterStrict : 0 < preferenceGap (ranking betterSlot) (ranking pivotSlot) := by
          simpa only [hbetterEq, hpivotEq] using (Finset.mem_filter.mp hbetter).2
        rw [hantisymmetric (ranking pivotSlot) (ranking betterSlot)] at hbetterStrict
        linarith
      exact lt_of_le_of_lt hslotLe hpivotLt
    apply Finset.mem_image.mpr
    refine ⟨betterSlot, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbetterLt⟩, ?_⟩
    exact hbetterEq
  calc
    (strictlyBetterArms preferenceGap pivot).card ≤
        (pickAnchorRankingTop ranking cutoff).card := Finset.card_le_card hsubset
    _ = cutoff := pickAnchorRankingTop_card preferenceGap ranking hranking cutoff hcutoff

/-- The source-ranked prefix discharges Pick-Anchor's top-set rank premise. -/
theorem pickAnchorRankingTop_rank_bound {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (cutoff : ℕ) (hcutoff : cutoff ≤ Fintype.card Arm) :
    PickAnchorTopSetRankBound preferenceGap (pickAnchorRankingTop ranking cutoff) cutoff := by
  intro pivot hpivot
  exact pickAnchorRankingTop_strictlyBetter_card_le preferenceGap ranking hranking hantisymmetric
    cutoff hcutoff pivot hpivot

/--
Lemma 3 for the canonical finite Bernoulli model, with its top set constructed
directly from the source preference ranking.  This removes the former
externally supplied `top` and rank-bound premises.
-/
theorem canonicalFreshPickAnchorUniform_goodAnchor_highProbability_of_preferenceRanking
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (delta epsilon : ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hepsilon : 0 < epsilon)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap) :
    1 - delta ≤ freshPickAnchorUniformGoodAnchorProbability
      cutoff delta epsilon
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample
        (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne)
        preferenceGap hprobability epsilon
        ((delta / 2) /
          (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
      preferenceGap hcutoff hdelta hdeltaLeOne := by
  apply canonicalFreshPickAnchorUniform_goodAnchor_highProbability_of_sourceSchedule
    cutoff delta epsilon (pickAnchorRankingTop ranking cutoff) preferenceGap hprobability
    hcutoff hdelta hdeltaLeOne hepsilon hantisymmetric hself hcomplete hsst
  · exact pickAnchorRankingTop_card preferenceGap ranking hranking cutoff hcutoffLeCard
  · exact pickAnchorRankingTop_rank_bound preferenceGap ranking hranking hantisymmetric cutoff
      hcutoffLeCard

end FalahatgarEtAl2017MaxingRanking

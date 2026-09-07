import FalahatgarEtAl2017MaxingRanking.PruneRetention
import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration
import AppliedModelingLib.Foundations.Probability.UniformHoeffding

/-!
# Prune size decomposition

Appendix A.6 separates the at-most-`cutoff` arms genuinely above the anchor
threshold from the bad arms that survive a round by comparison error.  This
file records that deterministic decomposition; concentration is responsible
only for bounding the latter population.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
Hoeffding's finite-population form for the bad-survivor count in one Prune
round.  The caller supplies the independent indicator family and the explicit
numeric tail check; no identical-marginal assumption is hidden here.
-/
theorem boundedIndependentSurvivalSum_exceeds_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (count : ℕ) (survival : ℕ → Ω → ℝ)
    (meanBound cutoff failure : ℝ)
    (hindependent : iIndepFun survival law)
    (hmeasurable : ∀ index, Measurable (survival index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      survival index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmeanBound : ∀ index < count, law[survival index] ≤ meanBound)
    (hcount : 0 < count)
    (hmargin : 0 ≤ cutoff - (count : ℝ) * meanBound)
    (htail : Real.exp (-((count : ℝ) *
      ((cutoff - (count : ℝ) * meanBound) / (count : ℝ))) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤ failure) :
    law.real {outcome | cutoff < ∑ index ∈ Finset.range count, survival index outcome} ≤ failure := by
  let error : ℝ := (cutoff - (count : ℝ) * meanBound) / (count : ℝ)
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have herror : 0 ≤ error := div_nonneg hmargin (le_of_lt hcountReal)
  have hsumMean :
      (∑ index ∈ Finset.range count, law[survival index]) ≤ (count : ℝ) * meanBound := by
    calc
      (∑ index ∈ Finset.range count, law[survival index]) ≤
          ∑ _index ∈ Finset.range count, meanBound := by
            apply Finset.sum_le_sum
            intro index hindex
            exact hmeanBound index (Finset.mem_range.mp hindex)
      _ = (count : ℝ) * meanBound := by simp [mul_comm]
  have hproduct : (count : ℝ) * error = cutoff - (count : ℝ) * meanBound := by
    dsimp [error]
    field_simp [ne_of_gt hcountReal]
  have hsubset :
      {outcome | cutoff < ∑ index ∈ Finset.range count, survival index outcome} ⊆
        {outcome | (count : ℝ) * error ≤
          ∑ index ∈ Finset.range count,
            (survival index outcome - law[survival index])} := by
    intro outcome hsurvives
    change cutoff < ∑ index ∈ Finset.range count, survival index outcome at hsurvives
    have hcentered :
        cutoff - (∑ index ∈ Finset.range count, law[survival index]) <
          ∑ index ∈ Finset.range count,
            (survival index outcome - law[survival index]) := by
      rw [Finset.sum_sub_distrib]
      linarith
    rw [hproduct]
    exact (sub_le_sub_left hsumMean cutoff).trans (le_of_lt hcentered)
  calc
    law.real {outcome | cutoff < ∑ index ∈ Finset.range count, survival index outcome} ≤
        law.real {outcome | (count : ℝ) * error ≤
          ∑ index ∈ Finset.range count,
            (survival index outcome - law[survival index])} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
      iidBoundedObservation_centeredSum_upperTail law survival count hindependent hmeasurable
        hbounded error herror
    _ ≤ failure := by simpa [error] using htail

/--
Finite-index Hoeffding form for a family of bad-survival indicators.  Prune
rounds are naturally indexed by the currently active bad arms, not a numeric
prefix; this theorem keeps that source indexing intact.
-/
theorem boundedIndependentSurvivalSum_exceeds_probability_finset
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (survival : Index → Ω → ℝ)
    (meanBound cutoff failure : ℝ)
    (hindependent : iIndepFun survival law)
    (hmeasurable : ∀ index, Measurable (survival index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      survival index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmeanBound : ∀ index, law[survival index] ≤ meanBound)
    (hmargin : 0 ≤ cutoff - (Fintype.card Index : ℝ) * meanBound)
    (htail : Real.exp (-(cutoff - (Fintype.card Index : ℝ) * meanBound) ^ 2 /
      (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) ≤ failure) :
    law.real {outcome | cutoff < ∑ index, survival index outcome} ≤ failure := by
  have hsumMean :
      (∑ index, law[survival index]) ≤ (Fintype.card Index : ℝ) * meanBound := by
    calc
      (∑ index, law[survival index]) ≤ ∑ _index : Index, meanBound := by
        apply Finset.sum_le_sum
        intro index _
        exact hmeanBound index
      _ = (Fintype.card Index : ℝ) * meanBound := by simp [mul_comm]
  have hsubset :
      {outcome | cutoff < ∑ index, survival index outcome} ⊆
        {outcome | cutoff - (Fintype.card Index : ℝ) * meanBound ≤
          ∑ index, (survival index outcome - law[survival index])} := by
    intro outcome hsurvives
    change cutoff < ∑ index, survival index outcome at hsurvives
    have hcentered :
        cutoff - (∑ index, law[survival index]) <
          ∑ index, (survival index outcome - law[survival index]) := by
      rw [Finset.sum_sub_distrib]
      linarith
    exact (sub_le_sub_left hsumMean cutoff).trans (le_of_lt hcentered)
  calc
    law.real {outcome | cutoff < ∑ index, survival index outcome} ≤
        law.real {outcome | cutoff - (Fintype.card Index : ℝ) * meanBound ≤
          ∑ index, (survival index outcome - law[survival index])} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(cutoff - (Fintype.card Index : ℝ) * meanBound) ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) :=
      AppliedModelingLib.Probability.boundedIIndep_centeredSum_upperTail_finset law survival
        hindependent hmeasurable hbounded _ hmargin
    _ ≤ failure := htail

/--
One Prune round has at most twice the good-anchor cutoff whenever at most that
many threshold-nonbetter arms survive.  This is the deterministic endgame in
Lemmas 14--15.
-/
theorem pruneRound_card_le_two_mul_of_goodAnchor_and_badSurvivors
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (active : Finset Arm) (decision : Arm → CompareDecision)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hbadSurvivors :
      ((pruneRound active decision).filter fun arm => preferenceGap arm anchor ≤ lower).card ≤ cutoff) :
    (pruneRound active decision).card ≤ 2 * cutoff := by
  let survivors := pruneRound active decision
  let good := active.filter fun arm => lower < preferenceGap arm anchor
  let badSurvivors := survivors.filter fun arm => preferenceGap arm anchor ≤ lower
  have hgoodCard : good.card ≤ cutoff := by
    have hsubset : good ⊆ (Finset.univ.filter fun arm => lower < preferenceGap arm anchor) := by
      intro arm harm
      simp only [good, Finset.mem_filter] at harm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, harm.2⟩
    exact (Finset.card_le_card hsubset).trans (by simpa [GoodAnchor] using hanchor)
  have hsurvivorSubset : survivors ⊆ good ∪ badSurvivors := by
    intro arm harm
    have hactive : arm ∈ active := by
      exact pruneRound_subset active decision (by simpa [survivors] using harm)
    by_cases hgood : lower < preferenceGap arm anchor
    · exact Finset.mem_union_left _ (by simpa [good] using And.intro hactive hgood)
    · have hbad : preferenceGap arm anchor ≤ lower := le_of_not_gt hgood
      exact Finset.mem_union_right _ (by simpa [badSurvivors] using And.intro harm hbad)
  calc
    (pruneRound active decision).card = survivors.card := rfl
    _ ≤ (good ∪ badSurvivors).card := Finset.card_le_card hsurvivorSubset
    _ ≤ good.card + badSurvivors.card := Finset.card_union_le _ _
    _ ≤ cutoff + cutoff := Nat.add_le_add hgoodCard (by simpa [badSurvivors, survivors] using hbadSurvivors)
    _ = 2 * cutoff := by omega

/--
The one-round size failure in Lemmas 14--15 reduces to a concentration bound
on the bad-survival indicators.  The equality hypothesis is intentionally
explicit: it is the bridge from independent comparison batches to the Prune
filter's cardinality.
-/
theorem pruneRound_card_failure_probability_of_badSurvivalIndicators
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (active : Finset Arm) (decision : Arm → CompareDecision)
    (count : ℕ) (survival : ℕ → Ω → ℝ)
    (meanBound failure : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hcard : ∀ outcome,
      (((pruneRound active decision).filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) =
        ∑ index ∈ Finset.range count, survival index outcome)
    (hindependent : iIndepFun survival law)
    (hmeasurable : ∀ index, Measurable (survival index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      survival index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmeanBound : ∀ index < count, law[survival index] ≤ meanBound)
    (hcount : 0 < count)
    (hmargin : 0 ≤ (cutoff : ℝ) - (count : ℝ) * meanBound)
    (htail : Real.exp (-((count : ℝ) *
      (((cutoff : ℝ) - (count : ℝ) * meanBound) / (count : ℝ))) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤ failure) :
    law.real {_outcome | ¬ (pruneRound active decision).card ≤ 2 * cutoff} ≤ failure := by
  have hsurvival := boundedIndependentSurvivalSum_exceeds_probability law count survival
    meanBound (cutoff : ℝ) failure hindependent hmeasurable hbounded hmeanBound
    hcount hmargin htail
  calc
    law.real {_outcome | ¬ (pruneRound active decision).card ≤ 2 * cutoff} ≤
        law.real {outcome | (cutoff : ℝ) <
          ∑ index ∈ Finset.range count, survival index outcome} := by
      refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
      intro outcome hfailure
      have hbadNotLe : ¬
          ((pruneRound active decision).filter fun arm => preferenceGap arm anchor ≤ lower).card ≤ cutoff := by
        intro hbad
        exact hfailure
          (pruneRound_card_le_two_mul_of_goodAnchor_and_badSurvivors
            preferenceGap lower cutoff anchor active decision hanchor hbad)
      have hbadLt : cutoff <
          ((pruneRound active decision).filter fun arm => preferenceGap arm anchor ≤ lower).card :=
        Nat.lt_of_not_ge hbadNotLe
      have hbadLtReal : (cutoff : ℝ) <
          (((pruneRound active decision).filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) := by
        exact_mod_cast hbadLt
      rw [hcard outcome] at hbadLtReal
      exact hbadLtReal
    _ ≤ failure := hsurvival

end FalahatgarEtAl2017MaxingRanking

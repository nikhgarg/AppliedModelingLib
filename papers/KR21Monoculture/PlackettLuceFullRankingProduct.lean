import KR21Monoculture.PlackettLuceFullRankingAtom

/-!
# Ordered product for a finite Plackett--Luce ranking atom

This is the finite combinatorial part of the exponential-race bridge.  It
turns the recursive without-replacement atom of a full ranking into the usual
product of each displayed candidate's weight divided by the total weight of
that candidate and all later displayed candidates.
-/

open AppliedModelingLib
open scoped BigOperators

namespace KR21Monoculture

noncomputable section

/-- The candidates drawn strictly before a position of a fresh list, together
with the list's initial forbidden set. -/
def freshListPrefixForbidden {α : Type*} [DecidableEq α] {k : ℕ}
    (forbidden : Finset α) (sample : finiteFreshList α k forbidden)
    (position : Fin k) : Finset α :=
  forbidden ∪ (Finset.univ.filter fun i : Fin k => i < position).image sample.1

/-- The denominator in the standard displayed-order Plackett--Luce product. -/
def fullRankingSuffixWeight {n : ℕ} (baseWeight : Candidate n → ℝ)
    (ranking : Ranking n) (position : Candidate n) : ℝ :=
  (Finset.univ.filter fun i : Candidate n => position ≤ i).sum
    (fun i => baseWeight (ranking i))

/-- The standard ordered product for a full Plackett--Luce ranking atom. -/
def fullRankingOrderedAtomWeight {n : ℕ} (baseWeight : Candidate n → ℝ)
    (ranking : Ranking n) : ℝ :=
  ∏ position : Candidate n,
    baseWeight (ranking position) /
      fullRankingSuffixWeight baseWeight ranking position

private theorem freshListPrefixForbidden_succ
    {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α} (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden))
    (position : Fin k) :
    freshListPrefixForbidden (insert head.1 forbidden) tail position =
      freshListPrefixForbidden forbidden (finiteFreshListCons head tail) position.succ := by
  ext a
  simp only [freshListPrefixForbidden, Finset.mem_union, Finset.mem_insert,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hinsert | ⟨i, hi, htail⟩)
    · rcases hinsert with rfl | hforbidden
      · right
        refine ⟨0, Fin.succ_pos position, ?_⟩
        exact finiteFreshListCons_zero head tail
      · exact Or.inl hforbidden
    · right
      refine ⟨i.succ, Fin.succ_lt_succ_iff.mpr hi, ?_⟩
      simpa using htail
  · rintro (hforbidden | ⟨i, hi, hsample⟩)
    · exact Or.inl (Or.inr hforbidden)
    · cases i using Fin.cases with
      | zero =>
          exact Or.inl (Or.inl (by simpa using hsample.symm))
      | succ i =>
          exact Or.inr ⟨i, Fin.succ_lt_succ_iff.mp hi, by simpa using hsample⟩

/-- The recursive without-replacement atom is the product of the conditional
draw factors associated with the preceding entries of its fresh list. -/
theorem finiteFreshListAtomWeight_eq_prefixProduct
    {α : Type*} [Fintype α] [DecidableEq α] (baseWeight : α → ℝ) :
    ∀ {k : ℕ} (forbidden : Finset α) (sample : finiteFreshList α k forbidden),
      finiteFreshListAtomWeight baseWeight forbidden sample =
        ∏ position : Fin k,
          baseWeight (sample.1 position) /
            finiteAvailableWeight baseWeight
              (freshListPrefixForbidden forbidden sample position)
  | 0, forbidden, sample => by
      rw [Fin.prod_univ_zero]
      simp [finiteFreshListAtomWeight]
  | k + 1, forbidden, sample => by
      classical
      let head : {a // a ∉ forbidden} :=
        ⟨sample.1 0, sample.2.2 0⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      have hreassemble : finiteFreshListCons head tail = sample := by
        exact finiteFreshListCons_tailOfHead sample head rfl
      have htail :=
        finiteFreshListAtomWeight_eq_prefixProduct baseWeight
          (insert head.1 forbidden) tail
      calc
        finiteFreshListAtomWeight baseWeight forbidden sample =
            (baseWeight head.1 / finiteAvailableWeight baseWeight forbidden) *
              finiteFreshListAtomWeight baseWeight (insert head.1 forbidden) tail := by
                simp [finiteFreshListAtomWeight, head, tail]
        _ = (baseWeight head.1 / finiteAvailableWeight baseWeight forbidden) *
              ∏ position : Fin k,
                baseWeight (tail.1 position) /
                  finiteAvailableWeight baseWeight
                    (freshListPrefixForbidden (insert head.1 forbidden) tail position) := by
                rw [htail]
        _ = ∏ position : Fin (k + 1),
              baseWeight ((finiteFreshListCons head tail).1 position) /
                finiteAvailableWeight baseWeight
                  (freshListPrefixForbidden forbidden (finiteFreshListCons head tail) position) := by
                rw [Fin.prod_univ_succ]
                congr 1
                · have hcons_zero :
                      (finiteFreshListCons head tail).1 (0 : Fin (k + 1)) = head.1 := by
                    simpa using (finiteFreshListCons_zero head tail)
                  rw [hcons_zero]
                  simp [freshListPrefixForbidden]
                · apply Finset.prod_congr rfl
                  intro position _
                  rw [freshListPrefixForbidden_succ head tail position]
                  simp
        _ = ∏ position : Fin (k + 1),
              baseWeight (sample.1 position) /
                finiteAvailableWeight baseWeight
                  (freshListPrefixForbidden forbidden sample position) := by
                rw [hreassemble]

private theorem mem_freshListPrefixForbidden_ranking_iff
    {n : ℕ} (ranking : Ranking n) (position i : Candidate n) :
    ranking i ∈
      freshListPrefixForbidden ∅ (rankingToFullFreshList ranking) position ↔
      i < position := by
  simp only [freshListPrefixForbidden, Finset.empty_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hji' : j = i := ranking.injective hji
    simpa [hji'] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- At a ranking position, the sampler's available mass is exactly the sum of
the weights at that position and every later position. -/
theorem finiteAvailableWeight_prefixRanking_eq_suffixWeight
    {n : ℕ} (baseWeight : Candidate n → ℝ) (ranking : Ranking n)
    (position : Candidate n) :
    finiteAvailableWeight baseWeight
      (freshListPrefixForbidden ∅ (rankingToFullFreshList ranking) position) =
      fullRankingSuffixWeight baseWeight ranking position := by
  classical
  unfold finiteAvailableWeight fullRankingSuffixWeight
  calc
    (∑ candidate : Candidate n,
        if candidate ∈
          freshListPrefixForbidden ∅ (rankingToFullFreshList ranking) position
        then 0 else baseWeight candidate) =
        ∑ i : Candidate n,
          if ranking i ∈
            freshListPrefixForbidden ∅ (rankingToFullFreshList ranking) position
          then 0 else baseWeight (ranking i) := by
            simpa using
              (Equiv.sum_comp ranking
                (fun candidate : Candidate n =>
                  if candidate ∈
                    freshListPrefixForbidden ∅
                      (rankingToFullFreshList ranking) position
                  then 0 else baseWeight candidate)).symm
    _ = ∑ i : Candidate n, if i < position then 0 else baseWeight (ranking i) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i < position <;>
            simp [mem_freshListPrefixForbidden_ranking_iff, hi]
    _ = (Finset.univ.filter (fun i : Candidate n => position ≤ i)).sum
          (fun i => baseWeight (ranking i)) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i < position
          · simp [hi]
          · simp [hi, not_lt.mp hi]

/-- The full-ranking atom of the concrete sequential Plackett--Luce sampler
is the standard product over its displayed ordered candidates. -/
theorem fullFreshListAtomWeight_rankingToFullFreshList_eq_orderedProduct
    {n : ℕ} (baseWeight : Candidate n → ℝ) (ranking : Ranking n) :
    finiteFreshListAtomWeight baseWeight ∅ (rankingToFullFreshList ranking) =
      fullRankingOrderedAtomWeight baseWeight ranking := by
  rw [finiteFreshListAtomWeight_eq_prefixProduct]
  unfold fullRankingOrderedAtomWeight
  apply Finset.prod_congr rfl
  intro position _
  rw [finiteAvailableWeight_prefixRanking_eq_suffixWeight]
  simp [rankingToFullFreshList]

/-- The concrete Plackett--Luce PMF has the usual finite ordered-product atom
formula on every full ranking. -/
theorem plackettLuceRankingPMF_apply_toReal_eq_orderedProduct
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    (plackettLuceRankingPMF theta value ranking).toReal =
      fullRankingOrderedAtomWeight (plackettLuceWeight theta value) ranking := by
  rw [plackettLuceRankingPMF_apply_toReal_eq_fullFreshAtomWeight]
  exact fullFreshListAtomWeight_rankingToFullFreshList_eq_orderedProduct _ _

end

end KR21Monoculture

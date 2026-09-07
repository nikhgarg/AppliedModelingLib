import KR21Monoculture.PlackettLuce

/-!
# Full-ranking atoms of the finite Plackett--Luce sampler

This module exposes the exact atom of the concrete sequential sampler on a
full ranking.  It is deliberately independent of outer value distributions:
the Gumbel/exponential-race bridge needs this finite probability identity
directly.
-/

open AppliedModelingLib

namespace KR21Monoculture

/-- Regard a ranking permutation as the corresponding fresh list containing
every candidate once. -/
def rankingToFullFreshList {n : ℕ} (ranking : Ranking n) :
    finiteFreshList (Candidate n) (n + 2) ∅ :=
  ⟨ranking, ranking.injective, fun _ => by simp⟩

/-- Converting the fresh list associated to a ranking back to a permutation
recovers that ranking. -/
theorem fullFreshListToRanking_rankingToFullFreshList {n : ℕ}
    (ranking : Ranking n) :
    fullFreshListToRanking (rankingToFullFreshList ranking) = ranking := by
  ext slot
  simp [rankingToFullFreshList, fullFreshListToRanking_apply]

/-- A full fresh list is determined by its associated ranking. -/
theorem fullFreshListToRanking_injective {n : ℕ} :
    Function.Injective (@fullFreshListToRanking n) := by
  intro a b hab
  apply Subtype.ext
  funext slot
  simpa only [fullFreshListToRanking_apply] using
    congrArg (fun ranking : Ranking n => ranking slot) hab

/-- The mass of a full ranking under the mapped Plackett--Luce PMF is the
mass of its unique preimage fresh list. -/
theorem plackettLuceRankingPMF_apply_eq_fullFreshAtom {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    plackettLuceRankingPMF theta value ranking =
      plackettLuceFreshRankingPMF theta value
        (rankingToFullFreshList ranking) := by
  let sample := rankingToFullFreshList ranking
  have hsample : fullFreshListToRanking sample = ranking := by
    exact fullFreshListToRanking_rankingToFullFreshList ranking
  have hiff : ∀ candidate : finiteFreshList (Candidate n) (n + 2) ∅,
      ranking = fullFreshListToRanking candidate ↔ candidate = sample := by
    intro candidate
    constructor
    · intro hcandidate
      apply fullFreshListToRanking_injective
      calc
        fullFreshListToRanking candidate = ranking := hcandidate.symm
        _ = fullFreshListToRanking sample := hsample.symm
    · intro hcandidate
      subst candidate
      exact hsample.symm
  unfold plackettLuceRankingPMF
  rw [PMF.map_apply]
  simp_rw [hiff]
  exact tsum_ite_eq sample _

/-- Exact real-valued sequential product atom for a full ranking. -/
theorem plackettLuceRankingPMF_apply_toReal_eq_fullFreshAtomWeight {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    (plackettLuceRankingPMF theta value ranking).toReal =
      finiteFreshListAtomWeight (plackettLuceWeight theta value) ∅
        (rankingToFullFreshList ranking) := by
  rw [plackettLuceRankingPMF_apply_eq_fullFreshAtom]
  unfold plackettLuceFreshRankingPMF
  exact finiteWithoutReplacementPMF_atom_toReal
    (plackettLuceWeight theta value)
    (fun i => (plackettLuceWeight_pos theta value i).le)
    (plackettLuceAvailableWeight_pos theta value)
    (∅ : Finset (Candidate n)) (by simp [Candidate])
    (rankingToFullFreshList ranking)

end KR21Monoculture

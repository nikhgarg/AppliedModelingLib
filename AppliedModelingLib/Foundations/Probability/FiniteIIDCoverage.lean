import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Coverage of finite iid samples

This module records the elementary finite-support coupon-coverage bridge used
when a likelihood theorem needs every atom in a prescribed finite collection
to have appeared at least once.  The result is deliberately stated for an
arbitrary finite PMF, rather than for a particular comparison design.
-/

open scoped BigOperators Topology
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The probability that an iid sample contains no occurrence of `atom`. -/
def finiteIidAtomOmissionProbability (μ : PMF α) (atom : α) (horizon : ℕ) : ℝ := by
  classical
  exact pmfProb (pmfProduct (Fin horizon) α μ)
    (fun sample : Fin horizon → α => ∀ index, sample index ≠ atom)

/-- The atom-omission probability is the iid power of its one-draw probability. -/
theorem finiteIidAtomOmissionProbability_eq
    (μ : PMF α) (atom : α) (horizon : ℕ) :
    finiteIidAtomOmissionProbability μ atom horizon =
      (pmfProb μ (fun report => report ≠ atom)) ^ horizon := by
  classical
  let p : α → Prop := fun report => report ≠ atom
  let q : (Fin horizon → α) → Prop :=
    fun sample => ∀ index, p (sample index)
  letI : DecidablePred q := fun sample => Fintype.decidableForallFintype
  calc
    finiteIidAtomOmissionProbability μ atom horizon =
        pmfProb (pmfProduct (Fin horizon) α μ) q := by
            unfold finiteIidAtomOmissionProbability pmfProb pmfExp
            apply Finset.sum_congr rfl
            intro sample _
            by_cases hsample : ∀ index, sample index ≠ atom
            · simp [q, p, hsample]
            · simp [q, p, hsample]
    _ = (pmfProb μ p) ^ horizon := by
      simpa only [q, Fintype.card_fin] using
        (pmfProduct_prob_forall (ι := Fin horizon) μ p)
    _ = (pmfProb μ (fun report => report ≠ atom)) ^ horizon := by
      congr 1

/-- Every positive-probability atom is eventually observed in a finite iid sample. -/
theorem finiteIidAtomOmissionProbability_tendsto_zero
    (μ : PMF α) (atom : α) (hmass : 0 < (μ atom).toReal) :
    Tendsto (finiteIidAtomOmissionProbability μ atom) atTop (𝓝 0) := by
  rw [show finiteIidAtomOmissionProbability μ atom =
      fun horizon => (pmfProb μ (fun report => report ≠ atom)) ^ horizon by
        funext horizon
        exact finiteIidAtomOmissionProbability_eq μ atom horizon]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · exact pmfProb_nonneg μ (fun report => report ≠ atom)
  · apply pmfProb_lt_one_of_mass_not μ (fun report => report ≠ atom) atom
    · simp
    · exact hmass

/-- The probability that at least one atom in `targets` is missing from an iid sample. -/
def finiteIidCoverageFailureProbability
    (μ : PMF α) (targets : Finset α) (horizon : ℕ) : ℝ := by
  classical
  exact pmfProb (pmfProduct (Fin horizon) α μ)
    (fun sample : Fin horizon → α =>
      ∃ atom, atom ∈ targets ∧ ∀ index, sample index ≠ atom)

/-- A finite union bound controls failure to observe every prescribed atom. -/
theorem finiteIidCoverageFailureProbability_le_sum
    (μ : PMF α) (targets : Finset α) (horizon : ℕ) :
    finiteIidCoverageFailureProbability μ targets horizon ≤
      ∑ atom ∈ targets, finiteIidAtomOmissionProbability μ atom horizon := by
  classical
  unfold finiteIidCoverageFailureProbability finiteIidAtomOmissionProbability
  exact pmfProb_exists_mem_le_sum
    (μ := pmfProduct (Fin horizon) α μ) (s := targets)
    (p := fun atom sample => ∀ index, sample index ≠ atom)

/-- A finite collection of positive-probability iid atoms is covered with probability
tending to one. -/
theorem finiteIidCoverageFailureProbability_tendsto_zero
    (μ : PMF α) (targets : Finset α)
    (hmass : ∀ atom, atom ∈ targets → 0 < (μ atom).toReal) :
    Tendsto (finiteIidCoverageFailureProbability μ targets) atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun horizon => ∑ atom ∈ targets, finiteIidAtomOmissionProbability μ atom horizon)
      atTop (𝓝 0) := by
    simpa using
      (tendsto_finset_sum targets
        (fun atom hatom => finiteIidAtomOmissionProbability_tendsto_zero μ atom
          (hmass atom hatom)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hsum ?_ ?_
  · intro horizon
    exact pmfProb_nonneg (pmfProduct (Fin horizon) α μ) _
  · intro horizon
    exact finiteIidCoverageFailureProbability_le_sum μ targets horizon

end
end Probability
end AppliedModelingLib

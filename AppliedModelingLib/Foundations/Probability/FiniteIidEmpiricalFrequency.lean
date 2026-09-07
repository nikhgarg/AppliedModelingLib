import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations

/-!
# Finite IID empirical-frequency lower tails

This module packages the elementary finite-alphabet consequence of the
Chernoff infrastructure: each positive-mass atom appears at every fixed lower
linear frequency with failure probability tending to zero.  The statement is
about literal iid samples, so downstream applications may retain their
original random experimental designs rather than replace them by a balanced
one.
-/

open scoped BigOperators Topology
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- Centering an atom indicator at `threshold` has expectation equal to its
atom mass minus that threshold. -/
theorem pmfExp_indicator_sub_eq
    [Fintype α] (μ : PMF α) (atom : α) (threshold : ℝ) :
    pmfExp μ (fun outcome => (if outcome = atom then (1 : ℝ) else 0) - threshold) =
      (μ atom).toReal - threshold := by
  calc
    pmfExp μ (fun outcome => (if outcome = atom then (1 : ℝ) else 0) - threshold) =
        pmfProb μ (fun outcome => outcome = atom) * (1 - threshold) +
          (1 - pmfProb μ (fun outcome => outcome = atom)) * (-threshold) := by
      apply pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
      intro outcome
      by_cases h : outcome = atom <;> simp [h]
    _ = (μ atom).toReal - threshold := by
      rw [pmfProb_singleton]
      ring

/-- The centered indicator sum is the empirical atom count minus its linear
threshold. -/
theorem finiteIidScoreSum_indicator_sub_eq
    {ι : Type*} [Fintype ι] (sample : ι → α) (atom : α) (threshold : ℝ) :
    finiteIidScoreSum (fun outcome => (if outcome = atom then (1 : ℝ) else 0) - threshold)
      sample =
      (empiricalCount sample atom : ℝ) - (Fintype.card ι : ℝ) * threshold := by
  unfold finiteIidScoreSum
  rw [Finset.sum_sub_distrib]
  have hcount :
      (∑ index : ι, if sample index = atom then (1 : ℝ) else 0) =
        (empiricalCount sample atom : ℝ) := by
    simp [empiricalCount, successIndexSet, Finset.sum_boole]
  rw [hcount]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Failure of a fixed atom to appear with at least the specified linear
frequency in a literal iid sample. -/
noncomputable def finiteIidAtomLowerFrequencyFailure
    [Fintype α] (μ : PMF α) (atom : α) (threshold : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (fun sample : Fin n → α => (empiricalCount sample atom : ℝ) ≤ (n : ℝ) * threshold)

/-- Any threshold strictly below an atom's mass is eventually exceeded by its
empirical count, with probability tending to one. -/
theorem finiteIidAtomLowerFrequencyFailure_tendsto_zero
    [Fintype α] (μ : PMF α) (atom : α) (threshold : ℝ)
    (hthreshold : threshold < (μ atom).toReal) :
    Tendsto (finiteIidAtomLowerFrequencyFailure μ atom threshold) atTop (𝓝 0) := by
  let score : α → ℝ := fun outcome => (if outcome = atom then (1 : ℝ) else 0) - threshold
  have hmean : 0 < pmfExp μ score := by
    rw [pmfExp_indicator_sub_eq]
    exact sub_pos.mpr hthreshold
  obtain ⟨rate, hrate, htail⟩ :=
    finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos μ score hmean
  have htail_zero : Tendsto
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) atTop (𝓝 0) :=
    htail.tendsto_zero_of_pos_rate hrate
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    htail_zero ?_ ?_
  · intro n
    exact pmfProb_nonneg (pmfProduct (Fin n) α μ) _
  · intro n
    unfold finiteIidAtomLowerFrequencyFailure
    refine pmfProb_le_of_imp (pmfProduct (Fin n) α μ) _ _ ?_
    intro sample hsample
    rw [finiteIidScoreSum_indicator_sub_eq]
    simp only [Fintype.card_fin]
    linarith

/-- Centering the complementary atom indicator at `threshold` has expectation
`threshold` minus the atom mass. -/
theorem pmfExp_threshold_sub_indicator_eq
    [Fintype α] (μ : PMF α) (atom : α) (threshold : ℝ) :
    pmfExp μ (fun outcome => threshold - (if outcome = atom then (1 : ℝ) else 0)) =
      threshold - (μ atom).toReal := by
  have hindicator :
      pmfExp μ (fun outcome => if outcome = atom then (1 : ℝ) else 0) =
        (μ atom).toReal := by
    simpa using pmfExp_indicator_sub_eq μ atom 0
  rw [pmfExp_sub, pmfExp_const, hindicator]

/-- The complementary centered indicator sum is its linear threshold minus
the empirical atom count. -/
theorem finiteIidScoreSum_threshold_sub_indicator_eq
    {ι : Type*} [Fintype ι] (sample : ι → α) (atom : α) (threshold : ℝ) :
    finiteIidScoreSum (fun outcome => threshold - (if outcome = atom then (1 : ℝ) else 0))
      sample =
      (Fintype.card ι : ℝ) * threshold - (empiricalCount sample atom : ℝ) := by
  calc
    finiteIidScoreSum (fun outcome => threshold - (if outcome = atom then (1 : ℝ) else 0))
        sample =
        -finiteIidScoreSum
          (fun outcome => (if outcome = atom then (1 : ℝ) else 0) - threshold) sample := by
          unfold finiteIidScoreSum
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro index _
          ring
    _ = (Fintype.card ι : ℝ) * threshold - (empiricalCount sample atom : ℝ) := by
      rw [finiteIidScoreSum_indicator_sub_eq]
      ring

/-- Failure of a fixed atom to stay below the specified linear frequency in a
literal iid sample. -/
noncomputable def finiteIidAtomUpperFrequencyFailure
    [Fintype α] (μ : PMF α) (atom : α) (threshold : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (fun sample : Fin n → α => (n : ℝ) * threshold ≤ (empiricalCount sample atom : ℝ))

/-- Any threshold strictly above an atom's mass is eventually not reached by
its empirical count, with probability tending to one. -/
theorem finiteIidAtomUpperFrequencyFailure_tendsto_zero
    [Fintype α] (μ : PMF α) (atom : α) (threshold : ℝ)
    (hthreshold : (μ atom).toReal < threshold) :
    Tendsto (finiteIidAtomUpperFrequencyFailure μ atom threshold) atTop (𝓝 0) := by
  let score : α → ℝ := fun outcome => threshold - (if outcome = atom then (1 : ℝ) else 0)
  have hmean : 0 < pmfExp μ score := by
    rw [pmfExp_threshold_sub_indicator_eq]
    exact sub_pos.mpr hthreshold
  obtain ⟨rate, hrate, htail⟩ :=
    finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos μ score hmean
  have htail_zero : Tendsto
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) atTop (𝓝 0) :=
    htail.tendsto_zero_of_pos_rate hrate
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    htail_zero ?_ ?_
  · intro n
    exact pmfProb_nonneg (pmfProduct (Fin n) α μ) _
  · intro n
    unfold finiteIidAtomUpperFrequencyFailure
    refine pmfProb_le_of_imp (pmfProduct (Fin n) α μ) _ _ ?_
    intro sample hsample
    rw [finiteIidScoreSum_threshold_sub_indicator_eq]
    simp only [Fintype.card_fin]
    linarith

/-- Failure of an empirical atom count to stay within an additive linear
deviation of its exact PMF mass. -/
noncomputable def finiteIidAtomMassDeviationFailure
    [Fintype α] (μ : PMF α) (atom : α) (epsilon : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (fun sample : Fin n → α =>
      (n : ℝ) * epsilon ≤
        |(empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal|)

/-- Every finite-alphabet empirical atom mass converges in probability to its
literal PMF mass.  The proof combines the two Chernoff one-sided tails. -/
theorem finiteIidAtomMassDeviationFailure_tendsto_zero
    [Fintype α] (μ : PMF α) (atom : α) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (finiteIidAtomMassDeviationFailure μ atom epsilon) atTop (𝓝 0) := by
  let lower : ℕ → ℝ := fun n =>
    finiteIidAtomLowerFrequencyFailure μ atom ((μ atom).toReal - epsilon) n
  let upper : ℕ → ℝ := fun n =>
    finiteIidAtomUpperFrequencyFailure μ atom ((μ atom).toReal + epsilon) n
  have hlower : Tendsto lower atTop (𝓝 0) := by
    dsimp [lower]
    apply finiteIidAtomLowerFrequencyFailure_tendsto_zero
    linarith
  have hupper : Tendsto upper atTop (𝓝 0) := by
    dsimp [upper]
    apply finiteIidAtomUpperFrequencyFailure_tendsto_zero
    linarith
  have hsum : Tendsto (fun n => lower n + upper n) atTop (𝓝 0) := by
    simpa using hlower.add hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hsum ?_ ?_
  · intro n
    exact pmfProb_nonneg (pmfProduct (Fin n) α μ) _
  · intro n
    let lowerEvent : (Fin n → α) → Prop := fun sample =>
      (empiricalCount sample atom : ℝ) ≤ (n : ℝ) * ((μ atom).toReal - epsilon)
    let upperEvent : (Fin n → α) → Prop := fun sample =>
      (n : ℝ) * ((μ atom).toReal + epsilon) ≤ (empiricalCount sample atom : ℝ)
    have hsubset : ∀ sample : Fin n → α,
        (n : ℝ) * epsilon ≤
          |(empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal| →
        lowerEvent sample ∨ upperEvent sample := by
      intro sample hdeviation
      by_cases hnonneg : 0 ≤
          (empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal
      · right
        dsimp [upperEvent]
        rw [abs_of_nonneg hnonneg] at hdeviation
        linarith
      · left
        dsimp [lowerEvent]
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at hdeviation
        linarith
    have hor :
        pmfProb (pmfProduct (Fin n) α μ) (fun sample => lowerEvent sample ∨ upperEvent sample) ≤
          pmfProb (pmfProduct (Fin n) α μ) lowerEvent +
            pmfProb (pmfProduct (Fin n) α μ) upperEvent := by
      rw [pmfProb_or_eq_add_sub_inter]
      have hnonneg := pmfProb_nonneg (pmfProduct (Fin n) α μ)
        (fun sample => lowerEvent sample ∧ upperEvent sample)
      linarith
    unfold finiteIidAtomMassDeviationFailure
    calc
      pmfProb (pmfProduct (Fin n) α μ)
          (fun sample : Fin n → α =>
            (n : ℝ) * epsilon ≤
              |(empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal|) ≤
          pmfProb (pmfProduct (Fin n) α μ) (fun sample => lowerEvent sample ∨ upperEvent sample) :=
        pmfProb_le_of_imp _ _ _ hsubset
      _ ≤ pmfProb (pmfProduct (Fin n) α μ) lowerEvent +
          pmfProb (pmfProduct (Fin n) α μ) upperEvent := hor
      _ = lower n + upper n := by
        rfl

/-- Failure of any finite-alphabet empirical atom mass to stay within an
additive linear deviation of its literal PMF mass. -/
noncomputable def finiteIidAnyMassDeviationFailure
    [Fintype α] (μ : PMF α) (epsilon : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (fun sample : Fin n → α => ∃ atom,
      (n : ℝ) * epsilon ≤
        |(empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal|)

/-- The maximum coordinatewise empirical-mass deviation of a finite iid
sample converges to zero in probability. -/
theorem finiteIidAnyMassDeviationFailure_tendsto_zero
    [Fintype α] (μ : PMF α) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (finiteIidAnyMassDeviationFailure μ epsilon) atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n => ∑ atom : α, finiteIidAtomMassDeviationFailure μ atom epsilon n)
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset α) (fun atom _ =>
      finiteIidAtomMassDeviationFailure_tendsto_zero μ atom epsilon hepsilon)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hsum ?_ ?_
  · intro n
    exact pmfProb_nonneg (pmfProduct (Fin n) α μ) _
  · intro n
    unfold finiteIidAnyMassDeviationFailure
    simpa [finiteIidAtomMassDeviationFailure] using
      (pmfProb_exists_mem_le_sum
        (μ := pmfProduct (Fin n) α μ) (s := (Finset.univ : Finset α))
        (p := fun (atom : α) (sample : Fin n → α) =>
          (n : ℝ) * epsilon ≤
            |(empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal|))

/-- A finite iid sample violates a common lower frequency threshold at one of
the specified atoms.  Naming the event lets downstream finite-feedback models
refer to its literal sample-space predicate without re-expanding it. -/
abbrev finiteIidFiniteSetLowerFrequencyEvent
    [Fintype α] (atoms : Finset α) (threshold : ℝ) {n : ℕ}
    (sample : Fin n → α) : Prop :=
  ∃ atom, atom ∈ atoms ∧
    (empiricalCount sample atom : ℝ) ≤ (n : ℝ) * threshold

/-- Failure of at least one member of a finite atom set to meet a common
lower linear frequency threshold. -/
noncomputable def finiteIidFiniteSetLowerFrequencyFailure
    [Fintype α] (μ : PMF α) (atoms : Finset α) (threshold : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (finiteIidFiniteSetLowerFrequencyEvent atoms threshold)

/-- A nonempty finite family of positive-mass atoms has one common strictly
positive lower threshold. -/
theorem exists_pos_lt_atomMass_of_finite
    [Fintype α] (μ : PMF α) (atoms : Finset α) (hatoms : atoms.Nonempty)
    (hmass : ∀ atom ∈ atoms, 0 < (μ atom).toReal) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ atom ∈ atoms, threshold < (μ atom).toReal := by
  let minMass : ℝ := atoms.inf' hatoms (fun atom => (μ atom).toReal)
  have hmin_pos : 0 < minMass := by
    rw [Finset.lt_inf'_iff]
    intro atom hatom
    exact hmass atom hatom
  refine ⟨minMass / 2, by linarith, ?_⟩
  intro atom hatom
  have hmin_le : minMass ≤ (μ atom).toReal := by
    exact Finset.inf'_le _ hatom
  linarith

/-- A finite collection of atoms whose masses all exceed `threshold` meets
that lower frequency simultaneously with probability tending to one. -/
theorem finiteIidFiniteSetLowerFrequencyFailure_tendsto_zero
    [Fintype α] (μ : PMF α) (atoms : Finset α) (threshold : ℝ)
    (hthreshold : ∀ atom ∈ atoms, threshold < (μ atom).toReal) :
    Tendsto (finiteIidFiniteSetLowerFrequencyFailure μ atoms threshold) atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n => ∑ atom ∈ atoms, finiteIidAtomLowerFrequencyFailure μ atom threshold n)
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum atoms (fun atom hatom =>
      finiteIidAtomLowerFrequencyFailure_tendsto_zero μ atom threshold (hthreshold atom hatom))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hsum ?_ ?_
  · intro n
    exact pmfProb_nonneg (pmfProduct (Fin n) α μ) _
  · intro n
    unfold finiteIidFiniteSetLowerFrequencyFailure finiteIidFiniteSetLowerFrequencyEvent
    simpa [finiteIidAtomLowerFrequencyFailure] using
      (pmfProb_exists_mem_le_sum
        (μ := pmfProduct (Fin n) α μ) (s := atoms)
        (p := fun (atom : α) (sample : Fin n → α) =>
          (empiricalCount sample atom : ℝ) ≤ (n : ℝ) * threshold))

end

end Probability
end AppliedModelingLib

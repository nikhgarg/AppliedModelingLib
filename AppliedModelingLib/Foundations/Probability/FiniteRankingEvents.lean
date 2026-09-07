import AppliedModelingLib.Foundations.Math.FiniteRanking
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators

namespace AppliedModelingLib

/-!
# Finite Ranking Events

Reusable probability bounds for finite ranking-error events.  The deterministic
adjacent-inversion kernels live in `Foundations.Math.FiniteRanking`; this file
packages them with finite PMF union bounds.
-/

noncomputable section

/-- Adjacent low indices in a finite chain. -/
abbrev FiniteAdjacentIndex (n : ℕ) :=
  {m : Fin n // m.val + 1 < n}

/-- The successor index associated with an adjacent finite-chain index. -/
def FiniteAdjacentIndex.succ {n : ℕ} (m : FiniteAdjacentIndex n) :
    Fin n :=
  ⟨m.1.val + 1, m.2⟩

/--
Finite PMF union bound for the event that a score vector has any weak
inversion: it is bounded by the sum of adjacent weak-inversion probabilities.
-/
theorem pmfProb_anyInversion_le_sum_adjacentInversion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ}
    (μ : PMF Ω) (x : Ω → Fin n → ℝ) :
    pmfProb μ
        (fun ω => ∃ i j : Fin n, i.val < j.val ∧ x ω j ≤ x ω i) ≤
      ∑ m : FiniteAdjacentIndex n,
        pmfProb μ
          (fun ω => x ω m.succ ≤ x ω m.1) := by
  classical
  let adjEvent : FiniteAdjacentIndex n → Ω → Prop :=
    fun m ω => x ω m.succ ≤ x ω m.1
  have hsub :
      ∀ ω : Ω,
        (∃ i j : Fin n, i.val < j.val ∧ x ω j ≤ x ω i) →
          ∃ m : FiniteAdjacentIndex n, adjEvent m ω := by
    intro ω hω
    rcases FiniteRanking.exists_adjacent_fin_inversion_of_any_inversion
        (x ω) hω with
      ⟨m, hm_succ, hstep⟩
    exact ⟨⟨m, hm_succ⟩, hstep⟩
  have hmono :
      pmfProb μ
          (fun ω => ∃ i j : Fin n, i.val < j.val ∧ x ω j ≤ x ω i) ≤
        pmfProb μ
          (fun ω => ∃ m, m ∈ (Finset.univ : Finset (FiniteAdjacentIndex n)) ∧
            adjEvent m ω) := by
    refine pmfProb_le_of_imp μ _ _ ?_
    intro ω hω
    rcases hsub ω hω with ⟨m, hm⟩
    exact ⟨m, by simp, hm⟩
  have hunion :=
    pmfProb_exists_mem_le_sum
      (μ := μ) (s := (Finset.univ : Finset (FiniteAdjacentIndex n)))
      (p := adjEvent)
  calc
    pmfProb μ
        (fun ω => ∃ i j : Fin n, i.val < j.val ∧ x ω j ≤ x ω i)
        ≤
      pmfProb μ
        (fun ω => ∃ m, m ∈ (Finset.univ : Finset (FiniteAdjacentIndex n)) ∧
          adjEvent m ω) := hmono
    _ ≤
      ∑ m ∈ (Finset.univ : Finset (FiniteAdjacentIndex n)),
        pmfProb μ (adjEvent m) := hunion
    _ =
      ∑ m : FiniteAdjacentIndex n,
        pmfProb μ
          (fun ω => x ω m.succ ≤ x ω m.1) := by
        simp [adjEvent]

/-- Adjacent low indices in the interval from `i` to `j`. -/
abbrev FiniteIntervalAdjacentIndex {n : ℕ} (i j : Fin n) :=
  {m : Fin n // i.val ≤ m.val ∧ m.val < j.val}

/-- The successor index associated with an interval-adjacent index. -/
def FiniteIntervalAdjacentIndex.succ {n : ℕ} {i j : Fin n}
    (m : FiniteIntervalAdjacentIndex i j) : Fin n :=
  ⟨m.1.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt m.2.2) j.isLt⟩

/--
Finite PMF union bound for a fixed nonadjacent weak inversion.  An inversion
between `i` and `j` is bounded by the sum of adjacent weak inversions along
the interval from `i` to `j`.
-/
theorem pmfProb_pairInversion_le_sum_intervalAdjacentInversion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ}
    (μ : PMF Ω) (x : Ω → Fin n → ℝ) {i j : Fin n}
    (hij : i.val < j.val) :
    pmfProb μ (fun ω => x ω j ≤ x ω i) ≤
      ∑ m : FiniteIntervalAdjacentIndex i j,
        pmfProb μ
          (fun ω => x ω m.succ ≤ x ω m.1) := by
  classical
  let adjEvent : FiniteIntervalAdjacentIndex i j → Ω → Prop :=
    fun m ω => x ω m.succ ≤ x ω m.1
  have hsub :
      ∀ ω : Ω, x ω j ≤ x ω i →
        ∃ m : FiniteIntervalAdjacentIndex i j, adjEvent m ω := by
    intro ω hω
    rcases FiniteRanking.exists_adjacent_fin_inversion_of_nonadjacent_inversion
        (x ω) hij hω with
      ⟨m, _hm_succ, him, hmj, hstep⟩
    exact ⟨⟨m, him, hmj⟩, by simpa [adjEvent, FiniteIntervalAdjacentIndex.succ] using hstep⟩
  have hmono :
      pmfProb μ (fun ω => x ω j ≤ x ω i) ≤
        pmfProb μ
          (fun ω =>
            ∃ m, m ∈ (Finset.univ : Finset (FiniteIntervalAdjacentIndex i j)) ∧
              adjEvent m ω) := by
    refine pmfProb_le_of_imp μ _ _ ?_
    intro ω hω
    rcases hsub ω hω with ⟨m, hm⟩
    exact ⟨m, by simp, hm⟩
  have hunion :=
    pmfProb_exists_mem_le_sum
      (μ := μ) (s := (Finset.univ : Finset (FiniteIntervalAdjacentIndex i j)))
      (p := adjEvent)
  calc
    pmfProb μ (fun ω => x ω j ≤ x ω i)
        ≤
      pmfProb μ
        (fun ω =>
          ∃ m, m ∈ (Finset.univ : Finset (FiniteIntervalAdjacentIndex i j)) ∧
            adjEvent m ω) := hmono
    _ ≤
      ∑ m ∈ (Finset.univ : Finset (FiniteIntervalAdjacentIndex i j)),
        pmfProb μ (adjEvent m) := hunion
    _ =
      ∑ m : FiniteIntervalAdjacentIndex i j,
        pmfProb μ
          (fun ω => x ω m.succ ≤ x ω m.1) := by
        simp [adjEvent]

end

end AppliedModelingLib

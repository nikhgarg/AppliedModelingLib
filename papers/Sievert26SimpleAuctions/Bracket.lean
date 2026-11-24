import Sievert26SimpleAuctions.Main
import Sievert26SimpleAuctions.UpperBound

/-! Both sides of the bracket for the universal constant. -/
namespace Sievert26SimpleAuctions

/-- Both bounds, for the same definitions of `REV`, `SREV`, `BREV`. -/
theorem main_bracket :
    (∃ (m : ℕ) (D : Fin m → FinDist), (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D) ∧
    (∀ (m : ℕ) (D : Fin m → FinDist), REV D ≤ (2486 / 1000 : ℝ) * max (SREV D) (BREV D)) :=
  ⟨lower_bound, upper_bound⟩

/-- The set of constants `c` with `REV ≤ c · max(SREV, BREV)` for all finite instances. -/
def ValidConstants : Set ℝ :=
  {c | ∀ (m : ℕ) (D : Fin m → FinDist), REV D ≤ c * max (SREV D) (BREV D)}

/-- `c* = inf` of the valid constants. -/
noncomputable def cStar : ℝ := sInf ValidConstants

/-- `2.1946 ≤ c* ≤ 2.486`. -/
theorem cStar_mem : (2.1946 : ℝ) ≤ cStar ∧ cStar ≤ 2486 / 1000 := by
  have hne : (2486 / 1000 : ℝ) ∈ ValidConstants := upper_bound
  have hlow : ∀ c ∈ ValidConstants, (2.1946 : ℝ) ≤ c := by
    intro c hc
    obtain ⟨m, D, h⟩ := lower_bound
    have h1 := hc m D
    by_contra hlt
    have h2 : 0 ≤ max (SREV D) (BREV D) := (UB.BREV_nonneg D).trans (le_max_right _ _)
    nlinarith [not_le.mp hlt]
  exact ⟨le_csInf ⟨_, hne⟩ hlow, csInf_le ⟨_, hlow⟩ hne⟩

end Sievert26SimpleAuctions

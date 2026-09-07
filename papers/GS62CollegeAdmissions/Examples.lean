import GS62CollegeAdmissions.MainTheorems
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The finite rank-table proofs below deliberately avoid the global simp
simproc, which panics on this Lean toolchain when reducing nested vectors. -/
syntax (name := finiteSimp) "finite_simp" Lean.Parser.Tactic.simpArgs : tactic

macro_rules
  | `(tactic| finite_simp [$args,*]) => `(tactic| simp only [$args,*] <;> decide)

/-!
# Gale--Shapley 1962: finite examples

This file checks the three concrete examples on printed pages 11--12 of the
paper.  Rank `0` is best.  The examples are deliberately stated using the
paper's rank tables, independently of the real-valued reusable matching API.
-/

namespace GS62CollegeAdmissions

/-- Stability for a bijective partner map written as finite rank tables. -/
def StableRankMatching {n : Nat}
    (menRank womenRank : Fin n → Fin n → Nat)
    (partner : Fin n → Fin n) : Prop :=
  Function.Bijective partner ∧
    ∀ m m', menRank m (partner m') < menRank m (partner m) →
      womenRank (partner m') m < womenRank (partner m') m' → False

/-! ## Example 1: exactly three stable marriages -/

def example1MenRank : Fin 3 → Fin 3 → Nat :=
  ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]]

def example1WomenRank : Fin 3 → Fin 3 → Nat :=
  ![![2, 0, 1], ![1, 2, 0], ![0, 1, 2]]

/-- Example 1's proposer-first-choice marriage. -/
def example1MenFirst : Fin 3 → Fin 3 := ![0, 1, 2]

/-- Example 1's receiver-first-choice marriage. -/
def example1WomenFirst : Fin 3 → Fin 3 := ![2, 0, 1]

/-- Example 1's all-second-choice marriage. -/
def example1AllSecond : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The three displayed marriages in Example 1 are stable. -/
theorem paper_gs62_example1_displayed_marriages_stable :
    StableRankMatching example1MenRank example1WomenRank example1MenFirst ∧
      StableRankMatching example1MenRank example1WomenRank example1WomenFirst ∧
      StableRankMatching example1MenRank example1WomenRank example1AllSecond := by
  unfold StableRankMatching
  decide

/-- Example 1 has no stable marriage other than the three displayed ones. -/
theorem paper_gs62_example1_exactly_three_stable_marriages :
    ∀ partner : Fin 3 → Fin 3,
      StableRankMatching example1MenRank example1WomenRank partner ↔
        partner = example1MenFirst ∨ partner = example1WomenFirst ∨
          partner = example1AllSecond := by
  unfold StableRankMatching
  decide

/-! ## Example 2: a unique stable marriage -/

def example2MenRank : Fin 4 → Fin 4 → Nat :=
  ![![0, 1, 2, 3], ![0, 3, 2, 1], ![1, 0, 2, 3], ![3, 1, 2, 0]]

def example2WomenRank : Fin 4 → Fin 4 → Nat :=
  ![![2, 3, 1, 0], ![2, 0, 3, 1], ![1, 2, 3, 0], ![2, 1, 0, 3]]

/-- The circled Example 2 marriage: `α-C`, `β-D`, `γ-A`, `δ-B`. -/
def example2Partner : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/--
Every permutation of four partners is either the displayed Example 2 outcome
or admits one of eight explicitly listed blocking-pair patterns.
-/
private theorem example2PermutationCertificate (p0 p1 p2 p3 : Fin 4) :
    p0 ≠ p1 → p0 ≠ p2 → p0 ≠ p3 →
    p1 ≠ p2 → p1 ≠ p3 → p2 ≠ p3 →
    (p0 = 2 ∧ p1 = 3 ∧ p2 = 0 ∧ p3 = 1) ∨
      (p1 = 1 ∧ p2 = 2) ∨
      ((p2 = 2 ∨ p2 = 3) ∧ p0 = 0) ∨
      ((p1 = 1 ∨ p1 = 2) ∧ p3 = 3) ∨
      ((p3 = 0 ∧ (p2 = 1 ∨ p2 = 2)) ∨ (p3 = 2 ∧ p2 = 1)) ∨
      (((p0 = 1 ∨ p0 = 2 ∨ p0 = 3) ∧ p1 = 0) ∨
        (p0 = 3 ∧ p1 = 2)) ∨
      ((p3 = 0 ∧ (p0 = 1 ∨ p0 = 2)) ∨ (p3 = 2 ∧ p0 = 1)) ∨
      ((p0 = 2 ∧ p2 = 1) ∨ (p0 = 3 ∧ (p2 = 1 ∨ p2 = 2))) ∨
      ((p1 = 1 ∨ p1 = 2) ∧ p0 = 3) := by
  fin_cases p0 <;> fin_cases p1 <;> fin_cases p2 <;> fin_cases p3 <;>
    decide

/-- Example 2's circled marriage is stable and is the unique stable marriage. -/
theorem paper_gs62_example2_unique_stable_marriage :
    StableRankMatching example2MenRank example2WomenRank example2Partner ∧
      ∀ partner : Fin 4 → Fin 4,
        StableRankMatching example2MenRank example2WomenRank partner →
          partner = example2Partner := by
  constructor
  · unfold StableRankMatching
    decide
  · intro partner hstable
    rcases hstable with ⟨⟨hinjective, _⟩, hnoBlock⟩
    have pairwise_ne {i j : Fin 4} (hij : i ≠ j) : partner i ≠ partner j := by
      intro h
      exact hij (hinjective h)
    have hcert := example2PermutationCertificate
      (partner 0) (partner 1) (partner 2) (partner 3)
      (pairwise_ne (i := 0) (j := 1) (by decide))
      (pairwise_ne (i := 0) (j := 2) (by decide))
      (pairwise_ne (i := 0) (j := 3) (by decide))
      (pairwise_ne (i := 1) (j := 2) (by decide))
      (pairwise_ne (i := 1) (j := 3) (by decide))
      (pairwise_ne (i := 2) (j := 3) (by decide))
    rcases hcert with htarget | hb12 | hb20 | hb13 | hb32 | hb01 |
      hb30 | hb02 | hb10
    · rcases htarget with ⟨h0, h1, h2, h3⟩
      funext i
      fin_cases i
      · change partner 0 = 2
        exact h0
      · change partner 1 = 3
        exact h1
      · change partner 2 = 0
        exact h2
      · change partner 3 = 1
        exact h3
    · rcases hb12 with ⟨h1, h2⟩
      exact (hnoBlock 1 2
        (by finite_simp [example2MenRank, h1, h2])
        (by finite_simp [example2WomenRank, h2])).elim
    · rcases hb20 with ⟨h2, h0⟩
      rcases h2 with h2 | h2 <;>
        exact (hnoBlock 2 0
          (by finite_simp [example2MenRank, h0, h2])
          (by finite_simp [example2WomenRank, h0])).elim
    · rcases hb13 with ⟨h1, h3⟩
      rcases h1 with h1 | h1 <;>
        exact (hnoBlock 1 3
          (by finite_simp [example2MenRank, h1, h3])
          (by finite_simp [example2WomenRank, h3])).elim
    · rcases hb32 with hb | hb
      · rcases hb with ⟨h3, h2⟩
        rcases h2 with h2 | h2 <;>
          exact (hnoBlock 3 2
            (by finite_simp [example2MenRank, h2, h3])
            (by finite_simp [example2WomenRank, h2])).elim
      · rcases hb with ⟨h3, h2⟩
        exact (hnoBlock 3 2
          (by finite_simp [example2MenRank, h2, h3])
          (by finite_simp [example2WomenRank, h2])).elim
    · rcases hb01 with hb | hb
      · rcases hb with ⟨h0, h1⟩
        rcases h0 with h0 | h0 | h0 <;>
          exact (hnoBlock 0 1
            (by finite_simp [example2MenRank, h0, h1])
            (by finite_simp [example2WomenRank, h1])).elim
      · rcases hb with ⟨h0, h1⟩
        exact (hnoBlock 0 1
          (by finite_simp [example2MenRank, h0, h1])
          (by finite_simp [example2WomenRank, h1])).elim
    · rcases hb30 with hb | hb
      · rcases hb with ⟨h3, h0⟩
        rcases h0 with h0 | h0 <;>
          exact (hnoBlock 3 0
            (by finite_simp [example2MenRank, h0, h3])
            (by finite_simp [example2WomenRank, h0])).elim
      · rcases hb with ⟨h3, h0⟩
        exact (hnoBlock 3 0
          (by finite_simp [example2MenRank, h0, h3])
          (by finite_simp [example2WomenRank, h0])).elim
    · rcases hb02 with hb | hb
      · rcases hb with ⟨h0, h2⟩
        exact (hnoBlock 0 2
          (by finite_simp [example2MenRank, h0, h2])
          (by finite_simp [example2WomenRank, h2])).elim
      · rcases hb with ⟨h0, h2⟩
        rcases h2 with h2 | h2 <;>
          exact (hnoBlock 0 2
            (by finite_simp [example2MenRank, h0, h2])
            (by finite_simp [example2WomenRank, h2])).elim
    · rcases hb10 with ⟨h1, h0⟩
      rcases h1 with h1 | h1 <;>
        exact (hnoBlock 1 0
          (by finite_simp [example2MenRank, h0, h1])
          (by finite_simp [example2WomenRank, h0])).elim

/-! ## Example 3: the roommates obstruction -/

/-- A perfect roommate pairing is a fixed-point-free involution. -/
def RoommatePairing {n : Nat} (partner : Fin n → Fin n) : Prop :=
  (∀ i, partner (partner i) = i) ∧ ∀ i, partner i ≠ i

/-- Stability for a roommate pairing, again with lower ranks preferred. -/
def StableRoommateRankTable {n : Nat}
    (rank : Fin n → Fin n → Nat) (partner : Fin n → Fin n) : Prop :=
  RoommatePairing partner ∧
    ∀ i j, i ≠ j → rank i j < rank i (partner i) →
      rank j i < rank j (partner j) → False

/--
The first three roommate lists from Example 3.  The fourth row is deliberately
left as an arbitrary function, matching the paper's statement that the
obstruction is independent of the fourth roommate's ranking.
-/
def example3Rank (fourthRank : Fin 4 → Fin 4) : Fin 4 → Fin 4 → Nat :=
  ![![3, 0, 1, 2], ![1, 3, 0, 2], ![0, 1, 3, 2],
    fun j => (fourthRank j : Nat)]

/-- Example 3 admits no stable roommate pairing, for every fourth preference list. -/
theorem paper_gs62_example3_no_stable_roommate_pairing :
    ∀ fourthRank partner : Fin 4 → Fin 4,
      ¬ StableRoommateRankTable (example3Rank fourthRank) partner := by
  unfold StableRoommateRankTable RoommatePairing
  intro fourthRank partner hstable
  rcases hstable with ⟨⟨hinvol, hfixed⟩, hnoBlock⟩
  have hinjective : Function.Injective partner := by
    intro i j hij
    calc
      i = partner (partner i) := (hinvol i).symm
      _ = partner (partner j) := by rw [hij]
      _ = j := hinvol j
  generalize h0 : partner 0 = p0
  fin_cases p0
  · exact hfixed 0 h0
  · have h1 : partner 1 = 0 := by
        calc
          partner 1 = partner (partner 0) := by rw [h0]; rfl
          _ = 0 := hinvol 0
    have h2 : partner 2 = 3 := by
      generalize h : partner 2 = p2
      fin_cases p2
      · have : (2 : Fin 4) = 1 := hinjective (h.trans h1.symm)
        have hval := congrArg Fin.val this
        norm_num at hval
      · have : (2 : Fin 4) = 0 := hinjective (h.trans h0.symm)
        have hval := congrArg Fin.val this
        norm_num at hval
      · exact (hfixed 2 h).elim
      · rfl
    exact hnoBlock 1 2 (by decide)
      (by rw [h1]; change 0 < 1; decide)
      (by rw [h2]; change 1 < 2; decide)
  · have h2 : partner 2 = 0 := by
        calc
          partner 2 = partner (partner 0) := by rw [h0]; rfl
          _ = 0 := hinvol 0
    have h1 : partner 1 = 3 := by
      generalize h : partner 1 = p1
      fin_cases p1
      · have : (1 : Fin 4) = 2 := hinjective (h.trans h2.symm)
        have hval := congrArg Fin.val this
        norm_num at hval
      · exact (hfixed 1 h).elim
      · have : (1 : Fin 4) = 0 := hinjective (h.trans h0.symm)
        have hval := congrArg Fin.val this
        norm_num at hval
      · rfl
    exact hnoBlock 0 1 (by decide)
      (by rw [h0]; change 0 < 1; decide)
      (by rw [h1]; change 1 < 2; decide)
  · have h3 : partner 3 = 0 := by
        calc
          partner 3 = partner (partner 0) := by rw [h0]; rfl
          _ = 0 := hinvol 0
    have h1 : partner 1 = 2 := by
      generalize h : partner 1 = p1
      fin_cases p1
      · have : (1 : Fin 4) = 3 := hinjective (h.trans h3.symm)
        have hval := congrArg Fin.val this
        norm_num at hval
      · exact (hfixed 1 h).elim
      · rfl
      · have : (1 : Fin 4) = 0 := hinjective (h.trans h0.symm)
        have hval := congrArg Fin.val this
        norm_num at hval
    have h2 : partner 2 = 1 := by
      calc
        partner 2 = partner (partner 1) := by rw [h1]
        _ = 1 := hinvol 1
    exact hnoBlock 0 2 (by decide)
      (by rw [h0]; change 1 < 2; decide)
      (by rw [h2]; change 0 < 1; decide)

end GS62CollegeAdmissions

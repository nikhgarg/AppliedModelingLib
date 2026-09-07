import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

set_option linter.dupNamespace false

/-!
# Finite Ranking Primitives

Paper-independent primitives for finite rankings with at least two positions.

The index `n` represents a candidate universe `Fin (n + 2)`, so first and
second positions are always available without extra nonemptiness side
conditions.

## Main declarations

- `Candidate`
- `Ranking`
- `firstChoice`
- `secondChoice`
- `swapTopTwo`
- `rankOf`
- `bestRemainingAfter`
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

/--
Candidate set with at least two candidates. The parameter `n` means there are
`n + 2` candidates.
-/
abbrev Candidate (n : ℕ) := Fin (n + 2)

/-- A ranking is a permutation of the candidate set. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Candidate n)

/-- The candidate placed first by a ranking. -/
def firstChoice {n : ℕ} (π : Ranking n) : Candidate n :=
  π 0

/-- The candidate placed second by a ranking. -/
def secondChoice {n : ℕ} (π : Ranking n) : Candidate n :=
  π 1

/-- The ranking obtained by swapping the first two positions of `π`. -/
def swapTopTwo {n : ℕ} (π : Ranking n) : Ranking n :=
  (Equiv.swap (0 : Candidate n) 1).trans π

/-- The position of candidate `c` in ranking `π`. Lower is better. -/
def rankOf {n : ℕ} (π : Ranking n) (c : Candidate n) : Candidate n :=
  π.symm c

/--
When exactly one candidate `c` has already been selected, the best remaining
candidate under `π` is the top candidate unless that top candidate is `c`, in
which case it is the runner-up.
-/
def bestRemainingAfter {n : ℕ} (π : Ranking n) (c : Candidate n) : Candidate n :=
  if firstChoice π = c then secondChoice π else firstChoice π

@[simp] theorem firstChoice_apply_zero {n : ℕ} (π : Ranking n) :
    firstChoice π = π 0 := rfl

@[simp] theorem secondChoice_apply_one {n : ℕ} (π : Ranking n) :
    secondChoice π = π 1 := rfl

@[simp] theorem firstChoice_swapTopTwo {n : ℕ} (π : Ranking n) :
    firstChoice (swapTopTwo π) = secondChoice π := by
  simp [swapTopTwo, firstChoice, secondChoice]

@[simp] theorem secondChoice_swapTopTwo {n : ℕ} (π : Ranking n) :
    secondChoice (swapTopTwo π) = firstChoice π := by
  simp [swapTopTwo, firstChoice, secondChoice]

@[simp] theorem rankOf_firstChoice {n : ℕ} (π : Ranking n) :
    rankOf π (firstChoice π) = 0 := by
  simp [rankOf, firstChoice]

@[simp] theorem rankOf_secondChoice {n : ℕ} (π : Ranking n) :
    rankOf π (secondChoice π) = 1 := by
  simp [rankOf, secondChoice]

@[simp] theorem rankOf_swapTopTwo_firstChoice {n : ℕ} (π : Ranking n) :
    rankOf (swapTopTwo π) (firstChoice π) = 1 := by
  simp [rankOf, swapTopTwo, firstChoice]

@[simp] theorem rankOf_swapTopTwo_secondChoice {n : ℕ} (π : Ranking n) :
    rankOf (swapTopTwo π) (secondChoice π) = 0 := by
  simp [rankOf, swapTopTwo, secondChoice]

theorem rankOf_swapTopTwo_of_ne_first_second {n : ℕ} (π : Ranking n)
    {c : Candidate n}
    (hfirst : c ≠ firstChoice π) (hsecond : c ≠ secondChoice π) :
    rankOf (swapTopTwo π) c = rankOf π c := by
  unfold rankOf swapTopTwo
  have h0 : π.symm c ≠ (0 : Candidate n) := by
    intro h
    apply hfirst
    have hc : π 0 = c := by
      simpa using congrArg π h.symm
    simpa [firstChoice] using hc.symm
  have h1 : π.symm c ≠ (1 : Candidate n) := by
    intro h
    apply hsecond
    have hc : π 1 = c := by
      simpa using congrArg π h.symm
    simpa [secondChoice] using hc.symm
  change (Equiv.swap (0 : Candidate n) 1) (π.symm c) = π.symm c
  rw [Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem one_lt_rankOf_of_ne_first_second {n : ℕ} (π : Ranking n)
    {c : Candidate n}
    (hfirst : c ≠ firstChoice π) (hsecond : c ≠ secondChoice π) :
    (1 : Candidate n) < rankOf π c := by
  have h0 : (rankOf π c).val ≠ 0 := by
    intro h
    apply hfirst
    have hrank : rankOf π c = 0 := Fin.ext h
    have hc : π 0 = c := by
      simpa [rankOf] using congrArg π hrank.symm
    simpa [firstChoice] using hc.symm
  have h1 : (rankOf π c).val ≠ 1 := by
    intro h
    apply hsecond
    have hrank : rankOf π c = 1 := Fin.ext h
    have hc : π 1 = c := by
      simpa [rankOf] using congrArg π hrank.symm
    simpa [secondChoice] using hc.symm
  change 1 < (rankOf π c).val
  omega

@[simp] theorem firstChoice_ne_secondChoice {n : ℕ} (π : Ranking n) :
    firstChoice π ≠ secondChoice π := by
  intro h
  have : (0 : Candidate n) = 1 := by
    simpa [firstChoice, secondChoice] using congrArg π.symm h
  have h01 : (0 : Candidate n) ≠ 1 := by
    intro hfin
    have hval : (0 : ℕ) = 1 := by
      simpa using congrArg Fin.val hfin
    exact Nat.zero_ne_one hval
  exact h01 this

theorem swapTopTwo_firstChoice_ne {n : ℕ} (π : Ranking n) :
    firstChoice (swapTopTwo π) ≠ firstChoice π := by
  rw [firstChoice_swapTopTwo]
  exact (firstChoice_ne_secondChoice π).symm

@[simp] theorem bestRemainingAfter_of_eq {n : ℕ} (π : Ranking n) :
    bestRemainingAfter π (firstChoice π) = secondChoice π := by
  simp [bestRemainingAfter]

@[simp] theorem bestRemainingAfter_apply_zero {n : ℕ} (π : Ranking n) :
    bestRemainingAfter π (π 0) = π 1 := by
  simp [bestRemainingAfter, firstChoice, secondChoice]

@[simp] theorem bestRemainingAfter_apply_eq_zero_right {n : ℕ} (π σ : Ranking n)
    (h : π 0 = σ 0) :
    bestRemainingAfter π (σ 0) = π 1 := by
  rw [← h]
  exact bestRemainingAfter_apply_zero π

@[simp] theorem bestRemainingAfter_of_ne {n : ℕ} (π : Ranking n) {c : Candidate n}
    (h : firstChoice π ≠ c) :
    bestRemainingAfter π c = firstChoice π := by
  have h' : π 0 ≠ c := by
    simpa [firstChoice] using h
  simp [bestRemainingAfter, firstChoice, h']

/-- After candidate `c` is removed, the best remaining candidate is not `c`. -/
theorem bestRemainingAfter_ne_removed {n : ℕ} (π : Ranking n) (c : Candidate n) :
    bestRemainingAfter π c ≠ c := by
  by_cases h : firstChoice π = c
  · subst c
    rw [bestRemainingAfter_of_eq]
    exact (firstChoice_ne_secondChoice π).symm
  · rw [bestRemainingAfter_of_ne π h]
    exact h

end Ranking
end SocialChoice
end AppliedModelingLib

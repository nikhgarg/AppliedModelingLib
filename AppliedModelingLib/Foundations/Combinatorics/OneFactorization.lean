import AppliedModelingLib.Foundations.Graph.EvenPairing

/-!
# One-factorizations of finite complete graphs

A one-factorization partitions the edges of a finite complete graph into
perfect matchings.  We use the involutive representation of a matching from
`EvenPairing`; the coverage field below is therefore a literal statement that
each ordered edge has one matching index, rather than a cardinality surrogate.

This is the finite-design ingredient used in the Walecki construction and in
the standard recursive constructions of Steiner triple systems.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Combinatorics

open AppliedModelingLib.Foundations.Graph

/-- A partition of the edges of the complete graph on `α` into perfect
matchings indexed by `ι`. -/
structure OneFactorization (α ι : Type*) [Fintype α] [DecidableEq α] where
  matching : ι → EvenPairing α
  pair_covered_once : ∀ x y : α, x ≠ y →
    ∃! i : ι, (matching i).perm x = y

namespace OneFactorization

variable {α ι : Type*} [Fintype α] [DecidableEq α]
variable (F : OneFactorization α ι)

/-- The unique factor containing the edge from `x` to `y`. -/
noncomputable def factorOfPair (x y : α) (hxy : x ≠ y) : ι :=
  (F.pair_covered_once x y hxy).choose

theorem matching_factorOfPair (x y : α) (hxy : x ≠ y) :
    (F.matching (F.factorOfPair x y hxy)).perm x = y :=
  (F.pair_covered_once x y hxy).choose_spec.1

theorem factorOfPair_eq_of_matching {x y : α} (hxy : x ≠ y) (i : ι)
    (hi : (F.matching i).perm x = y) :
    i = F.factorOfPair x y hxy :=
  (F.pair_covered_once x y hxy).choose_spec.2 i hi

/-- Reversing an edge does not change its factor. -/
theorem factorOfPair_swap (x y : α) (hxy : x ≠ y) :
    F.factorOfPair y x hxy.symm = F.factorOfPair x y hxy := by
  symm
  apply F.factorOfPair_eq_of_matching hxy.symm
  let i : ι := F.factorOfPair x y hxy
  have hi : (F.matching i).perm x = y := F.matching_factorOfPair x y hxy
  change (F.matching i).perm y = x
  rw [← hi]
  exact (F.matching i).apply_apply x

theorem matching_injective_at (x : α) :
    Function.Injective (fun i : ι => (F.matching i).perm x) := by
  intro i j hij
  have hix : x ≠ (F.matching i).perm x := (F.matching i).apply_ne x |>.symm
  calc
    i = F.factorOfPair x ((F.matching i).perm x) hix :=
      F.factorOfPair_eq_of_matching hix i rfl
    _ = j := (F.factorOfPair_eq_of_matching hix j hij.symm).symm

/-- Transport a one-factorization along an equivalence of its point set. -/
noncomputable def map {β : Type*} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (F : OneFactorization α ι) : OneFactorization β ι where
  matching i :=
    { perm := (e.symm.trans (F.matching i).perm).trans e
      apply_apply := by
        intro x
        apply e.symm.injective
        simpa [Equiv.trans_apply] using (F.matching i).apply_apply (e.symm x)
      apply_ne := by
        intro x h
        apply (F.matching i).apply_ne (e.symm x)
        simpa [Equiv.trans_apply] using congrArg e.symm h }
  pair_covered_once x y hxy := by
    obtain ⟨i, hi, hiuniq⟩ := F.pair_covered_once (e.symm x) (e.symm y)
      (fun h => hxy (by simpa using congrArg e h))
    refine ⟨i, ?_, ?_⟩
    · apply e.symm.injective
      simpa [Equiv.trans_apply] using hi
    · intro j hj
      apply hiuniq j
      simpa [Equiv.trans_apply] using congrArg e.symm hj

end OneFactorization

end Combinatorics
end Foundations
end AppliedModelingLib

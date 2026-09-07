import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare

/-!
# Prune retention invariant

This is the deterministic core of Lemma 13 in Appendix A.6.  A candidate is
removed exactly on a lower Compare conclusion, so a protected candidate whose
calls all return upper remains in the final pruned set.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- One Prune round retains exactly the arms receiving an upper comparison decision. -/
noncomputable def pruneRound {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (decision : Arm → CompareDecision) : Finset Arm :=
  active.filter fun arm => decision arm = .upper

/-- Iterate source-style Prune rounds over a finite active arm set. -/
noncomputable def pruneRounds {Arm : Type*} [DecidableEq Arm] :
    List (Arm → CompareDecision) → Finset Arm → Finset Arm
  | [], active => active
  | decision :: remaining, active => pruneRounds remaining (pruneRound active decision)

/-- Running an appended schedule is the same as running its two pieces in order. -/
theorem pruneRounds_append {Arm : Type*} [DecidableEq Arm]
    (first second : List (Arm → CompareDecision)) (active : Finset Arm) :
    pruneRounds (first ++ second) active = pruneRounds second (pruneRounds first active) := by
  induction first generalizing active with
  | nil => simp [pruneRounds]
  | cons decision remaining ih =>
      simp only [List.cons_append, pruneRounds]
      exact ih (pruneRound active decision)

/-- A retained upper decision keeps an active candidate through one Prune round. -/
theorem mem_pruneRound_of_upper {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (decision : Arm → CompareDecision) (kept : Arm)
    (hmem : kept ∈ active) (hupper : decision kept = .upper) :
    kept ∈ pruneRound active decision := by
  simp [pruneRound, hmem, hupper]

/-- Prune only removes arms, never introduces new ones. -/
theorem pruneRound_subset {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (decision : Arm → CompareDecision) :
    pruneRound active decision ⊆ active := by
  intro arm harm
  simpa [pruneRound] using (Finset.mem_of_mem_filter arm harm)

/-- Every iterated Prune result is a subset of its initial active set. -/
theorem pruneRounds_subset {Arm : Type*} [DecidableEq Arm]
    (rounds : List (Arm → CompareDecision)) (active : Finset Arm) :
    pruneRounds rounds active ⊆ active := by
  induction rounds generalizing active with
  | nil => simp [pruneRounds]
  | cons decision remaining ih =>
      exact Set.Subset.trans (ih (pruneRound active decision))
        (pruneRound_subset active decision)

/--
Lemma 13's deterministic retention conclusion: if every scheduled comparison
for `kept` returns upper, it remains in the result of every Prune round.
-/
theorem mem_pruneRounds_of_allUpper {Arm : Type*} [DecidableEq Arm]
    (rounds : List (Arm → CompareDecision)) (active : Finset Arm) (kept : Arm)
    (hmem : kept ∈ active)
    (hupper : ∀ decision ∈ rounds, decision kept = .upper) :
    kept ∈ pruneRounds rounds active := by
  induction rounds generalizing active with
  | nil =>
      simpa [pruneRounds] using hmem
  | cons decision remaining ih =>
      simp only [pruneRounds]
      apply ih
      · exact mem_pruneRound_of_upper active decision kept hmem (hupper decision (by simp))
      · intro later hlater
        exact hupper later (by simp [hlater])

end FalahatgarEtAl2017MaxingRanking

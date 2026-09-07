import FalahatgarEtAl2017MaxingRanking.SubsetSequentialElimination
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort

/-!
# Finite existence consequences of SST

The source observes that a finite strongly stochastically transitive model has
both a maximum and a ranking.  The proofs below make its ``simple induction''
explicit.  Pairwise completeness is the weak-totality consequence of the
paper's complementary comparison probabilities.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- Antisymmetry of centered comparison probabilities implies weak pairwise completeness. -/
theorem preferenceComplete_of_antisymmetric
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second) :
    PreferenceComplete preferenceGap := by
  intro first second
  rcases le_total 0 (preferenceGap first second) with h | h
  · exact Or.inl h
  · right
    rw [hantisymmetric]
    exact neg_nonneg.mpr h

/-- The finite-induction maximum asserted in the main-paper SST discussion. -/
theorem exists_absoluteMaximum_of_preferenceComplete_sst
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap) :
    ∃ maximum, AbsoluteMaximum preferenceGap maximum := by
  classical
  rcases exists_listMaximum_of_preferenceComplete preferenceGap hcomplete hsst
      (Finset.univ : Finset Arm).toList (by
        intro hempty
        have hmem : Classical.choice (inferInstance : Nonempty Arm) ∈
            (Finset.univ : Finset Arm).toList := by simp
        simpa [hempty] using hmem) with
    ⟨maximum, _, hmaximum⟩
  refine ⟨maximum, ?_⟩
  intro competitor
  exact hmaximum competitor (by simp)

/-- The finite-induction ranking asserted in the main-paper SST discussion. -/
theorem exists_preferenceRanking_of_preferenceComplete_sst
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap) :
    ∃ ranking : Fin (Fintype.card Arm) → Arm,
      PreferenceRanking preferenceGap ranking := by
  classical
  let relation : Arm → Arm → Prop := fun first second =>
    0 ≤ preferenceGap first second
  let relationBool : Arm → Arm → Bool := fun first second =>
    decide (relation first second)
  let input : List Arm := (Finset.univ : Finset Arm).toList
  let sorted : List Arm := input.mergeSort relationBool
  have htrans : ∀ first middle last,
      relation first middle → relation middle last → relation first last := by
    intro first middle last hfirst hsecond
    exact (hfirst.trans (le_max_left _ _)).trans
      (hsst first middle last hfirst hsecond)
  have htotal : ∀ first second, relation first second ∨ relation second first := by
    exact hcomplete
  have hpairwise : sorted.Pairwise relation := by
    dsimp [sorted]
    simpa [relationBool] using
      (List.pairwise_mergeSort
        (le := relationBool)
        (fun first middle last hfirst hsecond => by
          simpa [relationBool] using htrans first middle last
            (by simpa [relationBool] using hfirst)
            (by simpa [relationBool] using hsecond))
        (fun first second => by
          simpa [relationBool, Bool.or_eq_true] using htotal first second)
        input)
  have hperm : List.Perm sorted input := by
    exact List.mergeSort_perm input relationBool
  have hnodup : sorted.Nodup := by
    exact hperm.nodup_iff.mpr (by
      dsimp [input]
      exact Finset.nodup_toList _)
  have hall : ∀ arm : Arm, arm ∈ sorted := by
    intro arm
    exact hperm.mem_iff.mpr (by simp [input])
  have hlength : sorted.length = Fintype.card Arm := by
    calc
      sorted.length = input.length := hperm.length_eq
      _ = Fintype.card Arm := by simp [input]
  let sortedEquiv : Fin sorted.length ≃ Arm :=
    hnodup.getEquivOfForallMemList sorted hall
  let rankEquiv : Fin (Fintype.card Arm) ≃ Arm :=
    (finCongr hlength.symm).trans sortedEquiv
  refine ⟨rankEquiv, rankEquiv.bijective, ?_⟩
  intro first second hfirstSecond
  change relation (rankEquiv first) (rankEquiv second)
  by_cases heq : first = second
  · subst second
    rcases hcomplete (rankEquiv first) (rankEquiv first) with h | h <;> exact h
  · have hlt : first < second := lt_of_le_of_ne hfirstSecond heq
    exact hpairwise.rel_get_of_lt (by simpa [rankEquiv, sortedEquiv] using hlt)

end FalahatgarEtAl2017MaxingRanking

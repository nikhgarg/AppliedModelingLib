import ZhouChenLi2014OptimalPACMultipleArm.UniformBudget
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

/-!
# Tie-broken Quartile-Elimination state

The source QE rule needs a finite tie convention: Bernoulli empirical means can
tie at the lower quartile, while the subsequent resource proof requires a
strict contraction.  We keep the highest empirical scores and resolve ties by
a fixed finite enumeration, thereby removing exactly one quarter rounded down.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

/-- A fixed finite order used only to resolve equal empirical scores. -/
@[reducible] noncomputable def finiteScoreTieBreakOrder {Arm : Type*} [Fintype Arm] :
    LinearOrder Arm :=
  LinearOrder.lift' (Fintype.equivFin Arm) (Fintype.equivFin Arm).injective

/-- The total order that lists larger scores first and resolves equal scores deterministically. -/
@[reducible] noncomputable def empiricalScoreOrder {Arm : Type*} [Fintype Arm]
    (score : Arm → ℝ) : LinearOrder Arm := by
  letI : LinearOrder Arm := finiteScoreTieBreakOrder
  let coordinate : Arm → (OrderDual ℝ ×ₗ Arm) := fun arm =>
    toLex (OrderDual.toDual (score arm), arm)
  apply LinearOrder.lift' coordinate
  intro first second hequal
  exact congrArg (fun pair => (ofLex pair).2) hequal

/-- Earlier positions in the score order have no smaller empirical score. -/
theorem empiricalScoreOrder_score_antitone {Arm : Type*} [Fintype Arm]
    (score : Arm → ℝ) {first second : Arm}
    (horder : @LE.le Arm (empiricalScoreOrder score).toLE first second) :
    score second ≤ score first := by
  letI : LinearOrder Arm := finiteScoreTieBreakOrder
  change toLex (OrderDual.toDual (score first), first) ≤
    toLex (OrderDual.toDual (score second), second) at horder
  have hscore := Prod.Lex.monotone_fst _ _ horder
  exact hscore

/-- The active arms sorted from largest to smallest empirical score. -/
noncomputable def empiricalScoreSortedActiveList {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) : List Arm := by
  classical
  letI : LinearOrder Arm := empiricalScoreOrder score
  exact active.sort (· ≤ ·)

/-- Sorting the finite active set does not introduce duplicate arms. -/
theorem empiricalScoreSortedActiveList_nodup {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) :
    (empiricalScoreSortedActiveList active score).Nodup := by
  classical
  unfold empiricalScoreSortedActiveList
  letI : LinearOrder Arm := empiricalScoreOrder score
  exact Finset.sort_nodup _ _

/-- Sorting preserves the cardinality of the active set. -/
theorem empiricalScoreSortedActiveList_length {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) :
    (empiricalScoreSortedActiveList active score).length = active.card := by
  classical
  unfold empiricalScoreSortedActiveList
  letI : LinearOrder Arm := empiricalScoreOrder score
  exact Finset.length_sort _

/-- Membership in the score-sorted list is exactly membership in the active set. -/
theorem mem_empiricalScoreSortedActiveList_iff {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) (arm : Arm) :
    arm ∈ empiricalScoreSortedActiveList active score ↔ arm ∈ active := by
  classical
  unfold empiricalScoreSortedActiveList
  letI : LinearOrder Arm := empiricalScoreOrder score
  exact Finset.mem_sort _

/-- The exact number of arms kept by the tie-broken QE stage. -/
def quartileSurvivorCount (activeCount : ℕ) : ℕ := activeCount - activeCount / 4

/--
The source QE output with an explicit finite tie convention: retain the first
`|S| - floor(|S|/4)` entries in descending empirical-score order.
-/
noncomputable def quartileEliminationSurvivors {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) : Finset Arm := by
  classical
  exact (empiricalScoreSortedActiveList active score).take
    (quartileSurvivorCount active.card) |>.toFinset

/-- The tie-broken QE stage retains exactly its stated rounded survivor count. -/
theorem quartileEliminationSurvivors_card {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) :
    (quartileEliminationSurvivors active score).card = quartileSurvivorCount active.card := by
  classical
  unfold quartileEliminationSurvivors
  rw [List.toFinset_card_of_nodup]
  · rw [List.length_take, empiricalScoreSortedActiveList_length]
    exact Nat.min_eq_left (Nat.sub_le _ _)
  · exact (empiricalScoreSortedActiveList_nodup active score).take

/-- The tie-broken QE survivors are a subset of the active arms. -/
theorem quartileEliminationSurvivors_subset {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) :
    quartileEliminationSurvivors active score ⊆ active := by
  classical
  intro arm harm
  unfold quartileEliminationSurvivors at harm
  rw [List.mem_toFinset] at harm
  have hmemSort : arm ∈ empiricalScoreSortedActiveList active score :=
    List.mem_of_mem_take harm
  exact (mem_empiricalScoreSortedActiveList_iff active score arm).mp hmemSort

/-- A nonempty active set remains nonempty after the rounded QE stage. -/
theorem quartileEliminationSurvivors_nonempty {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) (hactive : active.Nonempty) :
    (quartileEliminationSurvivors active score).Nonempty := by
  have hcard : 0 < active.card := Finset.card_pos.mpr hactive
  have hsurvivorCount : 0 < quartileSurvivorCount active.card := by
    unfold quartileSurvivorCount
    omega
  apply Finset.card_pos.mp
  rw [quartileEliminationSurvivors_card]
  exact hsurvivorCount

/-- A nontrivial QE round strictly decreases the number of active arms. -/
theorem quartileSurvivorCount_lt {activeCount : ℕ} (hactiveCount : 4 ≤ activeCount) :
    quartileSurvivorCount activeCount < activeCount := by
  unfold quartileSurvivorCount
  apply Nat.sub_lt (by omega)
  exact Nat.div_pos hactiveCount (by norm_num)

/--
Among the tie-broken QE survivors, some arm maximizes the empirical score over
the preceding active set.
-/
theorem exists_quartileEliminationSurvivor_score_ge {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (score : Arm → ℝ) (hactive : active.Nonempty) :
    ∃ survivor, survivor ∈ quartileEliminationSurvivors active score ∧
      ∀ competitor ∈ active, score competitor ≤ score survivor := by
  classical
  let ordered := empiricalScoreSortedActiveList active score
  have horderedLength : ordered.length = active.card := by
    exact empiricalScoreSortedActiveList_length active score
  have horderedNonempty : ordered ≠ [] := by
    intro hempty
    rw [hempty] at horderedLength
    have hcard : 0 < active.card := Finset.card_pos.mpr hactive
    simp at horderedLength
    omega
  have hsurvivorCount : 0 < quartileSurvivorCount active.card := by
    unfold quartileSurvivorCount
    have hcard : 0 < active.card := Finset.card_pos.mpr hactive
    omega
  have hpairwise : List.Pairwise
      (@LE.le Arm (empiricalScoreOrder score).toLE) ordered := by
    dsimp [ordered]
    unfold empiricalScoreSortedActiveList
    letI : LinearOrder Arm := empiricalScoreOrder score
    exact Finset.pairwise_sort _ _
  cases hordered : ordered with
  | nil => exact False.elim (horderedNonempty hordered)
  | cons survivor tail =>
      refine ⟨survivor, ?_, ?_⟩
      · unfold quartileEliminationSurvivors
        rw [List.mem_toFinset]
        change survivor ∈ (ordered.take (quartileSurvivorCount active.card))
        rw [hordered]
        obtain ⟨keptTailCount, hcount⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsurvivorCount)
        rw [hcount]
        simp
      · intro competitor hcompetitor
        have hcompetitorMem : competitor ∈ ordered :=
          (mem_empiricalScoreSortedActiveList_iff active score competitor).mpr hcompetitor
        rw [hordered] at hcompetitorMem hpairwise
        simp only [List.mem_cons] at hcompetitorMem
        rcases hcompetitorMem with hsame | htail
        · subst competitor
          exact le_rfl
        · exact empiricalScoreOrder_score_antitone score
            (List.rel_of_pairwise_cons hpairwise htail)

/--
If an active reference arm is eliminated, every retained arm has at least its
empirical score.  This is the order fact needed for QE's one-round tail bound.
-/
theorem score_le_quartileEliminationSurvivor_of_reference_eliminated
    {Arm : Type*} [Fintype Arm] (active : Finset Arm) (score : Arm → ℝ)
    {reference survivor : Arm} (hreference : reference ∈ active)
    (heliminated : reference ∉ quartileEliminationSurvivors active score)
    (hsurvivor : survivor ∈ quartileEliminationSurvivors active score) :
    score reference ≤ score survivor := by
  classical
  let ordered := empiricalScoreSortedActiveList active score
  let survivorCount := quartileSurvivorCount active.card
  have hsurvivorOrdered : survivor ∈ ordered := by
    have hsurvivorInTake : survivor ∈ ordered.take survivorCount := by
      unfold quartileEliminationSurvivors at hsurvivor
      rw [List.mem_toFinset] at hsurvivor
      exact hsurvivor
    exact List.mem_of_mem_take hsurvivorInTake
  have hreferenceOrdered : reference ∈ ordered :=
    (mem_empiricalScoreSortedActiveList_iff active score reference).mpr hreference
  have hsurvivorIndex : ordered.idxOf survivor < survivorCount := by
    apply (List.mem_take_iff_idxOf_lt hsurvivorOrdered).mp
    unfold quartileEliminationSurvivors at hsurvivor
    rw [List.mem_toFinset] at hsurvivor
    exact hsurvivor
  have hreferenceNotTake : reference ∉ ordered.take survivorCount := by
    intro htake
    apply heliminated
    unfold quartileEliminationSurvivors
    rw [List.mem_toFinset]
    exact htake
  have hreferenceIndex : survivorCount ≤ ordered.idxOf reference := by
    by_contra hlt
    exact hreferenceNotTake
      ((List.mem_take_iff_idxOf_lt hreferenceOrdered).mpr (Nat.lt_of_not_ge hlt))
  have hsurvivorIndexBound : ordered.idxOf survivor < ordered.length :=
    List.idxOf_lt_length_of_mem hsurvivorOrdered
  have hreferenceIndexBound : ordered.idxOf reference < ordered.length :=
    List.idxOf_lt_length_of_mem hreferenceOrdered
  let survivorPosition : Fin ordered.length := ⟨ordered.idxOf survivor, hsurvivorIndexBound⟩
  let referencePosition : Fin ordered.length :=
    ⟨ordered.idxOf reference, hreferenceIndexBound⟩
  have hposition : survivorPosition ≤ referencePosition := by
    rw [Fin.le_iff_val_le_val]
    exact (Nat.le_of_lt hsurvivorIndex).trans hreferenceIndex
  have hpairwise : List.Pairwise
      (@LE.le Arm (empiricalScoreOrder score).toLE) ordered := by
    dsimp [ordered]
    unfold empiricalScoreSortedActiveList
    letI : LinearOrder Arm := empiricalScoreOrder score
    exact Finset.pairwise_sort _ _
  have horder := hpairwise.rel_get_of_le hposition
  rw [List.idxOf_get hsurvivorIndexBound, List.idxOf_get hreferenceIndexBound] at horder
  exact empiricalScoreOrder_score_antitone score horder

/--
Under a uniform empirical-accuracy event, QE retains an arm within twice that
accuracy of every preceding active-arm mean.
-/
theorem exists_quartileEliminationSurvivor_mean_near_best_of_uniformEstimate
    {Arm : Type*} [Fintype Arm] (active : Finset Arm) (mean score : Arm → ℝ)
    (accuracy : ℝ) (hactive : active.Nonempty)
    (haccurate : ∀ arm ∈ active, |score arm - mean arm| ≤ accuracy) :
    ∃ survivor, survivor ∈ quartileEliminationSurvivors active score ∧
      ∀ competitor ∈ active, mean competitor - 2 * accuracy ≤ mean survivor := by
  obtain ⟨survivor, hsurvivor, hscore⟩ :=
    exists_quartileEliminationSurvivor_score_ge active score hactive
  refine ⟨survivor, hsurvivor, ?_⟩
  intro competitor hcompetitor
  have hcompetitorAccurate := abs_le.mp (haccurate competitor hcompetitor)
  have hsurvivorAccurate := abs_le.mp
    (haccurate survivor (quartileEliminationSurvivors_subset active score hsurvivor))
  nlinarith [hscore competitor hcompetitor]

end ZhouChenLi2014OptimalPACMultipleArm

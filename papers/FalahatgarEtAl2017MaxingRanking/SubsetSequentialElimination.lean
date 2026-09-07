import FalahatgarEtAl2017MaxingRanking.SequentialElimination

/-!
# Seq-Eliminate on a sampled subset

Pick-Anchor runs Seq-Eliminate on a sampled subset, which need not contain the
global absolute maximum.  The deterministic source argument only needs an arm
that is maximal *among the input list*.  This module makes that local premise
explicit, rather than applying the global-maximum theorem to a sampled list.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- A listed arm that weakly beats every arm occurring in one Seq-Eliminate input list. -/
def ListAbsoluteMaximum
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (maximum initial : Arm) (challengers : List Arm) : Prop :=
  (maximum = initial ∨ maximum ∈ challengers) ∧
    ∀ competitor, competitor = initial ∨ competitor ∈ challengers →
      0 ≤ preferenceGap maximum competitor

/-- An output is `ε`-preferable to every arm in one finite input list. -/
def ListEpsilonMaximum
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (initial : Arm) (challengers : List Arm) (selected : Arm) : Prop :=
  ∀ competitor, competitor = initial ∨ competitor ∈ challengers →
    -epsilon ≤ preferenceGap selected competitor

/-- Every pair has a weakly preferred direction, as for the paper's complementary pairwise probabilities. -/
def PreferenceComplete
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ) : Prop :=
  ∀ first second, 0 ≤ preferenceGap first second ∨ 0 ≤ preferenceGap second first

/-- A weak maximum of the arms occurring in one finite list. -/
def ListMaximum
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (input : List Arm) (maximum : Arm) : Prop :=
  maximum ∈ input ∧ ∀ competitor ∈ input, 0 ≤ preferenceGap maximum competitor

/--
The finite induction implicit in the source's statement that an SST model has
a maximum: every nonempty input list has a weak maximum under pairwise
completeness and SST.  This is local to the list, hence applies to a sampled
Pick-Anchor subset without assuming a global maximum was selected.
-/
theorem exists_listMaximum_of_preferenceComplete
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap) :
    ∀ input : List Arm, input ≠ [] → ∃ maximum,
      ListMaximum preferenceGap input maximum := by
  intro input
  induction input with
  | nil => simp
  | cons initial challengers ih =>
      intro _
      by_cases hchallengers : challengers = []
      · subst challengers
        refine ⟨initial, ?_⟩
        constructor
        · simp
        · intro competitor hcompetitor
          have hcompetitorEq : competitor = initial := by simpa using hcompetitor
          subst competitor
          have hself := hcomplete initial initial
          rcases hself with hself | hself <;> exact hself
      · rcases ih hchallengers with ⟨maximum, hmaximumMem, hmaximum⟩
        rcases hcomplete initial maximum with hinitial | hmaximumInitial
        · refine ⟨initial, ?_⟩
          constructor
          · simp
          · intro competitor hcompetitor
            rcases List.mem_cons.mp hcompetitor with hcompetitor | hcompetitor
            · subst competitor
              rcases hcomplete initial initial with hself | hself <;> exact hself
            · exact hinitial.trans ((le_max_left _ _).trans
                (hsst initial maximum competitor hinitial (hmaximum competitor hcompetitor)))
        · refine ⟨maximum, ?_⟩
          constructor
          · exact List.mem_cons_of_mem initial hmaximumMem
          · intro competitor hcompetitor
            rcases List.mem_cons.mp hcompetitor with hcompetitor | hcompetitor
            · simpa [hcompetitor] using hmaximumInitial
            · exact hmaximum competitor hcompetitor

/--
The local form of the SST transfer used in Appendix A.3: being
`ε`-preferable to a maximum of the input list is enough to be an
`ε`-maximum of that list.
-/
theorem listEpsilonMaximum_of_epsilonPreferableTo_listAbsoluteMaximum
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum selected initial : Arm) (challengers : List Arm)
    (hmaximum : ListAbsoluteMaximum preferenceGap maximum initial challengers)
    (hpreferable : -epsilon ≤ preferenceGap selected maximum) :
    ListEpsilonMaximum preferenceGap epsilon initial challengers selected := by
  intro competitor hcompetitor
  by_cases hselectedMaximum : 0 ≤ preferenceGap selected maximum
  · have hchain := hsst selected maximum competitor hselectedMaximum
      (hmaximum.2 competitor hcompetitor)
    exact hpreferable.trans ((le_max_left _ _).trans hchain)
  by_cases hselectedCompetitor : 0 ≤ preferenceGap selected competitor
  · exact (neg_nonpos.mpr hepsilon).trans hselectedCompetitor
  have hcompetitorSelected : 0 ≤ preferenceGap competitor selected := by
    rw [hantisymmetric selected competitor]
    linarith
  have hchain := hsst maximum competitor selected
    (hmaximum.2 competitor hcompetitor) hcompetitorSelected
  have hcomparisonBound :
      preferenceGap competitor selected ≤ preferenceGap maximum selected :=
    (le_max_right _ _).trans hchain
  rw [hantisymmetric selected competitor, hantisymmetric selected maximum] at hcomparisonBound
  linarith

/--
Seq-Eliminate's deterministic argument on a sampled list.  The maximum is
only required to dominate the initial arm and listed challengers, so this
theorem is applicable to Pick-Anchor without assuming the global best arm was
sampled.
-/
theorem sequentialEliminate_listEpsilonMaximum_of_listMaximumAppears
    {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : ListAbsoluteMaximum preferenceGap maximum initial challengers) :
    ListEpsilonMaximum preferenceGap epsilon initial challengers
      (sequentialEliminate step initial challengers) := by
  apply listEpsilonMaximum_of_epsilonPreferableTo_listAbsoluteMaximum
    preferenceGap epsilon hantisymmetric hsst hepsilon maximum
    (sequentialEliminate step initial challengers) initial challengers hmaximum
  rcases hmaximum.1 with hinitial | hchallenger
  · subst initial
    apply sequentialEliminate_preserves_epsilonPreferableToAbsoluteMaximum
      preferenceGap epsilon step hantisymmetric hsst hepsilon hvalid maximum maximum challengers
    exact (neg_nonpos.mpr hepsilon).trans (hmaximum.2 maximum (Or.inl rfl))
  · obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hchallenger
    rw [hsplit, sequentialEliminate_append]
    simp only [sequentialEliminate]
    exact sequentialEliminate_preserves_epsilonPreferableToAbsoluteMaximum
      preferenceGap epsilon step hantisymmetric hsst hepsilon hvalid maximum
      (step (sequentialEliminate step initial before) maximum) after
      (hvalid (sequentialEliminate step initial before) maximum).2

/-- A Seq-Eliminate update that returns one of its inputs never leaves the input list. -/
theorem sequentialEliminate_mem_input_of_step_returns_input
    {Arm : Type*} (step : Arm → Arm → Arm)
    (hstep : ∀ incumbent challenger,
      step incumbent challenger = incumbent ∨ step incumbent challenger = challenger)
    (initial : Arm) (challengers : List Arm) :
    sequentialEliminate step initial challengers = initial ∨
      sequentialEliminate step initial challengers ∈ challengers := by
  induction challengers generalizing initial with
  | nil => simp [sequentialEliminate]
  | cons challenger remaining ih =>
      simp only [sequentialEliminate]
      rcases ih (initial := step initial challenger) with hselected | hremaining
      · rw [hselected]
        rcases hstep initial challenger with hincumbent | hchallenger
        · exact Or.inl hincumbent
        · apply Or.inr
          rw [hchallenger]
          simp
      · apply Or.inr
        exact List.mem_cons_of_mem challenger hremaining

end FalahatgarEtAl2017MaxingRanking

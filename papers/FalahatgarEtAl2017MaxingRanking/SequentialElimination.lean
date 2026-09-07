import FalahatgarEtAl2017MaxingRanking.CoreDefinitions

/-!
# Seq-Eliminate correctness

This is the deterministic core of Appendix A.3.  The stochastic Compare proof
is represented here by the two consequences it supplies at every call: the
next incumbent is no worse than the old one, and is `ε`-preferable to the
challenger that the call removes.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- A single validated call of Seq-Eliminate's `Compare(challenger, incumbent, 0, ε, _)`. -/
def SequentialEliminationStepValid {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm) : Prop :=
  ∀ incumbent challenger,
    0 ≤ preferenceGap (step incumbent challenger) incumbent ∧
      -epsilon ≤ preferenceGap (step incumbent challenger) challenger

/-- Folding the source's running-incumbent update across an ordered finite arm list. -/
def sequentialEliminate {Arm : Type*} (step : Arm → Arm → Arm) : Arm → List Arm → Arm
  | incumbent, [] => incumbent
  | incumbent, challenger :: remaining =>
      sequentialEliminate step (step incumbent challenger) remaining

/--
The two Compare conclusions required along one realized Seq-Eliminate path.
Unlike `SequentialEliminationStepValid`, this asks only for calls that the
running-incumbent execution actually makes.  This is the deterministic shape
needed before applying the source's finite union bound to randomized calls.
-/
def SequentialEliminationPathValid {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm) :
    Arm → List Arm → Prop
  | _incumbent, [] => True
  | incumbent, challenger :: remaining =>
      (0 ≤ preferenceGap (step incumbent challenger) incumbent ∧
        -epsilon ≤ preferenceGap (step incumbent challenger) challenger) ∧
        SequentialEliminationPathValid preferenceGap epsilon step
          (step incumbent challenger) remaining

/-- Path validity is preserved after consuming an initial list prefix. -/
theorem sequentialEliminationPathValid_append_suffix {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (initial : Arm) (first second : List Arm)
    (hvalid : SequentialEliminationPathValid preferenceGap epsilon step initial
      (first ++ second)) :
    SequentialEliminationPathValid preferenceGap epsilon step
      (sequentialEliminate step initial first) second := by
  induction first generalizing initial with
  | nil =>
      simpa [sequentialEliminate] using hvalid
  | cons challenger remaining ih =>
      simp only [sequentialEliminate] at ⊢
      apply ih
      simpa [SequentialEliminationPathValid] using hvalid.2

/-- A validated replacement of an absolute maximum is again an absolute maximum. -/
theorem absoluteMaximum_of_validStep {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (old new : Arm)
    (hnewOld : 0 ≤ preferenceGap new old)
    (hold : AbsoluteMaximum preferenceGap old) :
    AbsoluteMaximum preferenceGap new := by
  intro competitor
  have hchain := hsst new old competitor hnewOld (hold competitor)
  exact hnewOld.trans ((le_max_left _ _).trans hchain)

/--
One nonnegative incumbent update preserves being `ε`-preferable to an
absolute maximum.  The negative comparison case is exactly where SST and
complementarity are needed.
-/
theorem epsilonPreferableToAbsoluteMaximum_of_validStep {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum old new : Arm)
    (hold : -epsilon ≤ preferenceGap old maximum)
    (hnewOld : 0 ≤ preferenceGap new old) :
    -epsilon ≤ preferenceGap new maximum := by
  by_cases hnewMaximum : 0 ≤ preferenceGap new maximum
  · exact (neg_nonpos.mpr hepsilon).trans hnewMaximum
  have hmaximumNew : 0 ≤ preferenceGap maximum new := by
    rw [hantisymmetric new maximum]
    linarith
  have hchain := hsst maximum new old hmaximumNew hnewOld
  have hcomparisonBound : preferenceGap maximum new ≤ preferenceGap maximum old :=
    (le_max_left _ _).trans hchain
  rw [hantisymmetric new maximum, hantisymmetric old maximum] at hcomparisonBound
  linarith

/-- The absolute-maximum invariant across all later validated Seq-Eliminate calls. -/
theorem sequentialEliminate_absoluteMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (initial : Arm) (challengers : List Arm)
    (hinitial : AbsoluteMaximum preferenceGap initial) :
    AbsoluteMaximum preferenceGap (sequentialEliminate step initial challengers) := by
  induction challengers generalizing initial with
  | nil =>
      simpa [sequentialEliminate] using hinitial
  | cons challenger remaining ih =>
      simp only [sequentialEliminate]
      apply ih
      exact absoluteMaximum_of_validStep preferenceGap hsst initial (step initial challenger)
        (hvalid initial challenger).1 hinitial

/--
After one challenger is `ε`-preferably retained, the invariant survives every
later validated incumbent update.
-/
theorem sequentialEliminate_preserves_epsilonPreferableToAbsoluteMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (maximum initial : Arm) (challengers : List Arm)
    (hinitial : -epsilon ≤ preferenceGap initial maximum) :
    -epsilon ≤ preferenceGap (sequentialEliminate step initial challengers) maximum := by
  induction challengers generalizing initial with
  | nil =>
      simpa [sequentialEliminate] using hinitial
  | cons challenger remaining ih =>
      simp only [sequentialEliminate]
      apply ih
      exact epsilonPreferableToAbsoluteMaximum_of_validStep preferenceGap epsilon hantisymmetric
        hsst hepsilon maximum initial (step initial challenger) hinitial
        (hvalid initial challenger).1

/-- The absolute-maximum invariant needs only realized-path validity. -/
theorem sequentialEliminate_absoluteMaximum_of_pathValid {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (initial : Arm) (challengers : List Arm)
    (hvalid : SequentialEliminationPathValid preferenceGap epsilon step initial challengers)
    (hinitial : AbsoluteMaximum preferenceGap initial) :
    AbsoluteMaximum preferenceGap (sequentialEliminate step initial challengers) := by
  induction challengers generalizing initial with
  | nil =>
      simpa [sequentialEliminate] using hinitial
  | cons challenger remaining ih =>
      change
        (0 ≤ preferenceGap (step initial challenger) initial ∧
          -epsilon ≤ preferenceGap (step initial challenger) challenger) ∧
          SequentialEliminationPathValid preferenceGap epsilon step
            (step initial challenger) remaining at hvalid
      simp only [sequentialEliminate]
      apply ih
      · exact hvalid.2
      · exact absoluteMaximum_of_validStep preferenceGap hsst initial
          (step initial challenger) hvalid.1.1 hinitial

/-- The `ε`-preference invariant needs only realized-path validity. -/
theorem sequentialEliminate_preserves_epsilonPreferableToAbsoluteMaximum_of_pathValid
    {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum initial : Arm) (challengers : List Arm)
    (hvalid : SequentialEliminationPathValid preferenceGap epsilon step initial challengers)
    (hinitial : -epsilon ≤ preferenceGap initial maximum) :
    -epsilon ≤ preferenceGap (sequentialEliminate step initial challengers) maximum := by
  induction challengers generalizing initial with
  | nil =>
      simpa [sequentialEliminate] using hinitial
  | cons challenger remaining ih =>
      change
        (0 ≤ preferenceGap (step initial challenger) initial ∧
          -epsilon ≤ preferenceGap (step initial challenger) challenger) ∧
          SequentialEliminationPathValid preferenceGap epsilon step
            (step initial challenger) remaining at hvalid
      simp only [sequentialEliminate]
      apply ih
      · exact hvalid.2
      · exact epsilonPreferableToAbsoluteMaximum_of_validStep preferenceGap epsilon
          hantisymmetric hsst hepsilon maximum initial (step initial challenger)
          hinitial hvalid.1.1

/-- Folding over appended challenger lists is equivalent to resuming from the first fold's result. -/
theorem sequentialEliminate_append {Arm : Type*} (step : Arm → Arm → Arm)
    (initial : Arm) (first second : List Arm) :
    sequentialEliminate step initial (first ++ second) =
      sequentialEliminate step (sequentialEliminate step initial first) second := by
  induction first generalizing initial with
  | nil => simp [sequentialEliminate]
  | cons challenger remaining ih =>
      simp [sequentialEliminate, ih]

/--
Appendix A.3's deterministic conclusion: when the absolute maximum is either
the initial incumbent or appears later as a challenger, validated Compare calls
make Seq-Eliminate return an `ε`-maximum of the entire finite arm set.
-/
theorem sequentialEliminate_epsilonMaximum_of_maximumAppears {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    EpsilonMaximum preferenceGap epsilon (sequentialEliminate step initial challengers) := by
  rcases happears with hinitial | hchallenger
  · subst initial
    exact epsilonMaximum_of_absoluteMaximum preferenceGap epsilon
      (sequentialEliminate step maximum challengers) hepsilon
      (sequentialEliminate_absoluteMaximum preferenceGap epsilon step hsst hvalid maximum challengers hmaximum)
  · apply epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum preferenceGap epsilon
      hantisymmetric hsst hepsilon maximum
    · exact hmaximum
    · obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hchallenger
      rw [hsplit, sequentialEliminate_append]
      simp only [sequentialEliminate]
      exact sequentialEliminate_preserves_epsilonPreferableToAbsoluteMaximum
        preferenceGap epsilon step hantisymmetric hsst hepsilon hvalid maximum
        (step (sequentialEliminate step initial before) maximum) after
        (hvalid (sequentialEliminate step initial before) maximum).2

/--
Appendix A.3's deterministic conclusion with validity required only along the
realized Seq-Eliminate execution path.
-/
theorem sequentialEliminate_epsilonMaximum_of_maximumAppears_of_pathValid {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum initial : Arm) (challengers : List Arm)
    (hvalid : SequentialEliminationPathValid preferenceGap epsilon step initial challengers)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    EpsilonMaximum preferenceGap epsilon (sequentialEliminate step initial challengers) := by
  rcases happears with hinitial | hchallenger
  · subst initial
    exact epsilonMaximum_of_absoluteMaximum preferenceGap epsilon
      (sequentialEliminate step maximum challengers) hepsilon
      (sequentialEliminate_absoluteMaximum_of_pathValid preferenceGap epsilon step hsst
        maximum challengers hvalid hmaximum)
  · apply epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum preferenceGap epsilon
      hantisymmetric hsst hepsilon maximum
    · exact hmaximum
    · obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hchallenger
      have hvalidSplit :
          SequentialEliminationPathValid preferenceGap epsilon step initial
            (before ++ maximum :: after) := by
        simpa [hsplit] using hvalid
      have hvalidSuffix := sequentialEliminationPathValid_append_suffix
        preferenceGap epsilon step initial before (maximum :: after) hvalidSplit
      change
        (0 ≤ preferenceGap
            (step (sequentialEliminate step initial before) maximum)
            (sequentialEliminate step initial before) ∧
          -epsilon ≤ preferenceGap
            (step (sequentialEliminate step initial before) maximum) maximum) ∧
          SequentialEliminationPathValid preferenceGap epsilon step
            (step (sequentialEliminate step initial before) maximum) after at hvalidSuffix
      rw [hsplit, sequentialEliminate_append]
      simp only [sequentialEliminate]
      exact sequentialEliminate_preserves_epsilonPreferableToAbsoluteMaximum_of_pathValid
        preferenceGap epsilon step hantisymmetric hsst hepsilon maximum
        (step (sequentialEliminate step initial before) maximum) after hvalidSuffix.2
        hvalidSuffix.1.2

end FalahatgarEtAl2017MaxingRanking

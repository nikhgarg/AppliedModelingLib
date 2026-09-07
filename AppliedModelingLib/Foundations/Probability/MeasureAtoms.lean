import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open MeasureTheory
open scoped ENNReal

namespace AppliedModelingLib

/-!
# Atomic-Mass Utilities

Small reusable facts about finite measures and singleton atoms.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Paper-style atom predicate for a measure: a positive-measure set with no
proper subset of genuinely intermediate measure.
-/
def IsMeasureAtom (μ : Measure Ω) (S : Set Ω) : Prop :=
  μ S ≠ 0 ∧ ∀ E : Set Ω, E ⊂ S → μ E = 0 ∨ μ E = μ S

/-- All measure atoms have real mass at most `α`. -/
def AtomsBoundedBy (μ : Measure Ω) (α : ℝ) : Prop :=
  ∀ S : Set Ω, IsMeasureAtom μ S → μ.real S ≤ α

/-- A positive-mass singleton is a measure atom. -/
theorem isMeasureAtom_singleton_of_measure_ne_zero
    (μ : Measure Ω) {x : Ω}
    (hpos : μ ({x} : Set Ω) ≠ 0) :
    IsMeasureAtom μ ({x} : Set Ω) := by
  constructor
  · exact hpos
  · intro E hE
    left
    have hx_not_mem : x ∉ E := by
      intro hx
      exact hE.2 (by
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hx)
    have hE_empty : E = ∅ := by
      ext y
      constructor
      · intro hy
        have hyx : y = x := by
          have hys : y ∈ ({x} : Set Ω) := hE.1 hy
          simpa using hys
        subst hyx
        exact False.elim (hx_not_mem hy)
      · intro hy
        simp at hy
    rw [hE_empty, measure_empty]

/--
If all atoms are bounded and `α` is nonnegative, then all singleton masses are
bounded by `α`.
-/
theorem atomsBoundedBy_measureReal_singleton_le
    (μ : Measure Ω) {α : ℝ}
    (hα : 0 ≤ α) (hatoms : AtomsBoundedBy μ α) (x : Ω) :
    μ.real ({x} : Set Ω) ≤ α := by
  by_cases hpos : μ ({x} : Set Ω) = 0
  · have hreal : μ.real ({x} : Set Ω) = 0 := by
      simp [Measure.real, hpos]
    linarith
  · exact hatoms ({x} : Set Ω) (isMeasureAtom_singleton_of_measure_ne_zero μ hpos)

/--
A finite measure has only finitely many singleton atoms whose mass is bounded
away from zero by a fixed positive `ENNReal` threshold.
-/
theorem finite_setOf_le_measure_singleton
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Set.Finite {x : Ω | ε ≤ μ ({x} : Set Ω)} := by
  classical
  by_contra hfinite
  let S : Set Ω := {x : Ω | ε ≤ μ ({x} : Set Ω)}
  have hinfinite : S.Infinite := hfinite
  have htop : μ S = ∞ := by
    exact
      hinfinite.meas_eq_top
        (μ := μ) ⟨ε, ne_of_gt hε, by intro x hx; exact hx⟩
  exact (measure_ne_top μ S) htop

/--
Real-valued version: a finite measure has only finitely many singleton atoms
whose real mass is at least a fixed positive threshold.
-/
theorem finite_setOf_le_measureReal_singleton
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {x : Ω | ε ≤ μ.real ({x} : Set Ω)} := by
  classical
  refine Set.Finite.subset
    (finite_setOf_le_measure_singleton μ (ε := ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.2 hε)) ?_
  intro x hx
  exact ENNReal.ofReal_le_of_le_toReal hx

end AppliedModelingLib

import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Finite PMFs and real simplices

This module gives the exact finite correspondence between a `PMF` and its
vector of real atom masses.  It is the representation bridge needed when a
finite probabilistic model uses a real-simplex compactness or fixed-point
theorem.

## Main declarations

- `pmfToStdSimplex`
- `stdSimplexToPMF`
- `pmfToStdSimplex_stdSimplexToPMF`
- `stdSimplexToPMF_pmfToStdSimplex`
-/

namespace AppliedModelingLib

noncomputable section

/-- The real atom-mass vector of a finite PMF. -/
def pmfToStdSimplex {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (distribution : PMF Outcome) : stdSimplex ℝ Outcome :=
  ⟨fun outcome => (distribution outcome).toReal,
    fun outcome => ENNReal.toReal_nonneg,
    pmfToRealSum distribution⟩

/-- The finite PMF represented by a real probability-simplex vector. -/
def stdSimplexToPMF {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (mass : stdSimplex ℝ Outcome) : PMF Outcome :=
  PMF.ofFintype (fun outcome => ENNReal.ofReal (mass.1 outcome)) (by
    calc
      (∑ outcome : Outcome, ENNReal.ofReal (mass.1 outcome)) =
          ENNReal.ofReal (∑ outcome : Outcome, mass.1 outcome) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.univ : Finset Outcome))
              (f := fun outcome => mass.1 outcome)
              (fun outcome _ => mass.2.1 outcome)
      _ = 1 := by rw [mass.2.2]; norm_num)

/-- Reading a simplex-generated PMF back as a real atom mass recovers its coordinate. -/
@[simp] theorem stdSimplexToPMF_apply_toReal
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (mass : stdSimplex ℝ Outcome) (outcome : Outcome) :
    (stdSimplexToPMF mass outcome).toReal = mass.1 outcome := by
  unfold stdSimplexToPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (mass.2.1 outcome)

/-- Converting a finite PMF to real simplex coordinates and back preserves the PMF. -/
theorem stdSimplexToPMF_pmfToStdSimplex
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (distribution : PMF Outcome) :
    stdSimplexToPMF (pmfToStdSimplex distribution) = distribution := by
  apply PMF.ext
  intro outcome
  apply (ENNReal.toReal_eq_toReal_iff'
    ((stdSimplexToPMF (pmfToStdSimplex distribution)).apply_ne_top outcome)
    (distribution.apply_ne_top outcome)).mp
  simp [pmfToStdSimplex]

/-- Converting a real simplex to a finite PMF and back preserves every coordinate. -/
theorem pmfToStdSimplex_stdSimplexToPMF
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (mass : stdSimplex ℝ Outcome) :
    pmfToStdSimplex (stdSimplexToPMF mass) = mass := by
  apply Subtype.ext
  funext outcome
  exact stdSimplexToPMF_apply_toReal mass outcome

/-- The vector expectation of the PMF represented by simplex coordinates is
the corresponding finite real convex combination. -/
theorem pmfVectorExp_stdSimplexToPMF
    {Outcome V : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mass : stdSimplex ℝ Outcome) (value : Outcome → V) :
    pmfVectorExp (stdSimplexToPMF mass) value =
      ∑ outcome, mass.1 outcome • value outcome := by
  unfold pmfVectorExp
  apply Finset.sum_congr rfl
  intro outcome _
  rw [stdSimplexToPMF_apply_toReal]

end

end AppliedModelingLib

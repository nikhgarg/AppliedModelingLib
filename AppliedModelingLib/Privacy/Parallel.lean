import AppliedModelingLib.Privacy.Finite

open scoped BigOperators ENNReal

namespace AppliedModelingLib.Privacy

/-!
# Parallel independent executions

The BNS16 monitor independently executes one stable transcript mechanism on
each of several datasets.  Neighboring monitor inputs change only one dataset,
so the full vector of executions has the original privacy parameters, with no
factor equal to the number of executions.

This file proves that claim from the literal heterogeneous finite product PMF.
The key factorization realizes the product as one selected coordinate plus an
independent tape for every other coordinate, then invokes randomized
post-processing from `Privacy.Finite`.
-/

section CoordinateInsertion

variable {Index Output : Type*} [DecidableEq Index]

/-- Insert one selected output into a function containing all other coordinates. -/
def insertAt (index : Index) (output : Output)
    (rest : {other : Index // other ≠ index} → Output) : Index → Output :=
  (AppliedModelingLib.oneCoordFunEquivProdRest (α := Output) index).symm (output, rest)

@[simp]
theorem insertAt_self (index : Index) (output : Output)
    (rest : {other : Index // other ≠ index} → Output) :
    insertAt index output rest index = output := by
  simp [insertAt, AppliedModelingLib.oneCoordFunEquivProdRest]

@[simp]
theorem insertAt_ne (index other : Index) (hother : other ≠ index)
    (output : Output) (rest : {other : Index // other ≠ index} → Output) :
    insertAt index output rest other = rest ⟨other, hother⟩ := by
  simp [insertAt, AppliedModelingLib.oneCoordFunEquivProdRest, hother]

end CoordinateInsertion

section ProductFactorization

variable {Index Output : Type*}
  [Fintype Index] [DecidableEq Index]
  [Fintype Output] [DecidableEq Output]

/-- The independent output tape on every coordinate except `index`. -/
noncomputable def restTape (law : Index → PMF Output) (index : Index) :
    PMF ({other : Index // other ≠ index} → Output) :=
  AppliedModelingLib.pmfPi (fun other => law other.1)

/-- A finite product law factored through one selected coordinate. -/
noncomputable def tapedAt (law : Index → PMF Output) (index : Index) :
    PMF (Index → Output) :=
  seededPostprocess (law index) (restTape law index) (insertAt index)

omit [DecidableEq Output] in
/-- Atomwise factorization of a heterogeneous product at one coordinate. -/
theorem tapedAt_apply (law : Index → PMF Output) (index : Index)
    (sample : Index → Output) :
    tapedAt law index sample = AppliedModelingLib.pmfPi law sample := by
  classical
  unfold tapedAt seededPostprocess
  rw [PMF.bind_apply, tsum_fintype]
  rw [AppliedModelingLib.pmfPi_apply]
  simp only [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single
    ((AppliedModelingLib.oneCoordFunEquivProdRest (α := Output) index sample).2)]
  · rw [Finset.sum_eq_single (sample index)]
    · rw [if_pos]
      · unfold restTape
        rw [AppliedModelingLib.pmfPi_apply]
        rw [Fintype.prod_eq_mul_prod_compl index
          (fun i : Index => law i (sample i))]
        rw [mul_comm (law index (sample index))]
        congr 1
        rw [Finset.prod_subtype
          (s := ({index}ᶜ : Finset Index))
          (p := fun other : Index => other ≠ index)]
        · apply Finset.prod_congr rfl
          intro other _
          rfl
        · intro other
          simp
      · simp [insertAt]
        exact (AppliedModelingLib.oneCoordFunEquivProdRest
          (α := Output) index).symm_apply_apply sample |>.symm
    · intro output _ houtput
      have hne : sample ≠ insertAt index output
          ((AppliedModelingLib.oneCoordFunEquivProdRest (α := Output) index sample).2) := by
        intro heq
        have hcoord : sample index = output :=
          (congrFun heq index).trans (insertAt_self index output _)
        exact houtput hcoord.symm
      simp [hne]
    · simp
  · intro rest _ hrest
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro output _
    have hne : sample ≠ insertAt index output rest := by
      intro heq
      apply hrest
      funext other
      calc
        rest other = insertAt index output rest other.1 :=
          (insertAt_ne index other.1 other.2 output rest).symm
        _ = sample other.1 := (congrFun heq other.1).symm
        _ = (AppliedModelingLib.oneCoordFunEquivProdRest
            (α := Output) index sample).2 other := rfl
    simp [hne]
  · simp

omit [DecidableEq Output] in
/-- The selected-coordinate factorization equals the canonical product PMF. -/
theorem tapedAt_eq_pmfPi (law : Index → PMF Output) (index : Index) :
    tapedAt law index = AppliedModelingLib.pmfPi law := by
  apply PMF.ext
  intro sample
  exact tapedAt_apply law index sample

/--
Changing one coordinate law of a heterogeneous independent product preserves
the directed max-KL parameters of that coordinate.
-/
theorem ApproxDomination.pmfPi_of_one_coordinate
    {epsilon delta : ℝ} {first second : Index → PMF Output}
    (index : Index)
    (hcoordinate : ApproxDomination epsilon delta (first index) (second index))
    (hother : ∀ other : Index, other ≠ index → first other = second other) :
    ApproxDomination epsilon delta (AppliedModelingLib.pmfPi first) (AppliedModelingLib.pmfPi second) := by
  have hrest : restTape first index = restTape second index := by
    unfold restTape
    congr 1
    funext other
    exact hother other.1 other.2
  rw [← tapedAt_eq_pmfPi first index, ← tapedAt_eq_pmfPi second index]
  unfold tapedAt
  rw [hrest]
  exact hcoordinate.seededPostprocess (restTape second index) (insertAt index)

/-- Two-sided one-coordinate product closeness has no loss in parameters. -/
theorem MaxKLClose.pmfPi_of_one_coordinate
    {epsilon delta : ℝ} {first second : Index → PMF Output}
    (index : Index)
    (hcoordinate : MaxKLClose epsilon delta (first index) (second index))
    (hother : ∀ other : Index, other ≠ index → first other = second other) :
    MaxKLClose epsilon delta (AppliedModelingLib.pmfPi first) (AppliedModelingLib.pmfPi second) := by
  constructor
  · exact hcoordinate.1.pmfPi_of_one_coordinate index hother
  · exact hcoordinate.2.pmfPi_of_one_coordinate index
      (fun other hne => (hother other hne).symm)

end ProductFactorization

section ParallelRuns

variable {Index Dataset Output : Type*}
  [Fintype Index] [DecidableEq Index]
  [Fintype Output] [DecidableEq Output]

/-- Lift an adjacency relation to collections differing in one related coordinate. -/
def OneCoordinateAdjacent (adjacent : Dataset → Dataset → Prop)
    (first second : Index → Dataset) : Prop :=
  ∃ index : Index,
    adjacent (first index) (second index) ∧
      ∀ other : Index, other ≠ index → first other = second other

/-- Lifting a symmetric adjacency relation coordinatewise remains symmetric. -/
theorem oneCoordinateAdjacent_symmetric
    {adjacent : Dataset → Dataset → Prop} (h : Symmetric adjacent) :
    Symmetric (OneCoordinateAdjacent (Index := Index) adjacent) := by
  intro first second hfirstSecond
  obtain ⟨index, hadjacent, hother⟩ := hfirstSecond
  refine ⟨index, h hadjacent, ?_⟩
  intro other hne
  exact (hother other hne).symm

/-- Independent executions of the same randomized algorithm across a finite collection. -/
noncomputable def parallelRuns (algorithm : Dataset → PMF Output)
    (datasets : Index → Dataset) : PMF (Index → Output) :=
  AppliedModelingLib.pmfPi (fun index => algorithm (datasets index))

/--
Parallel composition on disjoint inputs: if one dataset changes, a vector of
independent executions retains the single-execution max-KL parameters.
-/
theorem MaxKLStable.parallelRuns
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output} {epsilon delta : ℝ}
    (h : MaxKLStable adjacent algorithm epsilon delta) :
    MaxKLStable (OneCoordinateAdjacent (Index := Index) adjacent)
      (parallelRuns (Index := Index) algorithm) epsilon delta := by
  intro first second hfirstSecond
  obtain ⟨index, hadjacent, hother⟩ := hfirstSecond
  unfold AppliedModelingLib.Privacy.parallelRuns
  apply ApproxDomination.pmfPi_of_one_coordinate index (h hadjacent)
  intro other hne
  rw [hother other hne]

end ParallelRuns

end AppliedModelingLib.Privacy

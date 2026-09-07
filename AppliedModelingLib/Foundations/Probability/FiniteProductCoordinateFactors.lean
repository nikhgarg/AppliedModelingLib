import Mathlib.MeasureTheory.Constructions.Pi

/-!
# One-coordinate factors of finite product probability spaces

This module separates a distinguished coordinate of a finite independent
product from the remaining coordinates.  It is a measure-theoretic product
identity and carries no model-specific interpretation.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory

noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]

/-- An index type is equivalent to one distinguished index together with its
complement, represented by `Option`. -/
def optionNeEquiv (i : ι) : Option {j : ι // j ≠ i} ≃ ι where
  toFun
    | none => i
    | some j => j
  invFun j := if h : j = i then none else some ⟨j, h⟩
  left_inv x := by
    cases x with
    | none => simp
    | some j => simp [j.property]
  right_inv j := by
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

/-- The measurable equivalence that retains every coordinate except `i` and
then records the distinguished coordinate. -/
noncomputable def piWithoutCoordinateEquiv (i : ι) :
    (ι → α) ≃ᵐ ({j : ι // j ≠ i} → α) × α :=
  let reindex : (Option {j : ι // j ≠ i} → α) ≃ᵐ (ι → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => α) (optionNeEquiv i)
  reindex.symm.trans
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option {j : ι // j ≠ i} => α))

/-- Separate a distinguished coordinate from a finite function sample. -/
noncomputable def piWithoutCoordinate (i : ι) :
    (ι → α) → ({j : ι // j ≠ i} → α) × α :=
  piWithoutCoordinateEquiv i

/-- Reassembling a separated finite product restores each nondistinguished
coordinate from the complement factor. -/
theorem piWithoutCoordinateEquiv_symm_apply_of_ne (i : ι)
    (x : ({j : ι // j ≠ i} → α) × α) (j : ι) (hji : j ≠ i) :
    (piWithoutCoordinateEquiv i).symm x j = x.1 ⟨j, hji⟩ := by
  simp [piWithoutCoordinateEquiv, optionNeEquiv,
    MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piUnique, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi,
    Equiv.piUnique, hji]

/-- Reassembling a separated finite product restores the distinguished
coordinate from its displayed factor. -/
theorem piWithoutCoordinateEquiv_symm_apply_self (i : ι)
    (x : ({j : ι // j ≠ i} → α) × α) :
    (piWithoutCoordinateEquiv i).symm x i = x.2 := by
  simp [piWithoutCoordinateEquiv, optionNeEquiv,
    MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piUnique, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi,
    Equiv.piUnique]

theorem measurable_piWithoutCoordinate (i : ι) :
    Measurable (piWithoutCoordinate (α := α) i) :=
  (piWithoutCoordinateEquiv i).measurable

/-- Separating a finite product retains the chosen coordinate as the second
factor. -/
theorem piWithoutCoordinate_apply_self (i : ι) (x : ι → α) :
    (piWithoutCoordinate (α := α) i x).2 = x i := by
  calc
    (piWithoutCoordinate (α := α) i x).2 =
        (piWithoutCoordinateEquiv i).symm
          (piWithoutCoordinate (α := α) i x) i := by
          exact (piWithoutCoordinateEquiv_symm_apply_self i
            (piWithoutCoordinate (α := α) i x)).symm
    _ = x i := congrFun ((piWithoutCoordinateEquiv i).symm_apply_apply x) i

/-- Separating a finite product retains every nonchosen coordinate in the
first (complement) factor. -/
theorem piWithoutCoordinate_apply_of_ne (i j : ι) (hji : j ≠ i) (x : ι → α) :
    (piWithoutCoordinate (α := α) i x).1 ⟨j, hji⟩ = x j := by
  calc
    (piWithoutCoordinate (α := α) i x).1 ⟨j, hji⟩ =
        (piWithoutCoordinateEquiv i).symm
          (piWithoutCoordinate (α := α) i x) j := by
          exact (piWithoutCoordinateEquiv_symm_apply_of_ne i
            (piWithoutCoordinate (α := α) i x) j hji).symm
    _ = x j := congrFun ((piWithoutCoordinateEquiv i).symm_apply_apply x) j

/-- The finite independent product law factors into the product law of all
other coordinates and the law of the selected coordinate. -/
theorem map_piWithoutCoordinate
    (μ : ι → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (i : ι) :
    Measure.map (piWithoutCoordinate (α := α) i) (Measure.pi μ) =
      (Measure.pi fun j : {k : ι // k ≠ i} => μ j).prod (μ i) := by
  let e : Option {j : ι // j ≠ i} ≃ ι := optionNeEquiv i
  let μoption : Option {j : ι // j ≠ i} → Measure α := fun j => μ (e j)
  let μrest : {j : ι // j ≠ i} → Measure α := fun j => μ j
  let reindex : (Option {j : ι // j ≠ i} → α) ≃ᵐ (ι → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => α) e
  let split : (Option {j : ι // j ≠ i} → α) ≃ᵐ
      ({j : ι // j ≠ i} → α) × α :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option {j : ι // j ≠ i} => α)
  letI : ∀ j : Option {j : ι // j ≠ i}, IsProbabilityMeasure (μoption j) := by
    intro j
    dsimp [μoption]
    infer_instance
  letI : ∀ j : {j : ι // j ≠ i}, IsProbabilityMeasure (μrest j) := by
    intro j
    dsimp [μrest]
    infer_instance
  have hreindex : MeasurePreserving reindex (Measure.pi μoption) (Measure.pi μ) := by
    refine ⟨reindex.measurable, ?_⟩
    simpa [reindex, μoption, e, optionNeEquiv] using
      (Measure.pi_map_piCongrLeft e μ)
  have hsplitInverse : MeasurePreserving split.symm
      ((Measure.pi μrest).prod (μ i)) (Measure.pi μoption) := by
    refine ⟨split.symm.measurable, ?_⟩
    simpa [split, μoption, μrest, e, optionNeEquiv] using
      (Measure.pi_map_piOptionEquivProd μoption)
  have hsplit : MeasurePreserving split (Measure.pi μoption)
      ((Measure.pi μrest).prod (μ i)) := hsplitInverse.symm
  change Measure.map (split ∘ reindex.symm) (Measure.pi μ) = _
  calc
    Measure.map (split ∘ reindex.symm) (Measure.pi μ) =
        Measure.map split (Measure.map reindex.symm (Measure.pi μ)) := by
          rw [Measure.map_map split.measurable reindex.symm.measurable]
    _ = Measure.map split (Measure.pi μoption) := by
          rw [hreindex.symm.map_eq]
    _ = (Measure.pi μrest).prod (μ i) := hsplit.map_eq
    _ = (Measure.pi fun j : {k : ι // k ≠ i} => μ j).prod (μ i) := by rfl

/-- Separating a coordinate is a measure-preserving map onto the explicit
product of the remaining-coordinate law and the selected-coordinate law. -/
theorem piWithoutCoordinate_measurePreserving
    (μ : ι → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (i : ι) :
    MeasurePreserving (piWithoutCoordinate (α := α) i) (Measure.pi μ)
      ((Measure.pi fun j : {k : ι // k ≠ i} => μ j).prod (μ i)) :=
  ⟨measurable_piWithoutCoordinate i, map_piWithoutCoordinate μ i⟩

end

end AppliedModelingLib.Probability

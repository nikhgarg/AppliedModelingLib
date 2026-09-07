import AppliedModelingLib.Queueing.MulticlassPalmInput
import AppliedModelingLib.Foundations.Probability.FiniteProductCoordinateFactors
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureMarkFactors

/-!
# Reversible future-mark factors for a multiclass Palm input

For one passive class, this module gives a measurable equivalence that retains
every literal arrival state and every nonfuture service mark, while exposing
that class's strictly future service marks as a separate IID stream.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance multiclassPalmFutureMarkEquivDecidableEq : DecidableEq Class := Classical.decEq Class

/-- Passive classes other than the class whose future service marks are
isolated. -/
abbrev passiveMarkComplement (i : Class) (j : {k : Class // k ≠ i}) :=
  {k : {l : Class // l ≠ i} // k ≠ j}

/-- The retained part of one passive stationary marked path. -/
abbrev stationaryPoissonWorkFutureMarkExternal :=
  (Probability.PoissonProcess.GoodSuspensionState × ℝ) × (ℕ → ℝ)

/-- Reversibly separate one passive class from the other passive classes and
then split its future service marks from its literal arrival state. -/
noncomputable def passiveStationaryPoissonWorkFutureMarkEquiv
    (i : Class) (j : {k : Class // k ≠ i}) :
    ({k : Class // k ≠ i} → StationaryPoissonWorkPath) ≃ᵐ
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal) × (ℕ → ℝ) :=
  (piWithoutCoordinateEquiv (α := StationaryPoissonWorkPath) j).trans
    (((MeasurableEquiv.refl (passiveMarkComplement i j → StationaryPoissonWorkPath)).prodCongr
      Probability.Queueing.stationaryPoissonWorkFutureMarkEquiv).trans
      MeasurableEquiv.prodAssoc.symm)

/-- Reversibly split the full selected-arrival carrier at one passive class.
The first component retains the selected Palm path and all data other than the
isolated future service-mark stream. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv
    (i : Class) (j : {k : Class // k ≠ i}) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i ≃ᵐ
      ((((ℤ → ℝ) × (ℤ → ℝ)) ×
        ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
          stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)) :=
  ((MeasurableEquiv.refl ((ℤ → ℝ) × (ℤ → ℝ))).prodCongr
    (passiveStationaryPoissonWorkFutureMarkEquiv i j)).trans
    MeasurableEquiv.prodAssoc.symm

/-- The complete selected-class coordinate is retained in the external part
of the future-mark factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ))) :
    ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1 = x.1.1 := by
  rfl

/-- The complete selected Palm path is unchanged when only the isolated
future-mark stream changes. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (hxy : x.1 = y.1) :
    ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1 =
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).1 := by
  rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath]
  exact congrArg Prod.fst hxy

/-- Reassembling the passive factor restores the isolated stationary marked
path from its external coordinates and future mark stream. -/
theorem passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_selected
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
      stationaryPoissonWorkFutureMarkExternal) × (ℕ → ℝ)) :
    (passiveStationaryPoissonWorkFutureMarkEquiv i j).symm x j =
      Probability.Queueing.stationaryPoissonWorkFromFutureMarkFactors
        (x.1.2, x.2) := by
  change (piWithoutCoordinateEquiv j).symm
    (x.1.1, Probability.Queueing.stationaryPoissonWorkFromFutureMarkFactors
      (x.1.2, x.2)) j = _
  rw [piWithoutCoordinateEquiv_symm_apply_self]

/-- Reassembling the passive factor restores every nonselected passive path
from the retained external coordinates. -/
theorem passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_of_ne
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
      stationaryPoissonWorkFutureMarkExternal) × (ℕ → ℝ))
    (k : {l : Class // l ≠ i}) (hkj : k ≠ j) :
    (passiveStationaryPoissonWorkFutureMarkEquiv i j).symm x k =
      x.1.1 ⟨k, hkj⟩ := by
  change (piWithoutCoordinateEquiv j).symm
    (x.1.1, Probability.Queueing.stationaryPoissonWorkFromFutureMarkFactors
      (x.1.2, x.2)) k = _
  rw [piWithoutCoordinateEquiv_symm_apply_of_ne]

/-- On the factored carrier, the future mark at coordinate `n` reconstructs
as the positive two-sided mark at label `n + 1`. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (n : ℕ) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2
      (Int.ofNat (n + 1)) = x.2 n := by
  change (((passiveStationaryPoissonWorkFutureMarkEquiv i j).symm
    (x.1.2, x.2)) j).2 (Int.ofNat (n + 1)) = x.2 n
  rw [passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_selected]
  rfl

/-- The reconstructed passive arrival state is part of the external factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ))) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1 =
      x.1.2.2.1.1 := by
  change (((passiveStationaryPoissonWorkFutureMarkEquiv i j).symm
    (x.1.2, x.2)) j).1 = x.1.2.2.1.1
  rw [passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_selected]
  rfl

/-- Every nonisolated passive path on the factored carrier is determined by
the external factor alone. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (k : {l : Class // l ≠ i}) (hkj : k ≠ j) :
    ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 k =
      x.1.2.1 ⟨k, hkj⟩ := by
  change ((passiveStationaryPoissonWorkFutureMarkEquiv i j).symm
    (x.1.2, x.2)) k = _
  rw [passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_of_ne]

/-- The isolated passive arrival state is unchanged when only the future-mark
stream coordinate of the factored carrier changes. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (hxy : x.1 = y.1) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1 =
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2 j).1 := by
  rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival]
  simpa [hxy]

/-- Every nonisolated passive path is unchanged when only the future-mark
stream coordinate of the factored carrier changes. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (k : {l : Class // l ≠ i}) (hkj : k ≠ j) (hxy : x.1 = y.1) :
    ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 k =
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2 k := by
  rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath
      i j x k hkj,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath
      i j y k hkj]
  simpa [hxy]

/-- One isolated future service mark agrees whenever the corresponding IID
coordinates of two factored carriers agree. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark_eq_of_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (n : ℕ) (hcoordinate : x.2 n = y.2 n) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2
      (Int.ofNat (n + 1)) =
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2 j).2
        (Int.ofNat (n + 1)) := by
  rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark]
  exact hcoordinate

/-- The reconstructed passive origin mark is part of the external factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginMark
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ))) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2 0 =
      x.1.2.2.1.2 := by
  change (((passiveStationaryPoissonWorkFutureMarkEquiv i j).symm
    (x.1.2, x.2)) j).2 0 = x.1.2.2.1.2
  rw [passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_selected]
  rfl

/-- The reconstructed passive past marks are part of the external factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastMark
    (i : Class) (j : {k : Class // k ≠ i})
    (x : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (n : ℕ) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2
      (Int.negSucc n) = x.1.2.2.2 n := by
  change (((passiveStationaryPoissonWorkFutureMarkEquiv i j).symm
    (x.1.2, x.2)) j).2 (Int.negSucc n) = x.1.2.2.2 n
  rw [passiveStationaryPoissonWorkFutureMarkEquiv_symm_apply_selected]
  rfl

/-- The isolated passive origin mark is unchanged when only the exposed
future-mark stream changes. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginMark_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (hxy : x.1 = y.1) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2 0 =
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2 j).2 0 := by
  rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginMark,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginMark]
  simpa [hxy]

/-- The isolated passive past marks are unchanged when only the exposed
future-mark stream changes. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastMark_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (n : ℕ) (hxy : x.1 = y.1) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2
      (Int.negSucc n) =
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2 j).2
        (Int.negSucc n) := by
  rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastMark,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastMark]
  simpa [hxy]

/-- Every isolated positive mark strictly before a visible IID prefix agrees
when the external factors and that prefix agree. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark_eq_of_prefix
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (N n : ℕ) (hn : n < N)
    (hprefix : ∀ m < N, x.2 m = y.2 m) :
    (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).2
      (Int.ofNat (n + 1)) =
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2 j).2
        (Int.ofNat (n + 1)) := by
  exact multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark_eq_of_eq
    i j x y n (hprefix n hn)

/-- A selected-class work mark is determined by the external part of the
future-mark factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (m : ℤ) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) i m =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) i m := by
  simp only [multiclassStationaryPoissonWorkClassTaggedRequirementAt]
  have hpath := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath_eq_of_fst_eq
    i j x y hxy
  exact congrFun (congrArg Prod.snd hpath) m

/-- A work mark of every nonisolated passive class is determined by the
external part of the future-mark factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassiveRequirement_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (k : Class) (hki : k ≠ i) (hkj : (⟨k, hki⟩ : {l : Class // l ≠ i}) ≠ j)
    (m : ℤ) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) k m =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) k m := by
  simp only [multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg hki]
  have hpath := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath_eq_of_fst_eq
    i j x y ⟨k, hki⟩ hkj hxy
  exact congrFun (congrArg Prod.snd hpath) m

/-- The isolated passive origin work mark is determined by the external part
of the future-mark factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginRequirement_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1 0 =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) j.1 0 := by
  simp only [multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg j.2]
  exact multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginMark_eq_of_fst_eq
    i j x y hxy

/-- The isolated passive past work marks are determined by the external part
of the future-mark factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastRequirement_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (m : ℕ) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1
        (Int.negSucc m) =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) j.1
          (Int.negSucc m) := by
  simp only [multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg j.2]
  exact multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastMark_eq_of_fst_eq
    i j x y m hxy

/-- An isolated future work mark strictly before a visible IID prefix agrees
whenever that prefix and the external factors agree. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveFutureRequirement_eq_of_prefix
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (N m : ℕ) (hm : m < N)
    (hprefix : ∀ r < N, x.2 r = y.2 r) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1
        (Int.ofNat (m + 1)) =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) j.1
          (Int.ofNat (m + 1)) := by
  simp only [multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg j.2]
  exact multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark_eq_of_prefix
    i j x y N m hm hprefix

/-- Every literal arrival coordinate of the reconstructed selected carrier is
fixed by the external part of the future-mark factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : ((((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ)))
    (k : Class) (m : ℤ) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) k m =
      multiclassStationaryPoissonWorkClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) k m := by
  by_cases hki : k = i
  · subst k
    simp only [multiclassStationaryPoissonWorkClassTaggedArrival]
    rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath,
      multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath]
    simpa [hxy]
  · simp only [multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hki]
    change Probability.PoissonProcess.suspensionBaseArrival
      ((((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2
        ⟨k, hki⟩).1) m =
      Probability.PoissonProcess.suspensionBaseArrival
        ((((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y).2
          ⟨k, hki⟩).1) m
    by_cases hkj : (⟨k, hki⟩ : {l : Class // l ≠ i}) = j
    · subst j
      rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival_eq_of_fst_eq
        i ⟨k, hki⟩ x y hxy]
    · rw [multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath_eq_of_fst_eq
        i j x y ⟨k, hki⟩ hkj hxy]

/-- Factoring a selected-arrival carrier reads the isolated class's positive
two-sided mark at label `n + 1` into future coordinate `n`. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_futureMark
    (i : Class) (j : {k : Class // k ≠ i})
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (n : ℕ) :
    (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j z).2 n =
      (z.2 j).2 (Int.ofNat (n + 1)) := by
  symm
  simpa using
    (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark
      i j (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j z) n)

/-- The passive future-mark equivalence is measure preserving under the
finite independent stationary input law. -/
theorem passiveStationaryPoissonWorkFutureMarkEquiv_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (passiveStationaryPoissonWorkFutureMarkEquiv i j)
      (Measure.pi fun k : {k : Class // k ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1))
      (
        (
          (Measure.pi fun k : passiveMarkComplement i j =>
            Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
            (((Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)).prod
              (ProbabilityTheory.expMeasure (1 : ℝ))).prod
              (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))
        ).prod (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
      ) := by
  let μ : {k : Class // k ≠ i} → Measure StationaryPoissonWorkPath := fun k =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)
  let ρ : Measure (passiveMarkComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate k.1.1)
  let E : Measure stationaryPoissonWorkFutureMarkExternal :=
    ((Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)).prod
      (ProbabilityTheory.expMeasure (1 : ℝ))).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let F : Measure (ℕ → ℝ) :=
    Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)
  letI : ∀ k : {k : Class // k ≠ i}, IsProbabilityMeasure (μ k) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    haveI : IsProbabilityMeasure
        (Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)) :=
      Probability.PoissonProcess.isProbabilityMeasure_goodSuspensionMeasure
        (harrivalRate j.1)
    haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
    haveI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
    infer_instance
  letI : IsProbabilityMeasure F := by
    dsimp [F]
    exact Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  let hsplit := piWithoutCoordinate_measurePreserving μ j
  let hmarks := Probability.Queueing.stationaryPoissonWorkFutureMarkFactors_measurePreserving
    (harrivalRate j.1)
  let hproduct := (MeasurePreserving.id ρ).prod hmarks
  let hassoc := (measurePreserving_prodAssoc ρ E F).symm
  change MeasurePreserving (passiveStationaryPoissonWorkFutureMarkEquiv i j)
    (Measure.pi μ) ((ρ.prod E).prod F)
  convert hassoc.comp (hproduct.comp hsplit) using 1

/-- The law of every factor retained while one passive class's strictly future
service marks are exposed as a separate IID stream. -/
noncomputable def multiclassPalmFutureMarkExternalMeasure
    (arrivalRate : Class → ℝ) (i : Class) (j : {k : Class // k ≠ i}) :
    Measure (((ℤ → ℝ) × (ℤ → ℝ)) ×
      ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
        stationaryPoissonWorkFutureMarkExternal)) :=
  ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
    (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
    ((Measure.pi fun k : passiveMarkComplement i j =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
      (((Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)).prod
        (ProbabilityTheory.expMeasure (1 : ℝ))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))

/-- The external component of the selected-Palm future-mark factor is a
probability measure whenever every class has positive arrival rate. -/
theorem isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) := by
  dsimp [multiclassPalmFutureMarkExternalMeasure]
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : ∀ k : passiveMarkComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure (Measure.pi fun k : passiveMarkComplement i j =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)) := by
    infer_instance
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)) :=
    Probability.PoissonProcess.isProbabilityMeasure_goodSuspensionMeasure
      (harrivalRate j.1)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  infer_instance

/-- The full selected-arrival future-mark equivalence is measure preserving
onto an external-state/IID-future-mark product law. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      (
        (
          ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
            (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
            ((Measure.pi fun k : passiveMarkComplement i j =>
              Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
              (((Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)).prod
                (ProbabilityTheory.expMeasure (1 : ℝ))).prod
                (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
        ).prod (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
      ) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let ρ : Measure (passiveMarkComplement i j → StationaryPoissonWorkPath) :=
    Measure.pi fun k => Probability.Queueing.stationaryPoissonWorkMeasure
      (arrivalRate k.1.1)
  let E : Measure stationaryPoissonWorkFutureMarkExternal :=
    ((Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)).prod
      (ProbabilityTheory.expMeasure (1 : ℝ))).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let F : Measure (ℕ → ℝ) :=
    Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)
  letI : ∀ k : {k : Class // k ≠ i},
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1)
  letI : ∀ k : passiveMarkComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : IsProbabilityMeasure
      (Measure.pi fun k : {k : Class // k ≠ i} =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1)) := by
    infer_instance
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    haveI : IsProbabilityMeasure
        (Probability.PoissonProcess.goodSuspensionMeasure (arrivalRate j.1)) :=
      Probability.PoissonProcess.isProbabilityMeasure_goodSuspensionMeasure
        (harrivalRate j.1)
    haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
    haveI : IsProbabilityMeasure
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
      Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
    infer_instance
  letI : IsProbabilityMeasure F := by
    dsimp [F]
    exact Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  let hpassive := passiveStationaryPoissonWorkFutureMarkEquiv_measurePreserving
    arrivalRate harrivalRate i j
  let hproduct := (MeasurePreserving.id tagged.Ptag).prod hpassive
  let hassoc := (measurePreserving_prodAssoc tagged.Ptag (ρ.prod E) F).symm
  change MeasurePreserving (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j)
    (tagged.Ptag.prod passive.Pbase) ((tagged.Ptag.prod (ρ.prod E)).prod F)
  convert hassoc.comp hproduct using 1

/-- The same factorization expressed through the reusable external-state
measure API. -/
theorem multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i}) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  simpa [multiclassPalmFutureMarkExternalMeasure] using
    (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving
      arrivalRate harrivalRate i j)

end

end AppliedModelingLib.Queueing

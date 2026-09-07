import AppliedModelingLib.Queueing.MulticlassPalmInput
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors

/-!
# Selected-service-mark factors in a multiclass Palm input

The service requirement of a distinguished arrival is independent of its
arrival path, its other service marks, and every passive stationary input.
This module exposes that product structure without making any queueing claim.
Later queueing arguments use the factorization only after proving that their
service-start observable is measurable with respect to the retained factors.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- Split the marked selected-Palm input into its complete arrival path, the
selected service mark, the strictly positive and negative mark tails, and all
passive stationary input paths. -/
def multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors
    (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      ((ℤ → ℝ) × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ))) ×
        ({j : Class // j ≠ i} → StationaryPoissonWorkPath) :=
  fun z =>
    ((z.1.1, Probability.PoissonProcess.twoSidedHeadPositiveNegative z.1.2), z.2)

/-- The selected-mark factor map is Borel. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors
    (i : Class) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors i) := by
  exact ((measurable_fst.comp measurable_fst).prodMk
    (Probability.PoissonProcess.measurable_twoSidedHeadPositiveNegative.comp
      (measurable_snd.comp measurable_fst))).prodMk measurable_snd

/-- Under the concrete multiclass Palm law, the selected service mark and its
two mark tails are the explicit IID factors of the selected marked path; all
passive stationary paths remain independent. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (((ProbabilityTheory.expMeasure (1 : ℝ)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase := by
  let G : Measure (ℤ → ℝ) :=
    Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)
  let M : Measure (ℤ → ℝ) :=
    Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)
  let R : Measure ({j : Class // j ≠ i} → StationaryPoissonWorkPath) :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  letI : IsProbabilityMeasure G :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure M :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure R := by
    dsimp [R]
    exact (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  change Measure.map
      (Prod.map (Prod.map id Probability.PoissonProcess.twoSidedHeadPositiveNegative) id)
      ((G.prod M).prod R) =
    (G.prod (((ProbabilityTheory.expMeasure (1 : ℝ)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod R
  rw [← Measure.map_prod_map (G.prod M) R
      (measurable_id.prodMap
        Probability.PoissonProcess.measurable_twoSidedHeadPositiveNegative) measurable_id,
    ← Measure.map_prod_map G M measurable_id
      Probability.PoissonProcess.measurable_twoSidedHeadPositiveNegative,
    Measure.map_id,
    Probability.PoissonProcess.map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure
      (by norm_num),
    Measure.map_id]

/-- The factors other than the selected customer's service mark.  The two
mark tails retain every other selected-class service requirement. -/
abbrev MulticlassPalmSelectedMarkExternalCarrier (i : Class) :=
  ((ℤ → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))) ×
    ({j : Class // j ≠ i} → StationaryPoissonWorkPath)

/-- Reorder a raw selected-mark split so the selected service mark is a
separate final coordinate. -/
def multiclassPalmSelectedMarkFactorReorder
    {α β γ δ ε : Type*} :
    (α × ((β × γ) × δ)) × ε → ((α × (γ × δ)) × ε) × β :=
  fun x => (((x.1.1, (x.1.2.1.2, x.1.2.2)), x.2), x.1.2.1.1)

/-- The factor reordering is Borel. -/
theorem measurable_multiclassPalmSelectedMarkFactorReorder
    {α β γ δ ε : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace ε] :
    Measurable (@multiclassPalmSelectedMarkFactorReorder α β γ δ ε) := by
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · apply Measurable.prodMk
      · exact measurable_fst.comp measurable_fst
      · exact (measurable_snd.comp (measurable_fst.comp
          (measurable_snd.comp measurable_fst))).prodMk
            (measurable_snd.comp (measurable_snd.comp measurable_fst))
    · exact measurable_snd
  · exact measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp measurable_fst))

/-- The selected service mark is isolated as a separate coordinate while all
input data relevant to the rest of the queue remains in the external factor. -/
def multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors
    (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      MulticlassPalmSelectedMarkExternalCarrier i × ℝ :=
  multiclassPalmSelectedMarkFactorReorder ∘
    multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors i

/-- The separated final coordinate is exactly the selected customer's
zero-indexed unit service mark. -/
theorem multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors_snd
    (i : Class) (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i z i 0 := by
  simp [multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors,
    multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors,
    multiclassPalmSelectedMarkFactorReorder,
    Probability.PoissonProcess.twoSidedHeadPositiveNegative_apply,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt]

/-- Reconstruct a selected-Palm sample from the retained external input data
and the separated selected service mark. -/
def multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors
    (i : Class) :
    MulticlassPalmSelectedMarkExternalCarrier i × ℝ →
      MulticlassStationaryPoissonWorkClassTaggedSample Class i :=
  fun x =>
    ((x.1.1.1, fun k => match k with
      | 0 => x.2
      | Int.ofNat (n + 1) => x.1.1.2.1 n
      | Int.negSucc n => x.1.1.2.2 n), x.1.2)

/-- The reconstruction from selected-mark factors is Borel. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors
    (i : Class) :
    Measurable (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i) := by
  unfold multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · exact measurable_fst.comp (measurable_fst.comp measurable_fst)
    · apply measurable_pi_iff.2
      intro k
      cases k with
      | ofNat n =>
          cases n with
          | zero => exact measurable_snd
          | succ n => exact ((measurable_pi_apply n).comp
              (measurable_fst.comp (measurable_snd.comp
                (measurable_fst.comp measurable_fst))))
      | negSucc n => exact ((measurable_pi_apply n).comp
          (measurable_snd.comp (measurable_snd.comp
            (measurable_fst.comp measurable_fst))))
  · exact measurable_snd.comp measurable_fst

/-- Holding the external factor fixed holds the selected arrival path fixed. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_selectedArrivalPath_eq_of_fst_eq
    (i : Class) (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (hxy : x.1 = y.1) :
    (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).1.1 =
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y).1.1 := by
  rcases x with ⟨x, selectedMark⟩
  rcases y with ⟨y, selectedMark'⟩
  change x = y at hxy
  subst y
  rfl

/-- Holding the external factor fixed holds every passive marked input path
fixed. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_passivePath_eq_of_fst_eq
    (i : Class) (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (j : {k : Class // k ≠ i}) (hxy : x.1 = y.1) :
    (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x).2 j =
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y).2 j := by
  rcases x with ⟨x, selectedMark⟩
  rcases y with ⟨y, selectedMark'⟩
  change x = y at hxy
  subst y
  rfl

/-- The selected service-mark tail is fixed by the external factor away from
the distinguished zero-indexed mark. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_selectedRequirement_eq_of_fst_eq_of_ne_zero
    (i : Class) (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (m : ℤ) (hm : m ≠ 0) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) i m =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) i m := by
  rcases x with ⟨x, selectedMark⟩
  rcases y with ⟨y, selectedMark'⟩
  change x = y at hxy
  subst y
  cases m with
  | ofNat m =>
      cases m with
      | zero => exact (hm rfl).elim
      | succ _ => rfl
  | negSucc _ => rfl

/-- All physical arrival epochs are fixed by the selected-mark external
factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_arrival_eq_of_fst_eq
    (i : Class) (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (j : Class) (m : ℤ) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) j m =
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) j m := by
  classical
  by_cases hji : j = i
  · subst j
    simp only [multiclassStationaryPoissonWorkClassTaggedArrival, dif_pos]
    exact congrArg (fun gaps => Probability.PoissonProcess.candidatePalmArrival gaps m)
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_selectedArrivalPath_eq_of_fst_eq
        i x y hxy)
  · simp only [multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hji]
    exact congrArg (fun path => Probability.Queueing.stationaryPoissonWorkArrival path m)
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_passivePath_eq_of_fst_eq
        i x y ⟨j, hji⟩ hxy)

/-- Every nonselected service requirement is fixed by the selected-mark
external factor. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_requirement_eq_of_fst_eq
    (i : Class) (x y : MulticlassPalmSelectedMarkExternalCarrier i × ℝ)
    (j : Class) (m : ℤ)
    (hnotSelected : j ≠ i ∨ m ≠ 0) (hxy : x.1 = y.1) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) j m =
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i
        (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i y) j m := by
  classical
  by_cases hji : j = i
  · subst j
    have hm : m ≠ 0 := by simpa using hnotSelected
    exact multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_selectedRequirement_eq_of_fst_eq_of_ne_zero
      i x y m hm hxy
  · simp only [multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_neg hji]
    exact congrArg (fun path => path.2 m)
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_passivePath_eq_of_fst_eq
        i x y ⟨j, hji⟩ hxy)

/-- Splitting and reconstructing the selected marked Palm input is pointwise
the identity. -/
theorem multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_apply
    (i : Class) (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z) = z := by
  rcases z with ⟨⟨gap, mark⟩, passive⟩
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext k
      cases k with
      | ofNat n =>
          cases n with
          | zero => simp [multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors,
              multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors,
              multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors,
              multiclassPalmSelectedMarkFactorReorder,
              Probability.PoissonProcess.twoSidedHeadPositiveNegative_apply]
          | succ n => rfl
      | negSucc n => rfl
  · rfl

/-- Reconstructing then splitting selected-mark factors is pointwise the
identity. -/
theorem multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors_from_apply
    (i : Class) (x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ) :
    multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x) = x := by
  rcases x with ⟨⟨⟨gap, future, past⟩, passive⟩, head⟩
  simp [multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors,
    multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors,
    multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors,
    multiclassPalmSelectedMarkFactorReorder,
    Probability.PoissonProcess.twoSidedHeadPositiveNegative_apply]

/-- The selected-mark external factor is a measurable equivalence. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv
    (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i ≃ᵐ
      MulticlassPalmSelectedMarkExternalCarrier i × ℝ where
  toFun := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i
  invFun := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i
  left_inv := multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_apply i
  right_inv := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors_from_apply i
  measurable_toFun := by
    exact (measurable_multiclassPalmSelectedMarkFactorReorder).comp
      (measurable_multiclassStationaryPoissonWorkClassTaggedSelectedMarkFactors i)
  measurable_invFun :=
    measurable_multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i

/-- The selected-mark external factor has the explicit product law in which
the selected unit-exponential service mark is independent of the retained
input data. -/
theorem map_multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    Measure.map (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
        (ProbabilityTheory.expMeasure (1 : ℝ)) := by
  let A : Measure (ℤ → ℝ) :=
    Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let C : Measure (ℕ → ℝ) :=
    Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)
  let D : Measure (ℕ → ℝ) :=
    Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)
  let E : Measure ({j : Class // j ≠ i} → StationaryPoissonWorkPath) :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  letI : IsProbabilityMeasure A :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure B :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure C :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure D :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    exact (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  let reorder : ((ℤ → ℝ) × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ))) ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath) →
      (((ℤ → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))) ×
        ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) × ℝ :=
    multiclassPalmSelectedMarkFactorReorder
  let h₁ := measurePreserving_prodAssoc A ((B.prod C).prod D) E
  let h₂ := (MeasurePreserving.id A).prod
    (measurePreserving_prodAssoc (B.prod C) D E)
  let h₃ := (MeasurePreserving.id A).prod
    (measurePreserving_prodAssoc B C (D.prod E))
  let h₄ := (MeasurePreserving.id A).prod
    (Measure.measurePreserving_swap (μ := B) (ν := C.prod (D.prod E)))
  let h₅ := (measurePreserving_prodAssoc A (C.prod (D.prod E)) B).symm
  let h₆ := (MeasurePreserving.id A).prod
    (measurePreserving_prodAssoc C D E).symm
  let h₇ := (measurePreserving_prodAssoc A (C.prod D) E).symm
  let h₈ := h₆.prod (MeasurePreserving.id B)
  let h₉ := h₇.prod (MeasurePreserving.id B)
  have hreorder : MeasurePreserving reorder
      ((A.prod ((B.prod C).prod D)).prod E)
      (((A.prod (C.prod D)).prod E).prod B) := by
    convert h₉.comp (h₈.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))))) using 1
  change Measure.map (reorder ∘
      Prod.map (Prod.map id Probability.PoissonProcess.twoSidedHeadPositiveNegative) id)
      (((A.prod (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod E)) =
    (((A.prod (C.prod D)).prod E).prod B)
  calc
    Measure.map (reorder ∘
        Prod.map (Prod.map id Probability.PoissonProcess.twoSidedHeadPositiveNegative) id)
        ((A.prod (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod E) =
        Measure.map reorder
          (Measure.map (Prod.map
            (Prod.map id Probability.PoissonProcess.twoSidedHeadPositiveNegative) id)
            ((A.prod (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod E)) := by
              symm
              rw [Measure.map_map hreorder.measurable
                ((measurable_id.prodMap
                  Probability.PoissonProcess.measurable_twoSidedHeadPositiveNegative).prodMap
                    measurable_id)]
    _ = Measure.map reorder ((A.prod ((B.prod C).prod D)).prod E) := by
      rw [← Measure.map_prod_map (A.prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))) E
          (measurable_id.prodMap
            Probability.PoissonProcess.measurable_twoSidedHeadPositiveNegative) measurable_id,
        ← Measure.map_prod_map A
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) measurable_id
          Probability.PoissonProcess.measurable_twoSidedHeadPositiveNegative,
        Measure.map_id,
        Probability.PoissonProcess.map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure
          (by norm_num)]
      rw [Measure.map_id]
    _ = ((A.prod (C.prod D)).prod E).prod B := hreorder.map_eq

/-- The selected-mark factor equivalence transports the concrete multiclass
Palm law to the displayed product law. -/
theorem multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    MeasurePreserving
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      ((((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
        (ProbabilityTheory.expMeasure (1 : ℝ))) := by
  refine ⟨(multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i).measurable,
    ?_⟩
  exact map_multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors
    arrivalRate harrivalRate i

/-- Any Borel statistic of the retained external input is independent of the
selected customer's unit-exponential service mark.  This is the expectation
form used after a queueing argument proves that a waiting-time selector does
not inspect that customer's own mark. -/
theorem integral_multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternal_mul_selectedMark
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (f : MulticlassPalmSelectedMarkExternalCarrier i → ℝ)
    (hf : Measurable f) :
    ∫ z, f (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).1 *
        (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
    ∫ z, f (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).1 ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let E : Measure (MulticlassPalmSelectedMarkExternalCarrier i) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let e := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure B :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpres : MeasurePreserving e P (E.prod B) := by
    simpa [e, P, E, B] using
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv_measurePreserving
        arrivalRate harrivalRate i)
  have hmul : Measurable (fun x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ =>
      f x.1 * x.2) := (hf.comp measurable_fst).mul measurable_snd
  have hfst : Measurable (fun x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ =>
      f x.1) := hf.comp measurable_fst
  calc
    ∫ z, f (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).1 *
        (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2 ∂P =
        ∫ x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ, f x.1 * x.2 ∂(E.prod B) := by
          simpa [e] using hpres.hasLaw.integral_comp hmul.aestronglyMeasurable
    _ = (∫ x, f x ∂E) * (∫ y, y ∂B) := by
      exact MeasureTheory.integral_prod_mul f (fun y : ℝ => y)
    _ = ∫ x, f x ∂E := by
      rw [AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num : (0 : ℝ) < 1)]
      norm_num [B]
    _ = ∫ x : MulticlassPalmSelectedMarkExternalCarrier i × ℝ, f x.1 ∂(E.prod B) := by
      rw [MeasureTheory.integral_fun_fst]
      simp [MeasureTheory.probReal_univ]
    _ = ∫ z, f (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).1 ∂P := by
      symm
      simpa [e] using hpres.hasLaw.integral_comp hfst.aestronglyMeasurable

/-- The preceding factorization written in the original tagged-input
coordinates: a Borel external selector is independent of the selected class's
zero-indexed unit service requirement. -/
theorem integral_multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternal_mul_requirementAt_zero
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (f : MulticlassPalmSelectedMarkExternalCarrier i → ℝ)
    (hf : Measurable f) :
    ∫ z, f (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).1 *
        multiclassStationaryPoissonWorkClassTaggedRequirementAt i z i 0 ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
    ∫ z, f (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).1 ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  simpa only [multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors_snd]
    using
      (integral_multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternal_mul_selectedMark
        arrivalRate harrivalRate i f hf)

end

end AppliedModelingLib.Queueing

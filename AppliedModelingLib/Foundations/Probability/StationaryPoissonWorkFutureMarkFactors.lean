import AppliedModelingLib.Foundations.Probability.PoissonSuspensionWorkMarks
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors
import Mathlib.Tactic

/-!
# Future service-mark factors of a stationary Poisson input

This module keeps the literal stationary arrival state fixed and splits its
independent two-sided service-mark path into the origin mark, the past marks,
and the strictly future IID mark stream.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open PoissonProcess

noncomputable section

/-- Retain the literal stationary arrival state, the origin service mark, and
the past service marks; expose only the strictly future marks as the IID
stream. -/
def stationaryPoissonWorkFutureMarkFactors
    (z : GoodSuspensionState × (ℤ → ℝ)) :
    ((GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) :=
  let q := twoSidedHeadPositiveNegative z.2
  (((z.1, q.1.1), q.2), q.1.2)

/-- Reconstruct the literal stationary marked path from its arrival state,
origin mark, past marks, and strictly future marks. -/
def stationaryPoissonWorkFromFutureMarkFactors :
    ((GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) →
      GoodSuspensionState × (ℤ → ℝ) :=
  fun x =>
    (x.1.1.1, fun k => match k with
      | 0 => x.1.1.2
      | Int.ofNat (n + 1) => x.2 n
      | Int.negSucc n => x.1.2 n)

/-- The factor map is Borel measurable. -/
theorem measurable_stationaryPoissonWorkFutureMarkFactors :
    Measurable stationaryPoissonWorkFutureMarkFactors := by
  have q : Measurable (fun z : GoodSuspensionState × (ℤ → ℝ) =>
      twoSidedHeadPositiveNegative z.2) :=
    measurable_twoSidedHeadPositiveNegative.comp
      (measurable_snd : Measurable (fun z : GoodSuspensionState × (ℤ → ℝ) => z.2))
  have hhead : Measurable (fun z : GoodSuspensionState × (ℤ → ℝ) =>
      (twoSidedHeadPositiveNegative z.2).1.1) :=
    measurable_fst.comp (measurable_fst.comp q)
  have hpast : Measurable (fun z : GoodSuspensionState × (ℤ → ℝ) =>
      (twoSidedHeadPositiveNegative z.2).2) := measurable_snd.comp q
  have hfuture : Measurable (fun z : GoodSuspensionState × (ℤ → ℝ) =>
      (twoSidedHeadPositiveNegative z.2).1.2) :=
    measurable_snd.comp (measurable_fst.comp q)
  exact ((measurable_fst.prodMk hhead).prodMk hpast).prodMk hfuture

/-- The reconstruction map is Borel measurable. -/
theorem measurable_stationaryPoissonWorkFromFutureMarkFactors :
    Measurable stationaryPoissonWorkFromFutureMarkFactors := by
  apply (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
  refine measurable_pi_iff.2 fun k => ?_
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          simpa [stationaryPoissonWorkFromFutureMarkFactors] using
            (measurable_snd.comp (measurable_fst.comp measurable_fst))
      | succ n =>
          simpa [stationaryPoissonWorkFromFutureMarkFactors] using
            ((measurable_pi_apply n).comp measurable_snd)
  | negSucc n =>
      simpa [stationaryPoissonWorkFromFutureMarkFactors] using
        ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst))

/-- Splitting then reconstructing a stationary marked path is pointwise the
identity. -/
theorem stationaryPoissonWorkFromFutureMarkFactors_apply_factors
    (z : GoodSuspensionState × (ℤ → ℝ)) :
    stationaryPoissonWorkFromFutureMarkFactors
      (stationaryPoissonWorkFutureMarkFactors z) = z := by
  rcases z with ⟨arrival, work⟩
  apply Prod.ext
  · rfl
  · funext k
    cases k with
    | ofNat n =>
        cases n with
        | zero => simp [stationaryPoissonWorkFutureMarkFactors,
            stationaryPoissonWorkFromFutureMarkFactors,
            twoSidedHeadPositiveNegative_apply]
        | succ n =>
            change work (Int.ofNat (n + 1)) = work (Int.ofNat (n + 1))
            rfl
    | negSucc n => simp [stationaryPoissonWorkFutureMarkFactors,
        stationaryPoissonWorkFromFutureMarkFactors,
        twoSidedHeadPositiveNegative_apply]

/-- Reconstructing then splitting the displayed factors is pointwise the
identity. -/
theorem stationaryPoissonWorkFutureMarkFactors_fromFactors_apply
    (x : ((GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) :
    stationaryPoissonWorkFutureMarkFactors
      (stationaryPoissonWorkFromFutureMarkFactors x) = x := by
  rcases x with ⟨⟨⟨arrival, head⟩, past⟩, future⟩
  simp [stationaryPoissonWorkFutureMarkFactors,
    stationaryPoissonWorkFromFutureMarkFactors, twoSidedHeadPositiveNegative_apply]

/-- The literal stationary marked-path factor is a measurable equivalence. -/
noncomputable def stationaryPoissonWorkFutureMarkEquiv :
    (GoodSuspensionState × (ℤ → ℝ)) ≃ᵐ
      ((GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) where
  toFun := stationaryPoissonWorkFutureMarkFactors
  invFun := stationaryPoissonWorkFromFutureMarkFactors
  left_inv := stationaryPoissonWorkFromFutureMarkFactors_apply_factors
  right_inv := stationaryPoissonWorkFutureMarkFactors_fromFactors_apply
  measurable_toFun := measurable_stationaryPoissonWorkFutureMarkFactors
  measurable_invFun := measurable_stationaryPoissonWorkFromFutureMarkFactors

/-- The literal stationary marked input factors into its arrival/origin/past
state and an independent IID future service-mark stream. -/
theorem map_stationaryPoissonWorkFutureMarkFactors
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map stationaryPoissonWorkFutureMarkFactors
      (stationaryPoissonWorkMeasure rate) =
      (((goodSuspensionMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ)) := by
  let A : Measure GoodSuspensionState := goodSuspensionMeasure rate
  let H : Measure ℝ := expMeasure (1 : ℝ)
  let F : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  let P : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure A := isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : IsProbabilityMeasure H := isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure F :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure P :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let split : GoodSuspensionState × (ℤ → ℝ) →
      GoodSuspensionState × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
    Prod.map id twoSidedHeadPositiveNegative
  let reorder : GoodSuspensionState × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) →
      ((GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    fun y => (((y.1, y.2.1.1), y.2.2), y.2.1.2)
  have hsplit : Measure.map split (A.prod (twoSidedInterarrivalMeasure (1 : ℝ))) =
      A.prod ((H.prod F).prod P) := by
    rw [← Measure.map_prod_map A (twoSidedInterarrivalMeasure (1 : ℝ))
      measurable_id measurable_twoSidedHeadPositiveNegative, Measure.map_id,
      map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure (by norm_num)]
  have hreorder : MeasurePreserving reorder (A.prod ((H.prod F).prod P))
      (((A.prod H).prod P).prod F) := by
    let h₁ := (measurePreserving_prodAssoc A (H.prod F) P).symm
    let h₂ := ((measurePreserving_prodAssoc A H F).symm).prod
      (MeasurePreserving.id P)
    let h₃ := measurePreserving_prodAssoc (A.prod H) F P
    let h₄ := (MeasurePreserving.id (A.prod H)).prod
      (Measure.measurePreserving_swap (μ := F) (ν := P))
    let h₅ := (measurePreserving_prodAssoc (A.prod H) P F).symm
    convert h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))) using 1
  change Measure.map (reorder ∘ split)
    (A.prod (twoSidedInterarrivalMeasure (1 : ℝ))) = ((A.prod H).prod P).prod F
  calc
    Measure.map (reorder ∘ split) (A.prod (twoSidedInterarrivalMeasure (1 : ℝ))) =
        Measure.map reorder
          (Measure.map split (A.prod (twoSidedInterarrivalMeasure (1 : ℝ)))) := by
          symm
          rw [Measure.map_map hreorder.measurable
            (measurable_id.prodMap measurable_twoSidedHeadPositiveNegative)]
    _ = Measure.map reorder (A.prod ((H.prod F).prod P)) := by rw [hsplit]
    _ = ((A.prod H).prod P).prod F := hreorder.map_eq
    _ =
        (((goodSuspensionMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ)) := by rfl

/-- The stationary future-mark factor map is measure preserving. -/
theorem stationaryPoissonWorkFutureMarkFactors_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving stationaryPoissonWorkFutureMarkFactors
      (stationaryPoissonWorkMeasure rate)
      ((((goodSuspensionMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  exact ⟨measurable_stationaryPoissonWorkFutureMarkFactors,
    map_stationaryPoissonWorkFutureMarkFactors hrate⟩

end

end AppliedModelingLib.Probability.Queueing

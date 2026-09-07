import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteHeadTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalHeadTail
import Mathlib.Tactic

/-!
# Literal two-stream head-tail factors

This module factors two independent one-sided exponential paths together with
an independent initial state.  It exposes the nearest coordinate of each
path and the complete strictly older tails.  The order of every coordinate is
recorded explicitly, so recurrence arguments cannot silently replace a
shifted source path with a fresh independent input.

No queueing or stationary-law conclusion is made here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Reassembling a displayed first exponential gap with its literal tail is
measurable. -/
theorem measurable_prependInterarrival :
    Measurable (fun p : ℝ × (ℕ → ℝ) => prependInterarrival p.1 p.2) := by
  simpa [prependInterarrival] using headTailEquiv.symm.measurable

/-- Splitting a path into its first gap and tail and then reassembling it
recovers the literal path. -/
theorem prependInterarrival_headTail (ξ : ℕ → ℝ) :
    prependInterarrival (headTail ξ).1 (headTail ξ).2 = ξ := by
  funext n
  cases n <;> rfl

/-- An exponential first gap independently paired with an exponential
interarrival tail reassembles to the original exponential path law. -/
theorem map_prependInterarrival_expMeasure_prod
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map (fun p : ℝ × (ℕ → ℝ) => prependInterarrival p.1 p.2)
      ((expMeasure rate).prod (exponentialInterarrivalMeasure rate)) =
      exponentialInterarrivalMeasure rate := by
  rw [← map_headTail_exponentialInterarrivalMeasure hrate,
    Measure.map_map measurable_prependInterarrival measurable_headTail]
  have hcomp : (fun p : ℝ × (ℕ → ℝ) => prependInterarrival p.1 p.2) ∘ headTail = id := by
    funext ξ
    simpa only [Function.comp_apply, id_eq] using prependInterarrival_headTail ξ
  rw [hcomp, Measure.map_id]

/-- Split two literal one-sided paths at their nearest coordinates while
retaining an arbitrary independent initial state with the strictly older
tails. -/
def initialTwoStreamHeadTailFactors {Ω : Type*}
    (x : Ω × ((Nat → Real) × (Nat → Real))) :
    (Ω × ((Nat → Real) × (Nat → Real))) × (Real × Real) :=
  ((x.1, (fun n => x.2.1 (n + 1), fun n => x.2.2 (n + 1))),
    (x.2.1 0, x.2.2 0))

/-- The two-stream literal factorization is measurable. -/
theorem measurable_initialTwoStreamHeadTailFactors {Ω : Type*}
    [MeasurableSpace Ω] :
    Measurable (initialTwoStreamHeadTailFactors (Ω := Ω)) := by
  unfold initialTwoStreamHeadTailFactors
  exact
    ((measurable_fst.prodMk
      ((measurable_pi_iff.2 fun n =>
        measurable_pi_apply (n + 1) |>.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_pi_iff.2 fun n =>
          measurable_pi_apply (n + 1) |>.comp (measurable_snd.comp measurable_snd)))).prodMk
      (((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))

/-- The raw product reordering after independently splitting both one-sided
paths. -/
private def initialTwoStreamHeadTailRearrange {Ω : Type*}
    (x : Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real)))) :
    (Ω × ((Nat → Real) × (Nat → Real))) × (Real × Real) :=
  ((x.1, (x.2.1.2, x.2.2.2)), (x.2.1.1, x.2.2.1))

private theorem measurable_initialTwoStreamHeadTailRearrange {Ω : Type*}
    [MeasurableSpace Ω] :
    Measurable (initialTwoStreamHeadTailRearrange (Ω := Ω)) := by
  unfold initialTwoStreamHeadTailRearrange
  exact
    ((measurable_fst.prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
      ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))

private theorem initialTwoStreamHeadTailFactors_eq_rearrange {Ω : Type*}
    (x : Ω × ((Nat → Real) × (Nat → Real))) :
    initialTwoStreamHeadTailFactors x =
      initialTwoStreamHeadTailRearrange
        (Prod.map id (Prod.map headTail headTail) x) := by
  rfl

private def prodRotateMiddleRight {α β γ : Type*}
    (x : α × (β × γ)) : (α × γ) × β :=
  ((x.1, x.2.2), x.2.1)

private theorem measurable_prodRotateMiddleRight {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (prodRotateMiddleRight (α := α) (β := β) (γ := γ)) := by
  unfold prodRotateMiddleRight
  exact ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))

private theorem map_prodRotateMiddleRight
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (prodRotateMiddleRight (α := α) (β := β) (γ := γ))
      (μ.prod (ν.prod ξ)) = (μ.prod ξ).prod ν := by
  have hassocSymm :
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (β × γ) → (α × β) × γ)
        (μ.prod (ν.prod ξ)) = (μ.prod ν).prod ξ := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm : α × (β × γ) → (α × β) × γ) ∘
          (MeasurableEquiv.prodAssoc : (α × β) × γ → α × (β × γ)) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (prodRotateMiddleRight (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
      Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          (Measure.map (Prod.map Prod.swap id)
            (Measure.map (MeasurableEquiv.prodAssoc.symm : α × (β × γ) → (α × β) × γ)
              (μ.prod (ν.prod ξ))))) := by
        symm
        rw [Measure.map_map (measurable_swap.prodMap measurable_id)
            MeasurableEquiv.prodAssoc.symm.measurable,
          Measure.map_map MeasurableEquiv.prodAssoc.measurable
            ((measurable_swap.prodMap measurable_id).comp
              MeasurableEquiv.prodAssoc.symm.measurable),
          Measure.map_map measurable_swap
            (MeasurableEquiv.prodAssoc.measurable.comp
              ((measurable_swap.prodMap measurable_id).comp
                MeasurableEquiv.prodAssoc.symm.measurable))]
        rfl
    _ = Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          (Measure.map (Prod.map Prod.swap id) ((μ.prod ν).prod ξ))) := by
        rw [hassocSymm]
    _ = Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          ((ν.prod μ).prod ξ)) := by
        rw [← Measure.map_prod_map _ _ measurable_swap measurable_id,
          Measure.prod_swap, Measure.map_id]
    _ = Measure.map Prod.swap (ν.prod (μ.prod ξ)) := by
        rw [Measure.prodAssoc_prod]
    _ = (μ.prod ξ).prod ν := by
        rw [Measure.prod_swap]

private def prodRotateMiddleLeft {α β γ : Type*}
    (x : α × (β × γ)) : β × (α × γ) :=
  (x.2.1, (x.1, x.2.2))

private theorem measurable_prodRotateMiddleLeft {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (prodRotateMiddleLeft (α := α) (β := β) (γ := γ)) := by
  unfold prodRotateMiddleLeft
  exact (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

private theorem map_prodRotateMiddleLeft
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (prodRotateMiddleLeft (α := α) (β := β) (γ := γ))
      (μ.prod (ν.prod ξ)) = ν.prod (μ.prod ξ) := by
  calc
    Measure.map (prodRotateMiddleLeft (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
      Measure.map Prod.swap
        (Measure.map (prodRotateMiddleRight (α := α) (β := β) (γ := γ))
          (μ.prod (ν.prod ξ))) := by
        symm
        rw [Measure.map_map measurable_swap measurable_prodRotateMiddleRight]
        rfl
    _ = Measure.map Prod.swap ((μ.prod ξ).prod ν) := by
        rw [map_prodRotateMiddleRight]
    _ = ν.prod (μ.prod ξ) := by
        rw [Measure.prod_swap]

private def prodMiddleSwap {α β γ δ : Type*}
    (x : (α × β) × (γ × δ)) : (α × γ) × (β × δ) :=
  ((x.1.1, x.2.1), (x.1.2, x.2.2))

private theorem measurable_prodMiddleSwap {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (prodMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ)) := by
  unfold prodMiddleSwap
  exact
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))

private theorem map_prodMiddleSwap
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ) (ζ : Measure δ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ξ] [IsProbabilityMeasure ζ] :
    Measure.map (prodMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ))
      ((μ.prod ν).prod (ξ.prod ζ)) = (μ.prod ξ).prod (ν.prod ζ) := by
  have hleft :
      Measure.map (MeasurableEquiv.prodAssoc : (α × β) × (γ × δ) →
        α × (β × (γ × δ))) ((μ.prod ν).prod (ξ.prod ζ)) =
        μ.prod (ν.prod (ξ.prod ζ)) := by
    exact Measure.prodAssoc_prod
  have hmiddle :
      Measure.map (Prod.map id (prodRotateMiddleLeft (α := β) (β := γ) (γ := δ)))
        (μ.prod (ν.prod (ξ.prod ζ))) = μ.prod (ξ.prod (ν.prod ζ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_prodRotateMiddleLeft,
      Measure.map_id, map_prodRotateMiddleLeft]
  have hright :
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ)) (μ.prod (ξ.prod (ν.prod ζ))) =
        (μ.prod ξ).prod (ν.prod ζ) := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
          (α × γ) × (β × δ)) ∘
          (MeasurableEquiv.prodAssoc : (α × γ) × (β × δ) →
            α × (γ × (β × δ))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (prodMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ))
        ((μ.prod ν).prod (ξ.prod ζ)) =
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ))
        (Measure.map (Prod.map id (prodRotateMiddleLeft (α := β) (β := γ) (γ := δ)))
          (Measure.map (MeasurableEquiv.prodAssoc : (α × β) × (γ × δ) →
            α × (β × (γ × δ))) ((μ.prod ν).prod (ξ.prod ζ)))) := by
        symm
        rw [Measure.map_map (measurable_id.prodMap measurable_prodRotateMiddleLeft)
          MeasurableEquiv.prodAssoc.measurable,
          Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            ((measurable_id.prodMap measurable_prodRotateMiddleLeft).comp
              MeasurableEquiv.prodAssoc.measurable)]
        rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ))
        (Measure.map (Prod.map id (prodRotateMiddleLeft (α := β) (β := γ) (γ := δ)))
          (μ.prod (ν.prod (ξ.prod ζ)))) := by rw [hleft]
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ)) (μ.prod (ξ.prod (ν.prod ζ))) := by rw [hmiddle]
    _ = (μ.prod ξ).prod (ν.prod ζ) := hright

private theorem map_initialTwoStreamHeadTailRearrange
    {Ω : Type*} [MeasurableSpace Ω]
    (initialLaw : Measure Ω) [IsProbabilityMeasure initialLaw]
    {leftRate rightRate : Real} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (initialTwoStreamHeadTailRearrange (Ω := Ω))
      (initialLaw.prod
        (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
          ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)))) =
      (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((expMeasure leftRate).prod (expMeasure rightRate)) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hright
  have houter :
      Measure.map
        (MeasurableEquiv.prodAssoc.symm :
          Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real))) →
            (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real)))
        (initialLaw.prod
          (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
            ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)))) =
        (initialLaw.prod ((expMeasure leftRate).prod
          (exponentialInterarrivalMeasure leftRate))).prod
          ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)) := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm :
          Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real))) →
            (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real))) ∘
          (MeasurableEquiv.prodAssoc :
            (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real)) →
              Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real)))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  have hrotate :
      Measure.map
        (Prod.map
          (prodRotateMiddleRight (α := Ω) (β := Real) (γ := Nat → Real))
          Prod.swap)
        ((initialLaw.prod ((expMeasure leftRate).prod
          (exponentialInterarrivalMeasure leftRate))).prod
          ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate))) =
        ((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (expMeasure leftRate)).prod
          ((exponentialInterarrivalMeasure rightRate).prod (expMeasure rightRate)) := by
    rw [← Measure.map_prod_map _ _ measurable_prodRotateMiddleRight measurable_swap,
      map_prodRotateMiddleRight, Measure.prod_swap]
  have hmiddle :
      Measure.map
        (prodMiddleSwap
          (α := Ω × (Nat → Real)) (β := Real)
          (γ := Nat → Real) (δ := Real))
        (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (expMeasure leftRate)).prod
          ((exponentialInterarrivalMeasure rightRate).prod (expMeasure rightRate))) =
        ((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate)).prod
          ((expMeasure leftRate).prod (expMeasure rightRate)) := by
    exact map_prodMiddleSwap
      (initialLaw.prod (exponentialInterarrivalMeasure leftRate))
      (expMeasure leftRate) (exponentialInterarrivalMeasure rightRate)
      (expMeasure rightRate)
  have hfinal :
      Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate)).prod
          ((expMeasure leftRate).prod (expMeasure rightRate))) =
        (initialLaw.prod
          ((exponentialInterarrivalMeasure leftRate).prod
            (exponentialInterarrivalMeasure rightRate))).prod
          ((expMeasure leftRate).prod (expMeasure rightRate)) := by
    rw [← Measure.map_prod_map _ _ MeasurableEquiv.prodAssoc.measurable measurable_id,
      Measure.prodAssoc_prod, Measure.map_id]
  calc
    Measure.map (initialTwoStreamHeadTailRearrange (Ω := Ω))
        (initialLaw.prod
          (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
            ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)))) =
      Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (Measure.map
          (prodMiddleSwap
            (α := Ω × (Nat → Real)) (β := Real)
            (γ := Nat → Real) (δ := Real))
          (Measure.map
            (Prod.map
              (prodRotateMiddleRight (α := Ω) (β := Real) (γ := Nat → Real))
              Prod.swap)
            (Measure.map
              (MeasurableEquiv.prodAssoc.symm :
                Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real))) →
                  (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real)))
              (initialLaw.prod
                (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
                  ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate))))))) := by
        rw [Measure.map_map
          (measurable_prodRotateMiddleRight.prodMap measurable_swap)
          MeasurableEquiv.prodAssoc.symm.measurable,
          Measure.map_map
            (measurable_prodMiddleSwap (α := Ω × (Nat → Real)) (β := Real)
              (γ := Nat → Real) (δ := Real))
            ((measurable_prodRotateMiddleRight.prodMap measurable_swap).comp
              MeasurableEquiv.prodAssoc.symm.measurable),
          Measure.map_map
            ((MeasurableEquiv.prodAssoc.measurable.prodMap measurable_id))
            ((measurable_prodMiddleSwap (α := Ω × (Nat → Real)) (β := Real)
              (γ := Nat → Real) (δ := Real)).comp
              ((measurable_prodRotateMiddleRight.prodMap measurable_swap).comp
                MeasurableEquiv.prodAssoc.symm.measurable))]
        rfl
    _ = Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (Measure.map
          (prodMiddleSwap
            (α := Ω × (Nat → Real)) (β := Real)
            (γ := Nat → Real) (δ := Real))
          (Measure.map
            (Prod.map
              (prodRotateMiddleRight (α := Ω) (β := Real) (γ := Nat → Real))
              Prod.swap)
            ((initialLaw.prod ((expMeasure leftRate).prod
              (exponentialInterarrivalMeasure leftRate))).prod
              ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate))))) := by
        rw [houter]
    _ = Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (Measure.map
          (prodMiddleSwap
            (α := Ω × (Nat → Real)) (β := Real)
            (γ := Nat → Real) (δ := Real))
          (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
            (expMeasure leftRate)).prod
            ((exponentialInterarrivalMeasure rightRate).prod (expMeasure rightRate)))) := by
        rw [hrotate]
    _ = Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate)).prod
          ((expMeasure leftRate).prod (expMeasure rightRate))) := by
        rw [hmiddle]
    _ = (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((expMeasure leftRate).prod (expMeasure rightRate)) := hfinal

/-- An arbitrary independent initial state, the two strictly older source
tails, and the two nearest innovations have the corresponding exact product
law.  The coordinates are not replaced by shifted copies of the source.
-/
theorem map_initialTwoStreamHeadTailFactors
    {Ω : Type*} [MeasurableSpace Ω]
    (initialLaw : Measure Ω) [IsProbabilityMeasure initialLaw]
    {leftRate rightRate : Real} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (initialTwoStreamHeadTailFactors (Ω := Ω))
      (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))) =
      (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((expMeasure leftRate).prod (expMeasure rightRate)) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hright
  rw [show initialTwoStreamHeadTailFactors (Ω := Ω) =
      initialTwoStreamHeadTailRearrange (Ω := Ω) ∘
        Prod.map id (Prod.map headTail headTail) by
    funext x
    exact initialTwoStreamHeadTailFactors_eq_rearrange x]
  rw [← Measure.map_map measurable_initialTwoStreamHeadTailRearrange
    (measurable_id.prodMap (measurable_headTail.prodMap measurable_headTail))]
  rw [← Measure.map_prod_map _ _ measurable_id
    (measurable_headTail.prodMap measurable_headTail), Measure.map_id,
    ← Measure.map_prod_map _ _ measurable_headTail measurable_headTail,
    map_headTail_exponentialInterarrivalMeasure hleft,
    map_headTail_exponentialInterarrivalMeasure hright]
  exact map_initialTwoStreamHeadTailRearrange initialLaw hleft hright

/- The elementary three-factor rearrangement needed when a first head is
removed from the left stream while a companion stream is retained literally. -/
private def leftHeadTailWithCompanionRearrange {α β γ : Type*}
    (x : (α × β) × γ) : (β × γ) × α :=
  ((x.1.2, x.2), x.1.1)

private theorem measurable_leftHeadTailWithCompanionRearrange {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (leftHeadTailWithCompanionRearrange (α := α) (β := β) (γ := γ)) := by
  exact ((measurable_snd.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_fst.comp measurable_fst)

private theorem map_leftHeadTailWithCompanionRearrange
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (leftHeadTailWithCompanionRearrange (α := α) (β := β) (γ := γ))
      ((μ.prod ν).prod ξ) = (ν.prod ξ).prod μ := by
  have hassocSymm :
      Measure.map (MeasurableEquiv.prodAssoc.symm : β × (γ × α) -> (β × γ) × α)
        (ν.prod (ξ.prod μ)) = (ν.prod ξ).prod μ := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm : β × (γ × α) -> (β × γ) × α) ∘
          (MeasurableEquiv.prodAssoc : (β × γ) × α -> β × (γ × α)) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (leftHeadTailWithCompanionRearrange (α := α) (β := β) (γ := γ))
        ((μ.prod ν).prod ξ) =
      Measure.map (MeasurableEquiv.prodAssoc.symm : β × (γ × α) -> (β × γ) × α)
        (Measure.map (Prod.map id Prod.swap)
          (Measure.map (prodRotateMiddleLeft (α := α) (β := β) (γ := γ))
            (Measure.map (MeasurableEquiv.prodAssoc : (α × β) × γ -> α × (β × γ))
              ((μ.prod ν).prod ξ)))) := by
        symm
        rw [Measure.map_map measurable_prodRotateMiddleLeft
            MeasurableEquiv.prodAssoc.measurable,
          Measure.map_map (measurable_id.prodMap measurable_swap)
            (measurable_prodRotateMiddleLeft.comp MeasurableEquiv.prodAssoc.measurable),
          Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            ((measurable_id.prodMap measurable_swap).comp
              (measurable_prodRotateMiddleLeft.comp MeasurableEquiv.prodAssoc.measurable))]
        rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : β × (γ × α) -> (β × γ) × α)
        (Measure.map (Prod.map id Prod.swap)
          (Measure.map (prodRotateMiddleLeft (α := α) (β := β) (γ := γ))
            (μ.prod (ν.prod ξ)))) := by
          rw [Measure.prodAssoc_prod]
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : β × (γ × α) -> (β × γ) × α)
        (Measure.map (Prod.map id Prod.swap) (ν.prod (μ.prod ξ))) := by
          rw [map_prodRotateMiddleLeft]
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : β × (γ × α) -> (β × γ) × α)
        (ν.prod (ξ.prod μ)) := by
          rw [← Measure.map_prod_map _ _ measurable_id measurable_swap,
            Measure.map_id, Measure.prod_swap]
    _ = (ν.prod ξ).prod μ := hassocSymm

/-- Remove the literal first head from the currently active stream, retaining
the inactive stream exactly as supplied.  The output is the state-indexed
unconsumed stream pair together with that consumed active head. -/
def twoStreamAfterActiveHead
    (initial : Fin 2) (x : (Nat -> Real) × (Nat -> Real)) :
    ((Nat -> Real) × (Nat -> Real)) × Real :=
  if initial = 0 then
    ((fun n => x.1 (n + 1), x.2), x.1 0)
  else ((x.1, fun n => x.2 (n + 1)), x.2 0)

theorem measurable_twoStreamAfterActiveHead (initial : Fin 2) :
    Measurable (twoStreamAfterActiveHead initial) := by
  fin_cases initial
  · exact
      ((measurable_pi_iff.2 fun n =>
        measurable_pi_apply (n + 1) |>.comp measurable_fst).prodMk measurable_snd).prodMk
        ((measurable_pi_apply 0).comp measurable_fst)
  · exact
      (measurable_fst.prodMk
        (measurable_pi_iff.2 fun n =>
          measurable_pi_apply (n + 1) |>.comp measurable_snd)).prodMk
        ((measurable_pi_apply 0).comp measurable_snd)

/-- The literal active-stream tail and untouched inactive stream retain their
two-stream product law, independently of the first active holding time. -/
theorem map_twoStreamAfterActiveHead
    (initial : Fin 2) {leftRate rightRate : Real}
    (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (twoStreamAfterActiveHead initial)
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) =
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)).prod
        (if initial = 0 then expMeasure leftRate else expMeasure rightRate) := by
  let leftTail := exponentialInterarrivalMeasure leftRate
  let rightTail := exponentialInterarrivalMeasure rightRate
  let leftHead := expMeasure leftRate
  let rightHead := expMeasure rightRate
  letI : IsProbabilityMeasure leftTail := by
    dsimp [leftTail]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightTail := by
    dsimp [rightTail]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure leftHead := by
    dsimp [leftHead]
    exact isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure rightHead := by
    dsimp [rightHead]
    exact isProbabilityMeasure_expMeasure hright
  fin_cases initial
  · change Measure.map (fun x : (Nat -> Real) × (Nat -> Real) =>
        ((fun n => x.1 (n + 1), x.2), x.1 0)) (leftTail.prod rightTail) =
        (leftTail.prod rightTail).prod leftHead
    calc
      Measure.map (fun x : (Nat -> Real) × (Nat -> Real) =>
          ((fun n => x.1 (n + 1), x.2), x.1 0)) (leftTail.prod rightTail) =
        Measure.map leftHeadTailWithCompanionRearrange
          (Measure.map (Prod.map headTail id) (leftTail.prod rightTail)) := by
            symm
            rw [Measure.map_map measurable_leftHeadTailWithCompanionRearrange
              (measurable_headTail.prodMap measurable_id)]
            rfl
      _ = Measure.map leftHeadTailWithCompanionRearrange
          ((leftHead.prod leftTail).prod rightTail) := by
            rw [← Measure.map_prod_map _ _ measurable_headTail measurable_id,
              map_headTail_exponentialInterarrivalMeasure hleft, Measure.map_id]
      _ = (leftTail.prod rightTail).prod leftHead := by
            exact map_leftHeadTailWithCompanionRearrange leftHead leftTail rightTail
  · change Measure.map (fun x : (Nat -> Real) × (Nat -> Real) =>
        ((x.1, fun n => x.2 (n + 1)), x.2 0)) (leftTail.prod rightTail) =
        (leftTail.prod rightTail).prod rightHead
    calc
      Measure.map (fun x : (Nat -> Real) × (Nat -> Real) =>
          ((x.1, fun n => x.2 (n + 1)), x.2 0)) (leftTail.prod rightTail) =
        Measure.map (prodRotateMiddleRight (α := Nat -> Real) (β := Real)
          (γ := Nat -> Real))
          (Measure.map (Prod.map id headTail) (leftTail.prod rightTail)) := by
            symm
            rw [Measure.map_map measurable_prodRotateMiddleRight
              (measurable_id.prodMap measurable_headTail)]
            rfl
      _ = Measure.map (prodRotateMiddleRight (α := Nat -> Real) (β := Real)
          (γ := Nat -> Real)) (leftTail.prod (rightHead.prod rightTail)) := by
            rw [← Measure.map_prod_map _ _ measurable_id measurable_headTail,
              Measure.map_id, map_headTail_exponentialInterarrivalMeasure hright]
      _ = (leftTail.prod rightTail).prod rightHead := by
            exact map_prodRotateMiddleRight leftTail rightHead rightTail

/-- Reattach a displayed active first gap to the active tail while retaining
the inactive stream literally.  This is the inverse coordinate operation to
`twoStreamAfterActiveHead`. -/
def twoStreamPrependActiveHead
    (initial : Fin 2) (x : ((Nat -> Real) × (Nat -> Real)) × Real) :
    (Nat -> Real) × (Nat -> Real) :=
  if initial = 0 then
    (prependInterarrival x.2 x.1.1, x.1.2)
  else
    (x.1.1, prependInterarrival x.2 x.1.2)

theorem measurable_twoStreamPrependActiveHead (initial : Fin 2) :
    Measurable (twoStreamPrependActiveHead initial) := by
  fin_cases initial
  · exact
      ((measurable_prependInterarrival.comp
        ((measurable_snd.prodMk (measurable_fst.comp measurable_fst)))).prodMk
        (measurable_snd.comp measurable_fst))
  · exact
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_prependInterarrival.comp
          ((measurable_snd.prodMk (measurable_snd.comp measurable_fst))))

/-- Splitting off the active first gap and reattaching it is pointwise the
identity on the literal two-stream path. -/
theorem twoStreamPrependActiveHead_afterActiveHead
    (initial : Fin 2) (x : (Nat -> Real) × (Nat -> Real)) :
    twoStreamPrependActiveHead initial (twoStreamAfterActiveHead initial x) = x := by
  fin_cases initial
  · ext n <;> cases n <;> rfl
  · ext n <;> cases n <;> rfl

/-- An independent exponential active head and its two unconsumed literal
streams reassemble to the original two-stream exponential path law. -/
theorem map_twoStreamPrependActiveHead
    (initial : Fin 2) {leftRate rightRate : Real}
    (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (twoStreamPrependActiveHead initial)
      (((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)).prod
        (if initial = 0 then expMeasure leftRate else expMeasure rightRate)) =
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate) := by
  rw [← map_twoStreamAfterActiveHead initial hleft hright,
    Measure.map_map (measurable_twoStreamPrependActiveHead initial)
      (measurable_twoStreamAfterActiveHead initial)]
  have hcomp : twoStreamPrependActiveHead initial ∘ twoStreamAfterActiveHead initial = id := by
    funext x
    simpa only [Function.comp_apply, id_eq] using
      twoStreamPrependActiveHead_afterActiveHead initial x
  rw [hcomp, Measure.map_id]

/-- The same reattachment operation when the active exponential head is
listed before the two literal tails. -/
def twoStreamPrependActiveHeadFromHeadTail
    (initial : Fin 2) (x : Real × ((Nat -> Real) × (Nat -> Real))) :
    (Nat -> Real) × (Nat -> Real) :=
  twoStreamPrependActiveHead initial (x.2, x.1)

theorem measurable_twoStreamPrependActiveHeadFromHeadTail (initial : Fin 2) :
    Measurable (twoStreamPrependActiveHeadFromHeadTail initial) := by
  exact (measurable_twoStreamPrependActiveHead initial).comp
    (measurable_snd.prodMk measurable_fst)

/-- Reassembling a head-first active residual and two literal tails recovers
the original two-stream exponential path law. -/
theorem map_twoStreamPrependActiveHeadFromHeadTail
    (initial : Fin 2) {leftRate rightRate : Real}
    (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (twoStreamPrependActiveHeadFromHeadTail initial)
      ((if initial = 0 then expMeasure leftRate else expMeasure rightRate).prod
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate))) =
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) := by infer_instance
  letI : IsProbabilityMeasure
      (if initial = 0 then expMeasure leftRate else expMeasure rightRate) := by
    split_ifs <;> infer_instance
  rw [show twoStreamPrependActiveHeadFromHeadTail initial =
      twoStreamPrependActiveHead initial ∘ Prod.swap by rfl,
    ← Measure.map_map (measurable_twoStreamPrependActiveHead initial) measurable_swap,
    Measure.prod_swap]
  exact map_twoStreamPrependActiveHead initial hleft hright

end

end AppliedModelingLib.Probability.PoissonProcess

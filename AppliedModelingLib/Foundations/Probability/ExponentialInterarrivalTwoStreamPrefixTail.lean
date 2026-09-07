import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalPostArrival

/-!
# Fixed-index factors of two independent exponential renewal streams

This module separates two independent exponential-interarrival paths at the
same deterministic coordinate.  It retains both consumed finite prefixes and
both unconsumed tails, in an order suited to a later alternating-renewal
argument.  The result is a deterministic-index product factorization; it does
not make a clock-time restart assertion.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The two finite prefixes and two complete tails obtained by splitting each
of two paths after exactly `n` consumed interarrivals. -/
def twoStreamPrefixTail (n : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      ((Fin n → ℝ) × (Fin n → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun paths =>
    ((prefixInterarrival n paths.1, prefixInterarrival n paths.2),
      (futureInterarrival n paths.1, futureInterarrival n paths.2))

/-- The fixed-index two-stream split is Borel measurable. -/
theorem measurable_twoStreamPrefixTail (n : ℕ) :
    Measurable (twoStreamPrefixTail n) := by
  exact
    (((measurable_prefixInterarrival n).comp measurable_fst).prodMk
      ((measurable_prefixInterarrival n).comp measurable_snd)).prodMk
      (((measurable_pi_iff.2 fun k => measurable_futureInterarrival n k).comp
        measurable_fst).prodMk
        ((measurable_pi_iff.2 fun k => measurable_futureInterarrival n k).comp
          measurable_snd))

private def prefixTailMiddleSwap {α β γ δ : Type*}
    (x : (α × β) × (γ × δ)) : (α × γ) × (β × δ) :=
  ((x.1.1, x.2.1), (x.1.2, x.2.2))

private theorem measurable_prefixTailMiddleSwap {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] :
    Measurable (prefixTailMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ)) := by
  exact
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))

private def prefixTailRotateMiddleLeft {α β γ : Type*}
    (x : α × (β × γ)) : β × (α × γ) :=
  (x.2.1, (x.1, x.2.2))

private theorem measurable_prefixTailRotateMiddleLeft {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (prefixTailRotateMiddleLeft (α := α) (β := β) (γ := γ)) := by
  exact (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

private def prefixTailRotateMiddleRight {α β γ : Type*}
    (x : α × (β × γ)) : (α × γ) × β :=
  ((x.1, x.2.2), x.2.1)

private theorem measurable_prefixTailRotateMiddleRight {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (prefixTailRotateMiddleRight (α := α) (β := β) (γ := γ)) := by
  exact ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))

private theorem map_prefixTailRotateMiddleRight
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (prefixTailRotateMiddleRight (α := α) (β := β) (γ := γ))
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
    Measure.map (prefixTailRotateMiddleRight (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
      Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          (Measure.map (Prod.map Prod.swap id)
            (Measure.map (MeasurableEquiv.prodAssoc.symm : α × (β × γ) →
              (α × β) × γ) (μ.prod (ν.prod ξ))))) := by
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

private theorem map_prefixTailRotateMiddleLeft
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (prefixTailRotateMiddleLeft (α := α) (β := β) (γ := γ))
      (μ.prod (ν.prod ξ)) = ν.prod (μ.prod ξ) := by
  calc
    Measure.map (prefixTailRotateMiddleLeft (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
      Measure.map Prod.swap
        (Measure.map (prefixTailRotateMiddleRight (α := α) (β := β) (γ := γ))
          (μ.prod (ν.prod ξ))) := by
            symm
            rw [Measure.map_map measurable_swap measurable_prefixTailRotateMiddleRight]
            rfl
    _ = Measure.map Prod.swap ((μ.prod ξ).prod ν) := by
      rw [map_prefixTailRotateMiddleRight]
    _ = ν.prod (μ.prod ξ) := by
      rw [Measure.prod_swap]

private theorem map_prefixTailMiddleSwap
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ) (ζ : Measure δ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ξ] [IsProbabilityMeasure ζ] :
    Measure.map (prefixTailMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ))
      ((μ.prod ν).prod (ξ.prod ζ)) = (μ.prod ξ).prod (ν.prod ζ) := by
  let leftAssoc : (α × β) × (γ × δ) → α × (β × (γ × δ)) :=
    MeasurableEquiv.prodAssoc
  let rotate : β × (γ × δ) → γ × (β × δ) := fun x => (x.2.1, (x.1, x.2.2))
  let rightAssoc : α × (γ × (β × δ)) → (α × γ) × (β × δ) :=
    MeasurableEquiv.prodAssoc.symm
  have hleftAssoc : Measurable leftAssoc := MeasurableEquiv.prodAssoc.measurable
  have hrotate : Measurable rotate := by
    exact (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hrightAssoc : Measurable rightAssoc := MeasurableEquiv.prodAssoc.symm.measurable
  have hleftLaw : Measure.map leftAssoc ((μ.prod ν).prod (ξ.prod ζ)) =
      μ.prod (ν.prod (ξ.prod ζ)) := by
    simpa [leftAssoc] using (Measure.prodAssoc_prod :
      Measure.map (MeasurableEquiv.prodAssoc : (α × β) × (γ × δ) →
        α × (β × (γ × δ))) ((μ.prod ν).prod (ξ.prod ζ)) =
        μ.prod (ν.prod (ξ.prod ζ)))
  have hrotateLaw : Measure.map rotate (ν.prod (ξ.prod ζ)) =
      ξ.prod (ν.prod ζ) := by
    simpa [rotate] using map_prefixTailRotateMiddleLeft ν ξ ζ
  have hrightLaw : Measure.map rightAssoc (μ.prod (ξ.prod (ν.prod ζ))) =
      (μ.prod ξ).prod (ν.prod ζ) := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp : (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ)) ∘
        (MeasurableEquiv.prodAssoc : (α × γ) × (β × δ) →
          α × (γ × (β × δ))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (prefixTailMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ))
        ((μ.prod ν).prod (ξ.prod ζ)) =
      Measure.map rightAssoc
        (Measure.map (Prod.map id rotate)
          (Measure.map leftAssoc ((μ.prod ν).prod (ξ.prod ζ)))) := by
            rw [Measure.map_map (measurable_id.prodMap hrotate) hleftAssoc,
              Measure.map_map hrightAssoc
                ((measurable_id.prodMap hrotate).comp hleftAssoc)]
            rfl
    _ = Measure.map rightAssoc
        (Measure.map (Prod.map id rotate) (μ.prod (ν.prod (ξ.prod ζ)))) := by
          rw [hleftLaw]
    _ = Measure.map rightAssoc (μ.prod (ξ.prod (ν.prod ζ))) := by
          rw [← Measure.map_prod_map _ _ measurable_id hrotate,
            Measure.map_id, hrotateLaw]
    _ = (μ.prod ξ).prod (ν.prod ζ) := hrightLaw

private theorem twoStreamPrefixTail_eq_middleSwap (n : ℕ) :
    twoStreamPrefixTail n =
      prefixTailMiddleSwap ∘
        Prod.map
          (fun path : ℕ → ℝ => (prefixInterarrival n path, futureInterarrival n path))
          (fun path : ℕ → ℝ => (prefixInterarrival n path, futureInterarrival n path)) := by
  funext paths
  rfl

/-- After any common deterministic coordinate, the two finite consumed
prefixes factor from the two complete unconsumed exponential tails. -/
theorem map_twoStreamPrefixTail
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (n : ℕ) :
    Measure.map (twoStreamPrefixTail n)
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) =
      ((Measure.map (prefixInterarrival n)
        (exponentialInterarrivalMeasure leftRate)).prod
        (Measure.map (prefixInterarrival n)
          (exponentialInterarrivalMeasure rightRate))).prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) := by
  let left : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let right : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let leftFactor : (ℕ → ℝ) → (Fin n → ℝ) × (ℕ → ℝ) :=
    fun path => (prefixInterarrival n path, futureInterarrival n path)
  let rightFactor : (ℕ → ℝ) → (Fin n → ℝ) × (ℕ → ℝ) :=
    fun path => (prefixInterarrival n path, futureInterarrival n path)
  letI : IsProbabilityMeasure left := by
    simpa [left] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure right := by
    simpa [right] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival n) left) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival n) right) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  have hleftFactor : Measurable leftFactor := by
    exact (measurable_prefixInterarrival n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hrightFactor : Measurable rightFactor := hleftFactor
  have hleftLaw : Measure.map leftFactor left =
      (Measure.map (prefixInterarrival n) left).prod left := by
    simpa [left, leftFactor] using
      (prefixInterarrival_futureInterarrival_hasLaw_prod hleft n).map_eq
  have hrightLaw : Measure.map rightFactor right =
      (Measure.map (prefixInterarrival n) right).prod right := by
    simpa [right, rightFactor] using
      (prefixInterarrival_futureInterarrival_hasLaw_prod hright n).map_eq
  rw [twoStreamPrefixTail_eq_middleSwap n]
  rw [← Measure.map_map measurable_prefixTailMiddleSwap
    (hleftFactor.prodMap hrightFactor),
    ← Measure.map_prod_map _ _ hleftFactor hrightFactor,
    hleftLaw, hrightLaw]
  exact map_prefixTailMiddleSwap
    (Measure.map (prefixInterarrival n) left) left
    (Measure.map (prefixInterarrival n) right) right

/-- Split two independent paths after possibly different deterministic
coordinates.  This is the literal factor needed when an alternating path has
completed one more visit in its inactive state than in its current active
state. -/
def twoStreamAsymmetricPrefixTail (leftCount rightCount : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      ((Fin leftCount → ℝ) × (Fin rightCount → ℝ)) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun paths =>
    ((prefixInterarrival leftCount paths.1,
      prefixInterarrival rightCount paths.2),
      (futureInterarrival leftCount paths.1,
        futureInterarrival rightCount paths.2))

/-- The two-stream split at two deterministic coordinates is Borel measurable. -/
theorem measurable_twoStreamAsymmetricPrefixTail
    (leftCount rightCount : ℕ) :
    Measurable (twoStreamAsymmetricPrefixTail leftCount rightCount) := by
  exact
    (((measurable_prefixInterarrival leftCount).comp measurable_fst).prodMk
      ((measurable_prefixInterarrival rightCount).comp measurable_snd)).prodMk
      (((measurable_pi_iff.2 fun k =>
        measurable_futureInterarrival leftCount k).comp measurable_fst).prodMk
        ((measurable_pi_iff.2 fun k =>
          measurable_futureInterarrival rightCount k).comp measurable_snd))

private theorem twoStreamAsymmetricPrefixTail_eq_middleSwap
    (leftCount rightCount : ℕ) :
    twoStreamAsymmetricPrefixTail leftCount rightCount =
      prefixTailMiddleSwap ∘
        Prod.map
          (fun path : ℕ → ℝ =>
            (prefixInterarrival leftCount path,
              futureInterarrival leftCount path))
          (fun path : ℕ → ℝ =>
            (prefixInterarrival rightCount path,
              futureInterarrival rightCount path)) := by
  funext paths
  rfl

/-- The two consumed deterministic prefixes factor from the two complete
unconsumed exponential tails even when their lengths differ. -/
theorem map_twoStreamAsymmetricPrefixTail
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (leftCount rightCount : ℕ) :
    Measure.map (twoStreamAsymmetricPrefixTail leftCount rightCount)
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) =
      ((Measure.map (prefixInterarrival leftCount)
        (exponentialInterarrivalMeasure leftRate)).prod
        (Measure.map (prefixInterarrival rightCount)
          (exponentialInterarrivalMeasure rightRate))).prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) := by
  let left : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let right : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let leftFactor : (ℕ → ℝ) → (Fin leftCount → ℝ) × (ℕ → ℝ) :=
    fun path => (prefixInterarrival leftCount path,
      futureInterarrival leftCount path)
  let rightFactor : (ℕ → ℝ) → (Fin rightCount → ℝ) × (ℕ → ℝ) :=
    fun path => (prefixInterarrival rightCount path,
      futureInterarrival rightCount path)
  letI : IsProbabilityMeasure left := by
    simpa [left] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure right := by
    simpa [right] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival leftCount) left) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival leftCount).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival rightCount) right) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival rightCount).aemeasurable
  have hleftFactor : Measurable leftFactor := by
    exact (measurable_prefixInterarrival leftCount).prodMk
      (measurable_pi_iff.2 fun k =>
        measurable_futureInterarrival leftCount k)
  have hrightFactor : Measurable rightFactor := by
    exact (measurable_prefixInterarrival rightCount).prodMk
      (measurable_pi_iff.2 fun k =>
        measurable_futureInterarrival rightCount k)
  have hleftLaw : Measure.map leftFactor left =
      (Measure.map (prefixInterarrival leftCount) left).prod left := by
    simpa [left, leftFactor] using
      (prefixInterarrival_futureInterarrival_hasLaw_prod hleft leftCount).map_eq
  have hrightLaw : Measure.map rightFactor right =
      (Measure.map (prefixInterarrival rightCount) right).prod right := by
    simpa [right, rightFactor] using
      (prefixInterarrival_futureInterarrival_hasLaw_prod hright rightCount).map_eq
  rw [twoStreamAsymmetricPrefixTail_eq_middleSwap leftCount rightCount]
  rw [← Measure.map_map measurable_prefixTailMiddleSwap
    (hleftFactor.prodMap hrightFactor),
    ← Measure.map_prod_map _ _ hleftFactor hrightFactor,
    hleftLaw, hrightLaw]
  exact map_prefixTailMiddleSwap
    (Measure.map (prefixInterarrival leftCount) left) left
    (Measure.map (prefixInterarrival rightCount) right) right

end

end AppliedModelingLib.Probability.PoissonProcess

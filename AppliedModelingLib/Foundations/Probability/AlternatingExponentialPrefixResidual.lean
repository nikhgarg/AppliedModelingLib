import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTwoStreamPrefixTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTwoStreamExternalTimeResidualTail
import AppliedModelingLib.Foundations.Probability.AlternatingTwoStateSwitching

/-!
# Fixed-prefix residual factors for alternating exponential holds

The two paths in this module are state-local holding-time streams: the first
path is active at the beginning of the displayed alternating block and the
second is inactive.  At an even alternating-count fiber, both paths have
contributed the same number of complete holds.  The factor below exposes those
two prefixes and the active stream's residual history, while leaving precisely
the residual active hold and the untouched inactive tail as the future pair.

This is a fixed-fiber product factor, not a simultaneous-calendar-clock
interpretation of the two state-local paths and not a strong-Markov axiom.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Split two state-local paths after `n` completed visits each, keeping the
first path's tail adjacent to the consumed prefixes and the second path's
tail as a companion. -/
def twoStreamPrefixActiveTailWithCompanion (n : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) :=
  fun paths =>
    (((prefixInterarrival n paths.1, prefixInterarrival n paths.2),
      futureInterarrival n paths.1), futureInterarrival n paths.2)

/-- The deterministic two-stream prefix/active-tail split is measurable. -/
theorem measurable_twoStreamPrefixActiveTailWithCompanion (n : ℕ) :
    Measurable (twoStreamPrefixActiveTailWithCompanion n) := by
  exact
    ((((measurable_prefixInterarrival n).comp measurable_fst).prodMk
      ((measurable_prefixInterarrival n).comp measurable_snd)).prodMk
      ((measurable_pi_iff.2 fun k => measurable_futureInterarrival n k).comp
        measurable_fst)).prodMk
      ((measurable_pi_iff.2 fun k => measurable_futureInterarrival n k).comp
        measurable_snd)

private theorem twoStreamPrefixActiveTailWithCompanion_eq_assoc
    (n : ℕ) :
    twoStreamPrefixActiveTailWithCompanion n =
      (MeasurableEquiv.prodAssoc.symm :
        ((Fin n → ℝ) × (Fin n → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) →
          (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ)) ∘
        twoStreamPrefixTail n := by
  rfl

/-- The two state-local prefixes factor from their respective complete tails,
with the active tail positioned for a subsequent external-time residual
factorization. -/
theorem map_twoStreamPrefixActiveTailWithCompanion
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate) (n : ℕ) :
    Measure.map (twoStreamPrefixActiveTailWithCompanion n)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) =
      ((((Measure.map (prefixInterarrival n)
        (exponentialInterarrivalMeasure activeRate)).prod
          (Measure.map (prefixInterarrival n)
            (exponentialInterarrivalMeasure inactiveRate))).prod
          (exponentialInterarrivalMeasure activeRate)).prod
        (exponentialInterarrivalMeasure inactiveRate)) := by
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.map (prefixInterarrival n)
      (exponentialInterarrivalMeasure activeRate)).prod
      (Measure.map (prefixInterarrival n)
        (exponentialInterarrivalMeasure inactiveRate))
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) activeLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) inactiveLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  rw [twoStreamPrefixActiveTailWithCompanion_eq_assoc n]
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_twoStreamPrefixTail n)]
  rw [map_twoStreamPrefixTail hactive hinactive n]
  have hfactor :
      Measure.map (MeasurableEquiv.prodAssoc.symm :
        ((Fin n → ℝ) × (Fin n → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) →
          (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ))
        (prefixLaw.prod (activeLaw.prod inactiveLaw)) =
      (prefixLaw.prod activeLaw).prod inactiveLaw := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm :
          ((Fin n → ℝ) × (Fin n → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) →
            (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ)) ∘
          (MeasurableEquiv.prodAssoc :
            (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) →
              ((Fin n → ℝ) × (Fin n → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  simpa [prefixLaw, activeLaw, inactiveLaw] using hfactor

/-- The nonnegative calendar remainder after the two consumed state-local
prefixes.  The clamp makes this a total measurable external clock; on the
corresponding even-count fiber its value is the literal elapsed active hold. -/
def alternatingEvenPrefixElapsed (t : ℝ) (n : ℕ) :
    (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
  fun prefixes => max 0
    (t - ((∑ i, prefixes.1 i) + ∑ i, prefixes.2 i))

/-- The fixed-prefix alternating elapsed clock is Borel measurable. -/
theorem measurable_alternatingEvenPrefixElapsed (t : ℝ) (n : ℕ) :
    Measurable (alternatingEvenPrefixElapsed t n) := by
  unfold alternatingEvenPrefixElapsed
  have hleft : Measurable (fun prefixes : (Fin n → ℝ) × (Fin n → ℝ) =>
      ∑ i, prefixes.1 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp measurable_fst
  have hright : Measurable (fun prefixes : (Fin n → ℝ) × (Fin n → ℝ) =>
      ∑ i, prefixes.2 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp measurable_snd
  exact measurable_const.max (measurable_const.sub (hleft.add hright))

/-- On an even alternating-count fiber, expose both consumed state-local
prefixes and the active residual history.  The returned future pair consists
of the fresh residual active stream and the literally untouched inactive tail. -/
def alternatingEvenPrefixResidualFactor (t : ℝ) (n : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
  externalTimeLeftHistoryResidualCompanionFactor
    (alternatingEvenPrefixElapsed t n) ∘
      twoStreamPrefixActiveTailWithCompanion n

/-- Measurability of the even alternating-prefix residual factor. -/
theorem measurable_alternatingEvenPrefixResidualFactor (t : ℝ) (n : ℕ) :
    Measurable (alternatingEvenPrefixResidualFactor t n) := by
  exact (measurable_externalTimeLeftHistoryResidualCompanionFactor
    (alternatingEvenPrefixElapsed t n)
    (measurable_alternatingEvenPrefixElapsed t n)).comp
      (measurable_twoStreamPrefixActiveTailWithCompanion n)

/-- After exactly `n` completed visits to each state-local stream, the
consumed prefixes and active residual history factor from the pair made of a
fresh active residual stream and an untouched inactive stream.  This is the
probabilistic core of the even alternating-count fiber; the later fiber event
is a measurable restriction of its first coordinate. -/
theorem map_alternatingEvenPrefixResidualFactor
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (t : ℝ) (n : ℕ) :
    Measure.map (alternatingEvenPrefixResidualFactor t n)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) =
      (Measure.map (externalTimePastHistory (alternatingEvenPrefixElapsed t n))
        (((Measure.map (prefixInterarrival n)
          (exponentialInterarrivalMeasure activeRate)).prod
            (Measure.map (prefixInterarrival n)
              (exponentialInterarrivalMeasure inactiveRate))).prod
          (exponentialInterarrivalMeasure activeRate))).prod
        ((exponentialInterarrivalMeasure activeRate).prod
          (exponentialInterarrivalMeasure inactiveRate)) := by
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.map (prefixInterarrival n)
      (exponentialInterarrivalMeasure activeRate)).prod
      (Measure.map (prefixInterarrival n)
        (exponentialInterarrivalMeasure inactiveRate))
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let elapsed : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    alternatingEvenPrefixElapsed t n
  let split : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    twoStreamPrefixActiveTailWithCompanion n
  let factor : (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
    externalTimeLeftHistoryResidualCompanionFactor elapsed
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) activeLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) inactiveLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  have hsplit : Measure.map split (activeLaw.prod inactiveLaw) =
      (prefixLaw.prod activeLaw).prod inactiveLaw := by
    simpa [split, prefixLaw, activeLaw, inactiveLaw] using
      map_twoStreamPrefixActiveTailWithCompanion hactive hinactive n
  have hfactor : Measure.map factor ((prefixLaw.prod activeLaw).prod inactiveLaw) =
      (Measure.map (externalTimePastHistory elapsed) (prefixLaw.prod activeLaw)).prod
        (activeLaw.prod inactiveLaw) := by
    simpa [factor, elapsed, prefixLaw, activeLaw, inactiveLaw] using
      map_externalTimeLeftHistory_residualCompanion prefixLaw hactive hinactive elapsed
        (measurable_alternatingEvenPrefixElapsed t n) (fun _ => le_max_left _ _)
  change Measure.map (factor ∘ split) (activeLaw.prod inactiveLaw) = _
  rw [← Measure.map_map (measurable_externalTimeLeftHistoryResidualCompanionFactor
    elapsed (measurable_alternatingEvenPrefixElapsed t n))
    (measurable_twoStreamPrefixActiveTailWithCompanion n), hsplit, hfactor]

/-- The even-prefix history is independent of the actual future pair.  This
is stated as independence (rather than only a map equality) so that later
count-fiber history restrictions can be applied without changing the future
law. -/
theorem indepFun_alternatingEvenPrefixResidualFactor
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (t : ℝ) (n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun paths => (alternatingEvenPrefixResidualFactor t n paths).1)
      (fun paths => (alternatingEvenPrefixResidualFactor t n paths).2)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) := by
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.map (prefixInterarrival n) activeLaw).prod
      (Measure.map (prefixInterarrival n) inactiveLaw)
  let elapsed : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    alternatingEvenPrefixElapsed t n
  let factor : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
    alternatingEvenPrefixResidualFactor t n
  let history : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ) →
      ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ)) :=
    externalTimePastHistory elapsed
  let future : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let historyLaw : Measure
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) :=
    Measure.map history (prefixLaw.prod activeLaw)
  let F := fun paths : (ℕ → ℝ) × (ℕ → ℝ) => (factor paths).1
  let G := fun paths : (ℕ → ℝ) × (ℕ → ℝ) => (factor paths).2
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival n) activeLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival n) inactiveLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingEvenPrefixElapsed t n)).aemeasurable
  have hfactor : Measure.map factor μ = historyLaw.prod future := by
    simpa [factor, μ, historyLaw, history, future, prefixLaw, activeLaw,
      inactiveLaw, elapsed] using
      map_alternatingEvenPrefixResidualFactor hactive hinactive t n
  have hF : Measurable F := by
    exact measurable_fst.comp
      (measurable_alternatingEvenPrefixResidualFactor t n)
  have hG : Measurable G := by
    exact measurable_snd.comp
      (measurable_alternatingEvenPrefixResidualFactor t n)
  have hmapF : Measure.map F μ = historyLaw := by
    calc
      Measure.map F μ = Measure.map (Prod.fst ∘ factor) μ := by rfl
      _ = Measure.map Prod.fst (Measure.map factor μ) := by
        exact (Measure.map_map measurable_fst
          (measurable_alternatingEvenPrefixResidualFactor t n)).symm
      _ = Measure.map Prod.fst (historyLaw.prod future) := by rw [hfactor]
      _ = historyLaw := by
        rw [Measure.map_fst_prod]
        simp
  have hmapG : Measure.map G μ = future := by
    calc
      Measure.map G μ = Measure.map (Prod.snd ∘ factor) μ := by rfl
      _ = Measure.map Prod.snd (Measure.map factor μ) := by
        exact (Measure.map_map measurable_snd
          (measurable_alternatingEvenPrefixResidualFactor t n)).symm
      _ = Measure.map Prod.snd (historyLaw.prod future) := by rw [hfactor]
      _ = future := by
        rw [Measure.map_snd_prod]
        simp
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hF.aemeasurable hG.aemeasurable]
  change Measure.map factor μ = (Measure.map F μ).prod (Measure.map G μ)
  rw [hfactor, hmapF, hmapG]

/-- The active-first two-stream split after possibly different visit counts.
It is used on odd alternating fibers, where the presently inactive stream has
one additional completed visit. -/
def twoStreamAsymmetricPrefixActiveTailWithCompanion
    (activeCount inactiveCount : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ → ℝ)) × (ℕ → ℝ) :=
  fun paths =>
    (((prefixInterarrival activeCount paths.1,
      prefixInterarrival inactiveCount paths.2),
      futureInterarrival activeCount paths.1),
      futureInterarrival inactiveCount paths.2)

/-- Measurability of the active-first asymmetric split. -/
theorem measurable_twoStreamAsymmetricPrefixActiveTailWithCompanion
    (activeCount inactiveCount : ℕ) :
    Measurable
      (twoStreamAsymmetricPrefixActiveTailWithCompanion activeCount inactiveCount) := by
  exact
    ((((measurable_prefixInterarrival activeCount).comp measurable_fst).prodMk
      ((measurable_prefixInterarrival inactiveCount).comp measurable_snd)).prodMk
      ((measurable_pi_iff.2 fun k =>
        measurable_futureInterarrival activeCount k).comp measurable_fst)).prodMk
      ((measurable_pi_iff.2 fun k =>
        measurable_futureInterarrival inactiveCount k).comp measurable_snd)

private theorem twoStreamAsymmetricPrefixActiveTailWithCompanion_eq_assoc
    (activeCount inactiveCount : ℕ) :
    twoStreamAsymmetricPrefixActiveTailWithCompanion activeCount inactiveCount =
      (MeasurableEquiv.prodAssoc.symm :
        ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
          ((ℕ → ℝ) × (ℕ → ℝ)) →
          (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
            (ℕ → ℝ)) × (ℕ → ℝ)) ∘
        twoStreamAsymmetricPrefixTail activeCount inactiveCount := by
  rfl

/-- The asymmetric active-first prefixes factor from their complete tails. -/
theorem map_twoStreamAsymmetricPrefixActiveTailWithCompanion
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (activeCount inactiveCount : ℕ) :
    Measure.map
      (twoStreamAsymmetricPrefixActiveTailWithCompanion activeCount inactiveCount)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) =
      ((((Measure.map (prefixInterarrival activeCount)
        (exponentialInterarrivalMeasure activeRate)).prod
          (Measure.map (prefixInterarrival inactiveCount)
            (exponentialInterarrivalMeasure inactiveRate))).prod
          (exponentialInterarrivalMeasure activeRate)).prod
        (exponentialInterarrivalMeasure inactiveRate)) := by
  let prefixLaw : Measure
      ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) :=
    (Measure.map (prefixInterarrival activeCount)
      (exponentialInterarrivalMeasure activeRate)).prod
      (Measure.map (prefixInterarrival inactiveCount)
        (exponentialInterarrivalMeasure inactiveRate))
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival activeCount) activeLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival activeCount).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival inactiveCount) inactiveLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival inactiveCount).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  rw [twoStreamAsymmetricPrefixActiveTailWithCompanion_eq_assoc
    activeCount inactiveCount]
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_twoStreamAsymmetricPrefixTail activeCount inactiveCount)]
  rw [map_twoStreamAsymmetricPrefixTail hactive hinactive activeCount inactiveCount]
  have hfactor :
      Measure.map (MeasurableEquiv.prodAssoc.symm :
        ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
          ((ℕ → ℝ) × (ℕ → ℝ)) →
          (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
            (ℕ → ℝ)) × (ℕ → ℝ))
        (prefixLaw.prod (activeLaw.prod inactiveLaw)) =
      (prefixLaw.prod activeLaw).prod inactiveLaw := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm :
          ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
            ((ℕ → ℝ) × (ℕ → ℝ)) →
            (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
              (ℕ → ℝ)) × (ℕ → ℝ)) ∘
          (MeasurableEquiv.prodAssoc :
            (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
              (ℕ → ℝ)) × (ℕ → ℝ) →
              ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
                ((ℕ → ℝ) × (ℕ → ℝ))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  simpa [prefixLaw, activeLaw, inactiveLaw] using hfactor

/-- The nonnegative elapsed time after asymmetric active/inactive prefixes. -/
def alternatingAsymmetricPrefixElapsed (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    (Fin activeCount → ℝ) × (Fin inactiveCount → ℝ) → ℝ :=
  fun prefixes => max 0
    (t - ((∑ i, prefixes.1 i) + ∑ i, prefixes.2 i))

/-- The asymmetric prefix elapsed clock is Borel measurable. -/
theorem measurable_alternatingAsymmetricPrefixElapsed (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    Measurable (alternatingAsymmetricPrefixElapsed t activeCount inactiveCount) := by
  unfold alternatingAsymmetricPrefixElapsed
  have hactive : Measurable
      (fun prefixes : (Fin activeCount → ℝ) × (Fin inactiveCount → ℝ) =>
        ∑ i, prefixes.1 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp measurable_fst
  have hinactive : Measurable
      (fun prefixes : (Fin activeCount → ℝ) × (Fin inactiveCount → ℝ) =>
        ∑ i, prefixes.2 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp measurable_snd
  exact measurable_const.max (measurable_const.sub (hactive.add hinactive))

/-- Expose asymmetric completed state-local prefixes and the current active
stream's stopped history.  The output future pair is the active residual tail
followed by the inactive untouched tail. -/
def alternatingAsymmetricPrefixResidualFactor (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ))) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  externalTimeLeftHistoryResidualCompanionFactor
    (alternatingAsymmetricPrefixElapsed t activeCount inactiveCount) ∘
      twoStreamAsymmetricPrefixActiveTailWithCompanion activeCount inactiveCount

/-- Measurability of the asymmetric prefix residual factor. -/
theorem measurable_alternatingAsymmetricPrefixResidualFactor (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    Measurable
      (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount) := by
  exact (measurable_externalTimeLeftHistoryResidualCompanionFactor
    (alternatingAsymmetricPrefixElapsed t activeCount inactiveCount)
    (measurable_alternatingAsymmetricPrefixElapsed t activeCount inactiveCount)).comp
      (measurable_twoStreamAsymmetricPrefixActiveTailWithCompanion
        activeCount inactiveCount)

/-- The asymmetric active prefix/history factors from a fresh active residual
tail and untouched inactive tail.  This is the product core for an odd
alternating-count fiber. -/
theorem map_alternatingAsymmetricPrefixResidualFactor
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (t : ℝ) (activeCount inactiveCount : ℕ) :
    Measure.map
      (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) =
      (Measure.map (externalTimePastHistory
        (alternatingAsymmetricPrefixElapsed t activeCount inactiveCount))
        (((Measure.map (prefixInterarrival activeCount)
          (exponentialInterarrivalMeasure activeRate)).prod
            (Measure.map (prefixInterarrival inactiveCount)
              (exponentialInterarrivalMeasure inactiveRate))).prod
          (exponentialInterarrivalMeasure activeRate))).prod
        ((exponentialInterarrivalMeasure activeRate).prod
          (exponentialInterarrivalMeasure inactiveRate)) := by
  let prefixLaw : Measure
      ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) :=
    (Measure.map (prefixInterarrival activeCount)
      (exponentialInterarrivalMeasure activeRate)).prod
      (Measure.map (prefixInterarrival inactiveCount)
        (exponentialInterarrivalMeasure inactiveRate))
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let elapsed : (Fin activeCount → ℝ) × (Fin inactiveCount → ℝ) → ℝ :=
    alternatingAsymmetricPrefixElapsed t activeCount inactiveCount
  let split : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ → ℝ)) × (ℕ → ℝ) :=
    twoStreamAsymmetricPrefixActiveTailWithCompanion activeCount inactiveCount
  let factor :
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ → ℝ)) × (ℕ → ℝ) →
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ))) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
    externalTimeLeftHistoryResidualCompanionFactor elapsed
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival activeCount) activeLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival activeCount).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival inactiveCount) inactiveLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival inactiveCount).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  have hsplit : Measure.map split (activeLaw.prod inactiveLaw) =
      (prefixLaw.prod activeLaw).prod inactiveLaw := by
    simpa [split, prefixLaw, activeLaw, inactiveLaw] using
      map_twoStreamAsymmetricPrefixActiveTailWithCompanion
        hactive hinactive activeCount inactiveCount
  have hfactor : Measure.map factor ((prefixLaw.prod activeLaw).prod inactiveLaw) =
      (Measure.map (externalTimePastHistory elapsed) (prefixLaw.prod activeLaw)).prod
        (activeLaw.prod inactiveLaw) := by
    simpa [factor, elapsed, prefixLaw, activeLaw, inactiveLaw] using
      map_externalTimeLeftHistory_residualCompanion prefixLaw hactive hinactive elapsed
        (measurable_alternatingAsymmetricPrefixElapsed t activeCount inactiveCount)
        (fun _ => le_max_left _ _)
  change Measure.map (factor ∘ split) (activeLaw.prod inactiveLaw) = _
  rw [← Measure.map_map
    (measurable_externalTimeLeftHistoryResidualCompanionFactor elapsed
      (measurable_alternatingAsymmetricPrefixElapsed t activeCount inactiveCount))
    (measurable_twoStreamAsymmetricPrefixActiveTailWithCompanion
      activeCount inactiveCount), hsplit, hfactor]

/-- The asymmetric active-prefix history is independent of its future pair.
For the odd alternating fiber, instantiate this with the current state first
and the other state second. -/
theorem indepFun_alternatingAsymmetricPrefixResidualFactor
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (t : ℝ) (activeCount inactiveCount : ℕ) :
    ProbabilityTheory.IndepFun
      (fun paths =>
        (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount paths).1)
      (fun paths =>
        (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount paths).2)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) := by
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let prefixLaw : Measure
      ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) :=
    (Measure.map (prefixInterarrival activeCount) activeLaw).prod
      (Measure.map (prefixInterarrival inactiveCount) inactiveLaw)
  let elapsed : (Fin activeCount → ℝ) × (Fin inactiveCount → ℝ) → ℝ :=
    alternatingAsymmetricPrefixElapsed t activeCount inactiveCount
  let factor : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ))) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
    alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount
  let history : ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
      (ℕ → ℝ) →
      ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ)) :=
    externalTimePastHistory elapsed
  let future : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let historyLaw : Measure
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ))) :=
    Measure.map history (prefixLaw.prod activeLaw)
  let F := fun paths : (ℕ → ℝ) × (ℕ → ℝ) => (factor paths).1
  let G := fun paths : (ℕ → ℝ) × (ℕ → ℝ) => (factor paths).2
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival activeCount) activeLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival activeCount).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival inactiveCount) inactiveLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival inactiveCount).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingAsymmetricPrefixElapsed t activeCount inactiveCount)).aemeasurable
  have hfactor : Measure.map factor μ = historyLaw.prod future := by
    simpa [factor, μ, historyLaw, history, future, prefixLaw, activeLaw,
      inactiveLaw, elapsed] using
      map_alternatingAsymmetricPrefixResidualFactor
        hactive hinactive t activeCount inactiveCount
  have hF : Measurable F := by
    exact measurable_fst.comp
      (measurable_alternatingAsymmetricPrefixResidualFactor
        t activeCount inactiveCount)
  have hG : Measurable G := by
    exact measurable_snd.comp
      (measurable_alternatingAsymmetricPrefixResidualFactor
        t activeCount inactiveCount)
  have hmapF : Measure.map F μ = historyLaw := by
    calc
      Measure.map F μ = Measure.map (Prod.fst ∘ factor) μ := by rfl
      _ = Measure.map Prod.fst (Measure.map factor μ) := by
        exact (Measure.map_map measurable_fst
          (measurable_alternatingAsymmetricPrefixResidualFactor
            t activeCount inactiveCount)).symm
      _ = Measure.map Prod.fst (historyLaw.prod future) := by rw [hfactor]
      _ = historyLaw := by
        rw [Measure.map_fst_prod]
        simp
  have hmapG : Measure.map G μ = future := by
    calc
      Measure.map G μ = Measure.map (Prod.snd ∘ factor) μ := by rfl
      _ = Measure.map Prod.snd (Measure.map factor μ) := by
        exact (Measure.map_map measurable_snd
          (measurable_alternatingAsymmetricPrefixResidualFactor
            t activeCount inactiveCount)).symm
      _ = Measure.map Prod.snd (historyLaw.prod future) := by rw [hfactor]
      _ = future := by
        rw [Measure.map_snd_prod]
        simp
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hF.aemeasurable hG.aemeasurable]
  change Measure.map factor μ = (Measure.map F μ).prod (Measure.map G μ)
  rw [hfactor, hmapF, hmapG]

/-- Deterministically shifting both state-local streams after the same number
of completed visits commutes with their pair representation. -/
theorem switchGapsAfterPairs_twoStateGapsOfPair
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) :
    TwoStateSwitching.switchGapsAfterPairs
      (TwoStateSwitching.twoStateGapsOfPair paths) n =
      TwoStateSwitching.twoStateGapsOfPair
        (futureInterarrival n paths.1, futureInterarrival n paths.2) := by
  funext state k
  fin_cases state <;> rfl

/-- If the currently active shifted stream has zero renewal count at an
elapsed time, reducing its first gap is exactly its literal residual tail.
The inactive state-local stream remains literally untouched. -/
theorem switchGapsAfterActiveElapsed_eq_residualTail_companion
    (active inactive : ℕ → ℝ) (elapsed : ℝ)
    (hactive : canonicalRenewalCount elapsed active = 0) :
    TwoStateSwitching.switchGapsAfterActiveElapsed 0
      (TwoStateSwitching.twoStateGapsOfPair (active, inactive)) elapsed =
      TwoStateSwitching.twoStateGapsOfPair (residualTail elapsed active, inactive) := by
  have hresidual : residualTail elapsed active =
      firstGapResidualTail elapsed active := by
    have h := residualTail_eq_firstGapResidualTail_on_countFiber
      elapsed active 0 hactive
    have hfuture : futureInterarrival 0 active = active := by
      funext k
      simp [futureInterarrival, interarrival]
    simpa [arrivalPrefix, hfuture] using h
  funext state k
  fin_cases state
  · cases k with
    | zero =>
        simp [TwoStateSwitching.switchGapsAfterActiveElapsed,
          TwoStateSwitching.twoStateGapsOfPair, hresidual, firstGapResidualTail,
          interarrival]
    | succ k =>
        simp [TwoStateSwitching.switchGapsAfterActiveElapsed,
          TwoStateSwitching.twoStateGapsOfPair, hresidual, firstGapResidualTail,
          interarrival]
  · simp [TwoStateSwitching.switchGapsAfterActiveElapsed,
      TwoStateSwitching.twoStateGapsOfPair]

/-- The state-one counterpart: only the first state-one coordinate is
residualized, while the state-zero companion remains literal. -/
theorem switchGapsAfterActiveElapsed_one_eq_companion_residualTail
    (inactive active : ℕ → ℝ) (elapsed : ℝ)
    (hactive : canonicalRenewalCount elapsed active = 0) :
    TwoStateSwitching.switchGapsAfterActiveElapsed 1
      (TwoStateSwitching.twoStateGapsOfPair (inactive, active)) elapsed =
      TwoStateSwitching.twoStateGapsOfPair (inactive, residualTail elapsed active) := by
  have hresidual : residualTail elapsed active =
      firstGapResidualTail elapsed active := by
    have h := residualTail_eq_firstGapResidualTail_on_countFiber
      elapsed active 0 hactive
    have hfuture : futureInterarrival 0 active = active := by
      funext k
      simp [futureInterarrival, interarrival]
    simpa [arrivalPrefix, hfuture] using h
  funext state k
  fin_cases state
  · simp [TwoStateSwitching.switchGapsAfterActiveElapsed,
      TwoStateSwitching.twoStateGapsOfPair]
  · cases k with
    | zero =>
        simp [TwoStateSwitching.switchGapsAfterActiveElapsed,
          TwoStateSwitching.twoStateGapsOfPair, hresidual, firstGapResidualTail,
          interarrival]
    | succ k =>
        simp [TwoStateSwitching.switchGapsAfterActiveElapsed,
          TwoStateSwitching.twoStateGapsOfPair, hresidual, firstGapResidualTail,
          interarrival]

/-- After an equal pair shift and the following state-zero visit, the
state-zero tail has advanced one additional coordinate while the state-one
tail has not. -/
theorem switchGapsAfterFirst_zero_afterPairs_twoStateGapsOfPair
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) :
    TwoStateSwitching.switchGapsAfterFirst 0
      (TwoStateSwitching.switchGapsAfterPairs
        (TwoStateSwitching.twoStateGapsOfPair paths) n) =
      TwoStateSwitching.twoStateGapsOfPair
        (futureInterarrival (n + 1) paths.1, futureInterarrival n paths.2) := by
  funext state k
  fin_cases state
  · change paths.1 (n + (k + 1)) = paths.1 ((n + 1) + k)
    rw [Nat.add_comm k 1, ← Nat.add_assoc]
  · change paths.2 (n + k) = paths.2 (n + k)
    rfl

/-- On an even alternating-count fiber, the literal state-indexed future
streams are exactly the residual of the active shifted stream and the
untouched inactive shifted stream.  The separate active-count premise is the
history-coordinate condition that will be imposed when restricting the
product factor above. -/
theorem switchGapsAfterElapsed_evenFiber_eq_residualActive_companion
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ)
    (hcount : canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n)
    (hprefix :
      (∑ i, (prefixInterarrival n paths.1) i) +
        ∑ i, (prefixInterarrival n paths.2) i ≤ t)
    (hactive : canonicalRenewalCount
      (alternatingEvenPrefixElapsed t n
        (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
      (futureInterarrival n paths.1) = 0) :
    TwoStateSwitching.switchGapsAfterElapsed 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t =
      TwoStateSwitching.twoStateGapsOfPair
        (externalTimeResidualTail (alternatingEvenPrefixElapsed t n)
          ((prefixInterarrival n paths.1, prefixInterarrival n paths.2),
            futureInterarrival n paths.1),
          futureInterarrival n paths.2) := by
  let elapsed := alternatingEvenPrefixElapsed t n
    (prefixInterarrival n paths.1, prefixInterarrival n paths.2)
  have hprefix' : arrivalPrefix n paths.1 + arrivalPrefix n paths.2 ≤ t := by
    simpa [prefixInterarrival, arrivalPrefix, interarrival,
      Fin.sum_univ_eq_sum_range] using hprefix
  have hsum :
      (∑ i, prefixInterarrival n paths.1 i) +
        ∑ i, prefixInterarrival n paths.2 i =
      arrivalPrefix n paths.1 + arrivalPrefix n paths.2 := by
    simp [prefixInterarrival, arrivalPrefix, interarrival,
      Fin.sum_univ_eq_sum_range]
  have helapsed : elapsed = t -
      (arrivalPrefix n paths.1 + arrivalPrefix n paths.2) := by
    rw [show elapsed = max 0
      (t - ((∑ i, prefixInterarrival n paths.1 i) +
        ∑ i, prefixInterarrival n paths.2 i)) by rfl,
      max_eq_right (sub_nonneg.mpr hprefix), hsum]
  rw [TwoStateSwitching.switchGapsAfterElapsed_of_count_eq_two_mul 0
    (TwoStateSwitching.twoStateGapsOfPair paths) t n hcount,
    switchGapsAfterPairs_twoStateGapsOfPair]
  change TwoStateSwitching.switchGapsAfterActiveElapsed 0
      (TwoStateSwitching.twoStateGapsOfPair
        (futureInterarrival n paths.1, futureInterarrival n paths.2))
      (t - (arrivalPrefix n paths.1 + arrivalPrefix n paths.2)) = _
  rw [← helapsed]
  simpa [elapsed, externalTimeResidualTail] using
    switchGapsAfterActiveElapsed_eq_residualTail_companion
      (futureInterarrival n paths.1) (futureInterarrival n paths.2) elapsed hactive

/-- On an odd alternating-count fiber that began in state zero, the literal
future state-indexed streams are the untouched state-zero tail after its
`n+1`st completed visit and the genuine residual of the currently active
state-one tail after its `n`th completed visit. -/
theorem switchGapsAfterElapsed_oddFiber_eq_companion_residualActive
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ)
    (hcount : canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1)
    (hprefix :
      (∑ i, prefixInterarrival (n + 1) paths.1 i) +
        ∑ i, prefixInterarrival n paths.2 i ≤ t)
    (hactive : canonicalRenewalCount
      (alternatingAsymmetricPrefixElapsed t n (n + 1)
        (prefixInterarrival n paths.2,
          prefixInterarrival (n + 1) paths.1))
      (futureInterarrival n paths.2) = 0) :
    TwoStateSwitching.switchGapsAfterElapsed 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t =
      TwoStateSwitching.twoStateGapsOfPair (Prod.swap
        (alternatingAsymmetricPrefixResidualFactor t n (n + 1)
          (paths.2, paths.1)).2) := by
  let elapsed := alternatingAsymmetricPrefixElapsed t n (n + 1)
    (prefixInterarrival n paths.2, prefixInterarrival (n + 1) paths.1)
  have hsum :
      (∑ i, prefixInterarrival n paths.2 i) +
        ∑ i, prefixInterarrival (n + 1) paths.1 i =
      arrivalPrefix n paths.2 + arrivalPrefix (n + 1) paths.1 := by
    simp [prefixInterarrival, arrivalPrefix, interarrival,
      Fin.sum_univ_eq_sum_range]
  have hprefixFlip :
      (∑ i, prefixInterarrival n paths.2 i) +
        ∑ i, prefixInterarrival (n + 1) paths.1 i ≤ t := by
    linarith
  have helapsed : elapsed = t -
      (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2) := by
    rw [show elapsed = max 0
      (t - ((∑ i, prefixInterarrival n paths.2 i) +
        ∑ i, prefixInterarrival (n + 1) paths.1 i)) by rfl,
      max_eq_right (sub_nonneg.mpr hprefixFlip), hsum]
    ring
  rw [TwoStateSwitching.switchGapsAfterElapsed_of_count_eq_two_mul_add_one 0
    (TwoStateSwitching.twoStateGapsOfPair paths) t n hcount,
    switchGapsAfterFirst_zero_afterPairs_twoStateGapsOfPair]
  change TwoStateSwitching.switchGapsAfterActiveElapsed 1
      (TwoStateSwitching.twoStateGapsOfPair
        (futureInterarrival (n + 1) paths.1, futureInterarrival n paths.2))
      (t - (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2)) = _
  rw [← helapsed]
  simpa [elapsed, alternatingAsymmetricPrefixResidualFactor,
    twoStreamAsymmetricPrefixActiveTailWithCompanion, externalTimeResidualTail,
    externalTimeLeftHistoryResidualCompanionFactor] using
    switchGapsAfterActiveElapsed_one_eq_companion_residualTail
      (futureInterarrival (n + 1) paths.1) (futureInterarrival n paths.2)
      elapsed hactive

/-- After `n` complete visits from each state-local stream, the alternating
renewal count is the completed even count plus the count of the literal
shifted alternating tail.  This is a deterministic renewal identity; the
tail-divergence and positivity premises will later hold almost surely under
the product exponential law. -/
theorem canonicalRenewalCount_evenPrefix_add
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hpos : ∀ i : ℕ, 0 < interarrival i
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (htail : Tendsto (fun m : ℕ => arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair
          (futureInterarrival n paths.1, futureInterarrival n paths.2))))
      atTop atTop) :
    canonicalRenewalCount
      (arrivalPrefix n paths.1 + arrivalPrefix n paths.2 + u)
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) =
      2 * n + canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair
            (futureInterarrival n paths.1, futureInterarrival n paths.2))) := by
  let gaps := TwoStateSwitching.alternatingGaps 0
    (TwoStateSwitching.twoStateGapsOfPair paths)
  have htail' : Tendsto (fun m : ℕ => futureArrivalTime (2 * n) m gaps)
      atTop atTop := by
    simpa [gaps, futureArrivalTime_eq_arrivalTime_tail,
      TwoStateSwitching.futureInterarrival_two_mul_alternatingGaps,
      switchGapsAfterPairs_twoStateGapsOfPair] using htail
  have hcount := canonicalRenewalCount_arrivalPrefix_add
    (2 * n) u hu gaps hpos htail'
  rw [TwoStateSwitching.arrivalPrefix_two_mul_alternatingGaps] at hcount
  simpa [gaps, TwoStateSwitching.futureInterarrival_two_mul_alternatingGaps,
    switchGapsAfterPairs_twoStateGapsOfPair] using hcount

/-- After `n + 1` completed state-zero visits and `n` completed state-one
visits, the alternating renewal count is the odd completed count plus the
literal state-one-started shifted tail count. -/
theorem canonicalRenewalCount_oddPrefix_add
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hpos : ∀ i : ℕ, 0 < interarrival i
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (htail : Tendsto (fun m : ℕ => arrivalTime m
      (TwoStateSwitching.alternatingGaps 1
        (TwoStateSwitching.twoStateGapsOfPair
          (futureInterarrival (n + 1) paths.1,
            futureInterarrival n paths.2)))) atTop atTop) :
    canonicalRenewalCount
      (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 + u)
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) =
      (2 * n + 1) + canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 1
          (TwoStateSwitching.twoStateGapsOfPair
            (futureInterarrival (n + 1) paths.1,
              futureInterarrival n paths.2))) := by
  let gaps := TwoStateSwitching.alternatingGaps 0
    (TwoStateSwitching.twoStateGapsOfPair paths)
  have htail' : Tendsto (fun m : ℕ => futureArrivalTime (2 * n + 1) m gaps)
      atTop atTop := by
    simpa [gaps, futureArrivalTime_eq_arrivalTime_tail,
      TwoStateSwitching.futureInterarrival_two_mul_add_one_alternatingGaps,
      switchGapsAfterFirst_zero_afterPairs_twoStateGapsOfPair] using htail
  have hcount := canonicalRenewalCount_arrivalPrefix_add
    (2 * n + 1) u hu gaps hpos htail'
  rw [TwoStateSwitching.arrivalPrefix_two_mul_add_one_alternatingGaps] at hcount
  simpa [gaps,
    TwoStateSwitching.futureInterarrival_two_mul_add_one_alternatingGaps,
    switchGapsAfterFirst_zero_afterPairs_twoStateGapsOfPair] using hcount

/-- An even canonical alternating count has completed the corresponding
state-local prefix.  The `n = 0` case uses the nonnegative calendar domain;
positive fibers follow directly from the definition of the canonical count. -/
theorem canonicalRenewalCount_even_eq_prefix_le
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ) (ht : 0 ≤ t)
    (hfuture : ∃ m : ℕ, t < arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (hcount : canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n) :
    arrivalPrefix n paths.1 + arrivalPrefix n paths.2 ≤ t := by
  cases n with
  | zero =>
      simpa [arrivalPrefix] using ht
  | succ n =>
      let gaps := TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)
      have hlt : 2 * (n + 1) - 1 < canonicalRenewalCount t gaps := by
        rw [show canonicalRenewalCount t gaps = 2 * (n + 1) by
          simpa [gaps] using hcount]
        omega
      have hle := arrivalTime_le_of_lt_canonicalRenewalCount t gaps hfuture hlt
      have hpref : arrivalPrefix (2 * (n + 1)) gaps =
          arrivalTime (2 * (n + 1) - 1) gaps := by
        unfold arrivalPrefix arrivalTime
        congr 1
      calc
        arrivalPrefix (n + 1) paths.1 + arrivalPrefix (n + 1) paths.2 =
            arrivalPrefix (2 * (n + 1)) gaps := by
              symm
              simpa [gaps] using
                TwoStateSwitching.arrivalPrefix_two_mul_alternatingGaps 0
                  (TwoStateSwitching.twoStateGapsOfPair paths) (n + 1)
        _ = arrivalTime (2 * (n + 1) - 1) gaps := hpref
        _ ≤ t := hle

/-- An odd canonical alternating count has completed the asymmetric prefix
of `n + 1` state-zero and `n` state-one visits. -/
theorem canonicalRenewalCount_odd_eq_prefix_le
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ)
    (hfuture : ∃ m : ℕ, t < arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (hcount : canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1) :
    arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t := by
  let gaps := TwoStateSwitching.alternatingGaps 0
    (TwoStateSwitching.twoStateGapsOfPair paths)
  have hlt : 2 * n < canonicalRenewalCount t gaps := by
    rw [show canonicalRenewalCount t gaps = 2 * n + 1 by
      simpa [gaps] using hcount]
    omega
  have hle := arrivalTime_le_of_lt_canonicalRenewalCount t gaps hfuture hlt
  have hpref : arrivalPrefix (2 * n + 1) gaps = arrivalTime (2 * n) gaps := by
    unfold arrivalPrefix arrivalTime
    rfl
  calc
    arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 =
        arrivalPrefix (2 * n + 1) gaps := by
          symm
          simpa [gaps] using
            TwoStateSwitching.arrivalPrefix_two_mul_add_one_alternatingGaps 0
              (TwoStateSwitching.twoStateGapsOfPair paths) n
    _ = arrivalTime (2 * n) gaps := hpref
    _ ≤ t := hle

/-- A shifted alternating tail has zero count exactly when its currently
active state-local stream has zero count, provided both paths continue beyond
the displayed time.  The result concerns only the first hold and does not
identify any simultaneous residual clock. -/
theorem canonicalRenewalCount_zero_alternating_iff_active_zero
    (active inactive : ℕ → ℝ) (u : ℝ)
    (halt : ∃ m : ℕ, u < arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair (active, inactive))) )
    (hactive : ∃ m : ℕ, u < arrivalTime m active) :
    canonicalRenewalCount u
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair (active, inactive))) = 0 ↔
      canonicalRenewalCount u active = 0 := by
  rw [canonicalRenewalCount_eq_zero_iff,
    canonicalRenewalCount_eq_zero_iff]
  simp only [halt, hactive, not_true_eq_false, or_false]
  simp [arrivalTime, TwoStateSwitching.alternatingGaps,
    TwoStateSwitching.alternatingGap,
    TwoStateSwitching.twoStateGapsOfPair, interarrival]

/-- On every positive, nonexplosive regular path, the even alternating-count
fiber is exactly the event visible in the even prefix/residual history: its
two consumed prefixes have elapsed and the current active tail has zero
count.  This is the deterministic identification needed before applying the
even product factor to a measurable fiber event. -/
theorem canonicalRenewalCount_even_iff_prefix_activeZero
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ) (ht : 0 ≤ t)
    (hfuture : ∃ m : ℕ, t < arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (hpos : ∀ i : ℕ, 0 < interarrival i
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (htail : Tendsto (fun m : ℕ => arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair
          (futureInterarrival n paths.1, futureInterarrival n paths.2))))
      atTop atTop)
    (hactiveTail : Tendsto (fun m : ℕ => arrivalTime m
      (futureInterarrival n paths.1)) atTop atTop) :
    canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n ↔
      (arrivalPrefix n paths.1 + arrivalPrefix n paths.2 ≤ t ∧
        canonicalRenewalCount
          (alternatingEvenPrefixElapsed t n
            (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
          (futureInterarrival n paths.1) = 0) := by
  let gaps := TwoStateSwitching.alternatingGaps 0
    (TwoStateSwitching.twoStateGapsOfPair paths)
  let elapsedPrefix := arrivalPrefix n paths.1 + arrivalPrefix n paths.2
  let active := futureInterarrival n paths.1
  let inactive := futureInterarrival n paths.2
  have hprefixSum :
      (∑ i, prefixInterarrival n paths.1 i) +
        ∑ i, prefixInterarrival n paths.2 i = elapsedPrefix := by
    simp [elapsedPrefix, prefixInterarrival, arrivalPrefix, interarrival,
      Fin.sum_univ_eq_sum_range]
  have hprefixPath : arrivalPrefix (2 * n) gaps = elapsedPrefix := by
    simpa [gaps, elapsedPrefix] using
      TwoStateSwitching.arrivalPrefix_two_mul_alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths) n
  have hzero : ∀ u : ℝ,
      canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair (active, inactive))) = 0 ↔
        canonicalRenewalCount u active = 0 := by
    intro u
    apply canonicalRenewalCount_zero_alternating_iff_active_zero
    · exact (htail.eventually_gt_atTop u).exists
    · exact (hactiveTail.eventually_gt_atTop u).exists
  constructor
  · intro hcount
    have hpref : elapsedPrefix ≤ t := by
      simpa [gaps, elapsedPrefix] using canonicalRenewalCount_even_eq_prefix_le
        paths t n ht hfuture hcount
    let u := t - elapsedPrefix
    have hu : 0 ≤ u := sub_nonneg.mpr hpref
    have htotal : canonicalRenewalCount (elapsedPrefix + u) gaps = 2 * n := by
      rw [show elapsedPrefix + u = t by dsimp [u]; ring]
      simpa [gaps] using hcount
    have hshift := canonicalRenewalCount_evenPrefix_add paths n u hu hpos htail
    have htailZero : canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair (active, inactive))) = 0 := by
      rw [hshift] at htotal
      simpa [active, inactive] using Nat.add_left_cancel htotal
    refine ⟨hpref, ?_⟩
    rw [show alternatingEvenPrefixElapsed t n
      (prefixInterarrival n paths.1, prefixInterarrival n paths.2) = u by
        dsimp [u]
        rw [alternatingEvenPrefixElapsed, hprefixSum,
          max_eq_right (sub_nonneg.mpr hpref)] ]
    exact (hzero u).mp htailZero
  · rintro ⟨hpref, hactiveZero⟩
    let u := t - elapsedPrefix
    have hu : 0 ≤ u := sub_nonneg.mpr hpref
    have htime : elapsedPrefix + u = t := by
      dsimp [u]
      ring
    have hactiveZero' : canonicalRenewalCount u active = 0 := by
      rw [← hactiveZero]
      dsimp [u]
      rw [alternatingEvenPrefixElapsed, hprefixSum,
        max_eq_right (sub_nonneg.mpr hpref)]
    have htailZero : canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair (active, inactive))) = 0 :=
      (hzero u).mpr hactiveZero'
    have hshift := canonicalRenewalCount_evenPrefix_add paths n u hu hpos htail
    have htotal : canonicalRenewalCount t gaps = 2 * n +
        canonicalRenewalCount u
          (TwoStateSwitching.alternatingGaps 0
            (TwoStateSwitching.twoStateGapsOfPair (active, inactive))) := by
      calc
        canonicalRenewalCount t gaps =
            canonicalRenewalCount (elapsedPrefix + u) gaps := by rw [htime]
        _ = _ := by
          simpa [gaps, elapsedPrefix, active, inactive] using hshift
    rw [htailZero] at htotal
    simpa [gaps] using htotal

/-- The state-one-started version of the zero-count identification. -/
theorem canonicalRenewalCount_zero_alternating_one_iff_active_zero
    (inactive active : ℕ → ℝ) (u : ℝ)
    (halt : ∃ m : ℕ, u < arrivalTime m
      (TwoStateSwitching.alternatingGaps 1
        (TwoStateSwitching.twoStateGapsOfPair (inactive, active))) )
    (hactive : ∃ m : ℕ, u < arrivalTime m active) :
    canonicalRenewalCount u
      (TwoStateSwitching.alternatingGaps 1
        (TwoStateSwitching.twoStateGapsOfPair (inactive, active))) = 0 ↔
      canonicalRenewalCount u active = 0 := by
  rw [canonicalRenewalCount_eq_zero_iff,
    canonicalRenewalCount_eq_zero_iff]
  simp only [halt, hactive, not_true_eq_false, or_false]
  simp [arrivalTime, TwoStateSwitching.alternatingGaps,
    TwoStateSwitching.alternatingGap,
    TwoStateSwitching.twoStateGapsOfPair, interarrival]

/-- On every positive, nonexplosive regular path, the odd alternating-count
fiber is exactly the asymmetric exposed-history event: the state-zero
`n+1`/state-one `n` prefixes have elapsed and the active state-one tail has
zero count. -/
theorem canonicalRenewalCount_odd_iff_prefix_activeZero
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ)
    (hfuture : ∃ m : ℕ, t < arrivalTime m
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (hpos : ∀ i : ℕ, 0 < interarrival i
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)))
    (htail : Tendsto (fun m : ℕ => arrivalTime m
      (TwoStateSwitching.alternatingGaps 1
        (TwoStateSwitching.twoStateGapsOfPair
          (futureInterarrival (n + 1) paths.1,
            futureInterarrival n paths.2)))) atTop atTop)
    (hactiveTail : Tendsto (fun m : ℕ => arrivalTime m
      (futureInterarrival n paths.2)) atTop atTop) :
    canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1 ↔
      (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t ∧
        canonicalRenewalCount
          (alternatingAsymmetricPrefixElapsed t n (n + 1)
            (prefixInterarrival n paths.2,
              prefixInterarrival (n + 1) paths.1))
          (futureInterarrival n paths.2) = 0) := by
  let gaps := TwoStateSwitching.alternatingGaps 0
    (TwoStateSwitching.twoStateGapsOfPair paths)
  let elapsedPrefix := arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2
  let active := futureInterarrival n paths.2
  let inactive := futureInterarrival (n + 1) paths.1
  have hprefixSum :
      (∑ i, prefixInterarrival n paths.2 i) +
        ∑ i, prefixInterarrival (n + 1) paths.1 i = elapsedPrefix := by
    simp [elapsedPrefix, prefixInterarrival, arrivalPrefix, interarrival,
      Fin.sum_univ_eq_sum_range]
    ring
  have hzero : ∀ u : ℝ,
      canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 1
          (TwoStateSwitching.twoStateGapsOfPair (inactive, active))) = 0 ↔
        canonicalRenewalCount u active = 0 := by
    intro u
    apply canonicalRenewalCount_zero_alternating_one_iff_active_zero
    · exact (htail.eventually_gt_atTop u).exists
    · exact (hactiveTail.eventually_gt_atTop u).exists
  constructor
  · intro hcount
    have hpref : elapsedPrefix ≤ t := by
      simpa [gaps, elapsedPrefix] using canonicalRenewalCount_odd_eq_prefix_le
        paths t n hfuture hcount
    let u := t - elapsedPrefix
    have hu : 0 ≤ u := sub_nonneg.mpr hpref
    have htotal : canonicalRenewalCount (elapsedPrefix + u) gaps = 2 * n + 1 := by
      rw [show elapsedPrefix + u = t by dsimp [u]; ring]
      simpa [gaps] using hcount
    have hshift := canonicalRenewalCount_oddPrefix_add paths n u hu hpos htail
    have htailZero : canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 1
          (TwoStateSwitching.twoStateGapsOfPair (inactive, active))) = 0 := by
      rw [hshift] at htotal
      simpa [inactive, active] using Nat.add_left_cancel htotal
    refine ⟨hpref, ?_⟩
    rw [show alternatingAsymmetricPrefixElapsed t n (n + 1)
      (prefixInterarrival n paths.2, prefixInterarrival (n + 1) paths.1) = u by
        dsimp [u]
        rw [alternatingAsymmetricPrefixElapsed, hprefixSum,
          max_eq_right (sub_nonneg.mpr hpref)] ]
    exact (hzero u).mp htailZero
  · rintro ⟨hpref, hactiveZero⟩
    let u := t - elapsedPrefix
    have hu : 0 ≤ u := sub_nonneg.mpr hpref
    have htime : elapsedPrefix + u = t := by
      dsimp [u]
      ring
    have hactiveZero' : canonicalRenewalCount u active = 0 := by
      rw [← hactiveZero]
      dsimp [u]
      rw [alternatingAsymmetricPrefixElapsed, hprefixSum,
        max_eq_right (sub_nonneg.mpr hpref)]
    have htailZero : canonicalRenewalCount u
        (TwoStateSwitching.alternatingGaps 1
          (TwoStateSwitching.twoStateGapsOfPair (inactive, active))) = 0 :=
      (hzero u).mpr hactiveZero'
    have hshift := canonicalRenewalCount_oddPrefix_add paths n u hu hpos htail
    have htotal : canonicalRenewalCount t gaps = (2 * n + 1) +
        canonicalRenewalCount u
          (TwoStateSwitching.alternatingGaps 1
            (TwoStateSwitching.twoStateGapsOfPair (inactive, active))) := by
      calc
        canonicalRenewalCount t gaps =
            canonicalRenewalCount (elapsedPrefix + u) gaps := by rw [htime]
        _ = _ := by
          simpa [gaps, elapsedPrefix, inactive, active] using hshift
    rw [htailZero] at htotal
    simpa [gaps] using htotal

/-- Under the two-stream exponential product law, the even-fiber/history
equivalence holds simultaneously for every nonnegative calendar time.  Its
regularity premises are transported a.s. from the literal product inputs. -/
theorem ae_forall_canonicalRenewalCount_even_iff_prefix_activeZero
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate) (n : ℕ) :
    ∀ᵐ paths ∂
      (exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate),
      ∀ t : ℝ, 0 ≤ t →
        (canonicalRenewalCount t
          (TwoStateSwitching.alternatingGaps 0
            (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n ↔
          (arrivalPrefix n paths.1 + arrivalPrefix n paths.2 ≤ t ∧
            canonicalRenewalCount
              (alternatingEvenPrefixElapsed t n
                (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
              (futureInterarrival n paths.1) = 0)) := by
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let shift : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun paths => (futureInterarrival n paths.1, futureInterarrival n paths.2)
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  have hfst : HasLaw (Prod.fst : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ) activeLaw μ :=
    ⟨measurable_fst.aemeasurable, by
      rw [Measure.map_fst_prod]
      simp⟩
  have hsnd : HasLaw (Prod.snd : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ) inactiveLaw μ :=
    ⟨measurable_snd.aemeasurable, by
      rw [Measure.map_snd_prod]
      simp⟩
  have hactivePos : ∀ᵐ paths ∂μ, ∀ k : ℕ, 0 < interarrival k paths.1 := by
    have hmap : ∀ᵐ gaps ∂Measure.map Prod.fst μ,
        ∀ k : ℕ, 0 < interarrival k gaps := by
      rw [hfst.map_eq]
      exact ae_all_interarrival_positive hactive
    exact Measure.tendsto_ae_map hfst.aemeasurable hmap
  have hinactivePos : ∀ᵐ paths ∂μ, ∀ k : ℕ, 0 < interarrival k paths.2 := by
    have hmap : ∀ᵐ gaps ∂Measure.map Prod.snd μ,
        ∀ k : ℕ, 0 < interarrival k gaps := by
      rw [hsnd.map_eq]
      exact ae_all_interarrival_positive hinactive
    exact Measure.tendsto_ae_map hsnd.aemeasurable hmap
  have hshiftMeas : Measurable shift := by
    exact
      ((measurable_pi_iff.2 fun k => measurable_futureInterarrival n k).comp
        measurable_fst).prodMk
        ((measurable_pi_iff.2 fun k => measurable_futureInterarrival n k).comp
          measurable_snd)
  have hshiftLaw : HasLaw shift μ μ := by
    refine ⟨hshiftMeas.aemeasurable, ?_⟩
    change Measure.map (Prod.map (futureInterarrival n) (futureInterarrival n))
      (activeLaw.prod inactiveLaw) = activeLaw.prod inactiveLaw
    rw [← Measure.map_prod_map _ _
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k),
      (futureInterarrival_hasLaw_path hactive n).map_eq,
      (futureInterarrival_hasLaw_path hinactive n).map_eq]
  have hglobal : ∀ᵐ paths ∂μ, Tendsto (fun k : ℕ => arrivalTime k
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths))) atTop atTop := by
    simpa [μ, activeLaw, inactiveLaw] using
      TwoStateSwitching.ae_tendsto_arrivalTime_alternatingGaps_prod
        0 activeRate inactiveRate hactive hinactive
  have htail : ∀ᵐ paths ∂μ, Tendsto (fun k : ℕ => arrivalTime k
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair (shift paths)))) atTop atTop := by
    have hmap : ∀ᵐ tails ∂Measure.map shift μ, Tendsto (fun k : ℕ => arrivalTime k
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair tails))) atTop atTop := by
      rw [hshiftLaw.map_eq]
      simpa [μ, activeLaw, inactiveLaw] using
        TwoStateSwitching.ae_tendsto_arrivalTime_alternatingGaps_prod
          0 activeRate inactiveRate hactive hinactive
    exact Measure.tendsto_ae_map hshiftLaw.aemeasurable hmap
  have hactiveTailLaw : HasLaw
      (fun paths : (ℕ → ℝ) × (ℕ → ℝ) => futureInterarrival n paths.1)
      activeLaw μ := by
    simpa [Function.comp_def] using
      (futureInterarrival_hasLaw_path hactive n).fun_comp hfst
  have hactiveTail : ∀ᵐ paths ∂μ, Tendsto (fun k : ℕ => arrivalTime k
      (futureInterarrival n paths.1)) atTop atTop := by
    have hmap : ∀ᵐ gaps ∂Measure.map
        (fun paths : (ℕ → ℝ) × (ℕ → ℝ) => futureInterarrival n paths.1) μ,
        Tendsto (fun k : ℕ => arrivalTime k gaps) atTop atTop := by
      rw [hactiveTailLaw.map_eq]
      simpa [activeLaw] using ae_arrivalTime_tendsto_atTop hactive
    exact Measure.tendsto_ae_map hactiveTailLaw.aemeasurable hmap
  change ∀ᵐ paths ∂μ, ∀ t : ℝ, 0 ≤ t →
    (canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n ↔
      (arrivalPrefix n paths.1 + arrivalPrefix n paths.2 ≤ t ∧
        canonicalRenewalCount
          (alternatingEvenPrefixElapsed t n
            (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
          (futureInterarrival n paths.1) = 0))
  refine (hglobal.and (hactivePos.and (hinactivePos.and (htail.and hactiveTail)))).mono ?_
  intro paths hregular
  rcases hregular with ⟨hglobal, hactivePos, hinactivePos, htail, hactiveTail⟩
  intro t ht
  apply canonicalRenewalCount_even_iff_prefix_activeZero paths t n ht
    ((hglobal.eventually_gt_atTop t).exists)
  · intro k
    rcases k.even_or_odd' with ⟨m, rfl | rfl⟩
    · change 0 < TwoStateSwitching.alternatingGap 0
        (TwoStateSwitching.twoStateGapsOfPair paths) (2 * m)
      rw [TwoStateSwitching.alternatingGap_two_mul]
      simpa [interarrival] using hactivePos m
    · change 0 < TwoStateSwitching.alternatingGap 0
        (TwoStateSwitching.twoStateGapsOfPair paths) (2 * m + 1)
      rw [TwoStateSwitching.alternatingGap_two_mul_add_one]
      simpa [interarrival] using hinactivePos m
  · simpa [shift] using htail
  · exact hactiveTail

/-- The odd-fiber/history equivalence holds simultaneously for every
nonnegative time almost surely under the two-stream exponential product law.
The state-one active stream is selected only after the asymmetric deterministic
prefix split; no simultaneous calendar residual is used. -/
theorem ae_forall_canonicalRenewalCount_odd_iff_prefix_activeZero
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate) (n : ℕ) :
    ∀ᵐ paths ∂
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate),
      ∀ t : ℝ, 0 ≤ t →
        (canonicalRenewalCount t
          (TwoStateSwitching.alternatingGaps 0
            (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1 ↔
          (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t ∧
            canonicalRenewalCount
              (alternatingAsymmetricPrefixElapsed t n (n + 1)
                (prefixInterarrival n paths.2,
                  prefixInterarrival (n + 1) paths.1))
              (futureInterarrival n paths.2) = 0)) := by
  let leftLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := leftLaw.prod rightLaw
  let shift : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun paths => (futureInterarrival (n + 1) paths.1,
      futureInterarrival n paths.2)
  letI : IsProbabilityMeasure leftLaw := by
    simpa [leftLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightLaw := by
    simpa [rightLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  have hfst : HasLaw (Prod.fst : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ) leftLaw μ :=
    ⟨measurable_fst.aemeasurable, by
      rw [Measure.map_fst_prod]
      simp⟩
  have hsnd : HasLaw (Prod.snd : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ) rightLaw μ :=
    ⟨measurable_snd.aemeasurable, by
      rw [Measure.map_snd_prod]
      simp⟩
  have hleftPos : ∀ᵐ paths ∂μ, ∀ k : ℕ, 0 < interarrival k paths.1 := by
    have hmap : ∀ᵐ gaps ∂Measure.map Prod.fst μ,
        ∀ k : ℕ, 0 < interarrival k gaps := by
      rw [hfst.map_eq]
      exact ae_all_interarrival_positive hleft
    exact Measure.tendsto_ae_map hfst.aemeasurable hmap
  have hrightPos : ∀ᵐ paths ∂μ, ∀ k : ℕ, 0 < interarrival k paths.2 := by
    have hmap : ∀ᵐ gaps ∂Measure.map Prod.snd μ,
        ∀ k : ℕ, 0 < interarrival k gaps := by
      rw [hsnd.map_eq]
      exact ae_all_interarrival_positive hright
    exact Measure.tendsto_ae_map hsnd.aemeasurable hmap
  have hleftShift : Measurable (futureInterarrival (n + 1)) :=
    measurable_pi_iff.2 fun k => measurable_futureInterarrival (n + 1) k
  have hrightShift : Measurable (futureInterarrival n) :=
    measurable_pi_iff.2 fun k => measurable_futureInterarrival n k
  have hshiftMeas : Measurable shift := by
    exact (hleftShift.comp measurable_fst).prodMk (hrightShift.comp measurable_snd)
  have hshiftLaw : HasLaw shift μ μ := by
    refine ⟨hshiftMeas.aemeasurable, ?_⟩
    change Measure.map
      (Prod.map (futureInterarrival (n + 1)) (futureInterarrival n))
      (leftLaw.prod rightLaw) = leftLaw.prod rightLaw
    rw [← Measure.map_prod_map _ _ hleftShift hrightShift,
      (futureInterarrival_hasLaw_path hleft (n + 1)).map_eq,
      (futureInterarrival_hasLaw_path hright n).map_eq]
  have hglobal : ∀ᵐ paths ∂μ, Tendsto (fun k : ℕ => arrivalTime k
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths))) atTop atTop := by
    simpa [μ, leftLaw, rightLaw] using
      TwoStateSwitching.ae_tendsto_arrivalTime_alternatingGaps_prod
        0 leftRate rightRate hleft hright
  have htail : ∀ᵐ paths ∂μ, Tendsto (fun k : ℕ => arrivalTime k
      (TwoStateSwitching.alternatingGaps 1
        (TwoStateSwitching.twoStateGapsOfPair (shift paths)))) atTop atTop := by
    have hmap : ∀ᵐ tails ∂Measure.map shift μ, Tendsto (fun k : ℕ => arrivalTime k
        (TwoStateSwitching.alternatingGaps 1
          (TwoStateSwitching.twoStateGapsOfPair tails))) atTop atTop := by
      rw [hshiftLaw.map_eq]
      simpa [μ, leftLaw, rightLaw] using
        TwoStateSwitching.ae_tendsto_arrivalTime_alternatingGaps_prod
          1 leftRate rightRate hleft hright
    exact Measure.tendsto_ae_map hshiftLaw.aemeasurable hmap
  have hactiveTailLaw : HasLaw
      (fun paths : (ℕ → ℝ) × (ℕ → ℝ) => futureInterarrival n paths.2)
      rightLaw μ := by
    simpa [Function.comp_def] using
      (futureInterarrival_hasLaw_path hright n).fun_comp hsnd
  have hactiveTail : ∀ᵐ paths ∂μ, Tendsto (fun k : ℕ => arrivalTime k
      (futureInterarrival n paths.2)) atTop atTop := by
    have hmap : ∀ᵐ gaps ∂Measure.map
        (fun paths : (ℕ → ℝ) × (ℕ → ℝ) => futureInterarrival n paths.2) μ,
        Tendsto (fun k : ℕ => arrivalTime k gaps) atTop atTop := by
      rw [hactiveTailLaw.map_eq]
      simpa [rightLaw] using ae_arrivalTime_tendsto_atTop hright
    exact Measure.tendsto_ae_map hactiveTailLaw.aemeasurable hmap
  change ∀ᵐ paths ∂μ, ∀ t : ℝ, 0 ≤ t →
    (canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1 ↔
      (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t ∧
        canonicalRenewalCount
          (alternatingAsymmetricPrefixElapsed t n (n + 1)
            (prefixInterarrival n paths.2,
              prefixInterarrival (n + 1) paths.1))
          (futureInterarrival n paths.2) = 0))
  refine (hglobal.and (hleftPos.and (hrightPos.and (htail.and hactiveTail)))).mono ?_
  intro paths hregular
  rcases hregular with ⟨hglobal, hleftPos, hrightPos, htail, hactiveTail⟩
  intro t ht
  apply canonicalRenewalCount_odd_iff_prefix_activeZero paths t n
    ((hglobal.eventually_gt_atTop t).exists)
  · intro k
    rcases k.even_or_odd' with ⟨m, rfl | rfl⟩
    · change 0 < TwoStateSwitching.alternatingGap 0
        (TwoStateSwitching.twoStateGapsOfPair paths) (2 * m)
      rw [TwoStateSwitching.alternatingGap_two_mul]
      simpa [interarrival] using hleftPos m
    · change 0 < TwoStateSwitching.alternatingGap 0
        (TwoStateSwitching.twoStateGapsOfPair paths) (2 * m + 1)
      rw [TwoStateSwitching.alternatingGap_two_mul_add_one]
      simpa [interarrival] using hrightPos m
  · simpa [shift] using htail
  · exact hactiveTail

/-- The measurable exposed-history event representing an even alternating
count fiber.  The first component retains both consumed prefixes; the second
component's natural coordinate is the active shifted renewal count. -/
def evenPrefixActiveZeroHistoryEvent (t : ℝ) (n : ℕ) :
    Set (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) :=
  {history |
    (∑ i, history.1.1 i) + ∑ i, history.1.2 i ≤ t ∧ history.2.1 = 0}

/-- The even exposed-history fiber event is Borel measurable. -/
theorem measurableSet_evenPrefixActiveZeroHistoryEvent (t : ℝ) (n : ℕ) :
    MeasurableSet (evenPrefixActiveZeroHistoryEvent t n) := by
  have hleft : Measurable
      (fun history : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ)) =>
        ∑ i, history.1.1 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  have hright : Measurable
      (fun history : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ)) =>
        ∑ i, history.1.2 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hcount : Measurable
      (fun history : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ)) =>
        history.2.1) :=
    measurable_fst.comp measurable_snd
  exact (measurableSet_le (hleft.add hright) measurable_const).inter
    (hcount (measurableSet_singleton 0))

/-- The asymmetric exposed-history event representing an odd alternating
count fiber.  Its prefix order is current active state first, then inactive. -/
def asymmetricPrefixActiveZeroHistoryEvent (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    Set (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
      (ℕ × (ℕ → ℝ))) :=
  {history |
    (∑ i, history.1.1 i) + ∑ i, history.1.2 i ≤ t ∧ history.2.1 = 0}

/-- The asymmetric exposed-history fiber event is Borel measurable. -/
theorem measurableSet_asymmetricPrefixActiveZeroHistoryEvent (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    MeasurableSet
      (asymmetricPrefixActiveZeroHistoryEvent t activeCount inactiveCount) := by
  have hactive : Measurable
      (fun history : ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ)) => ∑ i, history.1.1 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  have hinactive : Measurable
      (fun history : ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ)) => ∑ i, history.1.2 i) := by
    exact Finset.univ.measurable_fun_sum fun i _ =>
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hcount : Measurable
      (fun history : ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ)) => history.2.1) :=
    measurable_fst.comp measurable_snd
  exact (measurableSet_le (hactive.add hinactive) measurable_const).inter
    (hcount (measurableSet_singleton 0))

/-- The future pair produced by the even prefix/residual factor retains the
original two-stream exponential product law. -/
theorem map_snd_alternatingEvenPrefixResidualFactor
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (t : ℝ) (n : ℕ) :
    Measure.map (fun paths : (ℕ → ℝ) × (ℕ → ℝ) =>
      (alternatingEvenPrefixResidualFactor t n paths).2)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) =
      (exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate) := by
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.map (prefixInterarrival n) activeLaw).prod
      (Measure.map (prefixInterarrival n) inactiveLaw)
  let elapsed : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    alternatingEvenPrefixElapsed t n
  let history : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ) →
      ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ)) :=
    externalTimePastHistory elapsed
  let historyLaw : Measure
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) :=
    Measure.map history (prefixLaw.prod activeLaw)
  let factor : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
    alternatingEvenPrefixResidualFactor t n
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival n) activeLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (prefixInterarrival n) inactiveLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingEvenPrefixElapsed t n)).aemeasurable
  have hfactor : Measure.map factor μ = historyLaw.prod μ := by
    simpa [factor, μ, historyLaw, history, prefixLaw, activeLaw, inactiveLaw,
      elapsed] using
      map_alternatingEvenPrefixResidualFactor hactive hinactive t n
  calc
    Measure.map (fun paths : (ℕ → ℝ) × (ℕ → ℝ) =>
        (alternatingEvenPrefixResidualFactor t n paths).2) (activeLaw.prod inactiveLaw) =
        Measure.map (Prod.snd ∘ factor) μ := by rfl
    _ = Measure.map Prod.snd (Measure.map factor μ) := by
      exact (Measure.map_map measurable_snd
        (measurable_alternatingEvenPrefixResidualFactor t n)).symm
    _ = Measure.map Prod.snd (historyLaw.prod μ) := by rw [hfactor]
    _ = μ := by
      rw [Measure.map_snd_prod]
      simp
    _ = activeLaw.prod inactiveLaw := rfl

/-- The even factor's first coordinate belongs to its exposed-history event
exactly when the consumed prefixes fit before the clock and the active
shifted stream has zero residual count. -/
theorem mem_evenPrefixActiveZeroHistoryEvent_factor_fst_iff
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ) :
    (alternatingEvenPrefixResidualFactor t n paths).1 ∈
      evenPrefixActiveZeroHistoryEvent t n ↔
      ((∑ i, prefixInterarrival n paths.1 i) +
        ∑ i, prefixInterarrival n paths.2 i ≤ t ∧
        canonicalRenewalCount
          (alternatingEvenPrefixElapsed t n
            (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
          (futureInterarrival n paths.1) = 0) := by
  rfl

/-- The even factor's future coordinate is the literal active residual paired
with the untouched inactive stream. -/
theorem alternatingEvenPrefixResidualFactor_snd_eq
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ) :
    (alternatingEvenPrefixResidualFactor t n paths).2 =
      (externalTimeResidualTail (alternatingEvenPrefixElapsed t n)
        ((prefixInterarrival n paths.1, prefixInterarrival n paths.2),
          futureInterarrival n paths.1), futureInterarrival n paths.2) := by
  rfl

/-- The future pair produced by the asymmetric active-first factor has its
native active-first exponential product law. -/
theorem map_snd_alternatingAsymmetricPrefixResidualFactor
    {activeRate inactiveRate : ℝ}
    (hactive : 0 < activeRate) (hinactive : 0 < inactiveRate)
    (t : ℝ) (activeCount inactiveCount : ℕ) :
    Measure.map (fun paths : (ℕ → ℝ) × (ℕ → ℝ) =>
      (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount paths).2)
      ((exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate)) =
      (exponentialInterarrivalMeasure activeRate).prod
        (exponentialInterarrivalMeasure inactiveRate) := by
  let activeLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure activeRate
  let inactiveLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure inactiveRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := activeLaw.prod inactiveLaw
  let prefixLaw : Measure
      ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) :=
    (Measure.map (prefixInterarrival activeCount) activeLaw).prod
      (Measure.map (prefixInterarrival inactiveCount) inactiveLaw)
  let elapsed : (Fin activeCount → ℝ) × (Fin inactiveCount → ℝ) → ℝ :=
    alternatingAsymmetricPrefixElapsed t activeCount inactiveCount
  let history : ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
      (ℕ → ℝ) →
      ((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ)) :=
    externalTimePastHistory elapsed
  let historyLaw : Measure
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ))) :=
    Measure.map history (prefixLaw.prod activeLaw)
  let factor : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin activeCount → ℝ) × (Fin inactiveCount → ℝ)) ×
        (ℕ × (ℕ → ℝ))) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
    alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount
  letI : IsProbabilityMeasure activeLaw := by
    simpa [activeLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hactive
  letI : IsProbabilityMeasure inactiveLaw := by
    simpa [inactiveLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hinactive
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival activeCount) activeLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival activeCount).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival inactiveCount) inactiveLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival inactiveCount).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingAsymmetricPrefixElapsed t activeCount inactiveCount)).aemeasurable
  have hfactor : Measure.map factor μ = historyLaw.prod μ := by
    simpa [factor, μ, historyLaw, history, prefixLaw, activeLaw, inactiveLaw,
      elapsed] using
      map_alternatingAsymmetricPrefixResidualFactor hactive hinactive t activeCount inactiveCount
  calc
    Measure.map (fun paths : (ℕ → ℝ) × (ℕ → ℝ) =>
        (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount paths).2)
        (activeLaw.prod inactiveLaw) = Measure.map (Prod.snd ∘ factor) μ := by rfl
    _ = Measure.map Prod.snd (Measure.map factor μ) := by
      exact (Measure.map_map measurable_snd
        (measurable_alternatingAsymmetricPrefixResidualFactor
          t activeCount inactiveCount)).symm
    _ = Measure.map Prod.snd (historyLaw.prod μ) := by rw [hfactor]
    _ = μ := by
      rw [Measure.map_snd_prod]
      simp
    _ = activeLaw.prod inactiveLaw := rfl

/-- The asymmetric factor's first coordinate belongs to its exposed-history
event exactly when its active-first prefixes fit before the clock and the
active shifted stream has zero residual count. -/
theorem mem_asymmetricPrefixActiveZeroHistoryEvent_factor_fst_iff
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount paths).1 ∈
      asymmetricPrefixActiveZeroHistoryEvent t activeCount inactiveCount ↔
      ((∑ i, prefixInterarrival activeCount paths.1 i) +
        ∑ i, prefixInterarrival inactiveCount paths.2 i ≤ t ∧
        canonicalRenewalCount
          (alternatingAsymmetricPrefixElapsed t activeCount inactiveCount
            (prefixInterarrival activeCount paths.1,
              prefixInterarrival inactiveCount paths.2))
          (futureInterarrival activeCount paths.1) = 0) := by
  rfl

/-- The asymmetric factor's second coordinate is the literal active residual
paired with the untouched inactive stream. -/
theorem alternatingAsymmetricPrefixResidualFactor_snd_eq
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ)
    (activeCount inactiveCount : ℕ) :
    (alternatingAsymmetricPrefixResidualFactor t activeCount inactiveCount paths).2 =
      (externalTimeResidualTail
        (alternatingAsymmetricPrefixElapsed t activeCount inactiveCount)
        ((prefixInterarrival activeCount paths.1,
          prefixInterarrival inactiveCount paths.2),
          futureInterarrival activeCount paths.1),
        futureInterarrival inactiveCount paths.2) := by
  rfl

/-- Each exact even alternating-count fiber factors from the complete
state-indexed future holding streams.  This is a source-level statement about
the two visit-local exponential sequences: the inactive stream is untouched,
and only the currently active stream is residualized. -/
theorem measure_evenAlternatingCountFutureFiber_factor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (B : Set (Fin 2 → ℕ → ℝ)) (hB : MeasurableSet B) :
    let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)
    let count : (ℕ → ℝ) × (ℕ → ℝ) → ℕ := fun paths =>
      canonicalRenewalCount t
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair paths))
    let future : (ℕ → ℝ) × (ℕ → ℝ) → Fin 2 → ℕ → ℝ := fun paths =>
      TwoStateSwitching.switchGapsAfterElapsed 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t
    μ (count ⁻¹' {2 * n} ∩ future ⁻¹' B) =
      μ (count ⁻¹' {2 * n}) * μ (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  dsimp
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure leftRate).prod
      (exponentialInterarrivalMeasure rightRate)
  let count : (ℕ → ℝ) × (ℕ → ℝ) → ℕ := fun paths =>
    canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths))
  let future : (ℕ → ℝ) × (ℕ → ℝ) → Fin 2 → ℕ → ℝ := fun paths =>
    TwoStateSwitching.switchGapsAfterElapsed 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t
  let F : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ × (ℕ → ℝ))) := fun paths =>
    (alternatingEvenPrefixResidualFactor t n paths).1
  let G : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) := fun paths =>
    (alternatingEvenPrefixResidualFactor t n paths).2
  let A := evenPrefixActiveZeroHistoryEvent t n
  let C : Set ((ℕ → ℝ) × (ℕ → ℝ)) := count ⁻¹' {2 * n}
  let D : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    TwoStateSwitching.twoStateGapsOfPair ⁻¹' B
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hF : Measurable F := by
    exact measurable_fst.comp (measurable_alternatingEvenPrefixResidualFactor t n)
  have hG : Measurable G := by
    exact measurable_snd.comp (measurable_alternatingEvenPrefixResidualFactor t n)
  have hA : MeasurableSet A := measurableSet_evenPrefixActiveZeroHistoryEvent t n
  have hD : MeasurableSet D := hB.preimage TwoStateSwitching.measurable_twoStateGapsOfPair
  have hindep : ProbabilityTheory.IndepFun F G μ := by
    simpa [F, G, μ] using
      indepFun_alternatingEvenPrefixResidualFactor hleft hright t n
  have hCF : C =ᵐ[μ] F ⁻¹' A := by
    filter_upwards [ae_forall_canonicalRenewalCount_even_iff_prefix_activeZero
      hleft hright n] with paths hpaths
    apply propext
    change count paths = 2 * n ↔ F paths ∈ A
    rw [mem_evenPrefixActiveZeroHistoryEvent_factor_fst_iff]
    rw [show (∑ i, prefixInterarrival n paths.1 i) +
        ∑ i, prefixInterarrival n paths.2 i =
        arrivalPrefix n paths.1 + arrivalPrefix n paths.2 by
      simp [prefixInterarrival, arrivalPrefix, interarrival,
        Fin.sum_univ_eq_sum_range]]
    simpa [count] using hpaths t ht
  have hpiece : Set.inter C (future ⁻¹' B) =ᵐ[μ]
      Set.inter (F ⁻¹' A) ((TwoStateSwitching.twoStateGapsOfPair ∘ G) ⁻¹' B) := by
    filter_upwards [ae_forall_canonicalRenewalCount_even_iff_prefix_activeZero
      hleft hright n] with paths hpaths
    apply propext
    have hcount : count paths = 2 * n ↔ F paths ∈ A := by
      rw [mem_evenPrefixActiveZeroHistoryEvent_factor_fst_iff]
      rw [show (∑ i, prefixInterarrival n paths.1 i) +
          ∑ i, prefixInterarrival n paths.2 i =
          arrivalPrefix n paths.1 + arrivalPrefix n paths.2 by
        simp [prefixInterarrival, arrivalPrefix, interarrival,
          Fin.sum_univ_eq_sum_range]]
      simpa [count] using hpaths t ht
    constructor
    · rintro ⟨hC, hfuture⟩
      refine ⟨hcount.mp hC, ?_⟩
      have hhistory :
          (∑ i, prefixInterarrival n paths.1 i) +
            ∑ i, prefixInterarrival n paths.2 i ≤ t ∧
          canonicalRenewalCount
            (alternatingEvenPrefixElapsed t n
              (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
            (futureInterarrival n paths.1) = 0 := by
        rw [← mem_evenPrefixActiveZeroHistoryEvent_factor_fst_iff]
        exact hcount.mp hC
      have hfutureEq : future paths =
          TwoStateSwitching.twoStateGapsOfPair (G paths) := by
        simpa [future, G, alternatingEvenPrefixResidualFactor_snd_eq] using
          switchGapsAfterElapsed_evenFiber_eq_residualActive_companion paths t n hC
            hhistory.1 hhistory.2
      simpa [hfutureEq] using hfuture
    · rintro ⟨hApaths, hfuture⟩
      have hC : count paths = 2 * n := hcount.mpr hApaths
      refine ⟨hC, ?_⟩
      have hhistory :
          (∑ i, prefixInterarrival n paths.1 i) +
            ∑ i, prefixInterarrival n paths.2 i ≤ t ∧
          canonicalRenewalCount
            (alternatingEvenPrefixElapsed t n
              (prefixInterarrival n paths.1, prefixInterarrival n paths.2))
            (futureInterarrival n paths.1) = 0 := by
        rw [← mem_evenPrefixActiveZeroHistoryEvent_factor_fst_iff]
        exact hApaths
      have hfutureEq : future paths =
          TwoStateSwitching.twoStateGapsOfPair (G paths) := by
        simpa [future, G, alternatingEvenPrefixResidualFactor_snd_eq] using
          switchGapsAfterElapsed_evenFiber_eq_residualActive_companion paths t n hC
            hhistory.1 hhistory.2
      simpa [hfutureEq] using hfuture
  have hGmeasure : μ (G ⁻¹' D) = μ D := by
    calc
      μ (G ⁻¹' D) = (Measure.map G μ) D :=
        (Measure.map_apply hG hD).symm
      _ = μ D := by
        rw [show Measure.map G μ = μ by
          simpa [G, μ] using
            map_snd_alternatingEvenPrefixResidualFactor hleft hright t n]
  have hCmeasure : μ C = μ (F ⁻¹' A) :=
    MeasureTheory.measure_congr hCF
  calc
    μ (Set.inter (count ⁻¹' {2 * n}) (future ⁻¹' B)) =
        μ (Set.inter C (future ⁻¹' B)) := by rfl
    _ = μ (Set.inter (F ⁻¹' A)
        ((TwoStateSwitching.twoStateGapsOfPair ∘ G) ⁻¹' B)) :=
      MeasureTheory.measure_congr hpiece
    _ = μ (Set.inter (F ⁻¹' A) (G ⁻¹' D)) := by rfl
    _ = μ (F ⁻¹' A) * μ (G ⁻¹' D) := by
      exact (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mp
        hindep A D hA hD)
    _ = μ C * μ D := by rw [hGmeasure, hCmeasure]
    _ = μ (count ⁻¹' {2 * n}) * μ
        (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by rfl

/-- The odd-fiber factor is written in the source's fixed state-zero/state-one
coordinate order.  Internally, the current state-one stream is placed first
to apply the active-stream residual theorem; the returned future pair is then
swapped back to state-indexed order. -/
def alternatingOddPrefixResidualFactor (t : ℝ) (n : ℕ) :
    (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun paths =>
    ((alternatingAsymmetricPrefixResidualFactor t n (n + 1)
      (Prod.swap paths)).1,
      Prod.swap (alternatingAsymmetricPrefixResidualFactor t n (n + 1)
        (Prod.swap paths)).2)

/-- Measurability of the odd-fiber source-order factor. -/
theorem measurable_alternatingOddPrefixResidualFactor (t : ℝ) (n : ℕ) :
    Measurable (alternatingOddPrefixResidualFactor t n) := by
  exact
    ((measurable_fst.comp
      (measurable_alternatingAsymmetricPrefixResidualFactor t n (n + 1))).comp
        measurable_swap).prodMk
      ((measurable_swap.comp (measurable_snd.comp
        (measurable_alternatingAsymmetricPrefixResidualFactor t n (n + 1)))).comp
          measurable_swap)

/-- Under a state-zero/state-one exponential product source law, the odd
factor exposes the active-first history and leaves a fresh future pair in the
original state-coordinate order. -/
theorem map_alternatingOddPrefixResidualFactor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (n : ℕ) :
    Measure.map (alternatingOddPrefixResidualFactor t n)
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) =
      (Measure.map
        (externalTimePastHistory (alternatingAsymmetricPrefixElapsed t n (n + 1)))
        (((Measure.map (prefixInterarrival n)
          (exponentialInterarrivalMeasure rightRate)).prod
            (Measure.map (prefixInterarrival (n + 1))
              (exponentialInterarrivalMeasure leftRate))).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) := by
  let leftLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := leftLaw.prod rightLaw
  let activeLaw : Measure (ℕ → ℝ) := rightLaw
  let inactiveLaw : Measure (ℕ → ℝ) := leftLaw
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) :=
    (Measure.map (prefixInterarrival n) activeLaw).prod
      (Measure.map (prefixInterarrival (n + 1)) inactiveLaw)
  let elapsed : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ :=
    alternatingAsymmetricPrefixElapsed t n (n + 1)
  let history : ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ → ℝ) →
      ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ)) :=
    externalTimePastHistory elapsed
  let historyLaw : Measure
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) :=
    Measure.map history (prefixLaw.prod activeLaw)
  let oldFactor := alternatingAsymmetricPrefixResidualFactor t n (n + 1)
  let outputSwap :
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) →
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) ×
        ((ℕ → ℝ) × (ℕ → ℝ)) :=
    Prod.map id Prod.swap
  letI : IsProbabilityMeasure leftLaw := by
    simpa [leftLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightLaw := by
    simpa [rightLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) activeLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival (n + 1)) inactiveLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival (n + 1)).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingAsymmetricPrefixElapsed t n (n + 1))).aemeasurable
  have hswap : Measure.map Prod.swap μ = activeLaw.prod inactiveLaw := by
    simpa [μ, activeLaw, inactiveLaw] using
      (Measure.prod_swap : Measure.map Prod.swap (leftLaw.prod rightLaw) =
        rightLaw.prod leftLaw)
  have hold : Measure.map oldFactor (activeLaw.prod inactiveLaw) =
      historyLaw.prod (activeLaw.prod inactiveLaw) := by
    simpa [oldFactor, historyLaw, history, prefixLaw, activeLaw, inactiveLaw,
      elapsed] using
      map_alternatingAsymmetricPrefixResidualFactor hright hleft t n (n + 1)
  have hout : Measure.map outputSwap
      (historyLaw.prod (activeLaw.prod inactiveLaw)) = historyLaw.prod μ := by
    change Measure.map (Prod.map id Prod.swap)
        (historyLaw.prod (activeLaw.prod inactiveLaw)) = historyLaw.prod μ
    rw [← Measure.map_prod_map _ _ measurable_id measurable_swap,
      Measure.map_id, Measure.prod_swap]
  calc
    Measure.map (alternatingOddPrefixResidualFactor t n) (leftLaw.prod rightLaw) =
        Measure.map outputSwap
          (Measure.map oldFactor (Measure.map Prod.swap μ)) := by
          change Measure.map ((outputSwap ∘ oldFactor) ∘ Prod.swap) μ = _
          rw [← Measure.map_map
            ((measurable_id.prodMap measurable_swap).comp
              (measurable_alternatingAsymmetricPrefixResidualFactor t n (n + 1)))
            measurable_swap,
            ← Measure.map_map (measurable_id.prodMap measurable_swap)
              (measurable_alternatingAsymmetricPrefixResidualFactor t n (n + 1))]
    _ = Measure.map outputSwap (Measure.map oldFactor
        (activeLaw.prod inactiveLaw)) := by rw [hswap]
    _ = Measure.map outputSwap
        (historyLaw.prod (activeLaw.prod inactiveLaw)) := by rw [hold]
    _ = historyLaw.prod μ := hout
    _ = (Measure.map
        (externalTimePastHistory (alternatingAsymmetricPrefixElapsed t n (n + 1)))
        (((Measure.map (prefixInterarrival n)
          (exponentialInterarrivalMeasure rightRate)).prod
            (Measure.map (prefixInterarrival (n + 1))
              (exponentialInterarrivalMeasure leftRate))).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) := by
      rfl

/-- The source-order future coordinate of the odd factor has the original
state-zero/state-one exponential product law. -/
theorem map_snd_alternatingOddPrefixResidualFactor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (n : ℕ) :
    Measure.map (fun paths : (ℕ → ℝ) × (ℕ → ℝ) =>
      (alternatingOddPrefixResidualFactor t n paths).2)
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) =
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate) := by
  let leftLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := leftLaw.prod rightLaw
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) :=
    (Measure.map (prefixInterarrival n) rightLaw).prod
      (Measure.map (prefixInterarrival (n + 1)) leftLaw)
  let elapsed : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ :=
    alternatingAsymmetricPrefixElapsed t n (n + 1)
  let historyLaw : Measure
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) :=
    Measure.map (externalTimePastHistory elapsed) (prefixLaw.prod rightLaw)
  letI : IsProbabilityMeasure leftLaw := by
    simpa [leftLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightLaw := by
    simpa [rightLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) rightLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival (n + 1)) leftLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival (n + 1)).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingAsymmetricPrefixElapsed t n (n + 1))).aemeasurable
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfactor : Measure.map (alternatingOddPrefixResidualFactor t n) μ =
      historyLaw.prod μ := by
    simpa [μ, historyLaw, elapsed, prefixLaw, leftLaw, rightLaw] using
      map_alternatingOddPrefixResidualFactor hleft hright t n
  calc
    Measure.map (fun paths : (ℕ → ℝ) × (ℕ → ℝ) =>
        (alternatingOddPrefixResidualFactor t n paths).2) μ =
        Measure.map Prod.snd (Measure.map (alternatingOddPrefixResidualFactor t n) μ) := by
          exact (Measure.map_map measurable_snd
            (measurable_alternatingOddPrefixResidualFactor t n)).symm
    _ = Measure.map Prod.snd (historyLaw.prod μ) := by rw [hfactor]
    _ = μ := by
      rw [Measure.map_snd_prod]
      simp
    _ = leftLaw.prod rightLaw := rfl

/-- The exposed odd-fiber history is independent of the source-order future
pair.  This transports the active-first factor through the two coordinate
swaps explicitly, rather than asserting a continuous-time strong-Markov
property. -/
theorem indepFun_alternatingOddPrefixResidualFactor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun paths => (alternatingOddPrefixResidualFactor t n paths).1)
      (fun paths => (alternatingOddPrefixResidualFactor t n paths).2)
      ((exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)) := by
  let leftLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightLaw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := leftLaw.prod rightLaw
  let prefixLaw : Measure ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) :=
    (Measure.map (prefixInterarrival n) rightLaw).prod
      (Measure.map (prefixInterarrival (n + 1)) leftLaw)
  let elapsed : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ :=
    alternatingAsymmetricPrefixElapsed t n (n + 1)
  let historyLaw : Measure
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) :=
    Measure.map (externalTimePastHistory elapsed) (prefixLaw.prod rightLaw)
  let factor := alternatingOddPrefixResidualFactor t n
  let F := fun paths : (ℕ → ℝ) × (ℕ → ℝ) => (factor paths).1
  let G := fun paths : (ℕ → ℝ) × (ℕ → ℝ) => (factor paths).2
  letI : IsProbabilityMeasure leftLaw := by
    simpa [leftLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightLaw := by
    simpa [rightLaw] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival n) rightLaw) :=
    Measure.isProbabilityMeasure_map (measurable_prefixInterarrival n).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (prefixInterarrival (n + 1)) leftLaw) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefixInterarrival (n + 1)).aemeasurable
  letI : IsProbabilityMeasure prefixLaw := by
    dsimp [prefixLaw]
    infer_instance
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory elapsed
        (measurable_alternatingAsymmetricPrefixElapsed t n (n + 1))).aemeasurable
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfactor : Measure.map factor μ = historyLaw.prod μ := by
    simpa [factor, μ, historyLaw, elapsed, prefixLaw, leftLaw, rightLaw] using
      map_alternatingOddPrefixResidualFactor hleft hright t n
  have hF : Measurable F := by
    exact measurable_fst.comp (measurable_alternatingOddPrefixResidualFactor t n)
  have hG : Measurable G := by
    exact measurable_snd.comp (measurable_alternatingOddPrefixResidualFactor t n)
  have hmapF : Measure.map F μ = historyLaw := by
    calc
      Measure.map F μ = Measure.map (Prod.fst ∘ factor) μ := by rfl
      _ = Measure.map Prod.fst (Measure.map factor μ) := by
        exact (Measure.map_map measurable_fst
          (measurable_alternatingOddPrefixResidualFactor t n)).symm
      _ = Measure.map Prod.fst (historyLaw.prod μ) := by rw [hfactor]
      _ = historyLaw := by
        rw [Measure.map_fst_prod]
        simp
  have hmapG : Measure.map G μ = μ := by
    calc
      Measure.map G μ = Measure.map (Prod.snd ∘ factor) μ := by rfl
      _ = Measure.map Prod.snd (Measure.map factor μ) := by
        exact (Measure.map_map measurable_snd
          (measurable_alternatingOddPrefixResidualFactor t n)).symm
      _ = Measure.map Prod.snd (historyLaw.prod μ) := by rw [hfactor]
      _ = μ := by
        rw [Measure.map_snd_prod]
        simp
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hF.aemeasurable hG.aemeasurable]
  change Measure.map factor μ = (Measure.map F μ).prod (Measure.map G μ)
  rw [hfactor, hmapF, hmapG]

/-- The odd source-order factor exposes exactly the active-first count-fiber
history condition. -/
theorem mem_asymmetricPrefixActiveZeroHistoryEvent_oddFactor_fst_iff
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ) :
    (alternatingOddPrefixResidualFactor t n paths).1 ∈
      asymmetricPrefixActiveZeroHistoryEvent t n (n + 1) ↔
      ((∑ i, prefixInterarrival n paths.2 i) +
        ∑ i, prefixInterarrival (n + 1) paths.1 i ≤ t ∧
        canonicalRenewalCount
          (alternatingAsymmetricPrefixElapsed t n (n + 1)
            (prefixInterarrival n paths.2,
              prefixInterarrival (n + 1) paths.1))
          (futureInterarrival n paths.2) = 0) := by
  rfl

/-- The odd source-order factor's future coordinate is the state-indexed
future pair in the same order as the original input streams. -/
theorem alternatingOddPrefixResidualFactor_snd_eq
    (paths : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) (n : ℕ) :
    (alternatingOddPrefixResidualFactor t n paths).2 =
      Prod.swap (alternatingAsymmetricPrefixResidualFactor t n (n + 1)
        (Prod.swap paths)).2 := by
  rfl

/-- Each exact odd alternating-count fiber factors from the complete literal
state-indexed future holding streams.  The proof uses the active-first
fixed-prefix residual factor only after explicitly swapping back to the
source state-coordinate order. -/
theorem measure_oddAlternatingCountFutureFiber_factor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (B : Set (Fin 2 → ℕ → ℝ)) (hB : MeasurableSet B) :
    let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)
    let count : (ℕ → ℝ) × (ℕ → ℝ) → ℕ := fun paths =>
      canonicalRenewalCount t
        (TwoStateSwitching.alternatingGaps 0
          (TwoStateSwitching.twoStateGapsOfPair paths))
    let future : (ℕ → ℝ) × (ℕ → ℝ) → Fin 2 → ℕ → ℝ := fun paths =>
      TwoStateSwitching.switchGapsAfterElapsed 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t
    μ (count ⁻¹' {2 * n + 1} ∩ future ⁻¹' B) =
      μ (count ⁻¹' {2 * n + 1}) *
        μ (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  dsimp
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure leftRate).prod
      (exponentialInterarrivalMeasure rightRate)
  let count : (ℕ → ℝ) × (ℕ → ℝ) → ℕ := fun paths =>
    canonicalRenewalCount t
      (TwoStateSwitching.alternatingGaps 0
        (TwoStateSwitching.twoStateGapsOfPair paths))
  let future : (ℕ → ℝ) × (ℕ → ℝ) → Fin 2 → ℕ → ℝ := fun paths =>
    TwoStateSwitching.switchGapsAfterElapsed 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t
  let F : (ℕ → ℝ) × (ℕ → ℝ) →
      (((Fin n → ℝ) × (Fin (n + 1) → ℝ)) × (ℕ × (ℕ → ℝ))) := fun paths =>
    (alternatingOddPrefixResidualFactor t n paths).1
  let G : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) := fun paths =>
    (alternatingOddPrefixResidualFactor t n paths).2
  let A := asymmetricPrefixActiveZeroHistoryEvent t n (n + 1)
  let C : Set ((ℕ → ℝ) × (ℕ → ℝ)) := count ⁻¹' {2 * n + 1}
  let D : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    TwoStateSwitching.twoStateGapsOfPair ⁻¹' B
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hF : Measurable F := by
    exact measurable_fst.comp (measurable_alternatingOddPrefixResidualFactor t n)
  have hG : Measurable G := by
    exact measurable_snd.comp (measurable_alternatingOddPrefixResidualFactor t n)
  have hA : MeasurableSet A :=
    measurableSet_asymmetricPrefixActiveZeroHistoryEvent t n (n + 1)
  have hD : MeasurableSet D := hB.preimage TwoStateSwitching.measurable_twoStateGapsOfPair
  have hindep : ProbabilityTheory.IndepFun F G μ := by
    simpa [F, G, μ] using
      indepFun_alternatingOddPrefixResidualFactor hleft hright t n
  have hcountEq : ∀ paths : (ℕ → ℝ) × (ℕ → ℝ),
      (arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t ∧
        canonicalRenewalCount
          (alternatingAsymmetricPrefixElapsed t n (n + 1)
            (prefixInterarrival n paths.2,
              prefixInterarrival (n + 1) paths.1))
          (futureInterarrival n paths.2) = 0) ↔ F paths ∈ A := by
    intro paths
    have hsum : (∑ i, prefixInterarrival n paths.2 i) +
        ∑ i, prefixInterarrival (n + 1) paths.1 i =
        arrivalPrefix n paths.2 + arrivalPrefix (n + 1) paths.1 := by
      simp [prefixInterarrival, arrivalPrefix, interarrival,
        Fin.sum_univ_eq_sum_range]
    rw [mem_asymmetricPrefixActiveZeroHistoryEvent_oddFactor_fst_iff]
    constructor
    · rintro ⟨hprefix, hzero⟩
      refine ⟨?_, hzero⟩
      calc
        (∑ i, prefixInterarrival n paths.2 i) +
            ∑ i, prefixInterarrival (n + 1) paths.1 i =
            arrivalPrefix n paths.2 + arrivalPrefix (n + 1) paths.1 := hsum
        _ = arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 := by ring
        _ ≤ t := hprefix
    · rintro ⟨hprefix, hzero⟩
      refine ⟨?_, hzero⟩
      calc
        arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 =
            arrivalPrefix n paths.2 + arrivalPrefix (n + 1) paths.1 := by ring
        _ = (∑ i, prefixInterarrival n paths.2 i) +
            ∑ i, prefixInterarrival (n + 1) paths.1 i := hsum.symm
        _ ≤ t := hprefix
  have hCF : C =ᵐ[μ] F ⁻¹' A := by
    filter_upwards [ae_forall_canonicalRenewalCount_odd_iff_prefix_activeZero
      hleft hright n] with paths hpaths
    apply propext
    change count paths = 2 * n + 1 ↔ F paths ∈ A
    rw [← hcountEq paths]
    simpa [count] using hpaths t ht
  have hpiece : Set.inter C (future ⁻¹' B) =ᵐ[μ]
      Set.inter (F ⁻¹' A) ((TwoStateSwitching.twoStateGapsOfPair ∘ G) ⁻¹' B) := by
    filter_upwards [ae_forall_canonicalRenewalCount_odd_iff_prefix_activeZero
      hleft hright n] with paths hpaths
    apply propext
    have hcount : count paths = 2 * n + 1 ↔ F paths ∈ A := by
      rw [← hcountEq paths]
      simpa [count] using hpaths t ht
    constructor
    · rintro ⟨hC, hfuture⟩
      refine ⟨hcount.mp hC, ?_⟩
      have hhistory :
          arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t ∧
          canonicalRenewalCount
            (alternatingAsymmetricPrefixElapsed t n (n + 1)
              (prefixInterarrival n paths.2,
                prefixInterarrival (n + 1) paths.1))
            (futureInterarrival n paths.2) = 0 :=
        (hcountEq paths).mpr (hcount.mp hC)
      have hfutureEq : future paths =
          TwoStateSwitching.twoStateGapsOfPair (G paths) := by
        simpa [future, G, alternatingOddPrefixResidualFactor_snd_eq] using
          switchGapsAfterElapsed_oddFiber_eq_companion_residualActive paths t n hC
            (by
              rw [show (∑ i, prefixInterarrival (n + 1) paths.1 i) +
                  ∑ i, prefixInterarrival n paths.2 i =
                  arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 by
                simp [prefixInterarrival, arrivalPrefix, interarrival,
                  Fin.sum_univ_eq_sum_range]]
              exact hhistory.1)
            hhistory.2
      simpa [hfutureEq] using hfuture
    · rintro ⟨hApaths, hfuture⟩
      have hC : count paths = 2 * n + 1 := hcount.mpr hApaths
      refine ⟨hC, ?_⟩
      have hhistory :
          arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 ≤ t ∧
          canonicalRenewalCount
            (alternatingAsymmetricPrefixElapsed t n (n + 1)
              (prefixInterarrival n paths.2,
                prefixInterarrival (n + 1) paths.1))
            (futureInterarrival n paths.2) = 0 :=
        (hcountEq paths).mpr hApaths
      have hfutureEq : future paths =
          TwoStateSwitching.twoStateGapsOfPair (G paths) := by
        simpa [future, G, alternatingOddPrefixResidualFactor_snd_eq] using
          switchGapsAfterElapsed_oddFiber_eq_companion_residualActive paths t n hC
            (by
              rw [show (∑ i, prefixInterarrival (n + 1) paths.1 i) +
                  ∑ i, prefixInterarrival n paths.2 i =
                  arrivalPrefix (n + 1) paths.1 + arrivalPrefix n paths.2 by
                simp [prefixInterarrival, arrivalPrefix, interarrival,
                  Fin.sum_univ_eq_sum_range]]
              exact hhistory.1)
            hhistory.2
      simpa [hfutureEq] using hfuture
  have hGmeasure : μ (G ⁻¹' D) = μ D := by
    calc
      μ (G ⁻¹' D) = (Measure.map G μ) D :=
        (Measure.map_apply hG hD).symm
      _ = μ D := by
        rw [show Measure.map G μ = μ by
          simpa [G, μ] using
            map_snd_alternatingOddPrefixResidualFactor hleft hright t n]
  have hCmeasure : μ C = μ (F ⁻¹' A) :=
    MeasureTheory.measure_congr hCF
  calc
    μ (Set.inter (count ⁻¹' {2 * n + 1}) (future ⁻¹' B)) =
        μ (Set.inter C (future ⁻¹' B)) := by rfl
    _ = μ (Set.inter (F ⁻¹' A)
        ((TwoStateSwitching.twoStateGapsOfPair ∘ G) ⁻¹' B)) :=
      MeasureTheory.measure_congr hpiece
    _ = μ (Set.inter (F ⁻¹' A) (G ⁻¹' D)) := by rfl
    _ = μ (F ⁻¹' A) * μ (G ⁻¹' D) := by
      exact (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mp
        hindep A D hA hD)
    _ = μ C * μ D := by rw [hGmeasure, hCmeasure]
    _ = μ (count ⁻¹' {2 * n + 1}) * μ
        (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by rfl

/-- The canonical alternating renewal count for source-order state-local
paths beginning in state zero. -/
def alternatingZeroStartCount (t : ℝ) :
    (ℕ → ℝ) × (ℕ → ℝ) → ℕ := fun paths =>
  canonicalRenewalCount t
    (TwoStateSwitching.alternatingGaps 0
      (TwoStateSwitching.twoStateGapsOfPair paths))

/-- The literal state-indexed future streams at a deterministic clock time
for source-order state-local paths beginning in state zero. -/
noncomputable def alternatingZeroStartFuture (t : ℝ) :
    (ℕ → ℝ) × (ℕ → ℝ) → Fin 2 → ℕ → ℝ := fun paths =>
  TwoStateSwitching.switchGapsAfterElapsed 0
    (TwoStateSwitching.twoStateGapsOfPair paths) t

/-- The literal state-indexed future streams at a deterministic clock time
for source-order state-local paths beginning in state one. -/
noncomputable def alternatingOneStartFuture (t : ℝ) :
    (ℕ → ℝ) × (ℕ → ℝ) → Fin 2 → ℕ → ℝ := fun paths =>
  TwoStateSwitching.switchGapsAfterElapsed 1
    (TwoStateSwitching.twoStateGapsOfPair paths) t

/-- Measurability of the source-order alternating count. -/
theorem measurable_alternatingZeroStartCount (t : ℝ) :
    Measurable (alternatingZeroStartCount t) := by
  exact (measurable_canonicalRenewalCount t).comp
    ((TwoStateSwitching.measurable_alternatingGaps 0).comp
      TwoStateSwitching.measurable_twoStateGapsOfPair)

/-- Measurability of the source-order alternating future pair. -/
theorem measurable_alternatingZeroStartFuture (t : ℝ) :
    Measurable (alternatingZeroStartFuture t) := by
  exact (TwoStateSwitching.measurable_switchGapsAfterElapsed 0).comp
    (TwoStateSwitching.measurable_twoStateGapsOfPair.prodMk measurable_const)

/-- Measurability of the source-order state-one alternating future pair. -/
theorem measurable_alternatingOneStartFuture (t : ℝ) :
    Measurable (alternatingOneStartFuture t) := by
  exact (TwoStateSwitching.measurable_switchGapsAfterElapsed 1).comp
    (TwoStateSwitching.measurable_twoStateGapsOfPair.prodMk measurable_const)

/-- Summing the exact even count fibers gives factorization of the event that
the deterministic-time endpoint remains in state zero and any measurable
literal state-indexed future event. -/
theorem measure_alternatingZeroStart_stateZero_future_factor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (Fin 2 → ℕ → ℝ)) (hB : MeasurableSet B) :
    let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)
    let stateZero : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
      {paths | TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = 0}
    μ (Set.inter stateZero (alternatingZeroStartFuture t ⁻¹' B)) =
      μ stateZero * μ (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  dsimp
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure leftRate).prod
      (exponentialInterarrivalMeasure rightRate)
  let count := alternatingZeroStartCount t
  let future := alternatingZeroStartFuture t
  let stateZero : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {paths | TwoStateSwitching.stateAt 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t = 0}
  let D : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    TwoStateSwitching.twoStateGapsOfPair ⁻¹' B
  let counts : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    fun n => count ⁻¹' {2 * n}
  let pieces : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    fun n => Set.inter (counts n) (future ⁻¹' B)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hcountMeas : Measurable count := by
    simpa [count] using measurable_alternatingZeroStartCount t
  have hfutureMeas : Measurable future := by
    simpa [future] using measurable_alternatingZeroStartFuture t
  have hcountsMeas : ∀ n : ℕ, MeasurableSet (counts n) := by
    intro n
    exact hcountMeas (measurableSet_singleton (2 * n))
  have hpiecesMeas : ∀ n : ℕ, MeasurableSet (pieces n) := by
    intro n
    exact (hcountsMeas n).inter (hfutureMeas hB)
  have hcountsDisjoint : Pairwise (Function.onFun Disjoint counts) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro paths hn hm
    change count paths = 2 * n at hn
    change count paths = 2 * m at hm
    apply hnm
    omega
  have hpiecesDisjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro paths hn hm
    exact (Set.disjoint_left.1 (hcountsDisjoint hnm)) hn.1 hm.1
  have hcountsUnion : (⋃ n : ℕ, counts n) = stateZero := by
    ext paths
    constructor
    · intro hpaths
      rcases Set.mem_iUnion.1 hpaths with ⟨n, hn⟩
      change count paths = 2 * n at hn
      change TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = 0
      unfold TwoStateSwitching.stateAt
      rw [show canonicalRenewalCount t
          (TwoStateSwitching.alternatingGaps 0
            (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n by
          simpa [count, alternatingZeroStartCount] using hn]
      exact TwoStateSwitching.stateAfterSwitches_even 0 ⟨n, by omega⟩
    · intro hpaths
      change TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = 0 at hpaths
      rcases (count paths).even_or_odd' with ⟨n, hn | hn⟩
      · exact Set.mem_iUnion.2 ⟨n, hn⟩
      · exfalso
        unfold TwoStateSwitching.stateAt at hpaths
        rw [show canonicalRenewalCount t
            (TwoStateSwitching.alternatingGaps 0
              (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1 by
            simpa [count, alternatingZeroStartCount] using hn,
          TwoStateSwitching.stateAfterSwitches_odd 0 ⟨n, by omega⟩] at hpaths
        exact TwoStateSwitching.otherState_ne 0 hpaths
  have hpiecesUnion : (⋃ n : ℕ, pieces n) =
      Set.inter stateZero (future ⁻¹' B) := by
    ext paths
    constructor
    · intro hpaths
      rcases Set.mem_iUnion.1 hpaths with ⟨n, hn⟩
      exact ⟨hcountsUnion ▸ Set.mem_iUnion.2 ⟨n, hn.1⟩, hn.2⟩
    · rintro ⟨hstate, hfuture⟩
      rw [← hcountsUnion] at hstate
      rcases Set.mem_iUnion.1 hstate with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨hn, hfuture⟩⟩
  calc
    μ (Set.inter stateZero (future ⁻¹' B)) = μ (⋃ n : ℕ, pieces n) := by
      rw [hpiecesUnion]
    _ = ∑' n : ℕ, μ (pieces n) :=
      measure_iUnion hpiecesDisjoint hpiecesMeas
    _ = ∑' n : ℕ, μ (counts n) * μ D := by
      apply tsum_congr
      intro n
      simpa [pieces, counts, count, future, D, μ,
        alternatingZeroStartCount, alternatingZeroStartFuture] using
        measure_evenAlternatingCountFutureFiber_factor hleft hright t ht n B hB
    _ = (∑' n : ℕ, μ (counts n)) * μ D := by
      exact ENNReal.tsum_mul_right
    _ = μ D * ∑' n : ℕ, μ (counts n) := by ac_rfl
    _ = μ D * μ (⋃ n : ℕ, counts n) := by
      rw [measure_iUnion hcountsDisjoint hcountsMeas]
    _ = μ D * μ stateZero := by rw [hcountsUnion]
    _ = μ stateZero * μ D := by ac_rfl

/-- Summing the exact odd count fibers gives factorization of the event that
the deterministic-time endpoint is in state one and any measurable literal
state-indexed future event. -/
theorem measure_alternatingZeroStart_stateOne_future_factor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (Fin 2 → ℕ → ℝ)) (hB : MeasurableSet B) :
    let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)
    let stateOne : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
      {paths | TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = 1}
    μ (Set.inter stateOne (alternatingZeroStartFuture t ⁻¹' B)) =
      μ stateOne * μ (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  dsimp
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure leftRate).prod
      (exponentialInterarrivalMeasure rightRate)
  let count := alternatingZeroStartCount t
  let future := alternatingZeroStartFuture t
  let stateOne : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {paths | TwoStateSwitching.stateAt 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t = 1}
  let D : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    TwoStateSwitching.twoStateGapsOfPair ⁻¹' B
  let counts : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    fun n => count ⁻¹' {2 * n + 1}
  let pieces : ℕ → Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    fun n => Set.inter (counts n) (future ⁻¹' B)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hcountMeas : Measurable count := by
    simpa [count] using measurable_alternatingZeroStartCount t
  have hfutureMeas : Measurable future := by
    simpa [future] using measurable_alternatingZeroStartFuture t
  have hcountsMeas : ∀ n : ℕ, MeasurableSet (counts n) := by
    intro n
    exact hcountMeas (measurableSet_singleton (2 * n + 1))
  have hpiecesMeas : ∀ n : ℕ, MeasurableSet (pieces n) := by
    intro n
    exact (hcountsMeas n).inter (hfutureMeas hB)
  have hcountsDisjoint : Pairwise (Function.onFun Disjoint counts) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro paths hn hm
    change count paths = 2 * n + 1 at hn
    change count paths = 2 * m + 1 at hm
    apply hnm
    omega
  have hpiecesDisjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro paths hn hm
    exact (Set.disjoint_left.1 (hcountsDisjoint hnm)) hn.1 hm.1
  have hcountsUnion : (⋃ n : ℕ, counts n) = stateOne := by
    ext paths
    constructor
    · intro hpaths
      rcases Set.mem_iUnion.1 hpaths with ⟨n, hn⟩
      change count paths = 2 * n + 1 at hn
      change TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = 1
      unfold TwoStateSwitching.stateAt
      rw [show canonicalRenewalCount t
          (TwoStateSwitching.alternatingGaps 0
            (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n + 1 by
          simpa [count, alternatingZeroStartCount] using hn,
        TwoStateSwitching.stateAfterSwitches_odd 0 ⟨n, by omega⟩]
      simp
    · intro hpaths
      change TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = 1 at hpaths
      rcases (count paths).even_or_odd' with ⟨n, hn | hn⟩
      · exfalso
        unfold TwoStateSwitching.stateAt at hpaths
        rw [show canonicalRenewalCount t
            (TwoStateSwitching.alternatingGaps 0
              (TwoStateSwitching.twoStateGapsOfPair paths)) = 2 * n by
            simpa [count, alternatingZeroStartCount] using hn,
          TwoStateSwitching.stateAfterSwitches_even 0 ⟨n, by omega⟩] at hpaths
        exact TwoStateSwitching.otherState_ne 0 hpaths.symm
      · exact Set.mem_iUnion.2 ⟨n, hn⟩
  have hpiecesUnion : (⋃ n : ℕ, pieces n) =
      Set.inter stateOne (future ⁻¹' B) := by
    ext paths
    constructor
    · intro hpaths
      rcases Set.mem_iUnion.1 hpaths with ⟨n, hn⟩
      exact ⟨hcountsUnion ▸ Set.mem_iUnion.2 ⟨n, hn.1⟩, hn.2⟩
    · rintro ⟨hstate, hfuture⟩
      rw [← hcountsUnion] at hstate
      rcases Set.mem_iUnion.1 hstate with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨hn, hfuture⟩⟩
  calc
    μ (Set.inter stateOne (future ⁻¹' B)) = μ (⋃ n : ℕ, pieces n) := by
      rw [hpiecesUnion]
    _ = ∑' n : ℕ, μ (pieces n) :=
      measure_iUnion hpiecesDisjoint hpiecesMeas
    _ = ∑' n : ℕ, μ (counts n) * μ D := by
      apply tsum_congr
      intro n
      simpa [pieces, counts, count, future, D, μ,
        alternatingZeroStartCount, alternatingZeroStartFuture] using
        measure_oddAlternatingCountFutureFiber_factor hleft hright t ht n B hB
    _ = (∑' n : ℕ, μ (counts n)) * μ D := by
      exact ENNReal.tsum_mul_right
    _ = μ D * ∑' n : ℕ, μ (counts n) := by ac_rfl
    _ = μ D * μ (⋃ n : ℕ, counts n) := by
      rw [measure_iUnion hcountsDisjoint hcountsMeas]
    _ = μ D * μ stateOne := by rw [hcountsUnion]
    _ = μ stateOne * μ D := by ac_rfl

/-- At every nonnegative deterministic time, the source-order two-state
endpoint and its literal state-indexed future streams factor exactly. -/
theorem measure_alternatingZeroStart_state_future_factor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (ht : 0 ≤ t) (target : Fin 2)
    (B : Set (Fin 2 → ℕ → ℝ)) (hB : MeasurableSet B) :
    let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)
    let stateTarget : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
      {paths | TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair paths) t = target}
    μ (Set.inter stateTarget (alternatingZeroStartFuture t ⁻¹' B)) =
      μ stateTarget * μ (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  dsimp
  fin_cases target
  · exact measure_alternatingZeroStart_stateZero_future_factor
      hleft hright t ht B hB
  · exact measure_alternatingZeroStart_stateOne_future_factor
      hleft hright t ht B hB

/-- At every nonnegative deterministic time, the source-order two-state
endpoint and literal future streams factor when the displayed alternating
path begins in state one.  The proof transports the state-zero statement
through the measurable swap of the two source streams and relabels the
state-indexed output coordinates; it does not assert a fresh-clock or
strong-Markov property. -/
theorem measure_alternatingOneStart_state_future_factor
    {leftRate rightRate : ℝ}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (t : ℝ) (ht : 0 ≤ t) (target : Fin 2)
    (B : Set (Fin 2 → ℕ → ℝ)) (hB : MeasurableSet B) :
    let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
      (exponentialInterarrivalMeasure leftRate).prod
        (exponentialInterarrivalMeasure rightRate)
    let stateTarget : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
      {paths | TwoStateSwitching.stateAt 1
        (TwoStateSwitching.twoStateGapsOfPair paths) t = target}
    μ (Set.inter stateTarget (alternatingOneStartFuture t ⁻¹' B)) =
      μ stateTarget * μ (TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  dsimp
  let μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure leftRate).prod
      (exponentialInterarrivalMeasure rightRate)
  let μswap : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure rightRate).prod
      (exponentialInterarrivalMeasure leftRate)
  let stateTarget : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {paths | TwoStateSwitching.stateAt 1
      (TwoStateSwitching.twoStateGapsOfPair paths) t = target}
  let stateTargetSwap : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {paths | TwoStateSwitching.stateAt 0
      (TwoStateSwitching.twoStateGapsOfPair paths) t =
        TwoStateSwitching.otherState target}
  let futureOne := alternatingOneStartFuture t
  let futureZero := alternatingZeroStartFuture t
  let Bswap : Set (Fin 2 → ℕ → ℝ) :=
    TwoStateSwitching.swapStateIndexedGaps ⁻¹' B
  let D : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    TwoStateSwitching.twoStateGapsOfPair ⁻¹' B
  let Dswap : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    TwoStateSwitching.twoStateGapsOfPair ⁻¹' Bswap
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) := by
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hright
  have hotherInjective : Function.Injective TwoStateSwitching.otherState := by
    intro a b hab
    calc
      a = TwoStateSwitching.otherState (TwoStateSwitching.otherState a) :=
        (TwoStateSwitching.otherState_otherState a).symm
      _ = TwoStateSwitching.otherState (TwoStateSwitching.otherState b) := by
        rw [hab]
      _ = b := TwoStateSwitching.otherState_otherState b
  have hBswap : MeasurableSet Bswap := by
    exact hB.preimage TwoStateSwitching.measurable_swapStateIndexedGaps
  have hfutureZeroMeas : Measurable futureZero := by
    simpa [futureZero] using measurable_alternatingZeroStartFuture t
  have hstateTargetSwapMeas : MeasurableSet stateTargetSwap := by
    exact ((TwoStateSwitching.measurable_stateAt_fixedTime 0 t).comp
      TwoStateSwitching.measurable_twoStateGapsOfPair)
        (measurableSet_singleton _)
  have hDswapMeas : MeasurableSet Dswap := by
    exact TwoStateSwitching.measurable_twoStateGapsOfPair hBswap
  have hswapEventMeas : MeasurableSet
      (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) := by
    exact hstateTargetSwapMeas.inter (hfutureZeroMeas hBswap)
  have hmapSwap : Measure.map Prod.swap μ = μswap := by
    simpa [μ, μswap] using
      (Measure.prod_swap : Measure.map Prod.swap
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) =
        (exponentialInterarrivalMeasure rightRate).prod
          (exponentialInterarrivalMeasure leftRate))
  have hstateTransport : stateTarget = Prod.swap ⁻¹' stateTargetSwap := by
    ext paths
    change TwoStateSwitching.stateAt 1
        (TwoStateSwitching.twoStateGapsOfPair paths) t = target ↔
      TwoStateSwitching.stateAt 0
        (TwoStateSwitching.twoStateGapsOfPair (Prod.swap paths)) t =
          TwoStateSwitching.otherState target
    rw [TwoStateSwitching.stateAt_zero_swapPair_eq_otherState_stateAt_one]
    constructor
    · intro h
      rw [h]
    · intro h
      exact hotherInjective h
  have hfutureTransport : futureOne ⁻¹' B =
      Prod.swap ⁻¹' (futureZero ⁻¹' Bswap) := by
    ext paths
    change alternatingOneStartFuture t paths ∈ B ↔
      alternatingZeroStartFuture t (Prod.swap paths) ∈ Bswap
    change TwoStateSwitching.switchGapsAfterElapsed 1
        (TwoStateSwitching.twoStateGapsOfPair paths) t ∈ B ↔
      TwoStateSwitching.switchGapsAfterElapsed 0
        (TwoStateSwitching.twoStateGapsOfPair (Prod.swap paths)) t ∈
          TwoStateSwitching.swapStateIndexedGaps ⁻¹' B
    rw [TwoStateSwitching.switchGapsAfterElapsed_one_eq_swapStateIndexedGaps_zero_swapPair]
    rfl
  have hDTransport : Dswap = Prod.swap ⁻¹' D := by
    ext paths
    change TwoStateSwitching.swapStateIndexedGaps
        (TwoStateSwitching.twoStateGapsOfPair paths) ∈ B ↔
      TwoStateSwitching.twoStateGapsOfPair (Prod.swap paths) ∈ B
    rw [TwoStateSwitching.twoStateGapsOfPair_swap_eq_swapStateIndexedGaps]
  have hswapEventTransport :
      Set.inter stateTarget (futureOne ⁻¹' B) =
        Prod.swap ⁻¹' (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) := by
    rw [hstateTransport, hfutureTransport]
    ext paths
    rfl
  have hstateTransportMeas : MeasurableSet stateTargetSwap :=
    hstateTargetSwapMeas
  have hstateMeasure : μ stateTarget = μswap stateTargetSwap := by
    calc
      μ stateTarget = μ (Prod.swap ⁻¹' stateTargetSwap) := by rw [hstateTransport]
      _ = Measure.map Prod.swap μ stateTargetSwap := by
        rw [Measure.map_apply measurable_swap hstateTransportMeas]
      _ = μswap stateTargetSwap := by rw [hmapSwap]
  have hfutureMeasure : μ D = μswap Dswap := by
    have hDTransportInv : D = Prod.swap ⁻¹' Dswap := by
      calc
        D = Prod.swap ⁻¹' (Prod.swap ⁻¹' D) := by
          ext paths
          simp
        _ = Prod.swap ⁻¹' Dswap := by rw [hDTransport]
    calc
      μ D = μ (Prod.swap ⁻¹' Dswap) := by rw [hDTransportInv]
      _ = Measure.map Prod.swap μ Dswap := by
        rw [Measure.map_apply measurable_swap hDswapMeas]
      _ = μswap Dswap := by rw [hmapSwap]
  have hswapEventMeasure :
      μ (Set.inter stateTarget (futureOne ⁻¹' B)) =
        μswap (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) := by
    calc
      μ (Set.inter stateTarget (futureOne ⁻¹' B)) =
          μ (Prod.swap ⁻¹' (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap))) := by
            rw [hswapEventTransport]
      _ = Measure.map Prod.swap μ
          (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) := by
            rw [Measure.map_apply measurable_swap hswapEventMeas]
      _ = μswap (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) := by
            rw [hmapSwap]
  have hzero :
      μswap (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) =
        μswap stateTargetSwap * μswap Dswap := by
    simpa [μswap, stateTargetSwap, futureZero, Bswap, Dswap] using
      measure_alternatingZeroStart_state_future_factor hright hleft t ht
        (TwoStateSwitching.otherState target) Bswap hBswap
  calc
    μ (Set.inter stateTarget (futureOne ⁻¹' B)) =
        μswap (Set.inter stateTargetSwap (futureZero ⁻¹' Bswap)) :=
      hswapEventMeasure
    _ = μswap stateTargetSwap * μswap Dswap := hzero
    _ = μ stateTarget * μ D := by rw [hstateMeasure, hfutureMeasure]

end

end AppliedModelingLib.Probability.PoissonProcess

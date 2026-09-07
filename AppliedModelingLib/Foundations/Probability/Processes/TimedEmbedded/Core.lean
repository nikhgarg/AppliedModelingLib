import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core
import Mathlib.Tactic

/-!
# Timing a marked embedded path by a Poisson suspension

This module separates the pathwise real-time synchronization needed for a
marked M/M/1 construction from the still-open discrete stationarity proof. A
good two-sided exponential suspension is coupled to an arbitrary
integer-indexed embedded path. Real-time translation shifts the Poisson
suspension and reindexes the embedded path by exactly the crossing label of
that translation.

The action and its state/arrival covariance are proved pathwise. The generic
skew-product theorem below turns *any* two-sided embedded law invariant under
every integer reindexing into a genuine real-time stationary law. The existing
M/M/1 marked trajectory still needs that full two-sided shift-invariance
theorem, so this module does not yet claim a real-time stationary M/M/1 law,
thinning, Palm, or PASTA.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

variable {α : Type*}

/-- Shift an integer-indexed path so that old label `k` becomes new label zero. -/
def intPathShift (k : ℤ) (x : ℤ → α) : ℤ → α :=
  fun i => x (k + i)

theorem intPathShift_apply (k i : ℤ) (x : ℤ → α) :
    intPathShift k x i = x (k + i) := rfl

theorem intPathShift_zero (x : ℤ → α) : intPathShift 0 x = x := by
  funext i
  simp [intPathShift]

theorem intPathShift_comp (k l : ℤ) (x : ℤ → α) :
    intPathShift l (intPathShift k x) = intPathShift (k + l) x := by
  funext i
  change x (k + (l + i)) = x ((k + l) + i)
  congr 1
  omega

/-- Integer relabeling is measurable on every countable product path space. -/
theorem measurable_intPathShift [MeasurableSpace α] (k : ℤ) :
    Measurable (intPathShift (α := α) k) := by
  apply measurable_pi_iff.2
  intro i
  exact measurable_pi_apply (k + i)

/-- A measurable factor that commutes with integer relabeling transports an
integer-shift-preserving path law to its image law. -/
theorem measurePreserving_intPathShift_map_of_commutes
    {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (M : Measure (ℤ → α)) (f : (ℤ → α) → (ℤ → β))
    (hf : Measurable f)
    (hcomm : ∀ (k : ℤ) (x : ℤ → α),
      f (intPathShift k x) = intPathShift k (f x))
    {k : ℤ} (hshift : MeasurePreserving (intPathShift (α := α) k) M M) :
    MeasurePreserving (intPathShift (α := β) k) (M.map f) (M.map f) := by
  refine ⟨measurable_intPathShift (α := β) k, ?_⟩
  calc
    Measure.map (intPathShift (α := β) k) (M.map f) =
        Measure.map (intPathShift (α := β) k ∘ f) M := by
          rw [Measure.map_map (measurable_intPathShift (α := β) k) hf]
    _ = Measure.map (f ∘ intPathShift (α := α) k) M := by
          congr 1
          funext x
          exact (hcomm k x).symm
    _ = Measure.map f (M.map (intPathShift (α := α) k)) := by
          symm
          rw [Measure.map_map hf (measurable_intPathShift (α := α) k)]
    _ = Measure.map f M := by rw [hshift.map_eq]

/-- Couple a good two-sided exponential suspension to an arbitrary two-sided
embedded path.  The product law is introduced separately below. -/
def timedEmbeddedSuspensionFlow (t : ℝ) :
    (GoodSuspensionState × (ℤ → α)) → GoodSuspensionState × (ℤ → α) :=
  fun z =>
    (goodSuspensionFlow t z.1,
      intPathShift (suspensionCrossingIndexPastClosed t z.1.1) z.2)

/-- The event time of a labelled embedded coordinate. -/
def timedEmbeddedArrival (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) : ℝ :=
  suspensionBaseArrival z.1 i

/-- The embedded state/mark carried by a labelled event. -/
def timedEmbeddedState (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) : α :=
  z.2 i

/-- The independent product law on a Poisson suspension and a supplied
two-sided embedded path law.  Its real-time invariance is intentionally not
claimed here: that requires invariance of the path law under all integer
reindexings. -/
noncomputable def timedEmbeddedSuspensionProductMeasure
    [MeasurableSpace α] (rate : ℝ) (P : Measure (ℤ → α)) :
    Measure (GoodSuspensionState × (ℤ → α)) :=
  (goodSuspensionMeasure rate).prod P

/-- The reindexing coordinate of the timed action is jointly measurable in
the suspension state and the attached integer path. -/
theorem measurable_timedEmbeddedPathReindex [MeasurableSpace α] (t : ℝ) :
    Measurable (fun z : GoodSuspensionState × (ℤ → α) =>
      intPathShift (suspensionCrossingIndexPastClosed t z.1.1) z.2) := by
  have hcross : Measurable (fun p : GoodSuspensionState =>
      suspensionCrossingIndexPastClosed t p.1) :=
    (measurable_suspensionCrossingIndexPastClosed t).comp measurable_subtype_coe
  have heval : Measurable (fun z : ℤ × (ℤ → α) => z.2 z.1) :=
    measurable_from_prod_countable_right fun i => measurable_pi_apply i
  apply measurable_pi_iff.2
  intro i
  exact heval.comp ((hcross.comp measurable_fst |>.add_const i).prodMk measurable_snd)

theorem measurable_timedEmbeddedSuspensionFlow [MeasurableSpace α] (t : ℝ) :
    Measurable (timedEmbeddedSuspensionFlow (α := α) t) := by
  exact (measurable_goodSuspensionFlow t).comp measurable_fst |>.prodMk
    (measurable_timedEmbeddedPathReindex (α := α) t)

/-- If the two-sided embedded law is invariant under every integer relabeling,
then the clock/path skew action preserves its product with the stationary
Poisson suspension. This is the exact bridge from a discrete stationary
trajectory to real-time stationarity; it makes no thinning, Palm, or PASTA
claim. -/
theorem timedEmbeddedSuspensionFlow_measurePreserving_of_intPathShift
    [MeasurableSpace α] {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P)
    (t : ℝ) :
    MeasurePreserving (timedEmbeddedSuspensionFlow (α := α) t)
      (timedEmbeddedSuspensionProductMeasure rate P)
      (timedEmbeddedSuspensionProductMeasure rate P) := by
  letI : IsProbabilityMeasure (goodSuspensionMeasure rate) :=
    isProbabilityMeasure_goodSuspensionMeasure hrate
  let g : GoodSuspensionState → (ℤ → α) → (ℤ → α) := fun p =>
    intPathShift (suspensionCrossingIndexPastClosed t p.1)
  have hgm : Measurable (Function.uncurry g) := by
    simpa only [g, Function.uncurry] using
      measurable_timedEmbeddedPathReindex (α := α) t
  have hg : ∀ᵐ p ∂goodSuspensionMeasure rate, Measure.map (g p) P = P :=
    Filter.Eventually.of_forall fun p => (hpath _).map_eq
  change MeasurePreserving _ ((goodSuspensionMeasure rate).prod P)
    ((goodSuspensionMeasure rate).prod P)
  simpa only [g, timedEmbeddedSuspensionFlow] using
    (goodSuspensionFlow_measurePreserving_of_raw hrate t
      (suspensionFlow_measurePreserving_suspensionMeasure hrate t)).skew_product hgm hg

/-- The crossing label has the exact cocycle needed to reindex the attached
integer path after two real-time translations. -/
theorem suspensionCrossingIndexPastClosed_good_cocycle
    (p : GoodSuspensionState) (s t : ℝ) :
    suspensionCrossingIndexPastClosed s (goodSuspensionFlow t p).1 +
        suspensionCrossingIndexPastClosed t p.1 =
      suspensionCrossingIndexPastClosed (s + t) p.1 := by
  have h := suspensionCrossingIndexPastClosed_cocycle_of_reindex_divergence
    p.1.1
    (suspensionGoodGapPath_strictMono p.1.1 p.2.2)
    (suspensionGoodGapPath_future p.1.1 p.2.2)
    (suspensionGoodGapPath_past p.1.1 p.2.2)
    p.2.2.2 p.1.2 t s
  simpa [goodSuspensionFlow, add_comm] using h

/-- At time zero, a suspension state is already indexed by the gap containing
the origin, so the real-time flow does not relabel its attached path. -/
theorem suspensionCrossingIndexPastClosed_zero_good
    (p : GoodSuspensionState) :
    suspensionCrossingIndexPastClosed 0 p.1 = 0 := by
  have hbase : candidatePalmArrival p.1.1 (0 : ℤ) ≤ p.1.2 ∧
      p.1.2 < candidatePalmArrival p.1.1 ((0 : ℤ) + 1) := by
    constructor
    · simpa only [candidatePalmArrival_zero, zero_le] using p.2.1.1
    · rw [candidatePalmArrival_add_one, candidatePalmArrival_zero, zero_add]
      exact p.2.1.2
  have hcross := suspensionCrossingIndexPastClosed_interval p.1.1
    (suspensionGoodGapPath_future p.1.1 p.2.2)
    (suspensionGoodGapPath_past p.1.1 p.2.2) p.1.2 0
  have hcross' : candidatePalmArrival p.1.1
      (suspensionCrossingIndexPastClosed 0 p.1) ≤ p.1.2 ∧
      p.1.2 < candidatePalmArrival p.1.1
        (suspensionCrossingIndexPastClosed 0 p.1 + 1) := by
    simpa using hcross
  exact (candidatePalmArrival_interval_index_unique p.1.1
    (suspensionGoodGapPath_strictMono p.1.1 p.2.2) hcross' hbase)

/-- Zero real-time translation fixes both the good suspension state and every
coordinate of the attached two-sided path. -/
theorem timedEmbeddedSuspensionFlow_zero :
    timedEmbeddedSuspensionFlow (α := α) 0 = id := by
  funext z
  change (goodSuspensionFlow 0 z.1,
      intPathShift (suspensionCrossingIndexPastClosed 0 z.1.1) z.2) = z
  rw [show goodSuspensionFlow 0 z.1 = z.1 by
    exact congrFun goodSuspensionFlow_zero z.1,
    suspensionCrossingIndexPastClosed_zero_good z.1,
    intPathShift_zero]

/-- Translation by `t` relabels every event coordinate by the suspension's
crossing label and translates its epoch by `-t`. -/
theorem timedEmbeddedArrival_flow
    (z : GoodSuspensionState × (ℤ → α)) (t : ℝ) (j : ℤ) :
    timedEmbeddedArrival (timedEmbeddedSuspensionFlow (α := α) t z) j =
      timedEmbeddedArrival z
        (suspensionCrossingIndexPastClosed t z.1.1 + j) - t := by
  exact suspensionBaseArrival_goodSuspensionFlow z.1 t j

/-- Translation by `t` relabels the attached state/mark path by precisely the
same crossing label as its event epochs. -/
theorem timedEmbeddedState_flow
    (z : GoodSuspensionState × (ℤ → α)) (t : ℝ) (j : ℤ) :
    timedEmbeddedState (timedEmbeddedSuspensionFlow (α := α) t z) j =
      timedEmbeddedState z
        (suspensionCrossingIndexPastClosed t z.1.1 + j) := rfl

/-- The timed suspension action composes pointwise on every good exponential
path and arbitrary two-sided embedded path.  This is a pathwise statement;
it does not yet claim that a marked M/M/1 path law is invariant under these
integer reindexings. -/
theorem timedEmbeddedSuspensionFlow_add (s t : ℝ) :
    timedEmbeddedSuspensionFlow (α := α) (s + t) =
      timedEmbeddedSuspensionFlow (α := α) s ∘
        timedEmbeddedSuspensionFlow (α := α) t := by
  funext z
  apply Prod.ext
  · exact congrFun (goodSuspensionFlow_add s t) z.1
  · change intPathShift (suspensionCrossingIndexPastClosed (s + t) z.1.1) z.2 =
      intPathShift (suspensionCrossingIndexPastClosed s
        (goodSuspensionFlow t z.1).1)
        (intPathShift (suspensionCrossingIndexPastClosed t z.1.1) z.2)
    rw [intPathShift_comp]
    congr 2
    have h := suspensionCrossingIndexPastClosed_good_cocycle z.1 s t
    omega

/-- Package the skew-product preservation theorem as a real-time stationary
law. The premise is intentionally a full integer-shift invariance hypothesis
on the embedded path law; applying this to M/M/1 remains a separate theorem. -/
noncomputable def timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift
    [MeasurableSpace α] {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P) :
    Palm.ShiftInvariantProbabilityLaw (GoodSuspensionState × (ℤ → α)) where
  Pbase := timedEmbeddedSuspensionProductMeasure rate P
  isProbability := by
    change IsProbabilityMeasure ((goodSuspensionMeasure rate).prod P)
    letI : IsProbabilityMeasure (goodSuspensionMeasure rate) :=
      isProbabilityMeasure_goodSuspensionMeasure hrate
    infer_instance
  shift := timedEmbeddedSuspensionFlow
  shift_zero := timedEmbeddedSuspensionFlow_zero
  shift_add := timedEmbeddedSuspensionFlow_add
  shift_preserving := fun t =>
    timedEmbeddedSuspensionFlow_measurePreserving_of_intPathShift hrate P hpath t

end

end AppliedModelingLib.Probability.Queueing

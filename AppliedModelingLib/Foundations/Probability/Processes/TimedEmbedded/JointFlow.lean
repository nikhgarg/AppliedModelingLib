import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Core

/-!
# Joint measurability of stationary Poisson suspension flows

The stationary suspension APIs initially expose measurability only after a
real-time translation is fixed.  Recentring an independent passive input at a
random arrival epoch needs the stronger jointly measurable map `(t, state) ↦
shift t state`.  This module proves that property for the exponential
suspension and for a synchronously reindexed timed embedded path.

It does not make a Campbell, Palm, queueing, or stationarity assertion beyond
the already established fixed-time laws.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory

noncomputable section

/-- The boundary-correct crossing label is jointly measurable in real time
and the raw suspension state. -/
theorem measurable_uncurry_suspensionCrossingIndexPastClosed :
    Measurable (Function.uncurry suspensionCrossingIndexPastClosed) := by
  have hforward : Measurable (fun q : Real × ((Int -> Real) × Real) =>
      canonicalRenewalCount (q.2.2 + q.1) (suspensionFuturePath q.2.1)) := by
    exact measurable_jointCanonicalRenewalCount.comp
      (((measurable_snd.comp measurable_snd).add measurable_fst).prodMk
        (measurable_suspensionFuturePath.comp (measurable_fst.comp measurable_snd)))
  have hbackward : Measurable (fun q : Real × ((Int -> Real) × Real) =>
      canonicalRenewalCountLE (-(q.2.2 + q.1)) (suspensionPastPath q.2.1)) := by
    exact measurable_jointCanonicalRenewalCountLE.comp
      (((measurable_snd.comp measurable_snd).add measurable_fst).neg.prodMk
        (measurable_suspensionPastPath.comp (measurable_fst.comp measurable_snd)))
  change Measurable (fun q : Real × ((Int -> Real) × Real) => if
      0 ≤ q.2.2 + q.1 then
        Int.ofNat (canonicalRenewalCount (q.2.2 + q.1) (suspensionFuturePath q.2.1))
      else
        Int.negSucc (canonicalRenewalCountLE (-(q.2.2 + q.1))
          (suspensionPastPath q.2.1)))
  refine Measurable.ite
    (measurableSet_le measurable_const ((measurable_snd.comp measurable_snd).add measurable_fst))
    ?_ ?_
  · exact (measurable_of_countable (Int.ofNat : Nat -> Int)).comp hforward
  · exact (measurable_of_countable (Int.negSucc : Nat -> Int)).comp hbackward

/-- The raw special-flow action is jointly measurable in translation time and
raw suspension state. -/
theorem measurable_uncurry_suspensionFlow :
    Measurable (Function.uncurry suspensionFlow) := by
  let crossing : Real × ((Int -> Real) × Real) -> Int :=
    Function.uncurry suspensionCrossingIndexPastClosed
  have hcrossing : Measurable crossing :=
    measurable_uncurry_suspensionCrossingIndexPastClosed
  have hgapEval : Measurable (fun q : Int × (Int -> Real) =>
      twoSidedGap q.1 q.2) := by
    exact measurable_from_prod_countable_right fun i => measurable_twoSidedGap i
  have hshift : Measurable (fun q : Real × ((Int -> Real) × Real) =>
      suspensionGapShift (crossing q) q.2.1) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact hgapEval.comp
      ((measurable_const.add hcrossing).prodMk (measurable_fst.comp measurable_snd))
  have harrivalEval : Measurable (fun q : Int × (Int -> Real) =>
      candidatePalmArrival q.2 q.1) := by
    exact measurable_from_prod_countable_right fun i => measurable_candidatePalmArrival i
  change Measurable (fun q : Real × ((Int -> Real) × Real) =>
    (suspensionGapShift (crossing q) q.2.1,
      q.2.2 + q.1 - candidatePalmArrival q.2.1 (crossing q)))
  exact hshift.prodMk
    (((measurable_snd.comp measurable_snd).add measurable_fst).sub
      (harrivalEval.comp
        (hcrossing.prodMk (measurable_fst.comp measurable_snd))))

/-- The literal good-state Poisson suspension flow is jointly measurable in
real time and state. -/
theorem measurable_uncurry_goodSuspensionFlow :
    Measurable (Function.uncurry goodSuspensionFlow) := by
  apply Measurable.subtype_mk
  exact measurable_uncurry_suspensionFlow.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

end

end AppliedModelingLib.Probability.PoissonProcess

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory
open PoissonProcess

noncomputable section

/-- The timed embedded stationary flow is jointly measurable in real time
and state.  Its integer path is reindexed by the same measurable crossing
label as its Poisson suspension component. -/
theorem measurable_uncurry_timedEmbeddedSuspensionFlow
    {alpha : Type*} [MeasurableSpace alpha] :
    Measurable (Function.uncurry (timedEmbeddedSuspensionFlow (α := alpha))) := by
  let crossing : Real × (GoodSuspensionState × (Int -> alpha)) -> Int := fun q =>
    suspensionCrossingIndexPastClosed q.1 q.2.1.1
  have hcrossing : Measurable crossing := by
    exact measurable_uncurry_suspensionCrossingIndexPastClosed.comp
      (measurable_fst.prodMk
        ((measurable_subtype_coe.comp measurable_fst).comp measurable_snd))
  have hpathEval : Measurable (fun q : Int × (Int -> alpha) => q.2 q.1) := by
    exact measurable_from_prod_countable_right fun i => measurable_pi_apply i
  have hpath : Measurable (fun q : Real × (GoodSuspensionState × (Int -> alpha)) =>
      intPathShift (crossing q) q.2.2) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact hpathEval.comp
      ((hcrossing.add_const i).prodMk (measurable_snd.comp measurable_snd))
  change Measurable (fun q : Real × (GoodSuspensionState × (Int -> alpha)) =>
    (goodSuspensionFlow q.1 q.2.1,
      intPathShift (crossing q) q.2.2))
  exact (measurable_uncurry_goodSuspensionFlow.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk hpath

end

end AppliedModelingLib.Probability.Queueing

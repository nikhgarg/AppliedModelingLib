import LBG24SpatialUnderreporting.ConditionOneTail
import LBG24SpatialUnderreporting.MainTheorems

/-!
# Paper-facing Condition 1 source/selection packaging

The LBG source uses the same informal symbol `g` for a fixed-history
start-density contribution and for the random-start mechanism behind Lemma 2.
The formal development deliberately keeps those two roles separate:

* `Theorem2ConditionOneSource` records only the rate-independent scalar
  contribution used by the fixed-history likelihood algebra.
* `Theorem2ConditionOneSelection` records the well-typed conditional start
  kernel and conditional independence needed for the stochastic tail argument.

`Theorem2ConditionOneSourceSelection` packages both records for a single
source model without claiming that the scalar is a density of the kernel.  Such
a claim requires a separately formalized disintegration/density relation.

The canonical row below is therefore a precise source-facing version of Lemma
2, conditional on `σ(T₁)`.  It does not establish the later uses of Lemma 2
under the paper's full observed report history; that requires a forward
stopped-process regeneration result or an explicit history-level conditional
tail-law premise.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal

noncomputable section

/--
One source-level Condition-1 package for the two distinct formal roles of the
paper's informal `g`.  `scalarSource` and `selection` intentionally have no
linking field: the scalar record has no density semantics for the conditional
kernel, so asserting such a link here would overstate what the source and the
current formalization establish.
-/
structure Theorem2ConditionOneSourceSelection
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tail : Type*) [MeasurableSpace Tail] where
  /-- Rate-independent fixed-history `g(s)` contribution. -/
  scalarSource : Theorem2ConditionOneSource
  /-- Kernelized random-start mechanism and post-first-report-tail premise. -/
  selection : Theorem2ConditionOneSelection Ω P Tail

namespace Theorem2ConditionOneSourceSelection

/--
Canonical first-report Lemma-2 row.  For an exponential-interarrival carrier,
when the first report is the first canonical arrival and the supplied tail is
the future interarrival sequence, the selected post-start canonical tail has
the exponential no-arrival probability conditional on `σ(T₁)`.

This theorem intentionally makes no claim conditional on the full report
history used later in Theorem 2, and it does not identify `scalarSource` with a
density of `selection.rateFreeStartKernel`.
-/
theorem lemma2_canonical_first_report_no_arrival
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (M : Theorem2ConditionOneSourceSelection
      (ℕ → ℝ) (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      M.selection.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      M.selection.postFirstReportTail = futureInterarrival 1 →
      ∀ u : ℝ≥0, ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
        (condExpKernel (exponentialInterarrivalMeasure rate)
          (MeasurableSpace.comap M.selection.firstReportTime inferInstance) ω).real
            {ω' | Theorem2ConditionOneSelection.canonicalTailNoArrival u
              (M.selection.firstReportTime ω', M.selection.startTime ω')
              (M.selection.postFirstReportTail ω')} =
          noArrivalProb rate (u : ℝ) := by
  intro M hfirst htail u
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  exact LBG24SpatialUnderreporting.Theorem2ConditionOneSelection.conditional_canonicalTailNoArrival_real_given_firstReport_of_canonicalFirstArrival
    hrate M.selection hfirst htail u

end Theorem2ConditionOneSourceSelection

end

end LBG24SpatialUnderreporting

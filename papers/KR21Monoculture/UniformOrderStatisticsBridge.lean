import KR21Monoculture.QuantitativeWitnesses
import PRPKG24AccuracyDiversity.Uniform

open MeasureTheory

namespace KR21Monoculture

/-!
# Uniform order-statistic table for the KR21 three-firm instance

The finite rank-mean evaluator records a candidate's expected cardinal value
by its true rank.  This module proves that four-entry table from the actual
iid `Uniform[0,1]` product measure.  It deliberately does not identify the
whole sequential rank-mean experiment with the source's cardinal experiment;
that needs the separate ranking, independence, and label-symmetry bridges.
-/

/-- The source rank-mean table is the exact iid-uniform expected upper-order-statistic table. -/
theorem sourceExpectedOrderStatisticValue_eq_uniform01_expectedUpperOrderStatistic
    (candidate : SourceFourCandidate) :
    (sourceExpectedOrderStatisticValue candidate : ℝ) =
      AppliedModelingLib.Probability.expectedUpperOrderStatistic
        (Measure.pi (fun _ : Fin 4 => PRPKG24AccuracyDiversity.uniform01Measure))
        candidate := by
  rw [PRPKG24AccuracyDiversity.uniform01ProductMeasure_expectedUpperOrderStatistic_eq]
  fin_cases candidate <;>
    norm_num [sourceExpectedOrderStatisticValue, Fin.ext_iff]

end KR21Monoculture

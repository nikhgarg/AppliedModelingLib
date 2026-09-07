import AppliedModelingLib.Learning.Prediction

/-!
# Compatibility facade for prediction learning

Prediction, risk, multiaccuracy, and multicalibration now live under
`AppliedModelingLib.Learning.Prediction`.  This facade preserves the historical
`AppliedModelingLib.Statistics` names while downstream paper modules migrate.
-/

namespace AppliedModelingLib.Statistics

/-- Historical name for a real-valued prediction score. -/
abbrev Model (X : Type*) := AppliedModelingLib.Learning.Prediction.Score X

/-- Historical name for a finite observation weight. -/
abbrev FiniteWeight (X : Type*) :=
  AppliedModelingLib.Learning.Prediction.FiniteWeight X

/-- Historical name for a real-valued soft group. -/
abbrev Group (X : Type*) := AppliedModelingLib.Learning.Prediction.SoftGroup X

/-- Historical constant-score constructor. -/
abbrev constantModel {X : Type*} :=
  @AppliedModelingLib.Learning.Prediction.constantScore X

export AppliedModelingLib.Learning.Prediction
  (squaredError modelLoss squaredLoss groupMass groupLossNumerator groupLoss
    groupSquaredLoss groupSquaredDisagreement zeroOneLoss classificationError
    probabilisticClassificationLoss weightedRateNumerator weightedRateMass
    weightedRate weightedRateBeta weightedRate_gap_eq_expectation_gap
    posteriorConditionalMAE posteriorMAE levelSetIndicator
    ApproxMultiaccurateOnProducts OneSidedMultiaccurateOnProducts
    ModelClassClosedUnderNegation groupLossNumerator_residual_flip
    groupLossNumerator_neg_sourceResidual_eq
    approxMultiaccurateOnProducts_of_oneSided_negationClosed
    oneSidedMultiaccurateOnProducts_of_approxMultiaccurateOnProducts
    ApproxMulticalibratedInExpectation
    ApproxJointMulticalibratedInExpectation SelfOrthogonalOnGroups)

end AppliedModelingLib.Statistics

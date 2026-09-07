import AppliedModelingLib.Learning.Bandits
import AppliedModelingLib.Learning.BinaryOutcomeLikelihood
import AppliedModelingLib.Learning.ContinuousStrategicBurden
import AppliedModelingLib.Learning.ContinuousThresholdUtility
import AppliedModelingLib.Learning.EmpiricalRisk
import AppliedModelingLib.Learning.HumanFeedback
import AppliedModelingLib.Learning.Online
import AppliedModelingLib.Learning.OutcomeMonotoneCost
import AppliedModelingLib.Learning.OutcomeMonotoneThreshold
import AppliedModelingLib.Learning.OutcomeMonotoneThresholdComparativeStatics
import AppliedModelingLib.Learning.Prediction
import AppliedModelingLib.Learning.ReinforcementLearning
import AppliedModelingLib.Learning.Statistics
import AppliedModelingLib.Learning.StrategicResponse
import AppliedModelingLib.Learning.StrategicResponseWelfare

/-!
# Learning

Curated aggregate for prediction, statistics, online learning, bandits, human
feedback, empirical risk, and strategic-response models. New code should
normally import the narrow child facade or leaf it uses.

## Supported child facades

- `AppliedModelingLib.Learning.Bandits`
- `AppliedModelingLib.Learning.HumanFeedback`
- `AppliedModelingLib.Learning.Online`
- `AppliedModelingLib.Learning.Prediction`
- `AppliedModelingLib.Learning.ReinforcementLearning`
- `AppliedModelingLib.Learning.Statistics`

The remaining direct imports are stable declaration-owning modules whose
families have not yet earned a separate aggregate.
-/

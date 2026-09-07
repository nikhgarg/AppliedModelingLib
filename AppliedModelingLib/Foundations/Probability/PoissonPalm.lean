import AppliedModelingLib.Foundations.Probability.PalmArrivalPath
import AppliedModelingLib.Foundations.Probability.PalmCampbell
import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core
import AppliedModelingLib.Foundations.Probability.PoissonProcess

/-!
# Poisson and Palm interfaces

Curated entrypoint for Poisson-process primitives, tagged-arrival path models,
and the explicit stationary Palm/Campbell/PASTA interfaces. The Palm modules
state their provenance assumptions directly; this facade does not turn a
candidate arrival-path construction into a Palm law.
-/

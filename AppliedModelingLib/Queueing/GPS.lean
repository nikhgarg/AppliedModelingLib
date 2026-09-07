import AppliedModelingLib.Queueing.GPS.Core
import AppliedModelingLib.Queueing.GPS.AERateFloor
import AppliedModelingLib.Queueing.GPS.AENormalizedAllocation

/-!
# Generalized processor sharing

Curated queueing-domain entrypoint for deterministic fluid-GPS comparison,
almost-everywhere service-rate floors, and normalized GPS allocation. The
declarations retain their existing qualified names under queueing-domain source
modules.

The historical `AppliedModelingLib.Queueing.GPS.Core*` imports remain
supported. New queueing developments should normally import this facade or the
smallest underlying leaf they require.

The substantially larger executable finite-horizon family has its own curated
entrypoint at `AppliedModelingLib.Queueing.GPS.FiniteHorizon`; it is deliberately not
imported here.
-/

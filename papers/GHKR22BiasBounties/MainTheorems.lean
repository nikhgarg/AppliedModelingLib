import GHKR22BiasBounties.Core
import GHKR22BiasBounties.GeneralDistributionBoundary
import GHKR22BiasBounties.AdaptiveChecker
import GHKR22BiasBounties.FalsifyAndUpdate
import GHKR22BiasBounties.MonotoneBounty
import GHKR22BiasBounties.TernaryCSC
import GHKR22BiasBounties.Alternating
import GHKR22BiasBounties.Training
import GHKR22BiasBounties.MeasureCore
import GHKR22BiasBounties.MeasureAdaptiveChecker
import GHKR22BiasBounties.MeasureFalsifyAndUpdate
import GHKR22BiasBounties.MeasureMonotoneBounty
import GHKR22BiasBounties.MeasureVCTraining
import GHKR22BiasBounties.MeasureTraining
import GHKR22BiasBounties.MeasureTernaryCSC
import GHKR22BiasBounties.MeasureAlternating

/-!
# Paper-Facing Theorems: An Algorithmic Framework for Bias Bounties

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace GHKR22BiasBounties

end GHKR22BiasBounties

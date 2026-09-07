import AppliedModelingLib.Queueing.MM1DirectCausalWorkloadLaw
import AppliedModelingLib.Queueing.NonpreemptivePriorityLateBatchReplay

/-!
# Physical finite traces for a direct M/M/1 replay

This module connects the finite causal replay of a marked renewal history to
the corresponding literal chronological work-conserving arrival trace.
-/

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability.Queueing

noncomputable section

namespace MM1DirectCausal

/-- The scalar late-batch replay of a finite negative-time history is the
finite Lindley replay used by `timeReplay`. -/
theorem lateBatchPreWorkload_reverse_eq_timeReplay
    (serviceRate : ℝ) (h : NegativeTimeHistory) (N : ℕ) :
    lateBatchPreWorkload
      (reverseRemotePastIncrement (fun k => h.1 k / serviceRate) N)
      (reverseRemotePastIncrement h.2 N) N =
      timeReplay serviceRate 0 h N := by
  rw [lateBatchPreWorkload_eq_lindleyWorkload]
  unfold timeReplay remotePastReplayFrom
  rw [← congrFun (lindleyWorkload_eq_from_zero _) N]
  congr 1

end MM1DirectCausal

end

end AppliedModelingLib.Queueing

import AppliedModelingLib.Queueing.Lindley.RemotePastCutoff
import Mathlib.Tactic

/-!
# One-step remote-past identities for reflected workloads

The remote-past convention stores index zero immediately before the current
tag.  This deterministic file identifies what happens when the tag is moved
back by one input point.  It is intentionally independent of a probability
law and of any queueing tail calculation.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

/-- Drop the latest coordinate of an outward-from-present remote-past input. -/
def remotePastTail (f : Nat → Real) : Nat → Real := fun n => f (n + 1)

/-- A pre-batch late-batch state depends only on coordinates strictly before
that pre-batch index. -/
theorem lateBatchPreWorkload_congr_of_forall_lt
    {batch₁ service₁ batch₂ service₂ : Nat → Real} {n : Nat}
    (hbatch : ∀ j < n, batch₁ j = batch₂ j)
    (hservice : ∀ j < n, service₁ j = service₂ j) :
    lateBatchPreWorkload batch₁ service₁ n =
      lateBatchPreWorkload batch₂ service₂ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lateBatchPreWorkload_succ, lateBatchPreWorkload_succ]
      rw [lateBatchPostWorkload_eq_pre_add_batch,
        lateBatchPostWorkload_eq_pre_add_batch]
      have hpre : lateBatchPreWorkload batch₁ service₁ n =
          lateBatchPreWorkload batch₂ service₂ n := by
        apply ih
        · intro j hj
          exact hbatch j (Nat.lt_trans hj (Nat.lt_succ_self n))
        · intro j hj
          exact hservice j (Nat.lt_trans hj (Nat.lt_succ_self n))
      rw [hpre, hbatch n (Nat.lt_succ_self n), hservice n (Nat.lt_succ_self n)]

/-- Replaying one additional remote past input point gives the exact final
Lindley update from the replay rooted at the one-step older tail. -/
theorem lateBatchPreWorkload_reverseRemotePast_succ_eq_tail_update
    (batch service : Nat → Real) (N : Nat) :
    lateBatchPreWorkload
      (reverseRemotePastIncrement batch (N + 1))
      (reverseRemotePastIncrement service (N + 1)) (N + 1) =
      max
        (lateBatchPreWorkload
          (reverseRemotePastIncrement (remotePastTail batch) N)
          (reverseRemotePastIncrement (remotePastTail service) N) N +
          batch 0 - service 0) 0 := by
  rw [lateBatchPreWorkload_succ, lateBatchPostWorkload_eq_pre_add_batch]
  have hpre :
      lateBatchPreWorkload
        (reverseRemotePastIncrement batch (N + 1))
        (reverseRemotePastIncrement service (N + 1)) N =
        lateBatchPreWorkload
          (reverseRemotePastIncrement (remotePastTail batch) N)
          (reverseRemotePastIncrement (remotePastTail service) N) N := by
    apply lateBatchPreWorkload_congr_of_forall_lt
    · intro j hj
      unfold reverseRemotePastIncrement remotePastTail
      congr 1
      omega
    · intro j hj
      unfold reverseRemotePastIncrement remotePastTail
      congr 1
      omega
  rw [hpre]
  simp [reverseRemotePastIncrement]

end

end AppliedModelingLib.Probability.Queueing

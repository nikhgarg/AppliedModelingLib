import PRPKG24AccuracyDiversity.Basic

/-!
# Zero-support witness for the archival Corollary 1 domain

The source does not state strict positivity of every preferred-type
probability.  This small finite witness records why the all-optimal-sequences
claim cannot simply be extended to a zero-likelihood coordinate: that
coordinate can absorb the entire fixed slate while leaving the objective
unchanged.  It is a diagnostic counterexample, not a replacement theorem.
-/

namespace PRPKG24AccuracyDiversity

open AppliedModelingLib

noncomputable def zeroSupportModel : ConsumptionModel 2 where
  likelihood := fun t => if t = (0 : Fin 2) then 1 else 0
  valueOfCount := fun _ _ => 0

noncomputable def zeroSupportOffSupportAllocation : CountAllocation 2 where
  count := fun t => if t = (1 : Fin 2) then 1 else 0

theorem zeroSupportOffSupportAllocation_isOptimalAtTotal :
    (zeroSupportModel).IsOptimalAtTotal 1
      zeroSupportOffSupportAllocation := by
  refine ⟨?_, ?_⟩
  · simp [ConsumptionModel.FeasibleAtTotal, zeroSupportOffSupportAllocation,
      AppliedModelingLib.Allocation.HasTotal, AppliedModelingLib.Allocation.total]
  · intro b hb
    simp [zeroSupportModel, ConsumptionModel.objective,
      AppliedModelingLib.Allocation.objective]

theorem zeroSupportOffSupportAllocation_has_unit_offSupport_share :
    AppliedModelingLib.Allocation.share zeroSupportOffSupportAllocation
      (1 : Fin 2) = 1 := by
  rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero]
  · norm_num [zeroSupportOffSupportAllocation,
      AppliedModelingLib.Allocation.total]
  · simp [zeroSupportOffSupportAllocation,
      AppliedModelingLib.Allocation.total]

end PRPKG24AccuracyDiversity

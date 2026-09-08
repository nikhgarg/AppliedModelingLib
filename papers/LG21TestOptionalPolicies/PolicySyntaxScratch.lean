import LG21TestOptionalPolicies.ObservedAccessPolicySemantics

#guard_msgs(drop info) in
#check LG21TestOptionalPolicies.LG21ObservedAccessTwoBranchOutput.noAccessKernel_isMarkov

namespace LG21TestOptionalPolicies

open ProbabilityTheory

variable {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
variable (testFeature : Feature)
variable (accessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
variable (noAccessKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
variable [IsMarkovKernel noAccessKernel]

#guard_msgs(drop info) in
#check ({ accessOutput := accessOutput
          noAccessKernel := noAccessKernel
          noAccessKernel_isMarkov := inferInstance } :
  LG21ObservedAccessTwoBranchOutput testFeature)

end LG21TestOptionalPolicies

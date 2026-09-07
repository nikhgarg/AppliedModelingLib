import AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods

namespace AppliedModelingLib
namespace FairDivision

open scoped BigOperators

variable {Agent Item : Type*} [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item] [Nonempty Agent]
variable (v : Valuation Agent Item) {α : ℝ}

noncomputable def boundedEnvyStep (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)
    (g : Item) (state : Σ (goods : Finset Item), { A : Allocation Agent Item // IsAllocationOf A goods ∧ EnvyBoundedBy v A α }) :
    Σ (goods : Finset Item), { A : Allocation Agent Item // IsAllocationOf A goods ∧ EnvyBoundedBy v A α } :=
  let goods := state.1
  let A := state.2.val
  let halloc := state.2.property.1
  let hbound := state.2.property.2
  if hg : g ∈ goods then state else
  have hreduce := hasUnenviedReduction_of_acyclicReduction v (hasAcyclicReduction_of_envyCycleListExtraction v (hasEnvyCycleListExtraction_of_finite v))
  let reduction_exists := hreduce goods A halloc hbound
  let B := Classical.choose reduction_exists
  let owner_exists := Classical.choose_spec reduction_exists
  let owner := Classical.choose owner_exists
  let B_props := Classical.choose_spec owner_exists
  let hBalloc := B_props.1
  let hBbound := B_props.2.1
  let hunenvied := B_props.2.2
  let A_new := addItem B owner g
  let goods_new := insert g goods
  have halloc_new : IsAllocationOf A_new goods_new := by
    classical
    exact isAllocationOf_addItem_insert B goods owner g hBalloc hg
  have hbound_new : EnvyBoundedBy v A_new α := by
    classical
    exact envyBoundedBy_addItem_of_unenvied v B owner g hαnonneg hBbound hmargin hunenvied
  ⟨goods_new, ⟨A_new, halloc_new, hbound_new⟩⟩

noncomputable def boundedEnvyAlgorithm (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)
    (goodsList : List Item) :
    Σ (goods : Finset Item), { A : Allocation Agent Item // IsAllocationOf A goods ∧ EnvyBoundedBy v A α } :=
  goodsList.foldr (boundedEnvyStep v hαnonneg hmargin)
    ⟨∅, ⟨emptyAllocation Agent Item, isAllocationOf_empty, by
      intro i j
      simp [emptyAllocation, envy, hαnonneg]⟩⟩

theorem boundedEnvyAlgorithm_isAllocationOf_and_envyBoundedBy
    (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α) (goodsList : List Item) :
    let res := boundedEnvyAlgorithm v hαnonneg hmargin goodsList
    IsAllocationOf res.2.val res.1 ∧ EnvyBoundedBy v res.2.val α := by
  let res := boundedEnvyAlgorithm v hαnonneg hmargin goodsList
  exact res.2.property

theorem boundedEnvyAlgorithm_goods_eq_list_toFinset
    (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)
    (goodsList : List Item) (hnodup : goodsList.Nodup) :
    (boundedEnvyAlgorithm v hαnonneg hmargin goodsList).1 = goodsList.toFinset := by
  induction goodsList with
  | nil => rfl
  | cons head tail ih =>
    simp at hnodup
    have ih_eq : (boundedEnvyAlgorithm v hαnonneg hmargin tail).1 = tail.toFinset := ih hnodup.2
    have hnot_in : head ∉ tail.toFinset := by simp [hnodup.1]
    have hnot_in_state : head ∉ (boundedEnvyAlgorithm v hαnonneg hmargin tail).1 := by
      rw [ih_eq]
      exact hnot_in
    have h_foldr_cons : (boundedEnvyAlgorithm v hαnonneg hmargin (head :: tail)) =
        boundedEnvyStep v hαnonneg hmargin head
          (boundedEnvyAlgorithm v hαnonneg hmargin tail) := rfl
    have h_toFinset_cons : (head :: tail).toFinset = insert head tail.toFinset := by
      exact List.toFinset_cons
    rw [h_foldr_cons, h_toFinset_cons]
    unfold boundedEnvyStep
    simp [hnot_in_state]
    rw [ih_eq]

theorem boundedEnvyAlgorithm_isAllocationOf_list_toFinset_and_envyBoundedBy
    (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)
    (goodsList : List Item) (hnodup : goodsList.Nodup) :
    let res := boundedEnvyAlgorithm v hαnonneg hmargin goodsList
    IsAllocationOf res.2.val goodsList.toFinset ∧
      EnvyBoundedBy v res.2.val α := by
  classical
  let res := boundedEnvyAlgorithm v hαnonneg hmargin goodsList
  have hres := boundedEnvyAlgorithm_isAllocationOf_and_envyBoundedBy v hαnonneg hmargin goodsList
  have hgoods := boundedEnvyAlgorithm_goods_eq_list_toFinset v hαnonneg hmargin goodsList hnodup
  simpa [res, hgoods] using hres

end FairDivision
end AppliedModelingLib

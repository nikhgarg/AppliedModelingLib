import HT26EFXChores.PaperInterface
import HT26EFXChores.MainTheorems
import HT26EFXChores.Assumptions
import HT26EFXChores.Canonical
import HT26EFXChores.TriConstruction
import HT26EFXChores.ExceptionalCombination
import HT26EFXChores.AppendixTriInstance
import HT26EFXChores.ParetoConstruction
import HT26EFXChores.FullBiValuedDispatch

/-!
# Proof Interface: EFX for Additive Chores

This module holds the exact-type Lean proof endpoints for the transparent
source-facing specifications in `PaperInterface.lean`. It is not a second
semantic review surface: each source claim is compared only with its expanded
`...Spec : Prop`; Lean Meta separately verifies the endpoint type.
-/

namespace HT26EFXChores

theorem tri_valued_nonexistence :
  tri_valued_nonexistenceSpec := by
  intro n hn
  let choreInstance : AppliedModelingLib.FairDivision.AdditiveChoreInstance (Fin n)
      (Fin (n - 1 + 2 * (2 * ((n + 1) / 2) + 1))) := by
    simpa [appendixItemCount, appendixS, appendixT] using appendixTriInstance n
  refine ⟨n - 1 + 2 * (2 * ((n + 1) / 2) + 1), choreInstance, ?_, ?_⟩
  · simpa [choreInstance] using appendixTriInstance_tri_valued n
  · intro allocation halloc
    simpa [choreInstance, appendixItemCount, appendixS, appendixT] using
      (appendixTriInstance_no_efx n hn allocation halloc)

theorem tri_four_no_two_large :
  tri_four_no_two_largeSpec := by
  intro allocation halloc hefx agent
  rw [triA_filter_eq_inter]
  simpa [triFourCost] using tri_four_no_two_large_proof allocation halloc hefx agent

theorem tri_four_no_a_bundle_expensive :
  tri_four_no_a_bundle_expensiveSpec := by
  intro allocation halloc hefx hzero hone agent
  apply tri_four_no_A_bundle_expensive_proof allocation halloc hefx
  · rwa [triA_filter_eq_inter] at hzero
  · intro other hother
    simpa [triA_filter_eq_inter] using hone other hother

theorem efx_pareto_incompatibility :
  efx_pareto_incompatibilitySpec := by
  intro n hn r hr
  have hrnonneg : 0 ≤ r := by
    have hrTwo := po_r_gt_two n hn r hr
    linarith
  refine ⟨2 * n + 1, poChoreInstance n r hrnonneg, poCost_is_one_or_r n r, ?_⟩
  intro allocation hfeasible hefx hoptimal
  exact po_efx_not_pareto_optimal n hn r hr allocation hfeasible hefx hoptimal

theorem efx_pareto_construction_has_efx :
  efx_pareto_construction_has_efxSpec := by
  intro n hn r hr
  refine ⟨poEfxWitness n (by omega), poEfxWitness_feasible n (by omega), ?_⟩
  simpa [poCost] using poEfxWitness_is_efx n hn r (po_r_gt_two n hn r hr)

theorem efx_po_every_agent_large :
  efx_po_every_agent_largeSpec := by
  intro n hn r hr allocation halloc hefx agent
  exact po_every_agent_has_large n hn r hr allocation halloc hefx agent

theorem efx_po_cost_lower_bounds :
  efx_po_cost_lower_boundsSpec := by
  intro n hn r hr allocation halloc hefx
  constructor
  · intro agent
    exact po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx agent
  · exact po_some_agent_cost_ge_r_add_two n hn r hr allocation halloc hefx

theorem four_agent_bi_valued_efx_exists :
  four_agent_bi_valued_efx_existsSpec := by
  intro Item choreInstance hbi
  classical
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfBiValuedChoreCost Item choreInstance.cost choreInstance.chores hbi
  exact ⟨allocation, hallocation, hefx⟩

theorem m34_insertion :
  m34_insertionSpec := by
  intro Item r cost chores item hr hcost hitem hsmallThree allocation halloc hefx
  classical
  exact m34InsertionProof Item r cost chores item hr hcost hitem hsmallThree allocation halloc hefx

theorem m34_insertion_general_agents :
  m34_insertion_general_agentsSpec := by
  intro Agent Item _ _ _ _ r cost remaining chores hr hcost hdisjoint hlarge
  constructor
  · intro item hitem allocation halloc hefx
    exact m34InsertionGeneralAgentsProof Agent Item r cost chores item hr hcost
      (by
        intro hitemChores
        exact Finset.disjoint_left.mp hdisjoint hitem hitemChores)
      (hlarge item hitem) allocation halloc hefx
  · intro allocation halloc hefx
    exact m34InsertAllRemainingGeneralAgentsProof Agent Item r cost hr hcost remaining chores
      hdisjoint hlarge allocation halloc hefx

theorem composition :
  compositionSpec := by
  intro Agent Item r cost leftChores rightChores leftAllocation rightAllocation hr hcost hchores
    hleftAllocation hrightAllocation
  classical
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item =>
      AppliedModelingLib.FairDivision.IsOneOrRChoreCost.one_le cost r hcost (by linarith)
        agent item
  have hdisjoint : ∀ agent, Disjoint (leftAllocation agent) (rightAllocation agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleft hright
    exact (Finset.disjoint_left.mp hchores
      (hleftAllocation.1 agent item hleft) (hrightAllocation.1 agent item hright)).elim
  refine ⟨AppliedModelingLib.FairDivision.isAllocationOf_union leftAllocation rightAllocation leftChores
    rightChores hchores hleftAllocation hrightAllocation, ?_⟩
  constructor
  · rintro ⟨hleft, hright⟩
    exact AppliedModelingLib.FairDivision.efxForChores_union_of_envyFree_of_unit_slack
      cost leftAllocation rightAllocation hdisjoint hcostLower hleft hright
  constructor
  · intro hgap
    exact AppliedModelingLib.FairDivision.efxForChores_union_of_cost_gap
      cost leftAllocation rightAllocation hdisjoint hgap
  · intro i j hnonempty hgap
    exact AppliedModelingLib.FairDivision.doesNotStronglyEnvyForChores_union_of_cost_gap
      cost leftAllocation rightAllocation hdisjoint i j hnonempty hgap

theorem canonical_allocation_properties :
  canonical_allocation_propertiesSpec := by
  intro Item r cost chores a b hr hcost hb hchores hsmall
  classical
  have hrOne : 1 ≤ r := by linarith
  obtain ⟨hfair, henvy⟩ :=
    canonicalSmallChoreAllocation_fair Item r cost chores a b hrOne hcost hb hchores hsmall
  refine ⟨hfair, henvy, ?_, ?_⟩
  · intro hbpos
    exact existsSuperCanonicalSmallChoreAllocation Item r cost chores a b hrOne hcost hb hbpos
      hchores hsmall
  · intro hapos hbTwo N1 N2 hunion hdisjoint hN1Card hN2Card
    have hchoresTwo : chores.card = 4 * a + 2 := by omega
    exact existsSuperCanonicalOneShortEachSide Item r cost chores a hapos hrOne hcost hchoresTwo
      hsmall N1 N2 hunion hdisjoint hN1Card hN2Card

theorem balanced_orientation :
  balanced_orientationSpec := by
  intro Vertex Edge _ edges endpoints quota hends
  classical
  exact balancedOrientationProof Vertex Edge edges endpoints quota hends

theorem m2_efx_allocation :
  m2_efx_allocationSpec := by
  unfold m2_efx_allocationSpec
  intro Item r cost chores hr hcost hsmall
  classical
  exact m2EfxAllocationProof Item r cost chores hr hcost hsmall

theorem m2_efx_allocation_properties :
  m2_efx_allocation_propertiesSpec := by
  intro Item r cost chores hr hcost hsmall
  classical
  obtain ⟨allocation, halloc, hefx, hcertificates⟩ :=
    existsEfxOfM2_with_conditionalCertificates Item r cost chores hr hcost hsmall
  refine ⟨allocation, halloc, hefx, ?_, ?_, ?_⟩
  · intro hnotExceptional
    apply hcertificates
    simpa [IsM2Exceptional] using hnotExceptional
  · intro firstType secondType hfirstCard hsecondCard hdisjoint htypes hcount agent hagent
    exact existsEfxOfM2TwoDisjointTypes_preferred Item r cost chores firstType secondType agent
      hr hcost hfirstCard hsecondCard hdisjoint htypes (by simpa using hcount) hagent
  · intro dominant auxiliary q hdominant hauxiliary hdisjoint special hspecial companion hcompanion
      hne hshape
    exact existsExceptionalM2Allocation_sourceSchedule Item r cost chores dominant auxiliary q
      (by linarith) hcost hdominant hauxiliary hdisjoint hshape special companion hspecial
      hcompanion hne

theorem exceptional_residue_combination :
  exceptional_residue_combinationSpec := by
  intro Item r cost prefixChores m2Chores gapChores residueChores a quota prefixAllocation gap
    hr hcost hprefixM2 _hm2Small hgapResidue hgapResidueUnion hcanonical hprefixSmall hquota hgapAllocation
    hgapShort hleftEnvyFree exceptionalI exceptionalJ hexceptional hij hquotaI hquotaJ
  classical
  exact exceptional_residue_combination_proof Item r cost prefixChores m2Chores gapChores residueChores
    a quota prefixAllocation gap hr hcost hprefixM2 hgapResidue hgapResidueUnion hprefixSmall
    hcanonical hquota hgapAllocation hgapShort hleftEnvyFree exceptionalI exceptionalJ hexceptional hij
    hquotaI hquotaJ

theorem appendix_no_two_a_items :
  appendix_no_two_a_itemsSpec := by
  intro n Item r q cost chores A B C allocation hn hq hr hAcard hBcard hCcard hAB hAC hBC
    hpartition hcost halloc hefx agent
  classical
  exact appendix_no_two_A_items_proof n Item r q cost chores A B C allocation hn
    (by simpa [appendixQ, appendixS, appendixT] using hq)
    (by simpa [appendixS, appendixT] using hr)
    hAcard (by simpa [appendixS, appendixT] using hBcard)
    (by simpa [appendixS, appendixT] using hCcard) hAB hAC hBC hpartition hcost halloc hefx agent

theorem appendix_p1_p2_lower_bounds :
  appendix_p1_p2_lower_boundsSpec := by
  intro n Item r q cost chores A B C allocation P1 P2 p1 p2 hn hq hr hAcard hBcard hCcard
    hAB hAC hBC hpartition hcost halloc hefx hP1 hP2 hcostP1 hcostP2 hmin1 hmin1Lower hmin2
    hmin2Lower
  classical
  constructor
  · exact appendix_p1_lower_bound_proof n Item r q cost chores A B C allocation P1 P2 p1 p2 hn
      (by simpa [appendixQ, appendixS, appendixT] using hq)
      (by simpa [appendixS, appendixT] using hr)
      hAcard (by simpa [appendixS, appendixT] using hBcard)
      (by simpa [appendixS, appendixT] using hCcard) hAB hAC hBC hpartition hcost halloc hefx hP1
      hP2 hcostP1 hcostP2 hmin1 hmin2 hmin2Lower
  · exact appendix_p2_lower_bound_proof n Item r q cost chores A B C allocation P1 P2 p1 p2 hn
      (by simpa [appendixQ, appendixS, appendixT] using hq)
      (by simpa [appendixS, appendixT] using hr)
      hAcard (by simpa [appendixS, appendixT] using hBcard)
      (by simpa [appendixS, appendixT] using hCcard) hAB hAC hBC hpartition hcost halloc hefx hP1
      hP2 hcostP1 hcostP2 hmin1 hmin1Lower hmin2

end HT26EFXChores

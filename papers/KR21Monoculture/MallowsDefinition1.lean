import KR21Monoculture.Theorem2Definition1SourceFamilies
import KR21Monoculture.MainTheorems

/-!
# Source-faithful Mallows Definition 1

Theorem 9 in Appendix D claims that the concrete Kendall--Mallows family
satisfies every clause of the paper's Definition 1.  The older family bridge
only supplied the smaller collection of facts needed by Theorem 1.  This file
closes that semantic gap at the literal finite-ranking surface.
-/

open AppliedModelingLib Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped Topology

namespace KR21Monoculture

/-- The positive-domain inverse Mallows parameter is differentiable. -/
theorem mallowsAccuracyQ_differentiableAt_of_pos {theta : ℝ} (htheta : 0 < theta) :
    DifferentiableAt ℝ mallowsAccuracyQ theta := by
  have hlocal : mallowsInverseAccuracyQ =ᶠ[nhds theta] mallowsAccuracyQ := by
    filter_upwards [eventually_gt_nhds htheta] with y hy
    simp [mallowsAccuracyQ, hy]
  have hinverse : DifferentiableAt ℝ mallowsInverseAccuracyQ theta := by
    unfold mallowsInverseAccuracyQ
    exact (differentiableAt_id.add_const 1).inv (by linarith)
  exact hinverse.congr_of_eventuallyEq hlocal.symm

/-- Each concrete Mallows ranking atom is differentiable at positive accuracy. -/
theorem concreteMallowsSpec_atom_differentiable
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking n) :
    DifferentiableAt ℝ
      (fun theta' => (((concreteMallowsSpec center theta').law) pi).toReal)
      theta := by
  have hq_diff : DifferentiableAt ℝ mallowsAccuracyQ theta :=
    mallowsAccuracyQ_differentiableAt_of_pos htheta
  have hnum_diff :
      DifferentiableAt ℝ
        (fun theta' => mallowsWeight (mallowsAccuracyQ theta') center pi) theta := by
    unfold mallowsWeight
    exact hq_diff.pow _
  have hden_diff :
      DifferentiableAt ℝ
        (fun theta' => mallowsPartition (mallowsAccuracyQ theta') center) theta := by
    change DifferentiableAt ℝ
      (fun theta' => ∑ tau : Ranking n,
        (mallowsAccuracyQ theta') ^ kendallTau center tau) theta
    apply DifferentiableAt.fun_sum
    intro tau _
    exact hq_diff.pow _
  have hden_ne : mallowsPartition (mallowsAccuracyQ theta) center ≠ 0 :=
    ne_of_gt (mallowsPartition_pos (hq := mallowsAccuracyQ_pos theta) center)
  have hratio :
      DifferentiableAt ℝ
        (fun theta' =>
          mallowsWeight (mallowsAccuracyQ theta') center pi /
            mallowsPartition (mallowsAccuracyQ theta') center) theta :=
    hnum_diff.div hden_diff hden_ne
  simpa [concreteMallowsSpec, MallowsSpec.ofQ] using hratio

/-- At zero inverse-noise, the finite Mallows partition contains only the center. -/
theorem mallowsPartition_zero {n : ℕ} (center : Ranking n) :
    mallowsPartition 0 center = 1 := by
  classical
  unfold mallowsPartition
  calc
    (∑ pi : Ranking n, mallowsWeight 0 center pi) =
        mallowsWeight 0 center center := by
      refine Finset.sum_eq_single center ?_ ?_
      · intro pi _ hpi
        rcases exists_invertedPair_of_ne hpi with ⟨ab, hab⟩
        have hmem : ab ∈ inversionFinset center pi := by
          simpa [inversionFinset] using hab
        have hpos : 0 < kendallTau center pi := by
          simpa [kendallTau] using Finset.card_pos.mpr ⟨ab, hmem⟩
        unfold mallowsWeight
        exact zero_pow (Nat.ne_of_gt hpos)
      · simp
    _ = 1 := by simp

/-- The concrete inverse Mallows parameter tends to zero as source accuracy grows. -/
theorem mallowsAccuracyQ_tendsto_zero :
    Tendsto mallowsAccuracyQ atTop (nhds 0) := by
  have hinverse : Tendsto mallowsInverseAccuracyQ atTop (nhds 0) := by
    unfold mallowsInverseAccuracyQ
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  refine hinverse.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with theta htheta
  simp [mallowsAccuracyQ, htheta]

/-- The finite Mallows partition tends to one as inverse noise tends to zero. -/
theorem concreteMallowsPartition_tendsto_one {n : ℕ} (center : Ranking n) :
    Tendsto (fun theta => mallowsPartition (mallowsAccuracyQ theta) center)
      atTop (nhds 1) := by
  have hcont : ContinuousAt (fun q : ℝ => mallowsPartition q center) 0 := by
    unfold mallowsPartition
    exact AppliedModelingLib.continuousAt_finset_sum
      (s := (Finset.univ : Finset (Ranking n)))
      (f := fun pi q => mallowsWeight q center pi)
      (fun pi _ => by
        unfold mallowsWeight
        exact continuousAt_id.pow _)
  have hlimit := hcont.tendsto.comp mallowsAccuracyQ_tendsto_zero
  simpa [mallowsPartition_zero] using hlimit

/-- The true-ranking atom of the concrete Mallows family tends to one. -/
theorem concreteMallowsSpec_center_atom_tendsto_one
    {n : ℕ} (center : Ranking n) :
    Tendsto
      (fun theta => (((concreteMallowsSpec center theta).law) center).toReal)
      atTop (nhds 1) := by
  have hpartition := concreteMallowsPartition_tendsto_one center
  have hratio :
      Tendsto
        (fun theta => 1 / mallowsPartition (mallowsAccuracyQ theta) center)
        atTop (nhds (1 / 1)) :=
    Tendsto.div tendsto_const_nhds hpartition one_ne_zero
  have hatom_eq :
      (fun theta => (((concreteMallowsSpec center theta).law) center).toReal) =
        (fun theta => 1 / mallowsPartition (mallowsAccuracyQ theta) center) := by
    funext theta
    simpa [concreteMallowsSpec, MallowsSpec.ofQ] using
      (MallowsSpec.center_mass_toReal_eq_inv_partition
        (M := concreteMallowsSpec center theta))
  simpa [hatom_eq] using hratio

/--
Appendix D / Theorem 9: the concrete Kendall--Mallows family has every literal
Definition 1 field: smooth finite ranking atoms, the true-ranking limit, weak
monotonicity for each nonempty remaining set, and strict full-set improvement.
-/
theorem concreteMallowsAccuracyFamily_sourceDefinition1
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    SourceDefinition1NoisyPermutationFamily
      ({ dist := fun theta => (concreteMallowsSpec center theta).law,
         value := value } : AccuracyFamily n)
      center := by
  refine ⟨?_, concreteMallowsSpec_center_atom_tendsto_one center, ?_⟩
  · intro theta htheta pi
    exact ⟨AppliedModelingLib.continuousAt_of_epsilonContinuousAt
      (concreteMallowsSpec_atom_continuity center htheta pi),
      concreteMallowsSpec_atom_differentiable center htheta pi⟩
  · intro thetaA thetaH hthetaH hthetaHA
    have hq_lt :
        (concreteMallowsSpec center thetaA).q <
          (concreteMallowsSpec center thetaH).q := by
      simpa [concreteMallowsSpec, MallowsSpec.ofQ] using
        mallowsAccuracyQ_strictAnti hthetaH hthetaHA
    constructor
    · intro remaining hremaining
      exact
        MallowsComparison.paper_theorem4_mallows_remaining_utility_dominance_of_q_le
          (human := concreteMallowsSpec center thetaA)
          (algorithm := concreteMallowsSpec center thetaH)
          rfl (le_of_lt hq_lt)
          (weaklyOrderedBy_of_strictlyOrderedBy hvalue) hremaining
    · have hcard : 1 < (Finset.univ : Finset (Candidate n)).card := by
        simp [Candidate]
      exact
        expectedBestInSet_lt_of_mallows_q_lt_card_gt_one
          (Mmore := concreteMallowsSpec center thetaA)
          (Mless := concreteMallowsSpec center thetaH)
          rfl hq_lt hvalue (by simp) hcard

end KR21Monoculture

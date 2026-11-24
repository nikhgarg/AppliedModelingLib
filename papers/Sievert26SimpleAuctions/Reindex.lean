import Sievert26SimpleAuctions.Basic

/-! Item names do not matter: transport along a bijection to `Fin m`. -/
open Finset

namespace Sievert26SimpleAuctions

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem SREV_reindex (D : ι → FinDist) (f : κ ≃ ι) : SREV (fun j => D (f j)) = SREV D :=
  Equiv.sum_comp f (fun i => (D i).rev)

/-- bijection between realisations -/
def profEquiv (D : ι → FinDist) (f : κ ≃ ι) : Profile D ≃ Profile (fun j => D (f j)) :=
  Equiv.piCongrLeft' (fun i => Fin (D i).size) f.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem prob_reindex (D : ι → FinDist) (f : κ ≃ ι) (ω : Profile D) :
    prob (fun j => D (f j)) (profEquiv D f ω) = prob D ω :=
  Equiv.prod_comp f (fun i => (D i).prob (ω i))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem value_reindex (D : ι → FinDist) (f : κ ≃ ι) (ω : Profile D) (j : κ) :
    value (fun j => D (f j)) (profEquiv D f ω) j = value D ω (f j) := rfl

theorem BREV_reindex (D : ι → FinDist) (f : κ ≃ ι) : BREV (fun j => D (f j)) = BREV D := by
  unfold BREV
  congr 2
  funext p
  congr 1
  unfold bundleTail
  symm
  refine Fintype.sum_equiv (profEquiv D f) _ _ fun ω => ?_
  rw [prob_reindex]
  have hs : (∑ j, value (fun j => D (f j)) (profEquiv D f ω) j) = ∑ i, value D ω i :=
    Equiv.sum_comp f (fun i => value D ω i)
  by_cases hc : (p : ℝ) ≤ ∑ i, value D ω i
  · rw [if_pos hc, if_pos (hs.symm ▸ hc)]
  · rw [if_neg hc, if_neg (hs.symm ▸ hc)]

/-- transport of a mechanism -/
def Mechanism.reindex (M : Mechanism ι) (f : κ ≃ ι) : Mechanism κ where
  alloc v j := M.alloc (fun i => v (f.symm i)) (f j)
  pay v := M.pay (fun i => v (f.symm i))
  alloc_nonneg v j := M.alloc_nonneg _ _
  alloc_le_one v j := M.alloc_le_one _ _
  ir v hv := by
    have h := M.ir (fun i => v (f.symm i)) (fun i => hv _)
    rw [← Equiv.sum_comp f] at h
    simpa using h
  ic v v' hv hv' := by
    have h := M.ic (fun i => v (f.symm i)) (fun i => v' (f.symm i)) (fun i => hv _) (fun i => hv' _)
    rw [← Equiv.sum_comp f, ← Equiv.sum_comp f] at h
    simpa using h

theorem rev_reindex (D : ι → FinDist) (f : κ ≃ ι) (M : Mechanism ι) :
    (M.reindex f).rev (fun j => D (f j)) = M.rev D := by
  unfold Mechanism.rev
  symm
  refine Fintype.sum_equiv (profEquiv D f) _ _ fun ω => ?_
  rw [prob_reindex]
  congr 1
  change M.pay (value D ω) =
    M.pay (fun i => value (fun j => D (f j)) (profEquiv D f ω) (f.symm i))
  congr 1
  funext i
  rw [value_reindex]
  exact (congrArg (value D ω) (f.apply_symm_apply i)).symm

instance : Nonempty (Mechanism ι) :=
  ⟨{ alloc := fun _ _ => 0, pay := fun _ => 0
     alloc_nonneg := by simp, alloc_le_one := by simp, ir := by simp, ic := by simp }⟩

theorem REV_le_reindex (D : ι → FinDist) (f : κ ≃ ι) : REV D ≤ REV (fun j => D (f j)) := by
  refine ciSup_le fun M => ?_
  rw [← rev_reindex D f M]
  exact le_REV _ _

theorem exists_fin (D : ι → FinDist) (c : ℝ) (h : c * max (SREV D) (BREV D) < REV D) :
    ∃ (m : ℕ) (D' : Fin m → FinDist), c * max (SREV D') (BREV D') < REV D' := by
  refine ⟨Fintype.card ι, fun j => D ((Fintype.equivFin ι).symm j), ?_⟩
  rw [SREV_reindex, BREV_reindex]
  exact lt_of_lt_of_le h (REV_le_reindex D _)

end Sievert26SimpleAuctions

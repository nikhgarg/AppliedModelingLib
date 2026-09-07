import AppliedModelingLib.SocialChoice.Ranking.Mallows
import AppliedModelingLib.SocialChoice.Ranking.RankPower

/-!
# Mallows Rank Factorization

Assumption-driven rank-factorization API for finite Mallows laws.  Concrete
papers may construct this package from source-specific fiber decompositions;
the algebra in this file only consumes the package.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/-- Unnormalised first-choice Mallows kernel for a raw center and parameter. -/
noncomputable def firstWeightKernel
    {n : ℕ} (q : ℝ) (ρ : Ranking n) (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π then mallowsWeight q ρ π else 0

/-- Unnormalised first/second-choice Mallows kernel for a raw center and parameter. -/
noncomputable def firstSecondWeightKernel
    {n : ℕ} (q : ℝ) (ρ : Ranking n) (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π ∧ d = secondChoice π
    then mallowsWeight q ρ π
    else 0

/-- Canonical first-choice tail for the raw Mallows kernel. -/
noncomputable def firstTailKernel (n : ℕ) (q : ℝ) : ℝ :=
  ∑ τ : Ranking n,
    if firstChoice τ = (0 : Candidate n)
    then mallowsWeight q (Equiv.refl (Candidate n)) τ
    else 0

/-- Canonical first/second-choice tail for the raw Mallows kernel. -/
noncomputable def firstSecondTailKernel (n : ℕ) (q : ℝ) : ℝ :=
  ∑ τ : Ranking n,
    if firstChoice τ = (0 : Candidate n) ∧ secondChoice τ = (1 : Candidate n)
    then mallowsWeight q (Equiv.refl (Candidate n)) τ
    else 0

theorem firstSecondTailKernel_pos {q : ℝ} (hq_pos : 0 < q) :
    0 < firstSecondTailKernel n q := by
  classical
  unfold firstSecondTailKernel
  refine Finset.sum_pos' ?_ ?_
  · intro τ _
    by_cases hτ : τ 0 = (0 : Candidate n) ∧ τ 1 = (1 : Candidate n)
    · simp [hτ, firstChoice, secondChoice, mallowsWeight,
        pow_nonneg (le_of_lt hq_pos)]
    · simp [hτ, firstChoice, secondChoice]
  · refine ⟨Equiv.refl (Candidate n), Finset.mem_univ _, ?_⟩
    simp [firstChoice, secondChoice, mallowsWeight]

/--
Canonical first-choice tail after normalizing the Mallows center to the identity.
It is the common residual mass that remains after fixing the first candidate.
-/
noncomputable def firstTailCanonical : ℝ :=
  firstTailKernel n M.q

theorem firstTailCanonical_pos :
    0 < M.firstTailCanonical := by
  classical
  unfold firstTailCanonical
  refine Finset.sum_pos' ?_ ?_
  · intro τ _
    by_cases hτ : τ 0 = (0 : Candidate n)
    · simp [hτ, mallowsWeight, pow_nonneg (le_of_lt M.q_pos)]
    · simp [hτ]
  · refine ⟨Equiv.refl (Candidate n), Finset.mem_univ _, ?_⟩
    simp [firstChoice, mallowsWeight]

private theorem firstChoice_trans_center_eq_iff
    (ρ : Ranking n) (c : Candidate n) (τ : Ranking n) :
    c = firstChoice (τ.trans ρ) ↔
      firstChoice τ = rankOf ρ c := by
  constructor
  · intro h
    have h' := congrArg ρ.symm h
    simpa [firstChoice, rankOf] using h'.symm
  · intro h
    have hc : ρ (rankOf ρ c) = c := by
      simp [rankOf]
    rw [firstChoice_trans, h, hc]

private theorem secondChoice_trans_center_eq_iff
    (ρ : Ranking n) (c : Candidate n) (τ : Ranking n) :
    c = secondChoice (τ.trans ρ) ↔
      secondChoice τ = rankOf ρ c := by
  constructor
  · intro h
    have h' := congrArg ρ.symm h
    simpa [secondChoice, rankOf] using h'.symm
  · intro h
    have hc : ρ (rankOf ρ c) = c := by
      simp [rankOf]
    rw [secondChoice_trans, h, hc]

private theorem firstChoice_trans_cycleRange_symm_eq_iff
    (k : Candidate n) (σ : Ranking n) :
    firstChoice (σ.trans (Fin.cycleRange k).symm) = k ↔
      firstChoice σ = (0 : Candidate n) := by
  constructor
  · intro h
    have h' := congrArg (Fin.cycleRange k) h
    simpa [firstChoice, Fin.cycleRange_self] using h'
  · intro h
    rw [firstChoice_trans, h]
    apply (Fin.cycleRange k).injective
    simp [Fin.cycleRange_self]

private theorem secondChoice_trans_cycleRange_symm_eq_iff
    (k l : Candidate n) (σ : Ranking n) :
    secondChoice (σ.trans (Fin.cycleRange k).symm) = l ↔
      secondChoice σ = Fin.cycleRange k l := by
  constructor
  · intro h
    have h' := congrArg (Fin.cycleRange k) h
    simpa [secondChoice] using h'
  · intro h
    rw [secondChoice_trans, h]
    simp

private theorem trans_cycleRange_symm_trans_cycleRange
    (k : Candidate n) (σ : Ranking n) :
    (σ.trans (Fin.cycleRange k).symm).trans (Fin.cycleRange k) = σ := by
  ext i
  simp

private theorem kendallTau_refl_trans_cycleRange_symm_of_first_zero
    (k : Candidate n) (σ : Ranking n)
    (hσ : firstChoice σ = (0 : Candidate n)) :
    kendallTau (Equiv.refl (Candidate n))
        (σ.trans (Fin.cycleRange k).symm) =
      (k : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
  let τ : Ranking n := σ.trans (Fin.cycleRange k).symm
  have hfirst : firstChoice τ = k := by
    exact (firstChoice_trans_cycleRange_symm_eq_iff k σ).2 hσ
  have h := kendallTau_eq_firstChoice_add_cycleRange τ
  rw [hfirst, trans_cycleRange_symm_trans_cycleRange] at h
  simpa [τ] using h

private theorem firstChoice_trans_cycleIcc_one_symm_eq_zero_iff
    (s : Candidate n) (σ : Ranking n) :
    firstChoice (σ.trans (Fin.cycleIcc (1 : Candidate n) s).symm) =
        (0 : Candidate n) ↔
      firstChoice σ = (0 : Candidate n) := by
  have h01 : (0 : Candidate n) < (1 : Candidate n) := by
    change (0 : ℕ) < 1
    omega
  constructor
  · intro h
    have h' := congrArg (Fin.cycleIcc (1 : Candidate n) s) h
    simpa [firstChoice, Fin.cycleIcc_of_lt h01] using h'
  · intro h
    rw [firstChoice_trans, h]
    apply (Fin.cycleIcc (1 : Candidate n) s).injective
    simp [Fin.cycleIcc_of_lt h01]

private theorem secondChoice_trans_cycleIcc_one_symm_eq_iff
    (s : Candidate n) (σ : Ranking n) (hs1 : (1 : Candidate n) ≤ s) :
    secondChoice (σ.trans (Fin.cycleIcc (1 : Candidate n) s).symm) = s ↔
      secondChoice σ = (1 : Candidate n) := by
  constructor
  · intro h
    have h' := congrArg (Fin.cycleIcc (1 : Candidate n) s) h
    simpa [secondChoice, Fin.cycleIcc_of_last hs1] using h'
  · intro h
    rw [secondChoice_trans, h]
    apply (Fin.cycleIcc (1 : Candidate n) s).injective
    simp [Fin.cycleIcc_of_last hs1]

private theorem trans_cycleIcc_one_symm_trans_cycleIcc_one
    (s : Candidate n) (σ : Ranking n) :
    (σ.trans (Fin.cycleIcc (1 : Candidate n) s).symm).trans
        (Fin.cycleIcc (1 : Candidate n) s) = σ := by
  ext i
  simp

private theorem kendallTau_refl_trans_cycleIcc_one_symm_of_first_zero_second_one
    (s : Candidate n) (σ : Ranking n)
    (hfirst : firstChoice σ = (0 : Candidate n))
    (hsecond : secondChoice σ = (1 : Candidate n))
    (hs1 : (1 : Candidate n) ≤ s) :
    kendallTau (Equiv.refl (Candidate n))
        (σ.trans (Fin.cycleIcc (1 : Candidate n) s).symm) =
      (s : ℕ) - 1 + kendallTau (Equiv.refl (Candidate n)) σ := by
  let τ : Ranking n := σ.trans (Fin.cycleIcc (1 : Candidate n) s).symm
  have hfirstτ : firstChoice τ = (0 : Candidate n) := by
    exact (firstChoice_trans_cycleIcc_one_symm_eq_zero_iff s σ).2 hfirst
  have hsecondτ : secondChoice τ = s := by
    exact (secondChoice_trans_cycleIcc_one_symm_eq_iff s σ hs1).2 hsecond
  have h := kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one τ hfirstτ
  rw [hsecondτ, trans_cycleIcc_one_symm_trans_cycleIcc_one] at h
  simpa [τ] using h

/--
Raw-kernel version of the first-choice factorization: fixing the first
candidate at center rank `r` contributes a factor `q^r` times the canonical
tail.
-/
theorem firstWeightKernel_eq_rank_pow_mul_firstTailKernel
    {q : ℝ} (hq_pos : 0 < q) (ρ : Ranking n) (c : Candidate n) :
    firstWeightKernel q ρ c =
      q ^ (rankOf ρ c : ℕ) * firstTailKernel n q := by
  classical
  let k : Candidate n := rankOf ρ c
  let E : Ranking n := (Fin.cycleRange k).symm
  unfold firstWeightKernel firstTailKernel mallowsWeight
  calc
    (∑ π : Ranking n,
        if c = firstChoice π
        then q ^ kendallTau ρ π
        else 0)
        =
      ∑ τ : Ranking n,
        if c = firstChoice (τ.trans ρ)
        then q ^ kendallTau ρ (τ.trans ρ)
        else 0 := by
          simpa using
            (Equiv.sum_comp (rankingRightTransEquiv ρ)
              (fun π : Ranking n =>
                if c = firstChoice π
                then q ^ kendallTau ρ π
                else 0)).symm
    _ =
      ∑ τ : Ranking n,
        if firstChoice τ = k
        then q ^ kendallTau (Equiv.refl (Candidate n)) τ
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          have hiff :
              c = firstChoice (τ.trans ρ) ↔
                firstChoice τ = k := by
            simpa [k] using firstChoice_trans_center_eq_iff ρ c τ
          have hkendall :
              kendallTau ρ (τ.trans ρ) =
                kendallTau (Equiv.refl (Candidate n)) τ :=
            kendallTau_center_trans ρ τ
          by_cases hτ : firstChoice τ = k
          · rw [if_pos ((hiff).2 hτ), if_pos hτ, hkendall]
          · rw [if_neg (by intro h; exact hτ ((hiff).1 h)), if_neg hτ]
    _ =
      ∑ σ : Ranking n,
        if firstChoice (σ.trans E) = k
        then q ^ kendallTau (Equiv.refl (Candidate n)) (σ.trans E)
        else 0 := by
          simpa [E] using
            (Equiv.sum_comp (rankingRightTransEquiv E)
              (fun τ : Ranking n =>
                if firstChoice τ = k
                then q ^ kendallTau (Equiv.refl (Candidate n)) τ
                else 0)).symm
    _ =
      ∑ σ : Ranking n,
        q ^ (k : ℕ) *
          (if firstChoice σ = (0 : Candidate n)
           then q ^ kendallTau (Equiv.refl (Candidate n)) σ
           else 0) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hiff :
              firstChoice (σ.trans E) = k ↔
                firstChoice σ = (0 : Candidate n) := by
            simpa [E] using
              firstChoice_trans_cycleRange_symm_eq_iff k σ
          by_cases hσ : firstChoice σ = (0 : Candidate n)
          · have hkendall :
                kendallTau (Equiv.refl (Candidate n)) (σ.trans E) =
                  (k : ℕ) +
                    kendallTau (Equiv.refl (Candidate n)) σ := by
              simpa [E] using
                kendallTau_refl_trans_cycleRange_symm_of_first_zero
                  k σ hσ
            rw [if_pos (hiff.2 hσ), if_pos hσ, hkendall, pow_add]
          · rw [if_neg (by intro h; exact hσ (hiff.1 h)), if_neg hσ]
            ring
    _ =
      q ^ (k : ℕ) *
        ∑ σ : Ranking n,
          if firstChoice σ = (0 : Candidate n)
          then q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else 0 := by
          rw [Finset.mul_sum]
    _ =
      q ^ (rankOf ρ c : ℕ) *
        ∑ σ : Ranking n,
          if firstChoice σ = (0 : Candidate n)
          then q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else 0 := by
          rfl

/-- Raw first-choice fibers partition the raw Mallows partition function. -/
theorem sum_firstWeightKernel_eq_mallowsPartition
    (q : ℝ) (ρ : Ranking n) :
    (∑ c : Candidate n, firstWeightKernel q ρ c) =
      mallowsPartition q ρ := by
  classical
  unfold firstWeightKernel mallowsPartition
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro π _
  have hsum :
      (∑ c : Candidate n,
        if c = firstChoice π then mallowsWeight q ρ π else 0) =
        mallowsWeight q ρ π := by
    simpa using
      (Finset.sum_ite_eq' Finset.univ (firstChoice π)
        (fun _ : Candidate n => mallowsWeight q ρ π))
  rw [hsum]

/-- Raw Mallows partitions factor through the canonical first-choice tail. -/
theorem mallowsPartition_eq_rankPowerSum_mul_firstTailKernel
    {q : ℝ} (hq_pos : 0 < q) (ρ : Ranking n) :
    mallowsPartition q ρ =
      candidateRankPowerSum n q * firstTailKernel n q := by
  classical
  rw [← sum_firstWeightKernel_eq_mallowsPartition (n := n) q ρ]
  calc
    (∑ c : Candidate n, firstWeightKernel q ρ c)
        =
      ∑ c : Candidate n,
        q ^ (rankOf ρ c : ℕ) * firstTailKernel n q := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [firstWeightKernel_eq_rank_pow_mul_firstTailKernel hq_pos ρ c]
    _ =
      ∑ r : Candidate n,
        q ^ (r : ℕ) * firstTailKernel n q := by
          simpa [rankOf] using
            (Equiv.sum_comp ρ.symm
              (fun r : Candidate n =>
                q ^ (r : ℕ) * firstTailKernel n q))
    _ =
      candidateRankPowerSum n q * firstTailKernel n q := by
          unfold candidateRankPowerSum
          rw [Finset.sum_mul]

/--
Raw-kernel first/second fiber factorization.  The first chosen candidate
contributes its center rank, and the second contributes its normalized rank
after the first rank is cycled to the top.
-/
theorem firstSecondWeightKernel_eq_rank_cycleRange
    (q : ℝ) (ρ : Ranking n) {c d : Candidate n} (hcd : c ≠ d) :
    firstSecondWeightKernel q ρ c d =
      q ^ ((rankOf ρ c : ℕ) +
          (Fin.cycleRange (rankOf ρ c) (rankOf ρ d) : ℕ) - 1) *
        firstSecondTailKernel n q := by
  classical
  let k : Candidate n := rankOf ρ c
  let l : Candidate n := rankOf ρ d
  let s : Candidate n := Fin.cycleRange k l
  let E₁ : Ranking n := (Fin.cycleRange k).symm
  let E₂ : Ranking n := (Fin.cycleIcc (1 : Candidate n) s).symm
  have hkl_ne : k ≠ l := by
    intro hkl
    apply hcd
    have hcenter : ρ k = ρ l := by rw [hkl]
    simpa [k, l, rankOf] using hcenter
  have hs_ne_zero : s ≠ (0 : Candidate n) := by
    intro hs0
    have hcycle :
        Fin.cycleRange k l = Fin.cycleRange k k := by
      simp [s, hs0, Fin.cycleRange_self]
    exact hkl_ne ((Fin.cycleRange k).injective hcycle.symm)
  have hs1 : (1 : Candidate n) ≤ s := one_le_of_ne_zero hs_ne_zero
  unfold firstSecondWeightKernel firstSecondTailKernel mallowsWeight
  calc
    (∑ π : Ranking n,
        if c = firstChoice π ∧ d = secondChoice π
        then q ^ kendallTau ρ π
        else 0)
        =
      ∑ τ : Ranking n,
        if c = firstChoice (τ.trans ρ) ∧ d = secondChoice (τ.trans ρ)
        then q ^ kendallTau ρ (τ.trans ρ)
        else 0 := by
          simpa using
            (Equiv.sum_comp (rankingRightTransEquiv ρ)
              (fun π : Ranking n =>
                if c = firstChoice π ∧ d = secondChoice π
                then q ^ kendallTau ρ π
                else 0)).symm
    _ =
      ∑ τ : Ranking n,
        if firstChoice τ = k ∧ secondChoice τ = l
        then q ^ kendallTau (Equiv.refl (Candidate n)) τ
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          have hfirst :
              c = firstChoice (τ.trans ρ) ↔
                firstChoice τ = k := by
            simpa [k] using firstChoice_trans_center_eq_iff ρ c τ
          have hsecond :
              d = secondChoice (τ.trans ρ) ↔
                secondChoice τ = l := by
            simpa [l] using secondChoice_trans_center_eq_iff ρ d τ
          have hkendall :
              kendallTau ρ (τ.trans ρ) =
                kendallTau (Equiv.refl (Candidate n)) τ :=
            kendallTau_center_trans ρ τ
          by_cases hτ : firstChoice τ = k ∧ secondChoice τ = l
          · rw [if_pos ⟨hfirst.2 hτ.1, hsecond.2 hτ.2⟩,
              if_pos hτ, hkendall]
          · rw [if_neg (by
              intro h
              exact hτ ⟨hfirst.1 h.1, hsecond.1 h.2⟩), if_neg hτ]
    _ =
      ∑ σ : Ranking n,
        if firstChoice (σ.trans E₁) = k ∧ secondChoice (σ.trans E₁) = l
        then q ^ kendallTau (Equiv.refl (Candidate n)) (σ.trans E₁)
        else 0 := by
          simpa [E₁] using
            (Equiv.sum_comp (rankingRightTransEquiv E₁)
              (fun τ : Ranking n =>
                if firstChoice τ = k ∧ secondChoice τ = l
                then q ^ kendallTau (Equiv.refl (Candidate n)) τ
                else 0)).symm
    _ =
      ∑ σ : Ranking n,
        q ^ (k : ℕ) *
          (if firstChoice σ = (0 : Candidate n) ∧ secondChoice σ = s
           then q ^ kendallTau (Equiv.refl (Candidate n)) σ
           else 0) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hfirst :
              firstChoice (σ.trans E₁) = k ↔
                firstChoice σ = (0 : Candidate n) := by
            simpa [E₁] using firstChoice_trans_cycleRange_symm_eq_iff k σ
          have hsecond :
              secondChoice (σ.trans E₁) = l ↔
                secondChoice σ = s := by
            simpa [E₁, s] using secondChoice_trans_cycleRange_symm_eq_iff k l σ
          by_cases hσ : firstChoice σ = (0 : Candidate n) ∧ secondChoice σ = s
          · have hkendall :
                kendallTau (Equiv.refl (Candidate n)) (σ.trans E₁) =
                  (k : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
              simpa [E₁] using
                kendallTau_refl_trans_cycleRange_symm_of_first_zero
                  k σ hσ.1
            rw [if_pos ⟨hfirst.2 hσ.1, hsecond.2 hσ.2⟩,
              if_pos hσ, hkendall, pow_add]
          · rw [if_neg (by
              intro h
              exact hσ ⟨hfirst.1 h.1, hsecond.1 h.2⟩), if_neg hσ]
            ring
    _ =
      q ^ (k : ℕ) *
        ∑ σ : Ranking n,
          if firstChoice σ = (0 : Candidate n) ∧ secondChoice σ = s
          then q ^ kendallTau (Equiv.refl (Candidate n)) σ
          else 0 := by
          rw [Finset.mul_sum]
    _ =
      q ^ (k : ℕ) *
        ∑ ζ : Ranking n,
          if firstChoice (ζ.trans E₂) = (0 : Candidate n) ∧
              secondChoice (ζ.trans E₂) = s
          then q ^ kendallTau (Equiv.refl (Candidate n)) (ζ.trans E₂)
          else 0 := by
          congr 1
          simpa [E₂] using
            (Equiv.sum_comp (rankingRightTransEquiv E₂)
              (fun σ : Ranking n =>
                if firstChoice σ = (0 : Candidate n) ∧ secondChoice σ = s
                then q ^ kendallTau (Equiv.refl (Candidate n)) σ
                else 0)).symm
    _ =
      q ^ ((k : ℕ) + (s : ℕ) - 1) *
        ∑ ζ : Ranking n,
          if firstChoice ζ = (0 : Candidate n) ∧
              secondChoice ζ = (1 : Candidate n)
          then q ^ kendallTau (Equiv.refl (Candidate n)) ζ
          else 0 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro ζ _
          have hfirst :
              firstChoice (ζ.trans E₂) = (0 : Candidate n) ↔
                firstChoice ζ = (0 : Candidate n) := by
            simpa [E₂] using
              firstChoice_trans_cycleIcc_one_symm_eq_zero_iff s ζ
          have hsecond :
              secondChoice (ζ.trans E₂) = s ↔
                secondChoice ζ = (1 : Candidate n) := by
            simpa [E₂] using
              secondChoice_trans_cycleIcc_one_symm_eq_iff s ζ hs1
          by_cases hζ :
              firstChoice ζ = (0 : Candidate n) ∧
                secondChoice ζ = (1 : Candidate n)
          · have hkendall :
                kendallTau (Equiv.refl (Candidate n)) (ζ.trans E₂) =
                  (s : ℕ) - 1 +
                    kendallTau (Equiv.refl (Candidate n)) ζ := by
              simpa [E₂] using
                kendallTau_refl_trans_cycleIcc_one_symm_of_first_zero_second_one
                  s ζ hζ.1 hζ.2 hs1
            rw [if_pos ⟨hfirst.2 hζ.1, hsecond.2 hζ.2⟩,
              if_pos hζ, hkendall]
            have hpow :
                q ^ (k : ℕ) *
                    q ^ ((s : ℕ) - 1 +
                      kendallTau (Equiv.refl (Candidate n)) ζ) =
                  q ^ ((k : ℕ) + (s : ℕ) - 1) *
                    q ^ kendallTau (Equiv.refl (Candidate n)) ζ := by
              have hnat :
                  (k : ℕ) + ((s : ℕ) - 1 +
                    kendallTau (Equiv.refl (Candidate n)) ζ) =
                    ((k : ℕ) + (s : ℕ) - 1) +
                      kendallTau (Equiv.refl (Candidate n)) ζ := by
                have hs1_nat : (1 : ℕ) ≤ (s : ℕ) := hs1
                omega
              rw [← pow_add, hnat, pow_add]
            exact hpow
          · rw [if_neg (by
              intro h
              exact hζ ⟨hfirst.1 h.1, hsecond.1 h.2⟩), if_neg hζ]
            ring
    _ =
      q ^ ((rankOf ρ c : ℕ) +
          (Fin.cycleRange (rankOf ρ c) (rankOf ρ d) : ℕ) - 1) *
        ∑ ζ : Ranking n,
          if firstChoice ζ = (0 : Candidate n) ∧
              secondChoice ζ = (1 : Candidate n)
          then q ^ kendallTau (Equiv.refl (Candidate n)) ζ
          else 0 := by
          rfl

/-- Ordered top-two Mallows fiber factorization for a center-ordered pair. -/
theorem firstSecondWeightKernel_eq_of_lt
    (q : ℝ) (ρ : Ranking n) {c d : Candidate n}
    (hcd : rankOf ρ c < rankOf ρ d) :
    firstSecondWeightKernel q ρ c d =
      q ^ ((rankOf ρ c : ℕ) + (rankOf ρ d : ℕ) - 1) *
        firstSecondTailKernel n q := by
  have hne : c ≠ d := by
    intro h
    rw [h] at hcd
    exact (lt_irrefl (rankOf ρ d)) hcd
  rw [firstSecondWeightKernel_eq_rank_cycleRange q ρ hne]
  rw [Fin.cycleRange_of_gt hcd]

/--
Swapped top-two Mallows fiber factorization for a center-ordered pair.  The
swapped order has one additional Mallows factor `q`.
-/
theorem firstSecondWeightKernel_swap_eq_of_lt
    (q : ℝ) (ρ : Ranking n) {c d : Candidate n}
    (hcd : rankOf ρ c < rankOf ρ d) :
    firstSecondWeightKernel q ρ d c =
      q *
        (q ^ ((rankOf ρ c : ℕ) + (rankOf ρ d : ℕ) - 1) *
          firstSecondTailKernel n q) := by
  have hne : d ≠ c := by
    intro h
    rw [h] at hcd
    exact (lt_irrefl (rankOf ρ c)) hcd
  rw [firstSecondWeightKernel_eq_rank_cycleRange q ρ hne]
  rw [Fin.cycleRange_of_lt hcd]
  have hsucc :
      (((rankOf ρ c + 1 : Candidate n)) : ℕ) =
        (rankOf ρ c : ℕ) + 1 :=
    candidate_val_add_one_of_lt hcd
  rw [hsucc]
  have hpow :
      q ^ ((rankOf ρ d : ℕ) + ((rankOf ρ c : ℕ) + 1) - 1) =
        q * q ^ ((rankOf ρ c : ℕ) + (rankOf ρ d : ℕ) - 1) := by
    have hnat :
        (rankOf ρ d : ℕ) + ((rankOf ρ c : ℕ) + 1) - 1 =
          ((rankOf ρ c : ℕ) + (rankOf ρ d : ℕ) - 1) + 1 := by
      have hcd_nat : (rankOf ρ c : ℕ) < (rankOf ρ d : ℕ) := hcd
      omega
    rw [hnat, pow_succ']
  rw [hpow]
  ring

/--
The first-choice fiber of a finite Mallows law factors as `q^r` times a
canonical tail, where `r` is the center rank of the chosen candidate.
-/
theorem firstWeight_eq_rank_pow_mul_firstTailCanonical
    (c : Candidate n) :
    M.firstWeight c =
      M.q ^ (rankOf M.center c : ℕ) * M.firstTailCanonical := by
  rw [show M.firstWeight c = firstWeightKernel M.q M.center c by
    unfold firstWeightKernel firstWeight
    rfl]
  exact firstWeightKernel_eq_rank_pow_mul_firstTailKernel M.q_pos M.center c

/-- The partition also factors through the canonical first-choice tail. -/
theorem partition_eq_rankPowerSum_mul_firstTailCanonical :
    M.partition =
      candidateRankPowerSum n M.q * M.firstTailCanonical := by
  classical
  rw [← M.sum_firstWeight_eq_partition]
  calc
    (∑ c : Candidate n, M.firstWeight c)
        =
      ∑ c : Candidate n,
        M.q ^ (rankOf M.center c : ℕ) * M.firstTailCanonical := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstWeight_eq_rank_pow_mul_firstTailCanonical c]
    _ =
      ∑ r : Candidate n,
        M.q ^ (r : ℕ) * M.firstTailCanonical := by
          simpa [rankOf] using
            (Equiv.sum_comp M.center.symm
              (fun r : Candidate n =>
                M.q ^ (r : ℕ) * M.firstTailCanonical))
    _ =
      candidateRankPowerSum n M.q * M.firstTailCanonical := by
          unfold candidateRankPowerSum
          rw [Finset.sum_mul]

/--
First-choice probabilities in a finite Mallows law are normalized geometric
rank powers in the center ranking.
-/
theorem firstChoiceProb_eq_rank_pow_div_rankPowerSum
    (c : Candidate n) :
    firstChoiceProb M.law c =
      M.q ^ (rankOf M.center c : ℕ) / candidateRankPowerSum n M.q := by
  rw [M.firstChoiceProb_eq_firstWeight_div_partition]
  rw [M.firstWeight_eq_rank_pow_mul_firstTailCanonical c,
    M.partition_eq_rankPowerSum_mul_firstTailCanonical]
  have htail : M.firstTailCanonical ≠ 0 :=
    ne_of_gt M.firstTailCanonical_pos
  have hsum : candidateRankPowerSum n M.q ≠ 0 :=
    ne_of_gt (candidateRankPowerSum_pos n M.q_pos)
  field_simp [htail, hsum]

/--
Closed-form rank factorization for the first and top-two Mallows weights.

For a Mallows law centered at `M.center`, the top-candidate fiber at center rank
`r` has a factor `M.q^r`, and the ordered top-two fiber for center ranks
`r < s` has a factor `M.q^(r+s-1)` while the swapped order has one extra factor
of `M.q`.
-/
structure RankFactorization where
  firstTail : ℝ
  firstSecondTail : ℝ
  firstTail_pos : 0 < firstTail
  firstSecondTail_pos : 0 < firstSecondTail
  partition_eq :
    M.partition = candidateRankPowerSum n M.q * firstTail
  firstWeight_eq :
    ∀ c : Candidate n,
      M.firstWeight c = M.q ^ (rankOf M.center c : ℕ) * firstTail
  firstSecondWeight_eq_of_lt :
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      M.firstSecondWeight c d =
        M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
          firstSecondTail
  firstSecondWeight_swap_eq_of_lt :
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      M.firstSecondWeight d c =
        M.q *
          (M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
            firstSecondTail)

/--
The unordered top-two fiber for two distinct candidates has a symmetric
rank-factorized form.  The two possible top-two orders differ by exactly one
factor of `q`.
-/
theorem firstSecondWeight_add_swap_eq_rank_sum
    (fac : M.RankFactorization) {c d : Candidate n} (hcd : c ≠ d) :
    M.firstSecondWeight c d + M.firstSecondWeight d c =
      (1 + M.q) *
        (M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
          fac.firstSecondTail) := by
  have hrank_ne : rankOf M.center c ≠ rankOf M.center d := by
    intro h
    apply hcd
    have happly := congrArg M.center h
    simpa [rankOf] using happly
  rcases lt_or_gt_of_ne hrank_ne with hlt | hgt
  · rw [fac.firstSecondWeight_eq_of_lt c d hlt]
    rw [fac.firstSecondWeight_swap_eq_of_lt c d hlt]
    ring
  · rw [fac.firstSecondWeight_swap_eq_of_lt d c hgt]
    rw [fac.firstSecondWeight_eq_of_lt d c hgt]
    have hpow :
        M.q ^ ((rankOf M.center d : ℕ) + (rankOf M.center c : ℕ) - 1) =
          M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) := by
      congr 1
      omega
    rw [hpow]
    ring

/-- Canonical finite Mallows rank factorization. -/
noncomputable def rankFactorization : M.RankFactorization where
  firstTail := firstTailKernel n M.q
  firstSecondTail := firstSecondTailKernel n M.q
  firstTail_pos := by
    simpa [firstTailCanonical] using M.firstTailCanonical_pos
  firstSecondTail_pos := firstSecondTailKernel_pos M.q_pos
  partition_eq := by
    simpa [firstTailCanonical] using M.partition_eq_rankPowerSum_mul_firstTailCanonical
  firstWeight_eq := by
    intro c
    simpa [firstTailCanonical] using M.firstWeight_eq_rank_pow_mul_firstTailCanonical c
  firstSecondWeight_eq_of_lt := by
    intro c d hcd
    rw [show M.firstSecondWeight c d =
        firstSecondWeightKernel M.q M.center c d by
      unfold firstSecondWeightKernel firstSecondWeight
      rfl]
    exact firstSecondWeightKernel_eq_of_lt M.q M.center hcd
  firstSecondWeight_swap_eq_of_lt := by
    intro c d hcd
    rw [show M.firstSecondWeight d c =
        firstSecondWeightKernel M.q M.center d c by
      unfold firstSecondWeightKernel firstSecondWeight
      rfl]
    exact firstSecondWeightKernel_swap_eq_of_lt M.q M.center hcd

/--
Under the rank factorization, the first-choice tail is the top-two tail times
the rank-power partition of the remaining candidates after any fixed candidate
is removed from first position.
-/
theorem firstTail_eq_firstSecondTail_mul_removalPowerSum
    (fac : M.RankFactorization) (c : Candidate n) :
    fac.firstTail =
      fac.firstSecondTail *
        candidateRankRemovalPowerSum n M.q (rankOf M.center c) := by
  classical
  let k : Candidate n := rankOf M.center c
  have hc_center : M.center k = c := by
    simp [k, rankOf]
  have hsum_center :
      (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) =
        M.firstWeight c := by
    have hcomp :
        (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) =
          ∑ d : Candidate n, M.firstSecondWeight c d := by
      simpa using
        (Equiv.sum_comp M.center
          (fun d : Candidate n => M.firstSecondWeight c d))
    rw [hcomp, M.sum_firstSecondWeight_right_eq_firstWeight c]
  have hleft :
      (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) =
        M.q ^ (k : ℕ) * fac.firstSecondTail *
          candidateRankRemovalPowerSum n M.q k := by
    unfold candidateRankRemovalPowerSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    by_cases hrk : r < k
    · have hlt : rankOf M.center (M.center r) < rankOf M.center c := by
        simpa [k, rankOf] using hrk
      have hpow :
          M.q *
              (M.q ^ ((r : ℕ) + (k : ℕ) - 1) *
                fac.firstSecondTail) =
            M.q ^ (k : ℕ) * fac.firstSecondTail * M.q ^ (r : ℕ) := by
        have hsum :
            ((r : ℕ) + (k : ℕ) - 1) + 1 = (k : ℕ) + (r : ℕ) := by
          have hrk_nat : (r : ℕ) < (k : ℕ) := hrk
          omega
        rw [← mul_assoc M.q (M.q ^ ((r : ℕ) + (k : ℕ) - 1))
          fac.firstSecondTail]
        rw [← pow_succ', hsum, pow_add]
        ring
      rw [fac.firstSecondWeight_swap_eq_of_lt (M.center r) c hlt]
      rw [← hc_center]
      have hrk' : r < rankOf M.center c := by
        simpa [k] using hrk
      rw [if_pos hrk']
      simp [rankOf]
      exact hpow
    · by_cases hkr : k < r
      · have hlt : rankOf M.center c < rankOf M.center (M.center r) := by
          simpa [k, rankOf] using hkr
        have hpow :
            M.q ^ ((k : ℕ) + (r : ℕ) - 1) * fac.firstSecondTail =
              M.q ^ (k : ℕ) * fac.firstSecondTail * M.q ^ ((r : ℕ) - 1) := by
          have hsum :
              (k : ℕ) + (r : ℕ) - 1 = (k : ℕ) + ((r : ℕ) - 1) := by
            have hkr_nat : (k : ℕ) < (r : ℕ) := hkr
            omega
          rw [hsum, pow_add]
          ring
        rw [fac.firstSecondWeight_eq_of_lt c (M.center r) hlt]
        have hkr' : rankOf M.center c < r := by
          simpa [k] using hkr
        have hrk' : ¬r < rankOf M.center c := by
          simpa [k] using hrk
        rw [if_neg hrk', if_pos hkr']
        simp [rankOf]
        exact hpow
      · have hr_eq : r = k := le_antisymm (le_of_not_gt hkr) (le_of_not_gt hrk)
        subst r
        have hself : M.firstSecondWeight c c = 0 := by
          unfold firstSecondWeight
          apply Finset.sum_eq_zero
          intro π _
          have hnot : ¬(c = firstChoice π ∧ c = secondChoice π) := by
            intro h
            have hfs : firstChoice π = secondChoice π := h.1.symm.trans h.2
            exact firstChoice_ne_secondChoice π hfs
          have hraw : ¬(c = π 0 ∧ c = π 1) := by
            intro h
            apply hnot
            exact ⟨by simpa [firstChoice] using h.1,
              by simpa [secondChoice] using h.2⟩
          simp [firstChoice, secondChoice, hraw]
        simpa [hc_center] using hself
  have hright :
      M.firstWeight c = M.q ^ (k : ℕ) * fac.firstTail := by
    rw [fac.firstWeight_eq c]
  have hqk : M.q ^ (k : ℕ) ≠ 0 := ne_of_gt (pow_pos M.q_pos (k : ℕ))
  have hmain :
      M.q ^ (k : ℕ) *
          (fac.firstSecondTail * candidateRankRemovalPowerSum n M.q k) =
        M.q ^ (k : ℕ) * fac.firstTail := by
    calc
      M.q ^ (k : ℕ) *
          (fac.firstSecondTail * candidateRankRemovalPowerSum n M.q k)
          = M.q ^ (k : ℕ) * fac.firstSecondTail *
              candidateRankRemovalPowerSum n M.q k := by ring
      _ = (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) := by
            rw [hleft]
      _ = M.firstWeight c := hsum_center
      _ = M.q ^ (k : ℕ) * fac.firstTail := hright
  exact (mul_left_cancel₀ hqk hmain).symm

/-- Unnormalised first-choice mass of a center-rank prefix. -/
noncomputable def firstWeightPrefix (k : Fin (n + 1)) : ℝ :=
  ∑ c : Candidate n,
    if (rankOf M.center c : ℕ) ≤ k.val then M.firstWeight c else 0

theorem firstWeightPrefix_eq_rankPrefixPowerSum_mul
    (fac : M.RankFactorization) (k : Fin (n + 1)) :
    M.firstWeightPrefix k = candidateRankPrefixPowerSum n M.q k * fac.firstTail := by
  classical
  unfold firstWeightPrefix candidateRankPrefixPowerSum
  calc
    (∑ c : Candidate n,
        if (rankOf M.center c : ℕ) ≤ k.val then M.firstWeight c else 0)
        = ∑ c : Candidate n,
            if (rankOf M.center c : ℕ) ≤ k.val then
              M.q ^ (rankOf M.center c : ℕ) * fac.firstTail
            else
              0 := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [fac.firstWeight_eq c]
    _ = ∑ r : Candidate n,
          if (r : ℕ) ≤ k.val then M.q ^ (r : ℕ) * fac.firstTail else 0 := by
          simpa [rankOf] using
            (Equiv.sum_comp M.center.symm
              (fun r : Candidate n =>
                if (r : ℕ) ≤ k.val then M.q ^ (r : ℕ) * fac.firstTail else 0))
    _ = (∑ r : Candidate n,
          if (r : ℕ) ≤ k.val then M.q ^ (r : ℕ) else 0) * fac.firstTail := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _
          by_cases hr : (r : ℕ) ≤ k.val <;> simp [hr]

end MallowsSpec

end Ranking
end SocialChoice
end AppliedModelingLib

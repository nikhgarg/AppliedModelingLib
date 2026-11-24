import Sievert26SimpleAuctions.CertLoop
import Sievert26SimpleAuctions.CertRun
import Sievert26SimpleAuctions.Reindex

/-! The universal upper bound. -/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB
open UBCert

theorem y0d_pos (i : Fin 4) : 0 < y0d i := by fin_cases i <;> simp [y0d]

theorem tangents (i : Fin 4) : Tangent ((kn i : ℝ) / UN) ((bn i : ℝ) / UN) := by
  fin_cases i
  · exact tangent_sound _ _ _ _ (y0d_pos 0) xs0 tan0_ok
  · exact tangent_sound _ _ _ _ (y0d_pos 1) xs1 tan1_ok
  · exact tangent_sound _ _ _ _ (y0d_pos 2) xs2 tan2_ok
  · exact tangent_sound _ _ _ _ (y0d_pos 3) xs3 tan3_ok

theorem al0_pos : 0 < al0 := by simp [al0]
theorem Vmax_pos : 0 < Vmax := by simp [Vmax]

theorem levels_sound :
    (∀ t, 0 < t → pt 0 ≤ t →
        Good ((kap:ℝ) / SC) ((gCap:ℝ) / SC) (pt (alphaL levels al0 t)) t) ∧
      (∀ t, al0 ≤ alphaL levels al0 t) ∧
      (∀ t u, t ≤ u → alphaL levels al0 t ≤ alphaL levels al0 u) ∧
      (∀ t, alphaL levels al0 t ≤ al0 + (levels.map Prod.snd).sum) :=
  allLev_sound tab Vmax kap gCap Vmax_pos tab_ok levels 0 al0 al0_pos lev_ok

theorem pt_mono {a b : ℕ} (h : a ≤ b) : pt a ≤ pt b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) Dd_pos.le

theorem kappa_ok : ∑ i, aR i * sR i * ((kn i : ℝ) / UN) ≤ (kap : ℝ) / SC := by
  rw [Fin.sum_univ_four]
  unfold aR sR AN SN kn UN kap SC
  norm_num

theorem b_ok : ∑ i, aR i * ((bn i : ℝ) / UN) ≤ (bCap : ℝ) / UN := by
  rw [Fin.sum_univ_four]
  unfold aR AN bn UN bCap
  norm_num

/-- the concrete certificate -/
noncomputable def theCert : UCert where
  n := 4
  a := aR
  s := sR
  kp i := (kn i : ℝ) / UN
  bb i := (bn i : ℝ) / UN
  alpha t := pt (alphaL levels al0 t)
  A := pt (al0 + (levels.map Prod.snd).sum)
  kappa := (kap : ℝ) / SC
  b := (bCap : ℝ) / UN
  g := (gCap : ℝ) / SC
  a_nonneg := aR_nonneg
  s_pos := sR_pos
  alpha_pos t := pt_pos _ (lt_of_lt_of_le al0_pos (levels_sound.2.1 t))
  alpha_mono t u htu := pt_mono (levels_sound.2.2.1 t u htu)
  alpha_le t := pt_mono (levels_sound.2.2.2 t)
  kappa_nonneg := by positivity
  tan := tangents
  kappa_ge := kappa_ok
  b_ge := b_ok
  cert t T ht htT := levels_sound.1 t ht (by unfold pt; simp; exact ht.le) T htT

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- if every item has zero posted-price revenue, every mechanism earns at most zero -/
theorem rev_le_zero (D : ι → FinDist) (hS : ∑ i, (D i).rev ≤ 0) (M : Mechanism ι) :
    M.rev D ≤ 0 := by
  have hr : ∀ i, (D i).rev = 0 := by
    intro i
    have h1 := single_le_sum (f := fun i => (D i).rev) (fun i _ => rev_nonneg (D i)) (mem_univ i)
    have h2 := rev_nonneg (D i)
    linarith
  -- every positive value has probability zero
  have hp : ∀ i k, (D i).prob k * (D i).val k = 0 := by
    intro i k
    rcases eq_or_lt_of_le ((D i).val_nonneg k) with h | h
    · rw [← h, mul_zero]
    · have h1 := mul_tail_le (D i) ((D i).val k) h.le
      rw [hr i] at h1
      have h2 : (D i).prob k ≤ (D i).tail ((D i).val k) := by
        unfold FinDist.tail
        have := single_le_sum (f := fun k' => if (D i).val k ≤ (D i).val k' then (D i).prob k' else 0)
          (fun k' _ => by
            dsimp only
            split_ifs
            · exact (D i).prob_nonneg k'
            · exact le_rfl) (mem_univ k)
        simpa using this
      have h3 := (D i).prob_nonneg k
      nlinarith
  have hmean : ∀ i, E1 (D i) (fun x => x) = 0 := by
    intro i; unfold E1; exact sum_eq_zero fun k _ => hp i k
  have h1 : M.rev D ≤ Ex D (fun ω => ∑ i, value D ω i) := by
    unfold Mechanism.rev Ex
    refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (prob_nonneg D ω)
    have h := M.ir (value D ω) (value_nonneg D ω)
    have h2 : ∑ i, value D ω i * M.alloc (value D ω) i ≤ ∑ i, value D ω i :=
      sum_le_sum fun i _ => by
        simpa using mul_le_mul_of_nonneg_left (M.alloc_le_one (value D ω) i) (value_nonneg D ω i)
    linarith
  rw [Ex_sum] at h1
  have h2 : ∀ i, Ex D (fun ω => value D ω i) = 0 := fun i => by
    rw [Ex_marg D (fun x => x) i, hmean]
  simp_rw [h2] at h1
  simpa using h1

/-- positive separate revenue forces positive bundle revenue -/
theorem BREV_pos (D : ι → FinDist) (hS : 0 < SREV D) : 0 < BREV D := by
  by_contra hB
  have hB0 : BREV D = 0 := le_antisymm (not_lt.mp hB) (BREV_nonneg D)
  have hr : ∀ i, (D i).rev ≤ 0 := by
    intro i
    refine FinDist.rev_le _ _ fun p hp => ?_
    have h1 := mul_bundle_le D p hp
    rw [hB0] at h1
    have h2 : (D i).tail p ≤ bundleTail D p := by
      rw [tail_eq, bundleTail_eq, ← Ex_marg D (fun x => if p ≤ x then (1:ℝ) else 0) i]
      refine Ex_mono D fun ω => ?_
      by_cases h : p ≤ value D ω i
      · have : p ≤ ∑ j, value D ω j :=
          h.trans (single_le_sum (f := fun j => value D ω j) (fun j _ => value_nonneg D ω j)
            (mem_univ i))
        rw [if_pos h, if_pos this]
      · rw [if_neg h]; split_ifs <;> norm_num
    have := mul_le_mul_of_nonneg_left h2 hp
    linarith
  have : SREV D ≤ 0 := sum_nonpos fun i _ => hr i
  linarith

/-- two-parameter bound for every mechanism -/
theorem rev_bound (D : ι → FinDist) (M : Mechanism ι) :
    M.rev D ≤ (1 + (gCap : ℝ) / SC) * SREV D + (bCap : ℝ) / UN * BREV D := by
  rcases lt_or_ge 0 (SREV D) with hS | hS
  · exact main_estimate theCert D hS (BREV_pos D hS) M
  · have h0 : SREV D = 0 := le_antisymm hS (sum_nonneg fun i _ => rev_nonneg _)
    have h1 := rev_le_zero D hS M
    have h2 : 0 ≤ (bCap : ℝ) / UN * BREV D := mul_nonneg (by positivity) (BREV_nonneg D)
    rw [h0]; linarith

end UB

open UB UBCert in
/-- **Sharper two-parameter bound.** -/
theorem upper_bound_two {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → FinDist) :
    REV D ≤ 1.1187 * SREV D + 1.367299 * BREV D := by
  refine ciSup_le fun M => (rev_bound D M).trans (le_of_eq ?_)
  have e1 : (1 + (gCap : ℝ) / SC) = 1.1187 := by unfold gCap SC; norm_num
  have e2 : (bCap : ℝ) / UN = 1.367299 := by unfold bCap UN; norm_num
  rw [e1, e2]

/-- **Universal upper bound** for an arbitrary finite item set. -/
theorem upper_bound_general {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → FinDist) :
    REV D ≤ (2486 / 1000 : ℝ) * max (SREV D) (BREV D) := by
  have h := upper_bound_two D
  have h1 := le_max_left (SREV D) (BREV D)
  have h2 := le_max_right (SREV D) (BREV D)
  have h3 : 0 ≤ max (SREV D) (BREV D) := (UB.BREV_nonneg D).trans h2
  linarith

/-- **Universal upper bound.** For all finitely many independent, finitely supported items, every
(randomised) IC+IR mechanism earns at most `2.486 · max(SREV, BREV)`. -/
theorem upper_bound : ∀ (m : ℕ) (D : Fin m → FinDist),
    REV D ≤ (2486 / 1000 : ℝ) * max (SREV D) (BREV D) :=
  fun _ D => upper_bound_general D

end Sievert26SimpleAuctions

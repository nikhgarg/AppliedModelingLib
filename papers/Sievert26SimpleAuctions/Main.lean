import Sievert26SimpleAuctions.Instance
import Sievert26SimpleAuctions.RealA
import Sievert26SimpleAuctions.GroupB
import Sievert26SimpleAuctions.Reindex

/-! Combination of group `A` and group `B`, the mechanism, and the main theorem. -/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions

section combine
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable (DA : α → FinDist) (DB : β → FinDist)

/-- disjoint union of two independent item groups -/
def comb : α ⊕ β → FinDist := Sum.elim DA DB

theorem SREV_comb : SREV (comb DA DB) = SREV DA + SREV DB := by
  unfold SREV; rw [Fintype.sum_sum_type]; rfl

/-- expectations over the union are iterated expectations -/
theorem sum_comb (F : (α → ℝ) → (β → ℝ) → ℝ) :
    ∑ ω : Profile (comb DA DB), prob (comb DA DB) ω *
      F (fun a => value (comb DA DB) ω (Sum.inl a)) (fun b => value (comb DA DB) ω (Sum.inr b)) =
    ∑ ωb : Profile DB, prob DB ωb *
      ∑ ωa : Profile DA, prob DA ωa * F (value DA ωa) (value DB ωb) := by
  have h := Fintype.sum_equiv (Equiv.sumPiEquivProdPi (fun i => Fin ((comb DA DB) i).size))
    (fun ω : Profile (comb DA DB) => prob (comb DA DB) ω *
      F (fun a => value (comb DA DB) ω (Sum.inl a)) (fun b => value (comb DA DB) ω (Sum.inr b)))
    (fun q : Profile DA × Profile DB => (prob DA q.1 * prob DB q.2) *
      F (value DA q.1) (value DB q.2)) (by
      intro ω
      have : prob (comb DA DB) ω = prob DA (fun a => ω (Sum.inl a)) *
          prob DB (fun b => ω (Sum.inr b)) := by
        unfold prob; rw [Fintype.prod_sum_type]; rfl
      dsimp only; rw [this]; rfl)
  rw [h, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun ωb _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun ωa _ => ?_
  ring

theorem bundleTail_comb (p : ℝ) : bundleTail (comb DA DB) p =
    ∑ ωb : Profile DB, prob DB ωb * ∑ ωa : Profile DA,
      (if p ≤ (∑ i, value DA ωa i) + ∑ i, value DB ωb i then prob DA ωa else 0) := by
  have h := sum_comb DA DB (fun va vb => if p ≤ (∑ i, va i) + ∑ i, vb i then 1 else 0)
  unfold bundleTail
  have h1 : ∀ ω : Profile (comb DA DB),
      (if p ≤ ∑ i, value (comb DA DB) ω i then prob (comb DA DB) ω else 0) =
      prob (comb DA DB) ω * (if p ≤ (∑ a, value (comb DA DB) ω (Sum.inl a)) +
        ∑ b, value (comb DA DB) ω (Sum.inr b) then 1 else 0) := by
    intro ω; rw [Fintype.sum_sum_type]; split_ifs <;> simp
  rw [sum_congr rfl (fun ω _ => h1 ω), h]
  refine sum_congr rfl fun ωb _ => ?_
  congr 1
  refine sum_congr rfl fun ωa _ => ?_
  split_ifs <;> simp

end combine

section mechanism
variable {α β : Type} [Fintype α] [Fintype β]

/-- Surplus of the `A`-items at item prices `q`. -/
noncomputable def surplus (q : α → ℝ) (v : α → ℝ) : ℝ := ∑ a, max (v a - q a) 0

open Classical in
/-- Menu: buy the `B`-bundle at price `pB` and/or pay the entry fee `E` and buy any `A`-items at
prices `q`. -/
noncomputable def menuMech (q : α → ℝ) (E pB : ℝ) : Mechanism (α ⊕ β) where
  alloc v := Sum.elim
    (fun a => if E ≤ surplus q (fun a => v (Sum.inl a)) ∧ q a ≤ v (Sum.inl a) then 1 else 0)
    (fun _ => if pB ≤ ∑ b, v (Sum.inr b) then 1 else 0)
  pay v := (if E ≤ surplus q (fun a => v (Sum.inl a)) then
      E + ∑ a, (if q a ≤ v (Sum.inl a) then q a else 0) else 0) +
    (if pB ≤ ∑ b, v (Sum.inr b) then pB else 0)
  alloc_nonneg v i := by
    rcases i with a | b <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> norm_num
  alloc_le_one v i := by
    rcases i with a | b <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> norm_num
  ir v _ := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hA : 0 ≤ ∑ a, v (Sum.inl a) * (if E ≤ surplus q (fun a => v (Sum.inl a)) ∧
        q a ≤ v (Sum.inl a) then 1 else 0) - (if E ≤ surplus q (fun a => v (Sum.inl a)) then
        E + ∑ a, (if q a ≤ v (Sum.inl a) then q a else 0) else 0) := by
      by_cases hE : E ≤ surplus q (fun a => v (Sum.inl a))
      · simp only [hE, true_and, if_true]
        have : ∑ a, v (Sum.inl a) * (if q a ≤ v (Sum.inl a) then (1:ℝ) else 0) -
            ∑ a, (if q a ≤ v (Sum.inl a) then q a else 0) = surplus q (fun a => v (Sum.inl a)) := by
          rw [← sum_sub_distrib, surplus]
          refine sum_congr rfl fun a _ => ?_
          split_ifs with h
          · rw [max_eq_left (by linarith)]; ring
          · rw [max_eq_right (by linarith)]; ring
        linarith
      · simp [hE]
    have hB : 0 ≤ ∑ b : β, v (Sum.inr b) * (if pB ≤ ∑ b, v (Sum.inr b) then 1 else 0) -
        (if pB ≤ ∑ b, v (Sum.inr b) then pB else 0) := by
      rw [← sum_mul]
      split_ifs with h
      · linarith
      · simp
    linarith
  ic v v' _ _ := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have key : ∑ a, v (Sum.inl a) * (if E ≤ surplus q (fun a => v (Sum.inl a)) ∧
        q a ≤ v (Sum.inl a) then (1:ℝ) else 0) - (if E ≤ surplus q (fun a => v (Sum.inl a)) then
        E + ∑ a, (if q a ≤ v (Sum.inl a) then q a else 0) else 0) =
        max (surplus q (fun a => v (Sum.inl a)) - E) 0 := by
      by_cases hE : E ≤ surplus q (fun a => v (Sum.inl a))
      · simp only [hE, true_and, if_true]
        have : ∑ a, v (Sum.inl a) * (if q a ≤ v (Sum.inl a) then (1:ℝ) else 0) -
            ∑ a, (if q a ≤ v (Sum.inl a) then q a else 0) = surplus q (fun a => v (Sum.inl a)) := by
          rw [← sum_sub_distrib, surplus]
          refine sum_congr rfl fun a _ => ?_
          split_ifs with h
          · rw [max_eq_left (by linarith)]; ring
          · rw [max_eq_right (by linarith)]; ring
        rw [max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith)]
        simp [hE]
    have hA : ∑ a, v (Sum.inl a) * (if E ≤ surplus q (fun a => v' (Sum.inl a)) ∧
        q a ≤ v' (Sum.inl a) then (1:ℝ) else 0) - (if E ≤ surplus q (fun a => v' (Sum.inl a)) then
        E + ∑ a, (if q a ≤ v' (Sum.inl a) then q a else 0) else 0) ≤
        max (surplus q (fun a => v (Sum.inl a)) - E) 0 := by
      by_cases hE : E ≤ surplus q (fun a => v' (Sum.inl a))
      · simp only [hE, true_and, if_true]
        have : ∑ a, v (Sum.inl a) * (if q a ≤ v' (Sum.inl a) then (1:ℝ) else 0) -
            ∑ a, (if q a ≤ v' (Sum.inl a) then q a else 0) ≤
            surplus q (fun a => v (Sum.inl a)) := by
          rw [← sum_sub_distrib, surplus]
          refine sum_le_sum fun a _ => ?_
          split_ifs with h
          · rw [mul_one]; exact le_max_left _ _
          · rw [mul_zero, sub_zero]; exact le_max_right _ _
        exact le_trans (by linarith) (le_max_left _ _)
      · simp only [hE, false_and, if_false, mul_zero, sum_const_zero, sub_zero]
        exact le_max_right _ _
    have hB : ∑ b : β, v (Sum.inr b) * (if pB ≤ ∑ b, v' (Sum.inr b) then (1:ℝ) else 0) -
        (if pB ≤ ∑ b, v' (Sum.inr b) then pB else 0) ≤
        ∑ b : β, v (Sum.inr b) * (if pB ≤ ∑ b, v (Sum.inr b) then (1:ℝ) else 0) -
        (if pB ≤ ∑ b, v (Sum.inr b) then pB else 0) := by
      rw [← sum_mul, ← sum_mul]
      split_ifs with h1 h2 h2 <;> linarith
    linarith

theorem menuMech_det (q : α → ℝ) (E pB : ℝ) (v : α ⊕ β → ℝ) (i : α ⊕ β) :
    (menuMech q E pB).alloc v i = 0 ∨ (menuMech q E pB).alloc v i = 1 := by
  rcases i with a | b <;> simp only [menuMech, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp

end mechanism

section final
variable (d : Data)

/-- elementary second-moment bounds for a finite distribution -/
theorem moment_bounds {Ω : Type*} [Fintype Ω] (pr Z : Ω → ℝ) (hp : ∀ ω, 0 ≤ pr ω)
    (hs : ∑ ω, pr ω = 1) (c V τ : ℝ) (hτ : 0 < τ)
    (hV : ∑ ω, pr ω * (Z ω - c) ^ 2 ≤ V) :
    (∑ ω, pr ω * max c (Z ω) ≤ c + τ + V / (4 * τ)) ∧
    (1 - V / τ ^ 2 ≤ ∑ ω, pr ω * (if c - τ ≤ Z ω then 1 else 0)) := by
  constructor
  · have h1 : ∀ ω, pr ω * max c (Z ω) ≤ pr ω * (c + τ) + pr ω * (Z ω - c) ^ 2 * (1 / (4 * τ)) := by
      intro ω
      have h2 : max c (Z ω) ≤ (c + τ) + (Z ω - c) ^ 2 * (1 / (4 * τ)) := by
        have h0 : 0 ≤ (Z ω - c) ^ 2 * (1 / (4 * τ)) := by positivity
        refine max_le (by linarith) ?_
        have h3 : (Z ω - c) ^ 2 * (1 / (4 * τ)) - (Z ω - c - τ) =
            (Z ω - c - 2 * τ) ^ 2 * (1 / (4 * τ)) := by field_simp; ring
        have h4 : 0 ≤ (Z ω - c - 2 * τ) ^ 2 * (1 / (4 * τ)) := by positivity
        linarith
      calc _ ≤ pr ω * ((c + τ) + (Z ω - c) ^ 2 * (1 / (4 * τ))) :=
            mul_le_mul_of_nonneg_left h2 (hp ω)
        _ = _ := by ring
    calc _ ≤ ∑ ω, (pr ω * (c + τ) + pr ω * (Z ω - c) ^ 2 * (1 / (4 * τ))) :=
          sum_le_sum fun ω _ => h1 ω
      _ = (c + τ) + (∑ ω, pr ω * (Z ω - c) ^ 2) * (1 / (4 * τ)) := by
          rw [sum_add_distrib, ← sum_mul, ← sum_mul, hs, one_mul]
      _ ≤ c + τ + V / (4 * τ) := by
          have := mul_le_mul_of_nonneg_right hV (show 0 ≤ 1 / (4 * τ) by positivity)
          rw [div_eq_mul_one_div V]; linarith
  · have h1 : ∀ ω, pr ω - pr ω * (Z ω - c) ^ 2 * (1 / τ ^ 2) ≤
        pr ω * (if c - τ ≤ Z ω then 1 else 0) := by
      intro ω
      split_ifs with h
      · have : 0 ≤ pr ω * (Z ω - c) ^ 2 * (1 / τ ^ 2) := by
          have := hp ω; positivity
        linarith
      · have h2 : τ ^ 2 ≤ (Z ω - c) ^ 2 := by
          push Not at h; nlinarith
        have h3 : 1 ≤ (Z ω - c) ^ 2 * (1 / τ ^ 2) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
        nlinarith [mul_le_mul_of_nonneg_left h3 (hp ω)]
    calc 1 - V / τ ^ 2 ≤ 1 - (∑ ω, pr ω * (Z ω - c) ^ 2) * (1 / τ ^ 2) := by
          have := mul_le_mul_of_nonneg_right hV (show 0 ≤ 1 / τ ^ 2 by positivity)
          rw [div_eq_mul_one_div V]; linarith
      _ = ∑ ω, (pr ω - pr ω * (Z ω - c) ^ 2 * (1 / τ ^ 2)) := by
          rw [sum_sub_distrib, hs, ← sum_mul]
      _ ≤ _ := sum_le_sum fun ω _ => h1 ω

/-- All quantitative bounds for group size parameter `L`, with explicit deterministic witness. -/
theorem bounds_det (L : ℕ) (hL : 0 < L) (τ : ℝ) (hτ : 0 < τ) (hτN : τ ≤ d.N) :
    ∃ (D : (Data.IA ⊕ Fin (L ^ 2)) → FinDist) (M : Mechanism (Data.IA ⊕ Fin (L ^ 2))),
      (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
      SREV D ≤ d.N + d.N / GroupB.H L ∧
      BREV D ≤ d.N + τ + (2 * (d.N : ℝ) ^ 2 / L) / (4 * τ) ∧
      (119464 / 100000 : ℝ) * d.N + (d.N - τ) * (1 - (2 * (d.N : ℝ) ^ 2 / L) / τ ^ 2) ≤ M.rev D := by
  have hN : (0:ℝ) < d.N := by exact_mod_cast d.N_pos
  have hLR : (0:ℝ) < L := by exact_mod_cast hL
  have hH : 1 ≤ GroupB.H L := GroupB.H_pos L hL
  have hH0 : 0 < GroupB.H L := by linarith
  set δ : ℝ := d.N / ((L:ℝ) ^ 2 * GroupB.H L) with hδdef
  have hδ : 0 < δ := by positivity
  set B := GroupB.DB L hL δ hδ (L ^ 2) with hB
  have hMδ : ((L ^ 2 : ℕ) : ℝ) * (GroupB.H L * δ) = d.N := by
    rw [hδdef]; push_cast; field_simp
  have hMδ' : ((L ^ 2 : ℕ) : ℝ) * δ = d.N / GroupB.H L := by
    rw [hδdef]; push_cast; field_simp
  set V : ℝ := 2 * (d.N : ℝ) ^ 2 / L with hV
  have hvar : ∑ ω : Profile B, prob B ω * ((∑ i, value B ω i) - d.N) ^ 2 ≤ V := by
    have h := GroupB.variance_B L hL δ hδ (L ^ 2)
    rw [hMδ] at h
    refine le_trans h ?_
    rw [hV, hδdef]
    have : ((L ^ 2 : ℕ) : ℝ) * (2 * L * (d.N / ((L:ℝ) ^ 2 * GroupB.H L)) ^ 2) =
        2 * (d.N:ℝ) ^ 2 / L * (1 / GroupB.H L ^ 2) := by
      push_cast; field_simp
    rw [this]
    have h1 : 1 / GroupB.H L ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h2 : 0 ≤ 2 * (d.N:ℝ) ^ 2 / L := by positivity
    nlinarith
  obtain ⟨hm1, hm2⟩ := moment_bounds (prob B) (fun ω => ∑ i, value B ω i) (prob_nonneg B)
    (prob_sum B) d.N V τ hτ hvar
  refine ⟨comb d.DA B, menuMech (fun i : Data.IA => (d.P i.1 : ℝ)) d.e (d.N - τ),
    menuMech_det _ _ _, ?_, ?_, ?_⟩
  · rw [SREV_comb]
    have h1 := d.SREV_A
    have h2 := GroupB.SREV_B L hL δ hδ (L ^ 2)
    rw [hMδ'] at h2
    exact add_le_add h1 h2
  · refine BREV_le _ _ fun p hp => ?_
    rw [bundleTail_comb, mul_sum]
    refine le_trans (sum_le_sum fun ωb _ => ?_) hm1
    have h := d.bundle_A p (∑ i, value B ωb i) hp
    calc p * (prob B ωb * _) = prob B ωb * (p * _) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (prob_nonneg B ωb)
  · have h := sum_comb d.DA B (fun va vb => d.payFun va +
      (if (d.N : ℝ) - τ ≤ ∑ b, vb b then (d.N : ℝ) - τ else 0))
    have h1 : (menuMech (β := Fin (L ^ 2)) (fun i : Data.IA => (d.P i.1 : ℝ)) d.e (d.N - τ)).rev
        (comb d.DA B) = ∑ ω : Profile (comb d.DA B), prob (comb d.DA B) ω *
        (d.payFun (fun a => value (comb d.DA B) ω (Sum.inl a)) +
        (if (d.N : ℝ) - τ ≤ ∑ b, value (comb d.DA B) ω (Sum.inr b) then (d.N : ℝ) - τ else 0)) := by
      unfold Mechanism.rev
      refine sum_congr rfl fun ω _ => ?_
      congr 1
    rw [h1, h]
    have hA := d.rev_A
    have hin : ∀ ωb : Profile B, ∑ ωa : Profile d.DA, prob d.DA ωa * (d.payFun (value d.DA ωa) +
        (if (d.N : ℝ) - τ ≤ ∑ b, value B ωb b then (d.N : ℝ) - τ else 0)) =
        (∑ ωa : Profile d.DA, prob d.DA ωa * d.payFun (value d.DA ωa)) +
        (d.N - τ) * (if (d.N : ℝ) - τ ≤ ∑ b, value B ωb b then 1 else 0) := by
      intro ωb
      simp_rw [mul_add]
      rw [sum_add_distrib, ← sum_mul, prob_sum, one_mul]
      split_ifs <;> simp
    simp_rw [hin, mul_add]
    rw [sum_add_distrib, ← sum_mul, prob_sum, one_mul]
    have h3 : ∑ ωb : Profile B, prob B ωb *
        ((d.N - τ) * (if (d.N : ℝ) - τ ≤ ∑ b, value B ωb b then 1 else 0)) =
        (d.N - τ) * ∑ ωb : Profile B, prob B ωb *
          (if (d.N : ℝ) - τ ≤ ∑ b, value B ωb b then 1 else 0) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [h3]
    have := mul_le_mul_of_nonneg_left hm2 (sub_nonneg.mpr hτN)
    linarith

/-- All quantitative bounds for group size parameter `L`. -/
theorem bounds (L : ℕ) (hL : 0 < L) (τ : ℝ) (hτ : 0 < τ) (hτN : τ ≤ d.N) :
    ∃ D : (Data.IA ⊕ Fin (L ^ 2)) → FinDist,
      SREV D ≤ d.N + d.N / GroupB.H L ∧
      BREV D ≤ d.N + τ + (2 * (d.N : ℝ) ^ 2 / L) / (4 * τ) ∧
      (119464 / 100000 : ℝ) * d.N + (d.N - τ) * (1 - (2 * (d.N : ℝ) ^ 2 / L) / τ ^ 2) ≤ REV D := by
  obtain ⟨D, M, _, hS, hB, hR⟩ := bounds_det d L hL τ hτ hτN
  exact ⟨D, hS, hB, hR.trans (le_REV D M)⟩

open Filter Topology in
/-- For all large `L` the instance has ratio `> 2.1946`. -/
theorem exists_L : ∃ L : ℕ, 0 < L ∧
    (2.1946 : ℝ) * (d.N + d.N / GroupB.H L) <
      (119464 / 100000 : ℝ) * d.N + (d.N - d.N / 1000000) *
        (1 - (2 * (d.N : ℝ) ^ 2 / L) / (d.N / 1000000 : ℝ) ^ 2) ∧
    (2.1946 : ℝ) * (d.N + d.N / 1000000 + (2 * (d.N : ℝ) ^ 2 / L) / (4 * (d.N / 1000000))) <
      (119464 / 100000 : ℝ) * d.N + (d.N - d.N / 1000000) *
        (1 - (2 * (d.N : ℝ) ^ 2 / L) / (d.N / 1000000 : ℝ) ^ 2) := by
  have hN : (0:ℝ) < d.N := by exact_mod_cast d.N_pos
  have hV : Tendsto (fun L : ℕ => 2 * (d.N : ℝ) ^ 2 / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hH : Tendsto (fun L : ℕ => (d.N : ℝ) / GroupB.H L) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds GroupB.H_tendsto
  have hR : Tendsto (fun L : ℕ => (119464 / 100000 : ℝ) * d.N + (d.N - d.N / 1000000) *
        (1 - (2 * (d.N : ℝ) ^ 2 / L) / (d.N / 1000000 : ℝ) ^ 2)) atTop
      (𝓝 ((119464 / 100000 : ℝ) * d.N + (d.N - d.N / 1000000) *
        (1 - 0 / (d.N / 1000000 : ℝ) ^ 2))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (hV.div_const _)))
  have h1 : Tendsto (fun L : ℕ => (2.1946 : ℝ) * (d.N + d.N / GroupB.H L)) atTop
      (𝓝 ((2.1946 : ℝ) * (d.N + 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add hH)
  have h2 : Tendsto (fun L : ℕ => (2.1946 : ℝ) * (d.N + d.N / 1000000 +
      (2 * (d.N : ℝ) ^ 2 / L) / (4 * (d.N / 1000000)))) atTop
      (𝓝 ((2.1946 : ℝ) * (d.N + d.N / 1000000 + 0 / (4 * (d.N / 1000000))))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add (hV.div_const _))
  have e1 := h1.eventually_lt hR (by rw [zero_div]; norm_num; linarith)
  have e2 := h2.eventually_lt hR (by rw [zero_div, zero_div]; norm_num; linarith)
  obtain ⟨L, hL⟩ := ((eventually_gt_atTop 0).and (e1.and e2)).exists
  exact ⟨L, hL.1, hL.2.1, hL.2.2⟩

theorem reals_aux {S B R s b r : ℝ} (hS : S ≤ s) (hB : B ≤ b) (hR : r ≤ R)
    (h1 : (2.1946 : ℝ) * s < r) (h2 : (2.1946 : ℝ) * b < r) : (2.1946 : ℝ) * max S B < R := by
  rcases le_total S B with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem wrap {ι : Type} [Fintype ι] [DecidableEq ι] {s b r : ℝ}
    (h : ∃ D : ι → FinDist, SREV D ≤ s ∧ BREV D ≤ b ∧ r ≤ REV D)
    (h1 : (2.1946 : ℝ) * s < r) (h2 : (2.1946 : ℝ) * b < r) :
    ∃ (m : ℕ) (D : Fin m → FinDist), (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D := by
  obtain ⟨D, hS, hB, hR⟩ := h
  exact exists_fin D 2.1946 (reals_aux hS hB hR h1 h2)

theorem main_of_data (d : Data) : ∃ (m : ℕ) (D : Fin m → FinDist),
    (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D := by
  have hN : (0:ℝ) < d.N := by exact_mod_cast d.N_pos
  obtain ⟨L, hL, h1, h2⟩ := exists_L d
  exact wrap (bounds d L hL ((d.N : ℝ) / 1000000) (div_pos hN (by norm_num))
    (div_le_self hN.le (by norm_num))) h1 h2

end final

theorem wrap_det {ι : Type} [Fintype ι] [DecidableEq ι] {s b r : ℝ}
    (h : ∃ (D : ι → FinDist) (M : Mechanism ι),
      (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧ SREV D ≤ s ∧ BREV D ≤ b ∧ r ≤ M.rev D)
    (h1 : (2.1946 : ℝ) * s < r) (h2 : (2.1946 : ℝ) * b < r) :
    ∃ (m : ℕ) (D : Fin m → FinDist),
      (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D ∧
      ∃ M : Mechanism (Fin m),
        (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
        (2.1946 : ℝ) * max (SREV D) (BREV D) < M.rev D := by
  obtain ⟨D, M, hdet, hS, hB, hR⟩ := h
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let D' : Fin (Fintype.card ι) → FinDist := fun j => D (f j)
  let M' : Mechanism (Fin (Fintype.card ι)) := M.reindex f
  have hM' : (2.1946 : ℝ) * max (SREV D') (BREV D') < M'.rev D' := by
    rw [show SREV D' = SREV D from SREV_reindex D f,
      show BREV D' = BREV D from BREV_reindex D f,
      show M'.rev D' = M.rev D from rev_reindex D f M]
    exact reals_aux hS hB hR h1 h2
  refine ⟨Fintype.card ι, D', lt_of_lt_of_le hM' (le_REV D' M'), M',
    fun v j => hdet (fun i => v (f.symm i)) (f j), hM'⟩

theorem lower_bound_with_det :
    ∃ (m : ℕ) (D : Fin m → FinDist),
      (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D ∧
      ∃ M : Mechanism (Fin m),
        (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
        (2.1946 : ℝ) * max (SREV D) (BREV D) < M.rev D := by
  let d := Cert.theData
  have hN : (0:ℝ) < d.N := by exact_mod_cast d.N_pos
  obtain ⟨L, hL, h1, h2⟩ := exists_L d
  exact wrap_det (bounds_det d L hL ((d.N : ℝ) / 1000000) (div_pos hN (by norm_num))
    (div_le_self hN.le (by norm_num))) h1 h2

/-- **Main theorem.** There are finitely many items `1,…,m` with independent, finitely supported
values whose optimal revenue strictly exceeds `2.1946 · max(SREV, BREV)`. -/
theorem lower_bound : ∃ (m : ℕ) (D : Fin m → FinDist),
    (2.1946 : ℝ) * max (SREV D) (BREV D) < REV D :=
  let ⟨m, D, h, _⟩ := lower_bound_with_det
  ⟨m, D, h⟩

end Sievert26SimpleAuctions

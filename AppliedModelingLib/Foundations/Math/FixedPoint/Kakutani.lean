/-
Copyright (c) 2026 harfe
SPDX-License-Identifier: MIT

This file adapts `FixedPointTheorems/kakutani.lean` from
<https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems>.
See `LICENSE-FixedPointTheorems-MIT.txt` in this directory for the upstream MIT notice.
-/

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.Caratheodory

import AppliedModelingLib.Foundations.Math.FixedPoint.CompactConvexBrouwer

namespace AppliedModelingLib

/-
Kakutani Fixed-Point theorem:
Let s be a nonempty, compact, convex of a finite-dimensional space.
Let f be a set-valued map on s with closed graph,
and each f(x) be nonempty, compact, convex, and a subset of s.
Then there is a point x with x ∈ f(x).

Main result is `kakutani_fixed_point` below.
Proof relies on the Brouwer fixed-point theorem.

https://en.wikipedia.org/wiki/Kakutani_fixed-point_theorem
-/

open Classical
open Filter

/- defining the closed graph property of a set-valued map -/
def closedGraph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Set Y) : Prop :=
    IsClosed { z : X × Y | z.2 ∈ f z.1}

/- defining that x is a convex combinations of points y_i with weights a_i -/
def convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
  (x : V) (a : Fin k → ℝ) (y: Fin k → V) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧ x = ∑ i, a i • y i


lemma mem_of_convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
  (x : V) {a : Fin k → ℝ} {y: Fin k → V} (h0 : convex_comb x a y)
  s (h1 : Convex ℝ s) (h2 : ∀ i, y i ∈ s): x ∈ s := by {
  unfold convex_comb at h0
  rw [h0.2.2]
  apply Convex.sum_mem h1 (fun i _ ↦ h0.1 i) h0.2.1 fun i a ↦ h2 i
}


lemma sub_ICC_of_convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
    (x : V) {a : Fin k → ℝ} {y: Fin k → V} (h0 : convex_comb x a y)
    : a ∈ Set.Icc 0 1 := by {
  simp only [Set.mem_Icc]
  apply And.intro h0.1
  have h2 := h0.1
  have h1 := h0.2.1
  intro i
  simp only [Pi.one_apply]
  rw [←h1]
  apply Finset.single_le_sum (fun i a ↦ h2 i)
  simp only [Finset.mem_univ]
}


/- useful to get a fixed size of vectors -/
lemma caratheodory_1 {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) k (h1 : k = Module.finrank ℝ V) {x} (h2 : x ∈ convexHull ℝ s)
    : ∃ (z : Fin (k+1)→ V), ∃ a, Set.range z ⊆ s ∧ convex_comb x a z := by {
  obtain ⟨I ,hI,z1,α, h3⟩  := eq_pos_convex_span_of_mem_convexHull h2
  have h4 : hI.card ≤ k + 1 := by {
    apply le_trans $ AffineIndependent.card_le_finrank_succ h3.2.1
    rw [h1,add_le_add_iff_right]
    exact Submodule.finrank_le (vectorSpan ℝ (Set.range z1))
  }
  let g1 := hI.equivFin
  let g2 : Fin (hI.card) → Fin (k+1) := fun i ↦ Fin.ofNat _ i.1
  let g3 := g2 ∘ g1
  have hg3 : Function.Injective g3 := by {
    unfold g3
    refine (Equiv.injective_comp g1 g2).mpr ?_
    intro i1 i2 h5
    unfold g2 at h5
    simp only [Fin.ofNat_eq_cast] at h5
    rw [←Fin.val_eq_val] at h5 ⊢
    rwa [Fin.val_cast_of_lt, Fin.val_cast_of_lt] at h5 <;> omega
  }
  have hsne : s.Nonempty := convexHull_nonempty_iff.mp (Set.nonempty_of_mem h2)
  obtain ⟨sdef, hsdef⟩ := hsne
  let β := Function.extend g3 α (fun _ ↦ 0)
  let z2 := Function.extend g3 z1 (fun _ ↦ sdef)
  have h5 : Set.range z2 ⊆ s := by {
    intro y hy
    obtain ⟨i1, hi1⟩ := hy
    rw [← hi1]
    unfold z2
    by_cases h5 : ∃ i2, g3 i2 = i1
    {
      apply h3.1
      obtain ⟨i2, hi2⟩ := h5
      use i2
      rw [←hi2,Function.Injective.extend_apply hg3]
    }
    rwa [Function.extend_apply' _ _ _ h5]
  }
  use z2, β
  have h6 : ∑ i, β i = 1 := by {
    rw [←h3.2.2.2.1]
    symm
    apply Fintype.sum_of_injective g3 hg3
    exact fun i a ↦ Function.extend_apply' α (fun x ↦ 0) i a
    exact fun i ↦ Eq.symm (Function.Injective.extend_apply hg3 α (fun x ↦ 0) i)
  }
  have h7 : x = ∑ i, β i • z2 i := by {
    rw [←h3.2.2.2.2]
    apply Fintype.sum_of_injective g3 hg3
    intro i h7
    simp only [smul_eq_zero]
    exact Or.inl $ Function.extend_apply' α (fun x ↦ 0) i h7
    intro i
    unfold β z2
    rw [Function.Injective.extend_apply hg3,Function.Injective.extend_apply hg3]
  }
  have h9 i : 0 ≤ β i := by {
    unfold β
    have h12 : 0 ≤ α := fun i ↦ le_of_lt (h3.2.2.1 i)
    apply Function.extend_nonneg h12
    rfl
  }
  apply And.intro h5
  apply And.intro h9 (And.intro h6 h7)
}

lemma set_valued_map_approx_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcmpct : IsCompact s) (hcvx : Convex ℝ s) (hne : s.Nonempty) (f : s → Set V)
    (h1 : ∀ x, f x ⊆ s ∧ Convex ℝ (f x) ∧ (f x).Nonempty)
    k (hk : k = Module.finrank ℝ V) (eps : ℝ ) (heps : 0 < eps)
    : ∃ a : s, ∃ (y : Fin (k+1)→ s), ∃ z, ∃ α, convex_comb a.1 α z
    ∧ ∀ i, dist a (y i) < eps ∧ (z i ) ∈ f (y i)  := by {
  let eb (x : s) := Metric.ball x eps
  let G : s → Set V := fun x ↦ convexHull ℝ {z | ∃ y, dist x y < eps ∧ z ∈ f y}
  have hG1 : ∀ x, Convex ℝ (G x) := by {
    intro x
    exact convex_convexHull ℝ {z | ∃ y, dist x y < eps ∧ z ∈ f y}
  }
  haveI : CompactSpace ↑s := isCompact_iff_compactSpace.mp hcmpct
  have h2 := exists_continuous_forall_mem_convex_of_local_const hG1
  have h3 : ∃ g : C(s, V), ∀ x, g x ∈ G x := by {
    apply h2
    intro x
    obtain ⟨z, hz⟩ := (h1 x).2.2
    use z
    apply Metric.eventually_nhds_iff.mpr
    use eps
    apply And.intro heps
    intro y h3
    apply subset_convexHull
    use x
  }
  obtain ⟨g, hg⟩ := h3
  have h6 : ∀ x, g x ∈ s := by {
      intro x
      suffices h6 : G x ⊆ s  by {exact h6 (hg x)}
      unfold G
      apply convexHull_min _ hcvx
      intro z h5
      obtain ⟨y, hy⟩ := h5
      apply (h1 y).1 hy.2
    }
  have h5 : ∃ x, g x = x := by {
    let g2 : s → s := fun x ↦ ⟨g x, h6 x⟩
    have h7 : Continuous g2 := Continuous.subtype_mk g.continuous h6
    let g3 : C(s,s) := ⟨g2, h7⟩
    have brouwer_fpt := brouwer_fixed_point s hcvx hcmpct hne g3
    obtain ⟨x, hx⟩ := brouwer_fpt
    use x
    nth_rewrite 2 [←hx]
    rfl
  }
  obtain ⟨a, ha⟩ := h5
  have h5 : a.1 ∈ G a := by {
    rw [←ha]
    exact hg a
  }
  obtain ⟨z, ⟨α, h7⟩ ⟩ := caratheodory_1 _ k hk h5
  use a
  have h8 i : ∃ y, dist a y < eps ∧ (z i) ∈ f y := by {
    apply h7.1
    use i
  }
  obtain ⟨y, hy⟩ := axiomOfChoice h8
  use y, z, α
  tauto
}



theorem kakutani_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : s → Set V) (hcg : closedGraph f)
    (h1 : ∀ x, f x ⊆ s ∧ Convex ℝ (f x) ∧ (f x).Nonempty)
    : ∃ x : s, x.1 ∈ f x := by {
  let k := Module.finrank ℝ V
  have h2 := set_valued_map_approx_fixed_point s hcmpct hcvx hne f h1 k rfl
  have h31 (i : ℕ) : 0 < (1:ℝ )/(i+1) := Nat.one_div_pos_of_nat
  have h3 (i : ℕ) := h2 ((1:ℝ )/(i + 1)) (h31 i)
  have h5 i := Prod.exists'.mpr (Prod.exists'.mpr (Prod.exists'.mpr (h3 i)))
  obtain ⟨B,h6⟩ := axiomOfChoice h5
  clear h2 h3 h5
  let Btype := ((↑s × (Fin (k + 1) → ↑s)) × (Fin (k + 1) → V)) × (Fin (k + 1) → ℝ)
  let sB : Set Btype := (Set.univ ×ˢ {x | ∀ i, x i ∈ s}) ×ˢ (Set.Icc 0 1)
  have hBc : IsCompact sB := by {
    haveI : CompactSpace ↑s := isCompact_iff_compactSpace.mp hcmpct
    apply IsCompact.prod
    apply IsCompact.prod
    {
      apply isCompact_univ_iff.mpr
      apply instCompactSpaceProd
    }
    exact isCompact_pi_infinite fun i ↦ hcmpct
    exact isCompact_Icc
  }
  have h4 i : B i ∈ sB := by {
    unfold sB
    apply And.intro
    apply And.intro trivial
    intro i2
    apply (h1 ((B i).1.1.2 i2)).1
    exact ((h6 i).2 i2).2
    exact sub_ICC_of_convex_comb _ (h6 i).1
  }
  obtain ⟨B0, hB0, φ, h3⟩ := hBc.isSeqCompact h4
  let A := B ∘ φ
  have hA2 : Tendsto A atTop (nhds B0) := h3.2
  let x i := (A i).1.1.1
  let y j i := (A i).1.1.2 j
  let z j i := (A i).1.2 j
  let α j i := (A i).2 j
  let xxx := B0.1.1.1
  have ha2 j : Tendsto (α j) atTop (nhds (B0.2 j)) := by {
    exact (continuous_apply j).seqContinuous (Tendsto.snd_nhds hA2)
  }
  have hz2 j : Tendsto (z j) atTop (nhds (B0.1.2 j)) := by {
    exact (continuous_apply j).seqContinuous (Tendsto.fst_nhds hA2).snd_nhds
  }
  have hx2 : Tendsto x atTop (nhds xxx) :=  (Tendsto.fst_nhds hA2).fst_nhds.fst_nhds
  have hy2 j: Tendsto (y j) atTop (nhds xxx) := by {
    have h8 i : dist (x i) (y j i) < 1 / (↑(φ i) + 1) := ((h6 (φ i)).2 j).1
    have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
    apply tendsto_of_tendsto_of_dist hx2
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ h7
    intro i
    apply le_trans (le_of_lt (h8 i))
    simp only [one_div]
    apply inv_anti₀ (Nat.cast_add_one_pos i)
    simp only [add_le_add_iff_right, Nat.cast_le]
    exact h3.1.le_apply
  }
  have h8 j : B0.1.2 j ∈ f (xxx) := by {
    let yzj i := (y j i, z j i)
    have h10 i: yzj i ∈ {x | x.2 ∈ f x.1} := ((h6 (φ i)).2 j).2
    have h11 : Tendsto yzj atTop (nhds (xxx, B0.1.2 j))
        := Tendsto.prodMk_nhds (hy2 j) (hz2 j)
    exact hcg.isSeqClosed h10 h11
  }
  have h9 : convex_comb xxx.1 B0.2 B0.1.2 := by {
    apply And.intro
    {
      intro j
      apply ge_of_tendsto' (ha2 j)
      exact fun i ↦ (h6 (φ i)).1.1 j
    }
    apply And.intro
    {
      have h12 := tendsto_finset_sum Finset.univ (fun i _ ↦ ha2 i)
      have h11 i : ∑ c, α c i = 1 := (h6 (φ i)).1.2.1
      simp only [h11, tendsto_const_nhds_iff] at h12
      exact h12.symm
    }
    have h11 i : x i = ∑ j, α j i • z j i := (h6 (φ i)).1.2.2
    have h12 j := Tendsto.smul (ha2 j) (hz2 j)
    have h13 := tendsto_finset_sum Finset.univ (fun i _ ↦ h12 i)
    simp only [← h11] at h13
    have h14 : Tendsto (fun i ↦ (x i).1) atTop (nhds xxx.1) := by {
      apply continuous_subtype_val.seqContinuous hx2
    }
    apply tendsto_nhds_unique h14 h13
  }
  use xxx
  apply mem_of_convex_comb xxx.1 h9 _ (h1 xxx).2.1 h8
}

end AppliedModelingLib

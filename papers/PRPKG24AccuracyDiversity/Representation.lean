import PRPKG24AccuracyDiversity.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.StdSimplex

open scoped BigOperators
open AppliedModelingLib

namespace PRPKG24AccuracyDiversity

namespace CountAllocation

/-- Representation of a type in a recommendation allocation. -/
noncomputable def representation {T : ℕ} (a : CountAllocation T) (t : ItemType T) : ℝ := AppliedModelingLib.Allocation.share a t

/-- Exact target representation profile. -/
def HasExactRepresentation {T : ℕ}
    (a : CountAllocation T) (target : ItemType T → ℝ) : Prop := ∀ t, representation a t = target t

/-- Approximate target representation profile with uniform error `ε`. -/
def HasApproxRepresentation {T : ℕ}
    (a : CountAllocation T) (target : ItemType T → ℝ) (ε : ℝ) : Prop := ∀ t, |representation a t - target t| ≤ ε

/-- Representation of every type is at least the supplied lower bound. -/
def HasRepresentationAtLeast {T : ℕ}
    (a : CountAllocation T) (lower : ItemType T → ℝ) : Prop := ∀ t, lower t ≤ representation a t

@[simp] theorem representation_eq_share {T : ℕ}
    (a : CountAllocation T) (t : ItemType T) :
    representation a t = AppliedModelingLib.Allocation.share a t := rfl

end CountAllocation

/-- A plain target representation profile. -/
structure HomogeneityProfile (T : ℕ) where
  targetShare : ItemType T → ℝ

namespace HomogeneityProfile

/-- Exact agreement with a target representation profile. -/
def Exact {T : ℕ} (P : HomogeneityProfile T) (a : CountAllocation T) : Prop := CountAllocation.HasExactRepresentation a P.targetShare

/-- Approximate agreement with a target representation profile. -/
def Approx {T : ℕ} (P : HomogeneityProfile T) (a : CountAllocation T) (ε : ℝ) : Prop :=
  CountAllocation.HasApproxRepresentation a P.targetShare ε

end HomogeneityProfile

/--
A γ-homogeneity profile, represented by abstract target weights.

In the paper, the intended target weights are usually proportional to powers of type
likelihoods. We keep the weight function explicit here so the discrete finite layer does
not depend on real-power API details before the asymptotic branch is started.
-/
structure GammaHomogeneityProfile (T : ℕ) where
  gamma : ℝ
  targetWeight : ItemType T → ℝ

/-- The `0`-homogeneity profile: equal target weight on every type. -/
noncomputable def uniformProfile (T : ℕ) : GammaHomogeneityProfile T where
  gamma := 0
  targetWeight := fun _ => 1

namespace GammaHomogeneityProfile

/-- Normalizer for the target weights. -/
noncomputable def normalizer {T : ℕ} (G : GammaHomogeneityProfile T) : ℝ := ∑ t, G.targetWeight t

/-- Target share induced by the γ-profile weights, with zero fallback if the normalizer is zero. -/
noncomputable def targetShare {T : ℕ} (G : GammaHomogeneityProfile T) (t : ItemType T) : ℝ :=
  if h : G.normalizer = 0 then 0 else G.targetWeight t / G.normalizer

/-- Forget the γ-label and keep only the induced target-share profile. -/
noncomputable def toHomogeneityProfile {T : ℕ} (G : GammaHomogeneityProfile T) : HomogeneityProfile T where
  targetShare := G.targetShare

/-- Exact γ-homogeneity for a finite allocation. -/
noncomputable def Exact {T : ℕ} (G : GammaHomogeneityProfile T) (a : CountAllocation T) : Prop :=
  CountAllocation.HasExactRepresentation a G.targetShare

/-- Approximate γ-homogeneity for a finite allocation. -/
noncomputable def Approx {T : ℕ}
    (G : GammaHomogeneityProfile T) (a : CountAllocation T) (ε : ℝ) : Prop := CountAllocation.HasApproxRepresentation a G.targetShare ε

@[simp] theorem targetShare_of_normalizer_zero {T : ℕ}
    (G : GammaHomogeneityProfile T) (t : ItemType T) (h : G.normalizer = 0) :
    G.targetShare t = 0 := by
  simp [targetShare, h]

theorem targetShare_eq_div_of_normalizer_ne_zero {T : ℕ}
    (G : GammaHomogeneityProfile T) (t : ItemType T) (h : G.normalizer ≠ 0) :
    G.targetShare t = G.targetWeight t / G.normalizer := by
  simp [targetShare, h]

end GammaHomogeneityProfile
end PRPKG24AccuracyDiversity

namespace PRPKG24AccuracyDiversity

namespace CountAllocation

/-- Representation shares are nonnegative. -/
theorem representation_nonneg {T : ℕ} (a : CountAllocation T) (t : ItemType T) :
    0 ≤ representation a t := by
  simpa [representation] using AppliedModelingLib.Allocation.share_nonneg (a := a) (k := t)

/--
If the total count is larger than `T * K`, at least one type has count larger
than `K`.
-/
theorem exists_count_gt_of_card_mul_lt_total
    {T : ℕ} [NeZero T] (a : CountAllocation T) {K : ℕ}
    (hgt : T * K < AppliedModelingLib.Allocation.total a) :
    ∃ t : ItemType T, K < a.count t := by
  have hgt' :
      Fintype.card (ItemType T) * K < AppliedModelingLib.Allocation.total a := by
    simpa [Fintype.card_fin] using hgt
  exact AppliedModelingLib.Allocation.exists_count_gt_of_card_mul_lt_total a hgt'

/-- If the allocation has nonzero total, type representations sum to one. -/
theorem sum_representation_eq_one_of_total_ne_zero {T : ℕ}
    (a : CountAllocation T) (h : AppliedModelingLib.Allocation.total a ≠ 0) :
    ∑ t, representation a t = 1 := by
  simpa [representation] using
    AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero (a := a) h

/-- Exact representation implies approximate representation for every nonnegative tolerance. -/
theorem exact_implies_approx {T : ℕ}
    (a : CountAllocation T) (target : ItemType T → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    HasExactRepresentation a target → HasApproxRepresentation a target ε := by
  intro hExact t
  rw [hExact t]
  simpa using hε

end CountAllocation

namespace HomogeneityProfile

/-- Exact homogeneity implies approximate homogeneity for every nonnegative tolerance. -/
theorem exact_implies_approx {T : ℕ}
    (P : HomogeneityProfile T) (a : CountAllocation T) {ε : ℝ}
    (hε : 0 ≤ ε) :
    P.Exact a → P.Approx a ε := by
  intro hExact
  exact CountAllocation.exact_implies_approx a P.targetShare hε hExact

end HomogeneityProfile

namespace GammaHomogeneityProfile

/--
If the γ-profile normalizer is nonzero, its induced target shares sum to one.
-/
theorem sum_targetShare_eq_one_of_normalizer_ne_zero {T : ℕ}
    (G : GammaHomogeneityProfile T) (h : G.normalizer ≠ 0) :
    ∑ t, G.targetShare t = 1 := by
  have hreal : G.normalizer ≠ 0 := h
  calc
    ∑ t, G.targetShare t = ∑ t, G.targetWeight t / G.normalizer := by
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [targetShare_eq_div_of_normalizer_ne_zero (G := G) (t := t) h]
    _ = (∑ t, G.targetWeight t) / G.normalizer := by
      rw [Finset.sum_div]
    _ = G.normalizer / G.normalizer := by
      rfl
    _ = 1 := by
      field_simp [hreal]

/-- Nonnegative profile weights with positive normalizer induce nonnegative target shares. -/
theorem targetShare_nonneg_of_targetWeight_nonneg {T : ℕ}
    (G : GammaHomogeneityProfile T)
    (hweight_nonneg : ∀ t : ItemType T, 0 ≤ G.targetWeight t)
    (hnorm_pos : 0 < G.normalizer) (t : ItemType T) :
    0 ≤ G.targetShare t := by
  rw [targetShare_eq_div_of_normalizer_ne_zero (G := G) (t := t)
    (ne_of_gt hnorm_pos)]
  exact div_nonneg (hweight_nonneg t) hnorm_pos.le

/--
Nonnegative profile weights with positive normalizer induce a target-share
point in the finite standard simplex.
-/
theorem targetShare_mem_stdSimplex_of_targetWeight_nonneg {T : ℕ}
    (G : GammaHomogeneityProfile T)
    (hweight_nonneg : ∀ t : ItemType T, 0 ≤ G.targetWeight t)
    (hnorm_pos : 0 < G.normalizer) :
    G.targetShare ∈ stdSimplex ℝ (ItemType T) := by
  constructor
  · intro t
    exact targetShare_nonneg_of_targetWeight_nonneg
      G hweight_nonneg hnorm_pos t
  · exact sum_targetShare_eq_one_of_normalizer_ne_zero G
      (ne_of_gt hnorm_pos)

/-- Exact γ-homogeneity implies approximate γ-homogeneity for every nonnegative tolerance. -/
theorem exact_implies_approx {T : ℕ}
    (G : GammaHomogeneityProfile T) (a : CountAllocation T) {ε : ℝ}
    (hε : 0 ≤ ε) :
    G.Exact a → G.Approx a ε := by
  intro hExact
  exact CountAllocation.exact_implies_approx a G.targetShare hε hExact

/--
Coordinate count error implies approximate homogeneity.

This is the finite bridge used by rounding arguments: once each integer count
is within `C` of `N * targetShare`, representation shares are within `C / N`.
-/
theorem approx_of_count_abs_error {T : ℕ}
    (G : GammaHomogeneityProfile T) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : AppliedModelingLib.Allocation.total a = N) (hNpos : 0 < N)
    (hclose : ∀ t, |(a.count t : ℝ) - (N : ℝ) * G.targetShare t| ≤ C) :
    G.Approx a (C / (N : ℝ)) := by
  intro t
  have htotal_ne : AppliedModelingLib.Allocation.total a ≠ 0 := by
    rw [hN]
    exact Nat.ne_of_gt hNpos
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNreal_ne : (N : ℝ) ≠ 0 := ne_of_gt hNreal_pos
  have hrep :
      CountAllocation.representation a t = (a.count t : ℝ) / (N : ℝ) := by
    rw [CountAllocation.representation_eq_share]
    rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
      (a := a) (k := t) htotal_ne]
    rw [hN]
  calc
    |CountAllocation.representation a t - G.targetShare t|
        = |(a.count t : ℝ) / (N : ℝ) - G.targetShare t| := by
          rw [hrep]
    _ = |((a.count t : ℝ) - (N : ℝ) * G.targetShare t) / (N : ℝ)| := by
          congr 1
          field_simp [hNreal_ne]
    _ = |(a.count t : ℝ) - (N : ℝ) * G.targetShare t| / (N : ℝ) := by
          rw [abs_div]
          rw [abs_of_pos hNreal_pos]
    _ ≤ C / (N : ℝ) :=         div_le_div_of_nonneg_right (hclose t) hNreal_pos.le

/--
Pairwise bounded scaled counts imply bounded distance from the weighted target.

This is the algebraic averaging bridge needed by paper arguments such as PRPKG
Theorem 3: if all scaled quantities `count t / weight t` are within `C` of one
another, then each count is within `C * weight t` of the allocation with shares
proportional to `weight`.
-/
theorem count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded {T : ℕ}
    [Nonempty (ItemType T)]
    (a : CountAllocation T) (weight : ItemType T → ℝ) {N C : ℝ}
    (hN : (∑ i : ItemType T, (a.count i : ℝ)) = N)
    (hweight_pos : ∀ i, 0 < weight i)
    (hC : 0 ≤ C)
    (hpair :
      ∀ i j,
        |(a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j| ≤ C) :
    ∀ t,
      |(a.count t : ℝ) -
        weight t * (N / ∑ i : ItemType T, weight i)| ≤ C * weight t :=
   AppliedModelingLib.Allocation.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded
    a weight hN hweight_pos hC hpair

end GammaHomogeneityProfile

@[simp] theorem uniformProfile_targetShare {T : ℕ} [NeZero T]
    (t : ItemType T) :
    (uniformProfile T).targetShare t = 1 / (T : ℝ) := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne T)
  have hnorm : (uniformProfile T).normalizer = (T : ℝ) := by
    unfold GammaHomogeneityProfile.normalizer uniformProfile
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hnorm_ne : (uniformProfile T).normalizer ≠ 0 := by
    rw [hnorm]
    exact hTne
  rw [GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := uniformProfile T) (t := t) hnorm_ne]
  rw [hnorm]
  simp [uniformProfile]
/--
If all type counts are pairwise bounded by `C`, then each count is within
`C` of the uniform real average `N / T`.
-/
theorem count_abs_sub_uniform_average_le_C_of_pairwise_bounded
    {T : ℕ} [NeZero T]
    (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : AppliedModelingLib.Allocation.total a = N)
    (hbound : ∀ i j : ItemType T, (a.count i : ℝ) ≤ (a.count j : ℝ) + C)
    (t : ItemType T) :
    |(a.count t : ℝ) - (N : ℝ) / (T : ℝ)| ≤ C := by
  simpa [Fintype.card_fin] using
    AppliedModelingLib.Allocation.count_abs_sub_uniform_average_le_C_of_pairwise_bounded
      a hN hbound t

/--
If all type counts differ pairwise by at most one, then each count is within
...
one of the uniform real average `N / T`.
-/
theorem count_abs_sub_uniform_average_le_one_of_pairwise_balanced
    {T : ℕ} [NeZero T]
    (a : CountAllocation T) {N : ℕ}
    (hN : AppliedModelingLib.Allocation.total a = N)
    (hbal : ∀ i j : ItemType T, a.count i ≤ a.count j + 1)
    (t : ItemType T) :
    |(a.count t : ℝ) - (N : ℝ) / (T : ℝ)| ≤ 1 := by
  simpa [Fintype.card_fin] using
    AppliedModelingLib.Allocation.count_abs_sub_uniform_average_le_one_of_pairwise_balanced
      a hN hbal t

/--
Pairwise-balanced counts are approximately `0`-homogeneous, with finite
rounding error `1 / N`.
-/
theorem uniformProfile_approx_of_pairwise_balanced_counts
    {T : ℕ} [NeZero T]
    (a : CountAllocation T) {N : ℕ}
    (hN : AppliedModelingLib.Allocation.total a = N) (hNpos : 0 < N)
    (hbal : ∀ i j : ItemType T, a.count i ≤ a.count j + 1) :
    (uniformProfile T).Approx a (1 / (N : ℝ)) := by
  refine GammaHomogeneityProfile.approx_of_count_abs_error
    (uniformProfile T) a hN hNpos ?_
  intro t
  rw [uniformProfile_targetShare]
  have hclose :=
    count_abs_sub_uniform_average_le_one_of_pairwise_balanced a hN hbal t
  simpa [div_eq_mul_inv] using hclose

end PRPKG24AccuracyDiversity

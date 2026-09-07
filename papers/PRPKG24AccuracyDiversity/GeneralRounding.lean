import AppliedModelingLib.Applications.RecommenderSystems.Allocation
import AppliedModelingLib.Foundations.Math.FiniteRounding
import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Real.Archimedean

/-!
# General separable rounding

This file proves the corrected mathematical content of PRPKG24, Lemma D.5.
The source prints `strictly convex` in a maximization problem and then invokes
partial derivatives without assuming differentiability. The intended theorem
is true for strictly concave coordinate objectives, with no differentiability
assumption: secant-slope inequalities give the required exchange comparison.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace GeneralRounding

/-- The separable objective in Lemma D.5. -/
noncomputable def objective {κ : Type*} [Fintype κ]
    (g : κ → ℝ → ℝ) (x : κ → ℝ) : ℝ :=
  ∑ i : κ, g i (x i)

/-- A strictly concave fixed-sum objective has a strict maximum away from its maximizer. -/
theorem objective_lt_of_ne_of_strictConcave_maximizer
    {κ : Type*} [Fintype κ]
    (g : κ → ℝ → ℝ) (N : ℝ) (x y : κ → ℝ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = N)
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = N →
        objective g z ≤ objective g x)
    (hy_nonneg : ∀ i, 0 ≤ y i)
    (hy_sum : (∑ i : κ, y i) = N)
    (hy_ne : y ≠ x) :
    objective g y < objective g x := by
  classical
  let z : κ → ℝ := fun i => (x i + y i) / 2
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    exact div_nonneg (add_nonneg (hx_nonneg i) (hy_nonneg i)) (by norm_num)
  have hz_sum : (∑ i : κ, z i) = N := by
    dsimp [z]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      hx_sum, hy_sum]
    ring
  have hz_opt : objective g z ≤ objective g x := hx_opt z hz_nonneg hz_sum
  have hxy_ne : x ≠ y := Ne.symm hy_ne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy_ne
  have hpoint_le : ∀ i : κ,
      (g i (x i) + g i (y i)) / 2 ≤ g i (z i) := by
    intro i
    have h := (hconc i).concaveOn.2
      (show x i ∈ Set.Ici (0 : ℝ) by exact hx_nonneg i)
      (show y i ∈ Set.Ici (0 : ℝ) by exact hy_nonneg i)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (by norm_num)
    dsimp [z]
    convert h using 1 <;> simp only [smul_eq_mul] <;> ring_nf
  have hpoint_lt :
      (g j (x j) + g j (y j)) / 2 < g j (z j) := by
    have h := (hconc j).2
      (show x j ∈ Set.Ici (0 : ℝ) by exact hx_nonneg j)
      (show y j ∈ Set.Ici (0 : ℝ) by exact hy_nonneg j)
      hj
      (show 0 < (2 : ℝ)⁻¹ by positivity)
      (show 0 < (2 : ℝ)⁻¹ by positivity)
      (by norm_num)
    dsimp [z]
    convert h using 1 <;> simp only [smul_eq_mul] <;> ring_nf
  have hsum_mid :
      (∑ i : κ, (g i (x i) + g i (y i)) / 2) <
        ∑ i : κ, g i (z i) := by
    refine Finset.sum_lt_sum (fun i _hi => hpoint_le i) ?_
    exact ⟨j, Finset.mem_univ j, hpoint_lt⟩
  have hmid_rewrite :
      (∑ i : κ, (g i (x i) + g i (y i)) / 2) =
        (objective g x + objective g y) / 2 := by
    simp only [objective, div_eq_mul_inv, ← Finset.sum_mul,
      Finset.sum_add_distrib]
  rw [hmid_rewrite] at hsum_mid
  have hy_le : objective g y ≤ objective g x := hx_opt y hy_nonneg hy_sum
  change (∑ i : κ, g i (z i)) ≤ objective g x at hz_opt
  linarith

/-- Real optimality rules out a profitable unit transfer between two coordinates. -/
theorem pair_unit_exchange_strict_of_strictConcave_maximizer
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : κ → ℝ → ℝ) (N : ℝ) (x : κ → ℝ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = N)
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = N →
        objective g z ≤ objective g x)
    (high low : κ) (hne : high ≠ low) (hlow : 1 ≤ x low) :
    g high (x high + 1) - g high (x high) <
      g low (x low) - g low (x low - 1) := by
  let y : κ → ℝ := fun i =>
    if i = high then x i + 1 else if i = low then x i - 1 else x i
  have hy_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    by_cases hi : i = high
    · subst i
      simp [y]
      linarith [hx_nonneg high]
    · by_cases hj : i = low
      · subst i
        simp [y, hne.symm]
        linarith
      · simp [y, hi, hj, hx_nonneg i]
  have hy_sum : (∑ i : κ, y i) = N := by
    have hsum := AppliedModelingLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off
      (f := y) (g := x) hne (by
        intro i hih hil
        simp [y, hih, hil])
    simp [y, hne.symm] at hsum
    linarith
  have hy_ne : y ≠ x := by
    intro heq
    have hhigh := congrFun heq high
    simp [y] at hhigh
  have hobj := objective_lt_of_ne_of_strictConcave_maximizer
    g N x y hconc hx_nonneg hx_sum hx_opt hy_nonneg hy_sum hy_ne
  have hsum := AppliedModelingLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off
    (f := fun i => g i (y i)) (g := fun i => g i (x i)) hne (by
      intro i hih hil
      simp [y, hih, hil])
  simp [objective, y, hne.symm] at hobj hsum
  linarith

/-- Unit increments of a concave function are antitone. -/
theorem unit_increment_antitone_of_concaveOn
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    f (y + 1) - f y ≤ f (x + 1) - f x := by
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  have hy : 0 ≤ y := hx.trans hxy.le
  have hx1 : x + 1 ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ x + 1
    linarith
  have hy1 : y + 1 ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ y + 1
    linarith
  have hfirst := hf.neg.secant_mono
    (show x ∈ Set.Ici (0 : ℝ) by exact hx)
    hx1 hy1
    (by linarith : x + 1 ≠ x)
    (by linarith : y + 1 ≠ x)
    (by linarith : x + 1 ≤ y + 1)
  have hsecond := hf.neg.secant_mono
    hy1
    (show x ∈ Set.Ici (0 : ℝ) by exact hx)
    (show y ∈ Set.Ici (0 : ℝ) by exact hy)
    (by linarith : x ≠ y + 1)
    (by linarith : y ≠ y + 1)
    hxy.le
  simp only [Pi.neg_apply] at hfirst hsecond
  have hA :
      (f (y + 1) - f x) / (y + 1 - x) ≤ f (x + 1) - f x := by
    rw [show x + 1 - x = (1 : ℝ) by ring, div_one] at hfirst
    ring_nf at hfirst ⊢
    linarith
  have hB :
      f (y + 1) - f y ≤ (f (y + 1) - f x) / (y + 1 - x) := by
    rw [show x - (y + 1) = -(y + 1 - x) by ring,
      show y - (y + 1) = -(1 : ℝ) by ring,
      div_neg, div_neg, div_one] at hsecond
    ring_nf at hsecond ⊢
    linarith
  exact hB.trans hA

/-- Unit increments of a strictly concave function are strictly antitone. -/
theorem unit_increment_strictAntitone_of_strictConcaveOn
    (f : ℝ → ℝ) (hf : StrictConcaveOn ℝ (Set.Ici 0) f)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    f (y + 1) - f y < f (x + 1) - f x := by
  have hy : 0 ≤ y := hx.trans hxy.le
  have hx1 : x + 1 ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ x + 1
    linarith
  have hy1 : y + 1 ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ y + 1
    linarith
  have hfirst := hf.neg.secant_strict_mono
    (show x ∈ Set.Ici (0 : ℝ) by exact hx)
    hx1 hy1
    (by linarith : x + 1 ≠ x)
    (by linarith : y + 1 ≠ x)
    (by linarith : x + 1 < y + 1)
  have hsecond := hf.neg.secant_strict_mono
    hy1
    (show x ∈ Set.Ici (0 : ℝ) by exact hx)
    (show y ∈ Set.Ici (0 : ℝ) by exact hy)
    (by linarith : x ≠ y + 1)
    (by linarith : y ≠ y + 1)
    hxy
  simp only [Pi.neg_apply] at hfirst hsecond
  have hA :
      (f (y + 1) - f x) / (y + 1 - x) < f (x + 1) - f x := by
    rw [show x + 1 - x = (1 : ℝ) by ring, div_one] at hfirst
    ring_nf at hfirst ⊢
    linarith
  have hB :
      f (y + 1) - f y < (f (y + 1) - f x) / (y + 1 - x) := by
    rw [show x - (y + 1) = -(y + 1 - x) by ring,
      show y - (y + 1) = -(1 : ℝ) by ring,
      div_neg, div_neg, div_one] at hsecond
    ring_nf at hsecond ⊢
    linarith
  exact hB.trans hA

/-- Real optimality supplies the strict exchange certificate at floor/ceiling anchors. -/
theorem strict_floor_ceil_exchange_of_strictConcave_maximizer
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : κ → ℝ → ℝ) (N : ℝ) (x : κ → ℝ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = N)
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = N →
        objective g z ≤ objective g x) :
    ∀ high low : κ, 0 < ⌊x low⌋₊ →
      g high ((⌈x high⌉₊ : ℝ) + 1) - g high (⌈x high⌉₊ : ℝ) <
        g low (⌊x low⌋₊ : ℝ) - g low ((⌊x low⌋₊ - 1 : ℕ) : ℝ) := by
  intro high low hfloor_pos
  by_cases hne : high ≠ low
  · have hceil_ge : x high ≤ (⌈x high⌉₊ : ℝ) := Nat.le_ceil _
    have hhigh_bound :
        g high ((⌈x high⌉₊ : ℝ) + 1) - g high (⌈x high⌉₊ : ℝ) ≤
          g high (x high + 1) - g high (x high) :=
      unit_increment_antitone_of_concaveOn
        (g high) (hconc high).concaveOn (hx_nonneg high) hceil_ge
    have hfloor_le : (⌊x low⌋₊ : ℝ) ≤ x low := Nat.floor_le (hx_nonneg low)
    have hlow_one : (1 : ℝ) ≤ x low := by
      have hfloor_one_nat : (1 : ℕ) ≤ ⌊x low⌋₊ := Nat.succ_le_of_lt hfloor_pos
      have hfloor_one_real : (1 : ℝ) ≤ (⌊x low⌋₊ : ℝ) := by
        exact_mod_cast hfloor_one_nat
      exact hfloor_one_real.trans hfloor_le
    have hpair := pair_unit_exchange_strict_of_strictConcave_maximizer
      g N x hconc hx_nonneg hx_sum hx_opt high low hne hlow_one
    have hfloor_one : (1 : ℝ) ≤ (⌊x low⌋₊ : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hfloor_pos)
    have hstart_nonneg : 0 ≤ (⌊x low⌋₊ : ℝ) - 1 := by linarith
    have hstart_le : (⌊x low⌋₊ : ℝ) - 1 ≤ x low - 1 := by linarith
    have hlow_bound := unit_increment_antitone_of_concaveOn
      (g low) (hconc low).concaveOn hstart_nonneg hstart_le
    have hcast_sub : ((⌊x low⌋₊ - 1 : ℕ) : ℝ) = (⌊x low⌋₊ : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hfloor_pos)]
      norm_num
    norm_num at hlow_bound
    rw [hcast_sub]
    linarith
  · have heq : high = low := not_ne_iff.mp hne
    subst low
    have hfloor_one_nat : (1 : ℕ) ≤ ⌊x high⌋₊ :=
      Nat.succ_le_of_lt hfloor_pos
    have hstart_nonneg : 0 ≤ (⌊x high⌋₊ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (⌊x high⌋₊ : ℝ) := by
        exact_mod_cast hfloor_one_nat
      linarith
    have hfloor_le_ceil : ⌊x high⌋₊ ≤ ⌈x high⌉₊ := by
      exact Nat.floor_le_ceil (x high)
    have hstart_lt_ceil :
        (⌊x high⌋₊ : ℝ) - 1 < (⌈x high⌉₊ : ℝ) := by
      exact_mod_cast (show ⌊x high⌋₊ - 1 < ⌈x high⌉₊ by omega)
    have hstrict := unit_increment_strictAntitone_of_strictConcaveOn
      (g high) (hconc high) hstart_nonneg hstart_lt_ceil
    have hcast_sub : ((⌊x high⌋₊ - 1 : ℕ) : ℝ) =
        (⌊x high⌋₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hfloor_one_nat]
      norm_num
    norm_num at hstrict
    rw [hcast_sub]
    exact hstrict

/-- Real and integer optimality rule out a crossing around floor/ceiling anchors. -/
theorem noRoundingCrossingBetween_floor_ceil_of_strictConcave_maximizers
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : κ → ℝ → ℝ) (N : ℕ) (x : κ → ℝ) (a : κ → ℕ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = (N : ℝ))
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = (N : ℝ) →
        objective g z ≤ objective g x)
    (ha_sum : (∑ i : κ, a i) = N)
    (ha_opt : ∀ b : κ → ℕ, (∑ i : κ, b i) = N →
      objective g (fun i => (b i : ℝ)) ≤
        objective g (fun i => (a i : ℝ))) :
    AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
      a (fun i => ⌊x i⌋₊) (fun i => ⌈x i⌉₊) := by
  let A : AppliedModelingLib.Allocation κ := ⟨a⟩
  let lower : AppliedModelingLib.Allocation κ := ⟨fun i => ⌊x i⌋₊⟩
  let upper : AppliedModelingLib.Allocation κ := ⟨fun i => ⌈x i⌉₊⟩
  let weight : κ → ℝ := fun _ => 1
  let value : κ → ℕ → ℝ := fun i q => g i (q : ℝ)
  have hoptA : AppliedModelingLib.Allocation.IsOptimalAtTotal weight value N A := by
    constructor
    · exact ha_sum
    · intro b hb
      simpa [AppliedModelingLib.Allocation.objective, objective, A, weight, value] using
        ha_opt b.count hb
  have hDR : AppliedModelingLib.Allocation.HasDiminishingReturns value := by
    intro i q
    have h := unit_increment_antitone_of_concaveOn
      (g i) (hconc i).concaveOn
      (show 0 ≤ (q : ℝ) by positivity)
      (show (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ q)
    change
      g i ((q + 1 + 1 : ℕ) : ℝ) - g i ((q + 1 : ℕ) : ℝ) ≤
        g i ((q + 1 : ℕ) : ℝ) - g i (q : ℝ)
    norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
    ring_nf at h ⊢
    exact h
  have horder : ∀ i, lower.count i ≤ upper.count i := by
    intro i
    exact Nat.floor_le_ceil (x i)
  have hcert :
      AppliedModelingLib.Allocation.StrictRoundingExchangeCertificateBetween
        weight value lower upper := by
    intro high low hlow
    have h := strict_floor_ceil_exchange_of_strictConcave_maximizer
      g (N : ℝ) x hconc hx_nonneg hx_sum hx_opt high low hlow
    simpa [AppliedModelingLib.Allocation.weightedForwardMarginal,
      AppliedModelingLib.Allocation.weightedBackwardMarginal,
      AppliedModelingLib.Allocation.marginal, lower, upper, weight, value,
      ne_of_gt hlow] using h
  simpa [A, lower, upper] using
    AppliedModelingLib.Allocation.noRoundingCrossingBetween_of_strictExchangeCertificate
      A lower upper weight value N hoptA hDR (fun _ => by positivity) horder hcert

/--
Corrected PRPKG24 Lemma D.5.

For a separable strictly concave objective, every fixed-sum integer maximizer
lies within the number of coordinates of a fixed-sum real maximizer. This is
the source's displayed strict floor window, encoded without integer
subtraction on the lower side.
-/
theorem floor_count_close_of_strictConcave_maximizers
    {κ : Type*} [Fintype κ]
    (g : κ → ℝ → ℝ) (N : ℕ) (x : κ → ℝ) (a : κ → ℕ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = (N : ℝ))
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = (N : ℝ) →
        objective g z ≤ objective g x)
    (ha_sum : (∑ i : κ, a i) = N)
    (ha_opt : ∀ b : κ → ℕ, (∑ i : κ, b i) = N →
      objective g (fun i => (b i : ℝ)) ≤
        objective g (fun i => (a i : ℝ))) :
    ∀ t : κ,
      ⌊x t⌋₊ < a t + Fintype.card κ ∧
        a t < ⌊x t⌋₊ + Fintype.card κ := by
  classical
  have hno :=
    noRoundingCrossingBetween_floor_ceil_of_strictConcave_maximizers
      g N x a hconc hx_nonneg hx_sum hx_opt ha_sum ha_opt
  have horder : ∀ i : κ, ⌊x i⌋₊ ≤ ⌈x i⌉₊ := fun i =>
    Nat.floor_le_ceil (x i)
  intro t
  have hcard_pos : 0 < Fintype.card κ :=
    Fintype.card_pos_iff.mpr ⟨t⟩
  have hsum_floor_lt_real :
      (N : ℝ) <
        ((∑ i : κ, ⌊x i⌋₊) : ℝ) + (Fintype.card κ : ℝ) := by
    rw [← hx_sum]
    have hsum_lt :
        (∑ i : κ, x i) <
          ∑ i : κ, ((⌊x i⌋₊ : ℝ) + 1) := by
      refine Finset.sum_lt_sum
        (fun i _ => (Nat.lt_floor_add_one (x i)).le) ?_
      exact ⟨t, Finset.mem_univ t, Nat.lt_floor_add_one (x t)⟩
    simpa [Finset.sum_add_distrib] using hsum_lt
  have hsum_floor_lt :
      N < (∑ i : κ, ⌊x i⌋₊) + Fintype.card κ := by
    exact_mod_cast hsum_floor_lt_real
  have hsum_ceil_lt_real :
      ((∑ i : κ, ⌈x i⌉₊) : ℝ) <
        (N : ℝ) + (Fintype.card κ : ℝ) := by
    rw [← hx_sum]
    have hsum_lt :
        (∑ i : κ, (⌈x i⌉₊ : ℝ)) <
          ∑ i : κ, (x i + 1) := by
      refine Finset.sum_lt_sum
        (fun i _ => (Nat.ceil_lt_add_one (hx_nonneg i)).le) ?_
      exact ⟨t, Finset.mem_univ t, Nat.ceil_lt_add_one (hx_nonneg t)⟩
    simpa [Finset.sum_add_distrib] using hsum_lt
  have hsum_ceil_lt :
      (∑ i : κ, ⌈x i⌉₊) < N + Fintype.card κ := by
    exact_mod_cast hsum_ceil_lt_real
  constructor
  · by_contra hnot
    have hlow : a t + Fintype.card κ ≤ ⌊x t⌋₊ := le_of_not_gt hnot
    obtain ⟨high, hhigh_lt⟩ :=
      AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween.exists_high_of_low
        (a := a) (lower := fun i => ⌊x i⌋₊)
        (upper := fun i => ⌈x i⌉₊)
        (N := N) (U := ∑ i : κ, ⌈x i⌉₊)
        (C := Fintype.card κ) t ha_sum rfl hsum_ceil_lt horder hlow
    have hhigh_one : ⌈x high⌉₊ + 1 ≤ a high :=
      Nat.succ_le_of_lt hhigh_lt
    have hlow_one : a t + 1 ≤ ⌊x t⌋₊ := by omega
    exact hno high t ⟨hhigh_one, hlow_one⟩
  · by_contra hnot
    have hhigh : ⌊x t⌋₊ + Fintype.card κ ≤ a t := le_of_not_gt hnot
    obtain ⟨low, hlow_lt⟩ :=
      AppliedModelingLib.FiniteRounding.NoRoundingCrossing.exists_low_of_high
        (a := a) (b := fun i => ⌊x i⌋₊)
        (N := N) (B := ∑ i : κ, ⌊x i⌋₊)
        (C := Fintype.card κ) t ha_sum rfl hsum_floor_lt hhigh
    have hne : t ≠ low := by
      intro heq
      subst low
      have hfloor_lt_a : ⌊x t⌋₊ < a t := by omega
      exact (not_lt_of_ge (Nat.le_of_lt hlow_lt)) hfloor_lt_a
    letI : Nontrivial κ := ⟨⟨t, low, hne⟩⟩
    have hcard_two : 2 ≤ Fintype.card κ := by
      exact Nat.succ_le_iff.mpr Fintype.one_lt_card
    have hceil_one : ⌈x t⌉₊ + 1 ≤ a t := by
      have hceil_floor : ⌈x t⌉₊ ≤ ⌊x t⌋₊ + 1 :=
        Nat.ceil_le_floor_add_one (x t)
      omega
    have hlow_one : a low + 1 ≤ ⌊x low⌋₊ :=
      Nat.succ_le_of_lt hlow_lt
    exact hno t low ⟨hceil_one, hlow_one⟩

end GeneralRounding
end PRPKG24AccuracyDiversity

import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace AppliedModelingLib

noncomputable section

/-!
# Finite Optimization Helpers

Small reusable wrappers around `Finset.sup'` and `Finset.inf'` for finite
nonempty index types, plus compact finite-simplex domains for continuous
optimization.
-/

/-- Finite nonnegative vectors with total mass one. -/
def FiniteProbabilitySimplex {α : Type*} [Fintype α]
    (mass : α → ℝ) : Prop :=
  (∀ i : α, 0 ≤ mass i) ∧ (∑ i : α, mass i) = 1

/-- The finite real probability simplex is convex. -/
theorem finiteProbabilitySimplex_convex {α : Type*} [Fintype α] :
    Convex ℝ {mass : α → ℝ | FiniteProbabilitySimplex mass} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg
      (mul_nonneg ha (hx.1 i))
      (mul_nonneg hb (hy.1 i))
  · change (∑ i : α, (a * x i + b * y i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hx.2, hy.2, mul_one, mul_one]
    exact hab

/-- A segment from a finite simplex point in the direction of another such point stays feasible. -/
theorem finiteProbabilitySimplex_segment_update_add_sub
    {α : Type*} [Fintype α] (update target : α → ℝ)
    (hupdate : FiniteProbabilitySimplex update)
    (htarget : FiniteProbabilitySimplex target) :
    segment ℝ update (update + (target - update)) ⊆
      {mass : α → ℝ | FiniteProbabilitySimplex mass} := by
  have hend : update + (target - update) = target := by
    ext coordinate
    simp
  rw [hend]
  exact finiteProbabilitySimplex_convex.segment_subset hupdate htarget

/-- A finite probability-simplex coordinate is at most one. -/
theorem finiteProbabilitySimplex_coord_le_one
    {α : Type*} [Fintype α] {mass : α → ℝ}
    (hmass : FiniteProbabilitySimplex mass) (i : α) :
    mass i ≤ 1 := by
  have hle_sum : mass i ≤ ∑ j : α, mass j := by
    exact Finset.single_le_sum (fun j _hj => hmass.1 j) (by simp)
  simpa [hmass.2] using hle_sum

/--
The finite probability simplex is contained in the product cube `[0,1]^α`.
-/
theorem finiteProbabilitySimplex_subset_pi_Icc
    {α : Type*} [Fintype α] :
    {mass : α → ℝ | FiniteProbabilitySimplex mass} ⊆
      Set.univ.pi (fun _ : α => Set.Icc (0 : ℝ) 1) := by
  intro mass hmass i _hi
  exact ⟨hmass.1 i, finiteProbabilitySimplex_coord_le_one hmass i⟩

/-- The finite probability simplex is closed in the product topology. -/
theorem finiteProbabilitySimplex_isClosed
    {α : Type*} [Fintype α] :
    IsClosed {mass : α → ℝ | FiniteProbabilitySimplex mass} := by
  have hnonneg :
      IsClosed {mass : α → ℝ | ∀ i : α, 0 ≤ mass i} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter fun i : α =>
        (isClosed_Ici.preimage (continuous_apply i) :
          IsClosed {mass : α → ℝ | mass i ∈ Set.Ici (0 : ℝ)}))
  have hsum_cont : Continuous (fun mass : α → ℝ => ∑ i : α, mass i) :=
    continuous_finset_sum _ fun i _hi => continuous_apply i
  have hsum :
      IsClosed {mass : α → ℝ | (∑ i : α, mass i) = 1} :=
    isClosed_eq hsum_cont continuous_const
  simpa [FiniteProbabilitySimplex, Set.setOf_and] using hnonneg.inter hsum

/-- The finite probability simplex is compact. -/
theorem finiteProbabilitySimplex_isCompact
    {α : Type*} [Fintype α] :
    IsCompact {mass : α → ℝ | FiniteProbabilitySimplex mass} := by
  have hcube :
      IsCompact (Set.univ.pi (fun _ : α => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ : α => isCompact_Icc
  exact hcube.of_isClosed_subset
    finiteProbabilitySimplex_isClosed
    finiteProbabilitySimplex_subset_pi_Icc

/-- The finite probability simplex is nonempty for nonempty finite index types. -/
theorem finiteProbabilitySimplex_nonempty
    {α : Type*} [Fintype α] [Nonempty α] :
    ({mass : α → ℝ | FiniteProbabilitySimplex mass}).Nonempty := by
  let u : ℝ := (Fintype.card α : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  refine ⟨fun _i : α => u, ?_⟩
  constructor
  · intro _i
    dsimp [u]
    exact inv_nonneg.mpr hcard_pos.le
  · calc
      (∑ _i : α, u) = (Fintype.card α : ℝ) * u := by
        simp [nsmul_eq_mul]
      _ = 1 := by
        dsimp [u]
        field_simp [ne_of_gt hcard_pos]

/-- The uniform mass function belongs to the finite probability simplex. -/
theorem uniformProbabilityMass_finiteProbabilitySimplex
    {α : Type*} [Fintype α] [Nonempty α] :
    FiniteProbabilitySimplex (fun _i : α => (Fintype.card α : ℝ)⁻¹) := by
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  constructor
  · intro _i
    exact inv_nonneg.mpr hcard_pos.le
  · calc
      (∑ _i : α, (Fintype.card α : ℝ)⁻¹) =
          (Fintype.card α : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
            simp [nsmul_eq_mul]
      _ = 1 := by field_simp [hcard_pos.ne']

/-- Finite maximum of a real-valued function on a nonempty finite type. -/
def finiteMax {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).sup' Finset.univ_nonempty f

/-- Finite minimum of a real-valued function on a nonempty finite type. -/
def finiteMin {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).inf' Finset.univ_nonempty f

/-- A finite maximum is at least every indexed value. -/
theorem le_finiteMax {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (a : α) :
    f a ≤ finiteMax f := by
  unfold finiteMax
  exact Finset.le_sup' (s := (Finset.univ : Finset α)) (f := f) (by simp)

/-- A finite maximum is attained. -/
theorem exists_finiteMax_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    ∃ a : α, finiteMax f = f a := by
  unfold finiteMax
  obtain ⟨a, _ha, hmax⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset α))
      (H := Finset.univ_nonempty) (f := f)
  exact ⟨a, hmax⟩

/-- A finite minimum is at most every indexed value. -/
theorem finiteMin_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (a : α) :
    finiteMin f ≤ f a := by
  unfold finiteMin
  exact Finset.inf'_le (s := (Finset.univ : Finset α)) (f := f) (by simp)

/-- A finite minimum is attained. -/
theorem exists_finiteMin_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    ∃ a : α, finiteMin f = f a := by
  unfold finiteMin
  obtain ⟨a, _ha, hmin⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset α))
      (H := Finset.univ_nonempty) (f := f)
  exact ⟨a, hmin⟩

/-- A finite minimum is at most any upper bound on one indexed value. -/
theorem finiteMin_le_of_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (a : α) {c : ℝ} (h : f a ≤ c) :
    finiteMin f ≤ c :=
  (finiteMin_le f a).trans h

/-- A finite minimum is at least any pointwise lower bound. -/
theorem le_finiteMin {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {c : ℝ} (h : ∀ a, c ≤ f a) :
    c ≤ finiteMin f := by
  unfold finiteMin
  exact Finset.le_inf' (s := (Finset.univ : Finset α)) (f := f)
    Finset.univ_nonempty
    (by intro a _ha; exact h a)

/-- A finite minimum of a constant-valued function equals that constant. -/
theorem finiteMin_eq_of_forall {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) (h : ∀ a, f a = c) :
    finiteMin f = c := by
  unfold finiteMin
  apply le_antisymm
  · let a0 : α := Classical.choice inferInstance
    exact (Finset.inf'_le
      (s := (Finset.univ : Finset α)) (f := f) (by simp : a0 ∈ Finset.univ)).trans_eq
      (h a0)
  · apply Finset.le_inf'
    intro a _ha
    exact le_of_eq (h a).symm

/-- A finite minimum of nonnegative values is nonnegative. -/
theorem finiteMin_nonneg {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (h : ∀ a, 0 ≤ f a) :
    0 ≤ finiteMin f := by
  unfold finiteMin
  apply Finset.le_inf'
  intro a _ha
  exact h a

/-- A finite minimum of strictly positive values is strictly positive. -/
theorem finiteMin_pos {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (h : ∀ a, 0 < f a) :
    0 < finiteMin f := by
  unfold finiteMin
  rw [Finset.lt_inf'_iff]
  intro a _ha
  exact h a

/--
Every coordinate vector in a finite probability simplex has some coordinate
at least the uniform mass.  This is the finite simplex pigeonhole bound.
-/
theorem finiteProbabilitySimplex_inv_card_le_finiteMax
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hmass : FiniteProbabilitySimplex mass) :
    (Fintype.card α : ℝ)⁻¹ ≤ finiteMax mass := by
  by_contra hbound
  have hstrict : finiteMax mass < (Fintype.card α : ℝ)⁻¹ := lt_of_not_ge hbound
  have hcoord : ∀ i : α, mass i < (Fintype.card α : ℝ)⁻¹ := fun i =>
    (le_finiteMax mass i).trans_lt hstrict
  have hsum_lt : (∑ i : α, mass i) < ∑ _i : α, (Fintype.card α : ℝ)⁻¹ := by
    exact Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset α))
      Finset.univ_nonempty (fun i hi => hcoord i)
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have huniform_sum : (∑ _i : α, (Fintype.card α : ℝ)⁻¹) = 1 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hmass.2, huniform_sum] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-- The finite maximum of the uniform probability vector is its uniform mass. -/
theorem finiteMax_uniformProbabilityMass
    {α : Type*} [Fintype α] [Nonempty α] :
    finiteMax (fun _i : α => (Fintype.card α : ℝ)⁻¹) =
      (Fintype.card α : ℝ)⁻¹ := by
  apply le_antisymm
  · unfold finiteMax
    apply Finset.sup'_le
    intro i hi
    rfl
  · let i : α := Classical.choice inferInstance
    exact le_finiteMax (fun _i : α => (Fintype.card α : ℝ)⁻¹) i

/--
On a finite simplex, the sum of squares is minimized by the uniform vector.
This is the Cauchy-Schwarz form used by finite interval-partition objectives.
-/
theorem simplex_inv_card_le_sum_sq
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hsum : (∑ i : α, mass i) = 1) :
    ((Fintype.card α : ℝ)⁻¹) ≤ ∑ i : α, (mass i) ^ 2 := by
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hcs :=
    FiniteSum.sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset α)) (f := mass)
  have hmul :
      (1 : ℝ) ≤ (Fintype.card α : ℝ) * ∑ i : α, (mass i) ^ 2 := by
    simpa [hsum] using hcs
  have hdiv :=
    div_le_div_of_nonneg_right hmul hcard_pos.le
  simpa [one_div, mul_div_cancel_left₀ _ hcard_ne] using hdiv

/--
Equality in the finite Cauchy simplex bound forces the uniform vector.  This is
the equality case used when symmetric finite partition objectives have a value
tie at the uniform partition.
-/
theorem simplex_eq_inv_card_of_sum_sq_eq_inv_card
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hsum : (∑ i : α, mass i) = 1)
    (hsq : (∑ i : α, (mass i) ^ 2) =
      ((Fintype.card α : ℝ)⁻¹)) :
    ∀ i : α, mass i = (Fintype.card α : ℝ)⁻¹ := by
  let u : ℝ := (Fintype.card α : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hdev :
      (∑ i : α, (mass i - u) ^ 2) = 0 := by
    have hcalc :
        (∑ i : α, (mass i - u) ^ 2) =
          (∑ i : α, (mass i) ^ 2) - u := by
      calc
        (∑ i : α, (mass i - u) ^ 2)
            = ∑ i : α, ((mass i) ^ 2 - (2 * u) * mass i + u ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
        _ = (∑ i : α, (mass i) ^ 2) -
              2 * u * (∑ i : α, mass i) +
              (Fintype.card α : ℝ) * u ^ 2 := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                Finset.mul_sum, mul_assoc]
        _ = (∑ i : α, (mass i) ^ 2) - u := by
              rw [hsum]
              dsimp [u]
              field_simp [hcard_ne]
              ring
    rw [hcalc, hsq]
    dsimp [u]
    ring
  have hzero :
      ∀ i : α, (mass i - u) ^ 2 = 0 := by
    have hnonneg :
        ∀ x ∈ (Finset.univ : Finset α), 0 ≤ (mass x - u) ^ 2 := by
      intro x _hx
      exact sq_nonneg _
    simpa using
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdev
  intro i
  have hi : mass i - u = 0 := sq_eq_zero_iff.mp (hzero i)
  dsimp [u] at hi ⊢
  linarith

/--
Equivalent one-minus-sum-of-squares form: the objective
`(1 - ∑ᵢ massᵢ²) / 2` is at most its uniform-simplex value.
-/
theorem simplex_one_sub_sum_sq_div_two_le_uniform
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hsum : (∑ i : α, mass i) = 1) :
    (1 - ∑ i : α, (mass i) ^ 2) / 2 ≤
      (1 - (Fintype.card α : ℝ)⁻¹) / 2 := by
  have hsq := simplex_inv_card_le_sum_sq mass hsum
  linarith

/--
On a finite simplex, the sum of cubes of nonnegative masses is minimized by
the uniform vector.  This is the `p = 3` power-mean/Jensen inequality in the
normalization useful for interval objectives.
-/
theorem simplex_inv_card_sq_le_sum_cube
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hmass_nonneg : ∀ i : α, 0 ≤ mass i)
    (hsum : (∑ i : α, mass i) = 1) :
    ((Fintype.card α : ℝ)⁻¹) ^ 2 ≤ ∑ i : α, (mass i) ^ 3 := by
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hcard_sq_pos : 0 < (Fintype.card α : ℝ) ^ 2 := sq_pos_of_ne_zero hcard_ne
  have hcard_sq_ne : (Fintype.card α : ℝ) ^ 2 ≠ 0 := ne_of_gt hcard_sq_pos
  have hpow :=
    pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset α)) (f := mass)
      (by intro i _hi; exact hmass_nonneg i) 2
  have hmul :
      (1 : ℝ) ≤ (Fintype.card α : ℝ) ^ 2 *
          ∑ i : α, (mass i) ^ 3 := by
    simpa [hsum] using hpow
  have hdiv :=
    div_le_div_of_nonneg_right hmul hcard_sq_pos.le
  simpa [one_div, inv_pow, mul_div_cancel_left₀ _ hcard_sq_ne] using hdiv

/--
Equality in the finite nonnegative cube simplex bound also forces the uniform
vector.  This packages the equality case needed for Spearman-style interval
objectives after reducing them to cubic gap sums.
-/
theorem simplex_eq_inv_card_of_sum_cube_eq_inv_card_sq
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hmass_nonneg : ∀ i : α, 0 ≤ mass i)
    (hsum : (∑ i : α, mass i) = 1)
    (hcube : (∑ i : α, (mass i) ^ 3) =
      ((Fintype.card α : ℝ)⁻¹) ^ 2) :
    ∀ i : α, mass i = (Fintype.card α : ℝ)⁻¹ := by
  let u : ℝ := (Fintype.card α : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hu_pos : 0 < u := by
    dsimp [u]
    exact inv_pos.mpr hcard_pos
  have hsq_ge :
      u ≤ ∑ i : α, (mass i) ^ 2 := by
    dsimp [u]
    exact simplex_inv_card_le_sum_sq mass hsum
  have hidentity :
      (∑ i : α, mass i * (mass i - u) ^ 2) +
          2 * u * ((∑ i : α, (mass i) ^ 2) - u) =
        (∑ i : α, (mass i) ^ 3) - u ^ 2 := by
    calc
      (∑ i : α, mass i * (mass i - u) ^ 2) +
          2 * u * ((∑ i : α, (mass i) ^ 2) - u)
          =
        (∑ i : α, ((mass i) ^ 3 - 2 * u * (mass i) ^ 2 +
            u ^ 2 * mass i)) +
          2 * u * ((∑ i : α, (mass i) ^ 2) - u) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ =
        ((∑ i : α, (mass i) ^ 3) -
            2 * u * (∑ i : α, (mass i) ^ 2) +
            u ^ 2 * (∑ i : α, mass i)) +
          2 * u * ((∑ i : α, (mass i) ^ 2) - u) := by
            congr 1
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum, mul_assoc]
      _ = (∑ i : α, (mass i) ^ 3) - u ^ 2 := by
            rw [hsum]
            ring
  have htotal :
      (∑ i : α, mass i * (mass i - u) ^ 2) +
          2 * u * ((∑ i : α, (mass i) ^ 2) - u) = 0 := by
    rw [hidentity, hcube]
    dsimp [u]
    ring
  have hweighted_nonneg :
      0 ≤ ∑ i : α, mass i * (mass i - u) ^ 2 := by
    exact Finset.sum_nonneg fun i _hi =>
      mul_nonneg (hmass_nonneg i) (sq_nonneg _)
  have hsq_term_nonneg :
      0 ≤ 2 * u * ((∑ i : α, (mass i) ^ 2) - u) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hu_pos.le)
      (sub_nonneg.mpr hsq_ge)
  have hsq_term_le_zero :
      2 * u * ((∑ i : α, (mass i) ^ 2) - u) ≤ 0 := by
    nlinarith
  have hsq_le :
      (∑ i : α, (mass i) ^ 2) ≤ u := by
    nlinarith [hu_pos]
  have hsq_eq :
      (∑ i : α, (mass i) ^ 2) = u :=
    le_antisymm hsq_le hsq_ge
  exact
    simplex_eq_inv_card_of_sum_sq_eq_inv_card
      mass hsum (by
        dsimp [u] at hsq_eq
        simpa using hsq_eq)

/--
Equivalent one-minus-sum-of-cubes form: the objective
`(1 - ∑ᵢ massᵢ³) / 6` is at most its uniform-simplex value.
-/
theorem simplex_one_sub_sum_cube_div_six_le_uniform
    {α : Type*} [Fintype α] [Nonempty α] (mass : α → ℝ)
    (hmass_nonneg : ∀ i : α, 0 ≤ mass i)
    (hsum : (∑ i : α, mass i) = 1) :
    (1 - ∑ i : α, (mass i) ^ 3) / 6 ≤
      (1 - ((Fintype.card α : ℝ)⁻¹) ^ 2) / 6 := by
  have hcube := simplex_inv_card_sq_le_sum_cube mass hmass_nonneg hsum
  linarith

/--
Abstract finite maximin certificate.  If a candidate has every component equal
to `R`, and every feasible alternative has some component at most `R`, then
the candidate maximizes the finite minimum objective over the feasible set.
-/
theorem finiteMin_maximal_of_equalized_and_exists_component_le
    {α β : Type*} [Fintype α] [Nonempty α]
    (rate : β → α → ℝ) (feasible : β → Prop)
    (x : β) {R : ℝ}
    (hx_eq : ∀ a : α, rate x a = R)
    (halt : ∀ y : β, feasible y → ∃ a : α, rate y a ≤ R) :
    ∀ y : β, feasible y → finiteMin (rate y) ≤ finiteMin (rate x) := by
  intro y hy
  rcases halt y hy with ⟨a, ha⟩
  have hx_min : finiteMin (rate x) = R :=
    finiteMin_eq_of_forall (rate x) R hx_eq
  exact (finiteMin_le_of_le (rate y) a ha).trans_eq hx_min.symm

/--
Adjacent strict inequalities imply a strict inequality across the whole
integer chain.
-/
theorem lt_of_adjacent_lt_chain
    (x : ℕ → ℝ) {i j : ℕ} (hij : i < j)
    (hstep : ∀ k : ℕ, i ≤ k → k < j → x k < x (k + 1)) :
    x i < x j := by
  have hsucc : i + 1 ≤ j := Nat.succ_le_of_lt hij
  have hbase :
      i + 1 ≤ j → x i < x (i + 1) := by
    intro _h
    exact hstep i le_rfl hij
  have hind :
      ∀ n : ℕ, i + 1 ≤ n →
        (n ≤ j → x i < x n) →
        (n + 1 ≤ j → x i < x (n + 1)) := by
    intro n hle ih hn1
    have hn_lt_j : n < j := Nat.lt_of_succ_le hn1
    have hi_le_n : i ≤ n := (Nat.le_succ i).trans hle
    exact (ih hn_lt_j.le).trans (hstep n hi_le_n hn_lt_j)
  exact
    (Nat.le_induction
      (P := fun n _ => n ≤ j → x i < x n)
      hbase hind j hsucc) le_rfl

/-- Telescoping sum of adjacent differences along a natural-number chain. -/
theorem sum_range_adjacent_sub
    (x : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (x (k + 1) - x k)) = x n - x 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Adjacent gap vector induced by a finite cutpoint chain. -/
def finiteAdjacentGap (M : ℕ) (s : ℕ → ℝ) : Fin M → ℝ :=
  fun i => s (i.1 + 1) - s i.1

/--
Every monotone cutpoint chain with endpoints `0` and `1` induces a finite
probability simplex of adjacent gaps.
-/
theorem finiteProbabilitySimplex_finiteAdjacentGap_of_monotone_endpoint
    {M : ℕ} (s : ℕ → ℝ) (hmono : Monotone s)
    (h0 : s 0 = 0) (hM : s M = 1) :
    FiniteProbabilitySimplex (finiteAdjacentGap M s) := by
  constructor
  · intro i
    exact sub_nonneg.mpr (hmono (Nat.le_succ i.1))
  · calc
      (∑ i : Fin M, finiteAdjacentGap M s i)
          =
            ∑ k ∈ Finset.range M,
              (if h : k < M then
                finiteAdjacentGap M s ⟨k, h⟩
              else 0) := by
            exact
              Finset.sum_fin_eq_sum_range
                (fun i : Fin M => finiteAdjacentGap M s i)
      _ = ∑ k ∈ Finset.range M, (s (k + 1) - s k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hkM : k < M := Finset.mem_range.mp hk
            simp [finiteAdjacentGap, hkM]
      _ = 1 := by
            simpa [h0, hM] using sum_range_adjacent_sub s M

/--
The prefix cutpoints induced by a cutpoint chain's adjacent gaps recover the
original cutpoints on the finite range.
-/
theorem finiteGapCutpoint_finiteAdjacentGap_eq
    {M : ℕ} (s : ℕ → ℝ) (h0 : s 0 = 0) :
    ∀ k : ℕ, k ≤ M →
      FiniteSum.finiteGapCutpoint (finiteAdjacentGap M s) k = s k := by
  intro k hk
  unfold FiniteSum.finiteGapCutpoint
  have hsum :
      FiniteSum.finitePartitionPrefix
          (FiniteSum.finiteGapExtend (finiteAdjacentGap M s)) k =
        ∑ r ∈ Finset.range k, (s (r + 1) - s r) := by
    unfold FiniteSum.finitePartitionPrefix
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hr_lt_M : r < M := (Finset.mem_range.mp hr).trans_le hk
    simp [FiniteSum.finiteGapExtend, finiteAdjacentGap, hr_lt_M]
  rw [hsum]
  simpa [h0] using sum_range_adjacent_sub s k

/--
If a chain starts at `0`, ends at `1`, and its last adjacent gap is no larger
than every adjacent gap, then that last gap is at most the reciprocal of the
number of gaps.
-/
theorem last_gap_le_inv_of_last_gap_le_all
    (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (h0 : x 0 = 0) (hN : x n = 1)
    (hlast :
      ∀ k : ℕ, k < n →
        x n - x (n - 1) ≤ x (k + 1) - x k) :
    x n - x (n - 1) ≤ 1 / (n : ℝ) := by
  let d : ℝ := x n - x (n - 1)
  have hsum_le :
      (∑ _k ∈ Finset.range n, d) ≤
        ∑ k ∈ Finset.range n, (x (k + 1) - x k) := by
    exact Finset.sum_le_sum (by
      intro k hk
      exact hlast k (Finset.mem_range.mp hk))
  have hsum_width :
      (∑ k ∈ Finset.range n, (x (k + 1) - x k)) = 1 := by
    rw [sum_range_adjacent_sub x n, h0, hN]
    ring
  have hnd_le_one : (n : ℝ) * d ≤ 1 := by
    calc
      (n : ℝ) * d =
          (∑ _k ∈ Finset.range n, d) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range n, (x (k + 1) - x k) := hsum_le
      _ = 1 := hsum_width
  have hn_pos_real : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    d = ((n : ℝ) * d) / (n : ℝ) := by
      field_simp [hn_pos_real.ne']
    _ ≤ 1 / (n : ℝ) :=
      div_le_div_of_nonneg_right hnd_le_one hn_pos_real.le

/--
One-dimensional cascade obstruction for finite maximin equalization proofs.
If improving component `0` forces coordinate `1` up, improving each component
`i < m` propagates that strict increase from coordinate `i` to `i+1`, and an
increase at coordinate `m` blocks improvement of the last component, then not
all components `0, ..., m` can be strictly above `r`.
-/
theorem exists_index_le_of_endpoint_cascade
    {m : ℕ} (hm : 0 < m)
    {candidate alternative : ℕ → ℝ} {rate : ℕ → ℝ} {r : ℝ}
    (hfirst : r < rate 0 → candidate 1 < alternative 1)
    (hstep :
      ∀ i : ℕ, 1 ≤ i → i < m →
        candidate i < alternative i → r < rate i →
          candidate (i + 1) < alternative (i + 1))
    (hlast : candidate m < alternative m → rate m ≤ r) :
    ∃ i : ℕ, i ≤ m ∧ rate i ≤ r := by
  by_contra hnone
  have hall_gt : ∀ i : ℕ, i ≤ m → r < rate i := by
    intro i hi
    exact lt_of_not_ge (by
      intro hle
      exact hnone ⟨i, hi, hle⟩)
  have hcoord_one : candidate 1 < alternative 1 :=
    hfirst (hall_gt 0 (Nat.zero_le m))
  have hprop :
      ∀ k : ℕ, 1 ≤ k → k ≤ m → candidate k < alternative k := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
        intro _hkm
        exact hcoord_one
    | succ n hn ih =>
        intro hsuccm
        have hn_le_m : n ≤ m := Nat.le_of_lt (Nat.lt_of_succ_le hsuccm)
        have hn_lt_m : n < m := Nat.lt_of_succ_le hsuccm
        exact
          hstep n hn hn_lt_m (ih hn_le_m) (hall_gt n hn_le_m)
  have hm_ge_one : 1 ≤ m := Nat.succ_le_iff.mpr hm
  exact (not_lt_of_ge (hlast (hprop m hm_ge_one le_rfl))) (hall_gt m le_rfl)

end

end AppliedModelingLib

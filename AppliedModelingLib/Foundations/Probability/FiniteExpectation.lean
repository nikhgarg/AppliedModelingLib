import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators
open MeasureTheory

namespace AppliedModelingLib

/-- Finite expectation of a real-valued function under a PMF. -/
noncomputable def pmfExp {α : Type*} [Fintype α]
    (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

/-- A probability mass function on a nonempty subsingleton carrier is unique. -/
theorem pmf_eq_of_subsingleton {α : Type*} [Nonempty α] [Subsingleton α]
    (p q : PMF α) : p = q := by
  classical
  let a : α := Classical.choice (inferInstance : Nonempty α)
  have pmass : p a = 1 := (p.apply_eq_one_iff a).mpr (by
    apply Set.Subset.antisymm
    · intro x _
      simp only [Set.mem_singleton_iff]
      exact Subsingleton.elim _ _
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      obtain ⟨y, hy⟩ := p.support_nonempty
      simpa [Subsingleton.elim y a] using hy)
  have qmass : q a = 1 := (q.apply_eq_one_iff a).mpr (by
    apply Set.Subset.antisymm
    · intro x _
      simp only [Set.mem_singleton_iff]
      exact Subsingleton.elim _ _
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      obtain ⟨y, hy⟩ := q.support_nonempty
      simpa [Subsingleton.elim y a] using hy)
  apply PMF.ext
  intro x
  calc
    p x = p a := by rw [Subsingleton.elim x a]
    _ = 1 := pmass
    _ = q a := qmass.symm
    _ = q x := by rw [Subsingleton.elim x a]

/-- Finite PMF expectation of a vector-valued statistic. -/
noncomputable def pmfVectorExp {α V : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : PMF α) (f : α → V) : V :=
  ∑ a, (μ a).toReal • f a

/-- Finite vector expectation is linear under pointwise subtraction. -/
theorem pmfVectorExp_sub {α V : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : PMF α) (f g : α → V) :
    pmfVectorExp μ (fun a => f a - g a) = pmfVectorExp μ f - pmfVectorExp μ g := by
  unfold pmfVectorExp
  calc
    ∑ a, (μ a).toReal • (f a - g a) =
        ∑ a, ((μ a).toReal • f a - (μ a).toReal • g a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [smul_sub]
    _ = (∑ a, (μ a).toReal • f a) - ∑ a, (μ a).toReal • g a := by
      rw [Finset.sum_sub_distrib]

/-- Finite PMF expectation is the Bochner integral over the PMF's measure. -/
theorem pmfExp_eq_integral_toMeasure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfExp μ f = ∫ a, f a ∂μ.toMeasure := by
  simpa [pmfExp] using (PMF.integral_eq_sum μ f).symm

/-- The finite expectation of the point-mass probability at a fixed atom is
the atom's probability under the sampled PMF. -/
theorem pmfExp_pure_mass {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (atom : α) :
    pmfExp μ (fun outcome => (PMF.pure outcome atom).toReal) = (μ atom).toReal := by
  classical
  unfold pmfExp
  have hpure (outcome : α) :
      (PMF.pure outcome atom).toReal = if outcome = atom then (1 : ℝ) else 0 := by
    by_cases houtcome : outcome = atom
    · subst outcome
      simp [PMF.pure_apply]
    · have hatom : atom ≠ outcome := fun h => houtcome h.symm
      simp [PMF.pure_apply, houtcome, hatom]
  simp_rw [hpure]
  rw [Finset.sum_eq_single atom]
  · simp
  · intro outcome _ houtcome
    simp [houtcome]
  · simp

/-- Expectation for two independent PMF draws. -/
noncomputable def pmfPairExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) : ℝ :=
  pmfExp μ (fun a => pmfExp ν (fun b => f a b))

/-- Independent finite product PMF with identical coordinate law. -/
noncomputable def pmfProduct (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : PMF α) : PMF (ι → α) :=
  PMF.ofFintype (fun f : ι → α => ∏ i : ι, μ (f i)) (by
    classical
    have hcoord : ∑ a : α, μ a = 1 := by
      rw [← PMF.tsum_coe μ, tsum_fintype]
    calc
      ∑ f : ι → α, ∏ i : ι, μ (f i)
          = ∏ i : ι, ∑ a : α, μ a := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _i : ι => (Finset.univ : Finset α))
                (f := fun _i a => μ a))
      _ = 1 := by simp [hcoord])

@[simp] theorem pmfProduct_apply {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : PMF α) (f : ι → α) :
    pmfProduct ι α μ f = ∏ i : ι, μ (f i) := by
  simp [pmfProduct]

/-- Evaluating the one-coordinate iid product indexed by `PUnit` recovers its
underlying PMF. -/
@[simp] theorem pmfProduct_punit_map_apply {α : Type*} [Fintype α]
    (μ : PMF α) :
    (pmfProduct PUnit α μ).map (fun sample => sample PUnit.unit) = μ := by
  classical
  apply PMF.ext
  intro value
  rw [PMF.map_apply, tsum_fintype]
  refine (Finset.sum_eq_single (fun _ : PUnit => value) ?_ ?_).trans ?_
  · intro sample _ hsample
    by_cases hvalue : value = sample PUnit.unit
    · have hsampleEq : sample = fun _ : PUnit => value := by
        funext input
        cases input
        exact hvalue.symm
      exact (hsample hsampleEq).elim
    · simp [hvalue]
  · simp
  · simp [pmfProduct_apply]

@[simp] theorem pmfProduct_apply_toReal {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α]
    (μ : PMF α) (f : ι → α) :
    (pmfProduct ι α μ f).toReal = ∏ i : ι, (μ (f i)).toReal := by
  rw [pmfProduct_apply]
  simpa using
    (ENNReal.toReal_prod
      (s := (Finset.univ : Finset ι)) (f := fun i : ι => μ (f i)))

/-- An iid finite-product atom is positive when each coordinate atom is positive. -/
theorem pmfProduct_apply_toReal_pos_of_forall
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : PMF α) (f : ι → α)
    (hpos : ∀ i : ι, 0 < (μ (f i)).toReal) :
    0 < (pmfProduct ι α μ f).toReal := by
  rw [pmfProduct_apply_toReal]
  exact Finset.prod_pos (fun i _ => hpos i)

/-- Constant iid finite-product samples have positive mass when the atom does. -/
theorem pmfProduct_const_apply_toReal_pos
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : PMF α) (a : α) (hpos : 0 < (μ a).toReal) :
    0 < (pmfProduct ι α μ (fun _ : ι => a)).toReal :=
  pmfProduct_apply_toReal_pos_of_forall μ (fun _ : ι => a) (fun _ => hpos)

/-- Add one independent draw to a sample indexed by `ι`. -/
def extendDraw {ι α : Type*} (sample : ι → α) (newItem : α) : Option ι → α
  | none => newItem
  | some i => sample i

/-- Functions on `Option ι` are equivalent to a distinguished new draw and an old sample. -/
def optionFunEquivProd (ι α : Type*) : (Option ι → α) ≃ α × (ι → α) where
  toFun sample := (sample none, fun i => sample (some i))
  invFun pair := extendDraw pair.2 pair.1
  left_inv sample := by
    funext x
    cases x <;> rfl
  right_inv pair := by
    ext
    · rfl
    · rfl

/-- `Option (Fin a)` is a canonical one-point extension of `Fin a`. -/
def optionFinEquivFinSucc (a : ℕ) : Option (Fin a) ≃ Fin (a + 1) where
  toFun
    | none => Fin.last a
    | some i => Fin.castSucc i
  invFun j :=
    if h : j = Fin.last a then none else some (j.castPred h)
  left_inv x := by
    cases x with
    | none => simp
    | some i =>
        simp [Fin.castSucc_ne_last]
  right_inv j := by
    by_cases h : j = Fin.last a
    · subst h
      simp
    · simp [h, Fin.castSucc_castPred]

/--
An iid product sample on `Option ι` has the same finite expectation as first
drawing an iid old sample on `ι` and then drawing one independent new item.
-/
theorem pmfExp_pmfProduct_option_eq_pairExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) :
    pmfExp (pmfProduct (Option ι) α μ) F =
      pmfPairExp (pmfProduct ι α μ) μ
        (fun sample newItem => F (extendDraw sample newItem)) := by
  classical
  unfold pmfPairExp pmfExp
  let e := optionFunEquivProd ι α
  calc
    ∑ sample : Option ι → α,
        (pmfProduct (Option ι) α μ sample).toReal * F sample
        =
        ∑ pair : α × (ι → α),
          (pmfProduct (Option ι) α μ (e.symm pair)).toReal *
            F (e.symm pair) := by
          simpa [e] using
            (Equiv.sum_comp (optionFunEquivProd ι α).symm
              (fun sample : Option ι → α =>
                (pmfProduct (Option ι) α μ sample).toReal *
                  F sample)).symm
    _ =
        ∑ pair : α × (ι → α),
          ((μ pair.1).toReal * ∏ i : ι, (μ (pair.2 i)).toReal) *
            F (extendDraw pair.2 pair.1) := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          simp [e, optionFunEquivProd, extendDraw,
            Fintype.prod_option]
    _ =
        ∑ newItem : α, ∑ sample : ι → α,
          ((μ newItem).toReal * ∏ i : ι, (μ (sample i)).toReal) *
            F (extendDraw sample newItem) := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset α))
              (t := (Finset.univ : Finset (ι → α)))
              (f := fun newItem sample =>
                ((μ newItem).toReal *
                    ∏ i : ι, (μ (sample i)).toReal) *
                  F (extendDraw sample newItem)))
    _ =
        ∑ sample : ι → α, ∑ newItem : α,
          ((μ newItem).toReal * ∏ i : ι, (μ (sample i)).toReal) *
            F (extendDraw sample newItem) :=
          Finset.sum_comm
    _ =
        ∑ sample : ι → α,
          (∏ i : ι, (μ (sample i)).toReal) *
            (∑ newItem : α,
              (μ newItem).toReal * F (extendDraw sample newItem)) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro newItem _
          ring
    _ =
        ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (∑ newItem : α,
              (μ newItem).toReal * F (extendDraw sample newItem)) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [pmfProduct_apply_toReal]

/-- Append one new draw to a `Fin n`-indexed sample, using the final index for the new draw. -/
def extendFinDraw {α : Type*} (n : ℕ) (history : Fin n → α) (fresh : α) :
    Fin (n + 1) → α :=
  fun index => extendDraw history fresh ((optionFinEquivFinSucc n).symm index)

@[simp] theorem extendFinDraw_castSucc {α : Type*} {n : ℕ}
    (history : Fin n → α) (fresh : α) (index : Fin n) :
    extendFinDraw n history fresh index.castSucc = history index := by
  simp [extendFinDraw, extendDraw, optionFinEquivFinSucc, Fin.castSucc_ne_last]

@[simp] theorem extendFinDraw_last {α : Type*} (n : ℕ)
    (history : Fin n → α) (fresh : α) :
    extendFinDraw n history fresh (Fin.last n) = fresh := by
  simp [extendFinDraw, extendDraw, optionFinEquivFinSucc]

/-- Reindexing iid finite-product samples does not change finite expectation. -/
theorem pmfExp_pmfProduct_equiv
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : ι ≃ κ) (μ : PMF α) (F : (κ → α) → ℝ) :
    pmfExp (pmfProduct ι α μ)
        (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) =
      pmfExp (pmfProduct κ α μ) F := by
  classical
  unfold pmfExp
  let sampleEquiv : (ι → α) ≃ (κ → α) :=
    { toFun := fun sample j => sample (e.symm j)
      invFun := fun sample i => sample (e i)
      left_inv := by
        intro sample
        funext i
        simp
      right_inv := by
        intro sample
        funext j
        simp }
  calc
    ∑ sample : ι → α,
        (pmfProduct ι α μ sample).toReal *
          F (fun j : κ => sample (e.symm j))
        =
        ∑ sample : κ → α,
          (pmfProduct ι α μ (sampleEquiv.symm sample)).toReal *
            F sample := by
          simpa [sampleEquiv] using
            (Equiv.sum_comp sampleEquiv.symm
              (fun sample : ι → α =>
                (pmfProduct ι α μ sample).toReal *
                  F (fun j : κ => sample (e.symm j)))).symm
    _ =
        ∑ sample : κ → α,
          (pmfProduct κ α μ sample).toReal * F sample := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          have hprod :
              (pmfProduct ι α μ (sampleEquiv.symm sample)).toReal =
                (pmfProduct κ α μ sample).toReal := by
            rw [pmfProduct_apply_toReal, pmfProduct_apply_toReal]
            simpa [sampleEquiv] using
              (Equiv.prod_comp e
                (fun j : κ => (μ (sample j)).toReal))
          rw [hprod]

/--
An iid sample of length `n + 1` can be decomposed exactly into an iid history
of length `n` and one fresh draw.  This is the finite-PMF version of the
one-step filtration factorization used by stochastic-gradient analyses.
-/
theorem pmfExp_pmfProduct_finSucc_eq_pairExp
    {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ)
    (μ : PMF α) (F : (Fin (n + 1) → α) → ℝ) :
    pmfExp (pmfProduct (Fin (n + 1)) α μ) F =
      pmfPairExp (pmfProduct (Fin n) α μ) μ
        (fun history fresh => F (extendFinDraw n history fresh)) := by
  calc
    pmfExp (pmfProduct (Fin (n + 1)) α μ) F =
        pmfExp (pmfProduct (Option (Fin n)) α μ)
          (fun sample => F (fun index =>
            sample ((optionFinEquivFinSucc n).symm index))) := by
          exact (pmfExp_pmfProduct_equiv (optionFinEquivFinSucc n) μ F).symm
    _ = pmfPairExp (pmfProduct (Fin n) α μ) μ
        (fun history fresh => F (extendFinDraw n history fresh)) := by
          simpa [extendFinDraw] using
            (pmfExp_pmfProduct_option_eq_pairExp μ
              (fun sample => F (fun index =>
                sample ((optionFinEquivFinSucc n).symm index))))

/--
Flattening a finite two-level iid sample preserves finite expectations of
functions that read only the flattened coordinates.  This is useful when a
source model groups iid draws into user-level batches.
-/
theorem pmfExp_pmfProduct_pmfProduct_flatten
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (ι × κ → α) → ℝ) :
    pmfExp (pmfProduct ι (κ → α) (pmfProduct κ α μ))
        (fun sample : ι → κ → α => F (fun ij => sample ij.1 ij.2)) =
      pmfExp (pmfProduct (ι × κ) α μ) F := by
  classical
  let e : (ι → κ → α) ≃ (ι × κ → α) := (Equiv.curry ι κ α).symm
  unfold pmfExp
  calc
    ∑ sample : ι → κ → α,
        (pmfProduct ι (κ → α) (pmfProduct κ α μ) sample).toReal *
          F (fun ij => sample ij.1 ij.2)
        =
        ∑ flat : ι × κ → α,
          (pmfProduct ι (κ → α) (pmfProduct κ α μ) (e.symm flat)).toReal *
            F flat := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun sample : ι → κ → α =>
                (pmfProduct ι (κ → α) (pmfProduct κ α μ) sample).toReal *
                  F (fun ij => sample ij.1 ij.2))).symm
    _ =
        ∑ flat : ι × κ → α,
          (pmfProduct (ι × κ) α μ flat).toReal * F flat := by
          refine Finset.sum_congr rfl ?_
          intro flat _
          congr 1
          rw [pmfProduct_apply_toReal, pmfProduct_apply_toReal]
          simp_rw [pmfProduct_apply_toReal]
          simpa [e] using
            (Fintype.prod_prod_type' (fun i j => (μ (flat (i, j))).toReal)).symm

/-- The total real mass of a PMF on a finite type is `1`. -/
theorem pmfToRealSum {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    ∑ a : α, (μ a).toReal = 1 := by
  have h_univ : μ.toOuterMeasure (Set.univ : Set α) = 1 := by
    exact (PMF.toOuterMeasure_apply_eq_one_iff (p := μ) (s := (Set.univ : Set α))).2
      (by intro a _; simp)
  have h_sum_enn : ∑ a : α, μ a = 1 := by
    calc
      ∑ a : α, μ a = μ.toOuterMeasure (Set.univ : Set α) := by
        symm
        simpa using (PMF.toOuterMeasure_apply_fintype (p := μ) (s := (Set.univ : Set α)))
      _ = 1 := h_univ
  have h_ne_top : ∀ a ∈ (Finset.univ : Finset α), μ a ≠ ⊤ := by
    intro a _
    exact μ.apply_ne_top a
  calc
    ∑ a : α, (μ a).toReal = (∑ a : α, μ a).toReal := by
      symm
      simpa using (ENNReal.toReal_sum (s := (Finset.univ : Finset α)) (f := fun a => μ a) h_ne_top)
    _ = 1 := by
      simpa [h_sum_enn]

/-- Every atom of a PMF has real mass at most one. -/
theorem pmf_apply_toReal_le_one {α : Type*} (μ : PMF α) (a : α) :
    (μ a).toReal ≤ 1 := by
  have hle : μ a ≤ 1 := by
    rw [← PMF.tsum_coe μ]
    exact ENNReal.le_tsum a
  exact ENNReal.toReal_mono ENNReal.one_ne_top hle

/--
Full support turns a support-aware exclusion into an ordinary exclusion.
This is useful when a finite result first rules out positive-mass witnesses and
a later endpoint assumes every atom has positive mass.
-/
theorem not_exists_of_not_exists_pos_mass_of_full_support
    {ι α β : Type*}
    (μ : ι → α → PMF β) (p : ι → α → β → Prop)
    (hfull_support : ∀ i a b, 0 < (μ i a b).toReal)
    (hno_positive :
      ¬ ∃ i a b, 0 < (μ i a b).toReal ∧ p i a b) :
    ¬ ∃ i a b, p i a b := by
  rintro ⟨i, a, b, hp⟩
  exact hno_positive ⟨i, a, b, hfull_support i a b, hp⟩

/-- The uniform PMF over a finite nonempty type. -/
noncomputable def uniformPMF (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ : α => ((Fintype.card α : ENNReal)⁻¹)) (by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
    simpa [nsmul_eq_mul] using
      (ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top (Fintype.card α))))

@[simp] theorem uniformPMF_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    uniformPMF α a = ((Fintype.card α : ENNReal)⁻¹) := by
  rfl

theorem uniformPMF_apply_toReal {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (uniformPMF α a).toReal = (Fintype.card α : ℝ)⁻¹ := by
  simp [uniformPMF]

theorem uniformPMF_apply_toReal_pos {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    0 < (uniformPMF α a).toReal := by
  rw [uniformPMF_apply_toReal]
  exact inv_pos.mpr (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))

/--
The product of identical uniform coordinate laws is the uniform law on finite
functions.
-/
theorem pmfProduct_uniformPMF_eq_uniformPMF_fun
    (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α] :
    pmfProduct ι α (uniformPMF α) = uniformPMF (ι → α) := by
  classical
  ext f
  simp [pmfProduct_apply, uniformPMF, Finset.prod_const]
  exact (ENNReal.inv_pow (a := (Fintype.card α : ENNReal))
    (n := Fintype.card ι)).symm

theorem pmfExp_congr {α : Type*} [Fintype α]
    (μ : PMF α) {f g : α → ℝ}
    (h : ∀ a, f a = g a) :
    pmfExp μ f = pmfExp μ g := by
  unfold pmfExp
  simp [h]

/-- Uniform finite expectation is invariant under a relabeling equivalence. -/
theorem pmfExp_uniformPMF_comp_equiv {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) (f : α → ℝ) :
    pmfExp (uniformPMF α) (fun a => f (e a)) =
      pmfExp (uniformPMF α) f := by
  unfold pmfExp
  simpa [uniformPMF_apply_toReal] using
    (Equiv.sum_comp e (fun a : α => (Fintype.card α : ℝ)⁻¹ * f a))

/-- Uniform finite expectation is invariant under an equivalence of finite types. -/
theorem pmfExp_uniformPMF_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : β → ℝ) :
    pmfExp (uniformPMF β) f =
      pmfExp (uniformPMF α) (fun a => f (e a)) := by
  unfold pmfExp
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  calc
    ∑ b : β, (uniformPMF β b).toReal * f b =
        ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b := by
          simp
    _ = ∑ a : α, (Fintype.card β : ℝ)⁻¹ * f (e a) := by
          simpa using
            (Equiv.sum_comp e
              (fun b : β => (Fintype.card β : ℝ)⁻¹ * f b)).symm
    _ = ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a) := by
          simp [hcard]
    _ = ∑ a : α, (uniformPMF α a).toReal * f (e a) := by
          simp

/--
If `g` is obtained from `f` by relabeling a uniformly drawn finite input, then
the two expectations are equal.
-/
theorem pmfExp_uniformPMF_eq_of_comp_equiv {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) {f g : α → ℝ}
    (h : ∀ a, f (e a) = g a) :
    pmfExp (uniformPMF α) f = pmfExp (uniformPMF α) g := by
  calc
    pmfExp (uniformPMF α) f =
        pmfExp (uniformPMF α) (fun a => f (e a)) := by
          exact (pmfExp_uniformPMF_comp_equiv e f).symm
    _ = pmfExp (uniformPMF α) g := by
          exact pmfExp_congr (uniformPMF α) h

@[simp] theorem pmfExp_const {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (c : ℝ) :
    pmfExp μ (fun _ => c) = c := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * c = (∑ a : α, (μ a).toReal) * c := by
      simpa using (Finset.sum_mul (s := (Finset.univ : Finset α))
        (f := fun a => (μ a).toReal) (a := c)).symm
    _ = 1 * c := by rw [pmfToRealSum μ]
    _ = c := by ring

/--
If a finite random variable is equal to a constant on every positive-mass atom,
then its expectation is that constant.  Zero-mass atoms may carry arbitrary
values.
-/
theorem pmfExp_eq_const_of_support_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, 0 < (μ a).toReal → f a = c) :
    pmfExp μ f = c := by
  have hExp : pmfExp μ f = pmfExp μ (fun _ => c) := by
    unfold pmfExp
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hmass : 0 < (μ a).toReal
    · rw [h a hmass]
    · have hzero : (μ a).toReal = 0 :=
        le_antisymm (le_of_not_gt hmass) ENNReal.toReal_nonneg
      simp [hzero]
  rw [hExp, pmfExp_const]

@[simp] theorem pmfPairExp_ignore_right {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (g : α → ℝ) :
    pmfPairExp μ ν (fun a _ => g a) = pmfExp μ g := by
  unfold pmfPairExp
  simp [pmfExp_const]

@[simp] theorem pmfPairExp_ignore_left {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (g : β → ℝ) :
    pmfPairExp μ ν (fun _ b => g b) = pmfExp ν g := by
  unfold pmfPairExp
  simp [pmfExp_const]

/--
Reading one coordinate of a finite iid PMF product has the declared marginal
law.  This finite-expectation form is convenient when a source model draws a
fixed bundle of iid labels but leaves the remaining random structure
correlated.
-/
theorem pmfExp_pmfProduct_eval
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (i : ι) (F : α → ℝ) :
    pmfExp (pmfProduct ι α μ) (fun sample => F (sample i)) = pmfExp μ F := by
  let rest := {j : ι // j ≠ i}
  let e : ι ≃ Option rest := (Equiv.optionSubtypeNe i).symm
  calc
    pmfExp (pmfProduct ι α μ) (fun sample => F (sample i)) =
        pmfExp (pmfProduct (Option rest) α μ) (fun sample => F (sample none)) := by
      simpa [e] using
        (pmfExp_pmfProduct_equiv e μ (fun sample : Option rest → α => F (sample none)))
    _ = pmfPairExp (pmfProduct rest α μ) μ
        (fun sample newItem => F ((extendDraw sample newItem) none)) := by
      exact pmfExp_pmfProduct_option_eq_pairExp μ (fun sample => F (sample none))
    _ = pmfPairExp (pmfProduct rest α μ) μ (fun _ newItem => F newItem) := by
      rfl
    _ = pmfExp μ F := pmfPairExp_ignore_left _ _ F

/-- Probability of a predicate under a finite PMF, returned as a real number. -/
noncomputable def pmfProb {α : Type*} [Fintype α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] : ℝ :=
  pmfExp μ (fun a => if p a then 1 else 0)

/-- A finite PMF event probability agrees with its canonical measure's real mass. -/
theorem pmfProb_eq_toMeasure_real
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (law : PMF Outcome) (event : Outcome → Prop) [DecidablePred event] :
    pmfProb law event = law.toMeasure.real {outcome | event outcome} := by
  classical
  unfold pmfProb pmfExp Measure.real
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro outcome _
    by_cases hevent : event outcome <;> simp [hevent]
  · intro outcome _
    by_cases hevent : event outcome <;>
      simp [Set.indicator, hevent, law.apply_ne_top outcome]

/-- Finite PMF event probability is invariant under pointwise event equivalence. -/
theorem pmfProb_congr {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) :
    pmfProb μ p = pmfProb μ q := by
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a
  · have hq : q a := (h a).1 hp
    simp [hp, hq]
  · have hq : ¬ q a := fun hqa => hp ((h a).2 hqa)
    simp [hp, hq]

/-- Event probabilities computed as finite PMF expectations are nonnegative. -/
theorem pmfProb_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    0 ≤ pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  exact mul_nonneg ENNReal.toReal_nonneg (by by_cases hp : p a <;> simp [hp])

/-- The probability of a singleton event is the atom mass. -/
theorem pmfProb_singleton
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (a : α) :
    pmfProb μ (fun x => x = a) = (μ a).toReal := by
  classical
  unfold pmfProb pmfExp
  calc
    (∑ x : α, (μ x).toReal * if x = a then (1 : ℝ) else 0)
        = (μ a).toReal * (if a = a then (1 : ℝ) else 0) := by
            refine Finset.sum_eq_single
              (s := (Finset.univ : Finset α)) (a := a)
              (f := fun x => (μ x).toReal * if x = a then (1 : ℝ) else 0) ?_ ?_
            · intro b _hb hba
              simp [hba]
            · intro ha
              simp at ha
    _ = (μ a).toReal := by simp

/--
For an independent finite product PMF with identical coordinate law, the
probability that every coordinate satisfies `p` is the corresponding one-point
probability raised to the number of coordinates.
-/
theorem pmfProduct_prob_forall
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb (pmfProduct ι α μ) (fun f : ι → α => ∀ i : ι, p (f i)) =
      (pmfProb μ p) ^ Fintype.card ι := by
  classical
  have hpoint : ∀ f : ι → α,
      (pmfProduct ι α μ f).toReal *
          (if ∀ i : ι, p (f i) then (1 : ℝ) else 0) =
        ∏ i : ι, ((μ (f i)).toReal *
          (if p (f i) then (1 : ℝ) else 0)) := by
    intro f
    by_cases hall : ∀ i : ι, p (f i)
    · simp [hall]
    · have hnotall : ¬ ∀ i : ι, p (f i) := hall
      rcases not_forall.mp hnotall with ⟨i, hi⟩
      have hprod_zero :
          ∏ j : ι, (if p (f j) then (μ (f j)).toReal else 0) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ i)]
        simp [hi]
      simp [hnotall, hprod_zero]
  unfold pmfProb pmfExp
  calc
    ∑ f : ι → α, (pmfProduct ι α μ f).toReal *
        (if ∀ i : ι, p (f i) then (1 : ℝ) else 0)
        = ∑ f : ι → α, ∏ i : ι, ((μ (f i)).toReal *
            (if p (f i) then (1 : ℝ) else 0)) := by
          exact Finset.sum_congr rfl (fun f _ => hpoint f)
    _ = ∏ i : ι, ∑ a : α,
          ((μ a).toReal * (if p a then (1 : ℝ) else 0)) := by
          symm
          simpa using
            (Finset.prod_univ_sum
              (t := fun _i : ι => (Finset.univ : Finset α))
              (f := fun _i a => (μ a).toReal *
                (if p a then (1 : ℝ) else 0)))
    _ = (∑ a : α, (μ a).toReal *
          (if p a then (1 : ℝ) else 0)) ^ Fintype.card ι := by
          simp [Finset.prod_const]

/--
For an independent finite product PMF, the probability of a coordinate-wise
event with coordinate-dependent predicates factors into the product of the
one-coordinate probabilities.
-/
theorem pmfProduct_prob_forall_dependent
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : ι → α → Prop)
    [∀ i, DecidablePred (P i)] :
    pmfProb (pmfProduct ι α μ)
        (fun f : ι → α => ∀ i : ι, P i (f i)) =
      ∏ i : ι, pmfProb μ (P i) := by
  classical
  have hpoint : ∀ f : ι → α,
      (pmfProduct ι α μ f).toReal *
          (if ∀ i : ι, P i (f i) then (1 : ℝ) else 0) =
        ∏ i : ι, ((μ (f i)).toReal *
          (if P i (f i) then (1 : ℝ) else 0)) := by
    intro f
    by_cases hall : ∀ i : ι, P i (f i)
    · simp [hall]
    · have hnotall : ¬ ∀ i : ι, P i (f i) := hall
      rcases not_forall.mp hnotall with ⟨i, hi⟩
      have hprod_zero :
          ∏ j : ι, (if P j (f j) then (μ (f j)).toReal else 0) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ i)]
        simp [hi]
      simp [hnotall, hprod_zero]
  unfold pmfProb pmfExp
  calc
    ∑ f : ι → α, (pmfProduct ι α μ f).toReal *
        (if ∀ i : ι, P i (f i) then (1 : ℝ) else 0)
        = ∑ f : ι → α, ∏ i : ι, ((μ (f i)).toReal *
            (if P i (f i) then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl (fun f _ => hpoint f)
    _ = ∏ i : ι, ∑ a : α,
          ((μ a).toReal * (if P i a then (1 : ℝ) else 0)) := by
          symm
          simpa using
            (Finset.prod_univ_sum
              (t := fun _i : ι => (Finset.univ : Finset α))
              (f := fun i a => (μ a).toReal *
                (if P i a then (1 : ℝ) else 0)))

/-- The set of coordinates where a sample satisfies a predicate. -/
def successIndexSet {ι α : Type*} [Fintype ι]
    (p : α → Prop) [DecidablePred p] (sample : ι → α) : Finset ι :=
  (Finset.univ : Finset ι).filter (fun i => p (sample i))

/-- The success-index set equals `s` iff each coordinate has the prescribed status. -/
theorem successIndexSet_eq_iff {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    {p : α → Prop} [DecidablePred p]
    (sample : ι → α) (s : Finset ι) :
    successIndexSet p sample = s ↔
      ∀ i : ι, p (sample i) ↔ i ∈ s := by
  classical
  constructor
  · intro h i
    have hi := congrArg (fun t : Finset ι => i ∈ t) h
    simpa [successIndexSet] using hi
  · intro h
    ext i
    simp [successIndexSet, h i]

/--
For an independent finite product PMF, the probability of a fixed success-index
set is `q^|s| rho^(n-|s|)`, where `q` and `rho` are the one-draw success and
failure probabilities.
-/
theorem pmfProduct_prob_successIndexSet_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (s : Finset ι) :
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α => successIndexSet p sample = s) =
      (pmfProb μ p) ^ s.card *
        (pmfProb μ (fun a => ¬ p a)) ^
          (Fintype.card ι - s.card) := by
  classical
  calc
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α => successIndexSet p sample = s)
        =
        pmfProb (pmfProduct ι α μ)
          (fun sample : ι → α => ∀ i : ι, p (sample i) ↔ i ∈ s) := by
          refine pmfProb_congr _ ?_
          intro sample
          exact successIndexSet_eq_iff sample s
    _ = ∏ i : ι,
          pmfProb μ (fun a : α => p a ↔ i ∈ s) :=
          pmfProduct_prob_forall_dependent μ
            (fun i a => p a ↔ i ∈ s)
    _ = ∏ i : ι,
          if i ∈ s then
            pmfProb μ p
          else
            pmfProb μ (fun a : α => ¬ p a) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          by_cases his : i ∈ s
          · simp [his]
          · simp [his]
    _ =
        (pmfProb μ p) ^ s.card *
          (pmfProb μ (fun a : α => ¬ p a)) ^
            (Fintype.card ι - s.card) :=
          AppliedModelingLib.FiniteSum.prod_ite_mem_eq_pow_mul_pow s
            (pmfProb μ p)
            (pmfProb μ (fun a : α => ¬ p a))

/--
The number of successes in an independent finite product has the usual binomial
mass formula, stated directly for finite PMFs and real-valued finite
probabilities.
-/
theorem pmfProduct_prob_successIndexSet_card_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (j : ℕ) :
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α => (successIndexSet p sample).card = j) =
      (Nat.choose (Fintype.card ι) j : ℝ) *
        (pmfProb μ p) ^ j *
          (pmfProb μ (fun a => ¬ p a)) ^
            (Fintype.card ι - j) := by
  classical
  let exactSets : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powersetCard j
  have hindicator :
      ∀ sample : ι → α,
        (if (successIndexSet p sample).card = j then (1 : ℝ) else 0) =
          ∑ s ∈ exactSets,
            if successIndexSet p sample = s then (1 : ℝ) else 0 := by
    intro sample
    by_cases hcard : (successIndexSet p sample).card = j
    · have hmem : successIndexSet p sample ∈ exactSets := by
        simp [exactSets, hcard]
      simp [hcard, hmem]
    · have hne :
        ∀ s ∈ exactSets, successIndexSet p sample ≠ s := by
        intro s hs heq
        have hs_card : s.card = j := by
          simpa [exactSets] using (Finset.mem_powersetCard.mp hs).2
        exact hcard (by simpa [heq, hs_card])
      have hnotmem : successIndexSet p sample ∉ exactSets := by
        intro hmem
        exact hne (successIndexSet p sample) hmem rfl
      simp [hcard, hnotmem]
  unfold pmfProb pmfExp
  calc
    ∑ sample : ι → α,
        (pmfProduct ι α μ sample).toReal *
          (if (successIndexSet p sample).card = j then (1 : ℝ) else 0)
        =
        ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (∑ s ∈ exactSets,
              if successIndexSet p sample = s then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [hindicator sample]
    _ =
        ∑ sample : ι → α, ∑ s ∈ exactSets,
          (pmfProduct ι α μ sample).toReal *
            (if successIndexSet p sample = s then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [Finset.mul_sum]
    _ =
        ∑ s ∈ exactSets, ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (if successIndexSet p sample = s then (1 : ℝ) else 0) :=
          Finset.sum_comm
    _ =
        ∑ s ∈ exactSets,
          (pmfProb μ p) ^ s.card *
            (pmfProb μ (fun a : α => ¬ p a)) ^
              (Fintype.card ι - s.card) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          exact pmfProduct_prob_successIndexSet_eq μ p s
    _ =
        ∑ s ∈ exactSets,
          (pmfProb μ p) ^ j *
            (pmfProb μ (fun a : α => ¬ p a)) ^
              (Fintype.card ι - j) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hs_card : s.card = j := by
            simpa [exactSets] using (Finset.mem_powersetCard.mp hs).2
          simp [hs_card]
    _ =
        (Nat.choose (Fintype.card ι) j : ℝ) *
          (pmfProb μ p) ^ j *
            (pmfProb μ (fun a : α => ¬ p a)) ^
              (Fintype.card ι - j) := by
          simp [exactSets, Finset.card_powersetCard, Finset.card_univ, mul_assoc]

/--
The lower-tail probability for the number of successes in an independent
finite product is the corresponding finite binomial sum over `j < k`.
-/
theorem pmfProduct_prob_successIndexSet_card_lt_eq_sum
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (k : ℕ) :
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α => (successIndexSet p sample).card < k) =
      ∑ j ∈ Finset.range k,
        (Nat.choose (Fintype.card ι) j : ℝ) *
          (pmfProb μ p) ^ j *
            (pmfProb μ (fun a : α => ¬ p a)) ^
              (Fintype.card ι - j) := by
  classical
  have hindicator :
      ∀ sample : ι → α,
        (if (successIndexSet p sample).card < k then (1 : ℝ) else 0) =
          ∑ j ∈ Finset.range k,
            if (successIndexSet p sample).card = j then (1 : ℝ) else 0 := by
    intro sample
    by_cases hlt : (successIndexSet p sample).card < k
    · have hmem : (successIndexSet p sample).card ∈ Finset.range k := by
        simpa using hlt
      simp [hlt, hmem]
    · simp [hlt]
  unfold pmfProb pmfExp
  calc
    ∑ sample : ι → α,
        (pmfProduct ι α μ sample).toReal *
          (if (successIndexSet p sample).card < k then (1 : ℝ) else 0)
        =
        ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (∑ j ∈ Finset.range k,
              if (successIndexSet p sample).card = j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [hindicator sample]
    _ =
        ∑ sample : ι → α, ∑ j ∈ Finset.range k,
          (pmfProduct ι α μ sample).toReal *
            (if (successIndexSet p sample).card = j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [Finset.mul_sum]
    _ =
        ∑ j ∈ Finset.range k, ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (if (successIndexSet p sample).card = j then (1 : ℝ) else 0) :=
          Finset.sum_comm
    _ =
        ∑ j ∈ Finset.range k,
          (Nat.choose (Fintype.card ι) j : ℝ) *
            (pmfProb μ p) ^ j *
              (pmfProb μ (fun a : α => ¬ p a)) ^
                (Fintype.card ι - j) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact pmfProduct_prob_successIndexSet_card_eq μ p j

/--
Uniform finite probabilities are invariant under relabeling: if an event on
`β` pulled back along an equivalence is the event on `α`, then the two uniform
probabilities are equal.
-/
theorem pmfProb_uniformPMF_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (p : β → Prop) (q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p (e a) ↔ q a) :
    pmfProb (uniformPMF β) p =
      pmfProb (uniformPMF α) q := by
  classical
  unfold pmfProb
  calc
    pmfExp (uniformPMF β) (fun b => if p b then (1 : ℝ) else 0) =
        pmfExp (uniformPMF α)
          (fun a => if p (e a) then (1 : ℝ) else 0) :=
          pmfExp_uniformPMF_equiv e
            (fun b => if p b then (1 : ℝ) else 0)
    _ = pmfExp (uniformPMF α)
          (fun a => if q a then (1 : ℝ) else 0) := by
          refine pmfExp_congr (uniformPMF α) ?_
          intro a
          by_cases hp : p (e a)
          · have hq : q a := (h a).1 hp
            simp [hp, hq]
          · have hq : ¬ q a := fun hqa => hp ((h a).2 hqa)
            simp [hp, hq]

/--
Same-space version of `pmfProb_uniformPMF_equiv`: a finite uniform probability
is unchanged by a permutation of the sample space.
-/
theorem pmfProb_uniformPMF_eq_of_comp_equiv {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p (e a) ↔ q a) :
    pmfProb (uniformPMF α) p =
      pmfProb (uniformPMF α) q :=
  pmfProb_uniformPMF_equiv e p q h

/--
Function-space event exchangeability under pointwise relabeling of the range.
This is useful for random finite lists, draw prefixes, and assignment-valued
sample spaces whose coordinates are uniformly and independently drawn from a
finite type.
-/
theorem pmfProb_uniformPMF_fun_range_relabel {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) (p q : (ι → α) → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ f : ι → α, p (fun i => e (f i)) ↔ q f) :
    pmfProb (uniformPMF (ι → α)) p =
      pmfProb (uniformPMF (ι → α)) q := by
  classical
  let relabel : (ι → α) ≃ (ι → α) :=
    { toFun := fun f i => e (f i)
      invFun := fun f i => e.symm (f i)
      left_inv := by
        intro f
        funext i
        simp
      right_inv := by
        intro f
        funext i
        simp }
  exact pmfProb_uniformPMF_eq_of_comp_equiv relabel p q h

/-- Relabel the range of an injective finite function by an equivalence. -/
def injectiveFunRangeRelabelEquiv {ι α : Type*}
    (e : α ≃ α) :
    {f : ι → α // Function.Injective f} ≃
      {f : ι → α // Function.Injective f} where
  toFun f :=
    ⟨fun i => e (f.1 i), by
      intro i j h
      exact f.2 (e.injective h)⟩
  invFun f :=
    ⟨fun i => e.symm (f.1 i), by
      intro i j h
      exact f.2 (e.symm.injective h)⟩
  left_inv := by
    intro f
    ext i
    simp
  right_inv := by
    intro f
    ext i
    simp

/--
Uniform event exchangeability on ordered without-replacement samples, modeled
as injective finite functions, under pointwise relabeling of the range.
-/
theorem pmfProb_uniformPMF_injective_fun_range_relabel {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    [Nonempty {f : ι → α // Function.Injective f}]
    (e : α ≃ α)
    (p q : {f : ι → α // Function.Injective f} → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ f : {f : ι → α // Function.Injective f},
      p (injectiveFunRangeRelabelEquiv e f) ↔ q f) :
    pmfProb (uniformPMF {f : ι → α // Function.Injective f}) p =
      pmfProb (uniformPMF {f : ι → α // Function.Injective f}) q :=
  pmfProb_uniformPMF_eq_of_comp_equiv
    (injectiveFunRangeRelabelEquiv e) p q h

/--
Linearity identity for finite random counts: the expected number of elements
satisfying an outcome-dependent predicate is the sum of their event
probabilities.
-/
theorem pmfExp_card_filter_eq_sum_pmfProb {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ a, DecidablePred fun ω => p ω a] :
    pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) =
      ∑ a : α, pmfProb μ (fun ω => p ω a) := by
  classical
  have hcard :
      ∀ ω,
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) =
          ∑ a : α, if p ω a then (1 : ℝ) else 0 := by
    intro ω
    simp
  unfold pmfExp pmfProb
  calc
    ∑ ω : Ω, (μ ω).toReal *
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) =
        ∑ ω : Ω, (μ ω).toReal *
          (∑ a : α, if p ω a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [hcard ω]
    _ = ∑ ω : Ω, ∑ a : α,
          (μ ω).toReal * (if p ω a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ a : α, ∑ ω : Ω,
          (μ ω).toReal * (if p ω a then (1 : ℝ) else 0) := by
          exact Finset.sum_comm

/--
Linearity identity for finite random counts over a specified finite subfamily:
the expected number of elements of `s` satisfying an outcome-dependent
predicate is the sum of their event probabilities.
-/
theorem pmfExp_card_finset_filter_eq_sum_pmfProb {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ a, DecidablePred fun ω => p ω a]
    (s : Finset α) :
    pmfExp μ
        (fun ω => (((s.filter (p ω)).card : ℝ))) =
      ∑ a ∈ s, pmfProb μ (fun ω => p ω a) := by
  classical
  have hcard :
      ∀ ω,
        (((s.filter (p ω)).card : ℝ)) =
          ∑ a ∈ s, if p ω a then (1 : ℝ) else 0 := by
    intro ω
    simp
  unfold pmfExp pmfProb
  calc
    ∑ ω : Ω, (μ ω).toReal *
        (((s.filter (p ω)).card : ℝ)) =
        ∑ ω : Ω, (μ ω).toReal *
          (∑ a ∈ s, if p ω a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [hcard ω]
    _ = ∑ ω : Ω, ∑ a ∈ s,
          (μ ω).toReal * (if p ω a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ ω : Ω,
          (μ ω).toReal * (if p ω a then (1 : ℝ) else 0) := by
          exact Finset.sum_comm

end AppliedModelingLib

namespace AppliedModelingLib

/-- The finite image of a function whose domain is finite.  Coercing this
finset to a type gives the corresponding finite subtype, even when the
ambient codomain itself is not finite. -/
noncomputable def finiteFunctionRange {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) : Finset β :=
  (Finset.univ : Finset α).image f

/-- The canonical map from a finite domain into its finite function image. -/
noncomputable def finiteFunctionRangeValue {α β : Type*}
    [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    ↥(finiteFunctionRange f) :=
  ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

/-- Equality to a finite-image value is exactly equality of the underlying
function values. -/
theorem finiteFunctionRangeValue_eq_iff {α β : Type*}
    [Fintype α] [DecidableEq β] (f : α → β) (a : α)
    (b : ↥(finiteFunctionRange f)) :
    finiteFunctionRangeValue f a = b ↔ f a = b.1 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

@[simp] theorem pmfExp_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    pmfExp μ (fun _ => 0) = 0 := by
  simpa using pmfExp_const (μ := μ) (c := 0)

/-- Linearity of finite PMF expectation. -/
theorem pmfExp_add {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfExp μ (fun a => f a + g a) = pmfExp μ f + pmfExp μ g := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (f a + g a)
        = ∑ a : α, ((μ a).toReal * f a + (μ a).toReal * g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a : α, (μ a).toReal * f a) +
          (∑ a : α, (μ a).toReal * g a) := by
          rw [Finset.sum_add_distrib]

/-- Subtractive linearity of finite PMF expectation. -/
theorem pmfExp_sub {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfExp μ (fun a => f a - g a) = pmfExp μ f - pmfExp μ g := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (f a - g a)
        = ∑ a : α, ((μ a).toReal * f a - (μ a).toReal * g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a : α, (μ a).toReal * f a) -
          (∑ a : α, (μ a).toReal * g a) := by
          rw [Finset.sum_sub_distrib]

/--
Expectation of a ternary real-valued random variable taking values
`1`, `0`, and `-1` equals `Pr[X = 1] - Pr[X = -1]`.
-/
theorem pmfExp_ternary_eq_prob_one_sub_prob_neg_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (x : α → ℝ)
    (hx : ∀ a, x a = 1 ∨ x a = 0 ∨ x a = -1) :
    pmfExp μ x =
      pmfProb μ (fun a => x a = 1) -
        pmfProb μ (fun a => x a = -1) := by
  classical
  have hpoint :
      x =
        fun a =>
          (if x a = 1 then (1 : ℝ) else 0) -
            (if x a = -1 then (1 : ℝ) else 0) := by
    funext a
    rcases hx a with hpos | hrest
    · norm_num [hpos]
    · rcases hrest with hzero | hneg
      · simp [hzero]
      · norm_num [hneg]
  calc
    pmfExp μ x =
        pmfExp μ
          (fun a =>
            (if x a = 1 then (1 : ℝ) else 0) -
              (if x a = -1 then (1 : ℝ) else 0)) := by
          exact congrArg (fun y => pmfExp μ y) hpoint
    _ =
        pmfExp μ (fun a => if x a = 1 then (1 : ℝ) else 0) -
          pmfExp μ (fun a => if x a = -1 then (1 : ℝ) else 0) := by
          rw [pmfExp_sub]
    _ =
        pmfProb μ (fun a => x a = 1) -
          pmfProb μ (fun a => x a = -1) := rfl

@[simp] theorem pmfExp_neg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfExp μ (fun a => - f a) = - pmfExp μ f := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (- f a)
        = ∑ a : α, - ((μ a).toReal * f a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = - ∑ a : α, (μ a).toReal * f a := by
          rw [Finset.sum_neg_distrib]

/-- Multiplying the integrand by a constant on the left pulls out of expectation. -/
theorem pmfExp_const_mul {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfExp μ (fun a => c * f a) = c * pmfExp μ f := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (c * f a)
        = ∑ a : α, c * ((μ a).toReal * f a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = c * ∑ a : α, (μ a).toReal * f a := by
          rw [Finset.mul_sum]

/-- Multiplying the integrand by a constant on the right pulls out of expectation. -/
theorem pmfExp_mul_const {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfExp μ (fun a => f a * c) = pmfExp μ f * c := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (f a * c)
        = ∑ a : α, ((μ a).toReal * f a) * c := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a : α, (μ a).toReal * f a) * c := by
          rw [Finset.sum_mul]

/-- Finite PMF expectation commutes with a finite sum. -/
theorem pmfExp_sum {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    pmfExp μ (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, pmfExp μ (fun ω => f i ω) := by
  classical
  unfold pmfExp
  calc
    ∑ ω : Ω, (μ ω).toReal * (∑ i ∈ s, f i ω) =
        ∑ ω : Ω, ∑ i ∈ s, (μ ω).toReal * f i ω := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ ω : Ω, (μ ω).toReal * f i ω := by
          exact Finset.sum_comm

/-- Finite PMF expectation commutes with a finite type sum. -/
theorem pmfExp_univ_sum {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] (μ : PMF Ω) (f : ι → Ω → ℝ) :
    pmfExp μ (fun ω => ∑ i : ι, f i ω) =
      ∑ i : ι, pmfExp μ (fun ω => f i ω) := by
  simpa using pmfExp_sum μ (Finset.univ : Finset ι) f

/--
If a finite random variable takes value `x` on event `p` and value `y` off that
event, its expectation is `Pr[p] * x + (1 - Pr[p]) * y`.
-/
theorem pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (x y : ℝ)
    (h : ∀ a, f a = if p a then x else y) :
    pmfExp μ f = pmfProb μ p * x + (1 - pmfProb μ p) * y := by
  classical
  have hpoint :
      ∀ a, f a = y + (if p a then (1 : ℝ) else 0) * (x - y) := by
    intro a
    rw [h a]
    by_cases hp : p a <;> simp [hp]
  calc
    pmfExp μ f =
        pmfExp μ (fun a => y + (if p a then (1 : ℝ) else 0) * (x - y)) := by
          exact pmfExp_congr μ hpoint
    _ = pmfExp μ (fun _ => y) +
          pmfExp μ (fun a => (if p a then (1 : ℝ) else 0) * (x - y)) := by
          rw [pmfExp_add]
    _ = y + pmfProb μ p * (x - y) := by
          rw [pmfExp_const]
          rw [pmfExp_mul_const]
          rfl
    _ = pmfProb μ p * x + (1 - pmfProb μ p) * y := by
          ring

/-- A finite PMF expectation is bounded above by any pointwise upper bound. -/
theorem pmfExp_le_of_forall_le {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, f a ≤ c) :
    pmfExp μ f ≤ c := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * f a
        ≤ ∑ a : α, (μ a).toReal * c := by
          exact Finset.sum_le_sum (by
            intro a _
            exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = c := by
          calc
            ∑ a : α, (μ a).toReal * c
                = (∑ a : α, (μ a).toReal) * c := by
                    simpa using (Finset.sum_mul (s := (Finset.univ : Finset α))
                      (f := fun a => (μ a).toReal) (a := c)).symm
            _ = c := by
                    rw [pmfToRealSum μ]
                    ring

/-- Finite PMF expectation is monotone under pointwise comparison. -/
theorem pmfExp_le_pmfExp_of_forall_le {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) (h : ∀ a, f a ≤ g a) :
    pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  exact Finset.sum_le_sum (by
    intro a _
    exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)

/--
Finite PMF expectation is strictly monotone when the integrands are pointwise
ordered and the inequality is strict at one positive-mass atom.
-/
theorem pmfExp_lt_pmfExp_of_forall_le_exists_pos_lt
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) (hle : ∀ a, f a ≤ g a)
    (hexists : ∃ a, 0 < (μ a).toReal ∧ f a < g a) :
    pmfExp μ f < pmfExp μ g := by
  unfold pmfExp
  apply Finset.sum_lt_sum
  · intro a _
    exact mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg
  · obtain ⟨a, hmass, hstrict⟩ := hexists
    exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left hstrict hmass⟩

/-- Finite-PMF expectation is monotone when the comparison holds on its support. -/
theorem pmfExp_le_pmfExp_of_support_forall_le {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) (h : ∀ a ∈ μ.support, f a ≤ g a) :
    pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
  · have hzero : μ a = 0 := by
      by_contra hnonzero
      exact ha ((PMF.mem_support_iff μ a).mpr hnonzero)
    simp [hzero]

/-- A finite family of mutually exclusive events contained in a gate has total
probability at most the probability of that gate. -/
theorem pmfProb_sum_le_pmfProb_of_forall_unique_and_imp {Ω ι : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : PMF Ω) (p : ι → Ω → Prop) (gate : Ω → Prop)
    [∀ i, DecidablePred (p i)] [DecidablePred gate]
    (hunique : ∀ ω i j, p i ω → p j ω → i = j)
    (himp : ∀ i ω, p i ω → gate ω) :
    ∑ i : ι, pmfProb μ (p i) ≤ pmfProb μ gate := by
  classical
  rw [← pmfExp_card_filter_eq_sum_pmfProb μ (fun ω i => p i ω)]
  change pmfExp μ
      (fun ω => (((Finset.univ : Finset ι).filter (fun i => p i ω)).card : ℝ)) ≤
    pmfExp μ (fun ω => if gate ω then (1 : ℝ) else 0)
  apply pmfExp_le_pmfExp_of_forall_le
  intro ω
  by_cases hgate : gate ω
  · have hcard : ((Finset.univ : Finset ι).filter (fun i => p i ω)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro i hi j hj
      exact hunique ω i j (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
    simpa [hgate] using (show
      (((Finset.univ : Finset ι).filter (fun i => p i ω)).card : ℝ) ≤ 1 by
        exact_mod_cast hcard)
  · have hcard : ((Finset.univ : Finset ι).filter (fun i => p i ω)).card = 0 := by
      refine Finset.card_eq_zero.mpr ?_
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hpi
      exact hgate (himp i ω hpi)
    simp [hgate, hcard]

/-- A finite family of mutually exclusive events has total probability at most
one.  This is the expectation bound for its outcome-wise indicator count. -/
theorem pmfProb_sum_le_one_of_forall_unique {Ω ι : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : PMF Ω) (p : ι → Ω → Prop) [∀ i, DecidablePred (p i)]
    (hunique : ∀ ω i j, p i ω → p j ω → i = j) :
    ∑ i : ι, pmfProb μ (p i) ≤ 1 := by
  classical
  rw [← pmfExp_card_filter_eq_sum_pmfProb μ (fun ω i => p i ω)]
  calc
    pmfExp μ (fun ω => (((Finset.univ : Finset ι).filter (fun i => p i ω)).card : ℝ)) ≤
        pmfExp μ (fun _ => (1 : ℝ)) := by
      apply pmfExp_le_pmfExp_of_forall_le
      intro ω
      have hcard : ((Finset.univ : Finset ι).filter (fun i => p i ω)).card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro i hi j hj
        exact hunique ω i j (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2
      exact_mod_cast hcard
    _ = 1 := by simp

/--
Expectation upper bound from a pointwise event-indicator upper bound.  This is
the finite-PMF form of the common step `X <= C * 1_E`, hence
`E[X] <= C * Pr[E]`.
-/
theorem pmfExp_le_const_mul_pmfProb_of_forall_le_indicator
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (C : ℝ)
    (hpoint : ∀ a, f a ≤ C * (if p a then (1 : ℝ) else 0)) :
    pmfExp μ f ≤ C * pmfProb μ p := by
  classical
  calc
    pmfExp μ f
        ≤ pmfExp μ (fun a => C * (if p a then (1 : ℝ) else 0)) :=
          pmfExp_le_pmfExp_of_forall_le μ f
            (fun a => C * (if p a then (1 : ℝ) else 0)) hpoint
    _ = C * pmfProb μ p := by
          rw [pmfExp_const_mul]
          rfl

/--
Finite-loss accounting with an exceptional event.  If the truthful loss is no
larger than a comparison loss off `bad`, is at most `K` everywhere, and the
comparison loss is always at least one, then expected truthful loss is at
most the displayed multiplicative exceptional-event factor times expected
comparison loss.
-/
theorem pmfExp_loss_le_one_add_mul_pmfProb_mul_of_bad
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (bad : α → Prop) [DecidablePred bad]
    (truth comparison : α → ℝ) (K : ℝ)
    (hK : 1 ≤ K)
    (htruth_bound : ∀ a, truth a ≤ K)
    (hcomparison_lower : ∀ a, 1 ≤ comparison a)
    (hgood : ∀ a, ¬ bad a → truth a ≤ comparison a) :
    pmfExp μ truth ≤
      (1 + (K - 1) * pmfProb μ bad) * pmfExp μ comparison := by
  classical
  have hpoint : ∀ a,
      truth a ≤ comparison a +
        (K - 1) * (if bad a then (1 : ℝ) else 0) := by
    intro a
    by_cases hbad : bad a
    · simp [hbad]
      linarith [htruth_bound a, hcomparison_lower a]
    · simp [hbad]
      exact hgood a hbad
  have hbase :
      pmfExp μ truth ≤ pmfExp μ comparison + (K - 1) * pmfProb μ bad := by
    calc
      pmfExp μ truth ≤
          pmfExp μ (fun a => comparison a +
            (K - 1) * (if bad a then (1 : ℝ) else 0)) :=
          pmfExp_le_pmfExp_of_forall_le μ truth _ hpoint
      _ = pmfExp μ comparison + (K - 1) * pmfProb μ bad := by
          rw [pmfExp_add, pmfExp_const_mul]
          rfl
  have hcomparison_exp : 1 ≤ pmfExp μ comparison := by
    calc
      1 = pmfExp μ (fun _ : α => (1 : ℝ)) := (pmfExp_const μ 1).symm
      _ ≤ pmfExp μ comparison :=
        pmfExp_le_pmfExp_of_forall_le μ _ comparison hcomparison_lower
  have hfactor_nonneg : 0 ≤ (K - 1) * pmfProb μ bad := by
    exact mul_nonneg (sub_nonneg.mpr hK) (pmfProb_nonneg μ bad)
  nlinarith

/--
For independent finite PMFs, the pair expectation of an event indicator
`p a ∧ q b` factors as the product of the two event probabilities.
-/
theorem pmfPairExp_indicator_and_eq_mul_pmfProb
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    pmfPairExp μ ν
        (fun a b => if p a ∧ q b then (1 : ℝ) else 0) =
      pmfProb μ p * pmfProb ν q := by
  classical
  unfold pmfPairExp
  calc
    pmfExp μ
        (fun a => pmfExp ν
          (fun b => if p a ∧ q b then (1 : ℝ) else 0))
        =
        pmfExp μ
          (fun a => (if p a then (1 : ℝ) else 0) *
            pmfProb ν q) := by
          refine pmfExp_congr μ ?_
          intro a
          by_cases hp : p a
          · simp [hp, pmfProb]
          · simp [hp]
    _ = pmfProb μ p * pmfProb ν q := by
          rw [pmfExp_mul_const]
          rfl

/--
In a finite iid product, the event that every coordinate other than `i`
satisfies `p`, while coordinate `i` fails `p`, factors into the corresponding
one-coordinate probabilities.
-/
theorem pmfProduct_prob_forall_ne_and_not
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (i : ι) :
    pmfProb (pmfProduct ι α μ)
        (fun sample => (∀ j : ι, j ≠ i → p (sample j)) ∧ ¬ p (sample i)) =
      (pmfProb μ p) ^ (Fintype.card ι - 1) * (1 - pmfProb μ p) := by
  classical
  let Rest := {j : ι // j ≠ i}
  let e : Option Rest ≃ ι := Equiv.optionSubtypeNe i
  let event : (ι → α) → Prop :=
    fun sample => (∀ j : ι, j ≠ i → p (sample j)) ∧ ¬ p (sample i)
  let optionEvent : (Option Rest → α) → Prop :=
    fun sample => (∀ j : Rest, p (sample (some j))) ∧ ¬ p (sample none)
  have hevent (sample : Option Rest → α) :
      event (fun j : ι => sample (e.symm j)) ↔ optionEvent sample := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro j
        have hsymm : e.symm j.1 = some j := by
          simpa [e, Rest] using Equiv.optionSubtypeNe_symm_of_ne j.2
        simpa [hsymm] using h.1 j.1 j.2
      · have hsymm : e.symm i = none := by
          change (Equiv.optionSubtypeNe i).symm i = none
          exact Equiv.optionSubtypeNe_symm_self i
        simpa [hsymm] using h.2
    · rintro ⟨hforall, hnot⟩
      refine ⟨?_, ?_⟩
      · intro j hji
        have hsymm : e.symm j = some ⟨j, hji⟩ := by
          simpa [e, Rest] using Equiv.optionSubtypeNe_symm_of_ne hji
        simpa [hsymm] using hforall ⟨j, hji⟩
      · have hsymm : e.symm i = none := by
          change (Equiv.optionSubtypeNe i).symm i = none
          exact Equiv.optionSubtypeNe_symm_self i
        simpa [hsymm] using hnot
  have hprob_transport :
      pmfProb (pmfProduct ι α μ) event =
        pmfProb (pmfProduct (Option Rest) α μ) optionEvent := by
    unfold pmfProb
    calc
      pmfExp (pmfProduct ι α μ) (fun sample => if event sample then (1 : ℝ) else 0) =
          pmfExp (pmfProduct (Option Rest) α μ)
            (fun sample => if event (fun j : ι => sample (e.symm j)) then (1 : ℝ) else 0) := by
              symm
              exact pmfExp_pmfProduct_equiv e μ
                (fun sample => if event sample then (1 : ℝ) else 0)
      _ = pmfExp (pmfProduct (Option Rest) α μ)
            (fun sample => if optionEvent sample then (1 : ℝ) else 0) := by
              refine pmfExp_congr _ ?_
              intro sample
              by_cases h : event (fun j : ι => sample (e.symm j))
              · have hoption : optionEvent sample := (hevent sample).mp h
                simp [h, hoption]
              · have hoption : ¬ optionEvent sample := by
                  intro hoption
                  exact h ((hevent sample).mpr hoption)
                simp [h, hoption]
  have hprob_option :
      pmfProb (pmfProduct (Option Rest) α μ) optionEvent =
        (pmfProb μ p) ^ Fintype.card Rest * (1 - pmfProb μ p) := by
    unfold pmfProb
    rw [pmfExp_pmfProduct_option_eq_pairExp]
    calc
      pmfPairExp (pmfProduct Rest α μ) μ
          (fun sample newItem =>
            if optionEvent (extendDraw sample newItem) then (1 : ℝ) else 0) =
          pmfPairExp (pmfProduct Rest α μ) μ
            (fun sample newItem =>
              if (∀ j : Rest, p (sample j)) ∧ ¬ p newItem then (1 : ℝ) else 0) := by
            unfold pmfPairExp
            refine pmfExp_congr _ ?_
            intro sample
            refine pmfExp_congr _ ?_
            intro newItem
            have hextend :
                optionEvent (extendDraw sample newItem) ↔
                  (∀ j : Rest, p (sample j)) ∧ ¬ p newItem := by
              unfold optionEvent
              constructor
              · rintro ⟨hforall, hnot⟩
                refine ⟨?_, ?_⟩
                · intro j
                  simpa [extendDraw] using hforall j
                · simpa [extendDraw] using hnot
              · rintro ⟨hforall, hnot⟩
                refine ⟨?_, ?_⟩
                · intro j
                  cases j; simp [extendDraw, hforall]
                · simpa [extendDraw] using hnot
            by_cases h : optionEvent (extendDraw sample newItem)
            · have hright : (∀ j : Rest, p (sample j)) ∧ ¬ p newItem :=
                hextend.mp h
              simp [h, hright]
            · have hright : ¬ ((∀ j : Rest, p (sample j)) ∧ ¬ p newItem) := by
                intro hright
                exact h (hextend.mpr hright)
              simp [h, hright]
      _ = pmfProb (pmfProduct Rest α μ) (fun sample => ∀ j : Rest, p (sample j)) *
            pmfProb μ (fun x => ¬ p x) := by
            exact pmfPairExp_indicator_and_eq_mul_pmfProb
              (pmfProduct Rest α μ) μ
              (fun sample => ∀ j : Rest, p (sample j)) (fun x => ¬ p x)
      _ = (pmfProb μ p) ^ Fintype.card Rest * (1 - pmfProb μ p) := by
            rw [pmfProduct_prob_forall]
            have hcompl : pmfProb μ (fun x => ¬ p x) = 1 - pmfProb μ p := by
              unfold pmfProb pmfExp
              calc
                ∑ x : α, (μ x).toReal * (if ¬ p x then (1 : ℝ) else 0) =
                    ∑ x : α, ((μ x).toReal * 1 -
                      (μ x).toReal * (if p x then (1 : ℝ) else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro x _
                      by_cases hp : p x <;> simp [hp]
                _ = (∑ x : α, (μ x).toReal * 1) -
                      ∑ x : α, (μ x).toReal * (if p x then (1 : ℝ) else 0) := by
                      rw [Finset.sum_sub_distrib]
                _ = 1 - ∑ x : α, (μ x).toReal * (if p x then (1 : ℝ) else 0) := by
                      simp [pmfToRealSum μ]
            rw [hcompl]
  have hcard : Fintype.card Rest = Fintype.card ι - 1 := by
    calc
      Fintype.card Rest = Fintype.card ι - Fintype.card {j : ι // j = i} := by
        simpa [Rest] using (Fintype.card_subtype_compl (fun j : ι => j = i))
      _ = Fintype.card ι - 1 := by rw [Fintype.card_subtype_eq]
  change pmfProb (pmfProduct ι α μ) event = _
  rw [hprob_transport, hprob_option, hcard]

/-- Expectation of the reciprocal successor of a natural-valued finite random variable. -/
noncomputable def pmfExpReciprocalSucc {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℕ) : ℝ :=
  pmfExp μ (fun a => (((X a + 1 : ℕ) : ℝ)⁻¹))

theorem reciprocal_succ_nat_antitone {x y : ℕ} (hxy : x ≤ y) :
    ((((y + 1 : ℕ) : ℝ)⁻¹) ≤ (((x + 1 : ℕ) : ℝ)⁻¹)) := by
  have hxpos : 0 < ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos x
  have hypos : 0 < ((y + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos y
  have hle : ((x + 1 : ℕ) : ℝ) ≤ ((y + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hxy
  exact (inv_le_inv₀ hypos hxpos).mpr hle

theorem pmfExpReciprocalSucc_mono_of_forall_ge
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ)
    (hge : ∀ a, Y a ≤ X a) :
    pmfExpReciprocalSucc μ X ≤ pmfExpReciprocalSucc μ Y := by
  unfold pmfExpReciprocalSucc
  refine pmfExp_le_pmfExp_of_forall_le μ _ _ ?_
  intro a
  exact reciprocal_succ_nat_antitone (hge a)

theorem pmfExpReciprocalSucc_congr
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ)
    (heq : ∀ a, X a = Y a) :
    pmfExpReciprocalSucc μ X = pmfExpReciprocalSucc μ Y := by
  unfold pmfExpReciprocalSucc
  exact pmfExp_congr μ (by intro a; simp [heq a])

/--
If two natural-valued finite random variables agree on a good event, then their
reciprocal-successor expectations differ by at most the probability of the bad
event.  The pointwise loss is bounded by `1`.
-/
theorem pmfExpReciprocalSucc_le_add_prob_of_eq_on_event
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ) (good : α → Prop) [DecidablePred good]
    (heq : ∀ a, good a → X a = Y a) :
    pmfExpReciprocalSucc μ X ≤
      pmfExpReciprocalSucc μ Y + pmfProb μ (fun a => ¬ good a) := by
  have hpoint :
      ∀ a,
        (((X a + 1 : ℕ) : ℝ)⁻¹) ≤
          (((Y a + 1 : ℕ) : ℝ)⁻¹) +
            (if ¬ good a then (1 : ℝ) else 0) := by
    intro a
    by_cases hg : good a
    · have hxy : X a = Y a := heq a hg
      simp [hg, hxy]
    · have hx_le_one :
          (((X a + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        simpa using
          (reciprocal_succ_nat_antitone (x := 0) (y := X a)
            (Nat.zero_le (X a)))
      have hypos : 0 < ((Y a + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos (Y a)
      have hy_nonneg : 0 ≤ (((Y a + 1 : ℕ) : ℝ)⁻¹) :=
        le_of_lt (inv_pos.mpr hypos)
      have hone_le : (1 : ℝ) ≤ (((Y a + 1 : ℕ) : ℝ)⁻¹) + 1 := by
        simpa using add_le_add_right hy_nonneg 1
      exact le_trans hx_le_one (by simpa [hg] using hone_le)
  unfold pmfExpReciprocalSucc
  calc
    pmfExp μ (fun a => (((X a + 1 : ℕ) : ℝ)⁻¹)) ≤
        pmfExp μ
          (fun a =>
            (((Y a + 1 : ℕ) : ℝ)⁻¹) +
              (if ¬ good a then (1 : ℝ) else 0)) :=
          pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint
    _ = pmfExp μ (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹)) +
          pmfExp μ (fun a => if ¬ good a then (1 : ℝ) else 0) := by
          exact pmfExp_add μ
            (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹))
            (fun a => if ¬ good a then (1 : ℝ) else 0)
    _ = pmfExp μ (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹)) +
          pmfProb μ (fun a => ¬ good a) := by
          rfl

/--
If `Y` is pointwise no larger than `X` on a good event, then the
reciprocal-successor expectation of `X` is at most that of `Y`, up to the
probability of the bad event.  Outside the good event the pointwise loss is
bounded by `1`.
-/
theorem pmfExpReciprocalSucc_le_add_prob_of_ge_on_event
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ) (good : α → Prop) [DecidablePred good]
    (hge : ∀ a, good a → Y a ≤ X a) :
    pmfExpReciprocalSucc μ X ≤
      pmfExpReciprocalSucc μ Y + pmfProb μ (fun a => ¬ good a) := by
  have hpoint :
      ∀ a,
        (((X a + 1 : ℕ) : ℝ)⁻¹) ≤
          (((Y a + 1 : ℕ) : ℝ)⁻¹) +
            (if ¬ good a then (1 : ℝ) else 0) := by
    intro a
    by_cases hg : good a
    · simpa [hg] using reciprocal_succ_nat_antitone (hge a hg)
    · have hx_le_one :
          (((X a + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        simpa using
          (reciprocal_succ_nat_antitone (x := 0) (y := X a)
            (Nat.zero_le (X a)))
      have hypos : 0 < ((Y a + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos (Y a)
      have hy_nonneg : 0 ≤ (((Y a + 1 : ℕ) : ℝ)⁻¹) :=
        le_of_lt (inv_pos.mpr hypos)
      have hone_le : (1 : ℝ) ≤ (((Y a + 1 : ℕ) : ℝ)⁻¹) + 1 := by
        simpa using add_le_add_right hy_nonneg 1
      exact le_trans hx_le_one (by simpa [hg] using hone_le)
  unfold pmfExpReciprocalSucc
  calc
    pmfExp μ (fun a => (((X a + 1 : ℕ) : ℝ)⁻¹)) ≤
        pmfExp μ
          (fun a =>
            (((Y a + 1 : ℕ) : ℝ)⁻¹) +
              (if ¬ good a then (1 : ℝ) else 0)) :=
          pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint
    _ = pmfExp μ (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹)) +
          pmfExp μ (fun a => if ¬ good a then (1 : ℝ) else 0) := by
          exact pmfExp_add μ
            (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹))
            (fun a => if ¬ good a then (1 : ℝ) else 0)
    _ = pmfExp μ (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹)) +
          pmfProb μ (fun a => ¬ good a) := by
          rfl

/--
Uniform expectation on a product is the corresponding nested independent
uniform expectation.
-/
theorem pmfExp_uniformPMF_prod {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α × β → ℝ) :
    pmfExp (uniformPMF (α × β)) f =
      pmfPairExp (uniformPMF α) (uniformPMF β)
        (fun a b => f (a, b)) := by
  unfold pmfPairExp pmfExp
  classical
  calc
    ∑ p : α × β, (uniformPMF (α × β) p).toReal * f p =
        ∑ p : α × β,
          ((Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹) * f p := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [uniformPMF_apply_toReal, Fintype.card_prod]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          have hβ : (Fintype.card β : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
          field_simp [hα, hβ]
          rw [Nat.cast_mul]
          ring
    _ = ∑ a : α, ∑ b : β,
          ((Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹) *
            f (a, b) := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset α))
              (t := (Finset.univ : Finset β))
              (f := fun a b =>
                ((Fintype.card α : ℝ)⁻¹ *
                    (Fintype.card β : ℝ)⁻¹) * f (a, b)))
    _ = ∑ a : α, (uniformPMF α a).toReal *
          (∑ b : β, (uniformPMF β b).toReal * f (a, b)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [uniformPMF_apply_toReal, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [uniformPMF_apply_toReal]
          ring

/-- Under the uniform PMF, a finite event has probability `card(event)/card(space)`. -/
theorem pmfProb_uniformPMF_finset {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) :
    pmfProb (uniformPMF α) (fun a => a ∈ s) =
      (s.card : ℝ) / (Fintype.card α : ℝ) := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ a : α, (uniformPMF α a).toReal *
        (if a ∈ s then (1 : ℝ) else 0) =
        ∑ a : α, (Fintype.card α : ℝ)⁻¹ *
          (if a ∈ s then (1 : ℝ) else 0) := by
          simp
    _ = ∑ a : α, if a ∈ s then (Fintype.card α : ℝ)⁻¹ else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases ha : a ∈ s <;> simp [ha]
    _ = Finset.sum ((Finset.univ : Finset α).filter (fun a => a ∈ s))
          (fun _ => (Fintype.card α : ℝ)⁻¹) := by
          rw [Finset.sum_filter]
    _ = (s.card : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
          have hfilter :
              (Finset.univ : Finset α).filter (fun a => a ∈ s) = s := by
            ext a
            simp
          rw [hfilter, Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) / (Fintype.card α : ℝ) := by
          rw [div_eq_mul_inv]

/--
Constant finite fiber cardinalities compose: if every fiber of `f` has size
`fiberF` and every fiber of `g` has size `fiberG`, then every fiber of
`g ∘ f` has size `fiberF * fiberG`.
-/
theorem finite_constant_fiber_card_comp
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (f : α → β) (g : β → γ)
    (fiberF fiberG : ℕ)
    (hfiber_f : ∀ b : β,
      ((Finset.univ : Finset α).filter fun a => f a = b).card =
        fiberF)
    (hfiber_g : ∀ c : γ,
      ((Finset.univ : Finset β).filter fun b => g b = c).card =
        fiberG)
    (c : γ) :
    ((Finset.univ : Finset α).filter fun a => g (f a) = c).card =
      fiberF * fiberG := by
  classical
  let source : Finset α :=
    (Finset.univ : Finset α).filter fun a => g (f a) = c
  let middle : Finset β :=
    (Finset.univ : Finset β).filter fun b => g b = c
  have hmaps : ∀ a ∈ source, f a ∈ middle := by
    intro a ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  calc
    ((Finset.univ : Finset α).filter fun a => g (f a) = c).card =
        source.card := rfl
    _ = ∑ b ∈ middle, ((source.filter fun a => f a = b).card) := by
        exact Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ _b ∈ middle, fiberF := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        have hgb : g b = c := (Finset.mem_filter.mp hb).2
        have hfiber_event :
            source.filter (fun a => f a = b) =
              (Finset.univ : Finset α).filter fun a => f a = b := by
          ext a
          by_cases hfb : f a = b
          · simp [source, hfb, hgb]
          · simp [source, hfb]
        rw [hfiber_event, hfiber_f b]
    _ = fiberF * middle.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_comm middle.card fiberF
    _ = fiberF * fiberG := by
        rw [show middle.card = fiberG from hfiber_g c]

/--
Post-composing a finite map with an equivalence preserves constant fiber
cardinality.
-/
theorem finite_constant_fiber_card_equiv_comp
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (f : α → β) (e : β ≃ γ) (fiberCard : ℕ)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter fun a => f a = b).card =
        fiberCard)
    (c : γ) :
    ((Finset.univ : Finset α).filter fun a => e (f a) = c).card =
      fiberCard := by
  classical
  have hfilter :
      ((Finset.univ : Finset α).filter fun a => e (f a) = c) =
        ((Finset.univ : Finset α).filter fun a => f a = e.symm c) := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.1, by simpa using congrArg e.symm ha.2⟩
    · intro ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.1, by simpa using congrArg e ha.2⟩
  rw [hfilter, hfiber]

/-- The identity map on a finite type has singleton fibers. -/
theorem finite_id_fiber_card
    {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α) :
    ((Finset.univ : Finset α).filter fun a => a = a₀).card = 1 := by
  classical
  have hfilter :
      ((Finset.univ : Finset α).filter fun a => a = a₀) =
        ({a₀} : Finset α) := by
    ext a
    simp
  rw [hfilter]
  simp

/-- Every fiber of an equivalence between finite types has cardinality one. -/
theorem finite_equiv_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (b : β) :
    ((Finset.univ : Finset α).filter fun a => e a = b).card = 1 := by
  classical
  exact
    finite_constant_fiber_card_equiv_comp
      (fun a : α => a) e 1
      (fun a => finite_id_fiber_card a) b

/--
If every fiber of a finite map has the same positive cardinality, then pushing
the uniform law through that map gives the uniform law on the codomain, stated
as equality of event probabilities.
-/
theorem pmfProb_uniformPMF_comp_eq_of_constant_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β) (fiberCard : ℕ) (hfiber_pos : 0 < fiberCard)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter fun a => f a = b).card =
        fiberCard)
    (p : β → Prop) [DecidablePred p] :
    pmfProb (uniformPMF α) (fun a => p (f a)) =
      pmfProb (uniformPMF β) p := by
  classical
  let sourceEvent : Finset α :=
    (Finset.univ : Finset α).filter fun a => p (f a)
  let targetEvent : Finset β :=
    (Finset.univ : Finset β).filter fun b => p b
  have hsource_card :
      sourceEvent.card = fiberCard * targetEvent.card := by
    have hmaps : ∀ a ∈ sourceEvent, f a ∈ targetEvent := by
      intro a ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    calc
      sourceEvent.card =
          ∑ b ∈ targetEvent,
            ((sourceEvent.filter fun a => f a = b).card) := by
            exact Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ _b ∈ targetEvent, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            have hp : p b := (Finset.mem_filter.mp hb).2
            have hfiber_event :
                sourceEvent.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter fun a => f a = b := by
              ext a
              by_cases hfb : f a = b
              · simp [sourceEvent, hfb, hp]
              · simp [sourceEvent, hfb]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * targetEvent.card := by
            rw [Finset.sum_const, nsmul_eq_mul]
            exact Nat.mul_comm targetEvent.card fiberCard
  have htotal_card :
      Fintype.card α = fiberCard * Fintype.card β := by
    have hmaps : ∀ a ∈ (Finset.univ : Finset α),
        f a ∈ (Finset.univ : Finset β) := by
      intro a _ha
      exact Finset.mem_univ _
    calc
      Fintype.card α =
          (Finset.univ : Finset α).card := by simp
      _ = ∑ b : β,
            (((Finset.univ : Finset α).filter fun a => f a = b).card) := by
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := (Finset.univ : Finset α))
                (t := (Finset.univ : Finset β))
                (f := f) hmaps)
      _ = ∑ _b : β, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            exact hfiber b
      _ = fiberCard * Fintype.card β := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            exact Nat.mul_comm (Fintype.card β) fiberCard
  have hsource_prob :
      pmfProb (uniformPMF α) (fun a => p (f a)) =
        (sourceEvent.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [sourceEvent] using
      (pmfProb_uniformPMF_finset (α := α) sourceEvent)
  have htarget_prob :
      pmfProb (uniformPMF β) p =
        (targetEvent.card : ℝ) / (Fintype.card β : ℝ) := by
    simpa [targetEvent] using
      (pmfProb_uniformPMF_finset (α := β) targetEvent)
  rw [hsource_prob, htarget_prob]
  have hfiber_ne_real : (fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast hfiber_pos.ne'
  have hcard_beta_pos : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
  rw [hsource_card, htotal_card]
  norm_num [Nat.cast_mul]
  field_simp [hfiber_ne_real, hcard_beta_pos]

/-- Under the uniform PMF, a singleton atom has probability `1 / #space`. -/
theorem pmfProb_uniformPMF_singleton {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (a₀ : α) :
    pmfProb (uniformPMF α) (fun a => a = a₀) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  calc
    pmfProb (uniformPMF α) (fun a => a = a₀) =
        pmfProb (uniformPMF α) (fun a => a ∈ ({a₀} : Finset α)) := by
          unfold pmfProb
          refine pmfExp_congr (uniformPMF α) ?_
          intro a
          by_cases h : a = a₀ <;> simp [h]
    _ = (({a₀} : Finset α).card : ℝ) / (Fintype.card α : ℝ) :=
        pmfProb_uniformPMF_finset ({a₀} : Finset α)
    _ = (Fintype.card α : ℝ)⁻¹ := by
          simp [div_eq_mul_inv]

/--
For a uniform draw from a finite product, the probability that the left
coordinate equals a prescribed value is `1 / #left`.
-/
theorem pmfProb_uniformPMF_prod_fst_eq {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (a₀ : α) :
    pmfProb (uniformPMF (α × β)) (fun p : α × β => p.1 = a₀) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  unfold pmfProb
  rw [pmfExp_uniformPMF_prod]
  change
    pmfPairExp (uniformPMF α) (uniformPMF β)
        (fun a _ => if a = a₀ then (1 : ℝ) else 0) =
      (Fintype.card α : ℝ)⁻¹
  calc
    pmfPairExp (uniformPMF α) (uniformPMF β)
        (fun a _ => if a = a₀ then (1 : ℝ) else 0) =
        pmfExp (uniformPMF α)
          (fun a => if a = a₀ then (1 : ℝ) else 0) := by
          unfold pmfPairExp
          simp
    _ = (Fintype.card α : ℝ)⁻¹ :=
          pmfProb_uniformPMF_singleton a₀

/--
For a uniform draw from a finite product, an event depending only on the left
coordinate has the same probability as that event under the left-coordinate
uniform draw.
-/
theorem pmfProb_uniformPMF_prod_fst_event {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (p : α → Prop) [DecidablePred p] :
    pmfProb (uniformPMF (α × β)) (fun x : α × β => p x.1) =
      pmfProb (uniformPMF α) p := by
  classical
  calc
    pmfProb (uniformPMF (α × β)) (fun x : α × β => p x.1) =
        pmfPairExp (uniformPMF α) (uniformPMF β)
          (fun a _ => if p a then (1 : ℝ) else 0) := by
          unfold pmfProb
          rw [pmfExp_uniformPMF_prod]
    _ = pmfExp (uniformPMF α)
          (fun a => if p a then (1 : ℝ) else 0) := by
          simp
    _ = pmfProb (uniformPMF α) p := by
          rfl

/--
For a uniformly drawn finite function, one coordinate hits a prescribed value
with probability `1 / #values`.
-/
theorem pmfProb_uniformPMF_fun_eval_eq {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    {i : ι} (a₀ : α) :
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = a₀) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  let Rest := {x : ι // x ≠ i}
  let e : (ι → α) ≃ (α × (Rest → α)) :=
    { toFun := fun f => (f i, fun x => f x.1)
      invFun := fun p x =>
        if hx : x = i then p.1 else p.2 ⟨x, hx⟩
      left_inv := by
        intro f
        funext x
        by_cases hx : x = i
        · subst x
          simp
        · simp [hx]
      right_inv := by
        intro p
        rcases p with ⟨a, rest⟩
        apply Prod.ext
        · simp
        · funext x
          simp [x.property] }
  let targetPred : α × (Rest → α) → Prop :=
    fun p => p.1 = a₀
  have hsource :
      pmfProb (uniformPMF (ι → α))
          (fun f : ι → α => f i = a₀) =
        pmfProb (uniformPMF (α × (Rest → α))) targetPred := by
    unfold pmfProb
    symm
    calc
      pmfExp (uniformPMF (α × (Rest → α)))
          (fun p => if targetPred p then (1 : ℝ) else 0) =
          pmfExp (uniformPMF (ι → α))
            (fun f => if targetPred (e f) then (1 : ℝ) else 0) :=
            pmfExp_uniformPMF_equiv e
              (fun p : α × (Rest → α) =>
                if targetPred p then (1 : ℝ) else 0)
      _ = pmfExp (uniformPMF (ι → α))
            (fun f => if f i = a₀ then (1 : ℝ) else 0) := by
            refine pmfExp_congr (uniformPMF (ι → α)) ?_
            intro f
            simp [targetPred, e]
  have htarget :
      pmfProb (uniformPMF (α × (Rest → α))) targetPred =
        (Fintype.card α : ℝ)⁻¹ := by
    simpa [targetPred] using
      (pmfProb_uniformPMF_prod_fst_eq
        (α := α) (β := Rest → α) (a₀ := a₀))
  exact hsource.trans htarget

/--
For two independent uniform coordinates, the probability of a prescribed pair
of values is the product of the coordinate atom probabilities.
-/
theorem pmfProb_uniformPMF_prod_eq_pair {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (a₀ : α) (b₀ : β) :
    pmfProb (uniformPMF (α × β))
        (fun p : α × β => p.1 = a₀ ∧ p.2 = b₀) =
      (Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹ := by
  classical
  calc
    pmfProb (uniformPMF (α × β))
        (fun p : α × β => p.1 = a₀ ∧ p.2 = b₀) =
        pmfProb (uniformPMF (α × β)) (fun p : α × β => p = (a₀, b₀)) := by
          unfold pmfProb
          refine pmfExp_congr (uniformPMF (α × β)) ?_
          intro p
          cases p
          simp
    _ = (Fintype.card (α × β) : ℝ)⁻¹ :=
        pmfProb_uniformPMF_singleton (α := α × β) (a₀, b₀)
    _ = (Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹ := by
          rw [Fintype.card_prod, Nat.cast_mul]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          have hβ : (Fintype.card β : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
          field_simp [hα, hβ]

/--
For a uniformly drawn finite function, two distinct coordinates hit prescribed
values with probability `1 / #values ^ 2`.
-/
theorem pmfProb_uniformPMF_fun_eq_pair_of_ne {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    {i j : ι} (hij : i ≠ j) (a₀ b₀ : α) :
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = a₀ ∧ f j = b₀) =
      (Fintype.card α : ℝ)⁻¹ ^ 2 := by
  classical
  let Rest := {x : ι // x ≠ i ∧ x ≠ j}
  let e : (ι → α) ≃ ((α × α) × (Rest → α)) :=
    { toFun := fun f => ((f i, f j), fun x => f x.1)
      invFun := fun p x =>
        if hi : x = i then p.1.1
        else if hj : x = j then p.1.2
        else p.2 ⟨x, hi, hj⟩
      left_inv := by
        intro f
        funext x
        by_cases hi : x = i
        · subst x
          simp
        · by_cases hj : x = j
          · subst x
            simp [hij.symm]
          · simp [hi, hj]
      right_inv := by
        intro p
        rcases p with ⟨⟨a, b⟩, rest⟩
        apply Prod.ext
        · apply Prod.ext
          · simp
          · simp [hij.symm]
        · funext x
          simp [x.property.1, x.property.2] }
  let targetPred : ((α × α) × (Rest → α)) → Prop :=
    fun p => p.1 = (a₀, b₀)
  have hsource :
      pmfProb (uniformPMF (ι → α))
          (fun f : ι → α => f i = a₀ ∧ f j = b₀) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := by
    unfold pmfProb
    symm
    calc
      pmfExp (uniformPMF ((α × α) × (Rest → α)))
          (fun p => if targetPred p then (1 : ℝ) else 0) =
          pmfExp (uniformPMF (ι → α))
            (fun f => if targetPred (e f) then (1 : ℝ) else 0) :=
            pmfExp_uniformPMF_equiv e
              (fun p : (α × α) × (Rest → α) =>
                if targetPred p then (1 : ℝ) else 0)
      _ = pmfExp (uniformPMF (ι → α))
            (fun f => if f i = a₀ ∧ f j = b₀ then (1 : ℝ) else 0) := by
            refine pmfExp_congr (uniformPMF (ι → α)) ?_
            intro f
            simp [targetPred, e]
  have htarget :
      pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred =
        (Fintype.card (α × α) : ℝ)⁻¹ := by
    simpa [targetPred] using
      (pmfProb_uniformPMF_prod_fst_eq
        (α := α × α) (β := Rest → α) (a₀ := (a₀, b₀)))
  calc
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = a₀ ∧ f j = b₀) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := hsource
    _ = (Fintype.card (α × α) : ℝ)⁻¹ := htarget
    _ = (Fintype.card α : ℝ)⁻¹ ^ 2 := by
          rw [Fintype.card_prod, Nat.cast_mul]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          field_simp [hα]

/--
For two independent uniform coordinates on the same finite type, the collision
probability is `1 / #space`.
-/
theorem pmfProb_uniformPMF_prod_eq_diag {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] :
    pmfProb (uniformPMF (α × α)) (fun p : α × α => p.1 = p.2) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  let diag : Finset (α × α) :=
    (Finset.univ : Finset α).image fun a => (a, a)
  have hdiag_mem : ∀ p : α × α, p ∈ diag ↔ p.1 = p.2 := by
    intro p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨a, _ha, hpa⟩
      rw [← hpa]
    · intro hp
      rcases p with ⟨a, b⟩
      simp at hp
      subst b
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hdiag_card : diag.card = Fintype.card α := by
    simpa [diag] using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset α))
        (f := fun a : α => (a, a))
        (by
          intro a b h
          exact Prod.ext_iff.mp h |>.1))
  calc
    pmfProb (uniformPMF (α × α)) (fun p : α × α => p.1 = p.2) =
        pmfProb (uniformPMF (α × α)) (fun p : α × α => p ∈ diag) := by
          unfold pmfProb
          refine pmfExp_congr (uniformPMF (α × α)) ?_
          intro p
          by_cases hp : p.1 = p.2 <;> simp [hp, hdiag_mem p]
    _ = (diag.card : ℝ) / (Fintype.card (α × α) : ℝ) :=
        pmfProb_uniformPMF_finset diag
    _ = (Fintype.card α : ℝ)⁻¹ := by
          rw [hdiag_card, Fintype.card_prod, Nat.cast_mul]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          field_simp [hα]

/--
For a uniformly drawn finite function, two distinct coordinates collide with
probability `1 / #values`.
-/
theorem pmfProb_uniformPMF_fun_eq_of_ne {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    {i j : ι} (hij : i ≠ j) :
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = f j) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  let Rest := {x : ι // x ≠ i ∧ x ≠ j}
  let e : (ι → α) ≃ ((α × α) × (Rest → α)) :=
    { toFun := fun f => ((f i, f j), fun x => f x.1)
      invFun := fun p x =>
        if hi : x = i then p.1.1
        else if hj : x = j then p.1.2
        else p.2 ⟨x, hi, hj⟩
      left_inv := by
        intro f
        funext x
        by_cases hi : x = i
        · subst x
          simp
        · by_cases hj : x = j
          · subst x
            simp [hij.symm]
          · simp [hi, hj]
      right_inv := by
        intro p
        rcases p with ⟨⟨a, b⟩, rest⟩
        apply Prod.ext
        · apply Prod.ext
          · simp
          · simp [hij.symm]
        · funext x
          simp [x.property.1, x.property.2] }
  let targetPred : ((α × α) × (Rest → α)) → Prop :=
    fun p => p.1.1 = p.1.2
  have hsource :
      pmfProb (uniformPMF (ι → α))
          (fun f : ι → α => f i = f j) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := by
    unfold pmfProb
    symm
    calc
      pmfExp (uniformPMF ((α × α) × (Rest → α)))
          (fun p => if targetPred p then (1 : ℝ) else 0) =
          pmfExp (uniformPMF (ι → α))
            (fun f => if targetPred (e f) then (1 : ℝ) else 0) :=
            pmfExp_uniformPMF_equiv e
              (fun p : (α × α) × (Rest → α) =>
                if targetPred p then (1 : ℝ) else 0)
      _ = pmfExp (uniformPMF (ι → α))
            (fun f => if f i = f j then (1 : ℝ) else 0) := by
            refine pmfExp_congr (uniformPMF (ι → α)) ?_
            intro f
            simp [targetPred, e]
  have htarget :
      pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred =
        (Fintype.card α : ℝ)⁻¹ := by
    calc
      pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred =
          pmfProb (uniformPMF (α × α))
            (fun p : α × α => p.1 = p.2) := by
            exact pmfProb_uniformPMF_prod_fst_event
              (α := α × α) (β := Rest → α)
              (fun p : α × α => p.1 = p.2)
      _ = (Fintype.card α : ℝ)⁻¹ :=
          pmfProb_uniformPMF_prod_eq_diag
  calc
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = f j) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := hsource
    _ = (Fintype.card α : ℝ)⁻¹ := htarget

/--
Lower-bound an expected finite count from a finite subfamily whose elementwise
event probabilities are uniformly bounded below.
-/
theorem pmfExp_card_filter_ge_card_mul_of_forall_mem_prob_ge
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ a, DecidablePred fun ω => p ω a]
    (s : Finset α) (rate : ℝ)
    (_hrate_nonneg : 0 ≤ rate)
    (hprob : ∀ a ∈ s, rate ≤ pmfProb μ (fun ω => p ω a)) :
    (s.card : ℝ) * rate ≤
      pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) := by
  classical
  have htail_le_sum :
      (s.card : ℝ) * rate ≤
        ∑ a ∈ s, pmfProb μ (fun ω => p ω a) := by
    calc
      (s.card : ℝ) * rate = ∑ _a ∈ s, rate := by
          simp [nsmul_eq_mul]
      _ ≤ ∑ a ∈ s, pmfProb μ (fun ω => p ω a) :=
          Finset.sum_le_sum (by
            intro a ha
            exact hprob a ha)
  have htail_sum_le_univ :
      (∑ a ∈ s, pmfProb μ (fun ω => p ω a)) ≤
        ∑ a : α, pmfProb μ (fun ω => p ω a) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro a _ha
        simp)
      (fun a _ha _hnot => by
        unfold pmfProb pmfExp
        refine Finset.sum_nonneg ?_
        intro ω _
        exact mul_nonneg ENNReal.toReal_nonneg
          (by by_cases hp : p ω a <;> simp [hp]))
  calc
    (s.card : ℝ) * rate ≤
        ∑ a ∈ s, pmfProb μ (fun ω => p ω a) := htail_le_sum
    _ ≤ ∑ a : α, pmfProb μ (fun ω => p ω a) := htail_sum_le_univ
    _ =
        pmfExp μ
          (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) := by
          exact (pmfExp_card_filter_eq_sum_pmfProb μ p).symm

/--
Lower-bound an expected finite count over a specified finite subfamily from
elementwise lower bounds on event probabilities.
-/
theorem pmfExp_card_finset_filter_ge_card_mul_of_forall_mem_prob_ge
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ a, DecidablePred fun ω => p ω a]
    (s : Finset α) (rate : ℝ)
    (_hrate_nonneg : 0 ≤ rate)
    (hprob : ∀ a ∈ s, rate ≤ pmfProb μ (fun ω => p ω a)) :
    (s.card : ℝ) * rate ≤
      pmfExp μ
        (fun ω => (((s.filter (p ω)).card : ℝ))) := by
  classical
  calc
    (s.card : ℝ) * rate = ∑ _a ∈ s, rate := by
        simp [nsmul_eq_mul]
    _ ≤ ∑ a ∈ s, pmfProb μ (fun ω => p ω a) := by
        exact Finset.sum_le_sum (by
          intro a ha
          exact hprob a ha)
    _ =
        pmfExp μ
          (fun ω => (((s.filter (p ω)).card : ℝ))) := by
        exact (pmfExp_card_finset_filter_eq_sum_pmfProb μ p s).symm

/-- Finite PMF event probability is zero iff the event has no positive-mass witness. -/
theorem pmfProb_eq_zero_of_no_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hzero : ∀ a, p a → (μ a).toReal = 0) :
    pmfProb μ p = 0 := by
  unfold pmfProb pmfExp
  exact Finset.sum_eq_zero (by
    intro a _
    by_cases hp : p a
    · simp [hp, hzero a hp]
    · simp [hp])

/-- Finite PMF event probability is positive iff some positive-mass atom satisfies it. -/
theorem pmfProb_pos_iff_exists_pos_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    0 < pmfProb μ p ↔ ∃ a, p a ∧ 0 < (μ a).toReal := by
  constructor
  · intro hpos
    by_contra hno
    have hzero : ∀ a, p a → (μ a).toReal = 0 := by
      intro a ha
      have hnot : ¬ 0 < (μ a).toReal := by
        intro hmass
        exact hno ⟨a, ha, hmass⟩
      exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    rw [pmfProb_eq_zero_of_no_mass μ p hzero] at hpos
    exact (lt_irrefl 0 hpos)
  · rintro ⟨a, ha, hmass⟩
    have hnonneg : ∀ b : α, 0 ≤ (μ b).toReal * (if p b then (1 : ℝ) else 0) := by
      intro b
      by_cases hp : p b <;> simp [hp, ENNReal.toReal_nonneg]
    have hsingle_pos : 0 < (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
      simpa [ha] using hmass
    have hsingle_le :
        (μ a).toReal * (if p a then (1 : ℝ) else 0) ≤
          ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset α))
        (f := fun b : α => (μ b).toReal * (if p b then (1 : ℝ) else 0))
        (by intro b _; exact hnonneg b)
        (Finset.mem_univ a)
    have hsum_pos : 0 < ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) :=
      lt_of_lt_of_le hsingle_pos hsingle_le
    unfold pmfProb pmfExp
    exact hsum_pos

/-- Finite PMF probabilities are at most one. -/
theorem pmfProb_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb μ p ≤ 1 := by
  classical
  exact pmfExp_le_of_forall_le μ (fun a => if p a then (1 : ℝ) else 0) 1
    (by intro a; by_cases hp : p a <;> simp [hp])

/-- Complement rule for finite PMF probabilities. -/
theorem pmfProb_compl {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb μ (fun a => ¬p a) = 1 - pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ a : α, (μ a).toReal * (if ¬p a then (1 : ℝ) else 0)
        = ∑ a : α, (
            (μ a).toReal * 1 -
              (μ a).toReal * (if p a then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p a <;> simp [hp]
    _ = (∑ a : α, (μ a).toReal * 1) -
          ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          simp [pmfToRealSum μ]

/-- Positive mass inside an event makes its finite PMF probability positive. -/
theorem pmfProb_pos_of_mass {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : p a₀) (hmass : 0 < (μ a₀).toReal) :
    0 < pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  have hnonneg :
      ∀ a ∈ (Finset.univ : Finset α),
        0 ≤ (μ a).toReal * if p a then (1 : ℝ) else 0 := by
    intro a _
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    by_cases hpa : p a <;> simp [hpa]
  have hterm :
      (μ a₀).toReal * (if p a₀ then (1 : ℝ) else 0) = (μ a₀).toReal := by
    simp [hp]
  have hle :
      (μ a₀).toReal * (if p a₀ then (1 : ℝ) else 0) ≤
        ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    exact Finset.single_le_sum hnonneg (Finset.mem_univ a₀)
  rw [hterm] at hle
  exact lt_of_lt_of_le hmass hle

/-- A single event atom lower-bounds the finite PMF probability of the event. -/
theorem pmf_apply_toReal_le_pmfProb_of_mem {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : p a₀) :
    (μ a₀).toReal ≤ pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  have hnonneg :
      ∀ a ∈ (Finset.univ : Finset α),
        0 ≤ (μ a).toReal * if p a then (1 : ℝ) else 0 := by
    intro a _
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    by_cases hpa : p a <;> simp [hpa]
  have hterm :
      (μ a₀).toReal * (if p a₀ then (1 : ℝ) else 0) = (μ a₀).toReal := by
    simp [hp]
  have hle :
      (μ a₀).toReal * (if p a₀ then (1 : ℝ) else 0) ≤
        ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    exact Finset.single_le_sum hnonneg (Finset.mem_univ a₀)
  simpa [hterm] using hle

/--
If a target atom is identified with the probability of a finite preimage event,
then a positive-mass source point in that preimage makes the target atom
positive.
-/
theorem pmf_apply_toReal_pos_of_pmfProb_preimage
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF β) (ν : PMF α) (f : α → β)
    (hpreimage : ∀ b, (μ b).toReal = pmfProb ν (fun a => f a = b))
    {a₀ : α} {b : β}
    (hf : f a₀ = b) (hmass : 0 < (ν a₀).toReal) :
    0 < (μ b).toReal := by
  rw [hpreimage b]
  exact pmfProb_pos_of_mass ν (fun a => f a = b) a₀ hf hmass

/--
If every target atom is identified with the probability of its finite preimage,
then every target event has probability equal to the probability of its
preimage.
-/
theorem pmfProb_eq_pmfProb_preimage_of_atom_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF β) (ν : PMF α) (f : α → β)
    (hatom : ∀ b, (μ b).toReal = pmfProb ν (fun a => f a = b))
    (p : β → Prop) [DecidablePred p] :
    pmfProb μ p = pmfProb ν (fun a => p (f a)) := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ b : β, (μ b).toReal * (if p b then (1 : ℝ) else 0)
        = ∑ b : β,
            (∑ a : α, (ν a).toReal * (if f a = b then (1 : ℝ) else 0)) *
              (if p b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [hatom b]
          rfl
    _ = ∑ b : β, ∑ a : α,
            ((ν a).toReal * (if f a = b then (1 : ℝ) else 0)) *
              (if p b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β,
            ((ν a).toReal * (if f a = b then (1 : ℝ) else 0)) *
              (if p b then (1 : ℝ) else 0) := by
          exact Finset.sum_comm
    _ = ∑ a : α, (ν a).toReal * (if p (f a) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p (f a)
          · rw [Finset.sum_eq_single (f a)]
            · simp [hp]
            · intro b _ hb
              by_cases hfb : f a = b
              · exact False.elim (hb hfb.symm)
              · simp [hfb]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ (f a)))
          · rw [Finset.sum_eq_zero]
            · simp [hp]
            · intro b _
              by_cases hfb : f a = b
              · have hpb : ¬ p b := by simpa [hfb] using hp
                simp [hfb, hpb]
              · simp [hfb]

/-- Finite PMF event probability as the real value of the PMF outer measure. -/
theorem pmfProb_eq_toOuterMeasure_toReal
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb μ p = (μ.toOuterMeasure {a | p a}).toReal := by
  classical
  unfold pmfProb pmfExp
  have h_ne_top :
      ∀ a ∈ (Finset.univ : Finset α),
        Set.indicator {a | p a} μ a ≠ ⊤ := by
    intro a _
    by_cases hp : p a
    · simpa [Set.indicator, hp] using μ.apply_ne_top a
    · simp [Set.indicator, hp]
  calc
    ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0)
        = ∑ a : α, (Set.indicator {a | p a} μ a).toReal := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p a
          · simp [Set.indicator, hp]
          · simp [Set.indicator, hp]
    _ = (∑ a : α, Set.indicator {a | p a} μ a).toReal := by
          symm
          simpa using (ENNReal.toReal_sum (s := (Finset.univ : Finset α))
            (f := fun a => Set.indicator {a | p a} μ a) h_ne_top)
    _ = (μ.toOuterMeasure {a | p a}).toReal := by
          rw [PMF.toOuterMeasure_apply_fintype]

/-- The atom mass of a finite PMF pushforward is the probability of the preimage atom. -/
theorem pmf_map_apply_toReal_eq_pmfProb_preimage
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ν : PMF α) (f : α → β) (b : β) :
    ((ν.map f) b).toReal = pmfProb ν (fun a => f a = b) := by
  classical
  rw [pmfProb_eq_toOuterMeasure_toReal]
  have hsingleton :
      (ν.map f).toOuterMeasure ({b} : Set β) = (ν.map f) b :=
    PMF.toOuterMeasure_apply_singleton (ν.map f) b
  have hmap :
      (ν.map f).toOuterMeasure ({b} : Set β) =
        ν.toOuterMeasure (f ⁻¹' ({b} : Set β)) :=
    PMF.toOuterMeasure_map_apply f ν ({b} : Set β)
  rw [← hsingleton, hmap]
  rfl

theorem pmfExp_map {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (g : α → β) (f : β → ℝ) :
    pmfExp (μ.map g) f = pmfExp μ (fun a => f (g a)) := by
  classical
  calc
    pmfExp (μ.map g) f =
        ∑ b : β, (pmfProb μ (fun a => g a = b)) * f b := by
          unfold pmfExp
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [pmf_map_apply_toReal_eq_pmfProb_preimage]
    _ = ∑ b : β, (∑ a : α, (μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) * f b := by
          unfold pmfProb pmfExp
          rfl
    _ = ∑ b : β, ∑ a : α, ((μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) * f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β, ((μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) * f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (μ a).toReal * f (g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          calc
            ∑ b : β, ((μ a).toReal *
                (if g a = b then (1 : ℝ) else 0)) * f b =
                (μ a).toReal *
                  ∑ b : β, (if g a = b then (1 : ℝ) else 0) * f b := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro b _
                  ring
            _ = (μ a).toReal * f (g a) := by
                  simp [eq_comm]
    _ = pmfExp μ (fun a => f (g a)) := by
          rfl

/-- Finite vector expectation commutes with pushforward of a PMF. -/
theorem pmfVectorExp_map {α β V : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : PMF α) (g : α → β) (f : β → V) :
    pmfVectorExp (μ.map g) f = pmfVectorExp μ (fun a => f (g a)) := by
  classical
  calc
    pmfVectorExp (μ.map g) f =
        ∑ b : β, (pmfProb μ (fun a => g a = b)) • f b := by
          unfold pmfVectorExp
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [pmf_map_apply_toReal_eq_pmfProb_preimage]
    _ = ∑ b : β, (∑ a : α, (μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) • f b := by
          unfold pmfProb pmfExp
          rfl
    _ = ∑ b : β, ∑ a : α, ((μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
    _ = ∑ a : α, ∑ b : β, ((μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) • f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (μ a).toReal • f (g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          calc
            ∑ b : β, ((μ a).toReal *
                (if g a = b then (1 : ℝ) else 0)) • f b =
                (μ a).toReal • ∑ b : β,
                  (if g a = b then (1 : ℝ) else 0) • f b := by
                    rw [Finset.smul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    rw [mul_smul]
            _ = (μ a).toReal • f (g a) := by
                  simp [eq_comm]
    _ = pmfVectorExp μ (fun a => f (g a)) := by
          rfl

/-- A difference of finite vector expectations is the mass-difference weighted sum. -/
theorem pmfVectorExp_sub_eq_sum_massSub_smul
    {α V : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ ν : PMF α) (f : α → V) :
    pmfVectorExp μ f - pmfVectorExp ν f =
      ∑ a : α, ((μ a).toReal - (ν a).toReal) • f a := by
  unfold pmfVectorExp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [sub_smul]

/--
Coordinatewise PMF-mass error controls a vector expectation once a reference
value bounds the range of the statistic.  Centering at the reference removes
any dependence on the statistic's absolute level.
-/
theorem norm_pmfVectorExp_sub_le_card_mul_of_massDeviation
    {α V : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ ν : PMF α) (f : α → V) (reference : α)
    (epsilon bound : ℝ) (hepsilon : 0 ≤ epsilon)
    (hmass : ∀ a, |(μ a).toReal - (ν a).toReal| ≤ epsilon)
    (hbound : ∀ a, ‖f a - f reference‖ ≤ bound) :
    ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤
      (Fintype.card α : ℝ) * epsilon * bound := by
  have hμ : ∑ a : α, (μ a).toReal = 1 := by
    simpa [pmfExp] using (pmfExp_const μ (1 : ℝ))
  have hν : ∑ a : α, (ν a).toReal = 1 := by
    simpa [pmfExp] using (pmfExp_const ν (1 : ℝ))
  have hmassSum : ∑ a : α, ((μ a).toReal - (ν a).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, hμ, hν]
    ring
  rw [pmfVectorExp_sub_eq_sum_massSub_smul]
  have hcenter :
      (∑ a : α, ((μ a).toReal - (ν a).toReal) • f a) =
        ∑ a : α, ((μ a).toReal - (ν a).toReal) • (f a - f reference) := by
    calc
      ∑ a : α, ((μ a).toReal - (ν a).toReal) • f a =
          ∑ a : α, ((μ a).toReal - (ν a).toReal) •
            ((f a - f reference) + f reference) := by
              apply Finset.sum_congr rfl
              intro a _
              abel
      _ = (∑ a : α, ((μ a).toReal - (ν a).toReal) • (f a - f reference)) +
          (∑ a : α, ((μ a).toReal - (ν a).toReal)) • f reference := by
            calc
              ∑ a : α, ((μ a).toReal - (ν a).toReal) •
                  ((f a - f reference) + f reference) =
                  ∑ a : α, (((μ a).toReal - (ν a).toReal) • (f a - f reference) +
                    ((μ a).toReal - (ν a).toReal) • f reference) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [smul_add]
              _ = (∑ a : α, ((μ a).toReal - (ν a).toReal) • (f a - f reference)) +
                  ∑ a : α, ((μ a).toReal - (ν a).toReal) • f reference := by
                    rw [Finset.sum_add_distrib]
              _ = (∑ a : α, ((μ a).toReal - (ν a).toReal) • (f a - f reference)) +
                  (∑ a : α, ((μ a).toReal - (ν a).toReal)) • f reference := by
                    rw [← Finset.sum_smul]
      _ = ∑ a : α, ((μ a).toReal - (ν a).toReal) • (f a - f reference) := by
            rw [hmassSum, zero_smul, add_zero]
  rw [hcenter]
  calc
    ‖∑ a : α, ((μ a).toReal - (ν a).toReal) • (f a - f reference)‖ ≤
        ∑ a : α, ‖((μ a).toReal - (ν a).toReal) • (f a - f reference)‖ :=
      norm_sum_le _ _
    _ = ∑ a : α, |(μ a).toReal - (ν a).toReal| * ‖f a - f reference‖ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ _a : α, epsilon * bound := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul (hmass a) (hbound a) (norm_nonneg _) hepsilon
    _ = (Fintype.card α : ℝ) * epsilon * bound := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Finite PMF event probability commutes with pushforward. -/
theorem pmfProb_map {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (g : α → β) (p : β → Prop) [DecidablePred p] :
    pmfProb (μ.map g) p = pmfProb μ (fun a => p (g a)) := by
  unfold pmfProb
  rw [pmfExp_map]

/-- Finite expectation of a PMF bind decomposes into iterated expectations. -/
theorem pmfExp_bind {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (κ : α → PMF β) (f : β → ℝ) :
    pmfExp (μ.bind κ) f = pmfExp μ (fun a => pmfExp (κ a) f) := by
  classical
  unfold pmfExp
  calc
    ∑ b : β, ((μ.bind κ) b).toReal * f b =
        ∑ b : β, (∑ a : α, (μ a).toReal * (κ a b).toReal) * f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          have hbind_toReal :
              ((μ.bind κ) b).toReal =
                ∑ a : α, (μ a).toReal * (κ a b).toReal := by
            have h_ne_top :
                ∀ a ∈ (Finset.univ : Finset α), μ a * κ a b ≠ ⊤ := by
              intro a _
              exact ENNReal.mul_ne_top (μ.apply_ne_top a) ((κ a).apply_ne_top b)
            calc
              ((μ.bind κ) b).toReal =
                  (∑ a : α, μ a * κ a b).toReal := by
                    rw [PMF.bind_apply, tsum_fintype]
              _ = ∑ a : α, (μ a * κ a b).toReal := by
                    exact
                      ENNReal.toReal_sum
                        (s := (Finset.univ : Finset α))
                        (f := fun a : α => μ a * κ a b) h_ne_top
              _ = ∑ a : α, (μ a).toReal * (κ a b).toReal := by
                    simp [ENNReal.toReal_mul]
          rw [hbind_toReal]
    _ = ∑ b : β, ∑ a : α,
          ((μ a).toReal * (κ a b).toReal) * f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β,
          ((μ a).toReal * (κ a b).toReal) * f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (μ a).toReal *
          ∑ b : β, (κ a b).toReal * f b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring

/-- Finite event probability of a PMF bind decomposes into iterated probabilities. -/
theorem pmfProb_bind {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (κ : α → PMF β) (p : β → Prop) [DecidablePred p] :
    pmfProb (μ.bind κ) p = pmfExp μ (fun a => pmfProb (κ a) p) := by
  unfold pmfProb
  rw [pmfExp_bind]

/-- Positive mass outside an event makes its finite PMF probability strictly below one. -/
theorem pmfProb_lt_one_of_mass_not {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : ¬p a₀) (hmass : 0 < (μ a₀).toReal) :
    pmfProb μ p < 1 := by
  classical
  have hcompl :
      0 < pmfProb μ (fun a => ¬p a) :=
    pmfProb_pos_of_mass μ (fun a => ¬p a) a₀ hp hmass
  rw [pmfProb_compl μ p] at hcompl
  linarith

/-- Monotonicity of finite PMF probabilities under event inclusion. -/
theorem pmfProb_le_of_imp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) :
    pmfProb μ p ≤ pmfProb μ q := by
  classical
  unfold pmfProb
  refine pmfExp_le_pmfExp_of_forall_le μ
    (fun a => if p a then (1 : ℝ) else 0)
    (fun a => if q a then (1 : ℝ) else 0) ?_
  intro a
  by_cases hp : p a
  · have hq : q a := himp a hp
    simp [hp, hq]
  · by_cases hq : q a <;> simp [hp, hq]

/--
If a finite PMF puts less than `δ` mass outside `center`, then every atom is
within `δ` of the pure point mass at `center`.
-/
theorem atomwise_close_to_pure_of_wrong_prob_lt
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (center : α) {δ : ℝ} (hδ : 0 < δ)
    (hwrong : pmfProb μ (fun a => a ≠ center) < δ) :
    ∀ a : α,
      |(μ a).toReal - (((PMF.pure center : PMF α) a).toReal)| < δ := by
  classical
  intro a
  by_cases ha : a = center
  · subst a
    have hcompl :
        pmfProb μ (fun x => x ≠ center) = 1 - (μ center).toReal := by
      rw [← pmfProb_singleton μ center]
      simpa [Ne] using
        (pmfProb_compl μ (fun x => x = center))
    have hle : (μ center).toReal ≤ 1 := by
      rw [← pmfProb_singleton μ center]
      exact pmfProb_le_one μ (fun x => x = center)
    have habs :
        |(μ center).toReal -
            (((PMF.pure center : PMF α) center).toReal)| =
          1 - (μ center).toReal := by
      have hpure :
          (((PMF.pure center : PMF α) center).toReal) = 1 := by
        simp [PMF.pure_apply]
      rw [hpure]
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [habs, ← hcompl]
    exact hwrong
  · have hsingle_le :
        pmfProb μ (fun x => x = a) ≤ pmfProb μ (fun x => x ≠ center) :=
      pmfProb_le_of_imp μ (fun x => x = a) (fun x => x ≠ center) (by
        intro x hx
        exact fun hxc => ha (hx.symm.trans hxc))
    have hmass_lt : (μ a).toReal < δ := by
      rw [← pmfProb_singleton μ a]
      exact lt_of_le_of_lt hsingle_le hwrong
    have hpure : (((PMF.pure center : PMF α) a).toReal) = 0 := by
      simp [PMF.pure_apply, ha]
    rw [hpure, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hmass_lt

/-- A finite PMF expectation of a pointwise nonnegative function is nonnegative. -/
theorem pmfExp_nonneg_of_forall_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (h : ∀ a, 0 ≤ f a) :
    0 ≤ pmfExp μ f := by
  unfold pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  exact mul_nonneg ENNReal.toReal_nonneg (h a)

/-- Finite Markov inequality before division: a nonnegative statistic bounds
the probability that it exceeds a threshold. -/
theorem mul_pmfProb_le_pmfExp_of_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (h : ∀ a, 0 ≤ f a) (threshold : ℝ) :
    threshold * pmfProb μ (fun a => threshold ≤ f a) ≤ pmfExp μ f := by
  classical
  unfold pmfProb pmfExp
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : threshold ≤ f a
  · simp only [if_pos ha, mul_one]
    calc
      threshold * (μ a).toReal = (μ a).toReal * threshold := by ring
      _ ≤ (μ a).toReal * f a :=
        mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
  · simp [ha, mul_nonneg ENNReal.toReal_nonneg (h a)]

/-- Finite Markov inequality for a strictly positive threshold. -/
theorem pmfProb_le_div_pmfExp_of_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (h : ∀ a, 0 ≤ f a)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    pmfProb μ (fun a => threshold ≤ f a) ≤ pmfExp μ f / threshold := by
  rw [le_div_iff₀ hthreshold]
  simpa [mul_comm] using mul_pmfProb_le_pmfExp_of_nonneg μ f h threshold

/-- Variance of a real-valued random variable under a finite PMF. -/
noncomputable def pmfVariance {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) : ℝ :=
  pmfExp μ (fun a => (X a - pmfExp μ X) ^ 2)

/-- Finite PMF variance is nonnegative. -/
theorem pmfVariance_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) :
    0 ≤ pmfVariance μ X := by
  unfold pmfVariance
  exact pmfExp_nonneg_of_forall_nonneg μ _ (fun a => sq_nonneg _)

/-- Finite-PMF variance as second moment minus the square of the mean. -/
theorem pmfVariance_eq_exp_sq_sub_sq_exp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) :
    pmfVariance μ X =
      pmfExp μ (fun a => X a ^ 2) - (pmfExp μ X) ^ 2 := by
  let m : ℝ := pmfExp μ X
  calc
    pmfVariance μ X =
        pmfExp μ (fun a => (X a - m) ^ 2) := by
          simp [pmfVariance, m]
    _ = pmfExp μ
          (fun a => X a ^ 2 - (2 * m) * X a + m ^ 2) := by
          refine pmfExp_congr μ ?_
          intro a
          ring
    _ = pmfExp μ (fun a => X a ^ 2) -
          (2 * m) * pmfExp μ X + m ^ 2 := by
          rw [pmfExp_add]
          rw [pmfExp_sub]
          rw [pmfExp_const_mul]
          simp [pmfExp_const]
    _ = pmfExp μ (fun a => X a ^ 2) - (pmfExp μ X) ^ 2 := by
          simp [m]
          ring

/--
A nonnegative finite random variable bounded by `M` has variance at most
`M` times its mean.  This is the standard self-bounding second-moment
estimate `X^2 <= M * X`.
-/
theorem pmfVariance_le_mul_pmfExp_of_nonneg_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) (M : ℝ)
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hX_le : ∀ a, X a ≤ M) :
    pmfVariance μ X ≤ M * pmfExp μ X := by
  have hpoint : ∀ a, X a ^ 2 ≤ M * X a := by
    intro a
    have hfactor : 0 ≤ M - X a := by linarith [hX_le a]
    have hproduct := mul_nonneg (hX_nonneg a) hfactor
    nlinarith
  have hsecond :
      pmfExp μ (fun a => X a ^ 2) ≤ pmfExp μ (fun a => M * X a) :=
    pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint
  calc
    pmfVariance μ X =
        pmfExp μ (fun a => X a ^ 2) - (pmfExp μ X) ^ 2 :=
      pmfVariance_eq_exp_sq_sub_sq_exp μ X
    _ ≤ pmfExp μ (fun a => X a ^ 2) := by
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ pmfExp μ (fun a => M * X a) := hsecond
    _ = M * pmfExp μ X := pmfExp_const_mul μ M X

/--
Finite-PMF Chebyshev inequality in centered absolute-deviation form.
-/
theorem pmfProb_abs_sub_mean_ge_le_variance_div_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    pmfProb μ (fun a => ε ≤ |X a - pmfExp μ X|) ≤
      pmfVariance μ X / ε ^ 2 := by
  classical
  have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hpoint :
      ∀ a,
        (if ε ≤ |X a - pmfExp μ X| then (1 : ℝ) else 0) ≤
          (X a - pmfExp μ X) ^ 2 / ε ^ 2 := by
    intro a
    by_cases hdev : ε ≤ |X a - pmfExp μ X|
    · have habs : |ε| ≤ |X a - pmfExp μ X| := by
        simpa [abs_of_pos hε] using hdev
      have hsq : ε ^ 2 ≤ (X a - pmfExp μ X) ^ 2 := by
        simpa [sq_abs] using (sq_le_sq.2 habs)
      have hone :
          (1 : ℝ) ≤ (X a - pmfExp μ X) ^ 2 / ε ^ 2 := by
        rw [le_div_iff₀ hε2_pos]
        simpa using hsq
      simpa [hdev] using hone
    · have hnonneg :
          0 ≤ (X a - pmfExp μ X) ^ 2 / ε ^ 2 := by
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      simpa [hdev] using hnonneg
  calc
    pmfProb μ (fun a => ε ≤ |X a - pmfExp μ X|) ≤
        pmfExp μ
          (fun a => (X a - pmfExp μ X) ^ 2 / ε ^ 2) :=
          pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint
    _ = pmfVariance μ X / ε ^ 2 := by
          simp [pmfVariance, div_eq_mul_inv, pmfExp_mul_const]

/-- Strict-tail version of finite-PMF Chebyshev. -/
theorem pmfProb_abs_sub_mean_gt_le_variance_div_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    pmfProb μ (fun a => ε < |X a - pmfExp μ X|) ≤
      pmfVariance μ X / ε ^ 2 := by
  classical
  exact le_trans
    (pmfProb_le_of_imp μ
      (fun a => ε < |X a - pmfExp μ X|)
      (fun a => ε ≤ |X a - pmfExp μ X|)
      (fun _a ha => le_of_lt ha))
    (pmfProb_abs_sub_mean_ge_le_variance_div_sq μ X hε)

/--
If a real-valued finite random variable has positive expectation and variance at
most its expectation, the lower-half tail has probability at most `4 / E[X]`.
-/
theorem pmfProb_lt_half_expectation_le_four_div_expectation_of_variance_le_expectation
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) (EX : ℝ)
    (hmean : pmfExp μ X = EX)
    (hEX_pos : 0 < EX)
    (hvar : pmfVariance μ X ≤ EX) :
    pmfProb μ (fun a => X a < EX / 2) ≤ 4 / EX := by
  classical
  have hhalf_pos : 0 < EX / 2 := by positivity
  have htail :
      pmfProb μ (fun a => X a < EX / 2) ≤
        pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) := by
    refine pmfProb_le_of_imp μ
      (fun a => X a < EX / 2)
      (fun a => EX / 2 < |X a - pmfExp μ X|) ?_
    intro a ha
    rw [hmean]
    have hneg : X a - EX < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have hcheb :
      pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) ≤
        pmfVariance μ X / (EX / 2) ^ 2 :=
    pmfProb_abs_sub_mean_gt_le_variance_div_sq μ X hhalf_pos
  have hvar_div :
      pmfVariance μ X / (EX / 2) ^ 2 ≤ EX / (EX / 2) ^ 2 :=
    div_le_div_of_nonneg_right hvar (sq_nonneg _)
  calc
    pmfProb μ (fun a => X a < EX / 2) ≤
        pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) := htail
    _ ≤ pmfVariance μ X / (EX / 2) ^ 2 := hcheb
    _ ≤ EX / (EX / 2) ^ 2 := hvar_div
    _ = 4 / EX := by
          field_simp [ne_of_gt hEX_pos]
          ring

/--
Constant-factor lower-half Chebyshev bound.  If `Var X <= C * E[X]`, the
probability that `X` falls below half its mean is at most `4C / E[X]`.
-/
theorem pmfProb_lt_half_expectation_le_four_mul_div_expectation_of_variance_le_mul_expectation
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) (EX C : ℝ)
    (hmean : pmfExp μ X = EX)
    (hEX_pos : 0 < EX)
    (_hC_nonneg : 0 ≤ C)
    (hvar : pmfVariance μ X ≤ C * EX) :
    pmfProb μ (fun a => X a < EX / 2) ≤ 4 * C / EX := by
  classical
  have hhalf_pos : 0 < EX / 2 := by positivity
  have htail :
      pmfProb μ (fun a => X a < EX / 2) ≤
        pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) := by
    refine pmfProb_le_of_imp μ
      (fun a => X a < EX / 2)
      (fun a => EX / 2 < |X a - pmfExp μ X|) ?_
    intro a ha
    rw [hmean]
    have hneg : X a - EX < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have hcheb :
      pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) ≤
        pmfVariance μ X / (EX / 2) ^ 2 :=
    pmfProb_abs_sub_mean_gt_le_variance_div_sq μ X hhalf_pos
  have hvar_div :
      pmfVariance μ X / (EX / 2) ^ 2 ≤ (C * EX) / (EX / 2) ^ 2 :=
    div_le_div_of_nonneg_right hvar (sq_nonneg _)
  calc
    pmfProb μ (fun a => X a < EX / 2) ≤
        pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) := htail
    _ ≤ pmfVariance μ X / (EX / 2) ^ 2 := hcheb
    _ ≤ (C * EX) / (EX / 2) ^ 2 := hvar_div
    _ = 4 * C / EX := by
          field_simp [ne_of_gt hEX_pos]
          ring

/--
Second moment of a finite indicator count as the double sum of intersection
probabilities.
-/
theorem pmfExp_card_filter_sq_eq_sum_pmfProb_inter
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ i, DecidablePred fun ω => p ω i] :
    pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2) =
      ∑ i : α, ∑ j : α,
        pmfProb μ (fun ω => p ω i ∧ p ω j) := by
  classical
  have hsq :
      ∀ ω,
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2 =
          ∑ i : α, ∑ j : α,
            if p ω i ∧ p ω j then (1 : ℝ) else 0 := by
    intro ω
    have hcard :
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) =
          ∑ i : α, if p ω i then (1 : ℝ) else 0 := by
      simp
    calc
      (((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2 =
          (∑ i : α, if p ω i then (1 : ℝ) else 0) *
            (∑ j : α, if p ω j then (1 : ℝ) else 0) := by
            rw [hcard]
            ring
      _ = ∑ i : α,
            (if p ω i then (1 : ℝ) else 0) *
              (∑ j : α, if p ω j then (1 : ℝ) else 0) := by
            rw [Finset.sum_mul]
      _ = ∑ i : α, ∑ j : α,
            (if p ω i then (1 : ℝ) else 0) *
              (if p ω j then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ i : α, ∑ j : α,
            if p ω i ∧ p ω j then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hi : p ω i <;> by_cases hj : p ω j <;> simp [hi, hj]
  unfold pmfExp pmfProb
  calc
    ∑ ω : Ω, (μ ω).toReal *
        ((((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2) =
        ∑ ω : Ω, (μ ω).toReal *
          (∑ i : α, ∑ j : α,
            if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [hsq ω]
    _ = ∑ ω : Ω, ∑ i : α, ∑ j : α,
          (μ ω).toReal *
            (if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i : α, ∑ ω : Ω, ∑ j : α,
          (μ ω).toReal *
            (if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ i : α, ∑ j : α, ∑ ω : Ω,
          (μ ω).toReal *
            (if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]

/--
For a finite sum of indicators, pairwise negative correlation bounds the
variance by the expectation.
-/
theorem pmfVariance_card_filter_le_pmfExp_card_filter_of_pairwise_inter_le_mul
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ i, DecidablePred fun ω => p ω i]
    (hneg : ∀ i j : α, i ≠ j →
      pmfProb μ (fun ω => p ω i ∧ p ω j) ≤
        pmfProb μ (fun ω => p ω i) *
          pmfProb μ (fun ω => p ω j)) :
    pmfVariance μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) ≤
      pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) := by
  classical
  let count : Ω → ℝ :=
    fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)
  let P : α → ℝ := fun i => pmfProb μ (fun ω => p ω i)
  let P₂ : α → α → ℝ :=
    fun i j => pmfProb μ (fun ω => p ω i ∧ p ω j)
  have hmean :
      pmfExp μ count = ∑ i : α, P i := by
    simpa [count, P] using pmfExp_card_filter_eq_sum_pmfProb μ p
  have hsecond :
      pmfExp μ (fun ω => count ω ^ 2) =
        ∑ i : α, ∑ j : α, P₂ i j := by
    simpa [count, P₂] using pmfExp_card_filter_sq_eq_sum_pmfProb_inter μ p
  have hterm :
      ∀ i j : α,
        P₂ i j ≤ P i * P j + if i = j then P i else 0 := by
    intro i j
    by_cases hij : i = j
    · have hdiag : P₂ i j ≤ P i := by
        refine pmfProb_le_of_imp μ
          (fun ω => p ω i ∧ p ω j) (fun ω => p ω i) ?_
        intro ω hω
        exact hω.1
      have hprod_nonneg : 0 ≤ P i * P j :=
        mul_nonneg (pmfProb_nonneg μ (fun ω => p ω i))
          (pmfProb_nonneg μ (fun ω => p ω j))
      simpa [P₂, P, hij] using
        (le_trans hdiag (by linarith : P i ≤ P i * P j + P i))
    · simpa [P₂, P, hij] using hneg i j hij
  have hdouble_le :
      (∑ i : α, ∑ j : α, P₂ i j) ≤
        ∑ i : α, ∑ j : α, (P i * P j + if i = j then P i else 0) :=
    Finset.sum_le_sum (by
      intro i _
      exact Finset.sum_le_sum (by
        intro j _
        exact hterm i j))
  have hprod :
      (∑ i : α, ∑ j : α, P i * P j) = (∑ i : α, P i) ^ 2 := by
    calc
      (∑ i : α, ∑ j : α, P i * P j) =
          ∑ i : α, P i * (∑ j : α, P j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
      _ = (∑ i : α, P i) * (∑ j : α, P j) := by
          rw [Finset.sum_mul]
      _ = (∑ i : α, P i) ^ 2 := by ring
  have hdiag_sum :
      (∑ i : α, ∑ j : α, if i = j then P i else 0) =
        ∑ i : α, P i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp
  have hbound_sum :
      (∑ i : α, ∑ j : α, (P i * P j + if i = j then P i else 0)) =
        (∑ i : α, P i) ^ 2 + ∑ i : α, P i := by
    calc
      (∑ i : α, ∑ j : α, (P i * P j + if i = j then P i else 0)) =
          (∑ i : α, ∑ j : α, P i * P j) +
            (∑ i : α, ∑ j : α, if i = j then P i else 0) := by
            simp [Finset.sum_add_distrib]
      _ = (∑ i : α, P i) ^ 2 + ∑ i : α, P i := by
            rw [hprod, hdiag_sum]
  have hsecond_le :
      pmfExp μ (fun ω => count ω ^ 2) ≤
        (pmfExp μ count) ^ 2 + pmfExp μ count := by
    calc
      pmfExp μ (fun ω => count ω ^ 2) =
          ∑ i : α, ∑ j : α, P₂ i j := hsecond
      _ ≤ ∑ i : α, ∑ j : α,
            (P i * P j + if i = j then P i else 0) := hdouble_le
      _ = (∑ i : α, P i) ^ 2 + ∑ i : α, P i := hbound_sum
      _ = (pmfExp μ count) ^ 2 + pmfExp μ count := by rw [hmean]
  calc
    pmfVariance μ count =
        pmfExp μ (fun ω => count ω ^ 2) - (pmfExp μ count) ^ 2 :=
          pmfVariance_eq_exp_sq_sub_sq_exp μ count
    _ ≤ pmfExp μ count := by linarith

/-- Finite union bound for real-valued PMF probabilities. -/
theorem pmfProb_exists_mem_le_sum {α ι : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (s : Finset ι) (p : ι → α → Prop)
    [DecidablePred fun a => ∃ i, i ∈ s ∧ p i a]
    [∀ i, DecidablePred (p i)] :
    pmfProb μ (fun a => ∃ i, i ∈ s ∧ p i a) ≤
      ∑ i ∈ s, pmfProb μ (p i) := by
  classical
  have hpoint :
      ∀ a : α,
        (if ∃ i, i ∈ s ∧ p i a then (1 : ℝ) else 0) ≤
          ∑ i ∈ s, (if p i a then (1 : ℝ) else 0) := by
    intro a
    by_cases h : ∃ i, i ∈ s ∧ p i a
    · rcases h with ⟨i, hi, hp⟩
      have hnonneg :
          ∀ j ∈ s, 0 ≤ (if p j a then (1 : ℝ) else 0) := by
        intro j _hj
        by_cases hj : p j a <;> simp [hj]
      have hterm :
          (if p i a then (1 : ℝ) else 0) ≤
            ∑ j ∈ s, (if p j a then (1 : ℝ) else 0) :=
        Finset.single_le_sum
          (s := s) (f := fun j => if p j a then (1 : ℝ) else 0)
          hnonneg hi
      have hleft :
          (if ∃ i, i ∈ s ∧ p i a then (1 : ℝ) else 0) = 1 := by
        exact if_pos ⟨i, hi, hp⟩
      have hterm' :
          (1 : ℝ) ≤ ∑ j ∈ s, (if p j a then (1 : ℝ) else 0) := by
        rw [show (if p i a then (1 : ℝ) else 0) = 1 by simp [hp]] at hterm
        exact hterm
      simpa [hleft] using hterm'
    · simp [h]
  unfold pmfProb pmfExp
  calc
    ∑ a : α, (μ a).toReal *
        (if ∃ i, i ∈ s ∧ p i a then (1 : ℝ) else 0) ≤
        ∑ a : α, (μ a).toReal *
          (∑ i ∈ s, (if p i a then (1 : ℝ) else 0)) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          exact mul_le_mul_of_nonneg_left (hpoint a) ENNReal.toReal_nonneg
    _ = ∑ a : α, ∑ i ∈ s,
          (μ a).toReal * (if p i a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ a : α,
          (μ a).toReal * (if p i a then (1 : ℝ) else 0) := by
          exact Finset.sum_comm

/--
Finite union bound with a uniform per-event upper bound over a finite index
type.
-/
theorem pmfProb_exists_le_card_mul {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (μ : PMF α) (p : ι → α → Prop)
    [DecidablePred fun a => ∃ i, p i a]
    [∀ i, DecidablePred (p i)]
    (eps : ℝ)
    (hprob : ∀ i, pmfProb μ (p i) ≤ eps) :
    pmfProb μ (fun a => ∃ i, p i a) ≤
      (Fintype.card ι : ℝ) * eps := by
  classical
  have hunion :=
    pmfProb_exists_mem_le_sum
      (μ := μ) (s := (Finset.univ : Finset ι)) (p := p)
  calc
    pmfProb μ (fun a => ∃ i, p i a) =
        pmfProb μ
          (fun a => ∃ i, i ∈ (Finset.univ : Finset ι) ∧ p i a) := by
          unfold pmfProb
          refine pmfExp_congr μ ?_
          intro a
          by_cases h : ∃ i, p i a <;> simp [h]
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), pmfProb μ (p i) := hunion
    _ ≤ ∑ _i ∈ (Finset.univ : Finset ι), eps := by
          exact Finset.sum_le_sum (by
            intro i _hi
            exact hprob i)
    _ = (Fintype.card ι : ℝ) * eps := by
          simp [nsmul_eq_mul]

@[simp] theorem pmfProb_false {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    pmfProb μ (fun _ => False) = 0 := by
  simp [pmfProb]

/--
Compare finite probability deltas from a pointwise comparison of indicator
differences.
-/
theorem pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α)
    (p q r s : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s]
    (h : ∀ a,
      (if p a then (1 : ℝ) else 0) - (if q a then (1 : ℝ) else 0) ≤
        (if r a then (1 : ℝ) else 0) - (if s a then (1 : ℝ) else 0)) :
    pmfProb μ p - pmfProb μ q ≤ pmfProb μ r - pmfProb μ s := by
  classical
  unfold pmfProb
  rw [← pmfExp_sub, ← pmfExp_sub]
  exact pmfExp_le_pmfExp_of_forall_le μ
    (fun a =>
      (if p a then (1 : ℝ) else 0) - (if q a then (1 : ℝ) else 0))
    (fun a =>
      (if r a then (1 : ℝ) else 0) - (if s a then (1 : ℝ) else 0))
    h

/--
If `p` is included in `q`, then `q` splits into `p` plus the finite residual
event `q ∧ ¬p`.
-/
theorem pmfProb_eq_add_diff_of_imp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) :
    pmfProb μ q = pmfProb μ p + pmfProb μ (fun a => q a ∧ ¬p a) := by
  classical
  unfold pmfProb
  rw [← pmfExp_add]
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a
  · have hq : q a := himp a hp
    simp [hp, hq]
  · by_cases hq : q a <;> simp [hp, hq]

/--
Strict finite probability monotonicity from event inclusion plus positive mass
in the residual event.
-/
theorem pmfProb_lt_of_imp_of_mass {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) (a₀ : α)
    (hq : q a₀) (hp : ¬p a₀) (hmass : 0 < (μ a₀).toReal) :
    pmfProb μ p < pmfProb μ q := by
  classical
  have hres :
      0 < pmfProb μ (fun a => q a ∧ ¬p a) :=
    pmfProb_pos_of_mass μ (fun a => q a ∧ ¬p a) a₀ ⟨hq, hp⟩ hmass
  have hsplit := pmfProb_eq_add_diff_of_imp μ p q himp
  rw [hsplit]
  linarith

/-- Split an event by whether a second event also holds. -/
theorem pmfProb_eq_inter_add_inter_not
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfProb μ p =
      pmfProb μ (fun a => p a ∧ q a) +
        pmfProb μ (fun a => p a ∧ ¬ q a) := by
  classical
  unfold pmfProb
  rw [← pmfExp_add]
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a
  · by_cases hq : q a <;> simp [hp, hq]
  · simp [hp]

/-- For disjoint finite-PMF events, the probability of their union is the sum. -/
theorem pmfProb_or_eq_add_of_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hdisjoint : ∀ a, p a → q a → False) :
    pmfProb μ (fun a => p a ∨ q a) =
      pmfProb μ p + pmfProb μ q := by
  classical
  rw [pmfProb_eq_inter_add_inter_not μ (fun a => p a ∨ q a) p]
  have hleft :
      pmfProb μ (fun a => (p a ∨ q a) ∧ p a) =
        pmfProb μ p :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        exact h.2
      · intro hp
        exact ⟨Or.inl hp, hp⟩)
  have hright :
      pmfProb μ (fun a => (p a ∨ q a) ∧ ¬ p a) =
        pmfProb μ q :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        rcases h.1 with hp | hq
        · exact False.elim (h.2 hp)
        · exact hq
      · intro hq
        exact ⟨Or.inr hq, fun hp => hdisjoint a hp hq⟩)
  rw [hleft, hright]

/-- Inclusion-exclusion for two finite-PMF events. -/
theorem pmfProb_or_eq_add_sub_inter
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfProb μ (fun a => p a ∨ q a) =
      pmfProb μ p + pmfProb μ q -
        pmfProb μ (fun a => p a ∧ q a) := by
  classical
  have hor_split :=
    pmfProb_eq_inter_add_inter_not μ (fun a => p a ∨ q a) p
  have hq_split := pmfProb_eq_inter_add_inter_not μ q p
  have hleft :
      pmfProb μ (fun a => (p a ∨ q a) ∧ p a) =
        pmfProb μ p :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        exact h.2
      · intro hp
        exact ⟨Or.inl hp, hp⟩)
  have hright :
      pmfProb μ (fun a => (p a ∨ q a) ∧ ¬ p a) =
        pmfProb μ (fun a => q a ∧ ¬ p a) :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        rcases h.1 with hp | hq
        · exact False.elim (h.2 hp)
        · exact ⟨hq, h.2⟩
      · intro h
        exact ⟨Or.inr h.1, h.2⟩)
  have hpq_comm :
      pmfProb μ (fun a => q a ∧ p a) =
        pmfProb μ (fun a => p a ∧ q a) :=
    pmfProb_congr μ (by intro a; constructor <;> intro h <;> exact ⟨h.2, h.1⟩)
  rw [hor_split, hleft, hright]
  rw [hq_split, hpq_comm]
  ring

/-- Finite-PMF union bound for two events. -/
theorem pmfProb_or_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfProb μ (fun a => p a ∨ q a) ≤ pmfProb μ p + pmfProb μ q := by
  rw [pmfProb_or_eq_add_sub_inter]
  exact sub_le_self _ (pmfProb_nonneg μ (fun a => p a ∧ q a))

/--
For disjoint finite-PMF events, the probability that neither occurs is
`1 - P(p) - P(q)`.
-/
theorem pmfProb_not_and_not_eq_one_sub_add_of_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hdisjoint : ∀ a, p a → q a → False) :
    pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
      1 - pmfProb μ p - pmfProb μ q := by
  classical
  calc
    pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
        pmfProb μ (fun a => ¬ (p a ∨ q a)) := by
          exact pmfProb_congr μ (by intro a; tauto)
    _ = 1 - pmfProb μ (fun a => p a ∨ q a) := by
          rw [pmfProb_compl]
    _ = 1 - (pmfProb μ p + pmfProb μ q) := by
          rw [pmfProb_or_eq_add_of_disjoint μ p q hdisjoint]
    _ = 1 - pmfProb μ p - pmfProb μ q := by ring

/-- Complementing both events preserves a finite-PMF negative-correlation bound. -/
theorem pmfProb_not_and_not_le_mul_of_inter_le_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hinter : pmfProb μ (fun a => p a ∧ q a) ≤
      pmfProb μ p * pmfProb μ q) :
    pmfProb μ (fun a => ¬ p a ∧ ¬ q a) ≤
      pmfProb μ (fun a => ¬ p a) *
        pmfProb μ (fun a => ¬ q a) := by
  classical
  have hnotnot :
      pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
        1 - pmfProb μ p - pmfProb μ q +
          pmfProb μ (fun a => p a ∧ q a) := by
    calc
      pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
          pmfProb μ (fun a => ¬ (p a ∨ q a)) := by
            exact pmfProb_congr μ (by intro a; tauto)
      _ = 1 - pmfProb μ (fun a => p a ∨ q a) := by
            rw [pmfProb_compl]
      _ =
          1 - (pmfProb μ p + pmfProb μ q -
            pmfProb μ (fun a => p a ∧ q a)) := by
            rw [pmfProb_or_eq_add_sub_inter]
      _ =
          1 - pmfProb μ p - pmfProb μ q +
            pmfProb μ (fun a => p a ∧ q a) := by ring
  rw [hnotnot, pmfProb_compl, pmfProb_compl]
  nlinarith

/--
Finite union-bound lower-tail form: if two events each hold with probability at
least `1 - eps`, then their intersection holds with probability at least
`1 - epsP - epsQ`.
-/
theorem pmfProb_inter_ge_one_sub_add
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    {epsP epsQ : ℝ}
    (hp : 1 - epsP ≤ pmfProb μ p)
    (hq : 1 - epsQ ≤ pmfProb μ q) :
    1 - epsP - epsQ ≤ pmfProb μ (fun a => p a ∧ q a) := by
  classical
  have hsplit := pmfProb_eq_inter_add_inter_not μ p q
  have hres_le_notq :
      pmfProb μ (fun a => p a ∧ ¬ q a) ≤ pmfProb μ (fun a => ¬ q a) :=
    pmfProb_le_of_imp μ (fun a => p a ∧ ¬ q a) (fun a => ¬ q a)
      (by intro a ha; exact ha.2)
  have hnotq_eq := pmfProb_compl μ q
  have hnotq_le : pmfProb μ (fun a => ¬ q a) ≤ epsQ := by
    linarith
  have hres_le : pmfProb μ (fun a => p a ∧ ¬ q a) ≤ epsQ :=
    le_trans hres_le_notq hnotq_le
  linarith

/--
Finite change-of-variables bound for probabilities.

If an equivalence maps every point of event `p` into event `q`, and the target
atom has at least as much mass as the source atom on `p`, then `Pr[p] ≤ Pr[q]`.
This is the finite analogue of the injection/change-of-variables step in many
coupling proofs.
-/
theorem pmfProb_le_of_equiv_event_mass_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a → q (e a))
    (hmass : ∀ a, p a → (μ a).toReal ≤ (μ (e a)).toReal) :
    pmfProb μ p ≤ pmfProb μ q := by
  classical
  unfold pmfProb pmfExp
  have hleft :
      (∑ a : α, (μ a).toReal * if p a then (1 : ℝ) else 0) =
        ∑ a : α, if p a then (μ a).toReal else 0 := by
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases hp : p a <;> simp [hp]
  have hright :
      (∑ a : α, (μ a).toReal * if q a then (1 : ℝ) else 0) =
        ∑ a : α, if q a then (μ a).toReal else 0 := by
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases hq : q a <;> simp [hq]
  rw [hleft, hright]
  calc
    ∑ a : α, (if p a then (μ a).toReal else 0)
        ≤ ∑ a : α, (if p a then (μ (e a)).toReal else 0) := by
          refine Finset.sum_le_sum ?_
          intro a _
          by_cases hp : p a
          · exact by simpa [hp] using hmass a hp
          · simp [hp]
    _ = ∑ a : α, (if p (e.symm a) then (μ a).toReal else 0) := by
          simpa using
            (Equiv.sum_comp e
              (fun a : α => if p (e.symm a) then (μ a).toReal else 0))
    _ ≤ ∑ a : α, (if q a then (μ a).toReal else 0) := by
          refine Finset.sum_le_sum ?_
          intro a _
          by_cases hp : p (e.symm a)
          · have hq : q a := by
              simpa using hmap (e.symm a) hp
            simp [hp, hq]
          · by_cases hq : q a
            · simp [hp, hq, ENNReal.toReal_nonneg]
            · simp [hp, hq]

/--
Strict finite change-of-variables bound for probabilities.

If an equivalence maps every point of event `p` into event `q`, the target atom
has at least as much mass as the source atom on `p`, and one source event atom
has strictly smaller mass than its image, then `Pr[p] < Pr[q]`.
-/
theorem pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a → q (e a))
    (hmass : ∀ a, p a → (μ a).toReal ≤ (μ (e a)).toReal)
    {a₀ : α} (hp₀ : p a₀)
    (hstrict : (μ a₀).toReal < (μ (e a₀)).toReal) :
    pmfProb μ p < pmfProb μ q := by
  classical
  have himage :
      pmfProb μ (fun a => p (e.symm a)) ≤ pmfProb μ q := by
    refine pmfProb_le_of_imp μ (fun a => p (e.symm a)) q ?_
    intro a hp
    simpa using hmap (e.symm a) hp
  have hstrict_image :
      pmfProb μ p < pmfProb μ (fun a => p (e.symm a)) := by
    unfold pmfProb pmfExp
    have hleft :
        (∑ a : α, (μ a).toReal * if p a then (1 : ℝ) else 0) =
          ∑ a : α, if p a then (μ a).toReal else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p a <;> simp [hp]
    have hright :
        (∑ a : α, (μ a).toReal *
            if p (e.symm a) then (1 : ℝ) else 0) =
          ∑ a : α, if p (e.symm a) then (μ a).toReal else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p (e.symm a) <;> simp [hp]
    rw [hleft, hright]
    calc
      ∑ a : α, (if p a then (μ a).toReal else 0)
          < ∑ a : α, (if p a then (μ (e a)).toReal else 0) := by
            refine Finset.sum_lt_sum ?hle ?hlt
            · intro a _
              by_cases hp : p a
              · exact by simpa [hp] using hmass a hp
              · simp [hp]
            · exact ⟨a₀, Finset.mem_univ a₀, by simpa [hp₀] using hstrict⟩
      _ = ∑ a : α, (if p (e.symm a) then (μ a).toReal else 0) := by
            simpa using
              (Equiv.sum_comp e
              (fun a : α => if p (e.symm a) then (μ a).toReal else 0))
  exact lt_of_lt_of_le hstrict_image himage

/--
Finite cross-event change-of-variables bound.

To prove `Pr[p] ≤ Pr[q]`, it is enough to map only the asymmetric part
`p ∧ ¬q` into `q ∧ ¬p` with nondecreasing mass.  The common part
`p ∧ q` cancels on both sides.
-/
theorem pmfProb_le_of_cross_event_equiv_mass_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a ∧ ¬ q a → q (e a) ∧ ¬ p (e a))
    (hmass : ∀ a, p a ∧ ¬ q a → (μ a).toReal ≤ (μ (e a)).toReal) :
    pmfProb μ p ≤ pmfProb μ q := by
  classical
  have hle := pmfProb_le_of_equiv_event_mass_le μ e
    (fun a => p a ∧ ¬ q a) (fun a => q a ∧ ¬ p a) hmap hmass
  have hp := pmfProb_eq_inter_add_inter_not μ p q
  have hq := pmfProb_eq_inter_add_inter_not μ q p
  have hpq_comm :
      pmfProb μ (fun a => q a ∧ p a) =
        pmfProb μ (fun a => p a ∧ q a) := by
    unfold pmfProb
    refine pmfExp_congr μ ?_
    intro a
    by_cases hp' : p a <;> by_cases hq' : q a <;> simp [hp', hq']
  rw [hp, hq, hpq_comm]
  linarith

/--
Strict finite cross-event change-of-variables bound.

If the asymmetric part `p ∧ ¬q` maps into `q ∧ ¬p`, mass never decreases there,
and one source atom strictly increases, then `Pr[p] < Pr[q]`.
-/
theorem pmfProb_lt_of_cross_event_equiv_mass_le_of_exists_strict
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a ∧ ¬ q a → q (e a) ∧ ¬ p (e a))
    (hmass : ∀ a, p a ∧ ¬ q a → (μ a).toReal ≤ (μ (e a)).toReal)
    {a₀ : α} (hpq₀ : p a₀ ∧ ¬ q a₀)
    (hstrict : (μ a₀).toReal < (μ (e a₀)).toReal) :
    pmfProb μ p < pmfProb μ q := by
  classical
  have hlt := pmfProb_lt_of_equiv_event_mass_le_of_exists_strict μ e
    (fun a => p a ∧ ¬ q a) (fun a => q a ∧ ¬ p a)
    hmap hmass hpq₀ hstrict
  have hp := pmfProb_eq_inter_add_inter_not μ p q
  have hq := pmfProb_eq_inter_add_inter_not μ q p
  have hpq_comm :
      pmfProb μ (fun a => q a ∧ p a) =
        pmfProb μ (fun a => p a ∧ q a) := by
    unfold pmfProb
    refine pmfExp_congr μ ?_
    intro a
    by_cases hp' : p a <;> by_cases hq' : q a <;> simp [hp', hq']
  rw [hp, hq, hpq_comm]
  linarith

/-- Finite sums commute with finite PMF expectation. -/
theorem pmfExp_finset_sum {α ι : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (s : Finset ι) (f : ι → α → ℝ) :
    pmfExp μ (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, pmfExp μ (f i) := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (∑ i ∈ s, f i a)
        = ∑ a : α, ∑ i ∈ s, (μ a).toReal * f i a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ a : α, (μ a).toReal * f i a := by
          exact Finset.sum_comm

/-- Increment from rating `k` to rating `k + 1`, with a harmless zero value
outside the intended range. -/
private noncomputable def finTailCoeff {n : ℕ}
    (score : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then
    score ⟨k + 1, Nat.succ_lt_succ hk⟩ -
      score ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n)⟩
  else 0

/-- The `k + 1` upper-tail threshold, with a harmless bottom value outside the
intended range. -/
private def finTailThreshold {n : ℕ} (k : ℕ) : Fin (n + 1) :=
  if hk : k < n then ⟨k + 1, Nat.succ_lt_succ hk⟩ else 0

private theorem finTailCoeff_of_lt {n : ℕ} (score : Fin (n + 1) → ℝ)
    {k : ℕ} (hk : k < n) :
    finTailCoeff score k =
      score ⟨k + 1, Nat.succ_lt_succ hk⟩ -
        score ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n)⟩ := by
  simp [finTailCoeff, hk]

private theorem finTailThreshold_of_lt {n : ℕ} {k : ℕ} (hk : k < n) :
    finTailThreshold (n := n) k = ⟨k + 1, Nat.succ_lt_succ hk⟩ := by
  simp [finTailThreshold, hk]

/-- Pointwise telescoping decomposition of an increasing ordinal score on
`Fin (n + 1)` into upper-tail indicators. -/
private theorem fin_tail_score_eq_score_zero_add_sum {n : ℕ}
    (score : Fin (n + 1) → ℝ) (r : Fin (n + 1)) :
    score r =
      score 0 + ∑ k ∈ Finset.range n,
        if k < r.val then finTailCoeff score k else 0 := by
  let fNat : ℕ → ℝ := fun k =>
    if hk : k < n + 1 then score ⟨k, hk⟩ else 0
  have htel := Finset.sum_range_sub fNat r.val
  have hr_le_n : r.val ≤ n := Nat.lt_succ_iff.mp r.isLt
  have hfilter :
      (Finset.range n).filter (fun k => k < r.val) = Finset.range r.val := by
    ext k
    constructor
    · intro hk
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
    · intro hk
      have hk_lt_r : k < r.val := Finset.mem_range.mp hk
      have hk_lt_n : k < n := Nat.lt_of_lt_of_le hk_lt_r hr_le_n
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt_n, hk_lt_r⟩
  have hsum_filter :
      (∑ k ∈ Finset.range n, if k < r.val then finTailCoeff score k else 0) =
        ∑ k ∈ Finset.range r.val, finTailCoeff score k := by
    calc
      (∑ k ∈ Finset.range n, if k < r.val then finTailCoeff score k else 0)
          = ∑ k ∈ (Finset.range n).filter (fun k => k < r.val),
              finTailCoeff score k := by
            rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range r.val, finTailCoeff score k := by
            rw [hfilter]
  have hcoeff_sum :
      (∑ k ∈ Finset.range r.val, finTailCoeff score k) =
        ∑ k ∈ Finset.range r.val, (fNat (k + 1) - fNat k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_lt_r : k < r.val := Finset.mem_range.mp hk
    have hk_lt_n : k < n := Nat.lt_of_lt_of_le hk_lt_r hr_le_n
    have hk_succ_lt : k + 1 < n + 1 := Nat.succ_lt_succ hk_lt_n
    have hk_lt_succ : k < n + 1 := Nat.lt_trans hk_lt_n (Nat.lt_succ_self n)
    rw [finTailCoeff_of_lt score hk_lt_n]
    dsimp [fNat]
    rw [dif_pos hk_succ_lt, dif_pos hk_lt_succ]
  have hr_f : fNat r.val = score r := by
    dsimp [fNat]
    simp [r.isLt]
  have hzero_f : fNat 0 = score 0 := by
    simp [fNat]
  have hsum_eq :
      (∑ k ∈ Finset.range n, if k < r.val then finTailCoeff score k else 0) =
        score r - score 0 := by
    rw [hsum_filter, hcoeff_sum, htel, hr_f, hzero_f]
  linarith

/-- Finite ordinal expectation as a base score plus increments weighted by
upper-tail probabilities. -/
private theorem pmfExp_fin_tail_decomposition {n : ℕ}
    (μ : PMF (Fin (n + 1))) (score : Fin (n + 1) → ℝ) :
    pmfExp μ score =
      score 0 + ∑ k ∈ Finset.range n,
        finTailCoeff score k *
          pmfProb μ (fun r : Fin (n + 1) =>
            finTailThreshold (n := n) k ≤ r) := by
  classical
  calc
    pmfExp μ score =
        pmfExp μ (fun r : Fin (n + 1) =>
          score 0 + ∑ k ∈ Finset.range n,
            if k < r.val then finTailCoeff score k else 0) := by
          refine pmfExp_congr μ ?_
          intro r
          exact fin_tail_score_eq_score_zero_add_sum score r
    _ = score 0 +
        pmfExp μ (fun r : Fin (n + 1) =>
          ∑ k ∈ Finset.range n,
            if k < r.val then finTailCoeff score k else 0) := by
          rw [pmfExp_add, pmfExp_const]
    _ = score 0 + ∑ k ∈ Finset.range n,
        pmfExp μ (fun r : Fin (n + 1) =>
          if k < r.val then finTailCoeff score k else 0) := by
          rw [pmfExp_finset_sum]
    _ = score 0 + ∑ k ∈ Finset.range n,
        finTailCoeff score k *
          pmfProb μ (fun r : Fin (n + 1) =>
            finTailThreshold (n := n) k ≤ r) := by
          refine congrArg (fun x => score 0 + x) ?_
          refine Finset.sum_congr rfl ?_
          intro k hk_mem
          have hk : k < n := Finset.mem_range.mp hk_mem
          have hthreshold :
              finTailThreshold (n := n) k =
                (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (n + 1)) :=
            finTailThreshold_of_lt hk
          calc
            pmfExp μ (fun r : Fin (n + 1) =>
                if k < r.val then finTailCoeff score k else 0)
                =
                pmfExp μ (fun r : Fin (n + 1) =>
                  finTailCoeff score k *
                    (if finTailThreshold (n := n) k ≤ r then (1 : ℝ) else 0)) := by
                  refine pmfExp_congr μ ?_
                  intro r
                  have hevent :
                      (finTailThreshold (n := n) k ≤ r) ↔ k < r.val := by
                    rw [hthreshold]
                    change k + 1 ≤ r.val ↔ k < r.val
                    exact Nat.succ_le_iff
                  by_cases hkr : k < r.val
                  · have htail : finTailThreshold (n := n) k ≤ r := hevent.2 hkr
                    simp [hkr, htail]
                  · have htail : ¬ finTailThreshold (n := n) k ≤ r :=
                      fun hle => hkr (hevent.1 hle)
                    simp [hkr, htail]
            _ = finTailCoeff score k *
                pmfProb μ (fun r : Fin (n + 1) =>
                  finTailThreshold (n := n) k ≤ r) := by
                  rw [pmfExp_const_mul]
                  rfl

private theorem finTailCoeff_nonneg_of_monotone {n : ℕ}
    {score : Fin (n + 1) → ℝ} (hmono : Monotone score)
    {k : ℕ} (hk : k < n) :
    0 ≤ finTailCoeff score k := by
  rw [finTailCoeff_of_lt score hk]
  have hle :
      score ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n)⟩ ≤
        score ⟨k + 1, Nat.succ_lt_succ hk⟩ := by
    apply hmono
    change k ≤ k + 1
    exact Nat.le_succ k
  linarith

/--
Finite first-order stochastic dominance for ordinal ratings.  If every
upper-tail probability under `lo` is bounded by the corresponding upper-tail
probability under `hi`, then every monotone real score has weakly smaller
finite expectation under `lo`.
-/
theorem pmfExp_le_pmfExp_of_fin_tail_prob_le
    {m : ℕ} (lo hi : PMF (Fin m)) (score : Fin m → ℝ)
    (hmono : Monotone score)
    (htail : ∀ t : Fin m,
      pmfProb lo (fun r => t ≤ r) ≤ pmfProb hi (fun r => t ≤ r)) :
    pmfExp lo score ≤ pmfExp hi score := by
  classical
  cases m with
  | zero =>
      have hmass := pmfToRealSum lo
      simp at hmass
  | succ n =>
      rw [pmfExp_fin_tail_decomposition lo score,
        pmfExp_fin_tail_decomposition hi score]
      have hsum :
          (∑ k ∈ Finset.range n,
              finTailCoeff score k *
                pmfProb lo (fun r : Fin (n + 1) =>
                  finTailThreshold (n := n) k ≤ r)) ≤
            ∑ k ∈ Finset.range n,
              finTailCoeff score k *
                pmfProb hi (fun r : Fin (n + 1) =>
                  finTailThreshold (n := n) k ≤ r) := by
        refine Finset.sum_le_sum ?_
        intro k hk_mem
        have hk : k < n := Finset.mem_range.mp hk_mem
        exact mul_le_mul_of_nonneg_left
          (htail (finTailThreshold (n := n) k))
          (finTailCoeff_nonneg_of_monotone hmono hk)
      simpa [add_comm] using add_le_add_left hsum (score 0)

/--
The capped function `min 1` is expectation-subadditive in the only form needed
for finite allocation caps: the expectation of a capped random variable is at
most the cap of its expectation.
-/
theorem pmfExp_min_one_le_min_one_pmfExp {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfExp μ (fun a => min 1 (f a)) ≤ min 1 (pmfExp μ f) := by
  refine le_min ?_ ?_
  · exact pmfExp_le_of_forall_le μ (fun a => min 1 (f a)) 1
      (fun a => min_le_left 1 (f a))
  · unfold pmfExp
    exact Finset.sum_le_sum (by
      intro a _
      exact mul_le_mul_of_nonneg_left (min_le_right 1 (f a))
        ENNReal.toReal_nonneg)

/-- Finite PMF expectation bounded by a tail decomposition of a `[0,1]`-valued
function. -/
theorem pmfExp_le_of_nonneg_le_one_of_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (t : ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_le_one : ∀ a, f a ≤ 1) (ht : 0 ≤ t) :
    pmfExp μ f ≤ t + pmfProb μ (fun a => t < f a) := by
  have hpoint : ∀ a, f a ≤ (if t < f a then (1 : ℝ) else 0) + t := by
    intro a
    by_cases hlt : t < f a
    · have hle : f a ≤ t + 1 := by
        nlinarith [h_le_one a, ht]
      have hle' : f a ≤ 1 + t := by
        simpa [add_comm] using hle
      simpa [hlt] using hle'
    · have hle : f a ≤ t := le_of_not_gt hlt
      simpa [hlt] using hle
  have hbound :
      pmfExp μ f ≤ pmfExp μ (fun a => (if t < f a then (1 : ℝ) else 0) + t) :=
    pmfExp_le_pmfExp_of_forall_le μ f
      (fun a => (if t < f a then (1 : ℝ) else 0) + t) hpoint
  calc
    pmfExp μ f ≤ pmfExp μ (fun a => (if t < f a then (1 : ℝ) else 0) + t) := hbound
    _ = pmfExp μ (fun a => if t < f a then (1 : ℝ) else 0) +
          pmfExp μ (fun _ : α => t) := by
        simpa using
          (pmfExp_add (μ := μ) (f := fun a => if t < f a then (1 : ℝ) else 0)
            (g := fun _ : α => t))
    _ = t + pmfProb μ (fun a => t < f a) := by
        simp [pmfProb, add_comm]

/-- Finite PMF expectation lower bound from upper-tail mass for nonnegative
functions. -/
theorem pmfExp_ge_of_nonneg_of_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (t : ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (ht : 0 ≤ t) :
    t * pmfProb μ (fun a => t < f a) ≤ pmfExp μ f := by
  have hpoint : ∀ a, t * (if t < f a then (1 : ℝ) else 0) ≤ f a := by
    intro a
    by_cases hlt : t < f a
    · have hle : t ≤ f a := le_of_lt hlt
      simpa [hlt] using hle
    · have hzero : (if t < f a then (1 : ℝ) else 0) = 0 := by simp [hlt]
      simp [hzero, h_nonneg a]
  have hbound : pmfExp μ (fun a => t * (if t < f a then (1 : ℝ) else 0)) ≤ pmfExp μ f :=
    pmfExp_le_pmfExp_of_forall_le μ
      (fun a => t * (if t < f a then (1 : ℝ) else 0)) f hpoint
  have hleft :
      pmfExp μ (fun a => t * (if t < f a then (1 : ℝ) else 0)) =
        t * pmfProb μ (fun a => t < f a) := by
    rw [pmfExp_const_mul, pmfProb]
  calc
    t * pmfProb μ (fun a => t < f a) = pmfExp μ (fun a => t * (if t < f a then (1 : ℝ) else 0)) := hleft.symm
    _ ≤ pmfExp μ f := hbound

/-- Direct concentration-style upper bound for finite expectations. -/
theorem pmfExp_le_of_tail_prob_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (t : ℝ) (eps : ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_le_one : ∀ a, f a ≤ 1) (ht : 0 ≤ t)
    (h_tail : pmfProb μ (fun a => t < f a) ≤ eps) :
    pmfExp μ f ≤ t + eps := by
  calc
    pmfExp μ f ≤ t + pmfProb μ (fun a => t < f a) :=
      pmfExp_le_of_nonneg_le_one_of_tail μ f t h_nonneg h_le_one ht
    _ ≤ t + eps := by
      have htail' : pmfProb μ (fun a => t < f a) + t ≤ eps + t := by
        exact add_le_add_left h_tail t
      simpa [add_comm] using htail'

/-- A finite PMF expectation is strictly above a constant if every value is. -/
theorem pmfExp_lt_of_forall_lt {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, c < f a) :
    c < pmfExp μ f := by
  classical
  have hpos_atom : ∃ a : α, 0 < (μ a).toReal := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a : α, (μ a).toReal = 0 := by
      intro a
      exact le_antisymm (hnone a) ENNReal.toReal_nonneg
    have hsum_zero : ∑ a : α, (μ a).toReal = 0 := by
      simp [hzero]
    have hsum_one : ∑ a : α, (μ a).toReal = 1 := pmfToRealSum μ
    linarith
  rw [← pmfExp_const μ c]
  unfold pmfExp
  refine Finset.sum_lt_sum ?_ ?_
  · intro a _
    exact mul_le_mul_of_nonneg_left (le_of_lt (h a)) ENNReal.toReal_nonneg
  · rcases hpos_atom with ⟨a, ha⟩
    exact ⟨a, Finset.mem_univ a,
      mul_lt_mul_of_pos_left (h a) ha⟩

/--
A finite PMF expectation is strictly below a constant if every atom is at most
that constant and one positive-mass atom is strictly below it.
-/
theorem pmfExp_lt_of_forall_le_exists_lt {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (hle : ∀ a, f a ≤ c)
    (hex : ∃ a, 0 < (μ a).toReal ∧ f a < c) :
    pmfExp μ f < c := by
  classical
  rw [← pmfExp_const μ c]
  unfold pmfExp
  refine Finset.sum_lt_sum ?_ ?_
  · intro a _
    exact mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg
  · rcases hex with ⟨a, hmass, hlt⟩
    exact ⟨a, Finset.mem_univ a,
      mul_lt_mul_of_pos_left hlt hmass⟩

/--
A finite PMF expectation is strictly below a constant when every positive-mass
atom is at most that constant and one positive-mass atom is strictly below it.
Zero-mass atoms may have arbitrary values.
-/
theorem pmfExp_lt_of_support_forall_le_exists_lt {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (hle : ∀ a, 0 < (μ a).toReal → f a ≤ c)
    (hex : ∃ a, 0 < (μ a).toReal ∧ f a < c) :
    pmfExp μ f < c := by
  classical
  let supportValue : α → ℝ :=
    fun a => if (μ a).toReal = 0 then c else f a
  have hExpEq : pmfExp μ f = pmfExp μ supportValue := by
    unfold pmfExp supportValue
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hzero : (μ a).toReal = 0
    · simp [hzero]
    · simp [hzero]
  have hsupport_le : ∀ a, supportValue a ≤ c := by
    intro a
    by_cases hzero : (μ a).toReal = 0
    · simp [supportValue, hzero]
    · have hmass : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      simpa [supportValue, hzero] using hle a hmass
  have hsupport_lt : ∃ a, 0 < (μ a).toReal ∧ supportValue a < c := by
    rcases hex with ⟨a, hmass, hlt⟩
    have hzero : (μ a).toReal ≠ 0 := ne_of_gt hmass
    exact ⟨a, hmass, by simpa [supportValue, hzero] using hlt⟩
  rw [hExpEq]
  exact pmfExp_lt_of_forall_le_exists_lt μ supportValue c
    hsupport_le hsupport_lt

/--
A finite PMF expectation is strictly below a constant when every positive-mass
atom is strictly below that constant. Zero-mass atoms may have arbitrary values.
-/
theorem pmfExp_lt_of_support_forall_lt {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, 0 < (μ a).toReal → f a < c) :
    pmfExp μ f < c := by
  classical
  let g : α → ℝ := fun a => if (μ a).toReal = 0 then c else f a
  have hfg : pmfExp μ f = pmfExp μ g := by
    unfold pmfExp g
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hzero : (μ a).toReal = 0
    · simp [hzero]
    · simp [hzero]
  have hle : ∀ a, g a ≤ c := by
    intro a
    by_cases hzero : (μ a).toReal = 0
    · simp [g, hzero]
    · have hpos : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      exact le_of_lt (by simpa [g, hzero] using h a hpos)
  have hex : ∃ a, 0 < (μ a).toReal ∧ g a < c := by
    by_contra hnone
    push Not at hnone
    have hzero_all : ∀ a, (μ a).toReal = 0 := by
      intro a
      by_contra hzero
      have hpos : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      exact (not_lt_of_ge (hnone a hpos)) (by
        simpa [g, hzero] using h a hpos)
    have hsum_zero : ∑ a : α, (μ a).toReal = 0 := by
      simp [hzero_all]
    have hsum_one : ∑ a : α, (μ a).toReal = 1 := pmfToRealSum μ
    linarith
  rw [hfg]
  exact pmfExp_lt_of_forall_le_exists_lt μ g c hle hex

theorem abs_pmfExp_sub_le_sum_abs_atom_mul {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ ν : PMF α) (f : α → ℝ) :
    |pmfExp μ f - pmfExp ν f| ≤
      ∑ a : α, |(μ a).toReal - (ν a).toReal| * |f a| := by
  classical
  unfold pmfExp
  calc
    |(∑ a : α, (μ a).toReal * f a) -
        ∑ a : α, (ν a).toReal * f a|
        = |∑ a : α, ((μ a).toReal - (ν a).toReal) * f a| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ ≤ ∑ a : α, |((μ a).toReal - (ν a).toReal) * f a| :=
        Finset.abs_sum_le_sum_abs
          (fun a : α => ((μ a).toReal - (ν a).toReal) * f a) Finset.univ
    _ = ∑ a : α, |(μ a).toReal - (ν a).toReal| * |f a| := by
        simp [abs_mul]

theorem exists_atomwise_radius_pmfExp_close {α : Type*}
    [Fintype α] [DecidableEq α]
    (ν : PMF α) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ μ : PMF α,
        (∀ a : α, |(μ a).toReal - (ν a).toReal| < δ) →
          |pmfExp μ f - pmfExp ν f| < ε := by
  classical
  let S : ℝ := ∑ a : α, |f a|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun a _ => abs_nonneg (f a))
  refine ⟨ε / (S + 1), div_pos hε (by linarith), ?_⟩
  intro μ hμ
  have hbound :
      ∑ a : α, |(μ a).toReal - (ν a).toReal| * |f a| ≤
        (ε / (S + 1)) * S := by
    calc
      ∑ a : α, |(μ a).toReal - (ν a).toReal| * |f a|
          ≤ ∑ a : α, (ε / (S + 1)) * |f a| := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact mul_le_mul_of_nonneg_right (le_of_lt (hμ a)) (abs_nonneg (f a))
      _ = (ε / (S + 1)) * S := by
            dsimp [S]
            rw [Finset.mul_sum]
  have hstrict : (ε / (S + 1)) * S < ε := by
    have hden_pos : 0 < S + 1 := by linarith
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hden_pos).2 (by nlinarith)
  exact lt_of_le_of_lt
    ((abs_pmfExp_sub_le_sum_abs_atom_mul μ ν f).trans hbound)
    hstrict

@[simp] theorem pmfExp_pure {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℝ) :
    pmfExp (PMF.pure a) f = f a := by
  classical
  unfold pmfExp
  calc
    ∑ x : α, (PMF.pure a x).toReal * f x = ∑ x : α, if x = a then f a else 0 := by
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x = a
      · subst h
        simp [PMF.pure_apply]
      · simp [PMF.pure_apply, h]
    _ = f a := by
      simp

/--
Every finite PMF has a positive-mass atom whose value is weakly below the
expectation.
-/
theorem exists_support_value_le_pmfExp
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : PMF α) (f : α → ℝ) :
    ∃ a, 0 < (μ a).toReal ∧ f a ≤ pmfExp μ f := by
  classical
  by_contra hnone
  have hsupport_gt :
      ∀ a, 0 < (μ a).toReal → pmfExp μ f < f a := by
    intro a hmass
    have hnot : ¬ f a ≤ pmfExp μ f := by
      intro hle
      exact hnone ⟨a, hmass, hle⟩
    exact lt_of_not_ge hnot
  let supportValue : α → ℝ :=
    fun a =>
      if (μ a).toReal = 0 then
        pmfExp μ f + 1
      else f a
  have hExpEq : pmfExp μ f = pmfExp μ supportValue := by
    unfold pmfExp supportValue
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hzero : (μ a).toReal = 0
    · simp [hzero]
    · simp [hzero]
  have hall_gt : ∀ a, pmfExp μ f < supportValue a := by
    intro a
    by_cases hzero : (μ a).toReal = 0
    · simp [supportValue, hzero]
    · have hmass : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      simpa [supportValue, hzero] using hsupport_gt a hmass
  have hlt : pmfExp μ f < pmfExp μ f :=
    hExpEq ▸ (pmfExp_lt_of_forall_lt μ supportValue (pmfExp μ f) hall_gt)
  exact (lt_irrefl _) hlt

/--
If every value is weakly above a cutoff and a positive-mass value is strictly
above it, then the expectation is strictly above the cutoff.
-/
theorem cutoff_lt_pmfExp_of_all_ge_exists_gt
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (cutoff : ℝ)
    (hge : ∀ a, cutoff ≤ f a)
    (habove : ∃ a, 0 < (μ a).toReal ∧ cutoff < f a) :
    cutoff < pmfExp μ f := by
  have hneg : pmfExp μ (fun a => - f a) < -cutoff := by
    apply pmfExp_lt_of_forall_le_exists_lt
    · intro a
      exact neg_le_neg (hge a)
    · rcases habove with ⟨a, hmass, hgt⟩
      exact ⟨a, hmass, neg_lt_neg hgt⟩
  have hneg_mean : - pmfExp μ f < -cutoff := by
    simpa [pmfExp_neg] using hneg
  linarith

/--
Support-only version of `cutoff_lt_pmfExp_of_all_ge_exists_gt`: zero-mass
points do not need to satisfy the cutoff inequality.
-/
theorem cutoff_lt_pmfExp_of_support_ge_exists_gt
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (cutoff : ℝ)
    (hge : ∀ a, 0 < (μ a).toReal → cutoff ≤ f a)
    (habove : ∃ a, 0 < (μ a).toReal ∧ cutoff < f a) :
    cutoff < pmfExp μ f := by
  classical
  let supportValue : α → ℝ :=
    fun a => if (μ a).toReal = 0 then cutoff else f a
  have hExpEq : pmfExp μ f = pmfExp μ supportValue := by
    unfold pmfExp supportValue
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hzero : (μ a).toReal = 0
    · simp [hzero]
    · simp [hzero]
  have hsupport_ge : ∀ a, cutoff ≤ supportValue a := by
    intro a
    by_cases hzero : (μ a).toReal = 0
    · simp [supportValue, hzero]
    · have hmass : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      simpa [supportValue, hzero] using hge a hmass
  have hsupport_above :
      ∃ a, 0 < (μ a).toReal ∧ cutoff < supportValue a := by
    rcases habove with ⟨a, hmass, hgt⟩
    have hzero : (μ a).toReal ≠ 0 := ne_of_gt hmass
    exact ⟨a, hmass, by simpa [supportValue, hzero] using hgt⟩
  rw [hExpEq]
  exact cutoff_lt_pmfExp_of_all_ge_exists_gt
    μ supportValue cutoff hsupport_ge hsupport_above

/--
If every positive-mass atom has strictly positive value, then the finite PMF
expectation is strictly positive.
-/
theorem pmfExp_pos_of_support_forall_pos
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : PMF α) (f : α → ℝ)
    (hpos : ∀ a, 0 < (μ a).toReal → 0 < f a) :
    0 < pmfExp μ f := by
  have hneg :
      pmfExp μ (fun a => - f a) < 0 := by
    refine pmfExp_lt_of_support_forall_lt μ (fun a => - f a) 0 ?_
    intro a hmass
    exact neg_lt_zero.mpr (hpos a hmass)
  have hneg_mean : - pmfExp μ f < 0 := by
    simpa [pmfExp_neg] using hneg
  linarith

/--
If a finite PMF has a positive-mass value strictly above its expectation, then
it also has a positive-mass value strictly below its expectation.
-/
theorem exists_support_value_lt_pmfExp_of_exists_pmfExp_lt_value
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ)
    (habove : ∃ a, 0 < (μ a).toReal ∧ pmfExp μ f < f a) :
    ∃ a, 0 < (μ a).toReal ∧ f a < pmfExp μ f := by
  classical
  by_contra hnone
  have hno_below :
      ∀ a, 0 < (μ a).toReal → pmfExp μ f ≤ f a := by
    intro a hmass
    by_contra hlt_not
    exact hnone ⟨a, hmass, lt_of_not_ge hlt_not⟩
  let supportNegValue : α → ℝ :=
    fun a =>
      if (μ a).toReal = 0 then
        - pmfExp μ f
      else - f a
  have hExpNegEq :
      pmfExp μ supportNegValue = pmfExp μ (fun a => - f a) := by
    unfold pmfExp supportNegValue
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hzero : (μ a).toReal = 0
    · simp [hzero]
    · simp [hzero]
  have hle_neg : ∀ a, supportNegValue a ≤ - pmfExp μ f := by
    intro a
    by_cases hzero : (μ a).toReal = 0
    · simp [supportNegValue, hzero]
    · have hmass : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      simpa [supportNegValue, hzero] using neg_le_neg (hno_below a hmass)
  have habove_neg :
      ∃ a, 0 < (μ a).toReal ∧ supportNegValue a < - pmfExp μ f := by
    rcases habove with ⟨a, hmass, hgt⟩
    have hzero : (μ a).toReal ≠ 0 := ne_of_gt hmass
    exact ⟨a, hmass, by
      simpa [supportNegValue, hzero] using neg_lt_neg hgt⟩
  have hneg_lt : pmfExp μ supportNegValue < - pmfExp μ f :=
    pmfExp_lt_of_forall_le_exists_lt
      μ supportNegValue (- pmfExp μ f) hle_neg habove_neg
  rw [hExpNegEq, pmfExp_neg] at hneg_lt
  linarith

/--
If a finite PMF has a positive-mass value strictly below its expectation, then
it also has a positive-mass value strictly above its expectation.
-/
theorem exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ)
    (hbelow : ∃ a, 0 < (μ a).toReal ∧ f a < pmfExp μ f) :
    ∃ a, 0 < (μ a).toReal ∧ pmfExp μ f < f a := by
  rcases hbelow with ⟨a, hmass, hlt⟩
  have hneg_above :
      ∃ a, 0 < (μ a).toReal ∧
        pmfExp μ (fun a => - f a) < - f a := by
    refine ⟨a, hmass, ?_⟩
    rw [pmfExp_neg]
    linarith
  rcases
      exists_support_value_lt_pmfExp_of_exists_pmfExp_lt_value
        μ (fun a => - f a) hneg_above with
    ⟨aHigh, hmassHigh, hneg_below⟩
  refine ⟨aHigh, hmassHigh, ?_⟩
  rw [pmfExp_neg] at hneg_below
  linarith

/--
If no positive-mass value is strictly above the expectation, then every
positive-mass value is exactly the expectation.
-/
theorem no_support_value_gt_pmfExp_forces_support_at_pmfExp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ)
    (hno_above :
      ¬ ∃ a, 0 < (μ a).toReal ∧ pmfExp μ f < f a) :
    ∀ a, 0 < (μ a).toReal → f a = pmfExp μ f := by
  intro a hmass
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have habove :
        ∃ a, 0 < (μ a).toReal ∧ pmfExp μ f < f a :=
      exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
        μ f ⟨a, hmass, hlt⟩
    exact hno_above habove
  · exact hno_above ⟨a, hmass, hgt⟩

/--
If all positive-mass values equal the expectation, then there are no two
positive-mass atoms with different values.
-/
theorem support_at_pmfExp_forces_no_distinct_positive_mass_values
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → f a = pmfExp μ f) :
    ¬ ∃ a₁ a₂,
        0 < (μ a₁).toReal ∧ 0 < (μ a₂).toReal ∧ f a₁ ≠ f a₂ := by
  rintro ⟨a₁, a₂, hmass₁, hmass₂, hne⟩
  exact hne ((hsupport a₁ hmass₁).trans (hsupport a₂ hmass₂).symm)

/-- Linearity of independent-product expectation. -/
theorem pmfPairExp_add {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f g : α → β → ℝ) :
    pmfPairExp μ ν (fun a b => f a b + g a b) =
      pmfPairExp μ ν f + pmfPairExp μ ν g := by
  unfold pmfPairExp
  simp [pmfExp_add]

/-- Subtractive linearity of independent-product expectation. -/
theorem pmfPairExp_sub {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f g : α → β → ℝ) :
    pmfPairExp μ ν (fun a b => f a b - g a b) =
      pmfPairExp μ ν f - pmfPairExp μ ν g := by
  unfold pmfPairExp
  simp [pmfExp_sub]

/-- A two-stage finite expectation vanishes when every fresh-draw conditional expectation vanishes. -/
theorem pmfPairExp_eq_zero_of_forall_right {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ)
    (hzero : ∀ first, pmfExp ν (f first) = 0) :
    pmfPairExp μ ν f = 0 := by
  unfold pmfPairExp
  calc
    pmfExp μ (fun first => pmfExp ν (f first)) =
        pmfExp μ (fun _ => 0) := by
          apply pmfExp_congr
          exact hzero
    _ = 0 := pmfExp_zero μ

/-- A two-stage finite expectation inherits a uniform bound on each fresh-draw conditional expectation. -/
theorem pmfPairExp_le_of_forall_right {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) (bound : ℝ)
    (hbound : ∀ first, pmfExp ν (f first) ≤ bound) :
    pmfPairExp μ ν f ≤ bound := by
  unfold pmfPairExp
  exact pmfExp_le_of_forall_le μ _ bound hbound

/--
Under a finite iid product, a statistic of the new draw and an arbitrary
adaptive prefix has mean zero whenever its fresh-draw expectation vanishes
for every prefix.  `Option ι` distinguishes the fresh coordinate (`none`)
from the already observed coordinates (`some i`).
-/
theorem pmfExp_pmfProduct_fresh_eq_zero
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (statistic : (ι → α) → α → ℝ)
    (hzero : ∀ history, pmfExp μ (statistic history) = 0) :
    pmfExp (pmfProduct (Option ι) α μ)
        (fun sample => statistic (fun i => sample (some i)) (sample none)) = 0 := by
  calc
    pmfExp (pmfProduct (Option ι) α μ)
        (fun sample => statistic (fun i => sample (some i)) (sample none)) =
        pmfPairExp (pmfProduct ι α μ) μ statistic := by
          rw [pmfExp_pmfProduct_option_eq_pairExp]
          rfl
    _ = 0 := pmfPairExp_eq_zero_of_forall_right _ _ _ hzero

/--
Under a finite iid product, a statistic of a fresh draw and an arbitrary
adaptive prefix inherits any uniform bound on its fresh-draw expectation.
-/
theorem pmfExp_pmfProduct_fresh_le_of_forall
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (statistic : (ι → α) → α → ℝ) (bound : ℝ)
    (hbound : ∀ history, pmfExp μ (statistic history) ≤ bound) :
    pmfExp (pmfProduct (Option ι) α μ)
        (fun sample => statistic (fun i => sample (some i)) (sample none)) ≤ bound := by
  calc
    pmfExp (pmfProduct (Option ι) α μ)
        (fun sample => statistic (fun i => sample (some i)) (sample none)) =
        pmfPairExp (pmfProduct ι α μ) μ statistic := by
          rw [pmfExp_pmfProduct_option_eq_pairExp]
          rfl
    _ ≤ bound := pmfPairExp_le_of_forall_right _ _ _ bound hbound

/-- Swap the order of two finite independent PMF expectations. -/
theorem pmfPairExp_swap {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) :
    pmfPairExp μ ν f = pmfPairExp ν μ (fun b a => f a b) := by
  unfold pmfPairExp pmfExp
  calc
    ∑ a : α, (μ a).toReal * (∑ b : β, (ν b).toReal * f a b)
        = ∑ a : α, ∑ b : β,
            (μ a).toReal * ((ν b).toReal * f a b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ a : α, ∑ b : β,
            (ν b).toReal * ((μ a).toReal * f a b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = ∑ b : β, ∑ a : α,
            (ν b).toReal * ((μ a).toReal * f a b) := by
          exact Finset.sum_comm
    _ = ∑ b : β, (ν b).toReal *
            (∑ a : α, (μ a).toReal * f a b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.mul_sum]

/--
Variance as half the expected squared difference of two independent copies.
This finite identity is the base algebra for Efron--Stein/resampling bounds.
-/
theorem pmfVariance_eq_half_pmfPairExp_sq_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfVariance μ f =
      (1 / 2 : ℝ) * pmfPairExp μ μ (fun a b => (f a - f b) ^ 2) := by
  have hcross :
      pmfPairExp μ μ (fun a b => f a * f b) =
        pmfExp μ f * pmfExp μ f := by
    unfold pmfPairExp
    calc
      pmfExp μ (fun a => pmfExp μ (fun b => f a * f b)) =
          pmfExp μ (fun a => f a * pmfExp μ f) := by
            refine pmfExp_congr μ ?_
            intro a
            simpa [mul_comm] using pmfExp_const_mul μ (f a) f
      _ = pmfExp μ f * pmfExp μ f := by
            exact pmfExp_mul_const μ f (pmfExp μ f)
  have hpairsq :
      pmfPairExp μ μ (fun a b => (f a - f b) ^ 2) =
        2 * pmfExp μ (fun a => f a ^ 2) -
          2 * (pmfExp μ f) ^ 2 := by
    calc
      pmfPairExp μ μ (fun a b => (f a - f b) ^ 2) =
          pmfPairExp μ μ
            (fun a b => (f a ^ 2 - 2 * (f a * f b)) + f b ^ 2) := by
              unfold pmfPairExp
              refine pmfExp_congr μ ?_
              intro a
              refine pmfExp_congr μ ?_
              intro b
              ring
      _ =
          pmfPairExp μ μ (fun a b => f a ^ 2) -
            2 * pmfPairExp μ μ (fun a b => f a * f b) +
              pmfPairExp μ μ (fun a b => f b ^ 2) := by
              have hscale :
                  pmfPairExp μ μ (fun a b => 2 * (f a * f b)) =
                    2 * pmfPairExp μ μ (fun a b => f a * f b) := by
                unfold pmfPairExp
                calc
                  pmfExp μ
                      (fun a => pmfExp μ (fun b => 2 * (f a * f b))) =
                      pmfExp μ
                        (fun a => 2 * pmfExp μ (fun b => f a * f b)) := by
                          refine pmfExp_congr μ ?_
                          intro a
                          rw [pmfExp_const_mul]
                  _ = 2 * pmfExp μ
                      (fun a => pmfExp μ (fun b => f a * f b)) := by
                        rw [pmfExp_const_mul]
              rw [pmfPairExp_add, pmfPairExp_sub, hscale]
      _ =
          pmfExp μ (fun a => f a ^ 2) -
            2 * (pmfExp μ f * pmfExp μ f) +
              pmfExp μ (fun a => f a ^ 2) := by
              rw [pmfPairExp_ignore_right, pmfPairExp_ignore_left, hcross]
      _ = 2 * pmfExp μ (fun a => f a ^ 2) -
          2 * (pmfExp μ f) ^ 2 := by ring
  rw [pmfVariance_eq_exp_sq_sub_sq_exp, hpairsq]
  ring

/-- The square of a finite PMF expectation is at most the expected square. -/
theorem pmfExp_sq_le_pmfExp_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    (pmfExp μ f) ^ 2 ≤ pmfExp μ (fun a => f a ^ 2) := by
  have hvar : 0 ≤ pmfVariance μ f := pmfVariance_nonneg μ f
  rw [pmfVariance_eq_exp_sq_sub_sq_exp] at hvar
  linarith

/-- The norm of a finite vector expectation is at most the expected norm. -/
theorem norm_pmfVectorExp_le_pmfExp_norm
    {α V : Type*} [Fintype α] [DecidableEq α] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : PMF α) (f : α → V) :
    ‖pmfVectorExp μ f‖ ≤ pmfExp μ (fun a => ‖f a‖) := by
  unfold pmfVectorExp pmfExp
  calc
    ‖∑ a, (μ a).toReal • f a‖ ≤ ∑ a, ‖(μ a).toReal • f a‖ := norm_sum_le _ _
    _ = ∑ a, (μ a).toReal * ‖f a‖ := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]

/-- Squared-norm Jensen inequality for a finite vector expectation. -/
theorem sq_norm_pmfVectorExp_le_pmfExp_sq_norm
    {α V : Type*} [Fintype α] [DecidableEq α] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : PMF α) (f : α → V) :
    ‖pmfVectorExp μ f‖ ^ 2 ≤ pmfExp μ (fun a => ‖f a‖ ^ 2) := by
  calc
    ‖pmfVectorExp μ f‖ ^ 2 ≤ (pmfExp μ (fun a => ‖f a‖)) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (pmfExp_nonneg_of_forall_nonneg μ _
        (fun a => norm_nonneg _))).mpr (norm_pmfVectorExp_le_pmfExp_norm μ f)
    _ ≤ pmfExp μ (fun a => ‖f a‖ ^ 2) := pmfExp_sq_le_pmfExp_sq μ (fun a => ‖f a‖)

/-- Reindexing iid finite-product samples by an equivalence preserves variance. -/
theorem pmfVariance_pmfProduct_equiv
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : ι ≃ κ) (μ : PMF α) (F : (κ → α) → ℝ) :
    pmfVariance (pmfProduct ι α μ)
        (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) =
      pmfVariance (pmfProduct κ α μ) F := by
  have hsecond :
      pmfExp (pmfProduct ι α μ)
          (fun sample : ι → α => (F (fun j : κ => sample (e.symm j))) ^ 2) =
        pmfExp (pmfProduct κ α μ) (fun sample => (F sample) ^ 2) :=
    pmfExp_pmfProduct_equiv e μ (fun sample => (F sample) ^ 2)
  have hmean :
      pmfExp (pmfProduct ι α μ)
          (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) =
        pmfExp (pmfProduct κ α μ) F :=
    pmfExp_pmfProduct_equiv e μ F
  calc
    pmfVariance (pmfProduct ι α μ)
        (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) =
        pmfExp (pmfProduct ι α μ)
          (fun sample : ι → α => (F (fun j : κ => sample (e.symm j))) ^ 2) -
          (pmfExp (pmfProduct ι α μ)
            (fun sample : ι → α => F (fun j : κ => sample (e.symm j)))) ^ 2 :=
          pmfVariance_eq_exp_sq_sub_sq_exp _ _
    _ = pmfExp (pmfProduct κ α μ) (fun sample => (F sample) ^ 2) -
          (pmfExp (pmfProduct κ α μ) F) ^ 2 := by rw [hsecond, hmean]
    _ = pmfVariance (pmfProduct κ α μ) F :=
          (pmfVariance_eq_exp_sq_sub_sq_exp _ _).symm

@[simp] theorem pmfPairExp_zero {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) :
    pmfPairExp μ ν (fun _ _ => 0) = 0 := by
  unfold pmfPairExp
  simp

@[simp] theorem pmfPairExp_pure_left {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (a : α) (ν : PMF β) (f : α → β → ℝ) :
    pmfPairExp (PMF.pure a) ν f = pmfExp ν (fun b => f a b) := by
  unfold pmfPairExp
  simp

@[simp] theorem pmfPairExp_pure_right {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (b : β) (f : α → β → ℝ) :
    pmfPairExp μ (PMF.pure b) f = pmfExp μ (fun a => f a b) := by
  unfold pmfPairExp
  simp

end AppliedModelingLib

import Mathlib

/-!
# Single additive buyer, independent finitely supported item values

Definitions of `SREV`, `BREV`, (randomised) IC+IR mechanisms and `REV`.
All suprema range over *all* nonnegative real prices / *all* IC+IR mechanisms on `ℝ≥0^ι`.
-/
open Finset

namespace Sievert26SimpleAuctions

/-- A finitely supported probability distribution on the nonnegative reals. -/
structure FinDist where
  size : ℕ
  val : Fin size → ℝ
  prob : Fin size → ℝ
  val_nonneg : ∀ k, 0 ≤ val k
  prob_nonneg : ∀ k, 0 ≤ prob k
  prob_sum : ∑ k, prob k = 1

/-- `Pr[X ≥ p]`. -/
noncomputable def FinDist.tail (F : FinDist) (p : ℝ) : ℝ :=
  ∑ k, if p ≤ F.val k then F.prob k else 0

/-- Optimal posted price revenue of a single item, over all real prices `p ≥ 0`. -/
noncomputable def FinDist.rev (F : FinDist) : ℝ :=
  sSup (Set.range fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * F.tail p)

section
variable {ι : Type} [Fintype ι]

/-- A realisation: each item picks one of its support points. -/
abbrev Profile (D : ι → FinDist) : Type := (i : ι) → Fin (D i).size

/-- Product (independent) probability of a realisation. -/
noncomputable def prob (D : ι → FinDist) (ω : Profile D) : ℝ := ∏ i, (D i).prob (ω i)

/-- The value vector of a realisation. -/
noncomputable def value (D : ι → FinDist) (ω : Profile D) : ι → ℝ := fun i => (D i).val (ω i)

noncomputable def SREV (D : ι → FinDist) : ℝ := ∑ i, (D i).rev

theorem prob_nonneg (D : ι → FinDist) (ω : Profile D) : 0 ≤ prob D ω :=
  prod_nonneg fun i _ => (D i).prob_nonneg _

omit [Fintype ι] in
theorem value_nonneg (D : ι → FinDist) (ω : Profile D) (i : ι) : 0 ≤ value D ω i :=
  (D i).val_nonneg _

/-- A (possibly randomised) direct mechanism for one additive buyer: allocation probabilities in
`[0,1]`, payments in `ℝ`, IC and IR for *every* nonnegative value vector and deviation. -/
structure Mechanism (ι : Type) [Fintype ι] where
  alloc : (ι → ℝ) → ι → ℝ
  pay : (ι → ℝ) → ℝ
  alloc_nonneg : ∀ v i, 0 ≤ alloc v i
  alloc_le_one : ∀ v i, alloc v i ≤ 1
  ir : ∀ v, (∀ i, 0 ≤ v i) → 0 ≤ ∑ i, v i * alloc v i - pay v
  ic : ∀ v v', (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ v' i) →
    ∑ i, v i * alloc v' i - pay v' ≤ ∑ i, v i * alloc v i - pay v

variable [DecidableEq ι]

/-- `Pr[Σ v_i ≥ p]` under the product distribution. -/
noncomputable def bundleTail (D : ι → FinDist) (p : ℝ) : ℝ :=
  ∑ ω : Profile D, if p ≤ ∑ i, value D ω i then prob D ω else 0

/-- Optimal grand-bundle revenue, over all real prices `p ≥ 0`. -/
noncomputable def BREV (D : ι → FinDist) : ℝ :=
  sSup (Set.range fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * bundleTail D p)

/-- Expected revenue of a mechanism. -/
noncomputable def Mechanism.rev (M : Mechanism ι) (D : ι → FinDist) : ℝ :=
  ∑ ω : Profile D, prob D ω * M.pay (value D ω)

/-- Optimal revenue over all IC+IR mechanisms. -/
noncomputable def REV (D : ι → FinDist) : ℝ :=
  sSup (Set.range fun M : Mechanism ι => M.rev D)

/-- Product of sums = sum of products over realisations. -/
theorem sum_prod_pi {κ : ι → ℕ} {S : Type*} [CommSemiring S] (f : (i : ι) → Fin (κ i) → S) :
    ∑ ω : ((i : ι) → Fin (κ i)), ∏ i, f i (ω i) = ∏ i, ∑ k, f i k := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem prob_sum (D : ι → FinDist) : ∑ ω : Profile D, prob D ω = 1 := by
  unfold prob
  rw [sum_prod_pi (fun i k => (D i).prob k)]
  exact prod_eq_one fun i _ => (D i).prob_sum

theorem FinDist.tail_nonneg (F : FinDist) (p : ℝ) : 0 ≤ F.tail p :=
  sum_nonneg fun k _ => by split_ifs <;> simp [F.prob_nonneg k]

theorem bundleTail_nonneg (D : ι → FinDist) (p : ℝ) : 0 ≤ bundleTail D p :=
  sum_nonneg fun ω _ => by split_ifs <;> simp [prob_nonneg D ω]

instance : Nonempty {p : ℝ // 0 ≤ p} := ⟨⟨0, le_refl 0⟩⟩

theorem mean_bound {α : Type*} [Fintype α] (v q : α → ℝ) (hv : ∀ a, 0 ≤ v a)
    (hq : ∀ a, 0 ≤ q a) (p : ℝ) :
    p * ∑ a, (if p ≤ v a then q a else 0) ≤ ∑ a, v a * q a := by
  rw [mul_sum]
  refine sum_le_sum fun a _ => ?_
  split_ifs with h
  · exact mul_le_mul_of_nonneg_right h (hq a)
  · simpa using mul_nonneg (hv a) (hq a)

/-- The supremum in `FinDist.rev` is a genuine one (bounded family). -/
theorem FinDist.rev_bdd (F : FinDist) :
    BddAbove (Set.range fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * F.tail p) :=
  ⟨∑ k, F.val k * F.prob k, by
    rintro _ ⟨p, rfl⟩; exact mean_bound F.val F.prob F.val_nonneg F.prob_nonneg p⟩

/-- The supremum in `BREV` is a genuine one (bounded family). -/
theorem BREV_bdd (D : ι → FinDist) :
    BddAbove (Set.range fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * bundleTail D p) :=
  ⟨∑ ω : Profile D, (∑ i, value D ω i) * prob D ω, by
    rintro _ ⟨p, rfl⟩
    exact mean_bound _ _ (fun ω => sum_nonneg fun i _ => value_nonneg D ω i) (prob_nonneg D) p⟩

/-- The supremum in `REV` is a genuine one: revenue is bounded by the welfare. -/
theorem REV_bdd (D : ι → FinDist) : BddAbove (Set.range fun M : Mechanism ι => M.rev D) := by
  refine ⟨∑ ω : Profile D, prob D ω * ∑ i, value D ω i, ?_⟩
  rintro _ ⟨M, rfl⟩
  refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (prob_nonneg D ω)
  have h := M.ir (value D ω) (value_nonneg D ω)
  have h2 : ∑ i, value D ω i * M.alloc (value D ω) i ≤ ∑ i, value D ω i :=
    sum_le_sum fun i _ => by
      simpa using mul_le_mul_of_nonneg_left (M.alloc_le_one (value D ω) i) (value_nonneg D ω i)
  linarith

theorem le_REV (D : ι → FinDist) (M : Mechanism ι) : M.rev D ≤ REV D :=
  le_ciSup (f := fun M : Mechanism ι => M.rev D) (REV_bdd D) M

theorem FinDist.rev_le (F : FinDist) (B : ℝ) (h : ∀ p : ℝ, 0 ≤ p → p * F.tail p ≤ B) :
    F.rev ≤ B := ciSup_le fun p => h p.1 p.2

theorem BREV_le (D : ι → FinDist) (B : ℝ) (h : ∀ p : ℝ, 0 ≤ p → p * bundleTail D p ≤ B) :
    BREV D ≤ B := ciSup_le fun p => h p.1 p.2

end
end Sievert26SimpleAuctions

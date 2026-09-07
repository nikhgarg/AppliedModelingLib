import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Resampling a coordinate of a heterogeneous finite product

The coordinate PMFs in a finite product need not be identical.  This module
records the elementary deferred-decision identity that replacing one coordinate
by an independent draw from its own PMF preserves the complete product law.
-/

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace AppliedModelingLib

/-- Averaging an independently resampled coordinate of a heterogeneous finite
product gives back the original product expectation. -/
theorem pmfExp_pmfPi_resample_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) (F : (ι → α) → ℝ) (i : ι) :
    pmfExp (pmfPi μ) (fun sample =>
      pmfExp (μ i) (fun replacement => F (Function.update sample i replacement))) =
      pmfExp (pmfPi μ) F := by
  classical
  let Rest := {k : ι // k ≠ i}
  let e := oneCoordFunEquivProdRest (α := α) i
  have hrest_mass :
      ∑ rest : Rest → α, ∏ k : Rest, (μ k.1 (rest k)).toReal = 1 := by
    have hcoord : ∀ k : Rest, ∑ a : α, (μ k.1 a).toReal = 1 := by
      intro k
      exact pmfToRealSum (μ k.1)
    calc
      ∑ rest : Rest → α, ∏ k : Rest, (μ k.1 (rest k)).toReal
          = ∏ k : Rest, ∑ a ∈ (Finset.univ : Finset α), (μ k.1 a).toReal := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _k : Rest => (Finset.univ : Finset α))
                (f := fun k a => (μ k.1 a).toReal))
      _ = 1 := by simp [hcoord]
  have hprod_split :
      ∀ x : α × (Rest → α),
        (∏ k : ι, (μ k ((e.symm x) k)).toReal) =
          (μ i x.1).toReal * ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
    intro x
    let g : ι → ℝ := fun k => (μ k ((e.symm x) k)).toReal
    have hi_eval : g i = (μ i x.1).toReal := by
      simp [g, e, oneCoordFunEquivProdRest]
    have hrest :
        (∏ k ∈ ({i}ᶜ : Finset ι), g k) =
          ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
      rw [Finset.prod_subtype
        (s := ({i}ᶜ : Finset ι))
        (p := fun k : ι => k ≠ i)]
      · refine Finset.prod_congr rfl ?_
        intro k _
        simp [g, e, oneCoordFunEquivProdRest, k.2]
      · intro k
        simp
    calc
      ∏ k : ι, (μ k ((e.symm x) k)).toReal = ∏ k : ι, g k := rfl
      _ = g i * ∏ k ∈ ({i}ᶜ : Finset ι), g k := by
        rw [Fintype.prod_eq_mul_prod_compl]
      _ = (μ i x.1).toReal * ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
        rw [hi_eval, hrest]
  have hupdate (x : α × (Rest → α)) (replacement : α) :
      Function.update (e.symm x) i replacement = e.symm (replacement, x.2) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [e, oneCoordFunEquivProdRest]
    · simp [e, oneCoordFunEquivProdRest, hk]
  unfold pmfExp
  calc
    ∑ sample : ι → α, (pmfPi μ sample).toReal *
        ∑ replacement : α, (μ i replacement).toReal *
          F (Function.update sample i replacement) =
        ∑ x : α × (Rest → α), (pmfPi μ (e.symm x)).toReal *
          ∑ replacement : α, (μ i replacement).toReal *
            F (Function.update (e.symm x) i replacement) := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun sample : ι → α => (pmfPi μ sample).toReal *
                ∑ replacement : α, (μ i replacement).toReal *
                  F (Function.update sample i replacement))).symm
    _ = ∑ x : α × (Rest → α),
          ((μ i x.1).toReal * ∏ k : Rest, (μ k.1 (x.2 k)).toReal) *
            ∑ replacement : α, (μ i replacement).toReal *
              F (e.symm (replacement, x.2)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [pmfPi_apply_toReal, hprod_split x]
          apply congrArg (fun value =>
            ((μ i x.1).toReal * ∏ k : Rest, (μ k.1 (x.2 k)).toReal) * value)
          refine Finset.sum_congr rfl ?_
          intro replacement _
          rw [hupdate]
    _ = ∑ a : α, ∑ rest : Rest → α,
          ((μ i a).toReal * ∏ k : Rest, (μ k.1 (rest k)).toReal) *
            ∑ replacement : α, (μ i replacement).toReal *
              F (e.symm (replacement, rest)) := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset α))
              (t := (Finset.univ : Finset (Rest → α)))
              (f := fun a rest =>
                ((μ i a).toReal * ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                  ∑ replacement : α, (μ i replacement).toReal *
                    F (e.symm (replacement, rest))))
    _ = ∑ rest : Rest → α,
          (∑ a : α, (μ i a).toReal) *
            ((∏ k : Rest, (μ k.1 (rest k)).toReal) *
              ∑ replacement : α, (μ i replacement).toReal *
                F (e.symm (replacement, rest))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro rest _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = ∑ rest : Rest → α,
          (∏ k : Rest, (μ k.1 (rest k)).toReal) *
            ∑ replacement : α, (μ i replacement).toReal *
              F (e.symm (replacement, rest)) := by
          have hmass : ∑ a : α, (μ i a).toReal = 1 := pmfToRealSum (μ i)
          rw [hmass]
          simp
    _ = ∑ replacement : α, ∑ rest : Rest → α,
          ((μ i replacement).toReal *
            ∏ k : Rest, (μ k.1 (rest k)).toReal) *
              F (e.symm (replacement, rest)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro replacement _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro rest _
          ring
    _ = ∑ x : α × (Rest → α),
          (pmfPi μ (e.symm x)).toReal * F (e.symm x) := by
          symm
          calc
            ∑ x : α × (Rest → α),
                (pmfPi μ (e.symm x)).toReal * F (e.symm x) =
                ∑ x : α × (Rest → α),
                  ((μ i x.1).toReal * ∏ k : Rest,
                    (μ k.1 (x.2 k)).toReal) * F (e.symm x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _
                  rw [pmfPi_apply_toReal, hprod_split x]
            _ = ∑ replacement : α, ∑ rest : Rest → α,
                ((μ i replacement).toReal *
                  ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                    F (e.symm (replacement, rest)) := by
                  simpa [Finset.univ_product_univ] using
                    (Finset.sum_product'
                      (s := (Finset.univ : Finset α))
                      (t := (Finset.univ : Finset (Rest → α)))
                      (f := fun replacement rest =>
                        ((μ i replacement).toReal *
                          ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                            F (e.symm (replacement, rest))))
    _ = ∑ sample : ι → α, (pmfPi μ sample).toReal * F sample := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun sample : ι → α => (pmfPi μ sample).toReal * F sample))

/-- Independently resampling any coordinate of a heterogeneous finite product
preserves the complete product law. -/
theorem pmfPairExp_pmfPi_update_eq_pmfExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) (F : (ι → α) → ℝ) (i : ι) :
    pmfPairExp (pmfPi μ) (μ i)
        (fun sample replacement => F (Function.update sample i replacement)) =
      pmfExp (pmfPi μ) F := by
  unfold pmfPairExp
  exact pmfExp_pmfPi_resample_eq μ F i

/-- Flattening a finite family of coordinate-specific iid blocks preserves
finite expectations.  The outer coordinate laws may differ, while entries
within each block share that coordinate's law. -/
theorem pmfExp_pmfPi_pmfProduct_flatten
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) (F : (ι × κ → α) → ℝ) :
    pmfExp (pmfPi fun i : ι => pmfProduct κ α (μ i))
        (fun sample : ι → κ → α => F (fun ij => sample ij.1 ij.2)) =
      pmfExp (pmfPi fun ij : ι × κ => μ ij.1) F := by
  classical
  let e : (ι → κ → α) ≃ (ι × κ → α) := (Equiv.curry ι κ α).symm
  unfold pmfExp
  calc
    ∑ sample : ι → κ → α,
        (pmfPi (fun i : ι => pmfProduct κ α (μ i)) sample).toReal *
          F (fun ij => sample ij.1 ij.2) =
        ∑ flat : ι × κ → α,
          (pmfPi (fun i : ι => pmfProduct κ α (μ i)) (e.symm flat)).toReal *
            F flat := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun sample : ι → κ → α =>
                (pmfPi (fun i : ι => pmfProduct κ α (μ i)) sample).toReal *
                  F (fun ij => sample ij.1 ij.2))).symm
    _ = ∑ flat : ι × κ → α,
          (pmfPi (fun ij : ι × κ => μ ij.1) flat).toReal * F flat := by
          refine Finset.sum_congr rfl ?_
          intro flat _
          congr 1
          rw [pmfPi_apply_toReal, pmfPi_apply_toReal]
          simp_rw [pmfProduct_apply_toReal]
          simpa [e] using
            (Fintype.prod_prod_type' (fun i j => (μ i (flat (i, j))).toReal)).symm

end AppliedModelingLib

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace AppliedModelingLib

/--
Finite FKG for antitone real observables.

This is the order-dual form of mathlib's finite FKG inequality.
-/
theorem finiteFkg_antitone_real
    {α : Type*} [Fintype α] [DistribLattice α]
    (μ f g : α → ℝ)
    (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Antitone f) (hg : Antitone g)
    (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a ≤
      (∑ a, μ a) * ∑ a, μ a * (f a * g a) := by
  classical
  let μd : αᵒᵈ → ℝ := fun a => μ (OrderDual.ofDual a)
  let fd : αᵒᵈ → ℝ := fun a => f (OrderDual.ofDual a)
  let gd : αᵒᵈ → ℝ := fun a => g (OrderDual.ofDual a)
  have hμd₀ : 0 ≤ μd := by
    intro a
    exact hμ₀ (OrderDual.ofDual a)
  have hfd₀ : 0 ≤ fd := by
    intro a
    exact hf₀ (OrderDual.ofDual a)
  have hgd₀ : 0 ≤ gd := by
    intro a
    exact hg₀ (OrderDual.ofDual a)
  have hfd : Monotone fd := by
    intro a b hab
    exact hf hab
  have hgd : Monotone gd := by
    intro a b hab
    exact hg hab
  have hμd :
      ∀ a b : αᵒᵈ,
        μd a * μd b ≤ μd (a ⊓ b) * μd (a ⊔ b) := by
    intro a b
    simpa [μd, mul_comm, mul_left_comm, mul_assoc] using
      hμ (OrderDual.ofDual a) (OrderDual.ofDual b)
  have hd :=
    fkg (α := αᵒᵈ) (μ := μd) (f := fd) (g := gd)
      hμd₀ hfd₀ hgd₀ hfd hgd hμd
  have hμf :
      (∑ a : αᵒᵈ, μd a * fd a) =
        ∑ a : α, μ a * f a := by
    simpa [μd, fd] using
      (Equiv.sum_comp (OrderDual.toDual : α ≃ αᵒᵈ)
        (fun a : αᵒᵈ => μd a * fd a)).symm
  have hμg :
      (∑ a : αᵒᵈ, μd a * gd a) =
        ∑ a : α, μ a * g a := by
    simpa [μd, gd] using
      (Equiv.sum_comp (OrderDual.toDual : α ≃ αᵒᵈ)
        (fun a : αᵒᵈ => μd a * gd a)).symm
  have hμsum :
      (∑ a : αᵒᵈ, μd a) =
        ∑ a : α, μ a := by
    simpa [μd] using
      (Equiv.sum_comp (OrderDual.toDual : α ≃ αᵒᵈ)
        (fun a : αᵒᵈ => μd a)).symm
  have hμfg :
      (∑ a : αᵒᵈ, μd a * (fd a * gd a)) =
        ∑ a : α, μ a * (f a * g a) := by
    simpa [μd, fd, gd] using
      (Equiv.sum_comp (OrderDual.toDual : α ≃ αᵒᵈ)
        (fun a : αᵒᵈ => μd a * (fd a * gd a))).symm
  rwa [hμf, hμg, hμsum, hμfg] at hd

/--
If every fiber has nonnegative covariance between `F a` and a fiber-level
observable `G`, then any nonnegative mixture over fibers also has nonnegative
covariance.
-/
theorem weighted_average_covariance_nonneg_of_fiber_covariance
    {α β : Type*} [Fintype α] [Fintype β]
    (A : α → ℝ) (W : β → ℝ) (F : α → β → ℝ) (G : β → ℝ)
    (hA_nonneg : ∀ a, 0 ≤ A a)
    (hfiber : ∀ a,
      (∑ b, W b * F a b) * (∑ b, W b * G b) ≤
        (∑ b, W b) * (∑ b, W b * (F a b * G b))) :
    0 ≤
      (∑ a, A a * ∑ b, W b * (F a b * G b)) *
          ((∑ a, A a) * ∑ b, W b) -
        (∑ a, A a * ∑ b, W b * F a b) *
          ((∑ a, A a) * ∑ b, W b * G b) := by
  classical
  let SF : α → ℝ := fun a => ∑ b, W b * F a b
  let SG : ℝ := ∑ b, W b * G b
  let SW : ℝ := ∑ b, W b
  let SFG : α → ℝ := fun a => ∑ b, W b * (F a b * G b)
  have hsum :
      (∑ a, A a * SF a) * SG ≤
        SW * (∑ a, A a * SFG a) := by
    calc
      (∑ a, A a * SF a) * SG =
          ∑ a, A a * (SF a * SG) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro a _
        ring
      _ ≤ ∑ a, A a * (SW * SFG a) := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact mul_le_mul_of_nonneg_left (hfiber a) (hA_nonneg a)
      _ = SW * (∑ a, A a * SFG a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro a _
        ring
  have hA_sum_nonneg : 0 ≤ ∑ a, A a :=
    Finset.sum_nonneg (fun a _ => hA_nonneg a)
  have hcore :
      0 ≤ SW * (∑ a, A a * SFG a) -
        (∑ a, A a * SF a) * SG :=
    sub_nonneg.mpr hsum
  have hprod :
      0 ≤ (∑ a, A a) *
        (SW * (∑ a, A a * SFG a) -
          (∑ a, A a * SF a) * SG) :=
    mul_nonneg hA_sum_nonneg hcore
  convert hprod using 1
  simp [SF, SG, SW, SFG]
  ring

end AppliedModelingLib

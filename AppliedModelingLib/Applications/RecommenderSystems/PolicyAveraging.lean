import AppliedModelingLib.Applications.RecommenderSystems.Policy
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace AppliedModelingLib
namespace Policy

/--
Average a finite nonempty family of randomized policies into a single PMF.

The value at action `b` is the arithmetic mean of the probabilities assigned to
`b` by the policies indexed by `s`.
-/
noncomputable def averageOn {α β : Type*} [Fintype β]
    (ρ : α → PMF β) (s : Finset α) (hs : s.Nonempty) : PMF β :=
  PMF.ofFintype
    (fun b : β => (∑ a ∈ s, ρ a b) / (s.card : ENNReal))
    (by
      classical
      have hcard_ne_zero_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
      have hcard_ne_zero : (s.card : ENNReal) ≠ 0 := by
        exact_mod_cast hcard_ne_zero_nat
      have hcard_ne_top : (s.card : ENNReal) ≠ ⊤ :=
        ENNReal.natCast_ne_top s.card
      calc
        ∑ b : β, (∑ a ∈ s, ρ a b) / (s.card : ENNReal)
            = ∑ b : β, (s.card : ENNReal)⁻¹ * (∑ a ∈ s, ρ a b) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              rw [ENNReal.div_eq_inv_mul]
        _ = (s.card : ENNReal)⁻¹ * (∑ b : β, ∑ a ∈ s, ρ a b) := by
              rw [Finset.mul_sum]
        _ = (s.card : ENNReal)⁻¹ * (∑ a ∈ s, ∑ b : β, ρ a b) := by
              rw [Finset.sum_comm]
        _ = (s.card : ENNReal)⁻¹ * (∑ a ∈ s, (1 : ENNReal)) := by
              refine congrArg (fun z => (s.card : ENNReal)⁻¹ * z) ?_
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa [tsum_fintype] using (PMF.tsum_coe (ρ a))
        _ = (s.card : ENNReal)⁻¹ * (s.card : ENNReal) := by
              simp
        _ = 1 := ENNReal.inv_mul_cancel hcard_ne_zero hcard_ne_top)

/-- Real-valued action probabilities of `averageOn` are arithmetic means. -/
theorem averageOn_apply_toReal {α β : Type*} [Fintype β]
    (ρ : α → PMF β) (s : Finset α) (hs : s.Nonempty) (b : β) :
    ((averageOn ρ s hs) b).toReal =
      (∑ a ∈ s, (ρ a b).toReal) / (s.card : ℝ) := by
  unfold averageOn
  rw [PMF.ofFintype_apply]
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_sum]
  · rw [ENNReal.toReal_natCast]
  · intro a _
    exact PMF.apply_ne_top (ρ a) b

end Policy
end AppliedModelingLib

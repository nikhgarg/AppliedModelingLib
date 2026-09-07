import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Basic

/-!
# Geometric queue-state laws and independent product couplings

This module proves the exact geometric upper-tail formula needed by the
stationary M/M/1 calculation and constructs a product-space coupling with an
independent future-service random variable.  It does not derive geometric
stationarity from a birth-death queue dynamics; that stationary-state step
remains a separate proof obligation.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


lemma geometricPMF_real_apply
    (rho : ℝ) (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) (n : ℕ) :
    (geometricPMF (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
      (sub_le_self 1 hrho_nonneg) n).toReal = rho ^ n * (1 - rho) := by
  change (ENNReal.ofReal (geometricPMFReal (1 - rho) n)).toReal = _
  rw [ENNReal.toReal_ofReal]
  · simp only [geometricPMFReal]
    ring
  · exact geometricPMFReal_nonneg (sub_pos.mpr hrho_lt_one)
      (sub_le_self 1 hrho_nonneg)

theorem measureReal_geometricMeasure_tail
    (rho : ℝ) (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) (k : ℕ) :
    (geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
      (sub_le_self 1 hrho_nonneg)).real {n : ℕ | k ≤ n} = rho ^ k := by
  simp only [geometricMeasure, Measure.real, PMF.toMeasure_apply_eq_tsum]
  rw [ENNReal.tsum_toReal_eq]
  · have hterm : ∀ a : ℕ,
        (({n : ℕ | k ≤ n}).indicator
          (geometricPMF (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
            (sub_le_self 1 hrho_nonneg)) a).toReal =
        ({n : ℕ | k ≤ n}).indicator
          (fun n => (geometricPMF (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
            (sub_le_self 1 hrho_nonneg) n).toReal) a := by
      intro a
      by_cases ha : k ≤ a
      · simp [Set.indicator, ha]
      · simp [Set.indicator, ha]
    calc
      (∑' a : ℕ,
          (({n : ℕ | k ≤ n}).indicator
            (geometricPMF (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
              (sub_le_self 1 hrho_nonneg)) a).toReal) =
        ∑' a : ℕ,
          ({n : ℕ | k ≤ n}).indicator
            (fun n => (geometricPMF (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
              (sub_le_self 1 hrho_nonneg) n).toReal) a := tsum_congr hterm
      _ = rho ^ k := by
        rw [← tsum_subtype]
        let e : ℕ ≃ {n : ℕ | k ≤ n} :=
          { toFun := fun n => ⟨k + n, Nat.le_add_right k n⟩
            invFun := fun n => n.1 - k
            left_inv := fun n => Nat.add_sub_cancel_left k n
            right_inv := by
              intro n
              apply Subtype.ext
              simpa [Nat.add_comm] using Nat.sub_add_cancel n.2 }
        rw [← e.tsum_eq]
        change (∑' n : ℕ,
          (geometricPMF (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
            (sub_le_self 1 hrho_nonneg) (k + n)).toReal) = rho ^ k
        simp_rw [geometricPMF_real_apply rho hrho_nonneg hrho_lt_one]
        have hgeom := hasSum_geometric_of_lt_one hrho_nonneg hrho_lt_one
        have hsum : HasSum
            (fun n : ℕ => rho ^ (k + n) * (1 - rho)) (rho ^ k) := by
          convert (hgeom.mul_right (1 - rho)).mul_left (rho ^ k) using 1
          · funext n
            rw [pow_add]
            ring
          · field_simp [ne_of_gt (sub_pos.mpr hrho_lt_one)]
        exact hsum.tsum_eq
  · intro n
    by_cases hn : k ≤ n
    · simp only [Set.indicator, Set.mem_setOf_eq, hn, ite_true]
      change ENNReal.ofReal _ ≠ ∞
      exact ENNReal.ofReal_ne_top
    · simp [Set.indicator, hn]

/-- A canonical independent coupling of a geometric queue length and an arbitrary
independent future-service random variable, built on the product probability space. -/
theorem indepFun_geometricQueueLength_prod
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (service : Ω → S) (hservice : Measurable service)
    (rho : ℝ) (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    IndepFun (fun x : ℕ × Ω => x.1) (fun x => service x.2)
      ((geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
        (sub_le_self 1 hrho_nonneg)).prod P) := by
  letI : IsProbabilityMeasure
      (geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
        (sub_le_self 1 hrho_nonneg)) :=
    isProbabilityMeasure_geometricMeasure (sub_pos.mpr hrho_lt_one)
      (sub_le_self 1 hrho_nonneg)
  simpa only [id_eq] using
    (indepFun_prod
      (μ := geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
        (sub_le_self 1 hrho_nonneg)) (ν := P)
      (X := id) (Y := service) measurable_id hservice)

/-- The first coordinate of the product coupling retains the geometric tail. -/
theorem measureReal_geometricQueueLength_prod_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rho : ℝ) (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) (k : ℕ) :
    ((geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
      (sub_le_self 1 hrho_nonneg)).prod P).real
      (Prod.fst ⁻¹' Set.Ici k) = rho ^ k := by
  rw [Measure.real,
    (measurePreserving_fst
      (μ := geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
        (sub_le_self 1 hrho_nonneg)) (ν := P)).measure_preimage
      measurableSet_Ici.nullMeasurableSet]
  exact measureReal_geometricMeasure_tail rho hrho_nonneg hrho_lt_one k

end Queueing
end Probability
end AppliedModelingLib

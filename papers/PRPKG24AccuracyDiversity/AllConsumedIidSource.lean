import PRPKG24AccuracyDiversity.SourcePreferenceMixture
import PRPKG24AccuracyDiversity.TailHomogeneity
import Mathlib.MeasureTheory.Integral.Pi

/-!
# All-consumed iid source bridge

The all-consumed clause of Theorem 1(v) uses one common conditional value
distribution.  Conditional on the initially selected preferred type, a slate
of `q` items is a finite iid product draw from that distribution and every
draw is consumed.  This module proves the resulting finite expectation before
using the linear optimization theorem.

The `Integrable id D` hypothesis is intentional: a probability law alone does
not make its real-valued mean a finite real number.
-/

open scoped BigOperators
open MeasureTheory

namespace PRPKG24AccuracyDiversity

noncomputable section

/-- The realized all-consumed value of a finite sample is the sum of all draws. -/
def iidAllConsumedSampleValue {q : ℕ} (sample : Fin q → ℝ) : ℝ :=
  ∑ i, sample i

/-- The finite iid conditional law of `q` recommended values from `D`. -/
def iidAllConsumedSampleLaw (D : Measure ℝ) (q : ℕ) : Measure (Fin q → ℝ) :=
  Measure.pi (fun _ : Fin q => D)

/-- A finite iid product of the source probability law is a probability law. -/
theorem iidAllConsumedSampleLaw_isProbabilityMeasure
    (D : Measure ℝ) [IsProbabilityMeasure D] (q : ℕ) :
    IsProbabilityMeasure (iidAllConsumedSampleLaw D q) := by
  dsimp [iidAllConsumedSampleLaw]
  infer_instance

/--
The conditional all-consumed expectation of `q` iid source draws is `q` times
the finite source mean.  The proof uses the product-law coordinate marginals,
so the iid law is part of the checked semantics rather than a label.
-/
theorem iidAllConsumedSampleValue_expected
    (D : Measure ℝ) [IsProbabilityMeasure D] (q : ℕ)
    (h_integrable : Integrable (fun x : ℝ => x) D) :
    (∫ sample : Fin q → ℝ,
      iidAllConsumedSampleValue sample ∂iidAllConsumedSampleLaw D q) =
      (q : ℝ) * ∫ x : ℝ, x ∂D := by
  classical
  change
    (∫ sample : Fin q → ℝ, (∑ i, sample i)
      ∂iidAllConsumedSampleLaw D q) =
      (q : ℝ) * ∫ x : ℝ, x ∂D
  rw [iidAllConsumedSampleLaw, integral_finset_sum]
  · simp_rw [integral_eval]
    simp
  · intro i _
    exact integrable_eval h_integrable

/--
The literal source model for Theorem 1(v): first draw a preferred type from
`preferenceLaw`, then conditionally draw a finite iid slate from the one common
value law `D`, and consume all of it.
-/
noncomputable def iidAllConsumedSourceModel {T : ℕ}
    (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ) :
    ConsumptionModel T where
  likelihood := fun t => (preferenceLaw t).toReal
  valueOfCount := fun _ q =>
    ∫ sample : Fin q → ℝ,
      iidAllConsumedSampleValue sample ∂iidAllConsumedSampleLaw D q

/-- The source model's conditional count value is its finite iid expectation. -/
theorem iidAllConsumedSourceModel_value_eq_source_experiment
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    (t : ItemType T) (q : ℕ) :
    (iidAllConsumedSourceModel preferenceLaw D).valueOfCount t q =
      ∫ sample : Fin q → ℝ,
        iidAllConsumedSampleValue sample ∂iidAllConsumedSampleLaw D q :=
  rfl

/-- The literal iid source model is the common-mean linearized model. -/
theorem iidAllConsumedSourceModel_eq_linearized
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D]
    (h_integrable : Integrable (fun x : ℝ => x) D) :
    iidAllConsumedSourceModel preferenceLaw D =
      ConsumptionModel.linearized
        (fun t => (preferenceLaw t).toReal)
        (fun _ => ∫ x : ℝ, x ∂D) := by
  have hvalue :
      (fun _ : ItemType T => fun q : ℕ =>
        ∫ sample : Fin q → ℝ,
          iidAllConsumedSampleValue sample ∂iidAllConsumedSampleLaw D q) =
        (fun _ : ItemType T => fun q : ℕ =>
          (q : ℝ) * ∫ x : ℝ, x ∂D) := by
    funext t q
    exact iidAllConsumedSampleValue_expected D q h_integrable
  change
    ({ likelihood := fun t => (preferenceLaw t).toReal
       valueOfCount := fun _ q =>
         ∫ sample : Fin q → ℝ,
           iidAllConsumedSampleValue sample ∂iidAllConsumedSampleLaw D q } :
      ConsumptionModel T) =
      ({ likelihood := fun t => (preferenceLaw t).toReal
         valueOfCount := fun _ q => (q : ℝ) * ∫ x : ℝ, x ∂D } :
        ConsumptionModel T)
  rw [hvalue]

/--
Equation (3) for Theorem 1(v)'s literal two-stage experiment: a PMF chooses
the preferred type, then that type's iid all-consumed sample value is averaged.
-/
theorem iidAllConsumedSourceModel_objective_eq_source_experiment
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    (a : CountAllocation T) :
    (iidAllConsumedSourceModel preferenceLaw D).objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t =>
          ∫ sample : Fin (a.count t) → ℝ,
            iidAllConsumedSampleValue sample
              ∂iidAllConsumedSampleLaw D (a.count t)) := by
  exact ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
    (iidAllConsumedSourceModel preferenceLaw D) a preferenceLaw (by
      intro t
      rfl)

/--
The source-law version of Theorem 1(v)'s weak direction.  A nonnegative finite
common mean preserves the likelihood argmax direction.
-/
theorem iidAllConsumedSourceModel_allOn_max_likelihood_isOptimal
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D]
    (h_integrable : Integrable (fun x : ℝ => x) D)
    (hmean_nonneg : 0 ≤ ∫ x : ℝ, x ∂D)
    (N : ℕ) (best : ItemType T)
    (hbest : ∀ t, (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) :
    (iidAllConsumedSourceModel preferenceLaw D).IsOptimalAtTotal N
      (allOnTypeAllocation N best) := by
  rw [iidAllConsumedSourceModel_eq_linearized preferenceLaw D h_integrable]
  exact allOnTypeAllocation_linearized_isOptimalAtTotal
    (fun t => (preferenceLaw t).toReal) (fun _ => ∫ x : ℝ, x ∂D)
    N best (fun t =>
      mul_le_mul_of_nonneg_right (hbest t) hmean_nonneg)

/--
The source-law unique-argmax converse.  A positive finite common mean makes
every allocation using a nonmaximal preferred type strictly suboptimal.
-/
theorem iidAllConsumedSourceModel_unique_max_likelihood_only_optimal
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D]
    (h_integrable : Integrable (fun x : ℝ => x) D)
    (hmean_pos : 0 < ∫ x : ℝ, x ∂D)
    (N : ℕ) (best : ItemType T)
    (hbest_strict :
      ∀ t, t ≠ best → (preferenceLaw t).toReal < (preferenceLaw best).toReal)
    (a : CountAllocation T)
    (hopt : (iidAllConsumedSourceModel preferenceLaw D).IsOptimalAtTotal N a) :
    ∀ t, t ≠ best → a.count t = 0 := by
  rw [iidAllConsumedSourceModel_eq_linearized preferenceLaw D h_integrable] at hopt
  intro t ht
  exact linearized_optimal_count_eq_zero_of_strict_score_lt
    (N := N) (a := a) (t := t) (best := best) hopt
    (by
      simpa using
        mul_lt_mul_of_pos_right (hbest_strict t ht) hmean_pos)

end

end PRPKG24AccuracyDiversity

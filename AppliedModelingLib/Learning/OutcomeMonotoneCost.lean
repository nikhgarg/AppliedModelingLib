import AppliedModelingLib.Learning.StrategicResponse
import Mathlib.Data.Set.Image

/-!
# Outcome-monotone manipulation costs

This module isolates a reusable cost model for strategic classification.  A
feature has an outcome likelihood, and manipulation cost rises exactly with
strict improvements in that likelihood, with the source and destination
monotonicity conditions made explicit.

The main theorem proves that such a cost depends only on the two outcome
likelihoods.  Its canonical likelihood-level representation is defined on the
actual range of the likelihood map, so no arbitrary off-range values enter the
economic statement.

Upstream credit: the canonical representative uses Mathlib's
`Set.rangeFactorization`, `Set.rangeSplitting`, and
`Set.apply_rangeSplitting` from
[`Data/Set/Operations.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Set/Operations.lean),
at the repository's pinned Mathlib revision under Apache-2.0.  No external
proof or code is copied or ported.
-/

namespace AppliedModelingLib

/--
A nonnegative manipulation cost is outcome monotone when it is positive
exactly for strict likelihood improvements, decreasing the initial likelihood
strictly raises a positive improvement cost, and increasing the destination
likelihood strictly raises it.

The two last clauses use the order of arguments appearing in the inequalities:
`lowerInitial` has the lower likelihood and therefore the higher cost to a
common destination; `lowerFinal` is the cheaper of two improving destinations.
-/
def IsOutcomeMonotoneCost {Feature : Type*}
    (likelihood : Feature → ℝ) (cost : Feature → Feature → ℝ) : Prop :=
  (∀ initial final, 0 ≤ cost initial final) ∧
    (∀ initial final,
      0 < cost initial final ↔ likelihood initial < likelihood final) ∧
    (∀ lowerInitial higherInitial final,
      (0 < cost higherInitial final ∧
          cost higherInitial final < cost lowerInitial final) ↔
        (likelihood lowerInitial < likelihood higherInitial ∧
          likelihood higherInitial < likelihood final)) ∧
    (∀ initial lowerFinal higherFinal,
      (0 < cost initial lowerFinal ∧
          cost initial lowerFinal < cost initial higherFinal) ↔
        (likelihood initial < likelihood lowerFinal ∧
          likelihood lowerFinal < likelihood higherFinal))

/--
Multiplying an outcome-monotone cost by a strictly positive scalar preserves
the ordinal incentive comparisons that define outcome monotonicity.

The ordered-field equivalences are Mathlib's
[`mul_pos_iff_of_pos_left`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean)
and
[`mul_lt_mul_iff_of_pos_left`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean),
at the repository-pinned Mathlib revision under Apache-2.0.  No external
proof code is copied or ported.
-/
theorem IsOutcomeMonotoneCost.const_mul
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ} {scale : ℝ}
    (hscale : 0 < scale) (hcost : IsOutcomeMonotoneCost likelihood cost) :
    IsOutcomeMonotoneCost likelihood
      (fun initial final => scale * cost initial final) := by
  rcases hcost with ⟨hnonneg, hpositive, hinitial, hfinal⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro initial final
    exact mul_nonneg hscale.le (hnonneg initial final)
  · intro initial final
    rw [mul_pos_iff_of_pos_left hscale]
    exact hpositive initial final
  · intro lowerInitial higherInitial final
    constructor
    · rintro ⟨hpositiveScaled, hltScaled⟩
      exact (hinitial lowerInitial higherInitial final).mp
        ⟨(mul_pos_iff_of_pos_left hscale).mp hpositiveScaled,
          (mul_lt_mul_iff_of_pos_left hscale).mp hltScaled⟩
    · rintro hlevels
      rcases (hinitial lowerInitial higherInitial final).mpr hlevels with
        ⟨hpositive, hlt⟩
      exact ⟨(mul_pos_iff_of_pos_left hscale).mpr hpositive,
        (mul_lt_mul_iff_of_pos_left hscale).mpr hlt⟩
  · intro initial lowerFinal higherFinal
    constructor
    · rintro ⟨hpositiveScaled, hltScaled⟩
      exact (hfinal initial lowerFinal higherFinal).mp
        ⟨(mul_pos_iff_of_pos_left hscale).mp hpositiveScaled,
          (mul_lt_mul_iff_of_pos_left hscale).mp hltScaled⟩
    · rintro hlevels
      rcases (hfinal initial lowerFinal higherFinal).mpr hlevels with
        ⟨hpositive, hlt⟩
      exact ⟨(mul_pos_iff_of_pos_left hscale).mpr hpositive,
        (mul_lt_mul_iff_of_pos_left hscale).mpr hlt⟩

/-- Equal initial likelihoods induce equal costs to every fixed destination. -/
theorem IsOutcomeMonotoneCost.cost_eq_of_likelihood_eq_left
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {first second : Feature} (hlikelihood : likelihood first = likelihood second)
    (final : Feature) :
    cost first final = cost second final := by
  rcases hcost with ⟨hnonneg, hpositive, hinitial, _⟩
  rcases lt_trichotomy (cost first final) (cost second final) with
      hless | hequal | hgreater
  · have hsecondPositive : 0 < cost second final :=
      lt_of_le_of_lt (hnonneg first final) hless
    have hfirstLikelihood : likelihood first < likelihood final := by
      rw [hlikelihood]
      exact (hpositive second final).mp hsecondPositive
    have hfirstPositive : 0 < cost first final :=
      (hpositive first final).mpr hfirstLikelihood
    have hlevels :=
      (hinitial second first final).mp ⟨hfirstPositive, hless⟩
    exact (ne_of_lt hlevels.1 hlikelihood.symm).elim
  · exact hequal
  · have hfirstPositive : 0 < cost first final :=
      lt_of_le_of_lt (hnonneg second final) hgreater
    have hsecondLikelihood : likelihood second < likelihood final := by
      rw [← hlikelihood]
      exact (hpositive first final).mp hfirstPositive
    have hsecondPositive : 0 < cost second final :=
      (hpositive second final).mpr hsecondLikelihood
    have hlevels :=
      (hinitial first second final).mp ⟨hsecondPositive, hgreater⟩
    exact (ne_of_lt hlevels.1 hlikelihood).elim

/-- Equal destination likelihoods induce equal costs from every fixed initial feature. -/
theorem IsOutcomeMonotoneCost.cost_eq_of_likelihood_eq_right
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (initial : Feature) {first second : Feature}
    (hlikelihood : likelihood first = likelihood second) :
    cost initial first = cost initial second := by
  rcases hcost with ⟨hnonneg, hpositive, _, hfinal⟩
  rcases lt_trichotomy (cost initial first) (cost initial second) with
      hless | hequal | hgreater
  · have hsecondPositive : 0 < cost initial second :=
      lt_of_le_of_lt (hnonneg initial first) hless
    have hfirstLikelihood : likelihood initial < likelihood first := by
      rw [hlikelihood]
      exact (hpositive initial second).mp hsecondPositive
    have hfirstPositive : 0 < cost initial first :=
      (hpositive initial first).mpr hfirstLikelihood
    have hlevels :=
      (hfinal initial first second).mp ⟨hfirstPositive, hless⟩
    exact (ne_of_lt hlevels.2 hlikelihood).elim
  · exact hequal
  · have hfirstPositive : 0 < cost initial first :=
      lt_of_le_of_lt (hnonneg initial second) hgreater
    have hsecondLikelihood : likelihood initial < likelihood second := by
      rw [← hlikelihood]
      exact (hpositive initial first).mp hfirstPositive
    have hsecondPositive : 0 < cost initial second :=
      (hpositive initial second).mpr hsecondLikelihood
    have hlevels :=
      (hfinal initial second first).mp ⟨hsecondPositive, hgreater⟩
    exact (ne_of_lt hlevels.2 hlikelihood.symm).elim

/-- Raising the initial likelihood weakly lowers manipulation cost to a fixed destination. -/
theorem IsOutcomeMonotoneCost.cost_anti_left
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {lowerInitial higherInitial : Feature}
    (hlikelihood : likelihood lowerInitial ≤ likelihood higherInitial)
    (final : Feature) :
    cost higherInitial final ≤ cost lowerInitial final := by
  rcases lt_or_eq_of_le hlikelihood with hlt | heq
  · by_cases himproving : likelihood higherInitial < likelihood final
    · exact le_of_lt ((hcost.2.2.1 lowerInitial higherInitial final).mpr
        ⟨hlt, himproving⟩).2
    · have hzero : cost higherInitial final = 0 := by
        apply le_antisymm
        · exact le_of_not_gt ((hcost.2.1 higherInitial final).not.mpr himproving)
        · exact hcost.1 higherInitial final
      rw [hzero]
      exact hcost.1 lowerInitial final
  · exact le_of_eq (hcost.cost_eq_of_likelihood_eq_left heq final).symm

/-- Raising the destination likelihood weakly raises manipulation cost. -/
theorem IsOutcomeMonotoneCost.cost_mono_right
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (initial : Feature) {lowerFinal higherFinal : Feature}
    (hlikelihood : likelihood lowerFinal ≤ likelihood higherFinal) :
    cost initial lowerFinal ≤ cost initial higherFinal := by
  rcases lt_or_eq_of_le hlikelihood with hlt | heq
  · by_cases himproving : likelihood initial < likelihood lowerFinal
    · exact le_of_lt ((hcost.2.2.2 initial lowerFinal higherFinal).mpr
        ⟨himproving, hlt⟩).2
    · have hzero : cost initial lowerFinal = 0 := by
        apply le_antisymm
        · exact le_of_not_gt ((hcost.2.1 initial lowerFinal).not.mpr himproving)
        · exact hcost.1 initial lowerFinal
      rw [hzero]
      exact hcost.1 initial higherFinal
  · exact le_of_eq (hcost.cost_eq_of_likelihood_eq_right initial heq)

/--
Canonical cost on the attained outcome-likelihood range.  Choice of feature
representatives is harmless under `IsOutcomeMonotoneCost`, as proved below.
-/
noncomputable def outcomeLikelihoodCost {Feature : Type*}
    (likelihood : Feature → ℝ) (cost : Feature → Feature → ℝ) :
    Set.range likelihood → Set.range likelihood → ℝ :=
  fun initial final =>
    cost (Set.rangeSplitting likelihood initial)
      (Set.rangeSplitting likelihood final)

/-- The canonical likelihood-level cost reproduces the original feature-level cost. -/
@[simp] theorem outcomeLikelihoodCost_rangeFactorization
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (initial final : Feature) :
    outcomeLikelihoodCost likelihood cost
        (Set.rangeFactorization likelihood initial)
        (Set.rangeFactorization likelihood final) =
      cost initial final := by
  unfold outcomeLikelihoodCost
  have hinitial :
      likelihood
          (Set.rangeSplitting likelihood
            (Set.rangeFactorization likelihood initial)) =
        likelihood initial := by
    simpa using
      Set.apply_rangeSplitting likelihood
        (Set.rangeFactorization likelihood initial)
  have hfinal :
      likelihood
          (Set.rangeSplitting likelihood
            (Set.rangeFactorization likelihood final)) =
        likelihood final := by
    simpa using
      Set.apply_rangeSplitting likelihood
        (Set.rangeFactorization likelihood final)
  calc
    cost
        (Set.rangeSplitting likelihood
          (Set.rangeFactorization likelihood initial))
        (Set.rangeSplitting likelihood
          (Set.rangeFactorization likelihood final)) =
      cost initial
        (Set.rangeSplitting likelihood
          (Set.rangeFactorization likelihood final)) :=
      hcost.cost_eq_of_likelihood_eq_left hinitial _
    _ = cost initial final :=
      hcost.cost_eq_of_likelihood_eq_right initial hfinal

/-- Every outcome-monotone cost factors through the two attained likelihoods. -/
theorem IsOutcomeMonotoneCost.exists_likelihoodCost
    {Feature : Type*} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost) :
    ∃ likelihoodCost : Set.range likelihood → Set.range likelihood → ℝ,
      ∀ initial final,
        cost initial final =
          likelihoodCost
            (Set.rangeFactorization likelihood initial)
            (Set.rangeFactorization likelihood final) := by
  refine ⟨outcomeLikelihoodCost likelihood cost, ?_⟩
  intro initial final
  exact (outcomeLikelihoodCost_rangeFactorization hcost initial final).symm

end AppliedModelingLib

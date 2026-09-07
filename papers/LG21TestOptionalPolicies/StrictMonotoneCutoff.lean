import AppliedModelingLib.GameTheory.Choice.BinaryAE

/-!
# Strictly monotone binary cutoffs

This small analytic bridge is intentionally independent of any LG21 action
encoding.  It turns an a.e. binary best response to a continuous strictly
increasing gain function into an a.e. upper-tail rule, once the two payoff
sides are attained.  The callers must derive the gain from the literal
selected-population PBO; no posterior formula is assumed here.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory Set
open AppliedModelingLib

/-- A continuous strictly increasing gain with values weakly on both sides of
zero has a unique zero. -/
theorem lg21_exists_unique_zero_of_strictMono_continuous_crosses
    (gain : ℝ -> ℝ) (hcontinuous : Continuous gain)
    (hstrict : StrictMono gain)
    (hlow : ∃ low, gain low ≤ 0)
    (hhigh : ∃ high, 0 ≤ gain high) :
    ∃! cutoff, gain cutoff = 0 := by
  rcases hlow with ⟨low, hlow⟩
  rcases hhigh with ⟨high, hhigh⟩
  have hlowHigh : low ≤ high := by
    by_contra hnot
    have hhighLow : high < low := lt_of_not_ge hnot
    have hstrictGain : gain high < gain low := hstrict hhighLow
    linarith
  have hzero : (0 : ℝ) ∈ Set.Icc (gain low) (gain high) :=
    ⟨hlow, hhigh⟩
  rcases intermediate_value_Icc hlowHigh hcontinuous.continuousOn hzero with
    ⟨cutoff, hcutoff, hroot⟩
  refine ⟨cutoff, hroot, ?_⟩
  intro other hother
  apply hstrict.injective
  rw [hroot, hother]

/-- The sign of a strictly increasing function with a zero is exactly its
upper-tail order relative to that zero. -/
theorem lg21_nonneg_iff_ge_of_strictMono_zero
    (gain : ℝ -> ℝ) (hstrict : StrictMono gain)
    {cutoff : ℝ} (hroot : gain cutoff = 0) (value : ℝ) :
    0 ≤ gain value ↔ cutoff ≤ value := by
  constructor
  · intro hnonneg
    by_contra hnot
    have hlt : value < cutoff := lt_of_not_ge hnot
    have hnegative : gain value < 0 := by
      rw [← hroot]
      exact hstrict hlt
    exact (not_lt_of_ge hnonneg) hnegative
  · intro hge
    have hmono : gain cutoff ≤ gain value := hstrict.monotone hge
    simpa [hroot] using hmono

/-- The zero level of a strictly increasing gain is a singleton. -/
theorem lg21_zero_level_eq_singleton_of_strictMono
    (gain : ℝ -> ℝ) (hstrict : StrictMono gain)
    {cutoff : ℝ} (hroot : gain cutoff = 0) :
    {value | gain value = 0} = ({cutoff} : Set ℝ) := by
  ext value
  constructor
  · intro hvalue
    rw [Set.mem_singleton_iff]
    apply hstrict.injective
    rw [hvalue, hroot]
  · intro hvalue
    rw [Set.mem_singleton_iff] at hvalue
    subst value
    exact hroot

/-- A literal a.e. binary best response to a continuous strictly increasing
gain is the upper-tail cutoff rule whenever both payoff signs occur.  The
conclusion is a semantic action equality, not a classification by function
name. -/
theorem lg21_bool_choice_eq_decide_upperTail_ae_of_strictMono_continuous_crosses
    (law : Measure ℝ) [NoAtoms law]
    (decision : ℝ -> Bool) (gain : ℝ -> ℝ)
    (hbest : NoProfitableBinaryChoiceDeviationAE law
      (fun value => decision value = true) gain (fun _ => 0))
    (hcontinuous : Continuous gain) (hstrict : StrictMono gain)
    (hlow : ∃ low, gain low ≤ 0)
    (hhigh : ∃ high, 0 ≤ gain high) :
    ∃ cutoff : ℝ, gain cutoff = 0 ∧
      ∀ᵐ value ∂law, decision value = decide (cutoff ≤ value) := by
  rcases lg21_exists_unique_zero_of_strictMono_continuous_crosses
      gain hcontinuous hstrict hlow hhigh with ⟨cutoff, hroot, _⟩
  refine ⟨cutoff, hroot, ?_⟩
  apply bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
    decision hbest
  · intro value
    exact lg21_nonneg_iff_ge_of_strictMono_zero gain hstrict hroot value
  · rw [lg21_zero_level_eq_singleton_of_strictMono gain hstrict hroot]
    exact measure_singleton cutoff

end

end LG21TestOptionalPolicies

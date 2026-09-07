import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare

/-!
# Adaptive Compare: deterministic stopping layer

Appendix A.1 stops at the first empirical estimate outside a time-varying
confidence interval, or otherwise at the fixed maximum budget.  This file
formalizes the deterministic implication from the simultaneous confidence
event to the two Compare decisions.  The iid confidence-sequence probability
bound is the next statistical layer.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- Centered empirical preference after a positive number of comparisons. -/
noncomputable def adaptiveCenteredEstimate {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (outcome : Ω) : ℝ :=
  (∑ index ∈ Finset.range count, observation index outcome) / (count : ℝ) - 1 / 2

/-- Appendix A.1's time-varying confidence radius. -/
noncomputable def adaptiveConfidenceRadius (count : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt (Real.log (4 * (count : ℝ) ^ 2 / delta) / (2 * count : ℝ))

/-- The midpoint between Compare's lower and upper centered limits. -/
noncomputable def adaptiveCompareMidpoint (lower upper : ℝ) : ℝ := (lower + upper) / 2

/-- The source's first stopping time, or the terminal cap if no early stop occurs. -/
noncomputable def adaptiveCompareStoppingTime {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper delta : ℝ) (outcome : Ω) : ℕ :=
  by
    classical
    exact if hstop : ∃ time, time ∈ Finset.Icc 1 count ∧
        adaptiveConfidenceRadius time delta <
          |adaptiveCenteredEstimate observation time outcome -
            adaptiveCompareMidpoint lower upper|
      then Nat.find hstop
      else count

/-- The first source stopping time, when it exists, is among the inspected prefixes. -/
theorem adaptiveCompareStoppingTime_le_count {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper delta : ℝ) (outcome : Ω) :
    adaptiveCompareStoppingTime observation count lower upper delta outcome ≤ count := by
  classical
  unfold adaptiveCompareStoppingTime
  split
  · rename_i hstop
    have hstop' := hstop
    obtain ⟨time, htime⟩ := hstop
    exact (Nat.find_min' hstop' htime).trans (Finset.mem_Icc.mp htime.1).2
  · exact le_rfl

/-- Adaptive Compare follows the source's first-outside-the-interval rule. -/
noncomputable def adaptiveCompare {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper delta : ℝ) (outcome : Ω) :
    CompareDecision :=
  by
    classical
    exact if hstop : ∃ time, time ∈ Finset.Icc 1 count ∧
        adaptiveConfidenceRadius time delta <
          |adaptiveCenteredEstimate observation time outcome -
            adaptiveCompareMidpoint lower upper|
      then if adaptiveCenteredEstimate observation (Nat.find hstop) outcome ≤
        adaptiveCompareMidpoint lower upper then .lower else .upper
      else if adaptiveCenteredEstimate observation count outcome ≤
        adaptiveCompareMidpoint lower upper then .lower else .upper

/-- Under the lower hypothesis, uniform early confidence plus terminal confidence returns lower. -/
theorem adaptiveCompare_lower_of_confidence {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap delta : ℝ) (outcome : Ω)
    (hgap : trueGap ≤ lower) (hseparation : lower < upper)
    (hearly : ∀ time, time ∈ Finset.Icc 1 count →
      |adaptiveCenteredEstimate observation time outcome - trueGap| <
        adaptiveConfidenceRadius time delta)
    (hterminal : |adaptiveCenteredEstimate observation count outcome - trueGap| <
      (upper - lower) / 2) :
    adaptiveCompare observation count lower upper delta outcome = .lower := by
  classical
  unfold adaptiveCompare
  split
  · rename_i hstop
    apply if_pos
    by_contra hnotLower
    have htime := Nat.find_spec hstop
    have hupper : adaptiveCompareMidpoint lower upper <
        adaptiveCenteredEstimate observation (Nat.find hstop) outcome :=
      lt_of_not_ge hnotLower
    have hthreshold := htime.2
    rw [abs_of_pos (sub_pos.mpr hupper)] at hthreshold
    have herror : adaptiveCenteredEstimate observation (Nat.find hstop) outcome - trueGap <
        adaptiveConfidenceRadius (Nat.find hstop) delta :=
      lt_of_le_of_lt (le_abs_self _) (hearly _ htime.1)
    have hmid_lt_true : adaptiveCompareMidpoint lower upper < trueGap := by
      linarith
    unfold adaptiveCompareMidpoint at hmid_lt_true
    linarith
  · rename_i hstop
    apply if_pos
    have herror : adaptiveCenteredEstimate observation count outcome - trueGap <
        (upper - lower) / 2 :=
      lt_of_le_of_lt (le_abs_self _) hterminal
    unfold adaptiveCompareMidpoint
    linarith

/--
Appendix A.2's lower-hypothesis route only needs the one-sided upper
confidence inequalities at early and terminal times.
-/
theorem adaptiveCompare_lower_of_upperConfidence {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap delta : ℝ) (outcome : Ω)
    (hgap : trueGap ≤ lower) (hseparation : lower < upper)
    (hearly : ∀ time, time ∈ Finset.Icc 1 count →
      adaptiveCenteredEstimate observation time outcome - trueGap <
        adaptiveConfidenceRadius time delta)
    (hterminal : adaptiveCenteredEstimate observation count outcome - trueGap <
      (upper - lower) / 2) :
    adaptiveCompare observation count lower upper delta outcome = .lower := by
  classical
  unfold adaptiveCompare
  split
  · rename_i hstop
    apply if_pos
    by_contra hnotLower
    have htime := Nat.find_spec hstop
    have hupper : adaptiveCompareMidpoint lower upper <
        adaptiveCenteredEstimate observation (Nat.find hstop) outcome :=
      lt_of_not_ge hnotLower
    have hthreshold := htime.2
    rw [abs_of_pos (sub_pos.mpr hupper)] at hthreshold
    have hmid_lt_true : adaptiveCompareMidpoint lower upper < trueGap := by
      linarith [hearly _ htime.1]
    unfold adaptiveCompareMidpoint at hmid_lt_true
    linarith
  · rename_i hstop
    apply if_pos
    unfold adaptiveCompareMidpoint
    linarith

/-- Under the upper hypothesis, uniform early confidence plus terminal confidence returns upper. -/
theorem adaptiveCompare_upper_of_confidence {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap delta : ℝ) (outcome : Ω)
    (hgap : upper ≤ trueGap) (hseparation : lower < upper)
    (hearly : ∀ time, time ∈ Finset.Icc 1 count →
      |adaptiveCenteredEstimate observation time outcome - trueGap| <
        adaptiveConfidenceRadius time delta)
    (hterminal : |adaptiveCenteredEstimate observation count outcome - trueGap| <
      (upper - lower) / 2) :
    adaptiveCompare observation count lower upper delta outcome = .upper := by
  classical
  unfold adaptiveCompare
  split
  · rename_i hstop
    apply if_neg
    intro hnotUpper
    have htime := Nat.find_spec hstop
    have hthreshold := htime.2
    rw [abs_of_nonpos (sub_nonpos.mpr hnotUpper)] at hthreshold
    have herror : trueGap - adaptiveCenteredEstimate observation (Nat.find hstop) outcome <
        adaptiveConfidenceRadius (Nat.find hstop) delta := by
      have hleft := (abs_lt.mp (hearly _ htime.1)).1
      linarith
    have htrue_lt_mid : trueGap < adaptiveCompareMidpoint lower upper := by
      linarith
    unfold adaptiveCompareMidpoint at htrue_lt_mid
    linarith
  · rename_i hstop
    apply if_neg
    intro hnotUpper
    have hleft := (abs_lt.mp hterminal).1
    unfold adaptiveCompareMidpoint at hnotUpper
    linarith

/-- Appendix A.2's symmetric one-sided route under the upper hypothesis. -/
theorem adaptiveCompare_upper_of_lowerConfidence {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap delta : ℝ) (outcome : Ω)
    (hgap : upper ≤ trueGap) (hseparation : lower < upper)
    (hearly : ∀ time, time ∈ Finset.Icc 1 count →
      trueGap - adaptiveCenteredEstimate observation time outcome <
        adaptiveConfidenceRadius time delta)
    (hterminal : trueGap - adaptiveCenteredEstimate observation count outcome <
      (upper - lower) / 2) :
    adaptiveCompare observation count lower upper delta outcome = .upper := by
  classical
  unfold adaptiveCompare
  split
  · rename_i hstop
    apply if_neg
    intro hnotUpper
    have htime := Nat.find_spec hstop
    have hthreshold := htime.2
    rw [abs_of_nonpos (sub_nonpos.mpr hnotUpper)] at hthreshold
    have htrue_lt_mid : trueGap < adaptiveCompareMidpoint lower upper := by
      linarith [hearly _ htime.1]
    unfold adaptiveCompareMidpoint at htrue_lt_mid
    linarith
  · rename_i hstop
    apply if_neg
    intro hnotUpper
    unfold adaptiveCompareMidpoint at hnotUpper
    linarith

end FalahatgarEtAl2017MaxingRanking

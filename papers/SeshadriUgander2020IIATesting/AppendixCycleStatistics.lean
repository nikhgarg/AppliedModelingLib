import SeshadriUgander2020IIATesting.AlternatingCycles

/-!
# Cycle-partition statistics

These finite identities and bounds are the numerical part of Appendix Lemma 10
of Seshadri--Ugander (2020).  They are deliberately stated for an arbitrary
full `CycleDecomposition`; the separate graph construction supplies its
length bounds.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- A full edge partition has total cycle length equal to the paper's
incidence count `d`. -/
theorem sum_length_eq_incidenceCount :
    (∑ cycle : D.Cycle, D.length cycle) = F.incidenceCount := by
  calc
    (∑ cycle : D.Cycle, D.length cycle) =
        Fintype.card (Sigma fun cycle => Fin (D.length cycle)) := by simp
    _ = Fintype.card F.Observation := Fintype.card_congr D.edgeEquiv
    _ = F.incidenceCount := F.observation_card

/-- If every cycle in a full decomposition has length at most `maxLength`,
then the source average length `μ(σ)` is at most `maxLength`. -/
theorem cycleMean_le_of_forall_length_le (maxLength : ℕ)
    (hmax : ∀ cycle : D.Cycle, D.length cycle ≤ maxLength) :
    D.cycleMean ≤ maxLength := by
  have hcountPos : (0 : ℝ) < Fintype.card D.Cycle := by
    exact_mod_cast D.cycle_card_pos
  have htotal : (F.incidenceCount : ℝ) =
      ∑ cycle : D.Cycle, (D.length cycle : ℝ) := by
    exact_mod_cast D.sum_length_eq_incidenceCount.symm
  have hsum : (∑ cycle : D.Cycle, (D.length cycle : ℝ)) ≤
      ∑ _cycle : D.Cycle, (maxLength : ℝ) := by
    apply Finset.sum_le_sum
    intro cycle _
    exact_mod_cast hmax cycle
  unfold cycleMean
  rw [htotal]
  apply (div_le_iff₀ hcountPos).2
  simpa [mul_comm] using hsum

/-- Any positive lower bound on the number of cycles gives the corresponding
upper bound on the source mean `μ(σ) = d / |σ|`. -/
theorem cycleMean_le_of_cycle_card_lower (cycleCountLower : ℝ)
    (hlowerPos : 0 < cycleCountLower)
    (hlower : cycleCountLower ≤ Fintype.card D.Cycle) :
    D.cycleMean ≤ (F.incidenceCount : ℝ) / cycleCountLower := by
  have hincidenceNonneg : (0 : ℝ) ≤ F.incidenceCount := by positivity
  have hcycleCardPos : (0 : ℝ) < Fintype.card D.Cycle := by
    exact_mod_cast D.cycle_card_pos
  unfold cycleMean
  apply (div_le_div_iff₀ hcycleCardPos hlowerPos).2
  nlinarith

/-- If every cycle in a full decomposition has length at most `maxLength`,
then the source dispersion statistic `α(σ)` is at most `maxLength`. -/
theorem cycleDispersion_le_of_forall_length_le (maxLength : ℕ)
    (hmax : ∀ cycle : D.Cycle, D.length cycle ≤ maxLength) :
    CycleMixture.cycleDispersion F.incidenceCount D.length ≤ maxLength := by
  have hincidencePos : (0 : ℝ) < F.incidenceCount := by
    exact_mod_cast F.incidenceCount_pos
  have htotal : (F.incidenceCount : ℝ) =
      ∑ cycle : D.Cycle, (D.length cycle : ℝ) := by
    exact_mod_cast D.sum_length_eq_incidenceCount.symm
  have hterm : ∀ cycle : D.Cycle,
      (D.length cycle : ℝ) ^ 2 ≤ (maxLength : ℝ) * D.length cycle := by
    intro cycle
    have hlengthNonneg : (0 : ℝ) ≤ D.length cycle := by positivity
    have hlengthLe : (D.length cycle : ℝ) ≤ maxLength := by
      exact_mod_cast hmax cycle
    nlinarith
  have hsum : (∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2) ≤
      (maxLength : ℝ) * F.incidenceCount := by
    calc
      (∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2) ≤
          ∑ cycle : D.Cycle, (maxLength : ℝ) * D.length cycle := by
        apply Finset.sum_le_sum
        intro cycle _
        exact hterm cycle
      _ = (maxLength : ℝ) * ∑ cycle : D.Cycle, (D.length cycle : ℝ) := by
        rw [Finset.mul_sum]
      _ = (maxLength : ℝ) * F.incidenceCount := by rw [← htotal]
  unfold CycleMixture.cycleDispersion
  calc
    (1 / (F.incidenceCount : ℝ)) *
        ∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2 ≤
        (1 / (F.incidenceCount : ℝ)) * ((maxLength : ℝ) * F.incidenceCount) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = maxLength := by
      field_simp [ne_of_gt hincidencePos]

/-- Numerical data for a cycle partition with a short-cycle bulk and a
bounded exceptional part.  The graph construction, not this structure,
supplies the displayed bounds in Appendix Lemma 10. -/
structure TwoTierCycleBounds where
  exceptional : Finset D.Cycle
  shortBound : ℝ
  longBound : ℝ
  exceptionalMassBound : ℝ
  shortBound_nonneg : 0 ≤ shortBound
  short_le_long : shortBound ≤ longBound
  short_length_le : ∀ cycle : D.Cycle, cycle ∉ exceptional →
    (D.length cycle : ℝ) ≤ shortBound
  exceptional_length_le : ∀ cycle : D.Cycle, cycle ∈ exceptional →
    (D.length cycle : ℝ) ≤ longBound
  exceptional_mass_le :
    (∑ cycle ∈ exceptional, (D.length cycle : ℝ)) ≤ exceptionalMassBound

namespace TwoTierCycleBounds

variable (B : D.TwoTierCycleBounds)

/-- The two-tier length data bounds the sum of squared cycle lengths. -/
theorem sum_sq_length_le :
    (∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2) ≤
      B.shortBound * F.incidenceCount +
        (B.longBound - B.shortBound) * B.exceptionalMassBound := by
  classical
  let exceptionalWeight : D.Cycle → ℝ := fun cycle =>
    if cycle ∈ B.exceptional then D.length cycle else 0
  have hlengthNonneg : ∀ cycle : D.Cycle, 0 ≤ (D.length cycle : ℝ) := by
    intro cycle
    positivity
  have hterm : ∀ cycle : D.Cycle,
      (D.length cycle : ℝ) ^ 2 ≤ B.shortBound * D.length cycle +
        (B.longBound - B.shortBound) * exceptionalWeight cycle := by
    intro cycle
    by_cases hcycle : cycle ∈ B.exceptional
    · simp only [exceptionalWeight, if_pos hcycle]
      have hlength := B.exceptional_length_le cycle hcycle
      nlinarith [hlengthNonneg cycle]
    · simp only [exceptionalWeight, if_neg hcycle]
      have hlength := B.short_length_le cycle hcycle
      nlinarith [hlengthNonneg cycle]
  have hweight : (∑ cycle : D.Cycle, exceptionalWeight cycle) =
      ∑ cycle ∈ B.exceptional, (D.length cycle : ℝ) := by
    unfold exceptionalWeight
    rw [← Finset.sum_filter]
    simp
  have hraw : (∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2) ≤
      B.shortBound * (∑ cycle : D.Cycle, (D.length cycle : ℝ)) +
        (B.longBound - B.shortBound) *
          (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) := by
    calc
      (∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2) ≤
          ∑ cycle : D.Cycle, (B.shortBound * D.length cycle +
            (B.longBound - B.shortBound) * exceptionalWeight cycle) := by
        apply Finset.sum_le_sum
        intro cycle _
        exact hterm cycle
      _ = B.shortBound * (∑ cycle : D.Cycle, (D.length cycle : ℝ)) +
          (B.longBound - B.shortBound) * (∑ cycle : D.Cycle, exceptionalWeight cycle) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = B.shortBound * (∑ cycle : D.Cycle, (D.length cycle : ℝ)) +
          (B.longBound - B.shortBound) *
            (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) := by rw [hweight]
  have hcoeff : 0 ≤ B.longBound - B.shortBound := sub_nonneg.mpr B.short_le_long
  calc
    (∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2) ≤
        B.shortBound * (∑ cycle : D.Cycle, (D.length cycle : ℝ)) +
          (B.longBound - B.shortBound) *
            (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) := hraw
    _ ≤ B.shortBound * (∑ cycle : D.Cycle, (D.length cycle : ℝ)) +
          (B.longBound - B.shortBound) * B.exceptionalMassBound := by
      gcongr
      exact B.exceptional_mass_le
    _ = B.shortBound * F.incidenceCount +
          (B.longBound - B.shortBound) * B.exceptionalMassBound := by
      rw [← (D.sum_length_eq_incidenceCount :
        (∑ cycle : D.Cycle, D.length cycle) = F.incidenceCount)]
      norm_cast

/-- The source dispersion statistic obeys the mixed short/long bound
`α ≤ L + (M-L)R/d`. -/
theorem cycleDispersion_le :
    CycleMixture.cycleDispersion F.incidenceCount D.length ≤
      B.shortBound +
        ((B.longBound - B.shortBound) * B.exceptionalMassBound) /
          F.incidenceCount := by
  have hincidencePos : (0 : ℝ) < F.incidenceCount := by
    exact_mod_cast F.incidenceCount_pos
  unfold CycleMixture.cycleDispersion
  calc
    (1 / (F.incidenceCount : ℝ)) *
        ∑ cycle : D.Cycle, (D.length cycle : ℝ) ^ 2 ≤
        (1 / (F.incidenceCount : ℝ)) *
          (B.shortBound * F.incidenceCount +
            (B.longBound - B.shortBound) * B.exceptionalMassBound) :=
      mul_le_mul_of_nonneg_left B.sum_sq_length_le (by positivity)
    _ = B.shortBound +
          ((B.longBound - B.shortBound) * B.exceptionalMassBound) /
            F.incidenceCount := by
      field_simp [ne_of_gt hincidencePos]

/-- For the actual exceptional mass `r`, the short and exceptional caps give
the lower count `(d-r)/L + r/M` used in the Appendix-Lemma-10 mean bound. -/
theorem cycle_card_lower_of_exceptional_mass
    (hshortPos : 0 < B.shortBound) (hlongPos : 0 < B.longBound) :
    ((F.incidenceCount : ℝ) -
        ∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) / B.shortBound +
      (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) / B.longBound ≤
        Fintype.card D.Cycle := by
  classical
  let shortCycles : Finset D.Cycle := Finset.univ \ B.exceptional
  have hshortSum : (∑ cycle ∈ shortCycles, (D.length cycle : ℝ)) ≤
      B.shortBound * shortCycles.card := by
    calc
      (∑ cycle ∈ shortCycles, (D.length cycle : ℝ)) ≤
          ∑ _cycle ∈ shortCycles, B.shortBound := by
        apply Finset.sum_le_sum
        intro cycle hcycle
        exact B.short_length_le cycle (by
          simpa [shortCycles] using hcycle)
      _ = B.shortBound * shortCycles.card := by simp [mul_comm]
  have hexceptionalSum :
      (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) ≤
        B.longBound * B.exceptional.card := by
    calc
      (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) ≤
          ∑ _cycle ∈ B.exceptional, B.longBound := by
        apply Finset.sum_le_sum
        intro cycle hcycle
        exact B.exceptional_length_le cycle hcycle
      _ = B.longBound * B.exceptional.card := by simp [mul_comm]
  have hshortCount :
      (∑ cycle ∈ shortCycles, (D.length cycle : ℝ)) / B.shortBound ≤
        shortCycles.card := by
    apply (div_le_iff₀ hshortPos).2
    simpa [mul_comm] using hshortSum
  have hexceptionalCount :
      (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) / B.longBound ≤
        B.exceptional.card := by
    apply (div_le_iff₀ hlongPos).2
    simpa [mul_comm] using hexceptionalSum
  have hsumSplit : (∑ cycle : D.Cycle, (D.length cycle : ℝ)) =
      (∑ cycle ∈ shortCycles, (D.length cycle : ℝ)) +
        ∑ cycle ∈ B.exceptional, (D.length cycle : ℝ) := by
    rw [← Finset.sum_sdiff (show B.exceptional ⊆ Finset.univ by simp)]
  have hcardSplit : (shortCycles.card : ℝ) + B.exceptional.card =
      Fintype.card D.Cycle := by
    have hcardNat : shortCycles.card + B.exceptional.card = Fintype.card D.Cycle := by
      simpa [shortCycles] using
        Finset.card_sdiff_add_card_eq_card (show B.exceptional ⊆ Finset.univ by simp)
    exact_mod_cast hcardNat
  have htotal : (F.incidenceCount : ℝ) =
      ∑ cycle : D.Cycle, (D.length cycle : ℝ) := by
    exact_mod_cast D.sum_length_eq_incidenceCount.symm
  calc
    ((F.incidenceCount : ℝ) -
          ∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) / B.shortBound +
        (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) / B.longBound =
        (∑ cycle ∈ shortCycles, (D.length cycle : ℝ)) / B.shortBound +
          (∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)) / B.longBound := by
      rw [htotal, hsumSplit]
      ring
    _ ≤ (shortCycles.card : ℝ) + B.exceptional.card :=
      add_le_add hshortCount hexceptionalCount
    _ = Fintype.card D.Cycle := hcardSplit

/-- Replacing the actual exceptional mass by any larger budget preserves the
cycle-count lower bound when the exceptional cap is at least the short cap. -/
theorem cycle_card_lower
    (hshortPos : 0 < B.shortBound) (hlongPos : 0 < B.longBound) :
    ((F.incidenceCount : ℝ) - B.exceptionalMassBound) / B.shortBound +
      B.exceptionalMassBound / B.longBound ≤ Fintype.card D.Cycle := by
  let exceptionalMass : ℝ :=
    ∑ cycle ∈ B.exceptional, (D.length cycle : ℝ)
  have hmass : exceptionalMass ≤ B.exceptionalMassBound := by
    exact B.exceptional_mass_le
  have hfactorNonneg : 0 ≤
      (B.exceptionalMassBound - exceptionalMass) *
        (B.longBound - B.shortBound) :=
    mul_nonneg (sub_nonneg.mpr hmass) (sub_nonneg.mpr B.short_le_long)
  have hidentity :
      ((F.incidenceCount : ℝ) - exceptionalMass) / B.shortBound +
          exceptionalMass / B.longBound -
        (((F.incidenceCount : ℝ) - B.exceptionalMassBound) / B.shortBound +
          B.exceptionalMassBound / B.longBound) =
        ((B.exceptionalMassBound - exceptionalMass) *
          (B.longBound - B.shortBound)) /
          (B.shortBound * B.longBound) := by
    field_simp [ne_of_gt hshortPos, ne_of_gt hlongPos]
    ring
  have hbudget :
      ((F.incidenceCount : ℝ) - B.exceptionalMassBound) / B.shortBound +
          B.exceptionalMassBound / B.longBound ≤
        ((F.incidenceCount : ℝ) - exceptionalMass) / B.shortBound +
          exceptionalMass / B.longBound := by
    rw [← sub_nonneg]
    rw [hidentity]
    exact div_nonneg hfactorNonneg (mul_nonneg hshortPos.le hlongPos.le)
  apply hbudget.trans
  simpa [exceptionalMass] using
    cycle_card_lower_of_exceptional_mass (D := D) B hshortPos hlongPos

/-- The corrected positive-denominator mean bound obtained from two-tier
cycle data.  The explicit positivity premise is exactly what the source's
printed unconditional rational branch omitted. -/
theorem cycleMean_le
    (hshortPos : 0 < B.shortBound) (hlongPos : 0 < B.longBound)
    (hcountPos : 0 <
      ((F.incidenceCount : ℝ) - B.exceptionalMassBound) / B.shortBound +
        B.exceptionalMassBound / B.longBound) :
    D.cycleMean ≤ (F.incidenceCount : ℝ) /
      (((F.incidenceCount : ℝ) - B.exceptionalMassBound) / B.shortBound +
        B.exceptionalMassBound / B.longBound) :=
  cycleMean_le_of_cycle_card_lower (D := D) _ hcountPos
    (cycle_card_lower (D := D) B hshortPos hlongPos)

end TwoTierCycleBounds

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting

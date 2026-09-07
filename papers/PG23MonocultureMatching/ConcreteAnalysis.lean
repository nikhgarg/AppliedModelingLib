import PG23MonocultureMatching.ConcreteStability
import PG23MonocultureMatching.MainTheorems
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# PG23 Concrete Probability and Welfare Analysis

This module connects the literal continuum cutoff model to PG23's displayed
conditional crossing probabilities.  It keeps the source corrections visible:
score-level nullity handles aggregate cutoff ties, while nonatomic primitive
laws are used only where the printed pointwise or threshold argument needs
them.

Source anchors: `source_tex/proofs.tex:125-165,168-268,272-325`.
-/

namespace PG23MonocultureMatching

open Filter MeasureTheory Set
open AppliedModelingLib.Matching
open scoped Topology BigOperators

universe u v

/-- Fubini for the real-valued probability of measurable product sections. -/
theorem pg23_integral_sectionProbability_eq_productProbability
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (∫ x, ν.real (Prod.mk x ⁻¹' s) ∂μ) = (μ.prod ν).real s := by
  classical
  let f : α × β -> ℝ := s.indicator fun _ => 1
  have hf : Integrable f (μ.prod ν) := by
    exact (integrable_const (μ := μ.prod ν) (c := (1 : ℝ))).indicator hs
  have hsection (x : α) :
      (∫ y, f (x, y) ∂ν) = ν.real (Prod.mk x ⁻¹' s) := by
    have hsx : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
    have hfun : (fun y : β => f (x, y)) =
        (Prod.mk x ⁻¹' s).indicator (fun _ => (1 : ℝ)) := by
      funext y
      change (if (x, y) ∈ s then 1 else 0) = (if (x, y) ∈ s then 1 else 0)
      rfl
    rw [hfun]
    simpa [Measure.real] using
      (MeasureTheory.integral_indicator_one (μ := ν)
        (s := Prod.mk x ⁻¹' s) hsx)
  have hprod :
      (∫ z, f z ∂μ.prod ν) = (μ.prod ν).real s := by
    simpa [f, Measure.real] using
      (MeasureTheory.integral_indicator_one (μ := μ.prod ν) (s := s) hs)
  calc
    (∫ x, ν.real (Prod.mk x ⁻¹' s) ∂μ) =
        ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact (hsection x).symm
    _ = ∫ z, f z ∂μ.prod ν := (MeasureTheory.integral_prod f hf).symm
    _ = (μ.prod ν).real s := hprod

/-- Literal monoculture clearing gives the paper's strict crossing integral. -/
theorem pg23MonocultureCommonCutoff_strictCrossingIntegral_eq_supply
    {n : ℕ} [NeZero n]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
    {S p : ℝ}
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (n : ℝ)) (fun _ : Fin n => p)) :
    (∫ v : ℝ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        v (fun _ : Fin n => p) college ∂valueLaw) = S := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  have hstrict := pg23SourceMarketClearing_commonCutoff_strictTail_eq_supply
    (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw)
    (s := S) (p := p) hlevel (by simpa using hclear)
  rw [pg23MonocultureSourceMaxScoreLaw_eq_sumLaw] at hstrict
  let event : Set (ℝ × ℝ) := {z | p < z.1 + z.2}
  have hevent : MeasurableSet event := by
    exact measurableSet_lt measurable_const (by fun_prop)
  have hproduct : (valueLaw.prod noiseLaw).real event = S := by
    have hmap := map_measureReal_apply
      (μ := valueLaw.prod noiseLaw)
      (f := fun z : ℝ × ℝ => z.1 + z.2)
      (s := Ioi p)
      (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 + z.2)) measurableSet_Ioi
    have hpreimage :
        (fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Ioi p = event := by
      ext z
      rfl
    rw [hpreimage] at hmap
    rw [← hmap]
    exact hstrict
  calc
    (∫ v : ℝ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => p) college ∂valueLaw) =
        ∫ v : ℝ, noiseLaw.real (Prod.mk v ⁻¹' event) ∂valueLaw := by
      apply integral_congr_ae
      filter_upwards with v
      rw [AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass]
      unfold AppliedModelingLib.Probability.upperTailMass
      congr 1
      ext x
      simp only [event, mem_preimage, mem_setOf_eq, mem_Ioi]
      constructor <;> intro h <;> linarith
    _ = (valueLaw.prod noiseLaw).real event :=
      pg23_integral_sectionProbability_eq_productProbability
        valueLaw noiseLaw hevent
    _ = S := hproduct

/-- The maximum-noise tail is exactly the strict all-college crossing event. -/
theorem pg23PolycultureMaxNoiseLaw_upperTail_eq_crossingProbability
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (v p : ℝ) :
    (pg23PolycultureMaxNoiseLaw (College := Fin n) noiseLaw).real (Ioi (p - v)) =
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) Finset.univ v (fun _ => p) := by
  unfold pg23PolycultureMaxNoiseLaw
  rw [map_measureReal_apply
    (μ := Measure.pi (fun _ : Fin n => noiseLaw))
    (f := pg23PolycultureMaxNoise (College := Fin n))
    (s := Ioi (p - v)) pg23PolycultureMaxNoise_measurable measurableSet_Ioi]
  unfold AppliedModelingLib.Matching.cutoffCrossingProbability
  congr 1
  ext noise
  simp only [mem_preimage, mem_Ioi, pg23PolycultureMaxNoise,
    AppliedModelingLib.Matching.cutoffCrossedOn, AppliedModelingLib.Matching.noisyScore,
    Finset.lt_sup'_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro c
  constructor <;> intro h <;> linarith

/-- Literal polyculture clearing gives the paper's strict crossing integral. -/
theorem pg23PolycultureCommonCutoff_strictCrossingIntegral_eq_supply
    {n : ℕ} [NeZero n]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
    {S p : ℝ}
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (n : ℝ)) (fun _ : Fin n => p)) :
    (∫ v : ℝ,
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) Finset.univ
        v (fun _ : Fin n => p) ∂valueLaw) = S := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  let maxNoiseLaw := pg23PolycultureMaxNoiseLaw (College := Fin n) noiseLaw
  letI : IsProbabilityMeasure maxNoiseLaw :=
    pg23PolycultureMaxNoiseLaw_isProbabilityMeasure noiseLaw
  have hstrict := pg23SourceMarketClearing_commonCutoff_strictTail_eq_supply
    (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw)
    (s := S) (p := p) hlevel (by simpa using hclear)
  rw [pg23PolycultureSourceMaxScoreLaw_eq_sumMaxNoiseLaw] at hstrict
  let event : Set (ℝ × ℝ) := {z | p < z.1 + z.2}
  have hevent : MeasurableSet event := by
    exact measurableSet_lt measurable_const (by fun_prop)
  have hproduct : (valueLaw.prod maxNoiseLaw).real event = S := by
    have hmap := map_measureReal_apply
      (μ := valueLaw.prod maxNoiseLaw)
      (f := fun z : ℝ × ℝ => z.1 + z.2)
      (s := Ioi p)
      (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 + z.2)) measurableSet_Ioi
    have hpreimage :
        (fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Ioi p = event := by
      ext z
      rfl
    rw [hpreimage] at hmap
    rw [← hmap]
    exact hstrict
  calc
    (∫ v : ℝ,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) Finset.univ
          v (fun _ : Fin n => p) ∂valueLaw) =
        ∫ v : ℝ, maxNoiseLaw.real (Prod.mk v ⁻¹' event) ∂valueLaw := by
      apply integral_congr_ae
      filter_upwards with v
      have hsection : Prod.mk v ⁻¹' event = Ioi (p - v) := by
        ext x
        simp only [event, mem_preimage, mem_setOf_eq, mem_Ioi]
        constructor <;> intro h <;> linarith
      rw [hsection]
      exact (pg23PolycultureMaxNoiseLaw_upperTail_eq_crossingProbability
        noiseLaw v p).symm
    _ = (valueLaw.prod maxNoiseLaw).real event :=
      pg23_integral_sectionProbability_eq_productProbability
        valueLaw maxNoiseLaw hevent
    _ = S := hproduct

/-- Monoculture's common scalar clearing cutoff is independent of market size. -/
theorem pg23MonocultureCommonCutoff_eq_across_marketSizes
    {m n : ℕ}
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {S pm pn : ℝ} (hS : 0 < S ∧ S < 1)
    (hm : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin (m + 1)) valueLaw noiseLaw))
      (fun _ : Fin (m + 1) => S / (Fintype.card (Fin (m + 1)) : ℝ))
      (fun _ : Fin (m + 1) => pm))
    (hn : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => pn)) :
    pm = pn := by
  let sumLaw := Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
    (valueLaw.prod noiseLaw)
  letI : IsProbabilityMeasure sumLaw := by
    dsimp [sumLaw]
    exact Measure.isProbabilityMeasure_map
      (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 + z.2)).aemeasurable
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw
        (College := Fin (m + 1)) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  have hconnected := pg23MonocultureSourceMaxScoreLaw_connectedSupport
    (College := Fin (m + 1)) valueLaw noiseLaw hvalue hnoise
  have htm := pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
    (pg23MonocultureTypeLaw (College := Fin (m + 1)) valueLaw noiseLaw) hm
  have htn := pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
    (pg23MonocultureTypeLaw (College := Fin (n + 1)) valueLaw noiseLaw) hn
  rw [pg23MonocultureSourceMaxScoreLaw_eq_sumLaw] at hconnected htm htn
  exact pg23_cutoff_eq_of_connectedSupport_weakTail_eq
    sumLaw hconnected hS.1 hS.2 htm htn

/--
PG23 Theorem 1(i), plus the source's monoculture-invariance clause, for the
literal continuum model.  The conclusions are exposed directly rather than
through a theorem-facing conclusion package.
-/
theorem pg23Theorem1_probability_of_literal_commonCutoffClearing
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {monoCutoff polyCutoff : ℕ -> ℝ}
    {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hconc : maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hmono_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hpoly_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hmono_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => monoCutoff n))
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n)) :
    (∀ v : ℝ, v < vS ->
      Tendsto
        (fun n : ℕ => AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
          v (fun _ : Fin (n + 1) => polyCutoff n))
        atTop (nhds 0)) ∧
    (∀ v : ℝ, vS < v ->
      Tendsto
        (fun n : ℕ => AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
          v (fun _ : Fin (n + 1) => polyCutoff n))
        atTop (nhds 1)) ∧
    (∀ v : ℝ, ∀ m n : ℕ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) 0 =
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) 0) := by
  have hmass :=
    pg23_twoSidedPositiveIntervalMass_of_connectedSupport_noAtoms_upperTailMass_eq
      valueLaw hvalue hS htail
  have hpoly_integral : ∀ n : ℕ,
      (∫ v : ℝ, AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
        v (fun _ : Fin (n + 1) => polyCutoff n) ∂valueLaw) = S := by
    intro n
    exact pg23PolycultureCommonCutoff_strictCrossingIntegral_eq_supply
      valueLaw noiseLaw (hpoly_level n) (by simpa using hpoly_clear n)
  have hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n := by
    intro m n
    exact pg23MonocultureCommonCutoff_eq_across_marketSizes
      valueLaw noiseLaw hvalue hnoise hS (hmono_clear m) (hmono_clear n)
  have hwisdom :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
      valueLaw noiseLaw (fun _ => 0) hconc
      (⟨htail⟩ : AppliedModelingLib.Probability.UpperTailThresholdCertificate valueLaw S vS)
      hmass hpoly_integral hmono_cutoff
  simpa only [theorem1_wisdomProbabilityConclusion] using hwisdom

/-- An interior support threshold has a genuinely fractional strict upper tail. -/
theorem pg23_upperTailMass_mem_Ioo_of_mem_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    {x : ℝ} (hx : x ∈ interior law.support) :
    AppliedModelingLib.Probability.upperTailMass law x ∈ Ioo (0 : ℝ) 1 := by
  have hlocal := pg23_twoSidedPositiveIntervalMass_of_mem_interior_support law hx
  have hright_measure : 0 < law (Ioi x) := by
    apply lt_of_lt_of_le (hlocal.right_pos 1 zero_lt_one)
    apply measure_mono
    intro z hz
    exact hz.1
  have hleft_measure : 0 < law (Iic x) := by
    apply lt_of_lt_of_le (hlocal.left_pos 1 zero_lt_one)
    apply measure_mono
    intro z hz
    exact hz.2
  have htail_pos : 0 < AppliedModelingLib.Probability.upperTailMass law x := by
    exact ENNReal.toReal_pos hright_measure.ne' (measure_ne_top law _)
  have hlower_pos : 0 < AppliedModelingLib.Probability.lowerCDFMass law x := by
    exact ENNReal.toReal_pos hleft_measure.ne' (measure_ne_top law _)
  have hsum := AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one law x
  exact ⟨htail_pos, by linarith⟩

/--
Equal mass with an upper-tail step and positive off-threshold fractional mass
forces a positive high-value region where admission is still below one.
-/
theorem pg23_highValueBelowOneRegion_measure_pos_of_sameMass_fractional
    (law : Measure ℝ) [IsProbabilityMeasure law]
    {threshold : ℝ} {q : ℝ -> ℝ}
    (hq_integrable : Integrable q law)
    (hstep_integrable :
      Integrable (fun v : ℝ => if threshold < v then (1 : ℝ) else 0) law)
    (hq_bounds : ∀ v : ℝ, 0 ≤ q v ∧ q v ≤ 1)
    (hsame_mass :
      (∫ v : ℝ, q v ∂law) =
        ∫ v : ℝ, (if threshold < v then (1 : ℝ) else 0) ∂law)
    (hfractional :
      0 < law {v : ℝ | v ≠ threshold ∧ 0 < q v ∧ q v < 1}) :
    0 < law {v : ℝ | threshold < v ∧ q v < 1} := by
  let step : ℝ -> ℝ := fun v => if threshold < v then 1 else 0
  let region : Set ℝ := {v | threshold < v ∧ q v < 1}
  by_contra hnot
  have hregion_zero : law region = 0 := by
    exact nonpos_iff_eq_zero.mp (le_of_not_gt hnot)
  have hnot_region : ∀ᵐ v : ℝ ∂law, v ∉ region := by
    exact compl_mem_ae_iff.mpr hregion_zero
  have hdiff_nonneg : 0 ≤ᵐ[law] fun v => q v - step v := by
    filter_upwards [hnot_region] with v hv
    by_cases hhigh : threshold < v
    · have hnot_lt : ¬ q v < 1 := by
        intro hq
        exact hv ⟨hhigh, hq⟩
      have hq_eq : q v = 1 :=
        le_antisymm (hq_bounds v).2 (le_of_not_gt hnot_lt)
      simp [step, hhigh, hq_eq]
    · simp [step, hhigh, (hq_bounds v).1]
  let fractional : Set ℝ :=
    {v | v ≠ threshold ∧ 0 < q v ∧ q v < 1}
  have hfractional_diff : 0 < law (fractional \ region) := by
    rw [measure_diff_null hregion_zero]
    exact hfractional
  have hsupport_subset :
      fractional \ region ⊆ Function.support (fun v => q v - step v) := by
    intro v hv
    have hnot_high : ¬ threshold < v := by
      intro hhigh
      exact hv.2 ⟨hhigh, hv.1.2.2⟩
    change q v - step v ≠ 0
    simpa [step, hnot_high] using ne_of_gt hv.1.2.1
  have hsupport_pos :
      0 < law (Function.support (fun v => q v - step v)) :=
    lt_of_lt_of_le hfractional_diff (measure_mono hsupport_subset)
  have hdiff_integrable : Integrable (fun v => q v - step v) law := by
    exact hq_integrable.sub (by simpa [step] using hstep_integrable)
  have hdiff_integral_pos : 0 < ∫ v, q v - step v ∂law :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_integrable).2
      hsupport_pos
  have hdiff_integral :
      (∫ v, q v - step v ∂law) =
        (∫ v, q v ∂law) - ∫ v, step v ∂law := by
    exact integral_sub hq_integrable (by simpa [step] using hstep_integrable)
  have hsame_mass' : (∫ v, q v ∂law) = ∫ v, step v ∂law := by
    simpa [step] using hsame_mass
  rw [hdiff_integral, hsame_mass', sub_self] at hdiff_integral_pos
  exact (lt_irrefl 0) hdiff_integral_pos

/--
PG23 Theorem 1(ii)'s strict monoculture welfare loss, proved directly by
upper-tail rearrangement from the literal common-cutoff market.
-/
theorem pg23Theorem1_monocultureWelfare_strict_of_literal_commonCutoffClearing
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {monoCutoff vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := Fin 1) valueLaw noiseLaw))
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin 1) valueLaw noiseLaw))
      (fun _ : Fin 1 => S / (Fintype.card (Fin 1) : ℝ))
      (fun _ : Fin 1 => monoCutoff))
    (habs_integrable : Integrable (fun v : ℝ => |v|) valueLaw) :
    (∫ v : ℝ, v *
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff) 0 ∂valueLaw) <
      ∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw := by
  let q : ℝ -> ℝ := fun v =>
    AppliedModelingLib.Matching.singleCutoffCrossingProbability
      (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
      (fun _ : Fin 1 => monoCutoff) 0
  have hq_integrable : Integrable q valueLaw :=
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
      noiseLaw valueLaw monoCutoff 0
  have hq_value_integrable : Integrable (fun v : ℝ => v * q v) valueLaw :=
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_value_mul_integrable_of_abs_integrable
      noiseLaw valueLaw monoCutoff 0 habs_integrable
  have hstep_integrable := theorem1_optimalStepMatchProbability_integrable valueLaw vS
  have hstep_value_integrable :=
    theorem1_optimalStepMatchProbability_value_integrable_of_abs_integrable
      valueLaw vS habs_integrable
  have hq_bounds : ∀ v : ℝ, 0 ≤ q v ∧ q v ≤ 1 := by
    intro v
    exact ⟨
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_nonneg
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff) 0,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_one
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff) 0⟩
  have hq_mass : (∫ v : ℝ, q v ∂valueLaw) = S := by
    exact pg23MonocultureCommonCutoff_strictCrossingIntegral_eq_supply
      valueLaw noiseLaw 0 hlevel (by simpa using hclear)
  have hstep_mass :
      (∫ v : ℝ, (if vS < v then (1 : ℝ) else 0) ∂valueLaw) = S := by
    rw [← htail]
    simpa [theorem1_optimalStepMatchProbability] using
      theorem1_optimalStepMatchProbability_integral_eq_upperTailMass valueLaw vS
  have hsame_mass :
      (∫ v : ℝ, q v ∂valueLaw) =
        ∫ v : ℝ, (if vS < v then (1 : ℝ) else 0) ∂valueLaw :=
    hq_mass.trans hstep_mass.symm
  let region := pg23NoiseInteriorCutoffRegion noiseLaw monoCutoff
  have hregion_pos : 0 < valueLaw region := by
    exact pg23MonocultureNoiseInteriorCutoffRegion_measure_pos_of_marketClearing
      valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hlevel hS hclear
  have hregion_diff_pos : 0 < valueLaw (region \ ({vS} : Set ℝ)) := by
    rw [measure_diff_null (measure_singleton vS)]
    exact hregion_pos
  have hfractional :
      0 < valueLaw {v : ℝ | v ≠ vS ∧ 0 < q v ∧ q v < 1} := by
    apply lt_of_lt_of_le hregion_diff_pos
    apply measure_mono
    intro v hv
    have hv_ne : v ≠ vS := by
      simpa only [mem_singleton_iff] using hv.2
    have hinterior : monoCutoff - v ∈ interior noiseLaw.support := hv.1
    have hopen := pg23_upperTailMass_mem_Ioo_of_mem_interior_support
      noiseLaw hinterior
    have hq_formula :=
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass
        noiseLaw v monoCutoff (0 : Fin 1)
    exact ⟨hv_ne, by simpa [q, hq_formula] using hopen⟩
  exact AppliedModelingLib.integral_value_mul_lt_upperTailStep_of_same_mass_fractional
    valueLaw hq_integrable
    (by simpa [theorem1_optimalStepMatchProbability] using hstep_integrable)
    hq_value_integrable
    (by simpa [theorem1_optimalStepMatchProbability] using hstep_value_integrable)
    hq_bounds hsame_mass hfractional

/--
PG23 Theorem 1's complete welfare conclusion for literal common-cutoff
markets: polyculture converges to the efficient upper-tail welfare,
monoculture welfare is market-size invariant, and monoculture is strictly
suboptimal.  All three conclusions are visible at the theorem boundary.
-/
theorem pg23Theorem1_welfare_of_literal_commonCutoffClearing
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {monoCutoff polyCutoff : ℕ -> ℝ}
    {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hconc : maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hmono_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hpoly_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hmono_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => monoCutoff n))
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n))
    (habs_integrable : Integrable (fun v : ℝ => |v|) valueLaw) :
    Tendsto
      (fun n : ℕ => ∫ v : ℝ, v *
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
          v (fun _ : Fin (n + 1) => polyCutoff n) ∂valueLaw)
      atTop
      (nhds (∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)) ∧
    (∀ m n : ℕ,
      (∫ v : ℝ, v *
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw)) v
          (fun _ : Fin (m + 1) => monoCutoff m) 0 ∂valueLaw) =
      ∫ v : ℝ, v *
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) v
          (fun _ : Fin (n + 1) => monoCutoff n) 0 ∂valueLaw) ∧
    (∫ v : ℝ, v *
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff 0) 0 ∂valueLaw) <
      ∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw := by
  let polyMatch : ℕ -> ℝ -> ℝ := fun n v =>
    AppliedModelingLib.Matching.cutoffCrossingProbability
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
      v (fun _ : Fin (n + 1) => polyCutoff n)
  let monoMatch : ℕ -> ℝ -> ℝ := fun n v =>
    AppliedModelingLib.Matching.singleCutoffCrossingProbability
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) v
      (fun _ : Fin (n + 1) => monoCutoff n) 0
  have hprob_direct := pg23Theorem1_probability_of_literal_commonCutoffClearing
    valueLaw noiseLaw hvalue hnoise hS htail hconc hmono_level hpoly_level
    hmono_clear hpoly_clear
  have hprob : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS := by
    simpa only [polyMatch, monoMatch, theorem1_wisdomProbabilityConclusion]
      using hprob_direct
  have hpoly_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun v : ℝ => v * polyMatch n v) valueLaw := by
    intro n
    exact AppliedModelingLib.Matching.cutoffCrossingProbability_value_mul_aestronglyMeasurable
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) valueLaw Finset.univ
      (fun _ : Fin (n + 1) => polyCutoff n)
  have hpoly_bounds : ∀ n : ℕ, ∀ᵐ v : ℝ ∂valueLaw,
      0 ≤ polyMatch n v ∧ polyMatch n v ≤ 1 := by
    intro n
    filter_upwards with v
    exact ⟨
      AppliedModelingLib.Matching.cutoffCrossingProbability_nonneg
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ v
        (fun _ : Fin (n + 1) => polyCutoff n),
      AppliedModelingLib.Matching.cutoffCrossingProbability_le_one
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ v
        (fun _ : Fin (n + 1) => polyCutoff n)⟩
  have hpoly_welfare : Tendsto
      (fun n : ℕ => ∫ v : ℝ, v * polyMatch n v ∂valueLaw) atTop
      (nhds (∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)) := by
    apply theorem1_polyWelfare_tendsto_of_probability_step_integral
      (polyMatch := polyMatch) (monoMatch := monoMatch)
      (polyWelfare := fun n : ℕ => ∫ v : ℝ, v * polyMatch n v ∂valueLaw)
      (optimalWelfare := ∫ v : ℝ,
        v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)
      hprob (measure_singleton vS) habs_integrable hpoly_meas hpoly_bounds
    · intro n
      rfl
    · simp [theorem1_optimalStepMatchProbability]
  refine ⟨by simpa only [polyMatch] using hpoly_welfare, ?_, ?_⟩
  · intro m n
    apply integral_congr_ae
    filter_upwards with v
    exact congrArg (fun q : ℝ => v * q) (hprob.2.2 v m n)
  · exact
      pg23Theorem1_monocultureWelfare_strict_of_literal_commonCutoffClearing
        valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hS htail
        (hmono_level 0) (by simpa using hmono_clear 0) habs_integrable

/--
PG23 Corollary 4 for the literal continuum markets.  The proof uses the
support-invariant interior region instead of finite support endpoints.
-/
theorem pg23Corollary4_monocultureCutoff_lt_polycultureCutoff
    {n : ℕ} [NeZero n]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hn : 1 < n)
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {Pmono Ppoly S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono_level : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
    (hpoly_level : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
    (hmono_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Pmono))
    (hpoly_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Ppoly)) :
    Pmono < Ppoly := by
  let topFirm : Fin n := ⟨0, Nat.zero_lt_of_lt hn⟩
  let monoDemand : ℝ -> ℝ := fun P =>
    ∫ v : ℝ, AppliedModelingLib.Matching.singleCutoffCrossingProbability
      (Measure.pi (fun _ : Fin n => noiseLaw)) v
      (fun _ : Fin n => P) topFirm ∂valueLaw
  let polyDemand : ℝ -> ℝ := fun P =>
    ∫ v : ℝ, AppliedModelingLib.Matching.cutoffCrossingProbability
      (Measure.pi (fun _ : Fin n => noiseLaw)) Finset.univ v
      (fun _ : Fin n => P) ∂valueLaw
  have hmono_integral : monoDemand Pmono = S := by
    exact pg23MonocultureCommonCutoff_strictCrossingIntegral_eq_supply
      valueLaw noiseLaw topFirm hmono_level (by simpa using hmono_clear)
  have hpoly_integral : polyDemand Ppoly = S := by
    exact pg23PolycultureCommonCutoff_strictCrossingIntegral_eq_supply
      valueLaw noiseLaw hpoly_level (by simpa using hpoly_clear)
  have hmono_antitone :
      ∀ a b : ℝ, a ≤ b -> monoDemand b ≤ monoDemand a := by
    intro a b hab
    dsimp [monoDemand]
    exact MeasureTheory.integral_mono
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
        noiseLaw valueLaw b topFirm)
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
        noiseLaw valueLaw a topFirm)
      (fun v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_mono_lowerCutoff
          (Measure.pi (fun _ : Fin n => noiseLaw)) (c := topFirm)
          (by simpa using hab))
  have hregion_pos :
      0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw Ppoly) :=
    pg23PolycultureNoiseInteriorCutoffRegion_measure_pos_of_marketClearing
      valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hpoly_level hS hpoly_clear
  have hstrict_pos : 0 < valueLaw {v : ℝ |
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Ppoly) topFirm <
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) Finset.univ v
          (fun _ : Fin n => Ppoly)} := by
    apply lt_of_lt_of_le hregion_pos
    apply measure_mono
    intro v hv
    have htail_open := pg23_upperTailMass_mem_Ioo_of_mem_interior_support
      noiseLaw hv
    have hsum := AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one
      noiseLaw (Ppoly - v)
    have hcdf_open : AppliedModelingLib.Probability.lowerCDFMass noiseLaw (Ppoly - v) ∈
        Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [htail_open.1, htail_open.2]
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_lt_cutoffCrossingProbability_univ_constant_iidProduct
        noiseLaw topFirm hn hcdf_open
  have hstrict_at_poly : monoDemand Ppoly < polyDemand Ppoly := by
    apply corollary4_strict_demand_gap_of_pointwise_access valueLaw
    · exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
          noiseLaw valueLaw Ppoly topFirm
    · exact AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseLaw)) valueLaw Finset.univ
        (fun _ : Fin n => Ppoly)
    · rfl
    · rfl
    · intro v
      exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) Finset.univ (by simp)
          v (fun _ : Fin n => Ppoly)
    · exact hstrict_pos
  exact corollary4_mono_cutoff_lt_poly_cutoff_of_same_supply
    hmono_integral hpoly_integral hmono_antitone hstrict_at_poly

/--
PG23 Theorem 2(iii) on the support-invariant source region.  This replaces the
possibly extended-real endpoint notation `(vS, Pmono - X_-)` with its exact
probabilistic meaning: values above `vS` whose monoculture match probability
is below one.
-/
theorem pg23Theorem2_eventualMatchAdvantage_on_positiveRegion
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {monoCutoff polyCutoff : ℕ -> ℝ}
    {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hconc : maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hmono_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hpoly_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hmono_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => monoCutoff n))
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n)) :
    0 < valueLaw {v : ℝ | vS < v ∧
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff 0) 0 < 1} ∧
    (∀ v : ℝ,
      v ∈ {w : ℝ | vS < w ∧
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin 1 => noiseLaw)) w
          (fun _ : Fin 1 => monoCutoff 0) 0 < 1} ->
      ∀ᶠ n : ℕ in atTop,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) v
            (fun _ : Fin (n + 1) => monoCutoff n) 0 <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (n + 1) => polyCutoff n)) := by
  let monoMatch : ℕ -> ℝ -> ℝ := fun n v =>
    AppliedModelingLib.Matching.singleCutoffCrossingProbability
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) v
      (fun _ : Fin (n + 1) => monoCutoff n) 0
  let polyMatch : ℕ -> ℝ -> ℝ := fun n v =>
    AppliedModelingLib.Matching.cutoffCrossingProbability
      (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ v
      (fun _ : Fin (n + 1) => polyCutoff n)
  have hprob := pg23Theorem1_probability_of_literal_commonCutoffClearing
    valueLaw noiseLaw hvalue hnoise hS htail hconc hmono_level hpoly_level
    hmono_clear hpoly_clear
  have hq_integrable : Integrable (monoMatch 0) valueLaw := by
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
        noiseLaw valueLaw (monoCutoff 0) 0
  have hstep_integrable :
      Integrable (fun v : ℝ => if vS < v then (1 : ℝ) else 0) valueLaw := by
    simpa [theorem1_optimalStepMatchProbability] using
      theorem1_optimalStepMatchProbability_integrable valueLaw vS
  have hq_bounds : ∀ v : ℝ, 0 ≤ monoMatch 0 v ∧ monoMatch 0 v ≤ 1 := by
    intro v
    exact ⟨
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_nonneg
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff 0) 0,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_one
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff 0) 0⟩
  have hq_mass : (∫ v : ℝ, monoMatch 0 v ∂valueLaw) = S := by
    exact pg23MonocultureCommonCutoff_strictCrossingIntegral_eq_supply
      valueLaw noiseLaw 0 (hmono_level 0) (by simpa using hmono_clear 0)
  have hstep_mass :
      (∫ v : ℝ, (if vS < v then (1 : ℝ) else 0) ∂valueLaw) = S := by
    rw [← htail]
    simpa [theorem1_optimalStepMatchProbability] using
      theorem1_optimalStepMatchProbability_integral_eq_upperTailMass valueLaw vS
  have hsame_mass :
      (∫ v : ℝ, monoMatch 0 v ∂valueLaw) =
        ∫ v : ℝ, (if vS < v then (1 : ℝ) else 0) ∂valueLaw :=
    hq_mass.trans hstep_mass.symm
  let fractionalRegion :=
    pg23NoiseInteriorCutoffRegion noiseLaw (monoCutoff 0)
  have hfractional_region_pos : 0 < valueLaw fractionalRegion := by
    exact pg23MonocultureNoiseInteriorCutoffRegion_measure_pos_of_marketClearing
      valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate
      (hmono_level 0) hS (by simpa using hmono_clear 0)
  have hfractional_region_diff_pos :
      0 < valueLaw (fractionalRegion \ ({vS} : Set ℝ)) := by
    rw [measure_diff_null (measure_singleton vS)]
    exact hfractional_region_pos
  have hfractional :
      0 < valueLaw {v : ℝ |
        v ≠ vS ∧ 0 < monoMatch 0 v ∧ monoMatch 0 v < 1} := by
    apply lt_of_lt_of_le hfractional_region_diff_pos
    apply measure_mono
    intro v hv
    have hv_ne : v ≠ vS := by
      simpa only [mem_singleton_iff] using hv.2
    have hopen := pg23_upperTailMass_mem_Ioo_of_mem_interior_support
      noiseLaw hv.1
    have hformula :=
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass
        noiseLaw v (monoCutoff 0) (0 : Fin 1)
    exact ⟨hv_ne, by simpa [monoMatch, hformula] using hopen⟩
  have hregion_pos :
      0 < valueLaw {v : ℝ | vS < v ∧ monoMatch 0 v < 1} :=
    pg23_highValueBelowOneRegion_measure_pos_of_sameMass_fractional
      valueLaw hq_integrable hstep_integrable hq_bounds hsame_mass hfractional
  refine ⟨by simpa only [monoMatch] using hregion_pos, ?_⟩
  intro v hv
  have hv' : vS < v ∧ monoMatch 0 v < 1 := by
    simpa only [monoMatch] using hv
  let gap : ℝ := (1 - monoMatch 0 v) / 2
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith [hv'.2]
  have hmem : (1 : ℝ) ∈ Ioi (1 - gap) := by
    simp
    exact hgap_pos
  have hpoly_event : ∀ᶠ n : ℕ in atTop, 1 - gap < polyMatch n v :=
    (hprob.2.1 v hv'.1) (isOpen_Ioi.mem_nhds hmem)
  filter_upwards [hpoly_event] with n hn
  have hmono_eq : monoMatch n v = monoMatch 0 v := by
    exact hprob.2.2 v n 0
  have hmono_lt : monoMatch 0 v < 1 - gap := by
    dsimp [gap]
    linarith [hv'.2]
  simpa only [monoMatch, polyMatch] using
    (show monoMatch n v < polyMatch n v by linarith)

/-- Moving right from an interior support threshold strictly decreases its tail. -/
theorem pg23_upperTailMass_lt_of_left_mem_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    {x y : ℝ} (hx : x ∈ interior law.support) (hxy : x < y) :
    AppliedModelingLib.Probability.upperTailMass law y <
      AppliedModelingLib.Probability.upperTailMass law x := by
  have hlocal := pg23_twoSidedPositiveIntervalMass_of_mem_interior_support law hx
  have hinterval : 0 < law (Ioc x y) := by
    have hpos := hlocal.right_pos (y - x) (sub_pos.mpr hxy)
    simpa using hpos
  exact AppliedModelingLib.Probability.upperTailMass_lt_upperTailMass_of_Ioc_pos
    law hxy hinterval

/--
PG23 Theorem 2(i): monoculture weakly dominates polyculture in top-choice
probability and does so strictly on a positive-measure support-invariant
region.
-/
theorem pg23Theorem2_topChoiceProbability_mono_ge_poly
    {n : ℕ} [NeZero n]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hn : 1 < n)
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {Pmono Ppoly S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono_level : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
    (hpoly_level : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
    (hmono_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Pmono))
    (hpoly_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Ppoly)) :
    (∀ v : ℝ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Ppoly) ⟨0, Nat.zero_lt_of_lt hn⟩ ≤
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Pmono) ⟨0, Nat.zero_lt_of_lt hn⟩) ∧
    0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw Pmono) ∧
    (∀ v ∈ pg23NoiseInteriorCutoffRegion noiseLaw Pmono,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Ppoly) ⟨0, Nat.zero_lt_of_lt hn⟩ <
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Pmono) ⟨0, Nat.zero_lt_of_lt hn⟩) := by
  let topFirm : Fin n := ⟨0, Nat.zero_lt_of_lt hn⟩
  have hcutoff := pg23Corollary4_monocultureCutoff_lt_polycultureCutoff
    valueLaw noiseLaw hn hvalue hnoise hnoise_nondegenerate hS
    hmono_level hpoly_level hmono_clear hpoly_clear
  have hregion_pos :=
    pg23MonocultureNoiseInteriorCutoffRegion_measure_pos_of_marketClearing
      valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hmono_level hS hmono_clear
  refine ⟨?_, hregion_pos, ?_⟩
  · intro v
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_constant_mono_cutoff
        (Measure.pi (fun _ : Fin n => noiseLaw)) v topFirm hcutoff.le
  · intro v hv
    rw [
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass]
    exact pg23_upperTailMass_lt_of_left_mem_interior_support
      noiseLaw hv (by linarith)

/--
PG23 Theorem 2(ii) at the literal choice-function level.  Lean ranks are
zero-based, so rank `0` is the paper's rank `1`.
-/
theorem pg23Theorem2_monocultureSourceChoice_rank_eq_zero
    {College : Type v} [Fintype College] [Nonempty College]
    (value noise cutoff : ℝ) (ranking : PG23Ranking College) (c : College)
    (hchoice :
      pg23SourceChoice (fun _ : College => cutoff)
        (pg23MonocultureType value noise ranking) = some c) :
    pg23SourceRank (pg23MonocultureType value noise ranking) c = 0 := by
  let theta := pg23MonocultureType value noise ranking
  have hsem := pg23SourceChoice_semantics (College := College)
    (fun _ : College => cutoff) theta
  rw [hchoice] at hsem
  have hc_affordable : cutoff ≤ value + noise := by
    simpa [theta, pg23Affordable] using hsem.1
  have hall_affordable : ∀ d : College,
      pg23Affordable (fun _ : College => cutoff) theta d := by
    intro d
    simpa [theta, pg23Affordable] using hc_affordable
  let topRank : Fin (Fintype.card College) := ⟨0, Fintype.card_pos⟩
  let topCollege : College := ranking.symm topRank
  have hnot_preferred := hsem.2 topCollege (hall_affordable topCollege)
  by_contra hne
  apply hnot_preferred
  change pg23SourceRank theta topCollege < pg23SourceRank theta c
  have hc_pos : 0 < pg23SourceRank theta c := Nat.pos_of_ne_zero hne
  have htop_zero : pg23SourceRank theta topCollege = 0 := by
    change (ranking (ranking.symm topRank)).val = 0
    rw [ranking.apply_symm_apply]
  rw [htop_zero]
  exact hc_pos

/--
At a common cutoff in monoculture, the baseline source-choice fiber for college
`c` is exactly the event that `c` is top-ranked and the common score clears the
cutoff.
-/
theorem pg23MonocultureSourceChoice_eq_some_iff_topRank_and_cutoff
    {College : Type v} [Fintype College] [Nonempty College]
    (value noise cutoff : ℝ) (ranking : PG23Ranking College) (c : College) :
    pg23SourceChoice (fun _ : College => cutoff)
        (pg23MonocultureType value noise ranking) = some c ↔
      pg23MonocultureType value noise ranking ∈ pg23TopRankSet c ∧
        cutoff ≤ value + noise := by
  let theta := pg23MonocultureType value noise ranking
  constructor
  · intro hchoice
    have hrank :
        pg23SourceRank theta c = 0 :=
      pg23Theorem2_monocultureSourceChoice_rank_eq_zero
        value noise cutoff ranking c hchoice
    have hsem := pg23SourceChoice_semantics (College := College)
      (fun _ : College => cutoff) theta
    rw [hchoice] at hsem
    constructor
    · simpa [theta, pg23TopRankSet] using hrank
    · simpa [theta, pg23Affordable] using hsem.1
  · rintro ⟨htop, hcross⟩
    have hc_rank : pg23SourceRank theta c = 0 := by
      simpa [theta, pg23TopRankSet] using htop
    have hc_affordable :
        pg23Affordable (fun _ : College => cutoff) theta c := by
      simpa [theta, pg23Affordable] using hcross
    cases hchoice : pg23SourceChoice (fun _ : College => cutoff) theta with
    | none =>
        have hsem := pg23SourceChoice_semantics (College := College)
          (fun _ : College => cutoff) theta
        rw [hchoice] at hsem
        exact False.elim ((not_lt_of_ge hc_affordable) (hsem c))
    | some d =>
        have hsem := pg23SourceChoice_semantics (College := College)
          (fun _ : College => cutoff) theta
        rw [hchoice] at hsem
        have hnot := hsem.2 c hc_affordable
        have hd_rank_zero : pg23SourceRank theta d = 0 := by
          change ¬ pg23SourceRank theta c < pg23SourceRank theta d at hnot
          exact Nat.eq_zero_of_le_zero (by
            rw [hc_rank] at hnot
            exact Nat.le_of_not_gt hnot)
        have hdc : d = c := by
          change (ranking d).val = 0 at hd_rank_zero
          change (ranking c).val = 0 at hc_rank
          exact ranking.injective (Fin.ext (by rw [hd_rank_zero, hc_rank]))
        simpa [hdc] using hchoice

/--
For monoculture with a top-k active set, being matched is exactly having at
least one active application and clearing the common cutoff.
-/
theorem pg23MonocultureActiveSourceChoice_matched_iff
    {College : Type v} [Fintype College] [Nonempty College]
    (value noise cutoff : ℝ) (ranking : PG23Ranking College) (k : ℕ) :
    (∃ c : College,
      pg23ActiveSourceChoice
          (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
          (pg23MonocultureType value noise ranking) = some c) ↔
      0 < k ∧ cutoff ≤ value + noise := by
  constructor
  · rintro ⟨c, hchoice⟩
    have hc :=
      pg23ActiveSourceChoice_some_active_affordable
        (active := pg23TopKApplicationSet k ranking)
        (P := fun _ : College => cutoff)
        (theta := pg23MonocultureType value noise ranking)
        hchoice
    have hk : 0 < k := by
      rw [pg23TopKApplicationSet_mem] at hc
      omega
    have hscore : cutoff ≤ value + noise := by
      simpa [pg23Affordable] using hc.2
    exact ⟨hk, hscore⟩
  · rintro ⟨hk, hscore⟩
    let topCollege : College := ranking.symm ⟨0, Fintype.card_pos⟩
    have htop_active :
        topCollege ∈ pg23TopKApplicationSet k ranking :=
      pg23TopKApplicationSet_top_mem ranking hk
    have htop_affordable :
        pg23Affordable (fun _ : College => cutoff)
          (pg23MonocultureType value noise ranking) topCollege := by
      simpa [pg23Affordable] using hscore
    have hfeasible :
        (pg23ActiveAffordableSet
          (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
          (pg23MonocultureType value noise ranking)).Nonempty := by
      refine ⟨topCollege, ?_⟩
      rw [pg23ActiveAffordableSet_mem]
      exact ⟨htop_active, htop_affordable⟩
    refine ⟨Classical.choose
      (Finset.exists_min_image
        (pg23ActiveAffordableSet
          (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
          (pg23MonocultureType value noise ranking))
        (pg23SourceRank (pg23MonocultureType value noise ranking))
        hfeasible), ?_⟩
    simp [pg23ActiveSourceChoice, hfeasible]

/--
With top-k applications and a common monoculture score, every active-source
match goes to the applicant's top-ranked college.
-/
theorem pg23MonocultureActiveSourceChoice_rank_eq_zero
    {College : Type v} [Fintype College] [Nonempty College]
    (value noise cutoff : ℝ) (ranking : PG23Ranking College) (k : ℕ)
    (c : College)
    (hchoice :
      pg23ActiveSourceChoice
          (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
          (pg23MonocultureType value noise ranking) = some c) :
    pg23SourceRank (pg23MonocultureType value noise ranking) c = 0 := by
  let theta := pg23MonocultureType value noise ranking
  have hc :=
    pg23ActiveSourceChoice_some_active_affordable
      (active := pg23TopKApplicationSet k ranking)
      (P := fun _ : College => cutoff)
      (theta := theta) hchoice
  have hk : 0 < k := by
    rw [pg23TopKApplicationSet_mem] at hc
    omega
  let topCollege : College := ranking.symm ⟨0, Fintype.card_pos⟩
  have htop_active :
      topCollege ∈ pg23TopKApplicationSet k ranking :=
    pg23TopKApplicationSet_top_mem ranking hk
  have htop_affordable :
      pg23Affordable (fun _ : College => cutoff) theta topCollege := by
    simpa [theta, pg23Affordable] using hc.2
  have hrank_le :
      pg23SourceRank theta c ≤ pg23SourceRank theta topCollege :=
    pg23ActiveSourceChoice_rank_le_of_active_affordable
      (active := pg23TopKApplicationSet k ranking)
      (P := fun _ : College => cutoff)
      (theta := theta) hchoice htop_active htop_affordable
  have htop_zero : pg23SourceRank theta topCollege = 0 := by
    change (ranking (ranking.symm ⟨0, Fintype.card_pos⟩)).val = 0
    rw [ranking.apply_symm_apply]
  exact Nat.eq_zero_of_le_zero (by simpa [htop_zero] using hrank_le)

/--
With top-k applications and a common monoculture score, the active-source choice
fiber for college `c` is exactly the event that `c` is top-ranked and the common
score clears the common cutoff.
-/
theorem pg23MonocultureActiveSourceChoice_eq_some_iff_topRank_and_cutoff
    {College : Type v} [Fintype College] [Nonempty College]
    (value noise cutoff : ℝ) (ranking : PG23Ranking College) {k : ℕ}
    (hk : 0 < k) (c : College) :
    pg23ActiveSourceChoice
        (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
        (pg23MonocultureType value noise ranking) = some c ↔
      pg23MonocultureType value noise ranking ∈ pg23TopRankSet c ∧
        cutoff ≤ value + noise := by
  let theta := pg23MonocultureType value noise ranking
  constructor
  · intro hchoice
    have hrank :
        pg23SourceRank theta c = 0 :=
      pg23MonocultureActiveSourceChoice_rank_eq_zero
        value noise cutoff ranking k c hchoice
    have hc :=
      pg23ActiveSourceChoice_some_active_affordable
        (active := pg23TopKApplicationSet k ranking)
        (P := fun _ : College => cutoff)
        (theta := theta) hchoice
    constructor
    · simpa [theta, pg23TopRankSet] using hrank
    · simpa [theta, pg23Affordable] using hc.2
  · rintro ⟨htop, hcross⟩
    have hc_rank : pg23SourceRank theta c = 0 := by
      simpa [theta, pg23TopRankSet] using htop
    have hc_active : c ∈ pg23TopKApplicationSet k ranking := by
      rw [pg23TopKApplicationSet_mem]
      change pg23SourceRank theta c < k
      rw [hc_rank]
      exact hk
    have hc_affordable :
        pg23Affordable (fun _ : College => cutoff) theta c := by
      simpa [theta, pg23Affordable] using hcross
    apply (pg23ActiveSourceChoice_eq_some_iff
      (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff) theta c).mpr
    refine ⟨hc_active, hc_affordable, ?_⟩
    intro d _hd_active _hd_affordable
    change ¬ pg23SourceRank theta d < pg23SourceRank theta c
    rw [hc_rank]
    exact Nat.not_lt_zero _

/--
For monoculture common cutoffs, restricting applications to any positive top-k
set does not change the realized favorite-affordable choice.
-/
theorem pg23MonocultureActiveSourceChoice_eq_sourceChoice_commonCutoff
    {College : Type v} [Fintype College] [Nonempty College]
    (value noise cutoff : ℝ) (ranking : PG23Ranking College) {k : ℕ}
    (hk : 0 < k) :
    pg23ActiveSourceChoice
        (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
        (pg23MonocultureType value noise ranking) =
      pg23SourceChoice (fun _ : College => cutoff)
        (pg23MonocultureType value noise ranking) := by
  cases hactive :
      pg23ActiveSourceChoice
        (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
        (pg23MonocultureType value noise ranking) with
  | none =>
      cases hsource :
          pg23SourceChoice (fun _ : College => cutoff)
            (pg23MonocultureType value noise ranking) with
      | none => rfl
      | some c =>
          have hsource_event :=
            (pg23MonocultureSourceChoice_eq_some_iff_topRank_and_cutoff
              value noise cutoff ranking c).mp hsource
          have hactive_some :
              pg23ActiveSourceChoice
                  (pg23TopKApplicationSet k ranking) (fun _ : College => cutoff)
                  (pg23MonocultureType value noise ranking) = some c :=
            (pg23MonocultureActiveSourceChoice_eq_some_iff_topRank_and_cutoff
              value noise cutoff ranking hk c).mpr hsource_event
          rw [hactive] at hactive_some
          contradiction
  | some c =>
      have hactive_event :=
        (pg23MonocultureActiveSourceChoice_eq_some_iff_topRank_and_cutoff
          value noise cutoff ranking hk c).mp hactive
      have hsource_some :
          pg23SourceChoice (fun _ : College => cutoff)
              (pg23MonocultureType value noise ranking) = some c :=
        (pg23MonocultureSourceChoice_eq_some_iff_topRank_and_cutoff
          value noise cutoff ranking c).mpr hactive_event
      rw [hsource_some]

/--
For monoculture common cutoffs, differential-access matched mass equals the
baseline monoculture matched mass.  The access-count coordinate disappears
because every positive top-k active set contains the applicant's top-ranked
college and all monoculture scores are common.
-/
theorem pg23MonocultureDifferentialMatchedMass_commonCutoff_eq_baseline
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (p : ℝ) :
    (pg23MonocultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw).real
      {theta | ∃ c : College,
        pg23DifferentialSourceChoice (fun _ : College => p) theta = some c} =
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw).real
      {theta | ∃ c : College,
        pg23SourceChoice (fun _ : College => p) theta = some c} := by
  classical
  let sampleLaw : Measure (PG23MonocultureSample College) :=
    (valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw
  let sampleToDiff :
      Fin n × PG23MonocultureSample College ->
        PG23DifferentialApplicantType College n :=
    fun z => (z.1, pg23MonocultureSampleToType z.2)
  let diffSet : Set (PG23DifferentialApplicantType College n) :=
    {theta | ∃ c : College,
      pg23DifferentialSourceChoice (fun _ : College => p) theta = some c}
  let baseSet : Set (PG23ApplicantType College) :=
    {theta | ∃ c : College,
      pg23SourceChoice (fun _ : College => p) theta = some c}
  have hsampleToDiff_meas : Measurable sampleToDiff := by
    exact measurable_fst.prodMk
      (pg23MonocultureSampleToType_measurable.comp measurable_snd)
  have hdiffSet_meas : MeasurableSet diffSet := by
    have hset :
        diffSet =
          ⋃ c : College,
            {theta : PG23DifferentialApplicantType College n |
              pg23DifferentialSourceChoice (fun _ : College => p) theta =
                some c} := by
      ext theta
      simp [diffSet]
    rw [hset]
    exact MeasurableSet.iUnion fun c =>
      pg23DifferentialSourceChoice_fiber_measurable
        (College := College) (n := n) (fun _ : College => p) c
  have hbaseSet_meas : MeasurableSet baseSet := by
    have hset :
        baseSet =
          ⋃ c : College,
            {theta : PG23ApplicantType College |
              pg23SourceChoice (fun _ : College => p) theta = some c} := by
      ext theta
      simp [baseSet]
    rw [hset]
    exact MeasurableSet.iUnion fun c => by
      change MeasurableSet
        ((pg23SourceChoice (fun _ : College => p)) ⁻¹'
          ({some c} : Set (Option College)))
      exact pg23SourceChoice_fiber_measurable
        (College := College) (fun _ : College => p) (some c)
  have hmap_diff :
      Measure.map sampleToDiff (accessLaw.prod sampleLaw) =
        pg23MonocultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw := by
    simpa [sampleToDiff, sampleLaw, pg23MonocultureDifferentialTypeLaw,
      pg23DifferentialTypeLaw, pg23MonocultureTypeLaw] using
      (Measure.map_prod_map accessLaw sampleLaw measurable_id
        pg23MonocultureSampleToType_measurable).symm
  have hpreimage :
      sampleToDiff ⁻¹' diffSet =
        Prod.snd ⁻¹' (pg23MonocultureSampleToType ⁻¹' baseSet) := by
    ext z
    simp only [Set.mem_preimage, diffSet, baseSet, Set.mem_setOf_eq,
      sampleToDiff]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hchoice :=
        pg23MonocultureActiveSourceChoice_eq_sourceChoice_commonCutoff
          z.2.1.1 z.2.2 p z.2.1.2 (Nat.succ_pos z.1.val)
      simpa [pg23DifferentialSourceChoice, pg23DifferentialActiveSet,
        pg23MonocultureSampleToType] using hchoice.symm.trans hc
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hchoice :=
        pg23MonocultureActiveSourceChoice_eq_sourceChoice_commonCutoff
          z.2.1.1 z.2.2 p z.2.1.2 (Nat.succ_pos z.1.val)
      simpa [pg23DifferentialSourceChoice, pg23DifferentialActiveSet,
        pg23MonocultureSampleToType] using hchoice.trans hc
  calc
    (pg23MonocultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw).real diffSet =
        (Measure.map sampleToDiff (accessLaw.prod sampleLaw)).real diffSet := by
      rw [hmap_diff]
    _ = (accessLaw.prod sampleLaw).real (sampleToDiff ⁻¹' diffSet) :=
      map_measureReal_apply hsampleToDiff_meas hdiffSet_meas
    _ = (accessLaw.prod sampleLaw).real
        (Prod.snd ⁻¹' (pg23MonocultureSampleToType ⁻¹' baseSet)) := by
      rw [hpreimage]
    _ = (Measure.map Prod.snd (accessLaw.prod sampleLaw)).real
        (pg23MonocultureSampleToType ⁻¹' baseSet) := by
      rw [map_measureReal_apply measurable_snd
        (hbaseSet_meas.preimage pg23MonocultureSampleToType_measurable)]
    _ = sampleLaw.real (pg23MonocultureSampleToType ⁻¹' baseSet) := by
      have hmap_snd :
          Measure.map Prod.snd (accessLaw.prod sampleLaw) = sampleLaw := by
        simpa using (Measure.map_snd_prod (μ := accessLaw) (ν := sampleLaw))
      rw [hmap_snd]
    _ = (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw).real
        baseSet := by
      rw [pg23MonocultureTypeLaw]
      exact (map_measureReal_apply pg23MonocultureSampleToType_measurable
        hbaseSet_meas).symm

/-- Active-source monoculture matching is exactly weak active cutoff crossing. -/
theorem pg23MonocultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
    {College : Type v} [Fintype College]
    (value noise : ℝ) (ranking : PG23Ranking College)
    (active : Finset College) (P : College -> ℝ) :
    (∃ c : College,
      pg23ActiveSourceChoice active P
        (pg23MonocultureType value noise ranking) = some c) ↔
      AppliedModelingLib.Matching.cutoffWeaklyCrossedOn active
        (AppliedModelingLib.Matching.noisyScore value (fun _ : College => noise)) P := by
  rw [pg23ActiveSourceChoice_some_iff_exists_active_affordable]
  simp [pg23Affordable, AppliedModelingLib.Matching.cutoffWeaklyCrossedOn,
    AppliedModelingLib.Matching.noisyScore]

/-- Active-source polyculture matching is exactly weak active cutoff crossing. -/
theorem pg23PolycultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
    {College : Type v} [Fintype College]
    (value : ℝ) (ranking : PG23Ranking College) (noise : College -> ℝ)
    (active : Finset College) (P : College -> ℝ) :
    (∃ c : College,
      pg23ActiveSourceChoice active P
        (pg23PolycultureType value ranking noise) = some c) ↔
      AppliedModelingLib.Matching.cutoffWeaklyCrossedOn active
        (AppliedModelingLib.Matching.noisyScore value noise) P := by
  rw [pg23ActiveSourceChoice_some_iff_exists_active_affordable]
  simp [pg23Affordable, AppliedModelingLib.Matching.cutoffWeaklyCrossedOn,
    AppliedModelingLib.Matching.noisyScore]

/--
For a fixed active set, the polyculture active-source match probability is the
reusable weak cutoff-crossing probability.
-/
theorem pg23PolycultureActiveSourceChoice_matchProbability_eq_cutoffWeakCrossingProbability
    {College : Type v} [Fintype College] [MeasurableSpace (College -> ℝ)]
    (noiseLaw : Measure (College -> ℝ)) (value : ℝ)
    (ranking : PG23Ranking College) (active : Finset College)
    (P : College -> ℝ) :
    noiseLaw.real {noise : College -> ℝ |
      ∃ c : College,
        pg23ActiveSourceChoice active P
          (pg23PolycultureType value ranking noise) = some c} =
      AppliedModelingLib.Matching.cutoffWeakCrossingProbability
        noiseLaw active value P := by
  unfold AppliedModelingLib.Matching.cutoffWeakCrossingProbability
  congr 1
  ext noise
  exact
    pg23PolycultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
      value ranking noise active P

/--
For a fixed value and common cutoff, the literal monoculture active-source
match event has the paper's strict single-noise upper-tail probability.  The
nonatomic noise premise removes the weak cutoff boundary introduced by the
source choice rule.
-/
theorem pg23MonocultureActiveSourceChoice_matchProbability_eq_upperTailMass
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] [NoAtoms noiseLaw]
    (value cutoff : ℝ) (ranking : PG23Ranking (Fin n)) :
    noiseLaw.real {noise : ℝ |
      ∃ c : Fin n,
        pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => cutoff)
          (pg23MonocultureType value noise ranking) = some c} =
      AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - value) := by
  let threshold : ℝ := cutoff - value
  have hevent :
      {noise : ℝ |
        ∃ c : Fin n,
          pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => cutoff)
            (pg23MonocultureType value noise ranking) = some c} =
        Ici threshold := by
    ext noise
    constructor
    · intro hmatch
      have hweak :=
        (pg23MonocultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
          value noise ranking Finset.univ (fun _ : Fin n => cutoff)).1 hmatch
      rcases hweak with ⟨c, _hc, hle⟩
      simp only [mem_Ici]
      simp [threshold, AppliedModelingLib.Matching.noisyScore] at hle ⊢
      linarith
    · intro htail
      have hactive : (Finset.univ : Finset (Fin n)).Nonempty :=
        Finset.univ_nonempty
      rcases hactive with ⟨c, hc⟩
      have hweak :
          AppliedModelingLib.Matching.cutoffWeaklyCrossedOn Finset.univ
            (AppliedModelingLib.Matching.noisyScore value (fun _ : Fin n => noise))
            (fun _ : Fin n => cutoff) := by
        refine ⟨c, hc, ?_⟩
        simp only [mem_Ici] at htail
        simp [threshold, AppliedModelingLib.Matching.noisyScore] at htail ⊢
        linarith
      exact
        (pg23MonocultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
          value noise ranking Finset.univ (fun _ : Fin n => cutoff)).2 hweak
  have hlevel_real : noiseLaw.real ({threshold} : Set ℝ) = 0 := by
    simp [Measure.real, threshold, measure_singleton]
  have hIci_union : Ici threshold = ({threshold} : Set ℝ) ∪ Ioi threshold := by
    ext z
    simp [le_iff_eq_or_lt]
  have hdisjoint : Disjoint ({threshold} : Set ℝ) (Ioi threshold) := by
    rw [Set.disjoint_left]
    intro z hz hlt
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact (lt_irrefl threshold) hlt
  have hstrict : noiseLaw.real (Ici threshold) = noiseLaw.real (Ioi threshold) := by
    have hunion := measureReal_union (μ := noiseLaw) hdisjoint measurableSet_Ioi
    rw [← hIci_union, hlevel_real] at hunion
    linarith
  rw [hevent, AppliedModelingLib.Probability.upperTailMass]
  exact hstrict

/--
For a fixed value and common cutoff, the literal polyculture active-source
match event has the maximum-noise tail probability from the paper's displayed
formula.  Nonatomic iid noise removes the weak cutoff boundary.
-/
theorem pg23PolycultureActiveSourceChoice_matchProbability_eq_maxNoiseTail
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] [NoAtoms noiseLaw]
    (value cutoff : ℝ) (ranking : PG23Ranking (Fin n)) :
    (Measure.pi (fun _ : Fin n => noiseLaw)).real {noise : Fin n -> ℝ |
      ∃ c : Fin n,
        pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => cutoff)
          (pg23PolycultureType value ranking noise) = some c} =
      (pg23PolycultureMaxNoiseLaw (College := Fin n) noiseLaw).real
        (Ioi (cutoff - value)) := by
  calc
    (Measure.pi (fun _ : Fin n => noiseLaw)).real {noise : Fin n -> ℝ |
        ∃ c : Fin n,
          pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => cutoff)
            (pg23PolycultureType value ranking noise) = some c} =
        AppliedModelingLib.Matching.cutoffWeakCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) value (fun _ : Fin n => cutoff) := by
      exact
        pg23PolycultureActiveSourceChoice_matchProbability_eq_cutoffWeakCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) value ranking
          (Finset.univ : Finset (Fin n)) (fun _ : Fin n => cutoff)
    _ = AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) value (fun _ : Fin n => cutoff) := by
      exact
        AppliedModelingLib.Matching.cutoffWeakCrossingProbability_iidProduct_eq_cutoffCrossingProbability_of_noAtoms
          noiseLaw (Finset.univ : Finset (Fin n)) value
          (fun _ : Fin n => cutoff)
    _ = (pg23PolycultureMaxNoiseLaw (College := Fin n) noiseLaw).real
          (Ioi (cutoff - value)) := by
      exact
        (pg23PolycultureMaxNoiseLaw_upperTail_eq_crossingProbability
          noiseLaw value cutoff).symm

/--
The literal monoculture match event with a common noise draw and a specified
number of active applications.  With no applications the existential event is
empty; with at least one application it is exactly the single-noise cutoff
event from the source.
-/
noncomputable def pg23MonocultureConditionalMatchProbability
    (noiseLaw : Measure ℝ) (applications : ℕ) (v cutoff : ℝ) : ℝ :=
  noiseLaw.real {noise : ℝ | ∃ _ : Fin applications, cutoff < v + noise}

/-- A nonempty monoculture active set has the source single-noise probability. -/
theorem pg23MonocultureConditionalMatchProbability_succ_eq_upperTailMass
    (noiseLaw : Measure ℝ) (applications : ℕ) (v cutoff : ℝ) :
    pg23MonocultureConditionalMatchProbability
        noiseLaw (applications + 1) v cutoff =
      AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) := by
  have hevent :
      {noise : ℝ | ∃ _ : Fin (applications + 1), cutoff < v + noise} =
        Ioi (cutoff - v) := by
    ext noise
    constructor
    · rintro ⟨_, hcross⟩
      simp only [mem_Ioi]
      linarith
    · intro hcross
      exact ⟨⟨0, Nat.zero_lt_succ applications⟩, by
        simp only [mem_Ioi] at hcross
        linarith⟩
  simp only [pg23MonocultureConditionalMatchProbability,
    AppliedModelingLib.Probability.upperTailMass, hevent]

/-- The finite source distribution over positive application counts as real weights. -/
noncomputable def pg23DifferentialAccessWeights {n : ℕ}
    (accessLaw : Measure (Fin n)) : Fin n -> ℝ :=
  fun k => accessLaw.real ({k} : Set (Fin n))

/-- Application-access weights derived from a measure are nonnegative. -/
theorem pg23DifferentialAccessWeights_nonneg {n : ℕ}
    (accessLaw : Measure (Fin n)) :
    ∀ k : Fin n, 0 ≤ pg23DifferentialAccessWeights accessLaw k := by
  intro k
  unfold pg23DifferentialAccessWeights
  exact measureReal_nonneg

/-- A probability law over finite access counts has total real weight one. -/
theorem pg23DifferentialAccessWeights_sum_eq_one {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw] :
    (∑ k : Fin n, pg23DifferentialAccessWeights accessLaw k) = 1 := by
  have hsum := sum_measureReal_preimage_singleton
    (μ := accessLaw) (s := (Finset.univ : Finset (Fin n))) (f := fun k : Fin n => k)
    (fun k _ => MeasurableSet.singleton k)
  simpa [pg23DifferentialAccessWeights] using hsum

/--
In the monoculture differential-access model, randomizing over positive
application counts does not change the conditional access probability.  The
weights are source-visible: `κ k` is the weight on `k.val + 1` applications.
-/
theorem pg23MonocultureConditionalMatchProbability_weighted_eq_upperTailMass
    (noiseLaw : Measure ℝ) {n : ℕ} (κ : Fin n -> ℝ)
    (hκ_sum : (∑ k : Fin n, κ k) = 1) (v cutoff : ℝ) :
    (∑ k : Fin n,
        κ k *
          pg23MonocultureConditionalMatchProbability
            noiseLaw (k.val + 1) v cutoff) =
      AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) := by
  calc
    (∑ k : Fin n,
        κ k *
          pg23MonocultureConditionalMatchProbability
            noiseLaw (k.val + 1) v cutoff)
        = ∑ k : Fin n,
            κ k * AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [pg23MonocultureConditionalMatchProbability_succ_eq_upperTailMass]
    _ = (∑ k : Fin n, κ k) *
          AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) := by
          rw [← Finset.sum_mul]
    _ = AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) := by
          rw [hκ_sum, one_mul]

/--
Equivalently, the monoculture differential-access mixture agrees with any
fixed positive application count.  This is the probability-level content of
the source proof's `P_mono,kappa = P_mono` step.
-/
theorem pg23MonocultureConditionalMatchProbability_weighted_eq_positiveAccess
    (noiseLaw : Measure ℝ) {n : ℕ} (κ : Fin n -> ℝ)
    (hκ_sum : (∑ k : Fin n, κ k) = 1)
    (applications : ℕ) (v cutoff : ℝ) :
    (∑ k : Fin n,
        κ k *
          pg23MonocultureConditionalMatchProbability
            noiseLaw (k.val + 1) v cutoff) =
      pg23MonocultureConditionalMatchProbability
        noiseLaw (applications + 1) v cutoff := by
  rw [
    pg23MonocultureConditionalMatchProbability_weighted_eq_upperTailMass
      noiseLaw κ hκ_sum,
    pg23MonocultureConditionalMatchProbability_succ_eq_upperTailMass]

/-- Scalar match-at-all demand for monoculture at a common cutoff. -/
noncomputable def pg23MonocultureScalarMatchDemand
    (valueLaw noiseLaw : Measure ℝ) (cutoff : ℝ) : ℝ :=
  ∫ v : ℝ, AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) ∂valueLaw

/--
Scalar match-at-all demand for monoculture with differential application
access.  The finite weights `κ` are over positive application counts:
`k : Fin n` represents `k.val + 1` applications.
-/
noncomputable def pg23MonocultureDifferentialScalarMatchDemand
    (valueLaw noiseLaw : Measure ℝ) {n : ℕ} (κ : Fin n -> ℝ)
    (cutoff : ℝ) : ℝ :=
  ∫ v : ℝ,
    ∑ k : Fin n,
      κ k *
        pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v cutoff ∂valueLaw

/--
The scalar match-at-all demand generated by monoculture differential access is
identical to baseline monoculture demand at every common cutoff.
-/
theorem pg23MonocultureDifferentialScalarMatchDemand_eq_baseline
    (valueLaw noiseLaw : Measure ℝ) {n : ℕ} (κ : Fin n -> ℝ)
    (hκ_sum : (∑ k : Fin n, κ k) = 1) (cutoff : ℝ) :
    pg23MonocultureDifferentialScalarMatchDemand valueLaw noiseLaw κ cutoff =
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw cutoff := by
  unfold pg23MonocultureDifferentialScalarMatchDemand
    pg23MonocultureScalarMatchDemand
  apply integral_congr_ae
  filter_upwards with v
  exact pg23MonocultureConditionalMatchProbability_weighted_eq_upperTailMass
    noiseLaw κ hκ_sum v cutoff

/--
The scalar monoculture demand is the strict upper tail of the primitive
value-plus-noise law.
-/
theorem pg23MonocultureScalarMatchDemand_eq_sumLaw_strictTail
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (cutoff : ℝ) :
    pg23MonocultureScalarMatchDemand valueLaw noiseLaw cutoff =
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod noiseLaw)).real (Ioi cutoff) := by
  unfold pg23MonocultureScalarMatchDemand
  let event : Set (ℝ × ℝ) := {z | cutoff < z.1 + z.2}
  have hevent : MeasurableSet event := by
    exact measurableSet_lt measurable_const (by fun_prop)
  have hproduct :
      (valueLaw.prod noiseLaw).real event =
        (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
          (valueLaw.prod noiseLaw)).real (Ioi cutoff) := by
    have hmap := map_measureReal_apply
      (μ := valueLaw.prod noiseLaw)
      (f := fun z : ℝ × ℝ => z.1 + z.2)
      (s := Ioi cutoff)
      (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 + z.2))
      measurableSet_Ioi
    have hpreimage :
        (fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Ioi cutoff = event := by
      ext z
      rfl
    rw [hpreimage] at hmap
    exact hmap.symm
  calc
    (∫ v : ℝ,
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - v) ∂valueLaw) =
        ∫ v : ℝ, noiseLaw.real (Prod.mk v ⁻¹' event) ∂valueLaw := by
      apply integral_congr_ae
      filter_upwards with v
      unfold AppliedModelingLib.Probability.upperTailMass
      congr 1
      ext x
      simp only [event, mem_preimage, mem_setOf_eq, mem_Ioi]
      constructor <;> intro h <;> linarith
    _ = (valueLaw.prod noiseLaw).real event :=
      pg23_integral_sectionProbability_eq_productProbability
        valueLaw noiseLaw hevent
    _ = (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod noiseLaw)).real (Ioi cutoff) := hproduct

/--
Connected primitive value and noise supports make the monoculture scalar
clearing cutoff unique for any interior total supply.
-/
theorem pg23MonocultureScalarMatchDemand_unique_of_connectedSupport
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {S p q : ℝ} (hS : 0 < S ∧ S < 1)
    (hp : pg23MonocultureScalarMatchDemand valueLaw noiseLaw p = S)
    (hq : pg23MonocultureScalarMatchDemand valueLaw noiseLaw q = S) :
    p = q := by
  let sumLaw : Measure ℝ :=
    Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (valueLaw.prod noiseLaw)
  letI : IsProbabilityMeasure sumLaw := by
    dsimp [sumLaw]
    exact Measure.isProbabilityMeasure_map
      (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 + z.2)).aemeasurable
  have hconnected := pg23MonocultureSourceMaxScoreLaw_connectedSupport
    (College := Fin 1) valueLaw noiseLaw hvalue hnoise
  rw [pg23MonocultureSourceMaxScoreLaw_eq_sumLaw] at hconnected
  change IsPreconnected sumLaw.support at hconnected
  have hp_tail : sumLaw.real (Ioi p) = S := by
    change (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
      (valueLaw.prod noiseLaw)).real (Ioi p) = S
    rw [← pg23MonocultureScalarMatchDemand_eq_sumLaw_strictTail
      valueLaw noiseLaw p]
    exact hp
  have hq_tail : sumLaw.real (Ioi q) = S := by
    change (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
      (valueLaw.prod noiseLaw)).real (Ioi q) = S
    rw [← pg23MonocultureScalarMatchDemand_eq_sumLaw_strictTail
      valueLaw noiseLaw q]
    exact hq
  exact pg23_cutoff_eq_of_connectedSupport_strictTail_eq
    sumLaw hconnected hS.1 hS.2 hp_tail hq_tail

/-- Differential aggregate demand summed over colleges is the mass of matched applicants. -/
theorem pg23DifferentialSourceAggregateDemand_sum_eq_matchedMass
    {College : Type v} [Fintype College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsFiniteMeasure typeLaw] (P : College -> ℝ) :
    (∑ c : College,
      pg23DifferentialSourceAggregateDemand typeLaw P c) =
      typeLaw.real {theta | ∃ c : College,
        pg23DifferentialSourceChoice P theta = some c} := by
  classical
  let choice : PG23DifferentialApplicantType College n -> Option College :=
    pg23DifferentialSourceChoice P
  have hsum := MeasureTheory.sum_measureReal_preimage_singleton
    (μ := typeLaw) ((Finset.univ : Finset College).image some)
    (f := choice) (fun o ho => by
      rcases Finset.mem_image.mp ho with ⟨c, _hc, rfl⟩
      change MeasurableSet
        {theta : PG23DifferentialApplicantType College n | choice theta = some c}
      simpa [choice] using
        (pg23DifferentialSourceChoice_fiber_measurable
          (College := College) (n := n) P c))
  calc
    (∑ c : College,
        pg23DifferentialSourceAggregateDemand typeLaw P c) =
        ∑ o ∈ (Finset.univ : Finset College).image some,
          typeLaw.real (choice ⁻¹' ({o} : Set (Option College))) := by
      rw [Finset.sum_image]
      · rfl
      · intro a _ b _ hab
        exact Option.some.inj hab
    _ = typeLaw.real
        (choice ⁻¹' (↑((Finset.univ : Finset College).image some) :
          Set (Option College))) := hsum
    _ = typeLaw.real {theta | ∃ c : College,
          pg23DifferentialSourceChoice P theta = some c} := by
      congr 1
      ext theta
      simp [choice, eq_comm]

/--
At an equal-capacity common cutoff, differential exact clearing fixes the total
matched mass at the source supply `S`.
-/
theorem pg23DifferentialSourceMarketClearing_commonCutoff_matchedMass_eq_supply
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsFiniteMeasure typeLaw] {S p : ℝ}
    (hclear :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw)
        (fun _ : College => S / (Fintype.card College : ℝ))
        (fun _ : College => p)) :
    typeLaw.real {theta | ∃ c : College,
      pg23DifferentialSourceChoice (fun _ : College => p) theta = some c} = S := by
  rw [← pg23DifferentialSourceAggregateDemand_sum_eq_matchedMass typeLaw
    (fun _ : College => p)]
  calc
    (∑ c : College,
        pg23DifferentialSourceAggregateDemand typeLaw (fun _ : College => p) c) =
        ∑ _c : College, S / (Fintype.card College : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _
      exact hclear c
    _ = S := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card College : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp [hcard]

/-- A differential-access applicant always has at least one active application. -/
theorem pg23DifferentialActiveSet_nonempty
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) :
    (pg23DifferentialActiveSet theta).Nonempty := by
  exact
    ⟨theta.2.1.symm ⟨0, Fintype.card_pos⟩,
      pg23TopKApplicationSet_top_mem theta.2.1 (Nat.succ_pos theta.1.val)⟩

/-- Highest raw source score among the active applications of a differential applicant. -/
noncomputable def pg23DifferentialActiveMaxScore
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) : ℝ :=
  (pg23DifferentialActiveSet theta).sup'
    (pg23DifferentialActiveSet_nonempty theta)
    (fun c => pg23SourceScore theta.2 c)

/-- The score of the top-ranked active college is measurable on differential types. -/
theorem pg23DifferentialTopScore_measurable
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ} :
    Measurable
      (fun theta : PG23DifferentialApplicantType College n =>
        pg23SourceScore theta.2
          (theta.2.1.symm ⟨0, Fintype.card_pos⟩)) := by
  classical
  let topScoreSum : PG23DifferentialApplicantType College n -> ℝ :=
    fun theta =>
      ∑ c : College,
        if pg23SourceRank theta.2 c = 0 then pg23SourceScore theta.2 c else 0
  have hsum_meas : Measurable topScoreSum := by
    refine Finset.measurable_sum Finset.univ ?_
    intro c _hc
    have hrank :
        Measurable
          (fun theta : PG23DifferentialApplicantType College n =>
            pg23SourceRank theta.2 c) :=
      (pg23SourceRank_measurable c).comp measurable_snd
    have hscore :
        Measurable
          (fun theta : PG23DifferentialApplicantType College n =>
            pg23SourceScore theta.2 c) :=
      (pg23SourceScore_measurable c).comp measurable_snd
    exact Measurable.ite (measurableSet_eq_fun hrank measurable_const)
      hscore measurable_const
  convert hsum_meas using 1
  funext theta
  let topCollege : College := theta.2.1.symm ⟨0, Fintype.card_pos⟩
  have htop_rank : pg23SourceRank theta.2 topCollege = 0 := by
    change (theta.2.1 topCollege).val = 0
    simp [topCollege]
  change pg23SourceScore theta.2 topCollege =
    ∑ c : College,
      if pg23SourceRank theta.2 c = 0 then pg23SourceScore theta.2 c else 0
  rw [Finset.sum_eq_single topCollege]
  · simp [htop_rank]
  · intro c _hc hc_ne
    have hrank_ne : pg23SourceRank theta.2 c ≠ 0 := by
      intro hrank_zero
      apply hc_ne
      apply theta.2.1.injective
      apply Fin.ext
      change pg23SourceRank theta.2 c = pg23SourceRank theta.2 topCollege
      exact hrank_zero.trans htop_rank.symm
    simp [hrank_ne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ topCollege))

/-- The active maximum score is measurable on differential types. -/
theorem pg23DifferentialActiveMaxScore_measurable
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ} :
    Measurable
      (fun theta : PG23DifferentialApplicantType College n =>
        pg23DifferentialActiveMaxScore theta) := by
  classical
  let topScore : PG23DifferentialApplicantType College n -> ℝ :=
    fun theta =>
      pg23SourceScore theta.2
        (theta.2.1.symm ⟨0, Fintype.card_pos⟩)
  have htop_meas : Measurable topScore :=
    pg23DifferentialTopScore_measurable (College := College) (n := n)
  have hcoord : ∀ c : College,
      Measurable
        (fun theta : PG23DifferentialApplicantType College n =>
          if c ∈ pg23DifferentialActiveSet theta then
            pg23SourceScore theta.2 c
          else topScore theta) := by
    intro c
    exact Measurable.ite
      (pg23DifferentialActiveSet_mem_measurable (College := College) c)
      ((pg23SourceScore_measurable c).comp measurable_snd)
      htop_meas
  have hsup :
      Measurable
        ((Finset.univ : Finset College).sup' Finset.univ_nonempty
          (fun c => fun theta : PG23DifferentialApplicantType College n =>
            if c ∈ pg23DifferentialActiveSet theta then
              pg23SourceScore theta.2 c
            else topScore theta)) :=
    Finset.measurable_sup' Finset.univ_nonempty
      (fun c _hc => hcoord c)
  convert hsup using 1
  funext theta
  simp only [Finset.sup'_apply]
  let active := pg23DifferentialActiveSet theta
  let score : College -> ℝ := fun c => pg23SourceScore theta.2 c
  let topCollege : College := theta.2.1.symm ⟨0, Fintype.card_pos⟩
  have htop_active : topCollege ∈ active := by
    change topCollege ∈
      pg23TopKApplicationSet (theta.1.val + 1) theta.2.1
    simpa [topCollege] using
      (pg23TopKApplicationSet_top_mem theta.2.1 (Nat.succ_pos theta.1.val))
  apply le_antisymm
  · refine Finset.sup'_le (pg23DifferentialActiveSet_nonempty theta) score ?_
    intro c hc
    have hle :=
      Finset.le_sup'
        (fun d : College =>
          if d ∈ active then score d else topScore theta)
        (Finset.mem_univ c)
    simpa [active, score, hc] using hle
  · refine Finset.sup'_le Finset.univ_nonempty
      (fun c : College =>
        if c ∈ pg23DifferentialActiveSet theta then
          pg23SourceScore theta.2 c
        else topScore theta) ?_
    intro c _hc
    by_cases hc_active : c ∈ active
    · have hle : score c ≤ pg23DifferentialActiveMaxScore theta := by
        rw [pg23DifferentialActiveMaxScore, Finset.le_sup'_iff]
        exact ⟨c, hc_active, le_rfl⟩
      simpa [active, score, hc_active] using hle
    · have hle : topScore theta ≤ pg23DifferentialActiveMaxScore theta := by
        rw [pg23DifferentialActiveMaxScore, Finset.le_sup'_iff]
        exact ⟨topCollege, htop_active, by simp [topScore, topCollege]⟩
      simpa [active, score, hc_active] using hle

/-- The law of the active maximum score under a differential-access type law. -/
noncomputable def pg23DifferentialActiveMaxScoreLaw
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n)) : Measure ℝ :=
  Measure.map pg23DifferentialActiveMaxScore typeLaw

/-- Active maximum score pushforward preserves total probability. -/
theorem pg23DifferentialActiveMaxScoreLaw_isProbabilityMeasure
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw] :
    IsProbabilityMeasure
      (pg23DifferentialActiveMaxScoreLaw
        (College := College) typeLaw) := by
  unfold pg23DifferentialActiveMaxScoreLaw
  exact Measure.isProbabilityMeasure_map
    pg23DifferentialActiveMaxScore_measurable.aemeasurable

/--
For random top-k polyculture applications, the active-maximum score law has
the same support as the primitive one-dimensional sum law `v + X`.  The proof
does not condition on a positive-mass access count or ranking atom: to hit a
neighborhood of a primitive noise-support point, require all iid college-noise
coordinates to lie in that neighborhood.
-/
theorem pg23PolycultureDifferentialActiveMaxScoreLaw_support_eq_sumLaw
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    (pg23DifferentialActiveMaxScoreLaw
      (College := College)
      (pg23PolycultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw)).support =
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod noiseLaw)).support := by
  classical
  let rankingLaw : Measure (PG23Ranking College) :=
    pg23UniformRankingLaw (College := College)
  letI : IsProbabilityMeasure rankingLaw :=
    pg23UniformRankingLaw_isProbabilityMeasure (College := College)
  let iidNoiseLaw : Measure (College -> ℝ) := Measure.pi fun _ : College => noiseLaw
  let sampleLaw : Measure (PG23PolycultureSample College) :=
    (valueLaw.prod rankingLaw).prod iidNoiseLaw
  let fullLaw : Measure (Fin n × PG23PolycultureSample College) :=
    accessLaw.prod sampleLaw
  let sampleToDiff :
      Fin n × PG23PolycultureSample College ->
        PG23DifferentialApplicantType College n :=
    fun z => (z.1, pg23PolycultureSampleToType z.2)
  let activeScoreOnSample : Fin n × PG23PolycultureSample College -> ℝ :=
    fun z => pg23DifferentialActiveMaxScore (sampleToDiff z)
  let sumLaw : Measure ℝ :=
    Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (valueLaw.prod noiseLaw)
  have hsampleToDiff_meas : Measurable sampleToDiff := by
    exact measurable_fst.prodMk
      (pg23PolycultureSampleToType_measurable.comp measurable_snd)
  have hactiveScore_meas : Measurable activeScoreOnSample :=
    pg23DifferentialActiveMaxScore_measurable.comp hsampleToDiff_meas
  have hmap_diff :
      Measure.map sampleToDiff fullLaw =
        pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw := by
    simpa [sampleToDiff, fullLaw, sampleLaw, rankingLaw, iidNoiseLaw,
      pg23PolycultureDifferentialTypeLaw, pg23DifferentialTypeLaw,
      pg23PolycultureTypeLaw] using
      (Measure.map_prod_map accessLaw sampleLaw measurable_id
        pg23PolycultureSampleToType_measurable).symm
  have hleft_map :
      Measure.map pg23DifferentialActiveMaxScore
        (pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw) =
        Measure.map activeScoreOnSample fullLaw := by
    rw [← hmap_diff]
    rw [Measure.map_map pg23DifferentialActiveMaxScore_measurable
      hsampleToDiff_meas]
    rfl
  have hscore_eq :
      ∀ z : Fin n × PG23PolycultureSample College,
        activeScoreOnSample z =
          z.2.1.1 +
            (pg23TopKApplicationSet (z.1.val + 1) z.2.1.2).sup'
              ⟨z.2.1.2.symm ⟨0, Fintype.card_pos⟩,
                pg23TopKApplicationSet_top_mem z.2.1.2
                  (Nat.succ_pos z.1.val)⟩
              z.2.2 := by
    intro z
    let active := pg23TopKApplicationSet (z.1.val + 1) z.2.1.2
    let hactive : active.Nonempty :=
      ⟨z.2.1.2.symm ⟨0, Fintype.card_pos⟩,
        pg23TopKApplicationSet_top_mem z.2.1.2 (Nat.succ_pos z.1.val)⟩
    dsimp [activeScoreOnSample, sampleToDiff, pg23DifferentialActiveMaxScore,
      pg23DifferentialActiveSet, pg23PolycultureSampleToType,
      pg23PolycultureType, pg23SourceScore, active]
    change
      active.sup' _ (fun c => z.2.1.1 + z.2.2 c) =
        z.2.1.1 + active.sup' hactive z.2.2
    convert (Finset.add_sup' active z.2.2 z.2.1.1 hactive).symm using 1
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed Measure.isClosed_support
    change ∀ᵐ y ∂pg23DifferentialActiveMaxScoreLaw
        (College := College)
        (pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw),
      y ∈ sumLaw.support
    unfold pg23DifferentialActiveMaxScoreLaw
    rw [hleft_map]
    change sumLaw.support ∈ ae (Measure.map activeScoreOnSample fullLaw)
    rw [mem_ae_map_iff hactiveScore_meas.aemeasurable
      Measure.isClosed_support.measurableSet]
    have hvalue_pair :
        ∀ᵐ pair : ℝ × PG23Ranking College ∂valueLaw.prod rankingLaw,
          pair.1 ∈ valueLaw.support := by
      refine ae_of_ae_map (μ := valueLaw.prod rankingLaw) (f := Prod.fst)
        (p := fun v : ℝ => v ∈ valueLaw.support)
        measurable_fst.aemeasurable ?_
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact Measure.support_mem_ae
    have hvalue_sample :
        ∀ᵐ sample : PG23PolycultureSample College ∂sampleLaw,
          sample.1.1 ∈ valueLaw.support := by
      refine ae_of_ae_map (μ := sampleLaw) (f := Prod.fst)
        (p := fun pair : ℝ × PG23Ranking College =>
          pair.1 ∈ valueLaw.support)
        measurable_fst.aemeasurable ?_
      dsimp [sampleLaw]
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact hvalue_pair
    have hvalue_full :
        ∀ᵐ z : Fin n × PG23PolycultureSample College ∂fullLaw,
          z.2.1.1 ∈ valueLaw.support := by
      refine ae_of_ae_map (μ := fullLaw) (f := Prod.snd)
        (p := fun sample : PG23PolycultureSample College =>
          sample.1.1 ∈ valueLaw.support)
        measurable_snd.aemeasurable ?_
      dsimp [fullLaw]
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact hvalue_sample
    have hnoise_iid :
        ∀ᵐ noise ∂iidNoiseLaw, ∀ c : College, noise c ∈ noiseLaw.support := by
      rw [ae_all_iff]
      intro c
      exact Measure.tendsto_eval_ae_ae.eventually
        (Measure.support_mem_ae (μ := noiseLaw))
    have hnoise_sample :
        ∀ᵐ sample : PG23PolycultureSample College ∂sampleLaw,
          ∀ c : College, sample.2 c ∈ noiseLaw.support := by
      refine ae_of_ae_map (μ := sampleLaw) (f := Prod.snd)
        (p := fun noise : College -> ℝ =>
          ∀ c : College, noise c ∈ noiseLaw.support)
        measurable_snd.aemeasurable ?_
      dsimp [sampleLaw]
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact hnoise_iid
    have hnoise_full :
        ∀ᵐ z : Fin n × PG23PolycultureSample College ∂fullLaw,
          ∀ c : College, z.2.2 c ∈ noiseLaw.support := by
      refine ae_of_ae_map (μ := fullLaw) (f := Prod.snd)
        (p := fun sample : PG23PolycultureSample College =>
          ∀ c : College, sample.2 c ∈ noiseLaw.support)
        measurable_snd.aemeasurable ?_
      dsimp [fullLaw]
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact hnoise_sample
    filter_upwards [hvalue_full, hnoise_full] with z hv hnoise
    let active := pg23TopKApplicationSet (z.1.val + 1) z.2.1.2
    let hactive : active.Nonempty :=
      ⟨z.2.1.2.symm ⟨0, Fintype.card_pos⟩,
        pg23TopKApplicationSet_top_mem z.2.1.2 (Nat.succ_pos z.1.val)⟩
    rcases Finset.exists_mem_eq_sup' hactive z.2.2 with ⟨c, _hc, hc_eq⟩
    have hsummem :
        z.2.1.1 + z.2.2 c ∈ sumLaw.support :=
      pg23_sumLaw_mem_support_of_mem_support valueLaw noiseLaw hv (hnoise c)
    change activeScoreOnSample z ∈ sumLaw.support
    rw [hscore_eq z]
    change
      z.2.1.1 +
          active.sup'
            ⟨z.2.1.2.symm ⟨0, Fintype.card_pos⟩,
              pg23TopKApplicationSet_top_mem z.2.1.2
                (Nat.succ_pos z.1.val)⟩
            z.2.2 ∈ sumLaw.support
    simpa [active, hc_eq] using hsummem
  · intro y hy
    rw [Measure.support_eq_forall_isOpen]
    intro U hyU hU
    rcases pg23_sumLaw_support_open_meets_support_sum
        valueLaw noiseLaw hy hU hyU with
      ⟨v, hv, x, hx, hvxU⟩
    have hadd_nhds :
        ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' U) ∈ 𝓝 (v, x) :=
      (continuous_fst.add continuous_snd).continuousAt (hU.mem_nhds hvxU)
    rcases mem_nhds_prod_iff'.mp hadd_nhds with
      ⟨V, W, hVopen, hvV, hWopen, hxW, hVW⟩
    have hvalueV : 0 < valueLaw V :=
      (Measure.mem_support_iff_forall v).mp hv V (hVopen.mem_nhds hvV)
    have hnoiseW : 0 < noiseLaw W :=
      (Measure.mem_support_iff_forall x).mp hx W (hWopen.mem_nhds hxW)
    let noiseEvent : Set (College -> ℝ) := Set.univ.pi fun _ : College => W
    let sampleEvent : Set (PG23PolycultureSample College) :=
      (V ×ˢ (Set.univ : Set (PG23Ranking College))) ×ˢ noiseEvent
    let fullEvent : Set (Fin n × PG23PolycultureSample College) :=
      (Set.univ : Set (Fin n)) ×ˢ sampleEvent
    have hnoiseEvent_pos : 0 < iidNoiseLaw noiseEvent := by
      dsimp [noiseEvent, iidNoiseLaw]
      rw [Measure.pi_pi]
      exact bot_lt_iff_ne_bot.mpr <|
        Finset.prod_ne_zero_iff.mpr fun _ _ => hnoiseW.ne'
    have hvalueRanking_pos :
        0 < (valueLaw.prod rankingLaw)
          (V ×ˢ (Set.univ : Set (PG23Ranking College))) := by
      rw [Measure.prod_prod]
      apply ENNReal.mul_pos hvalueV.ne'
      rw [measure_univ]
      exact one_ne_zero
    have hsampleEvent_pos : 0 < sampleLaw sampleEvent := by
      dsimp [sampleEvent, sampleLaw]
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos hvalueRanking_pos.ne' hnoiseEvent_pos.ne'
    have hfullEvent_pos : 0 < fullLaw fullEvent := by
      dsimp [fullEvent, fullLaw]
      rw [Measure.prod_prod]
      apply ENNReal.mul_pos
      · rw [measure_univ]
        exact one_ne_zero
      · exact hsampleEvent_pos.ne'
    change 0 < pg23DifferentialActiveMaxScoreLaw
        (College := College)
        (pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw) U
    unfold pg23DifferentialActiveMaxScoreLaw
    rw [hleft_map]
    rw [Measure.map_apply hactiveScore_meas hU.measurableSet]
    apply lt_of_lt_of_le hfullEvent_pos
    apply measure_mono
    intro z hz
    change activeScoreOnSample z ∈ U
    rcases hz with ⟨_hz_access, hz_sample⟩
    rcases hz_sample with ⟨hz_value_rank, hz_noise⟩
    let active := pg23TopKApplicationSet (z.1.val + 1) z.2.1.2
    let hactive : active.Nonempty :=
      ⟨z.2.1.2.symm ⟨0, Fintype.card_pos⟩,
        pg23TopKApplicationSet_top_mem z.2.1.2 (Nat.succ_pos z.1.val)⟩
    rcases Finset.exists_mem_eq_sup' hactive z.2.2 with ⟨c, _hc, hc_eq⟩
    have hpair_mem : (z.2.1.1, z.2.2 c) ∈ V ×ˢ W :=
      ⟨hz_value_rank.1, hz_noise c (Set.mem_univ c)⟩
    have hsumU : z.2.1.1 + z.2.2 c ∈ U :=
      hVW hpair_mem
    rw [hscore_eq z]
    change
      z.2.1.1 +
          active.sup'
            ⟨z.2.1.2.symm ⟨0, Fintype.card_pos⟩,
              pg23TopKApplicationSet_top_mem z.2.1.2
                (Nat.succ_pos z.1.val)⟩
            z.2.2 ∈ U
    simpa [active, hc_eq] using hsumU

/--
Source connected-support primitives imply connected support for the concrete
random top-k active-maximum score law in the polyculture differential economy.
-/
theorem pg23PolycultureDifferentialActiveMaxScoreLaw_connectedSupport
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw) :
    IsPreconnected
      (pg23DifferentialActiveMaxScoreLaw
        (College := College)
        (pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw)).support := by
  rw [pg23PolycultureDifferentialActiveMaxScoreLaw_support_eq_sumLaw
    (College := College) accessLaw valueLaw noiseLaw]
  exact pg23_isPreconnected_support_map_add valueLaw noiseLaw hvalue hnoise

/-- At a common cutoff, differential matching is exactly the weak active-max tail. -/
theorem pg23DifferentialCommonCutoff_matched_iff_activeMaxScore
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (p : ℝ) (theta : PG23DifferentialApplicantType College n) :
    (∃ c : College,
      pg23DifferentialSourceChoice (fun _ : College => p) theta = some c) ↔
      p ≤ pg23DifferentialActiveMaxScore theta := by
  rw [pg23DifferentialSourceChoice, pg23ActiveSourceChoice_some_iff_exists_active_affordable]
  simp only [pg23Affordable]
  constructor
  · rintro ⟨c, hc_active, hc_score⟩
    exact le_trans hc_score
      (Finset.le_sup' (fun d => pg23SourceScore theta.2 d) hc_active)
  · intro hmax
    rcases Finset.exists_mem_eq_sup'
        (pg23DifferentialActiveSet_nonempty theta)
        (fun c => pg23SourceScore theta.2 c) with
      ⟨c, hc_active, hc_eq⟩
    refine ⟨c, hc_active, ?_⟩
    simpa [pg23DifferentialActiveMaxScore, hc_eq] using hmax

/-- The active-max score law's weak tail is exactly common-cutoff matched mass. -/
theorem pg23DifferentialActiveMaxScoreLaw_weakTail_eq_matchedMass
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n)) (p : ℝ) :
    (pg23DifferentialActiveMaxScoreLaw
        (College := College) typeLaw).real (Ici p) =
      typeLaw.real {theta | ∃ c : College,
        pg23DifferentialSourceChoice (fun _ : College => p) theta = some c} := by
  unfold pg23DifferentialActiveMaxScoreLaw
  rw [map_measureReal_apply pg23DifferentialActiveMaxScore_measurable]
  · congr 1
    ext theta
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq]
    exact (pg23DifferentialCommonCutoff_matched_iff_activeMaxScore p theta).symm
  · exact measurableSet_Ici

/--
If the common-cutoff matched-mass event is represented by a connected
one-dimensional active-score law, then common differential exact-clearing
cutoffs are unique.  The later polyculture proof only has to identify this
law for the random top-k active maximum.
-/
theorem pg23DifferentialSourceMarketClearing_commonCutoff_unique_of_matchedTailLaw
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (hconnected : IsPreconnected scoreLaw.support)
    (htail :
      ∀ p : ℝ,
        scoreLaw.real (Ici p) =
          typeLaw.real {theta | ∃ c : College,
            pg23DifferentialSourceChoice (fun _ : College => p) theta = some c})
    {S p q : ℝ} (hS : 0 < S ∧ S < 1)
    (hp :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw)
        (fun _ : College => S / (Fintype.card College : ℝ))
        (fun _ : College => p))
    (hq :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw)
        (fun _ : College => S / (Fintype.card College : ℝ))
        (fun _ : College => q)) :
    p = q := by
  have hp_matched :
      typeLaw.real {theta | ∃ c : College,
        pg23DifferentialSourceChoice (fun _ : College => p) theta = some c} = S :=
    pg23DifferentialSourceMarketClearing_commonCutoff_matchedMass_eq_supply
      (College := College) typeLaw hp
  have hq_matched :
      typeLaw.real {theta | ∃ c : College,
        pg23DifferentialSourceChoice (fun _ : College => q) theta = some c} = S :=
    pg23DifferentialSourceMarketClearing_commonCutoff_matchedMass_eq_supply
      (College := College) typeLaw hq
  exact pg23_cutoff_eq_of_connectedSupport_weakTail_eq
    scoreLaw hconnected hS.1 hS.2
    ((htail p).trans hp_matched) ((htail q).trans hq_matched)

/--
Common differential exact-clearing cutoffs are unique when the concrete active
maximum score law has connected support.
-/
theorem pg23DifferentialSourceMarketClearing_commonCutoff_unique_of_activeMaxScoreConnected
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hconnected :
      IsPreconnected
        (pg23DifferentialActiveMaxScoreLaw
          (College := College) typeLaw).support)
    {S p q : ℝ} (hS : 0 < S ∧ S < 1)
    (hp :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw)
        (fun _ : College => S / (Fintype.card College : ℝ))
        (fun _ : College => p))
    (hq :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw)
        (fun _ : College => S / (Fintype.card College : ℝ))
        (fun _ : College => q)) :
    p = q := by
  let scoreLaw :=
    pg23DifferentialActiveMaxScoreLaw (College := College) typeLaw
  letI : IsProbabilityMeasure scoreLaw :=
    pg23DifferentialActiveMaxScoreLaw_isProbabilityMeasure typeLaw
  exact
    pg23DifferentialSourceMarketClearing_commonCutoff_unique_of_matchedTailLaw
      (College := College) typeLaw scoreLaw hconnected
      (fun r =>
        pg23DifferentialActiveMaxScoreLaw_weakTail_eq_matchedMass
          (College := College) typeLaw r)
      hS hp hq

/--
For monoculture differential access, a common raw exact-clearing cutoff satisfies
the scalar monoculture demand equation.  This discharges the source-to-scalar
bridge used by the differential equal-cutoffs uniqueness proof.
-/
theorem pg23MonocultureDifferentialSourceMarketClearing_commonCutoff_scalar
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    {S p : ℝ}
    (hclear :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ))
          (fun _ : College => p)) :
    pg23MonocultureScalarMatchDemand valueLaw noiseLaw p = S := by
  let baseLaw := pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw
  let diffLaw :=
    pg23MonocultureDifferentialTypeLaw
      (College := College) accessLaw valueLaw noiseLaw
  letI : IsProbabilityMeasure baseLaw :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  letI : IsProbabilityMeasure diffLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hdiff_matched :
      diffLaw.real {theta | ∃ c : College,
        pg23DifferentialSourceChoice (fun _ : College => p) theta = some c} = S :=
    pg23DifferentialSourceMarketClearing_commonCutoff_matchedMass_eq_supply
      (College := College) diffLaw hclear
  have hbase_matched :
      baseLaw.real {theta | ∃ c : College,
        pg23SourceChoice (fun _ : College => p) theta = some c} = S := by
    rw [← pg23MonocultureDifferentialMatchedMass_commonCutoff_eq_baseline
      (College := College) accessLaw valueLaw noiseLaw p]
    exact hdiff_matched
  have hweak :
      (pg23SourceMaxScoreLaw baseLaw).real (Ici p) = S := by
    rw [pg23SourceMaxScoreLaw_weakTail_eq_matchedMass]
    exact hbase_matched
  letI : IsFiniteMeasure (pg23SourceMaxScoreLaw baseLaw) := by
    unfold pg23SourceMaxScoreLaw
    infer_instance
  have hlevel_measure :=
    pg23SourceMaxScoreLaw_level_null_of_scoreLevelNull baseLaw hlevel p
  have hlevel_real :
      (pg23SourceMaxScoreLaw baseLaw).real ({p} : Set ℝ) = 0 := by
    simp [Measure.real, hlevel_measure]
  have hIci_union : Ici p = ({p} : Set ℝ) ∪ Ioi p := by
    ext z
    simp [le_iff_eq_or_lt]
  have hdisjoint : Disjoint ({p} : Set ℝ) (Ioi p) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact (lt_irrefl p) hzp
  have hstrict :
      (pg23SourceMaxScoreLaw baseLaw).real (Ioi p) = S := by
    have hunion := measureReal_union
      (μ := pg23SourceMaxScoreLaw baseLaw) hdisjoint measurableSet_Ioi
    rw [← hIci_union, hweak, hlevel_real] at hunion
    linarith
  have hsum :
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod noiseLaw)).real (Ioi p) = S := by
    rw [pg23MonocultureSourceMaxScoreLaw_eq_sumLaw] at hstrict
    simpa [baseLaw] using hstrict
  rw [pg23MonocultureScalarMatchDemand_eq_sumLaw_strictTail]
  exact hsum

/--
For monoculture differential access, a common raw exact-clearing cutoff also
satisfies the weighted differential scalar demand equation.  The weighted
equation is not an independent source assumption: it is just the baseline
scalar equation plus the finite access-law weights summing to one.
-/
theorem pg23MonocultureDifferentialSourceMarketClearing_commonCutoff_differentialScalar
    {College : Type v} [Fintype College] [Nonempty College] {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    {S p : ℝ}
    (hclear :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ))
          (fun _ : College => p)) :
    pg23MonocultureDifferentialScalarMatchDemand valueLaw noiseLaw
        (pg23DifferentialAccessWeights accessLaw) p = S := by
  rw [pg23MonocultureDifferentialScalarMatchDemand_eq_baseline
    valueLaw noiseLaw (pg23DifferentialAccessWeights accessLaw)
    (pg23DifferentialAccessWeights_sum_eq_one accessLaw) p]
  exact pg23MonocultureDifferentialSourceMarketClearing_commonCutoff_scalar
    (College := College) accessLaw valueLaw noiseLaw hlevel hclear

/--
Monoculture differential-access raw clearing is unique once common raw
differential clearing cutoffs are connected to the scalar monoculture demand
equation.  The scalar equation is the only remaining bridge from the
source-level differential choice rule to the one-dimensional strict-tail proof.
-/
theorem pg23MonocultureDifferentialSourceMarketClearing_unique_of_scalarClearingBridge
    {College : Type v} [Fintype College] [Nonempty College]
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (hscalar_of_clear :
      ∀ p : ℝ,
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23MonocultureDifferentialTypeLaw
                (College := College) accessLaw valueLaw noiseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => p) ->
          pg23MonocultureScalarMatchDemand valueLaw noiseLaw p = S) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q := by
  let baseLaw := pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure baseLaw :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  have hcommon_unique :
      ∀ p q : ℝ,
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => p) ->
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => q) ->
          p = q := by
    intro p q hp hq
    have hp_scalar :
        pg23MonocultureScalarMatchDemand valueLaw noiseLaw p = S :=
      hscalar_of_clear p (by
        simpa [baseLaw, pg23MonocultureDifferentialTypeLaw] using hp)
    have hq_scalar :
        pg23MonocultureScalarMatchDemand valueLaw noiseLaw q = S :=
      hscalar_of_clear q (by
        simpa [baseLaw, pg23MonocultureDifferentialTypeLaw] using hq)
    exact pg23MonocultureScalarMatchDemand_unique_of_connectedSupport
      valueLaw noiseLaw hvalue hnoise hS hp_scalar hq_scalar
  have hunique :=
    pg23DifferentialSourceMarketClearing_unique_of_product_raw_scalar_unique
      (College := College) accessLaw baseLaw hlevel
      (pg23MonocultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
      (fun sigma => pg23MonocultureTypeLaw_relabel sigma valueLaw noiseLaw)
      S hS.1 hS.2
      (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
      hcommon_unique
  simpa [baseLaw, pg23MonocultureDifferentialTypeLaw] using hunique

/--
Monoculture differential-access exact-clearing raw cutoffs are unique under the
same connected-support and score-level-null primitives as the baseline
monoculture Equal Cutoffs Lemma.
-/
theorem pg23MonocultureDifferentialSourceMarketClearing_unique
    {College : Type v} [Fintype College] [Nonempty College]
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q :=
  pg23MonocultureDifferentialSourceMarketClearing_unique_of_scalarClearingBridge
    accessLaw valueLaw noiseLaw hvalue hnoise hlevel S hS
    (fun p hclear =>
      pg23MonocultureDifferentialSourceMarketClearing_commonCutoff_scalar
        accessLaw valueLaw noiseLaw hlevel hclear)

/--
Polyculture differential-access raw clearing is unique once the matched-mass
event at common cutoffs has been identified with the weak upper tail of a
connected one-dimensional active-score law.  This isolates the remaining
polyculture-specific probability proof: the random top-k active maximum has to
be shown to induce such a law.
-/
theorem pg23PolycultureDifferentialSourceMarketClearing_unique_of_matchedTailLaw
    {College : Type v} [Fintype College] [Nonempty College]
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (hconnected : IsPreconnected scoreLaw.support)
    (htail :
      ∀ p : ℝ,
        scoreLaw.real (Ici p) =
          (pg23PolycultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw).real
            {theta | ∃ c : College,
              pg23DifferentialSourceChoice (fun _ : College => p) theta =
                some c}) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q := by
  let baseLaw := pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure baseLaw :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  letI : IsProbabilityMeasure
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have htail_base :
      ∀ p : ℝ,
        scoreLaw.real (Ici p) =
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw).real
            {theta | ∃ c : College,
              pg23DifferentialSourceChoice (fun _ : College => p) theta =
                some c} := by
    intro p
    simpa [baseLaw, pg23PolycultureDifferentialTypeLaw] using htail p
  have hcommon_unique :
      ∀ p q : ℝ,
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => p) ->
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => q) ->
          p = q := by
    intro p q hp hq
    exact
      pg23DifferentialSourceMarketClearing_commonCutoff_unique_of_matchedTailLaw
        (College := College)
        (typeLaw := pg23DifferentialTypeLaw
          (College := College) accessLaw baseLaw)
        scoreLaw hconnected htail_base hS hp hq
  have hunique :=
    pg23DifferentialSourceMarketClearing_unique_of_product_raw_scalar_unique
      (College := College) accessLaw baseLaw hlevel
      (pg23PolycultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
      (fun sigma => pg23PolycultureTypeLaw_relabel sigma valueLaw noiseLaw)
      S hS.1 hS.2
      (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
      hcommon_unique
  simpa [baseLaw, pg23PolycultureDifferentialTypeLaw] using hunique

/--
Polyculture differential-access raw clearing is unique once the concrete
active-maximum score law for random top-k applications has connected support.
-/
theorem pg23PolycultureDifferentialSourceMarketClearing_unique_of_activeMaxScoreConnected
    {College : Type v} [Fintype College] [Nonempty College]
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (hconnected :
      IsPreconnected
        (pg23DifferentialActiveMaxScoreLaw
          (College := College)
          (pg23PolycultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw)).support) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q := by
  let baseLaw := pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure baseLaw :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  letI : IsProbabilityMeasure
      (pg23PolycultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw) := by
    change IsProbabilityMeasure
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
    exact pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  let scoreLaw :=
    pg23DifferentialActiveMaxScoreLaw
      (College := College)
      (pg23PolycultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw)
  letI : IsProbabilityMeasure scoreLaw :=
    pg23DifferentialActiveMaxScoreLaw_isProbabilityMeasure
      (pg23PolycultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw)
  exact
    pg23PolycultureDifferentialSourceMarketClearing_unique_of_matchedTailLaw
      accessLaw valueLaw noiseLaw hlevel S hS scoreLaw hconnected
      (fun r =>
        pg23DifferentialActiveMaxScoreLaw_weakTail_eq_matchedMass
          (College := College)
          (pg23PolycultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw) r)

/--
Polyculture differential-access raw clearing is unique under the source
connected-support primitives.  The random top-k active maximum is handled by
the concrete support equality with the primitive `value + noise` sum law.
-/
theorem pg23PolycultureDifferentialSourceMarketClearing_unique
    {College : Type v} [Fintype College] [Nonempty College]
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q :=
  pg23PolycultureDifferentialSourceMarketClearing_unique_of_activeMaxScoreConnected
    accessLaw valueLaw noiseLaw hlevel S hS
    (pg23PolycultureDifferentialActiveMaxScoreLaw_connectedSupport
      (College := College) accessLaw valueLaw noiseLaw hvalue hnoise)

/--
If baseline monoculture scalar clearing is unique, the differential-access
monoculture scalar clearing cutoff equals the baseline cutoff.  This is the
formal scalar bridge for the source line `P_mono,kappa = P_mono`.
-/
theorem pg23MonocultureDifferentialScalarCutoff_eq_baseline_of_unique
    (valueLaw noiseLaw : Measure ℝ) {n : ℕ} (κ : Fin n -> ℝ)
    (hκ_sum : (∑ k : Fin n, κ k) = 1)
    {Pmono Pdiff S : ℝ}
    (hunique :
      ∀ p q : ℝ,
        pg23MonocultureScalarMatchDemand valueLaw noiseLaw p = S ->
        pg23MonocultureScalarMatchDemand valueLaw noiseLaw q = S ->
        p = q)
    (hmono :
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pmono = S)
    (hdiff :
      pg23MonocultureDifferentialScalarMatchDemand valueLaw noiseLaw κ Pdiff = S) :
    Pdiff = Pmono := by
  have hdiff_base :
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pdiff = S := by
    rwa [pg23MonocultureDifferentialScalarMatchDemand_eq_baseline
      valueLaw noiseLaw κ hκ_sum Pdiff] at hdiff
  exact hunique Pdiff Pmono hdiff_base hmono

/--
Under the paper's connected-support primitives, the differential-access
monoculture scalar clearing cutoff equals the baseline monoculture cutoff.
-/
theorem pg23MonocultureDifferentialScalarCutoff_eq_baseline_of_connectedSupport
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {n : ℕ} (κ : Fin n -> ℝ)
    (hκ_sum : (∑ k : Fin n, κ k) = 1)
    {Pmono Pdiff S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono :
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pmono = S)
    (hdiff :
      pg23MonocultureDifferentialScalarMatchDemand valueLaw noiseLaw κ Pdiff = S) :
    Pdiff = Pmono :=
  pg23MonocultureDifferentialScalarCutoff_eq_baseline_of_unique
    valueLaw noiseLaw κ hκ_sum
    (fun p q hp hq =>
      pg23MonocultureScalarMatchDemand_unique_of_connectedSupport
        valueLaw noiseLaw hvalue hnoise hS hp hq)
    hmono hdiff

/--
PG23 Theorem 3's conditional match-probability clauses.  An index `k : Fin n`
represents exactly `k + 1` applications, enforcing the source domain
`1 <= k + 1 <= n` in the type.  The first clause identifies each monoculture
conditional event with the unrestricted single-noise probability; the second
states the resulting constancy across access counts.
-/
theorem pg23Theorem3_differentialApplicationAccess
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (monoCutoff polyCutoff : ℕ -> ℝ) :
    (∀ (n : ℕ) (k : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v (monoCutoff n) =
        AppliedModelingLib.Probability.upperTailMass noiseLaw (monoCutoff n - v)) ∧
    (∀ (n : ℕ) (k₁ k₂ : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k₁.val + 1) v (monoCutoff n) =
        pg23MonocultureConditionalMatchProbability
          noiseLaw (k₂.val + 1) v (monoCutoff n)) ∧
    (∀ (n : ℕ) (k₁ k₂ : Fin n) (v : ℝ), k₁ ≤ k₂ ->
      AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₁.val + 1) => polyCutoff n) ≤
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₂.val + 1) => polyCutoff n)) ∧
    (∀ (n : ℕ) (v : ℝ), polyCutoff n - v ∈ interior noiseLaw.support ->
      ∀ {k₁ k₂ : Fin n}, k₁ < k₂ ->
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₁.val + 1) => polyCutoff n) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₂.val + 1) => polyCutoff n)) := by
  have hmono : ∀ (n : ℕ) (k : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v (monoCutoff n) =
        AppliedModelingLib.Probability.upperTailMass noiseLaw (monoCutoff n - v) := by
    intro n k v
    exact pg23MonocultureConditionalMatchProbability_succ_eq_upperTailMass
      noiseLaw k.val v (monoCutoff n)
  refine ⟨hmono, ?_, ?_, ?_⟩
  · intro n k₁ k₂ v
    rw [hmono n k₁ v, hmono n k₂ v]
  · intro n k₁ k₂ v hk
    exact theorem3_polycultureAccess_iidProduct_positive_monotone
      noiseLaw polyCutoff n k₁.val k₂.val v hk
  · intro n v hinterior k₁ k₂ hk
    rw [
      AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow,
      AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow]
    have htail_open := pg23_upperTailMass_mem_Ioo_of_mem_interior_support
      noiseLaw hinterior
    have hsum := AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one
      noiseLaw (polyCutoff n - v)
    have hcdf_open :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (polyCutoff n - v) ∈
          Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [htail_open.1, htail_open.2]
    exact theorem3_polycultureAccessProbability_strict_of_cdf_pow
      hcdf_open.1 hcdf_open.2 (Nat.succ_lt_succ hk)

/--
PG23 Theorem 3 with the monoculture scalar bridge `P_mono,kappa = P_mono`
proved from connected-support primitives and explicit κ-weighted scalar
clearing.  The polyculture clauses are stated at the shared
differential-access cutoff `PpolyDiff`.
-/
theorem pg23Theorem3_differentialApplicationAccess_with_monocultureScalarBridge
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {n : ℕ} (κ : Fin n -> ℝ)
    (hκ_sum : (∑ k : Fin n, κ k) = 1)
    {Pmono PmonoDiff PpolyDiff S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono :
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pmono = S)
    (hmonoDiff :
      pg23MonocultureDifferentialScalarMatchDemand
        valueLaw noiseLaw κ PmonoDiff = S) :
    (∀ (k : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v PmonoDiff =
        AppliedModelingLib.Probability.upperTailMass noiseLaw (Pmono - v)) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k₁.val + 1) v PmonoDiff =
        pg23MonocultureConditionalMatchProbability
          noiseLaw (k₂.val + 1) v PmonoDiff) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ), k₁ ≤ k₂ ->
      AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₁.val + 1) => PpolyDiff) ≤
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₂.val + 1) => PpolyDiff)) ∧
    (∀ (v : ℝ), PpolyDiff - v ∈ interior noiseLaw.support ->
      ∀ {k₁ k₂ : Fin n}, k₁ < k₂ ->
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₁.val + 1) => PpolyDiff) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₂.val + 1) => PpolyDiff)) := by
  have hPmono :
    PmonoDiff = Pmono :=
    pg23MonocultureDifferentialScalarCutoff_eq_baseline_of_connectedSupport
      valueLaw noiseLaw hvalue hnoise κ hκ_sum hS hmono hmonoDiff
  have hshared :=
    pg23Theorem3_differentialApplicationAccess
      noiseLaw (fun _ : ℕ => PmonoDiff) (fun _ : ℕ => PpolyDiff)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v
    rw [← hPmono]
    exact pg23MonocultureConditionalMatchProbability_succ_eq_upperTailMass
      noiseLaw k.val v PmonoDiff
  · intro k₁ k₂ v
    exact hshared.2.1 n k₁ k₂ v
  · intro k₁ k₂ v hk
    exact hshared.2.2.1 n k₁ k₂ v hk
  · intro v hregion k₁ k₂ hk
    exact hshared.2.2.2 n v hregion hk

/--
PG23 Theorem 3 with the monoculture scalar bridge stated using the source's
finite probability law over application access.  The κ weights are derived
from `accessLaw`, rather than accepted as separate algebraic premises.
-/
theorem pg23Theorem3_differentialApplicationAccess_with_accessLawScalarBridge
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {n : ℕ} (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    {Pmono PmonoDiff PpolyDiff S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono :
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pmono = S)
    (hmonoDiff :
      pg23MonocultureDifferentialScalarMatchDemand
        valueLaw noiseLaw (pg23DifferentialAccessWeights accessLaw) PmonoDiff = S) :
    (∀ (k : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v PmonoDiff =
        AppliedModelingLib.Probability.upperTailMass noiseLaw (Pmono - v)) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k₁.val + 1) v PmonoDiff =
        pg23MonocultureConditionalMatchProbability
          noiseLaw (k₂.val + 1) v PmonoDiff) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ), k₁ ≤ k₂ ->
      AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₁.val + 1) => PpolyDiff) ≤
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₂.val + 1) => PpolyDiff)) ∧
    (∀ (v : ℝ), PpolyDiff - v ∈ interior noiseLaw.support ->
      ∀ {k₁ k₂ : Fin n}, k₁ < k₂ ->
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₁.val + 1) => PpolyDiff) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₂.val + 1) => PpolyDiff)) :=
  pg23Theorem3_differentialApplicationAccess_with_monocultureScalarBridge
    valueLaw noiseLaw hvalue hnoise
    (pg23DifferentialAccessWeights accessLaw)
    (pg23DifferentialAccessWeights_sum_eq_one accessLaw)
    hS hmono hmonoDiff

end PG23MonocultureMatching

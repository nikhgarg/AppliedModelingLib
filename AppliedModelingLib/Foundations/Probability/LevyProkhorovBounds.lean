import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Levy--Prokhorov Event Bounds

One-sided event transport and the finite continuity estimates used in robust
best-reply arguments. These results are kept outside the general measure-
inequality container so papers that do not use the Levy--Prokhorov metric do
not inherit its imports or change whenever this specialized layer grows.
-/

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped BigOperators ENNReal NNReal MeasureTheory symmDiff

namespace AppliedModelingLib

/--
A coupling controls the Lévy--Prokhorov distance between its two marginal
laws.  It is enough to bound the mass on which the coupled points are at
least `δ` apart; the same `δ` then controls both the spatial thickening and
the additive mass error in the definition of the metric.

This form is useful when two random paths are constructed on one probability
space and are close with high probability.
-/
theorem levyProkhorovEDist_map_le_of_measure_dist_ge_le
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → E}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (δ : ℝ≥0∞)
    (hbad : μ {ω | δ.toReal ≤ dist (X ω) (Y ω)} ≤ δ) :
    levyProkhorovEDist (μ.map X) (μ.map Y) ≤ δ := by
  letI : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hX
  letI : IsProbabilityMeasure (μ.map Y) :=
    Measure.isProbabilityMeasure_map hY
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hδε hεtop hB
  rw [Measure.map_apply_of_aemeasurable hX hB,
    Measure.map_apply_of_aemeasurable hY
      (Metric.isOpen_thickening (δ := ε.toReal) (E := B)).measurableSet]
  have hδtop : δ ≠ ∞ := ne_top_of_lt (hδε.trans hεtop)
  have hδeps : δ.toReal < ε.toReal :=
    ENNReal.toReal_lt_toReal hδtop hεtop.ne |>.mpr hδε
  calc
    μ (X ⁻¹' B) ≤
        μ (Y ⁻¹' Metric.thickening ε.toReal B ∪
          {ω | δ.toReal ≤ dist (X ω) (Y ω)}) := by
      apply measure_mono
      intro ω hω
      by_cases hfar : δ.toReal ≤ dist (X ω) (Y ω)
      · exact Or.inr hfar
      · left
        change Y ω ∈ Metric.thickening ε.toReal B
        rw [Metric.mem_thickening_iff]
        refine ⟨X ω, hω, ?_⟩
        rw [dist_comm]
        exact lt_of_lt_of_le (lt_of_not_ge hfar) hδeps.le
    _ ≤ μ (Y ⁻¹' Metric.thickening ε.toReal B) +
        μ {ω | δ.toReal ≤ dist (X ω) (Y ω)} :=
      measure_union_le _ _
    _ ≤ μ (Y ⁻¹' Metric.thickening ε.toReal B) + ε :=
      by
        simpa [add_comm] using
          add_le_add_left (hbad.trans hδε.le)
            (μ (Y ⁻¹' Metric.thickening ε.toReal B))

/--
If the Lévy--Prokhorov distance is less than `ε`, mass of a measurable event
under `μ` transfers to any event containing its `ε`-thickening under `ν`, up
to the standard additive `ε` loss.  This is the one-sided event form used in
robust best-reply arguments.
-/
theorem measure_le_measure_add_of_levyProkhorovEDist_lt_of_thickening_subset
    {α : Type*} [MeasurableSpace α] [PseudoEMetricSpace α]
    {μ ν : Measure α} {ε : ℝ≥0∞} {E A : Set α}
    (hdist : levyProkhorovEDist μ ν < ε)
    (hE : MeasurableSet E)
    (hthickening : Metric.thickening ε.toReal E ⊆ A) :
    μ E ≤ ν A + ε := by
  calc
    μ E ≤ ν (Metric.thickening ε.toReal E) + ε :=
      left_measure_le_of_levyProkhorovEDist_lt hdist hE
    _ ≤ ν A + ε := add_le_add (measure_mono hthickening) (le_refl ε)

/--
Real-valued form of
`measure_le_measure_add_of_levyProkhorovEDist_lt_of_thickening_subset` for
finite measures.  It exposes the familiar lower bound `μ(E) - ε ≤ ν(A)`.
-/
theorem measureProb_sub_le_measureProb_of_levyProkhorovEDist_lt_of_thickening_subset
    {α : Type*} [MeasurableSpace α] [PseudoEMetricSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ≥0∞} {E A : Set α}
    (hε : ε ≠ ∞)
    (hdist : levyProkhorovEDist μ ν < ε)
    (hE : MeasurableSet E)
    (hthickening : Metric.thickening ε.toReal E ⊆ A) :
    measureProb μ (fun x => x ∈ E) - ε.toReal ≤
      measureProb ν (fun x => x ∈ A) := by
  unfold measureProb
  have hmeasure : μ E ≤ ν A + ε :=
    measure_le_measure_add_of_levyProkhorovEDist_lt_of_thickening_subset
      hdist hE hthickening
  have hνA : ν A ≠ ∞ := measure_ne_top ν A
  have hsum : ν A + ε ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hνA, hε⟩
  have hreal : (μ E).toReal ≤ (ν A + ε).toReal :=
    ENNReal.toReal_mono hsum hmeasure
  rw [ENNReal.toReal_add hνA hε] at hreal
  exact sub_le_iff_le_add.mpr hreal

/--
For a finite family of baseline masses, the sum of natural powers after an
additive loss clipped at zero is continuous in that loss.  This is the scalar
continuity step behind robust finite-event payoff bounds.
-/
theorem continuous_sum_clippedSub_pow {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (n : ℕ) (c : ℝ) :
    Continuous fun ε : ℝ =>
      (∑ i : ι, (max 0 (m i - ε)) ^ n) - c := by
  apply Continuous.sub
  · apply continuous_finset_sum
    intro i _
    exact (continuous_const.max (continuous_const.sub continuous_id)).pow n
  · exact continuous_const

/--
If a finite nonnegative baseline power sum has strict slack over `α`, then a
strictly positive loss smaller than any prescribed positive margin retains the
slack after clipping.  This packages the finite continuity argument used to
choose a Prokhorov radius in robust best-reply proofs.
-/
theorem exists_pos_lt_sum_clippedSub_pow_sub_gt
    {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (n : ℕ) (c α margin : ℝ)
    (hm : ∀ i : ι, 0 ≤ m i) (hmargin : 0 < margin)
    (hprofit : α < (∑ i : ι, (m i) ^ n) - c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < margin ∧
      α < (∑ i : ι, (max 0 (m i - ε)) ^ n) - c := by
  let f : ℝ → ℝ := fun ε =>
    (∑ i : ι, (max 0 (m i - ε)) ^ n) - c
  have hf : Continuous f := continuous_sum_clippedSub_pow m n c
  have hf0 : α < f 0 := by
    unfold f
    have hsum : (∑ i : ι, (max 0 (m i)) ^ n) = ∑ i : ι, (m i) ^ n := by
      apply Finset.sum_congr rfl
      intro i _
      rw [max_eq_right (hm i)]
    simp only [sub_zero]
    rw [hsum]
    exact hprofit
  have hevent : {ε : ℝ | α < f ε} ∈ nhds 0 :=
    hf.continuousAt (Ioi_mem_nhds hf0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε : ℝ := min (δ / 2) (margin / 2)
  have hδhalf : 0 < δ / 2 := half_pos hδ
  have hmarginhalf : 0 < margin / 2 := half_pos hmargin
  have hε : 0 < ε := lt_min hδhalf hmarginhalf
  have hε_margin : ε < margin := by
    calc
      ε ≤ margin / 2 := min_le_right _ _
      _ < margin := by linarith
  refine ⟨ε, hε, hε_margin, ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have hε_δ : ε < δ := by
    calc
      ε ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  simpa [abs_of_pos hε] using hε_δ

end AppliedModelingLib

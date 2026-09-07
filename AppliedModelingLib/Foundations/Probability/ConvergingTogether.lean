import AppliedModelingLib.Foundations.Probability.TendstoInDistributionTight
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Bounded-Lipschitz approximation bounds

This module records the elementary coupling estimate behind
converging-together arguments.  It is stated for arbitrary pseudometric
targets and controls bounded Lipschitz test-function integrals directly, so
it does not silently impose a path-space separability hypothesis.
-/

namespace AppliedModelingLib.Probability

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A measurable map which is continuous almost everywhere under the limiting
law transports weak convergence of probability measures.  This is the
Portmanteau form of the extended continuous-mapping theorem; unlike the
ordinary continuous-mapping API, it permits discontinuities away from the
limit law's full-measure continuity set. -/
theorem ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous
    {ι E F : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {laws : ι → ProbabilityMeasure E} {limitLaw : ProbabilityMeasure E}
    (hlaws : Tendsto laws l (𝓝 limitLaw))
    {map : E → F} (hmap : Measurable map)
    (hcontinuous : ∀ᵐ point ∂(limitLaw : Measure E), ContinuousAt map point) :
    Tendsto (fun index => (laws index).map (f := map) hmap.aemeasurable) l
      (𝓝 (limitLaw.map (f := map) hmap.aemeasurable)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro target htarget
  let source : Set E := map ⁻¹' target
  let exceptional : Set E := {point | ¬ ContinuousAt map point}
  have hexceptional : (limitLaw : Measure E) exceptional = 0 := by
    change (limitLaw : Measure E) {point | ¬ ContinuousAt map point} = 0
    exact ae_iff.mp hcontinuous
  have hclosure : closure source ⊆ source ∪ exceptional := by
    intro point hpoint
    by_cases hpoint_continuous : ContinuousAt map point
    · left
      rw [mem_closure_iff_seq_limit] at hpoint
      obtain ⟨sequence, hsequence_mem, hsequence⟩ := hpoint
      apply htarget.mem_of_tendsto
        (by simpa only [Function.comp_def] using hpoint_continuous.tendsto.comp hsequence)
      exact Eventually.of_forall fun index => hsequence_mem index
    · right
      exact hpoint_continuous
  have hlimitClosure : (limitLaw : Measure E) (closure source) ≤
      (limitLaw : Measure E) source := by
    calc
      (limitLaw : Measure E) (closure source) ≤
          (limitLaw : Measure E) (source ∪ exceptional) := measure_mono hclosure
      _ ≤ (limitLaw : Measure E) source + (limitLaw : Measure E) exceptional :=
        measure_union_le _ _
      _ = (limitLaw : Measure E) source := by rw [hexceptional, add_zero]
  simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
  have hlimitMap : ((limitLaw : Measure E).map map) target =
      (limitLaw : Measure E) source := by
    rw [Measure.map_apply hmap htarget.measurableSet]
  rw [hlimitMap]
  change l.limsup (fun index => ((laws index : Measure E).map map) target) ≤
    (limitLaw : Measure E) source
  have hmapTarget : (fun index => ((laws index : Measure E).map map) target) =
      fun index => (laws index : Measure E) source := by
    funext index
    rw [Measure.map_apply hmap htarget.measurableSet]
  rw [hmapTarget]
  calc
    l.limsup (fun index => (laws index : Measure E) source) ≤
        l.limsup (fun index => (laws index : Measure E) (closure source)) :=
      Filter.limsup_le_limsup (Eventually.of_forall fun index =>
        measure_mono subset_closure)
    _ ≤ (limitLaw : Measure E) (closure source) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlaws isClosed_closure
    _ ≤ (limitLaw : Measure E) source := hlimitClosure

/-- Extended continuous-mapping theorem for convergence in distribution.  A
measurable post-processing map need only be continuous almost everywhere
under the limiting input law. -/
theorem TendstoInDistribution.ae_continuous_comp
    {ι E F Ω' : Type*} {Ω : ι → Type*}
    {m : ∀ index, MeasurableSpace (Ω index)} {μ : ∀ index, Measure (Ω index)}
    [∀ index, IsProbabilityMeasure (μ index)]
    {m' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ∀ index, Ω index → E} {Z : Ω' → E} {l : Filter ι} [l.IsCountablyGenerated]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {map : E → F} (hmap : Measurable map)
    (hcontinuous : ∀ᵐ point ∂ν.map Z, ContinuousAt map point)
    (h : TendstoInDistribution X l Z μ ν) :
    TendstoInDistribution (fun index => map ∘ X index) l (map ∘ Z) μ ν := by
  refine ⟨fun index => hmap.comp_aemeasurable (h.forall_aemeasurable index),
    hmap.comp_aemeasurable h.aemeasurable_limit, ?_⟩
  convert ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous
    h.tendsto hmap hcontinuous
  · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
    rw [AEMeasurable.map_map_of_aemeasurable hmap.aemeasurable
      (h.forall_aemeasurable _)]
  · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
    congr
    rw [AEMeasurable.map_map_of_aemeasurable hmap.aemeasurable h.aemeasurable_limit]

/-- Extended continuous mapping without a globally measurable extension of the
post-processing rule.  It is enough that its compositions with the random
inputs are almost-everywhere measurable.  This is useful for solution maps
which are naturally defined only on a solvable input domain. -/
theorem TendstoInDistribution.ae_continuous_comp_of_comp_aemeasurable
    {ι E F Ω' : Type*} {Ω : ι → Type*}
    {m : ∀ index, MeasurableSpace (Ω index)} {μ : ∀ index, Measure (Ω index)}
    [∀ index, IsProbabilityMeasure (μ index)]
    {m' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ∀ index, Ω index → E} {Z : Ω' → E} {l : Filter ι} [l.IsCountablyGenerated]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {map : E → F}
    (hcomp : ∀ index, AEMeasurable (map ∘ X index) (μ index))
    (hcompLimit : AEMeasurable (map ∘ Z) ν)
    (hcontinuous : ∀ᵐ point ∂ν.map Z, ContinuousAt map point)
    (h : TendstoInDistribution X l Z μ ν) :
    TendstoInDistribution (fun index => map ∘ X index) l (map ∘ Z) μ ν := by
  refine ⟨hcomp, hcompLimit, ?_⟩
  apply tendsto_of_forall_isClosed_limsup_le'
  intro target htarget
  let source : Set E := map ⁻¹' target
  let exceptional : Set E := {point | ¬ ContinuousAt map point}
  have hcontinuousPull : ∀ᵐ omega ∂ν, ContinuousAt map (Z omega) :=
    ae_of_ae_map h.aemeasurable_limit hcontinuous
  have hexceptionalPull : ν (Z ⁻¹' exceptional) = 0 := by
    change ν {omega | ¬ ContinuousAt map (Z omega)} = 0
    exact ae_iff.mp hcontinuousPull
  have hclosure : closure source ⊆ source ∪ exceptional := by
    intro point hpoint
    by_cases hpoint_continuous : ContinuousAt map point
    · left
      rw [mem_closure_iff_seq_limit] at hpoint
      obtain ⟨sequence, hsequence_mem, hsequence⟩ := hpoint
      apply htarget.mem_of_tendsto
        (by simpa only [Function.comp_def] using hpoint_continuous.tendsto.comp hsequence)
      exact Eventually.of_forall fun index => hsequence_mem index
    · right
      exact hpoint_continuous
  have hlimitClosure : (ν : Measure Ω') (Z ⁻¹' closure source) ≤
      (ν : Measure Ω') (Z ⁻¹' source) := by
    calc
      (ν : Measure Ω') (Z ⁻¹' closure source) ≤
          (ν : Measure Ω') (Z ⁻¹' (source ∪ exceptional)) :=
        measure_mono (Set.preimage_mono hclosure)
      _ ≤ (ν : Measure Ω') (Z ⁻¹' source) + (ν : Measure Ω') (Z ⁻¹' exceptional) :=
        measure_union_le _ _
      _ = (ν : Measure Ω') (Z ⁻¹' source) := by rw [hexceptionalPull, add_zero]
  have hlimitMap : ((ν : Measure Ω').map (map ∘ Z)) target =
      (ν : Measure Ω') (Z ⁻¹' source) := by
    rw [Measure.map_apply_of_aemeasurable hcompLimit htarget.measurableSet]
    rfl
  change l.limsup (fun index => ((μ index : Measure (Ω index)).map (map ∘ X index)) target) ≤
    ((ν : Measure Ω').map (map ∘ Z)) target
  rw [hlimitMap]
  have hmapTarget : (fun index =>
      ((μ index : Measure (Ω index)).map (map ∘ X index)) target) =
      fun index => (μ index : Measure (Ω index)) ((X index) ⁻¹' source) := by
    funext index
    rw [Measure.map_apply_of_aemeasurable (hcomp index) htarget.measurableSet]
    rfl
  rw [hmapTarget]
  calc
    l.limsup (fun index => (μ index : Measure (Ω index)) ((X index) ⁻¹' source)) ≤
        l.limsup (fun index => (μ index : Measure (Ω index)) ((X index) ⁻¹' closure source)) :=
      Filter.limsup_le_limsup (Eventually.of_forall fun index =>
        measure_mono (Set.preimage_mono subset_closure))
    _ = l.limsup (fun index =>
        ((μ index : Measure (Ω index)).map (X index)) (closure source)) := by
      congr 1
      funext index
      rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable index)
        isClosed_closure.measurableSet]
    _ ≤ ((ν : Measure Ω').map Z) (closure source) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto isClosed_closure
    _ = (ν : Measure Ω') (Z ⁻¹' closure source) := by
      rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit
        isClosed_closure.measurableSet]
    _ ≤ (ν : Measure Ω') (Z ⁻¹' source) := hlimitClosure

/-- A graph-continuous relation transports weak convergence without requiring
an arbitrary total extension of its output rule.  This is designed for
well-posed path equations: prelimit sample pairs may lie in a solvable domain
whose complement has no canonical solution, while sequential stability at the
limiting input still identifies every closed-set accumulation of outputs. -/
theorem TendstoInDistribution.graph_sequentially_continuous
    {E F Ω' : Type*} {Ω : ℕ → Type*}
    {m : ∀ n, MeasurableSpace (Ω n)} {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {m' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {X : ∀ n, Ω n → E} {Y : ∀ n, Ω n → F}
    {Z : Ω' → E} {W : Ω' → F}
    (hX : TendstoInDistribution X atTop Z μ ν)
    (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hW : AEMeasurable W ν)
    {good : ∀ n, Ω n → Prop}
    (hgood : ∀ n, ∀ᵐ value ∂μ n, good n value)
    (hgraph : ∀ᵐ omega ∂ν, ∀ (indices : ℕ → ℕ)
      (values : (k : ℕ) → Ω (indices k)),
        (∀ k, good (indices k) (values k)) →
        Tendsto indices atTop atTop →
        Tendsto (fun k => X (indices k) (values k)) atTop (𝓝 (Z omega)) →
        Tendsto (fun k => Y (indices k) (values k)) atTop (𝓝 (W omega))) :
    TendstoInDistribution Y atTop W μ ν := by
  refine ⟨hY, hW, ?_⟩
  apply tendsto_of_forall_isClosed_limsup_le'
  intro target htarget
  let graph : ℕ → Set E := fun n => {point | ∃ value : Ω n,
    good n value ∧ point = X n value ∧ Y n value ∈ target}
  let tails : ℕ → Set E := fun threshold =>
    closure (⋃ n ≥ threshold, graph n)
  have htails_closed : ∀ threshold, IsClosed (tails threshold) := fun threshold =>
    isClosed_closure
  have htails_antitone : Antitone tails := by
    intro first second hfirstsecond
    apply closure_mono
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨n, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with ⟨hn, hpoint⟩
    exact Set.mem_iUnion.mpr ⟨n,
      Set.mem_iUnion.mpr ⟨le_trans hfirstsecond hn, hpoint⟩⟩
  have hintersection : ∀ᵐ omega ∂ν,
      Z omega ∈ ⋂ threshold, tails threshold → W omega ∈ target := by
    filter_upwards [hgraph] with omega homega hmem
    have hnear : ∀ k : ℕ, ∃ point ∈ ⋃ n ≥ k, graph n,
        dist (Z omega) point < 1 / ((k + 1 : ℕ) : ℝ) := by
      intro k
      exact Metric.mem_closure_iff.mp (Set.mem_iInter.mp hmem k)
        (1 / ((k + 1 : ℕ) : ℝ)) (by positivity)
    choose points hpoints_mem hpoints_dist using hnear
    have hgraph_mem : ∀ k : ℕ, ∃ index ≥ k, points k ∈ graph index := by
      intro k
      rcases Set.mem_iUnion.mp (hpoints_mem k) with ⟨index, hpoint⟩
      rcases Set.mem_iUnion.mp hpoint with ⟨hindex, hpoint⟩
      exact ⟨index, hindex, hpoint⟩
    choose indices hindices_ge hindices_mem using hgraph_mem
    have hvalue : ∀ k : ℕ, ∃ value : Ω (indices k),
        good (indices k) value ∧ points k = X (indices k) value ∧
          Y (indices k) value ∈ target := by
      intro k
      exact hindices_mem k
    choose values hvalues_good hpoints_eq hvalues_target using hvalue
    have hindices : Tendsto indices atTop atTop := by
      apply tendsto_atTop.2
      intro threshold
      exact Filter.eventually_atTop.2 ⟨threshold, fun k hk =>
        le_trans hk (hindices_ge k)⟩
    have hinputs : Tendsto (fun k => X (indices k) (values k)) atTop (𝓝 (Z omega)) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      obtain ⟨threshold, hthreshold⟩ := exists_nat_one_div_lt hepsilon
      refine ⟨threshold, ?_⟩
      intro k hk
      calc
        dist (X (indices k) (values k)) (Z omega) =
            dist (points k) (Z omega) := by rw [hpoints_eq k]
        _ = dist (Z omega) (points k) := dist_comm _ _
        _ < 1 / ((k + 1 : ℕ) : ℝ) := hpoints_dist k
        _ ≤ 1 / ((threshold + 1 : ℕ) : ℝ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast Nat.add_le_add_right hk 1
        _ < epsilon := by simpa using hthreshold
    have houtputs := homega indices values hvalues_good hindices hinputs
    exact htarget.mem_of_tendsto houtputs (Filter.Eventually.of_forall hvalues_target)
  have hintersection_measure :
      ((ν.map Z) (⋂ threshold, tails threshold)) ≤ ν (W ⁻¹' target) := by
    rw [Measure.map_apply_of_aemeasurable hX.aemeasurable_limit (by
      exact MeasurableSet.iInter fun threshold => (htails_closed threshold).measurableSet)]
    exact measure_mono_ae <| by
      filter_upwards [hintersection] with omega hgood
      change Z omega ∈ ⋂ threshold, tails threshold → W omega ∈ target
      exact hgood
  have htails_tendsto : Tendsto ((ν.map Z) ∘ tails) atTop
      (𝓝 ((ν.map Z) (⋂ threshold, tails threshold))) :=
    tendsto_measure_iInter_atTop
      (fun threshold => (htails_closed threshold).measurableSet.nullMeasurableSet)
      htails_antitone ⟨0, measure_ne_top _ _⟩
  have hmap_target : (ν.map W) target = ν (W ⁻¹' target) :=
    Measure.map_apply_of_aemeasurable hW htarget.measurableSet
  change Filter.limsup (fun n => (μ n).map (Y n) target) atTop ≤
    (ν.map W) target
  rw [hmap_target]
  apply (Filter.limsup_le_iff').mpr
  intro upper hupper
  have hintersection_lt : (ν.map Z) (⋂ threshold, tails threshold) < upper :=
    lt_of_le_of_lt hintersection_measure hupper
  have htail_eventually : ∀ᶠ threshold in atTop, (ν.map Z) (tails threshold) < upper := by
    exact (tendsto_order.1 htails_tendsto).2 upper hintersection_lt
  obtain ⟨threshold, hthreshold⟩ := htail_eventually.exists
  have hpreimage : ∀ᶠ n in atTop,
      (μ n).map (Y n) target ≤ (μ n).map (X n) (tails threshold) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨threshold, fun n hn => hn⟩] with n hn
    rw [Measure.map_apply_of_aemeasurable (hY n) htarget.measurableSet]
    rw [Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n)
      (htails_closed threshold).measurableSet]
    apply measure_mono_ae
    filter_upwards [hgood n] with value hgood_value hvalue
    apply subset_closure
    exact Set.mem_iUnion.mpr ⟨n,
      Set.mem_iUnion.mpr ⟨hn, ⟨value, hgood_value, rfl, hvalue⟩⟩⟩
  have hlimsup : Filter.limsup (fun n => (μ n).map (Y n) target) atTop ≤
      (ν.map Z) (tails threshold) := by
    calc
      Filter.limsup (fun n => (μ n).map (Y n) target) atTop ≤
          Filter.limsup (fun n => (μ n).map (X n) (tails threshold)) atTop :=
        Filter.limsup_le_limsup hpreimage
      _ ≤ (ν.map Z) (tails threshold) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX.tendsto
          (htails_closed threshold)
  exact (eventually_lt_of_limsup_lt (hlimsup.trans_lt hthreshold)).mono
    (fun _ hvalue => hvalue.le)

/-- An almost-everywhere measurable map which lands almost surely in a
measurable support can be represented as a measurable map into that support.
The chosen fallback matters only on the null exceptional set, so the subtype
representative has the same ambient value almost everywhere. -/
theorem AEMeasurable.exists_subtype_mk_of_ae_mem
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {f : Ω → E} {s : Set E}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) (default : s)
    (hmem : ∀ᵐ omega ∂μ, f omega ∈ s) :
    ∃ g : Ω → s, AEMeasurable g μ ∧ ∀ᵐ omega ∂μ, (g omega : E) = f omega := by
  classical
  let representative : Ω → E := hf.mk f
  have hrepresentative_measurable : Measurable representative := hf.measurable_mk
  have hfeq : f =ᵐ[μ] representative := hf.ae_eq_mk
  have hrepresentative_mem : ∀ᵐ omega ∂μ, representative omega ∈ s := by
    filter_upwards [hmem, hfeq] with omega homega heq
    rw [heq] at homega
    exact homega
  let clipped : Ω → E := fun omega =>
    if h : representative omega ∈ s then representative omega else default
  have hclipped_measurable : Measurable clipped := by
    exact Measurable.ite (hs.preimage hrepresentative_measurable)
      hrepresentative_measurable measurable_const
  have hclipped_mem : ∀ omega, clipped omega ∈ s := by
    intro omega
    simp only [clipped]
    split
    · assumption
    · exact default.property
  let g : Ω → s := fun omega => ⟨clipped omega, hclipped_mem omega⟩
  refine ⟨g, hclipped_measurable.subtype_mk.aemeasurable, ?_⟩
  filter_upwards [hrepresentative_mem, hfeq] with omega homega heq
  simp only [g, clipped, dif_pos homega]
  exact heq.symm

/-- If two random variables are close outside a set of controlled mass, every
bounded Lipschitz real-valued test function has close expectations.  The first
term is the Lipschitz cost on the good set; the second uses the test function's
oscillation on the exceptional set. -/
theorem abs_integral_map_sub_le_of_measure_dist_ge
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [Nonempty E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → E}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    {M radius : ℝ} (hM : ∀ first second, dist (F first) (F second) ≤ M)
    (hradius : 0 < radius) :
    |∫ value, F value ∂μ.map X - ∫ value, F value ∂μ.map Y| ≤
      (L : ℝ) * (radius / 2) + M * μ.real {omega | radius / 2 ≤ dist (Y omega) (X omega)} := by
  let center : E := Classical.choice inferInstance
  have hX_integrable : Integrable (fun omega => F (X omega)) μ := by
    refine Integrable.of_bound (hF.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable
      (‖F center‖ + M) (ae_of_all _ fun omega => ?_)
    have hbound := hM (X omega) center
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (X omega)) (F center)).trans hbound
  have hY_integrable : Integrable (fun omega => F (Y omega)) μ := by
    refine Integrable.of_bound (hF.continuous.measurable.comp_aemeasurable hY).aestronglyMeasurable
      (‖F center‖ + M) (ae_of_all _ fun omega => ?_)
    have hbound := hM (Y omega) center
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (Y omega)) (F center)).trans hbound
  have hsub_integrable : Integrable (fun omega => ‖F (Y omega) - F (X omega)‖) μ := by
    exact (hY_integrable.sub hX_integrable).norm
  have hdist : AEMeasurable (fun omega => dist (Y omega) (X omega)) μ := hY.dist hX
  rw [integral_map hX hF.continuous.measurable.aestronglyMeasurable,
    integral_map hY hF.continuous.measurable.aestronglyMeasurable,
    ← integral_sub hX_integrable hY_integrable, ← Real.norm_eq_abs]
  calc
    ‖∫ omega, F (X omega) - F (Y omega) ∂μ‖ =
        ‖∫ omega, F (Y omega) - F (X omega) ∂μ‖ := by
          rw [show (fun omega => F (X omega) - F (Y omega)) =
              fun omega => -(F (Y omega) - F (X omega)) by
                funext omega
                ring,
            integral_neg, norm_neg]
    _ ≤ ∫ omega, ‖F (Y omega) - F (X omega)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ omega in {omega | dist (Y omega) (X omega) < radius / 2},
          ‖F (Y omega) - F (X omega)‖ ∂μ +
        ∫ omega in {omega | radius / 2 ≤ dist (Y omega) (X omega)},
          ‖F (Y omega) - F (X omega)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ hsub_integrable
      exact nullMeasurableSet_lt hdist (measurable_const.aemeasurable)
    _ ≤ ∫ omega in {omega | dist (Y omega) (X omega) < radius / 2},
          (L : ℝ) * (radius / 2) ∂μ +
        ∫ omega in {omega | radius / 2 ≤ dist (Y omega) (X omega)}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ hsub_integrable.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt hdist (measurable_const.aemeasurable)
        · intro omega homega
          simpa only [Real.norm_eq_abs, Real.dist_eq] using
            (hF.dist_le_mul (Y omega) (X omega)).trans
              (mul_le_mul_of_nonneg_left homega.le L.coe_nonneg)
      · refine setIntegral_mono hsub_integrable.integrableOn integrableOn_const fun omega => ?_
        simpa only [Real.norm_eq_abs, Real.dist_eq] using hM (Y omega) (X omega)
    _ = (L : ℝ) * (radius / 2) *
          μ.real {omega | dist (Y omega) (X omega) < radius / 2} +
        M * μ.real {omega | radius / 2 ≤ dist (Y omega) (X omega)} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        Set.univ_inter, smul_eq_mul]
      ring
    _ ≤ (L : ℝ) * (radius / 2) +
        M * μ.real {omega | radius / 2 ≤ dist (Y omega) (X omega)} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]

/-- A cofinal family of common-space approximations transfers convergence in
distribution.  Each fixed approximation may converge weakly to its own limit,
provided those limits converge to the final law and the approximation error is
small in probability along meshes that can be chosen arbitrarily far out.

The second-countability hypothesis is exactly the one used by the standard
bounded-Lipschitz characterization of weak convergence. -/
theorem tendstoInDistribution_of_cofinal_approximations
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [Nonempty E]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E} {approximation : ℕ → ℕ → Ω → E}
    {approximationLimit : ℕ → Ω' → E} {limit : Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) (μ n))
    (happroximation : ∀ radius : ℝ, 0 < radius → ∀ minimum : ℕ,
      ∃ mesh : ℕ, minimum ≤ mesh ∧ ∀ᶠ n : ℕ in atTop,
        (μ n).real {omega | radius / 2 ≤ dist (X n omega) (approximation mesh n omega)} < radius)
    (hfixed : ∀ mesh : ℕ,
      TendstoInDistribution (approximation mesh) atTop (approximationLimit mesh) μ ν)
    (hlimit : TendstoInDistribution approximationLimit atTop limit (fun _ => ν) ν) :
    TendstoInDistribution X atTop limit μ ν := by
  classical
  refine ⟨hX, hlimit.aemeasurable_limit, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hM⟩ ⟨L, hL⟩
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let center : E := Classical.choice inferInstance
  have hM_nonneg : 0 ≤ M := by
    simpa using hM center center
  let scale : ℝ := (L : ℝ) + M + 1
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  let radius : ℝ := epsilon / (6 * scale)
  have hradius : 0 < radius := by
    dsimp [radius]
    exact div_pos hepsilon (mul_pos (by norm_num) hscale_pos)
  have hradius_nonneg : 0 ≤ radius := hradius.le
  have hlimitF := hlimit.tendsto
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hlimitF
  have hlimitF' := hlimitF F ⟨M, hM⟩ ⟨L, hL⟩
  have hlimitNear : ∀ᶠ mesh : ℕ in atTop,
      dist (∫ value, F value ∂ν.map (approximationLimit mesh))
        (∫ value, F value ∂ν.map limit) < epsilon / 3 :=
    (Metric.tendsto_nhds.mp hlimitF') (epsilon / 3) (by linarith)
  obtain ⟨minimum, hminimum⟩ := Filter.eventually_atTop.1 hlimitNear
  obtain ⟨mesh, hminimum_mesh, hmeshApproximation⟩ :=
    happroximation radius hradius minimum
  have hlimitMesh :
      dist (∫ value, F value ∂ν.map (approximationLimit mesh))
        (∫ value, F value ∂ν.map limit) < epsilon / 3 :=
    hminimum mesh hminimum_mesh
  have hfixedF := (hfixed mesh).tendsto
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hfixedF
  have hfixedF' := hfixedF F ⟨M, hM⟩ ⟨L, hL⟩
  have hfixedNear : ∀ᶠ n : ℕ in atTop,
      dist (∫ value, F value ∂(μ n).map (approximation mesh n))
        (∫ value, F value ∂ν.map (approximationLimit mesh)) < epsilon / 3 :=
    (Metric.tendsto_nhds.mp hfixedF') (epsilon / 3) (by linarith)
  filter_upwards [hmeshApproximation, hfixedNear] with n hmesh hn
  have hcoupling := abs_integral_map_sub_le_of_measure_dist_ge (μ n)
    (hX n) ((hfixed mesh).forall_aemeasurable n) hL hM hradius
  have hcoupling' :
      |(∫ value, F value ∂(μ n).map (X n)) -
          ∫ value, F value ∂(μ n).map (approximation mesh n)| < epsilon / 3 := by
    refine lt_of_le_of_lt hcoupling ?_
    have hL_nonneg : 0 ≤ (L : ℝ) := L.coe_nonneg
    have hfirst : (L : ℝ) * (radius / 2) ≤ (L : ℝ) * radius := by
      gcongr
      linarith
    have hsecond : M * (μ n).real
        {omega | radius / 2 ≤ dist (X n omega) (approximation mesh n omega)} ≤ M * radius := by
      gcongr
    have hsum : (L : ℝ) * (radius / 2) + M * (μ n).real
        {omega | radius / 2 ≤ dist (X n omega) (approximation mesh n omega)} ≤ scale * radius := by
      calc
        (L : ℝ) * (radius / 2) + M * (μ n).real
            {omega | radius / 2 ≤ dist (X n omega) (approximation mesh n omega)} ≤
            (L : ℝ) * radius + M * radius := add_le_add hfirst hsecond
        _ ≤ scale * radius := by
          dsimp [scale]
          nlinarith
    have hsum' :
        (L : ℝ) * (radius / 2) + M * (μ n).real
            {omega | radius / 2 ≤ dist (approximation mesh n omega) (X n omega)} ≤
          scale * radius := by
      simpa only [dist_comm] using hsum
    calc
      (L : ℝ) * (radius / 2) + M * (μ n).real
          {omega | radius / 2 ≤ dist (approximation mesh n omega) (X n omega)} ≤
          scale * radius := hsum'
      _ = epsilon / 6 := by
        dsimp [radius]
        field_simp [hscale_pos.ne']
      _ < epsilon / 3 := by linarith
  have hfixedNear' :
      |(∫ value, F value ∂(μ n).map (approximation mesh n)) -
          ∫ value, F value ∂ν.map (approximationLimit mesh)| < epsilon / 3 := by
    simpa only [Real.dist_eq] using hn
  have hlimitMesh' :
      |(∫ value, F value ∂ν.map (approximationLimit mesh)) -
          ∫ value, F value ∂ν.map limit| < epsilon / 3 := by
    simpa only [Real.dist_eq] using hlimitMesh
  rw [Real.dist_eq]
  calc
    |(∫ value, F value ∂(μ n).map (X n)) - ∫ value, F value ∂ν.map limit| ≤
        |(∫ value, F value ∂(μ n).map (X n)) -
            ∫ value, F value ∂(μ n).map (approximation mesh n)| +
          |(∫ value, F value ∂(μ n).map (approximation mesh n)) -
            ∫ value, F value ∂ν.map limit| := by
              exact abs_sub_le _ _ _
    _ ≤ |(∫ value, F value ∂(μ n).map (X n)) -
            ∫ value, F value ∂(μ n).map (approximation mesh n)| +
          (|(∫ value, F value ∂(μ n).map (approximation mesh n)) -
              ∫ value, F value ∂ν.map (approximationLimit mesh)| +
            |(∫ value, F value ∂ν.map (approximationLimit mesh)) -
              ∫ value, F value ∂ν.map limit|) := by
              gcongr
              exact abs_sub_le _ _ _
    _ < epsilon := by linarith

/-- A common-space perturbation which vanishes in probability preserves a
distributional limit, without a separability requirement on the target.  The
proof is the closed-set Portmanteau argument: enlarge a closed target set by a
small closed metric thickening, then control the probability of leaving that
thickening by the perturbation bound. -/
theorem tendstoInDistribution_of_tendstoInDistribution_of_tendstoInProbability_portmanteau
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {X Y : ℕ → Ω → E} {limit : Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) (μ n))
    (hY : TendstoInDistribution Y atTop limit μ ν)
    (hclose : ∀ radius : ℝ, 0 < radius → ∀ᶠ n : ℕ in atTop,
      (μ n).real {omega | radius / 2 ≤ dist (X n omega) (Y n omega)} < radius) :
    TendstoInDistribution X atTop limit μ ν := by
  refine ⟨hX, hY.aemeasurable_limit, ?_⟩
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  change atTop.limsup (fun n => (μ n).map (X n) F) ≤ ν.map limit F
  rw [Measure.map_apply_of_aemeasurable hY.aemeasurable_limit hF.measurableSet]
  have hpreimage_subset (radius : ℝ) :
      ∀ n, (X n) ⁻¹' F ⊆
        (Y n) ⁻¹' Metric.cthickening radius F ∪
          {omega | radius ≤ dist (X n omega) (Y n omega)} := by
    intro n omega homega
    by_cases hfar : radius ≤ dist (X n omega) (Y n omega)
    · exact Or.inr hfar
    · left
      change Y n omega ∈ Metric.cthickening radius F
      rw [Metric.mem_cthickening_iff]
      calc
        Metric.infEDist (Y n omega) F ≤ edist (Y n omega) (X n omega) :=
          Metric.infEDist_le_edist_of_mem homega
        _ ≤ ENNReal.ofReal radius := by
          rw [edist_dist, dist_comm]
          exact ENNReal.ofReal_le_ofReal (lt_of_not_ge hfar).le
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon hlimit_finite
  have hlimitMapF : (ν.map limit) F = ν (limit ⁻¹' F) := by
    rw [Measure.map_apply_of_aemeasurable hY.aemeasurable_limit hF.measurableSet]
  have hlimitMap_finite : (ν.map limit) F < ∞ := by
    rw [hlimitMapF]
    exact hlimit_finite
  have hthick_tendsto :
      Tendsto (fun radius : ℝ => (ν.map limit) (Metric.cthickening radius F))
        (𝓝 0) (𝓝 ((ν.map limit) F)) :=
    tendsto_measure_cthickening_of_isClosed
      ⟨1, by norm_num, measure_ne_top _ _⟩ hF
  have hepsilon_half_pos : 0 < (epsilon : ℝ≥0∞) / 2 := by
    exact ENNReal.div_pos (ENNReal.coe_ne_zero.mpr hepsilon.ne') (by norm_num)
  have hthick_near : ∀ᶠ radius : ℝ in 𝓝 0,
      (ν.map limit) (Metric.cthickening radius F) <
        (ν.map limit) F + (epsilon : ℝ≥0∞) / 2 :=
    hthick_tendsto (Iio_mem_nhds <|
      ENNReal.lt_add_right hlimitMap_finite.ne hepsilon_half_pos.ne')
  rcases Metric.eventually_nhds_iff.mp hthick_near with ⟨delta, hdelta, hdelta_near⟩
  let radius : ℝ := min (delta / 2) ((epsilon : ℝ) / 4)
  have hradius_pos : 0 < radius := by
    dsimp [radius]
    positivity
  have hradius_delta : radius < delta := by
    dsimp [radius]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hradius_epsilon : 2 * radius ≤ (epsilon : ℝ) / 2 := by
    calc
      2 * radius ≤ 2 * ((epsilon : ℝ) / 4) := by
        gcongr
        exact min_le_right _ _
      _ = (epsilon : ℝ) / 2 := by ring
  have hthick_bound : (ν.map limit) (Metric.cthickening radius F) <
      (ν.map limit) F + (epsilon : ℝ≥0∞) / 2 :=
    hdelta_near (by simpa [Real.dist_eq, abs_of_pos hradius_pos] using hradius_delta)
  have hY_thick :
      atTop.limsup (fun n => (μ n) ((Y n) ⁻¹' Metric.cthickening radius F)) ≤
        (ν.map limit) (Metric.cthickening radius F) := by
    have hportmanteau := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      hY.tendsto (Metric.isClosed_cthickening (δ := radius) (E := F))
    convert hportmanteau using 1
    congr 1
    funext n
    change (μ n) (Y n ⁻¹' Metric.cthickening radius F) =
      (μ n).map (Y n) (Metric.cthickening radius F)
    rw [Measure.map_apply_of_aemeasurable (hY.forall_aemeasurable n)
      (Metric.isClosed_cthickening (δ := radius) (E := F)).measurableSet]
  have hepsilon_half : ENNReal.ofReal ((epsilon : ℝ) / 2) =
      (epsilon : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_coe_nnreal]
    norm_num
  have hclose_event : ∀ᶠ n : ℕ in atTop,
      (μ n) {omega | radius ≤ dist (X n omega) (Y n omega)} ≤
        (epsilon : ℝ≥0∞) / 2 := by
    filter_upwards [hclose (2 * radius) (by positivity)] with n hn
    rw [show (2 * radius) / 2 = radius by ring] at hn
    calc
      (μ n) {omega | radius ≤ dist (X n omega) (Y n omega)} =
          ENNReal.ofReal ((μ n).real {omega | radius ≤ dist (X n omega) (Y n omega)}) := by
            rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (2 * radius) :=
        ENNReal.ofReal_le_ofReal hn.le
      _ ≤ ENNReal.ofReal ((epsilon : ℝ) / 2) :=
        ENNReal.ofReal_le_ofReal hradius_epsilon
      _ = (epsilon : ℝ≥0∞) / 2 := hepsilon_half
  have hnear : ∀ᶠ n : ℕ in atTop,
      (μ n) ((X n) ⁻¹' F) ≤
        (μ n) ((Y n) ⁻¹' Metric.cthickening radius F) + (epsilon : ℝ≥0∞) / 2 := by
    filter_upwards [hclose_event] with n hn
    calc
      (μ n) ((X n) ⁻¹' F) ≤
          (μ n) ((Y n) ⁻¹' Metric.cthickening radius F ∪
            {omega | radius ≤ dist (X n omega) (Y n omega)}) :=
        measure_mono (hpreimage_subset radius n)
      _ ≤ (μ n) ((Y n) ⁻¹' Metric.cthickening radius F) +
          (μ n) {omega | radius ≤ dist (X n omega) (Y n omega)} :=
        measure_union_le _ _
      _ ≤ (μ n) ((Y n) ⁻¹' Metric.cthickening radius F) +
          (epsilon : ℝ≥0∞) / 2 := add_le_add_right hn _
  have hY_bounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n => (μ n) ((Y n) ⁻¹' Metric.cthickening radius F)) := by
    apply BddAbove.isBoundedUnder Filter.univ_mem
    refine ⟨1, ?_⟩
    rintro _ ⟨n, -, rfl⟩
    calc
      (μ n) ((Y n) ⁻¹' Metric.cthickening radius F) ≤ (μ n) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hY_cobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => (μ n) ((Y n) ⁻¹' Metric.cthickening radius F)) :=
    Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
  have hX_map : ∀ n, (μ n).map (X n) F = (μ n) ((X n) ⁻¹' F) := by
    intro n
    rw [Measure.map_apply_of_aemeasurable (hX n) hF.measurableSet]
  calc
    atTop.limsup (fun n => (μ n).map (X n) F) =
        atTop.limsup (fun n => (μ n) ((X n) ⁻¹' F)) := by
      congr 1
      funext n
      exact hX_map n
    _ ≤ atTop.limsup (fun n =>
        (μ n) ((Y n) ⁻¹' Metric.cthickening radius F) + (epsilon : ℝ≥0∞) / 2) :=
      Filter.limsup_le_limsup hnear
    _ = atTop.limsup (fun n => (μ n) ((Y n) ⁻¹' Metric.cthickening radius F)) +
        (epsilon : ℝ≥0∞) / 2 := by
      rw [limsup_add_const atTop _ _ hY_bounded hY_cobounded]
    _ ≤ (ν.map limit) (Metric.cthickening radius F) + (epsilon : ℝ≥0∞) / 2 :=
      add_le_add_left hY_thick _
    _ ≤ ((ν.map limit) F + (epsilon : ℝ≥0∞) / 2) + (epsilon : ℝ≥0∞) / 2 :=
      add_le_add_left hthick_bound.le _
    _ = ν (limit ⁻¹' F) + (epsilon : ℝ≥0∞) := by
      rw [hlimitMapF, add_assoc, ENNReal.add_halves]

/-- A common-space perturbation which vanishes in probability preserves a
distributional limit.  This is the one-approximation specialization of the
cofinal converging-together argument above. -/
theorem tendstoInDistribution_of_tendstoInDistribution_of_tendstoInProbability
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [Nonempty E]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {X Y : ℕ → Ω → E} {limit : Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) (μ n))
    (hY : TendstoInDistribution Y atTop limit μ ν)
    (hclose : ∀ radius : ℝ, 0 < radius → ∀ᶠ n : ℕ in atTop,
      (μ n).real {omega | radius / 2 ≤ dist (X n omega) (Y n omega)} < radius) :
    TendstoInDistribution X atTop limit μ ν := by
  have hself : TendstoInDistribution (fun _ : ℕ => limit) atTop limit
      (fun _ : ℕ => ν) ν := by
    apply tendstoInDistribution_of_ae_tendsto
      (fun _ => hY.aemeasurable_limit) hY.aemeasurable_limit
    filter_upwards with omega
    exact tendsto_const_nhds
  refine tendstoInDistribution_of_cofinal_approximations
    (μ := μ) (ν := ν) (X := X)
    (approximation := fun _ : ℕ => Y)
    (approximationLimit := fun _ : ℕ => limit)
    hX ?_ (fun _ => hY) hself
  intro radius hradius minimum
  exact ⟨minimum, le_rfl, hclose radius hradius⟩

/-- Independent weakly convergent probability laws have weakly convergent
product laws.  This is the measure-level joint-convergence step used before a
continuous mapping combines independently generated stochastic components. -/
theorem tendsto_probabilityMeasure_prod
    {ι E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [MeasurableSpace E] [MeasurableSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [TopologicalSpace.PseudoMetrizableSpace E] [TopologicalSpace.PseudoMetrizableSpace F]
    [OpensMeasurableSpace E] [OpensMeasurableSpace F]
    {l : Filter ι} {first : ι → ProbabilityMeasure E} {second : ι → ProbabilityMeasure F}
    {firstLimit : ProbabilityMeasure E} {secondLimit : ProbabilityMeasure F}
    (hfirst : Tendsto first l (𝓝 firstLimit))
    (hsecond : Tendsto second l (𝓝 secondLimit)) :
    Tendsto (fun index => (first index).prod (second index)) l
      (𝓝 (firstLimit.prod secondLimit)) := by
  exact (ProbabilityMeasure.continuous_prod.tendsto _).comp
    (hfirst.prodMk_nhds hsecond)

/-- Independent coordinatewise weak convergence gives joint weak convergence.
Unlike the constant-coordinate Slutsky rule, this permits both coordinates to
have nontrivial limiting laws, provided their prelimit and limiting pairs are
independent. -/
theorem tendstoInDistribution_prodMk_of_indepFun
    {ι E F : Type*} {Ω : ι → Type*} {Ω' : Type*}
    {mΩ : ∀ n, MeasurableSpace (Ω n)} {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [SecondCountableTopology F]
    [TopologicalSpace.PseudoMetrizableSpace F] [OpensMeasurableSpace F]
    {l : Filter ι} {X : ∀ n, Ω n → E} {Y : ∀ n, Ω n → F}
    {Z : Ω' → E} {W : Ω' → F}
    (hX : TendstoInDistribution X l Z μ ν)
    (hY : TendstoInDistribution Y l W μ ν)
    (hpre : ∀ n, IndepFun (X n) (Y n) (μ n))
    (hlimit : IndepFun Z W ν) :
    TendstoInDistribution (fun n omega => (X n omega, Y n omega)) l
      (fun omega => (Z omega, W omega)) μ ν := by
  refine ⟨fun n => (hX.forall_aemeasurable n).prodMk
    (hY.forall_aemeasurable n), hX.aemeasurable_limit.prodMk
      hY.aemeasurable_limit, ?_⟩
  have hproduct := tendsto_probabilityMeasure_prod hX.tendsto hY.tendsto
  have hpre_map (n : ι) :
      Measure.map (fun omega => (X n omega, Y n omega)) (μ n) =
        (Measure.map (X n) (μ n)).prod (Measure.map (Y n) (μ n)) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (hX.forall_aemeasurable n) (hY.forall_aemeasurable n)).1 (hpre n)
  have hlimit_map :
      Measure.map (fun omega => (Z omega, W omega)) ν =
        (Measure.map Z ν).prod (Measure.map W ν) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable_limit hY.aemeasurable_limit).1 hlimit
  simpa only [hpre_map, hlimit_map] using hproduct

/-- A sequence with varying probability spaces converges in distribution to a
constant whenever its distance from that constant vanishes in probability.
This is the constant-limit specialization of the bounded-Lipschitz coupling
argument, stated separately because it is frequently the final step for a
negligible stochastic error term. -/
theorem tendstoInDistribution_of_tendstoInProbability_const
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [Nonempty E]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E} {limit : E}
    (hX : ∀ n, AEMeasurable (X n) (μ n))
    (hclose : ∀ radius : ℝ, 0 < radius → ∀ᶠ n : ℕ in atTop,
      (μ n).real {omega | radius / 2 ≤ dist (X n omega) limit} < radius) :
    TendstoInDistribution X atTop (fun _ : Ω' => limit) μ ν := by
  classical
  refine ⟨hX, measurable_const.aemeasurable, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hM⟩ ⟨L, hL⟩
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let center : E := Classical.choice inferInstance
  have hM_nonneg : 0 ≤ M := by
    simpa using hM center center
  let scale : ℝ := (L : ℝ) + M + 1
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  let radius : ℝ := epsilon / (3 * scale)
  have hradius : 0 < radius := by
    dsimp [radius]
    exact div_pos hepsilon (mul_pos (by norm_num) hscale_pos)
  have hclose' := hclose radius hradius
  filter_upwards [hclose'] with n hn
  have hconstant : AEMeasurable (fun _ : Ω => limit) (μ n) :=
    measurable_const.aemeasurable
  have hcoupling := abs_integral_map_sub_le_of_measure_dist_ge (μ n)
    (hX n) hconstant hL hM hradius
  have hconstantIntegral :
      (∫ value, F value ∂(μ n).map (fun _ : Ω => limit)) = F limit := by
    rw [integral_map hconstant hL.continuous.measurable.aestronglyMeasurable]
    simp
  have hcoupling' :
      |(∫ value, F value ∂(μ n).map (X n)) - F limit| ≤
        (L : ℝ) * (radius / 2) + M * (μ n).real
          {omega | radius / 2 ≤ dist (X n omega) limit} := by
    rw [← hconstantIntegral]
    simpa only [dist_comm] using hcoupling
  have hcoupling'' :
      |(∫ value, F value ∂(μ n).map (X n)) - F limit| < epsilon := by
    refine lt_of_le_of_lt hcoupling' ?_
    · have hL_nonneg : 0 ≤ (L : ℝ) := L.coe_nonneg
      have hfirst : (L : ℝ) * (radius / 2) ≤ (L : ℝ) * radius := by
        gcongr
        linarith
      have hsecond : M * (μ n).real
          {omega | radius / 2 ≤ dist (X n omega) limit} ≤ M * radius := by
        gcongr
      have hsum : (L : ℝ) * (radius / 2) + M * (μ n).real
          {omega | radius / 2 ≤ dist (X n omega) limit} ≤ scale * radius := by
        calc
          (L : ℝ) * (radius / 2) + M * (μ n).real
              {omega | radius / 2 ≤ dist (X n omega) limit} ≤
              (L : ℝ) * radius + M * radius := add_le_add hfirst hsecond
          _ ≤ scale * radius := by
            dsimp [scale]
            nlinarith
      calc
        (L : ℝ) * (radius / 2) + M * (μ n).real
            {omega | radius / 2 ≤ dist (X n omega) limit} ≤ scale * radius := hsum
        _ = epsilon / 3 := by
          dsimp [radius]
          field_simp [hscale_pos.ne']
        _ < epsilon := by linarith
  rw [Real.dist_eq]
  have hlimitConstant : AEMeasurable (fun _ : Ω' => limit) ν :=
    measurable_const.aemeasurable
  have hlimitIntegral :
      (∫ value, F value ∂ν.map (fun _ : Ω' => limit)) = F limit := by
    rw [integral_map hlimitConstant hL.continuous.measurable.aestronglyMeasurable]
    simp
  change |(∫ value, F value ∂(μ n).map (X n)) -
      ∫ value, F value ∂ν.map (fun _ : Ω' => limit)| < epsilon
  rw [hlimitIntegral]
  exact hcoupling''

/-- Exact equality of the prelimit pushforward laws transports convergence in
distribution across different canonical sample spaces.  This is useful when
an auxiliary marked construction has the same output law as the source model. -/
theorem tendstoInDistribution_of_map_eq
    {ι E ΩLimit : Type*} {Ω Ω' : ι → Type*}
    [∀ index, MeasurableSpace (Ω index)]
    [∀ index, MeasurableSpace (Ω' index)]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace ΩLimit]
    {μ : ∀ index : ι, Measure (Ω index)}
    {μ' : ∀ index : ι, Measure (Ω' index)}
    [∀ index, IsProbabilityMeasure (μ index)]
    [∀ index, IsProbabilityMeasure (μ' index)]
    {ν : Measure ΩLimit} [IsProbabilityMeasure ν]
    {X : ∀ index : ι, Ω index → E} {Y : ∀ index : ι, Ω' index → E}
    {limit : ΩLimit → E} {filter : Filter ι}
    (hX : TendstoInDistribution X filter limit μ ν)
    (hY_measurable : ∀ index, AEMeasurable (Y index) (μ' index))
    (hmap : ∀ index,
      Measure.map (Y index) (μ' index) = Measure.map (X index) (μ index)) :
    TendstoInDistribution Y filter limit μ' ν := by
  refine ⟨hY_measurable, hX.aemeasurable_limit, ?_⟩
  convert hX.tendsto using 1
  funext index
  apply Subtype.ext
  exact hmap index

end AppliedModelingLib.Probability

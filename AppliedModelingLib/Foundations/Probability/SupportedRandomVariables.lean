import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Random variables supported almost everywhere on a measurable set

This module gives a total subtype-valued representative of a random variable
whose values lie in a measurable set almost everywhere.  The representative
keeps the original value on that full-measure event and uses a supplied point
of the support elsewhere.  It is useful when weak-convergence arguments take
place on a separable support rather than on an ambient path space.
-/

namespace AppliedModelingLib.Probability

open Filter MeasureTheory Topology

/-- The total subtype-valued representative of `f` that retains `f x` whenever
it lies in `s` and otherwise uses `base`. -/
noncomputable def aeCodRestrict {Ω E : Type*} {s : Set E} (base : s)
    (f : Ω → E) : Ω → s := by
  classical
  exact fun x => if hx : f x ∈ s then ⟨f x, hx⟩ else base

/-- On the support event, coercing the total representative recovers the
original random-variable value. -/
theorem aeCodRestrict_coe_eq {Ω E : Type*} {s : Set E} (base : s)
    (f : Ω → E) {x : Ω} (hx : f x ∈ s) :
    ((aeCodRestrict base f x : s) : E) = f x := by
  classical
  simp [aeCodRestrict, hx]

/-- If `f` is supported on `s` almost everywhere, its total representative
has the same ambient value almost everywhere. -/
theorem aeCodRestrict_coe_ae_eq {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set E} (base : s) (f : Ω → E)
    (hmem : ∀ᵐ x ∂μ, f x ∈ s) :
    (fun x => ((aeCodRestrict base f x : s) : E)) =ᵐ[μ] f := by
  filter_upwards [hmem] with x hx
  exact aeCodRestrict_coe_eq base f hx

/-- Almost-everywhere measurable ambient random variables admit an
almost-everywhere measurable total representative on every measurable support
that contains them almost surely. -/
theorem AEMeasurable.aeCodRestrict {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {μ : Measure Ω} {s : Set E} (base : s) {f : Ω → E}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s)
    (hmem : ∀ᵐ x ∂μ, f x ∈ s) :
    AEMeasurable (aeCodRestrict base f) μ := by
  classical
  let g : Ω → E := AEMeasurable.mk f hf
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have hg : Measurable g := hf.measurable_mk
  have hgmem : ∀ᵐ x ∂μ, g x ∈ s := by
    filter_upwards [hfg, hmem] with x hfgx hmemx
    exact hfgx ▸ hmemx
  let g' : Ω → s := fun x =>
    if hx : g x ∈ s then ⟨g x, hx⟩ else base
  have hpreimage : MeasurableSet {x | g x ∈ s} := hs.preimage hg
  have hgood : Measurable (fun x : {x | g x ∈ s} =>
      (⟨g x, x.property⟩ : s)) := by
    exact (hg.comp measurable_subtype_coe).subtype_mk
  have hbad : Measurable (fun _ : {x | g x ∉ s} => base) := measurable_const
  have hg' : Measurable g' := by
    exact Measurable.dite hgood hbad hpreimage
  apply hg'.aemeasurable.congr
  filter_upwards [hfg, hmem, hgmem] with x hfgx hmemx hgmemx
  change (if hx : g x ∈ s then ⟨g x, hx⟩ else base) =
    AppliedModelingLib.Probability.aeCodRestrict base f x
  rw [dif_pos hgmemx]
  rw [show AppliedModelingLib.Probability.aeCodRestrict base f x = ⟨f x, hmemx⟩ by
    simp [AppliedModelingLib.Probability.aeCodRestrict, hmemx]]
  exact Subtype.ext hfgx.symm

/-- Weak convergence in an ambient pseudometric space restricts to any
measurable, second-countable support that contains the prelimit and limit
random variables almost surely.  The proof extends each Lipschitz test
function on the support to the ambient space and then uses equality of the
two random variables on the support event. -/
theorem tendstoInDistribution_aeCodRestrict
    {ι Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {s : Set E} (base : s)
    [SecondCountableTopology s] [BorelSpace s]
    {X : ι → Ω → E} {Z : Ω' → E} {l : Filter ι} [Filter.IsCountablyGenerated l]
    (h : TendstoInDistribution X l Z μ ν) (hs : MeasurableSet s)
    (hX : ∀ i, ∀ᵐ x ∂μ i, X i x ∈ s)
    (hZ : ∀ᵐ z ∂ν, Z z ∈ s) :
    TendstoInDistribution
      (fun i => aeCodRestrict base (X i)) l
      (aeCodRestrict base Z) μ ν := by
  classical
  have hXmeas : ∀ i, AEMeasurable (aeCodRestrict base (X i)) (μ i) :=
    fun i => AEMeasurable.aeCodRestrict base (h.forall_aemeasurable i) hs (hX i)
  have hZmeas : AEMeasurable (aeCodRestrict base Z) ν :=
    AEMeasurable.aeCodRestrict base h.aemeasurable_limit hs hZ
  refine ⟨hXmeas, hZmeas, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hM⟩ ⟨L, hL⟩
  let f : E → ℝ := fun x => if hx : x ∈ s then F ⟨x, hx⟩ else F base
  have hf : LipschitzOnWith L f s := by
    intro x hx y hy
    simp only [f, dif_pos hx, dif_pos hy]
    simpa only [edist_dist] using hL ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨G, hG, hG_eq⟩ := hf.extend_real
  have hM_nonneg : 0 ≤ M := by
    exact (dist_nonneg.trans (hM base base))
  let Gclip : E → ℝ := fun x =>
    max (F base - M) (min (F base + M) (G x))
  have hGclip : LipschitzWith L Gclip := by
    dsimp [Gclip]
    simpa using
      (LipschitzWith.const (α := E) (F base - M)).max
        ((LipschitzWith.const (α := E) (F base + M)).min hG)
  have hGclip_lower : ∀ x, F base - M ≤ Gclip x := by
    intro x
    exact le_max_left _ _
  have hGclip_upper : ∀ x, Gclip x ≤ F base + M := by
    intro x
    dsimp [Gclip]
    exact max_le (by linarith [hM_nonneg]) (min_le_left _ _)
  have hGclipBound : ∀ x y, dist (Gclip x) (Gclip y) ≤ 2 * M := by
    intro x y
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [hGclip_lower x, hGclip_upper x,
      hGclip_lower y, hGclip_upper y]
  have hGclip_eq : Set.EqOn f Gclip s := by
    intro x hx
    have hbound := hM ⟨x, hx⟩ base
    rw [Real.dist_eq, abs_sub_le_iff] at hbound
    have hlow : F base - M ≤ F ⟨x, hx⟩ := by linarith [hbound.2]
    have hupp : F ⟨x, hx⟩ ≤ F base + M := by linarith [hbound.1]
    dsimp [Gclip]
    rw [← hG_eq hx]
    simp only [f, dif_pos hx, min_eq_right hupp, max_eq_right hlow]
  let Hclip : ℝ → ℝ := fun r => max (F base - M) (min (F base + M) r)
  have hHclip : LipschitzWith 1 Hclip := by
    dsimp [Hclip]
    simpa using
      (LipschitzWith.const (α := ℝ) (F base - M)).max
        ((LipschitzWith.const (α := ℝ) (F base + M)).min
          (LipschitzWith.id : LipschitzWith 1 (fun r : ℝ => r)))
  have hHclip_lower : ∀ r, F base - M ≤ Hclip r := by
    intro r
    exact le_max_left _ _
  have hHclip_upper : ∀ r, Hclip r ≤ F base + M := by
    intro r
    dsimp [Hclip]
    exact max_le (by linarith [hM_nonneg]) (min_le_left _ _)
  have hHclipBound : ∀ r q, dist (Hclip r) (Hclip q) ≤ 2 * M := by
    intro r q
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [hHclip_lower r, hHclip_upper r,
      hHclip_lower q, hHclip_upper q]
  have hHclip_Gclip : ∀ x, Hclip (Gclip x) = Gclip x := by
    intro x
    dsimp [Hclip]
    rw [min_eq_right (hGclip_upper x), max_eq_right (hGclip_lower x)]
  have hGdist := TendstoInDistribution.continuous_comp hGclip.continuous h
  have hGintegral := hGdist.tendsto
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hGintegral
  have hGintegral' := hGintegral Hclip ⟨2 * M, hHclipBound⟩ ⟨1, hHclip⟩
  have hGcomp_eq : ∀ i,
      (∫ r, Hclip r ∂(μ i).map (Gclip ∘ X i)) =
        ∫ x, Gclip x ∂(μ i).map (X i) := by
    intro i
    rw [integral_map
      (hGclip.continuous.measurable.comp_aemeasurable (h.forall_aemeasurable i))
      hHclip.continuous.measurable.aestronglyMeasurable,
      integral_map (h.forall_aemeasurable i) hGclip.continuous.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with x
    exact hHclip_Gclip (X i x)
  have hGcomp_limit_eq :
      (∫ r, Hclip r ∂ν.map (Gclip ∘ Z)) =
        ∫ z, Gclip z ∂ν.map Z := by
    rw [integral_map
      (hGclip.continuous.measurable.comp_aemeasurable h.aemeasurable_limit)
      hHclip.continuous.measurable.aestronglyMeasurable,
      integral_map h.aemeasurable_limit hGclip.continuous.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with z
    exact hHclip_Gclip (Z z)
  have hGintegral'' : Tendsto (fun i => ∫ x, Gclip x ∂(μ i).map (X i)) l
      (𝓝 (∫ z, Gclip z ∂ν.map Z)) := by
    convert hGintegral' using 1
    · funext i
      exact (hGcomp_eq i).symm
    · exact congrArg nhds hGcomp_limit_eq.symm
  have hXeq : ∀ i,
      (∫ y, F y ∂(μ i).map (aeCodRestrict base (X i))) =
        ∫ x, Gclip x ∂(μ i).map (X i) := by
    intro i
    rw [integral_map (hXmeas i) hL.continuous.measurable.aestronglyMeasurable,
      integral_map (h.forall_aemeasurable i) hGclip.continuous.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hX i] with x hx
    rw [show aeCodRestrict base (X i) x = ⟨X i x, hx⟩ by
      simp [aeCodRestrict, hx]]
    simpa only [f, dif_pos hx] using hGclip_eq hx
  have hZeq :
      (∫ y, F y ∂ν.map (aeCodRestrict base Z)) =
        ∫ z, Gclip z ∂ν.map Z := by
    rw [integral_map hZmeas hL.continuous.measurable.aestronglyMeasurable,
      integral_map h.aemeasurable_limit hGclip.continuous.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hZ] with z hz
    rw [show aeCodRestrict base Z z = ⟨Z z, hz⟩ by simp [aeCodRestrict, hz]]
    simpa only [f, dif_pos hz] using hGclip_eq hz
  convert hGintegral'' using 1
  · funext i
    exact hXeq i
  · exact congrArg nhds hZeq

end AppliedModelingLib.Probability

import AppliedModelingLib.Foundations.Probability.LargeDeviations
import AppliedModelingLib.Foundations.Math.IntegralConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Integral Large-Deviation Bounds

Reusable bridges from pointwise or almost-everywhere exponential envelopes to
exponential-rate bounds for integrals.

These lemmas cover the upper-bound half of the compact Laplace-principle
arguments that appear in continuous EconCS large-deviation papers: once an
error kernel is dominated by `C * exp (-n * rate)` almost everywhere, its
finite-measure integral has the same exponential upper bound up to a constant
prefactor.
-/

open Filter Topology MeasureTheory

namespace AppliedModelingLib
namespace Probability

noncomputable section

/--
Integral monotonicity for nonnegative functions over nested measurable
regions.  This packages the common Laplace/minorant step: a local witness
region contributes no more than the containing global error integral when the
integrand is nonnegative on the global region.
-/
theorem setIntegral_mono_subset_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {s t : Set α}
    (hf_int : IntegrableOn f t μ)
    (hf_nonneg : ∀ᵐ x ∂μ.restrict t, 0 ≤ f x)
    (hst : s ⊆ t) :
    ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
  setIntegral_mono_set hf_int hf_nonneg (Eventually.of_forall hst)

/--
Local-to-global integral monotonicity when the local witness integrand is
written differently from the global integrand but agrees on the witness set.
This is useful for paper conventions that zero out some global events while
retaining a raw large-deviation kernel on the local obstruction region.
-/
theorem setIntegral_mono_subset_of_eqOn_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {localF globalF : α → ℝ} {s t : Set α}
    (hs : MeasurableSet s)
    (hglobal_int : IntegrableOn globalF t μ)
    (hglobal_nonneg : ∀ᵐ x ∂μ.restrict t, 0 ≤ globalF x)
    (hst : s ⊆ t)
    (heq : Set.EqOn localF globalF s) :
    ∫ x in s, localF x ∂μ ≤ ∫ x in t, globalF x ∂μ := by
  calc
    ∫ x in s, localF x ∂μ = ∫ x in s, globalF x ∂μ :=
      setIntegral_congr_fun hs heq
    _ ≤ ∫ x in t, globalF x ∂μ :=
      setIntegral_mono_subset_of_ae_nonneg hglobal_int hglobal_nonneg hst

/--
Local-to-global integral monotonicity when the local witness integrand is
pointwise bounded above by the global integrand on the witness set.  This is
the inequality version of `setIntegral_mono_subset_of_eqOn_of_ae_nonneg`,
useful when a paper convention keeps at least the local large-deviation
obstruction but changes the global kernel elsewhere.
-/
theorem setIntegral_mono_subset_of_leOn_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {localF globalF : α → ℝ} {s t : Set α}
    (hs : MeasurableSet s)
    (hlocal_int : IntegrableOn localF s μ)
    (hglobal_int : IntegrableOn globalF t μ)
    (hglobal_nonneg : ∀ᵐ x ∂μ.restrict t, 0 ≤ globalF x)
    (hst : s ⊆ t)
    (hle : ∀ x, x ∈ s → localF x ≤ globalF x) :
    ∫ x in s, localF x ∂μ ≤ ∫ x in t, globalF x ∂μ := by
  have hglobal_int_s : IntegrableOn globalF s μ :=
    hglobal_int.mono_set hst
  have hlocal_le_global :
      ∫ x in s, localF x ∂μ ≤ ∫ x in s, globalF x ∂μ := by
    exact integral_mono_ae hlocal_int hglobal_int_s
      (by
        filter_upwards [ae_restrict_mem hs] with x hx
        exact hle x hx)
  exact hlocal_le_global.trans
    (setIntegral_mono_subset_of_ae_nonneg hglobal_int hglobal_nonneg hst)

/--
Real-valued essential-infimum interface tailored to Laplace-principle proofs.

`HasAEEssentialInfimum μ phi rate` records the two mathematical facts needed
from the statement “`rate` is the essential infimum of `phi`”: `rate` is an
almost-everywhere lower bound, and every strict near-sublevel has positive
real measure.
-/
def HasAEEssentialInfimum
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (phi : α → ℝ) (rate : ℝ) : Prop :=
  (∀ᵐ x ∂μ, rate ≤ phi x) ∧
    ∀ ε > 0, ∃ s : Set α,
      MeasurableSet s ∧
        0 < μ.real s ∧
          ∀ x, x ∈ s → phi x ≤ rate + ε

/--
Positive-weight near-essential-infimum interface for weighted Laplace
principles.  For every strict neighborhood of the essential infimum, there is
a positive-measure restricted set on which the weight is uniformly positive
and the rate function is within that neighborhood.
-/
def HasPositiveWeightNearAEEssentialInfimum
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w phi : α → ℝ) (rate : ℝ) : Prop :=
  ∀ ε > 0, ∃ s : Set α, ∃ c : ℝ,
    0 < μ.real s ∧ 0 < c ∧
      ∀ᵐ x ∂μ.restrict s, c ≤ w x ∧ phi x ≤ rate + ε

namespace HasAEEssentialInfimum

theorem ae_lower
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {phi : α → ℝ} {rate : ℝ}
    (h : HasAEEssentialInfimum μ phi rate) :
    ∀ᵐ x ∂μ, rate ≤ phi x :=
  h.1

theorem nearInfSets
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {phi : α → ℝ} {rate : ℝ}
    (h : HasAEEssentialInfimum μ phi rate) :
    ∀ ε > 0, ∃ s : Set α,
      0 < μ.real s ∧
        ∀ᵐ x ∂μ.restrict s, phi x ≤ rate + ε := by
  intro ε hε
  rcases h.2 ε hε with ⟨s, hs_meas, hpos, hle⟩
  exact ⟨s, hpos, ae_restrict_of_forall_mem hs_meas hle⟩

/--
Constructor from positive real measure of all measurable near-sublevel sets.
-/
theorem of_measurable_sublevel_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {phi : α → ℝ} {rate : ℝ}
    (hlower : ∀ᵐ x ∂μ, rate ≤ phi x)
    (hmeas : ∀ t : ℝ, MeasurableSet {x : α | phi x ≤ t})
    (hpos : ∀ ε > 0, 0 < μ.real {x : α | phi x ≤ rate + ε}) :
    HasAEEssentialInfimum μ phi rate := by
  refine ⟨hlower, ?_⟩
  intro ε hε
  refine ⟨{x : α | phi x ≤ rate + ε}, hmeas (rate + ε),
    hpos ε hε, ?_⟩
  intro x hx
  exact hx

/--
Constructor from positive `ENNReal` measure of all measurable near-sublevel
sets under a finite measure.
-/
theorem of_measurable_sublevel_measure_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {phi : α → ℝ} {rate : ℝ}
    (hlower : ∀ᵐ x ∂μ, rate ≤ phi x)
    (hmeas : ∀ t : ℝ, MeasurableSet {x : α | phi x ≤ t})
    (hpos : ∀ ε > 0, 0 < μ {x : α | phi x ≤ rate + ε}) :
    HasAEEssentialInfimum μ phi rate :=
  of_measurable_sublevel_pos hlower hmeas fun ε hε =>
    ENNReal.toReal_pos (ne_of_gt (hpos ε hε))
      (measure_ne_top μ {x : α | phi x ≤ rate + ε})

/--
For a measurable real payoff that is almost-everywhere bounded above, the
negative payoff has essential infimum equal to the negative essential
supremum. This is the measurable, discontinuity-tolerant Laplace bridge: it
does not replace an essential supremum by a pointwise maximum.
-/
theorem neg_of_essSup
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [NeZero μ]
    {f : α → ℝ} (hf : Measurable f)
    (hbound : IsBoundedUnder (· ≤ ·) (ae μ) f) :
    HasAEEssentialInfimum μ (fun x => -(f x)) (-(essSup f μ)) := by
  refine of_measurable_sublevel_measure_pos ?_ ?_ ?_
  · filter_upwards [ae_le_essSup hbound] with x hx
    linarith
  · intro t
    exact measurableSet_le hf.neg measurable_const
  · intro ε hε
    by_contra hnot
    have hzero : μ {x : α | -(f x) ≤ -(essSup f μ) + ε} = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have hbad_subset : {x : α | ¬ f x ≤ essSup f μ - ε} ⊆
        {x : α | -(f x) ≤ -(essSup f μ) + ε} := by
      intro x hx
      dsimp at hx ⊢
      linarith
    have hbad_zero : μ {x : α | ¬ f x ≤ essSup f μ - ε} = 0 :=
      measure_mono_null hbad_subset hzero
    have hae : ∀ᵐ x ∂μ, f x ≤ essSup f μ - ε := by
      rw [ae_iff]
      exact hbad_zero
    have hco : IsCoboundedUnder (· ≤ ·) (ae μ) f := by
      have hexists : ∃ n : ℕ, ∃ᶠ x in ae μ, -(n : ℝ) ≤ f x := by
        by_contra hno
        have hzero : ∀ n : ℕ, μ {x : α | -(n : ℝ) ≤ f x} = 0 := by
          intro n
          have hnotfreq : ¬ ∃ᶠ x in ae μ, -(n : ℝ) ≤ f x :=
            fun hfreq => hno ⟨n, hfreq⟩
          have hae_not : ∀ᵐ x ∂μ, ¬ (-(n : ℝ) ≤ f x) :=
            Filter.not_frequently.mp hnotfreq
          simpa only [not_not] using (ae_iff.mp hae_not)
        have huniv : (⋃ n : ℕ, {x : α | -(n : ℝ) ≤ f x}) = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          obtain ⟨n, hn⟩ := exists_nat_ge (-(f x))
          exact Set.mem_iUnion.mpr ⟨n, by dsimp; linarith⟩
        have hmeasure_univ : μ Set.univ = 0 := by
          rw [← huniv]
          exact measure_iUnion_null hzero
        exact (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) hmeasure_univ
      rcases hexists with ⟨n, hn⟩
      exact IsCoboundedUnder.of_frequently_ge hn
    have hle : essSup f μ ≤ essSup f μ - ε := by
      change Filter.limsup f (ae μ) ≤ essSup f μ - ε
      exact Filter.limsup_le_of_le hco hae
    linarith

/--
Continuous-minimizer constructor for the Laplace essential-infimum interface.
If `phi` has a global minimum `rate` at `x0`, is continuous at `x0`, and the
finite measure gives positive mass to every nonempty open set, then `rate` is
an almost-everywhere essential infimum in the source-style sense used by the
Laplace skeleton.
-/
theorem of_continuousAt_global_min_open_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {phi : α → ℝ} {rate : ℝ} (x0 : α)
    (hmin : ∀ x : α, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0) :
    HasAEEssentialInfimum μ phi rate := by
  refine ⟨Eventually.of_forall hmin, ?_⟩
  intro ε hε
  have htarget :
      {y : ℝ | y < rate + ε} ∈ 𝓝 (phi x0) := by
    rw [hx0]
    exact IsOpen.mem_nhds isOpen_Iio (lt_add_of_pos_right rate hε)
  have hpre :
      {x : α | phi x < rate + ε} ∈ 𝓝 x0 :=
    hcont htarget
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  have hU_nonempty : U.Nonempty := ⟨x0, hxU⟩
  have hμpos : 0 < μ U := hUopen.measure_pos μ hU_nonempty
  refine ⟨U, hUopen.measurableSet, ?_, ?_⟩
  · exact ENNReal.toReal_pos (ne_of_gt hμpos) (measure_ne_top μ U)
  · intro x hx
    exact le_of_lt (hUsub hx)

/--
Restricted-measure continuous-minimizer constructor for the Laplace
essential-infimum interface.  This is the local-cell form used in
piecewise-continuum Laplace arguments: the minimizer `x0` belongs to the cell
`s`, `rate` is a lower bound on `s`, and every open neighborhood of `x0`
intersects `s` in positive measure.
-/
theorem of_continuousAt_global_min_restrict
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {s : Set α} (hs : MeasurableSet s)
    {phi : α → ℝ} {rate : ℝ} (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U)) :
    HasAEEssentialInfimum (μ.restrict s) phi rate := by
  refine ⟨ae_restrict_of_forall_mem hs hmin, ?_⟩
  intro ε hε
  have htarget :
      {y : ℝ | y < rate + ε} ∈ 𝓝 (phi x0) := by
    rw [hx0]
    exact IsOpen.mem_nhds isOpen_Iio (lt_add_of_pos_right rate hε)
  have hpre :
      {x : α | phi x < rate + ε} ∈ 𝓝 x0 :=
    hcont htarget
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  have hμpos : 0 < μ (s ∩ U) := hlocal_pos U hUopen hxU
  have hrestrict_pos : 0 < (μ.restrict s) U := by
    rw [Measure.restrict_apply hUopen.measurableSet]
    rwa [Set.inter_comm]
  refine ⟨U, hUopen.measurableSet, ?_, ?_⟩
  · exact ENNReal.toReal_pos (ne_of_gt hrestrict_pos)
      (measure_ne_top (μ.restrict s) U)
  · intro x hx
    exact le_of_lt (hUsub hx)

/--
If a measure is positive on nonempty open sets and `x0` lies in the closure of
the interior of `s`, then every open neighborhood of `x0` intersects `s` in
positive measure.
-/
theorem local_pos_of_mem_closure_interior
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [Measure.IsOpenPosMeasure μ]
    {s : Set α} {x0 : α}
    (hclosure : x0 ∈ closure (interior s)) :
    ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U) := by
  intro U hU hxU
  have hU_nhds : U ∈ 𝓝 x0 := IsOpen.mem_nhds hU hxU
  have hnonempty : (U ∩ interior s).Nonempty :=
    (mem_closure_iff_nhds.mp hclosure) U hU_nhds
  have hopen : IsOpen (U ∩ interior s) := hU.inter isOpen_interior
  have hpos : 0 < μ (U ∩ interior s) :=
    hopen.measure_pos μ hnonempty
  have hsubset : U ∩ interior s ⊆ s ∩ U := by
    intro x hx
    exact ⟨interior_subset hx.2, hx.1⟩
  exact lt_of_lt_of_le hpos (measure_mono hsubset)

/--
Restricted-measure continuous-minimizer constructor where local positive cell
mass follows from the minimizer lying in the closure of the cell interior.
-/
theorem of_continuousAt_global_min_restrict_closure_interior
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    {phi : α → ℝ} {rate : ℝ} (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior s)) :
    HasAEEssentialInfimum (μ.restrict s) phi rate :=
  of_continuousAt_global_min_restrict hs x0 hmin hx0 hcont
    (local_pos_of_mem_closure_interior μ hclosure)

end HasAEEssentialInfimum

namespace HasPositiveWeightNearAEEssentialInfimum

/--
If the weight is uniformly positive almost everywhere, then every
near-essential-minimizer set is also a positive-weight near-essential-minimizer
set.
-/
theorem of_uniform_ae_lower_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w phi : α → ℝ} {rate c : ℝ}
    (hess : HasAEEssentialInfimum μ phi rate)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x) :
    HasPositiveWeightNearAEEssentialInfimum μ w phi rate := by
  intro ε hε
  rcases HasAEEssentialInfimum.nearInfSets hess ε hε with
    ⟨s, hμs_pos, hphi_s⟩
  refine ⟨s, c, hμs_pos, hcpos, ?_⟩
  filter_upwards [ae_restrict_of_ae hw_lower, hphi_s] with x hwx hphix
  exact ⟨hwx, hphix⟩

/--
Continuous positive-weight constructor for the weighted near-essential-infimum
interface.  If a limiting rate is continuous at a minimizer and the objective
weight is continuous and positive at that same point, every near-minimizer
neighborhood contains a positive-measure region where the weight is uniformly
positive.
-/
theorem of_continuousAt_pos_at_min_open_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {w phi : α → ℝ} {rate : ℝ} (x0 : α)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0) :
    HasPositiveWeightNearAEEssentialInfimum μ w phi rate := by
  intro ε hε
  let c : ℝ := w x0 / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hw_target : {y : ℝ | c < y} ∈ 𝓝 (w x0) := by
    exact IsOpen.mem_nhds isOpen_Ioi (by dsimp [c]; linarith)
  have hphi_target : {y : ℝ | y < rate + ε} ∈ 𝓝 (phi x0) := by
    rw [hx0]
    exact IsOpen.mem_nhds isOpen_Iio (lt_add_of_pos_right rate hε)
  have hw_pre : {x : α | c < w x} ∈ 𝓝 x0 := hw_cont hw_target
  have hphi_pre : {x : α | phi x < rate + ε} ∈ 𝓝 x0 :=
    hphi_cont hphi_target
  have hpre :
      ({x : α | c < w x} ∩ {x : α | phi x < rate + ε}) ∈ 𝓝 x0 :=
    Filter.inter_mem hw_pre hphi_pre
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  have hU_nonempty : U.Nonempty := ⟨x0, hxU⟩
  have hμpos : 0 < μ U := hUopen.measure_pos μ hU_nonempty
  refine ⟨U, c, ?_, hcpos, ?_⟩
  · exact ENNReal.toReal_pos (ne_of_gt hμpos) (measure_ne_top μ U)
  · exact ae_restrict_of_forall_mem hUopen.measurableSet (by
      intro x hx
      have hx' := hUsub hx
      exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩)

/--
Restricted-measure version of
`of_continuousAt_pos_at_min_open_pos`.  The caller supplies the standard local
positive-mass condition for the cell containing the minimizer.
-/
theorem of_continuousAt_pos_at_min_restrict
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {s : Set α} (hs : MeasurableSet s)
    {w phi : α → ℝ} {rate : ℝ} (x0 : α)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U)) :
    HasPositiveWeightNearAEEssentialInfimum (μ.restrict s) w phi rate := by
  intro ε hε
  let c : ℝ := w x0 / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hw_target : {y : ℝ | c < y} ∈ 𝓝 (w x0) := by
    exact IsOpen.mem_nhds isOpen_Ioi (by dsimp [c]; linarith)
  have hphi_target : {y : ℝ | y < rate + ε} ∈ 𝓝 (phi x0) := by
    rw [hx0]
    exact IsOpen.mem_nhds isOpen_Iio (lt_add_of_pos_right rate hε)
  have hw_pre : {x : α | c < w x} ∈ 𝓝 x0 := hw_cont hw_target
  have hphi_pre : {x : α | phi x < rate + ε} ∈ 𝓝 x0 :=
    hphi_cont hphi_target
  have hpre :
      ({x : α | c < w x} ∩ {x : α | phi x < rate + ε}) ∈ 𝓝 x0 :=
    Filter.inter_mem hw_pre hphi_pre
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  have hμpos : 0 < μ (s ∩ U) := hlocal_pos U hUopen hxU
  have hrestrict_pos : 0 < (μ.restrict s) U := by
    rw [Measure.restrict_apply hUopen.measurableSet]
    rwa [Set.inter_comm]
  refine ⟨U, c, ?_, hcpos, ?_⟩
  · exact ENNReal.toReal_pos (ne_of_gt hrestrict_pos)
      (measure_ne_top (μ.restrict s) U)
  · exact ae_restrict_of_forall_mem hUopen.measurableSet (by
      intro x hx
      have hx' := hUsub hx
      exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩)

/--
Restricted positive-weight constructor where local positive cell mass follows
from the minimizer lying in the closure of the cell interior.
-/
theorem of_continuousAt_pos_at_min_restrict_closure_interior
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    {w phi : α → ℝ} {rate : ℝ} (x0 : α)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hclosure : x0 ∈ closure (interior s)) :
    HasPositiveWeightNearAEEssentialInfimum (μ.restrict s) w phi rate :=
  of_continuousAt_pos_at_min_restrict hs x0 hx0 hphi_cont hw_cont hw_pos
    (HasAEEssentialInfimum.local_pos_of_mem_closure_interior μ hclosure)

end HasPositiveWeightNearAEEssentialInfimum

/--
If a nonnegative kernel is almost everywhere bounded by a common exponential
envelope over a finite measure space, then its integral satisfies the same
exponential upper bound, with the measure of the space absorbed into the
constant prefactor.
-/
theorem integral_hasExpUpperBoundWithConst_of_ae_le_const_exp
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {rate C : ℝ}
    (hCpos : 0 < C)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ,
      0 ≤ F n x ∧ F n x ≤ C * Real.exp (-(n : ℝ) * rate)) :
    HasExpUpperBoundWithConst (fun n => ∫ x, F n x ∂μ) rate := by
  let K : ℝ := C * μ.real Set.univ + 1
  have hμ_nonneg : 0 ≤ μ.real Set.univ := by
    rw [Measure.real]
    exact ENNReal.toReal_nonneg
  have hKpos : 0 < K := by
    dsimp [K]
    nlinarith [hCpos, hμ_nonneg]
  refine HasExpUpperBoundWithConst.of_eventually_le (C := K) hKpos ?_
  filter_upwards with n
  have hconst_nonneg :
      0 ≤ C * Real.exp (-(n : ℝ) * rate) :=
    mul_nonneg hCpos.le (Real.exp_pos _).le
  have hconst_int :
      Integrable (fun _x : α => C * Real.exp (-(n : ℝ) * rate)) μ :=
    integrable_const _
  have hF_int : Integrable (F n) μ := by
    refine hconst_int.mono' (hF_meas n) ?_
    filter_upwards [hbound n] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1,
      abs_of_nonneg hconst_nonneg] using hx.2
  have hnonneg : 0 ≤ ∫ x, F n x ∂μ := by
    exact integral_nonneg_of_ae ((hbound n).mono fun _x hx => hx.1)
  have hmono :
      ∫ x, F n x ∂μ ≤
        ∫ _x : α, C * Real.exp (-(n : ℝ) * rate) ∂μ := by
    exact integral_mono_ae hF_int hconst_int
      ((hbound n).mono fun _x hx => hx.2)
  have hconst_eval :
      (∫ _x : α, C * Real.exp (-(n : ℝ) * rate) ∂μ) =
        μ.real Set.univ * (C * Real.exp (-(n : ℝ) * rate)) := by
    rw [integral_const, smul_eq_mul]
  have hupper :
      ∫ x, F n x ∂μ ≤ K * Real.exp (-(n : ℝ) * rate) := by
    calc
      ∫ x, F n x ∂μ
          ≤ ∫ _x : α, C * Real.exp (-(n : ℝ) * rate) ∂μ := hmono
      _ = μ.real Set.univ * (C * Real.exp (-(n : ℝ) * rate)) := hconst_eval
      _ = (C * μ.real Set.univ) * Real.exp (-(n : ℝ) * rate) := by ring
      _ ≤ K * Real.exp (-(n : ℝ) * rate) := by
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
          (Real.exp_pos _).le
  exact ⟨hnonneg, hupper⟩

/--
Eventually-bounded variant of
`integral_hasExpUpperBoundWithConst_of_ae_le_const_exp`.  This is the form
needed after a uniform-convergence argument has produced the common envelope
only for sufficiently large sample sizes.
-/
theorem integral_hasExpUpperBoundWithConst_of_eventually_ae_le_const_exp
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {rate C : ℝ}
    (hCpos : 0 < C)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ,
      0 ≤ F n x ∧ F n x ≤ C * Real.exp (-(n : ℝ) * rate)) :
    HasExpUpperBoundWithConst (fun n => ∫ x, F n x ∂μ) rate := by
  let K : ℝ := C * μ.real Set.univ + 1
  have hμ_nonneg : 0 ≤ μ.real Set.univ := by
    rw [Measure.real]
    exact ENNReal.toReal_nonneg
  have hKpos : 0 < K := by
    dsimp [K]
    nlinarith [hCpos, hμ_nonneg]
  refine HasExpUpperBoundWithConst.of_eventually_le (C := K) hKpos ?_
  filter_upwards [hbound] with n hbound_n
  have hconst_nonneg :
      0 ≤ C * Real.exp (-(n : ℝ) * rate) :=
    mul_nonneg hCpos.le (Real.exp_pos _).le
  have hconst_int :
      Integrable (fun _x : α => C * Real.exp (-(n : ℝ) * rate)) μ :=
    integrable_const _
  have hF_int : Integrable (F n) μ := by
    refine hconst_int.mono' (hF_meas n) ?_
    filter_upwards [hbound_n] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1,
      abs_of_nonneg hconst_nonneg] using hx.2
  have hnonneg : 0 ≤ ∫ x, F n x ∂μ := by
    exact integral_nonneg_of_ae (hbound_n.mono fun _x hx => hx.1)
  have hmono :
      ∫ x, F n x ∂μ ≤
        ∫ _x : α, C * Real.exp (-(n : ℝ) * rate) ∂μ := by
    exact integral_mono_ae hF_int hconst_int
      (hbound_n.mono fun _x hx => hx.2)
  have hconst_eval :
      (∫ _x : α, C * Real.exp (-(n : ℝ) * rate) ∂μ) =
        μ.real Set.univ * (C * Real.exp (-(n : ℝ) * rate)) := by
    rw [integral_const, smul_eq_mul]
  have hupper :
      ∫ x, F n x ∂μ ≤ K * Real.exp (-(n : ℝ) * rate) := by
    calc
      ∫ x, F n x ∂μ
          ≤ ∫ _x : α, C * Real.exp (-(n : ℝ) * rate) ∂μ := hmono
      _ = μ.real Set.univ * (C * Real.exp (-(n : ℝ) * rate)) := hconst_eval
      _ = (C * μ.real Set.univ) * Real.exp (-(n : ℝ) * rate) := by ring
      _ ≤ K * Real.exp (-(n : ℝ) * rate) := by
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
          (Real.exp_pos _).le
  exact ⟨hnonneg, hupper⟩

/--
Rate-function form of
`integral_hasExpUpperBoundWithConst_of_ae_le_const_exp`: if the pointwise
exponential rate is almost everywhere at least `targetRate`, then the integral
inherits an exponential upper bound at `targetRate`.
-/
theorem integral_hasExpUpperBoundWithConst_of_ae_rate_envelope
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {R : α → ℝ} {targetRate C : ℝ}
    (hCpos : 0 < C)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hR : ∀ᵐ x ∂μ, targetRate ≤ R x)
    (hbound : ∀ n, ∀ᵐ x ∂μ,
      0 ≤ F n x ∧ F n x ≤ C * Real.exp (-(n : ℝ) * R x)) :
    HasExpUpperBoundWithConst (fun n => ∫ x, F n x ∂μ) targetRate := by
  refine integral_hasExpUpperBoundWithConst_of_ae_le_const_exp
    (μ := μ) (rate := targetRate) (C := C) hCpos hF_meas ?_
  intro n
  filter_upwards [hR, hbound n] with x hRx hx
  refine ⟨hx.1, ?_⟩
  have hexp :
      Real.exp (-(n : ℝ) * R x) ≤
        Real.exp (-(n : ℝ) * targetRate) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hRx
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact hx.2.trans (mul_le_mul_of_nonneg_left hexp hCpos.le)

/--
If a positive-measure set carries a common exponential lower envelope for a
kernel, then the set integral has the corresponding exponential lower bound.

This is the reusable positive-measure near-minimizer component in the
lower-bound half of compact Laplace-principle arguments.
-/
theorem setIntegral_hasExpLowerBoundWithConst_of_ae_const_exp_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} {F : ℕ → α → ℝ} {rate c : ℝ}
    (hμs_pos : 0 < μ.real s)
    (hcpos : 0 < c)
    (hF_int : ∀ n, IntegrableOn (F n) s μ)
    (hlower : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ.restrict s,
      c * Real.exp (-(n : ℝ) * rate) ≤ F n x) :
    HasExpLowerBoundWithConst
      (fun n : ℕ => ∫ x in s, F n x ∂μ)
      rate := by
  refine HasExpLowerBoundWithConst.of_eventually_ge
    (c := μ.real s * c) (mul_pos hμs_pos hcpos) ?_
  filter_upwards [hlower] with n hn
  have hconst_int :
      IntegrableOn
        (fun _x : α => c * Real.exp (-(n : ℝ) * rate)) s μ :=
    integrable_const _
  have hmono :
      ∫ x in s, c * Real.exp (-(n : ℝ) * rate) ∂μ ≤
        ∫ x in s, F n x ∂μ := by
    exact integral_mono_ae hconst_int (hF_int n) hn
  have hconst_eval :
      (∫ x in s, c * Real.exp (-(n : ℝ) * rate) ∂μ) =
        μ.real s * (c * Real.exp (-(n : ℝ) * rate)) := by
    rw [setIntegral_const, smul_eq_mul]
  calc
    (μ.real s * c) * Real.exp (-(n : ℝ) * rate)
        = μ.real s * (c * Real.exp (-(n : ℝ) * rate)) := by ring
    _ = ∫ x in s, c * Real.exp (-(n : ℝ) * rate) ∂μ := hconst_eval.symm
    _ ≤ ∫ x in s, F n x ∂μ := hmono

/--
Extract a common exponential lower envelope on a positive-measure subset from
pointwise lower envelopes on a positive-measure set.

This is a countable-cover device for Laplace lower bounds.  Each point may
have its own prefactor and threshold; since the prefactors can be rounded down
to reciprocal integers and thresholds are natural numbers, one reciprocal and
one threshold work on a positive-measure subset.
-/
theorem exists_positive_measure_subset_eventually_ae_const_exp_le_of_pointwise_expLowerBounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} {F : ℕ → α → ℝ} {targetRate : ℝ}
    (hs_meas : MeasurableSet s)
    (hF_meas : ∀ n : ℕ, Measurable (F n))
    (hμs_pos : 0 < μ.real s)
    (hlower_point : ∀ x : α, x ∈ s →
      HasExpLowerBoundWithConst (fun n : ℕ => F n x) targetRate) :
    ∃ t : Set α, ∃ c : ℝ,
      MeasurableSet t ∧
        0 < μ.real t ∧ 0 < c ∧ t ⊆ s ∧
          ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ.restrict t,
            c * Real.exp (-(n : ℝ) * targetRate) ≤ F n x := by
  let lowerSet : ℕ × ℕ → Set α := fun idx =>
    {x : α | x ∈ s ∧
      ∀ n : ℕ, idx.1 ≤ n →
        ((idx.2 + 1 : ℕ) : ℝ)⁻¹ *
            Real.exp (-(n : ℝ) * targetRate) ≤ F n x}
  have hlowerSet_meas : ∀ idx : ℕ × ℕ, MeasurableSet (lowerSet idx) := by
    intro idx
    dsimp [lowerSet]
    refine hs_meas.inter ?_
    change MeasurableSet
      ({x : α | ∀ n : ℕ, idx.1 ≤ n →
          ((idx.2 + 1 : ℕ) : ℝ)⁻¹ *
              Real.exp (-(n : ℝ) * targetRate) ≤ F n x} : Set α)
    rw [show
      ({x : α | ∀ n : ℕ, idx.1 ≤ n →
          ((idx.2 + 1 : ℕ) : ℝ)⁻¹ *
              Real.exp (-(n : ℝ) * targetRate) ≤ F n x} : Set α) =
        ⋂ n : ℕ,
          {x : α | idx.1 ≤ n →
            ((idx.2 + 1 : ℕ) : ℝ)⁻¹ *
                Real.exp (-(n : ℝ) * targetRate) ≤ F n x} by
        ext x
        simp]
    refine MeasurableSet.iInter fun n : ℕ => ?_
    by_cases hn : idx.1 ≤ n
    · simp [hn]
      have hpre :
          MeasurableSet
            ((F n) ⁻¹'
              Set.Ici
                (((idx.2 + 1 : ℕ) : ℝ)⁻¹ *
                  Real.exp (-(n : ℝ) * targetRate))) :=
        hF_meas n measurableSet_Ici
      simpa [Set.preimage, Set.mem_Ici] using hpre
    · simp [hn]
  have hs_subset_iUnion : s ⊆ ⋃ idx : ℕ × ℕ, lowerSet idx := by
    intro x hx
    rcases hlower_point x hx with ⟨c, hcpos, hbound⟩
    rcases exists_nat_one_div_lt hcpos with ⟨m, hm⟩
    rcases eventually_atTop.1 hbound with ⟨N, hN⟩
    refine Set.mem_iUnion.2 ⟨(N, m), ?_⟩
    refine ⟨hx, ?_⟩
    intro n hn
    have hrecip_le_c :
        ((m + 1 : ℕ) : ℝ)⁻¹ ≤ c := by
      simpa [one_div] using (le_of_lt hm)
    have hexp_nonneg :
        0 ≤ Real.exp (-(n : ℝ) * targetRate) := (Real.exp_pos _).le
    exact
      (mul_le_mul_of_nonneg_right hrecip_le_c hexp_nonneg).trans
        (hN n hn)
  have hμs_pos_enn : 0 < μ s :=
    (ENNReal.toReal_pos_iff.mp hμs_pos).1
  have hμ_iUnion_pos : 0 < μ (⋃ idx : ℕ × ℕ, lowerSet idx) :=
    hμs_pos_enn.trans_le (measure_mono hs_subset_iUnion)
  rcases exists_measure_pos_of_not_measure_iUnion_null
      (μ := μ) (s := lowerSet) (ne_of_gt hμ_iUnion_pos) with
    ⟨idx, hidx_pos⟩
  refine ⟨lowerSet idx, ((idx.2 + 1 : ℕ) : ℝ)⁻¹, hlowerSet_meas idx, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.toReal_pos (ne_of_gt hidx_pos) (measure_ne_top μ (lowerSet idx))
  · positivity
  · intro x hx
    exact hx.1
  · refine eventually_atTop.2 ⟨idx.1, ?_⟩
    intro n hn
    filter_upwards [ae_restrict_mem (hlowerSet_meas idx)] with x hx
    exact hx.2 n hn

/--
A lower exponential bound for an integral over a subset also lower bounds the
full integral when the integrand is nonnegative almost everywhere.
-/
theorem integral_hasExpLowerBoundWithConst_of_setIntegral_lower_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} {F : ℕ → α → ℝ} {rate : ℝ}
    (hset :
      HasExpLowerBoundWithConst
        (fun n : ℕ => ∫ x in s, F n x ∂μ)
        rate)
    (hF_int : ∀ n, Integrable (F n) μ)
    (hF_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x) :
    HasExpLowerBoundWithConst
      (fun n : ℕ => ∫ x, F n x ∂μ)
      rate := by
  rcases hset with ⟨c, hcpos, hbound⟩
  refine HasExpLowerBoundWithConst.of_eventually_ge hcpos ?_
  filter_upwards [hbound] with n hn
  exact hn.trans (setIntegral_le_integral (hF_int n) (hF_nonneg n))

/--
Exact exponential rate for a nonnegative integral from reusable upper bounds
below `rate` and positive-measure subset lower bounds above `rate`.

This packages the proof skeleton of compact Laplace-principle arguments while
leaving the construction of near-minimizer sets to the caller.
-/
theorem integral_hasExponentialRate_of_expUpperBounds_and_setLowerBounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {rate : ℝ}
    (hF_int : ∀ n, Integrable (F n) μ)
    (hF_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x)
    (hupper : ∀ targetRate, targetRate < rate →
      HasExpUpperBoundWithConst
        (fun n : ℕ => ∫ x, F n x ∂μ)
        targetRate)
    (hlower_sets : ∀ targetRate, rate < targetRate →
      ∃ s : Set α, ∃ c : ℝ,
        0 < μ.real s ∧ 0 < c ∧
          (∀ n, IntegrableOn (F n) s μ) ∧
            ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ.restrict s,
              c * Real.exp (-(n : ℝ) * targetRate) ≤ F n x) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, F n x ∂μ)
      rate := by
  let p : ℕ → ℝ := fun n => ∫ x, F n x ∂μ
  have hlower_full : ∀ targetRate, rate < targetRate →
      HasExpLowerBoundWithConst p targetRate := by
    intro targetRate htarget
    rcases hlower_sets targetRate htarget with
      ⟨s, c, hμs_pos, hcpos, hF_set_int, hlower⟩
    have hset :
        HasExpLowerBoundWithConst
          (fun n : ℕ => ∫ x in s, F n x ∂μ)
          targetRate :=
      setIntegral_hasExpLowerBoundWithConst_of_ae_const_exp_le
        μ hμs_pos hcpos hF_set_int hlower
    exact integral_hasExpLowerBoundWithConst_of_setIntegral_lower_bound
      μ hset hF_int hF_nonneg
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    rcases hlower_full (rate + 1) (by linarith) with
      ⟨c, hcpos, hbound⟩
    filter_upwards [hbound] with n hn
    exact (mul_pos hcpos (Real.exp_pos _)).trans_le hn
  exact hasExponentialRate_of_expUpperLowerBounds
    hpos hupper hlower_full

/--
Zero-rate specialization of
`integral_hasExponentialRate_of_expUpperBounds_and_setLowerBounds`.

For rate zero, the upper-bound side only needs an eventual fixed positive
upper bound on the integral. The lower-bound side is the usual
positive-measure set witness at every positive target rate.
-/
theorem integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {B : ℝ}
    (hBpos : 0 < B)
    (hF_int : ∀ n, Integrable (F n) μ)
    (hF_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x)
    (hupper_const : ∀ᶠ n in atTop, (∫ x, F n x ∂μ) ≤ B)
    (hlower_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ s : Set α, ∃ c : ℝ,
        0 < μ.real s ∧ 0 < c ∧
          (∀ n, IntegrableOn (F n) s μ) ∧
            ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ.restrict s,
              c * Real.exp (-(n : ℝ) * targetRate) ≤ F n x) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, F n x ∂μ)
      0 := by
  let p : ℕ → ℝ := fun n => ∫ x, F n x ∂μ
  have hlower_full : ∀ targetRate : ℝ, 0 < targetRate →
      HasExpLowerBoundWithConst p targetRate := by
    intro targetRate htarget
    rcases hlower_sets targetRate htarget with
      ⟨s, c, hμs_pos, hcpos, hF_set_int, hlower⟩
    have hset :
        HasExpLowerBoundWithConst
          (fun n : ℕ => ∫ x in s, F n x ∂μ)
          targetRate :=
      setIntegral_hasExpLowerBoundWithConst_of_ae_const_exp_le
        μ hμs_pos hcpos hF_set_int hlower
    exact integral_hasExpLowerBoundWithConst_of_setIntegral_lower_bound
      μ hset hF_int hF_nonneg
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    rcases hlower_full 1 (by norm_num) with
      ⟨c, hcpos, hbound⟩
    filter_upwards [hbound] with n hn
    exact (mul_pos hcpos (Real.exp_pos _)).trans_le hn
  exact
    hasExponentialRate_zero_of_eventually_le_const_and_expLowerBounds
      hBpos hpos hupper_const hlower_full

/--
Rate-function form of
`integral_hasExponentialRate_of_expUpperBounds_and_setLowerBounds`: an
almost-everywhere pointwise upper-rate envelope supplies all upper bounds
below `rate`, while positive-measure near-minimizer set lower bounds supply
all lower bounds above `rate`.
-/
theorem integral_hasExponentialRate_of_ae_rate_envelope_and_setLowerBounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {R : α → ℝ} {rate C : ℝ}
    (hCpos : 0 < C)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_int : ∀ n, Integrable (F n) μ)
    (hR : ∀ᵐ x ∂μ, rate ≤ R x)
    (hupper_envelope : ∀ n, ∀ᵐ x ∂μ,
      0 ≤ F n x ∧ F n x ≤ C * Real.exp (-(n : ℝ) * R x))
    (hlower_sets : ∀ targetRate, rate < targetRate →
      ∃ s : Set α, ∃ c : ℝ,
        0 < μ.real s ∧ 0 < c ∧
          (∀ n, IntegrableOn (F n) s μ) ∧
            ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ.restrict s,
              c * Real.exp (-(n : ℝ) * targetRate) ≤ F n x) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, F n x ∂μ)
      rate := by
  refine integral_hasExponentialRate_of_expUpperBounds_and_setLowerBounds
    μ hF_int ?_ ?_ hlower_sets
  · intro n
    exact (hupper_envelope n).mono fun _x hx => hx.1
  · intro targetRate htarget
    refine integral_hasExpUpperBoundWithConst_of_ae_rate_envelope
      (μ := μ) (R := R) (targetRate := targetRate) (C := C)
      hCpos hF_meas ?_ hupper_envelope
    exact hR.mono fun _x hx => le_trans htarget.le hx

/--
Compact-Laplace skeleton with explicit near-infimum sets.  If `phiSeq n`
converges uniformly to `phi`, `rate` is an almost-everywhere lower bound for
`phi`, and every `rate + ε` sublevel has positive measure in the restricted
near-infimum sense, then

`∫ exp (-(n : ℝ) * phiSeq n x) dμ`

has paper-style exponential decay rate `rate`.

This is the reusable source-assumption bridge for Laplace-principle arguments
before specializing to a particular essential-infimum API.
-/
theorem laplaceIntegral_hasExponentialRate_of_uniform_tendsto_nearInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (phiSeq : ℕ → α → ℝ) (phi : α → ℝ) {rate : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hphi_lower : ∀ᵐ x ∂μ, rate ≤ phi x)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε)
    (hnear : ∀ ε > 0,
      ∃ s : Set α,
        0 < μ.real s ∧
          ∀ᵐ x ∂μ.restrict s, phi x ≤ rate + ε) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate := by
  let F : ℕ → α → ℝ :=
    fun n x => Real.exp (-(n : ℝ) * (phiSeq n x))
  refine integral_hasExponentialRate_of_expUpperBounds_and_setLowerBounds
    (μ := μ) (F := F) (rate := rate) hF_int ?_ ?_ ?_
  · intro n
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  · intro targetRate htarget
    let ε : ℝ := (rate - targetRate) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    have htarget_le : targetRate ≤ rate - ε := by
      dsimp [ε]
      linarith
    refine integral_hasExpUpperBoundWithConst_of_eventually_ae_le_const_exp
      (μ := μ) (F := F) (rate := targetRate) (C := 1)
      (by norm_num) (fun n => (hF_int n).aestronglyMeasurable) ?_
    filter_upwards [huniform ε hεpos] with n hn
    filter_upwards [hphi_lower] with x hphi_x
    have hdiff_lower :
        -ε ≤ phiSeq n x - phi x :=
      (abs_le.mp (hn x)).1
    have hphiSeq_lower : targetRate ≤ phiSeq n x := by
      have : phi x - ε ≤ phiSeq n x := by
        linarith
      exact le_trans htarget_le (le_trans (sub_le_sub_right hphi_x ε) this)
    have hexp_le :
        Real.exp (-(n : ℝ) * (phiSeq n x)) ≤
          Real.exp (-(n : ℝ) * targetRate) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hphiSeq_lower
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    exact ⟨(Real.exp_pos _).le, by simpa [F] using hexp_le⟩
  · intro targetRate htarget
    let ε : ℝ := (targetRate - rate) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    rcases hnear ε hεpos with ⟨s, hμs_pos, hnear_s⟩
    refine ⟨s, 1, hμs_pos, by norm_num, ?_, ?_⟩
    · intro n
      exact (hF_int n).integrableOn
    · filter_upwards [huniform ε hεpos] with n hn
      filter_upwards [hnear_s] with x hphi_x
      have hdiff_upper :
          phiSeq n x - phi x ≤ ε :=
        (abs_le.mp (hn x)).2
      have hphiSeq_upper : phiSeq n x ≤ targetRate := by
        have : phiSeq n x ≤ phi x + ε := by
          linarith
        have hnear_target : rate + ε + ε = targetRate := by
          dsimp [ε]
          ring
        linarith
      have hexp_le :
          Real.exp (-(n : ℝ) * targetRate) ≤
            Real.exp (-(n : ℝ) * (phiSeq n x)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hphiSeq_upper
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      simpa [F] using hexp_le

/--
Source-style compact-Laplace wrapper using the reusable real-valued
essential-infimum interface.
-/
theorem laplaceIntegral_hasExponentialRate_of_uniform_tendsto_essentialInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (phiSeq : ℕ → α → ℝ) (phi : α → ℝ) {rate : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate :=
  laplaceIntegral_hasExponentialRate_of_uniform_tendsto_nearInf
    μ phiSeq phi hF_int
    (HasAEEssentialInfimum.ae_lower hess)
    huniform
    (HasAEEssentialInfimum.nearInfSets hess)

/--
For a measurable, almost-everywhere bounded-above payoff, the positive
Laplace integral has normalized logarithmic limit equal to its essential
supremum.  This is the measurable form of the Laplace principle: the limit
does not in general equal a pointwise supremum without an additional
near-maximizer condition.
-/
theorem positiveLaplaceIntegral_normalizedLog_tendsto_essSup
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [NeZero μ]
    (f : α → ℝ) (hf : Measurable f)
    (hbound : IsBoundedUnder (· ≤ ·) (ae μ) f)
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => Real.exp ((n : ℝ) * f x)) μ) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * Real.log
          (∫ x, Real.exp ((n : ℝ) * f x) ∂μ))
      atTop (nhds (essSup f μ)) := by
  have hrate :=
    laplaceIntegral_hasExponentialRate_of_uniform_tendsto_essentialInf
      μ (fun _ x => -(f x)) (fun x => -(f x))
      (by
        intro n
        convert hF_int n using 1
        ext x
        congr 1
        ring)
      (HasAEEssentialInfimum.neg_of_essSup hf hbound)
      (by
        intro ε hε
        filter_upwards with n x
        simp [hε.le])
  rw [HasExponentialRate] at hrate
  have hrate_neg := hrate.neg
  simpa [logDecay] using hrate_neg

/--
Weighted compact-Laplace skeleton with a positive-weight near-infimum
interface.  This is the source shape for objectives that integrate weighted
pairwise error probabilities: bounded nonnegative weights do not change the
exponential rate when every near-essential-minimizer set contains a
positive-measure subset where the weight is bounded below.
-/
theorem weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_weightedEssentialInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ w phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    HasExponentialRate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate := by
  let F : ℕ → α → ℝ :=
    fun n x => w x * Real.exp (-(n : ℝ) * (phiSeq n x))
  refine integral_hasExponentialRate_of_expUpperBounds_and_setLowerBounds
    (μ := μ) (F := F) (rate := rate) hF_int ?_ ?_ ?_
  · intro n
    filter_upwards [hw_nonneg] with x hwx
    exact mul_nonneg hwx (Real.exp_pos _).le
  · intro targetRate htarget
    let ε : ℝ := (rate - targetRate) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    have htarget_le : targetRate ≤ rate - ε := by
      dsimp [ε]
      linarith
    refine integral_hasExpUpperBoundWithConst_of_eventually_ae_le_const_exp
      (μ := μ) (F := F) (rate := targetRate) (C := W)
      hWpos (fun n => (hF_int n).aestronglyMeasurable) ?_
    filter_upwards [huniform ε hεpos] with n hn
    filter_upwards [hw_nonneg, hw_bound, HasAEEssentialInfimum.ae_lower hess]
      with x hwx_nonneg hwx_bound hphi_x
    have hdiff_lower :
        -ε ≤ phiSeq n x - phi x :=
      (abs_le.mp (hn x)).1
    have hphiSeq_lower : targetRate ≤ phiSeq n x := by
      have : phi x - ε ≤ phiSeq n x := by
        linarith
      exact le_trans htarget_le (le_trans (sub_le_sub_right hphi_x ε) this)
    have hexp_le :
        Real.exp (-(n : ℝ) * (phiSeq n x)) ≤
          Real.exp (-(n : ℝ) * targetRate) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hphiSeq_lower
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    refine ⟨?_, ?_⟩
    · exact mul_nonneg hwx_nonneg (Real.exp_pos _).le
    · exact mul_le_mul hwx_bound hexp_le (Real.exp_pos _).le hWpos.le
  · intro targetRate htarget
    let ε : ℝ := (targetRate - rate) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    rcases hweighted_near ε hεpos with
      ⟨s, c, hμs_pos, hcpos, hnear_s⟩
    refine ⟨s, c, hμs_pos, hcpos, ?_, ?_⟩
    · intro n
      exact (hF_int n).integrableOn
    · filter_upwards [huniform ε hεpos] with n hn
      filter_upwards [hnear_s] with x hx
      have hdiff_upper :
          phiSeq n x - phi x ≤ ε :=
        (abs_le.mp (hn x)).2
      have hphiSeq_upper : phiSeq n x ≤ targetRate := by
        have : phiSeq n x ≤ phi x + ε := by
          linarith
        have hnear_target : rate + ε + ε = targetRate := by
          dsimp [ε]
          ring
        linarith
      have hexp_le :
          Real.exp (-(n : ℝ) * targetRate) ≤
            Real.exp (-(n : ℝ) * (phiSeq n x)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hphiSeq_upper
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact mul_le_mul hx.1 hexp_le (Real.exp_pos _).le
        (le_trans hcpos.le hx.1)

/--
Eventual positivity for the weighted compact-Laplace integral.  This is the
positivity half needed to package the weighted Laplace theorem as an
`ExponentialRateCertificate`.
-/
theorem weightedLaplaceIntegral_eventually_pos_of_uniform_tendsto_weightedEssentialInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ w phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ := by
  let F : ℕ → α → ℝ :=
    fun n x => w x * Real.exp (-(n : ℝ) * (phiSeq n x))
  let targetRate : ℝ := rate + 1
  let ε : ℝ := (targetRate - rate) / 2
  have hεpos : 0 < ε := by
    dsimp [targetRate, ε]
    linarith
  rcases hweighted_near ε hεpos with
    ⟨s, c, hμs_pos, hcpos, hnear_s⟩
  have hF_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x := by
    intro n
    filter_upwards [hw_nonneg] with x hwx
    exact mul_nonneg hwx (Real.exp_pos _).le
  have hlower :
      ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ.restrict s,
        c * Real.exp (-(n : ℝ) * targetRate) ≤ F n x := by
    filter_upwards [huniform ε hεpos] with n hn
    filter_upwards [hnear_s] with x hx
    have hdiff_upper :
        phiSeq n x - phi x ≤ ε :=
      (abs_le.mp (hn x)).2
    have hphiSeq_upper : phiSeq n x ≤ targetRate := by
      have : phiSeq n x ≤ phi x + ε := by
        linarith
      have htarget : rate + ε + ε = targetRate := by
        dsimp [targetRate, ε]
        ring
      linarith
    have hexp_le :
        Real.exp (-(n : ℝ) * targetRate) ≤
          Real.exp (-(n : ℝ) * (phiSeq n x)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hphiSeq_upper
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    exact mul_le_mul hx.1 hexp_le (Real.exp_pos _).le
      (le_trans hcpos.le hx.1)
  have hset :
      HasExpLowerBoundWithConst
        (fun n : ℕ => ∫ x in s, F n x ∂μ)
        targetRate :=
    setIntegral_hasExpLowerBoundWithConst_of_ae_const_exp_le
      μ hμs_pos hcpos (fun n => (hF_int n).integrableOn) hlower
  have hfull :
      HasExpLowerBoundWithConst
        (fun n : ℕ => ∫ x, F n x ∂μ)
        targetRate :=
    integral_hasExpLowerBoundWithConst_of_setIntegral_lower_bound
      μ hset hF_int hF_nonneg
  rcases hfull with ⟨cfull, hcfull_pos, hbound⟩
  filter_upwards [hbound] with n hn
  exact (mul_pos hcfull_pos (Real.exp_pos _)).trans_le hn

/--
Certificate form of the weighted compact-Laplace theorem.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ w phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate where
  eventually_pos :=
    weightedLaplaceIntegral_eventually_pos_of_uniform_tendsto_weightedEssentialInf
      μ w phiSeq phi hF_int hw_nonneg hweighted_near huniform
  has_rate :=
    weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_weightedEssentialInf
      μ w phiSeq phi hF_int hWpos hw_nonneg hw_bound hess
      hweighted_near huniform

/--
Positive-kernel form of the weighted compact-Laplace theorem.  If
`-log (F n x) / n` converges uniformly to `phi x`, then the weighted integral
of `F n` has the same exponential-rate certificate as the corresponding
Laplace integral.

This is the reusable bridge for papers whose integrands are error
probabilities rather than literal exponentials.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) μ)
    (hw_int : Integrable w μ)
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ w phi rate)
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ)
      rate := by
  let phiSeq : ℕ → α → ℝ :=
    fun n x => if n = 0 then 0 else -Real.log (F n x) / (n : ℝ)
  have hExp_eq :
      ∀ {n : ℕ}, n ≠ 0 →
        ∀ x : α,
          Real.exp (-(n : ℝ) * phiSeq n x) = F n x := by
    intro n hn x
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hlog :
        -(n : ℝ) * phiSeq n x = Real.log (F n x) := by
      dsimp [phiSeq]
      simp [hn]
      field_simp [hnreal]
    rw [hlog]
    exact Real.exp_log (hF_pos n x)
  have hLaplace_int :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp (-(n : ℝ) * phiSeq n x)) μ := by
    intro n
    by_cases hn : n = 0
    · simpa [phiSeq, hn] using hw_int
    · refine (hF_int n).congr ?_
      filter_upwards with x
      simp [(hExp_eq hn x).symm]
  have huniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ x : α, |phiSeq n x - phi x| ≤ ε := by
    intro ε hε
    filter_upwards [huniform_log ε hε, eventually_gt_atTop 0] with n hnlog hnpos x
    have hn : n ≠ 0 := Nat.ne_of_gt hnpos
    simpa [phiSeq, hn] using hnlog x
  have hcert :
      ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ x, w x * Real.exp (-(n : ℝ) * phiSeq n x) ∂μ)
        rate :=
    weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
      μ w phiSeq phi hLaplace_int hWpos hw_nonneg hw_bound hess
      hweighted_near huniform
  refine ExponentialRateCertificate.congr ?_ hcert
  filter_upwards [eventually_gt_atTop 0] with n hnpos
  apply integral_congr_ae
  filter_upwards with x
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  simp [(hExp_eq hn x).symm]

/--
Source-style normalized logarithmic rate of a positive kernel.  The value at
`n = 0` is arbitrary; all large-deviation uses are eventual in `n`.
-/
def normalizedLogKernelRate
    {α : Type*} (F : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  if n = 0 then 0 else -Real.log (F n x) / (n : ℝ)

/--
Away from the arbitrary `n = 0` convention, the source-style normalized log
rate of a kernel is the same as the library's `logDecay` sequence at a fixed
parameter value.
-/
theorem normalizedLogKernelRate_eq_logDecay_at_of_ne
    {α : Type*} {F : ℕ → α → ℝ} {n : ℕ} (hn : n ≠ 0) (x : α) :
    normalizedLogKernelRate F n x = logDecay (fun k : ℕ => F k x) n := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [normalizedLogKernelRate, logDecay, hn]
  field_simp [hnreal]

/--
An exact exponential-rate certificate at a fixed parameter gives convergence
of the paper-style normalized logarithmic kernel rate at that parameter.
-/
theorem normalizedLogKernelRate_tendsto_of_exponentialRateCertificate
    {α : Type*} {F : ℕ → α → ℝ} {x : α} {rate : ℝ}
    (h : ExponentialRateCertificate (fun n : ℕ => F n x) rate) :
    Tendsto (fun n : ℕ => normalizedLogKernelRate F n x) atTop
      (nhds rate) := by
  have hrate :
      Tendsto (logDecay (fun n : ℕ => F n x)) atTop (nhds rate) := by
    simpa [HasExponentialRate] using h.has_rate
  refine hrate.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (normalizedLogKernelRate_eq_logDecay_at_of_ne
    (F := F) (Nat.ne_of_gt hn) x).symm

/--
Finite families of exact exponential-rate certificates give uniform
source-normalized-log convergence over the finite parameter set.
-/
theorem normalizedLogKernelRate_uniform_tendsto_fintype_of_exponentialRateCertificate
    {ι : Type*} [Fintype ι] {F : ℕ → ι → ℝ} {rate : ι → ℝ}
    (h : ∀ i : ι,
      ExponentialRateCertificate (fun n : ℕ => F n i) (rate i)) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ i : ι, |normalizedLogKernelRate F n i - rate i| ≤ ε := by
  intro ε hε
  filter_upwards
    [ExponentialRateCertificate.uniform_logDecay_fintype h ε hε,
      eventually_gt_atTop 0] with n hnlog hnpos i
  rw [normalizedLogKernelRate_eq_logDecay_at_of_ne
    (F := F) (Nat.ne_of_gt hnpos) i]
  exact hnlog i

/--
Uniform logarithmic convergence from a source-style exponential sandwich.
This is the algebraic core behind uniform large-deviation estimates: once
`F n x` is eventually trapped between `exp (-n * (rate x + eps))` and
`exp (-n * (rate x - eps))`, uniformly over a set, the normalized log kernel
converges uniformly to `rate` on that set.
-/
theorem normalizedLogKernelRate_uniform_on_of_exp_sandwich
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (hlower :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          Real.exp (-(n : ℝ) * (rate x + ε)) ≤ F n x)
    (hupper :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          F n x ≤ Real.exp (-(n : ℝ) * (rate x - ε))) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        |normalizedLogKernelRate F n x - rate x| ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hδle : δ ≤ ε := by dsimp [δ]; linarith
  filter_upwards
    [hlower δ hδpos, hupper δ hδpos, eventually_gt_atTop 0] with
    n hn_lower hn_upper hnpos x hx
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hF_pos : 0 < F n x :=
    lt_of_lt_of_le (Real.exp_pos _) (hn_lower x hx)
  have hlog_lower :
      -(n : ℝ) * (rate x + δ) ≤ Real.log (F n x) := by
    have hlog :=
      Real.log_le_log (Real.exp_pos (-(n : ℝ) * (rate x + δ)))
        (hn_lower x hx)
    simpa [Real.log_exp] using hlog
  have hlog_upper :
      Real.log (F n x) ≤ -(n : ℝ) * (rate x - δ) := by
    have hlog := Real.log_le_log hF_pos (hn_upper x hx)
    simpa [Real.log_exp] using hlog
  have hnorm_eq :
      normalizedLogKernelRate F n x =
        -Real.log (F n x) / (n : ℝ) := by
    simp [normalizedLogKernelRate, hn_ne]
  have hnorm_upper :
      normalizedLogKernelRate F n x ≤ rate x + δ := by
    rw [hnorm_eq]
    apply (div_le_iff₀ hnreal).2
    linarith
  have hnorm_lower :
      rate x - δ ≤ normalizedLogKernelRate F n x := by
    rw [hnorm_eq]
    apply (le_div_iff₀ hnreal).2
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/--
Uniform logarithmic convergence from a constant-factor exponential sandwich.
This is the form matching most reusable Chernoff/Cramer outputs: constants in
front of the exponent vanish after division by `n`.
-/
theorem normalizedLogKernelRate_uniform_on_of_exp_sandwich_const
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlower :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          c * Real.exp (-(n : ℝ) * (rate x + ε)) ≤ F n x)
    (hupper :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          F n x ≤ C * Real.exp (-(n : ℝ) * (rate x - ε))) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        |normalizedLogKernelRate F n x - rate x| ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / 3
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have h2δle : 2 * δ ≤ ε := by dsimp [δ]; linarith
  have hdivC_tendsto :
      Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
  have hdivc_tendsto :
      Tendsto (fun n : ℕ => Real.log c / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log c)
  have hdivC_event :
      ∀ᶠ n : ℕ in atTop, |Real.log C| / (n : ℝ) ≤ δ := by
    have hclose := (Metric.tendsto_nhds.1 hdivC_tendsto) δ hδpos
    filter_upwards [hclose] with n hn
    simpa [Real.dist_eq] using hn.le
  have hdivc_event :
      ∀ᶠ n : ℕ in atTop, |Real.log c| / (n : ℝ) ≤ δ := by
    have hclose := (Metric.tendsto_nhds.1 hdivc_tendsto) δ hδpos
    filter_upwards [hclose] with n hn
    simpa [Real.dist_eq] using hn.le
  filter_upwards
    [hlower δ hδpos, hupper δ hδpos, hdivC_event, hdivc_event,
      eventually_gt_atTop 0] with
    n hn_lower hn_upper hdivC hdivc hnpos x hx
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hleft_pos :
      0 < c * Real.exp (-(n : ℝ) * (rate x + δ)) :=
    mul_pos hc (Real.exp_pos _)
  have hF_pos : 0 < F n x :=
    lt_of_lt_of_le hleft_pos (hn_lower x hx)
  have hlog_lower :
      Real.log c + (-(n : ℝ) * (rate x + δ)) ≤
        Real.log (F n x) := by
    have hlog := Real.log_le_log hleft_pos (hn_lower x hx)
    rwa [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hright_pos :
      0 < C * Real.exp (-(n : ℝ) * (rate x - δ)) :=
    mul_pos hC (Real.exp_pos _)
  have hlog_upper :
      Real.log (F n x) ≤
        Real.log C + (-(n : ℝ) * (rate x - δ)) := by
    have hlog := Real.log_le_log hF_pos (hn_upper x hx)
    rwa [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hnorm_eq :
      normalizedLogKernelRate F n x =
        -Real.log (F n x) / (n : ℝ) := by
    simp [normalizedLogKernelRate, hn_ne]
  have hneg_logc_div_le : -Real.log c / (n : ℝ) ≤ δ := by
    have hneg_abs : -Real.log c ≤ |Real.log c| := neg_le_abs _
    have hdiv :
        -Real.log c / (n : ℝ) ≤ |Real.log c| / (n : ℝ) :=
      div_le_div_of_nonneg_right hneg_abs hnreal.le
    exact hdiv.trans hdivc
  have hlogC_div_le : Real.log C / (n : ℝ) ≤ δ :=
    (div_le_div_of_nonneg_right (le_abs_self (Real.log C)) hnreal.le).trans
      hdivC
  have hnorm_upper :
      normalizedLogKernelRate F n x ≤ rate x + 2 * δ := by
    rw [hnorm_eq]
    apply (div_le_iff₀ hnreal).2
    have hbase :
        -Real.log (F n x) ≤
          (n : ℝ) * (rate x + δ) - Real.log c := by
      linarith
    have hconst : -Real.log c ≤ (n : ℝ) * δ := by
      simpa [mul_comm] using (div_le_iff₀ hnreal).1 hneg_logc_div_le
    have htarget :
        (n : ℝ) * (rate x + δ) - Real.log c ≤
          (rate x + 2 * δ) * (n : ℝ) := by
      nlinarith
    exact hbase.trans htarget
  have hnorm_lower :
      rate x - 2 * δ ≤ normalizedLogKernelRate F n x := by
    rw [hnorm_eq]
    apply (le_div_iff₀ hnreal).2
    have hbase :
        (n : ℝ) * (rate x - δ) - Real.log C ≤
          -Real.log (F n x) := by
      linarith
    have hconst : Real.log C ≤ (n : ℝ) * δ := by
      simpa [mul_comm] using (div_le_iff₀ hnreal).1 hlogC_div_le
    have htarget :
        (rate x - 2 * δ) * (n : ℝ) ≤
          (n : ℝ) * (rate x - δ) - Real.log C := by
      nlinarith
    exact htarget.trans hbase
  rw [abs_sub_le_iff]
  constructor <;> linarith

/--
Uniform-on-set exponential-rate certificate for a source-shaped kernel.  The
constant prefactors are allowed because they disappear after normalizing
`-log` by the sample size.
-/
structure UniformExponentialRateCertificateOn
    {α : Type*} (F : ℕ → α → ℝ) (rate : α → ℝ) (s : Set α) where
  lowerConst : ℝ
  upperConst : ℝ
  lowerConst_pos : 0 < lowerConst
  upperConst_pos : 0 < upperConst
  lower :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        lowerConst * Real.exp (-(n : ℝ) * (rate x + ε)) ≤ F n x
  upper :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        F n x ≤ upperConst * Real.exp (-(n : ℝ) * (rate x - ε))

/--
Uniform-on-set normalized-log large-deviation certificate for a source-shaped
kernel.  This is the most direct form of assumptions such as
`-log F_n(x) / n -> rate x` uniformly on a compact parameter set.
-/
structure UniformNormalizedLogRateCertificateOn
    {α : Type*} (F : ℕ → α → ℝ) (rate : α → ℝ) (s : Set α) where
  eventually_pos :
    ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x
  uniform :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        |normalizedLogKernelRate F n x - rate x| ≤ ε

namespace UniformExponentialRateCertificateOn

/--
Build a unit-constant exponential sandwich from eventual positivity and
uniform convergence of the normalized log-kernel rate.
-/
def of_eventually_pos_normalizedLogKernelRate_uniform
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x, x ∈ s → 0 < F n x)
    (huniform :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          |normalizedLogKernelRate F n x - rate x| ≤ ε) :
    UniformExponentialRateCertificateOn F rate s where
  lowerConst := 1
  upperConst := 1
  lowerConst_pos := zero_lt_one
  upperConst_pos := zero_lt_one
  lower := by
    intro ε hε
    filter_upwards [hpos, huniform ε hε, eventually_gt_atTop 0] with
      n hnposF hn hnpos x hx
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
    have hFpos : 0 < F n x := hnposF x hx
    have hnorm_upper :
        normalizedLogKernelRate F n x ≤ rate x + ε := by
      have habs := hn x hx
      rw [abs_sub_le_iff] at habs
      linarith
    have hlog_lower :
        -(n : ℝ) * (rate x + ε) ≤ Real.log (F n x) := by
      have hnorm_eq :
          normalizedLogKernelRate F n x =
            -Real.log (F n x) / (n : ℝ) := by
        simp [normalizedLogKernelRate, hn_ne]
      rw [hnorm_eq] at hnorm_upper
      have hmul :=
        (div_le_iff₀ hnreal).1 hnorm_upper
      linarith
    have hexp_le : Real.exp (-(n : ℝ) * (rate x + ε)) ≤ F n x := by
      rw [← Real.exp_log hFpos]
      exact Real.exp_le_exp.mpr hlog_lower
    simpa using hexp_le
  upper := by
    intro ε hε
    filter_upwards [hpos, huniform ε hε, eventually_gt_atTop 0] with
      n hnposF hn hnpos x hx
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
    have hFpos : 0 < F n x := hnposF x hx
    have hnorm_lower :
        rate x - ε ≤ normalizedLogKernelRate F n x := by
      have habs := hn x hx
      rw [abs_sub_le_iff] at habs
      linarith
    have hlog_upper :
        Real.log (F n x) ≤ -(n : ℝ) * (rate x - ε) := by
      have hnorm_eq :
          normalizedLogKernelRate F n x =
            -Real.log (F n x) / (n : ℝ) := by
        simp [normalizedLogKernelRate, hn_ne]
      rw [hnorm_eq] at hnorm_lower
      have hmul :=
        (le_div_iff₀ hnreal).1 hnorm_lower
      linarith
    have hexp_le : F n x ≤ Real.exp (-(n : ℝ) * (rate x - ε)) := by
      rw [← Real.exp_log hFpos]
      exact Real.exp_le_exp.mpr hlog_upper
    simpa using hexp_le

/--
Build a unit-constant exponential sandwich from uniform convergence of the
normalized log-kernel rate and pointwise positivity.
-/
def of_normalizedLogKernelRate_uniform
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (huniform :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          |normalizedLogKernelRate F n x - rate x| ≤ ε) :
    UniformExponentialRateCertificateOn F rate s :=
  of_eventually_pos_normalizedLogKernelRate_uniform
    (by
      filter_upwards with n x hx
      exact hpos n x hx)
    huniform

/--
Build a uniform exponential-rate certificate on `s` from compact-local
normalized-log estimates on a compact superset `K`.
-/
def of_locally_normalizedLogKernelRate_uniform_on_compact_superset
    {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (hlocal :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ n : ℕ in atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate F n y - rate y| ≤ ε) :
    UniformExponentialRateCertificateOn F rate s :=
  of_normalizedLogKernelRate_uniform hpos
    (AppliedModelingLib.Math.eventually_uniform_abs_sub_le_on_subset_of_eventually_local_uniform_on_compact
      hKcompact hsub hlocal)

/--
A uniform exponential sandwich gives uniform convergence of the normalized
log-kernel rate on the same set.
-/
theorem normalizedLogKernelRate_uniform
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformExponentialRateCertificateOn F rate s) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        |normalizedLogKernelRate F n x - rate x| ≤ ε :=
  normalizedLogKernelRate_uniform_on_of_exp_sandwich_const
    C.lowerConst_pos C.upperConst_pos C.lower C.upper

/--
The lower half of a uniform exponential sandwich gives eventual positivity on
the certified set.
-/
theorem eventually_pos
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformExponentialRateCertificateOn F rate s) :
    ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x := by
  filter_upwards [C.lower 1 (by norm_num)] with n hn x hx
  exact lt_of_lt_of_le
    (mul_pos C.lowerConst_pos (Real.exp_pos _)) (hn x hx)

/--
A uniform exponential-rate sandwich is a uniform normalized-log certificate.
-/
def toUniformNormalizedLogRateCertificateOn
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformExponentialRateCertificateOn F rate s) :
    UniformNormalizedLogRateCertificateOn F rate s where
  eventually_pos := C.eventually_pos
  uniform := C.normalizedLogKernelRate_uniform

/--
A uniform exponential-rate certificate restricts to an exact pointwise
exponential-rate certificate at every point in the certified set.
-/
def toExponentialRateCertificate
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformExponentialRateCertificateOn F rate s)
    {x : α} (hx : x ∈ s) :
    ExponentialRateCertificate (fun n : ℕ => F n x) (rate x) where
  eventually_pos := by
    filter_upwards [C.eventually_pos] with n hn
    exact hn x hx
  has_rate := by
    have hnorm :
        Tendsto (fun n : ℕ => normalizedLogKernelRate F n x)
          atTop (𝓝 (rate x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hε2 : 0 < ε / 2 := by linarith
      have hclose_eventual := C.normalizedLogKernelRate_uniform (ε / 2) hε2
      have hclose :
          ∀ᶠ n : ℕ in atTop,
            |normalizedLogKernelRate F n x - rate x| ≤ ε / 2 := by
        filter_upwards [hclose_eventual] with n hn
        exact hn x hx
      rcases (eventually_atTop.1 hclose) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hdist := hN n hn
      have : dist (normalizedLogKernelRate F n x) (rate x) ≤ ε / 2 := by
        simpa [Real.dist_eq] using hdist
      exact lt_of_le_of_lt this (by linarith)
    rw [HasExponentialRate]
    refine hnorm.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact normalizedLogKernelRate_eq_logDecay_at_of_ne
      (F := F) (Nat.ne_of_gt hn) x

end UniformExponentialRateCertificateOn

namespace UniformNormalizedLogRateCertificateOn

/--
Constructor for a normalized-log certificate from eventual
positivity and uniform normalized-log convergence on a set.
-/
def of_eventually_pos_uniform
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (huniform :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          |normalizedLogKernelRate F n x - rate x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s where
  eventually_pos := hpos
  uniform := huniform

/--
All-index positivity plus uniform normalized-log convergence gives a
normalized-log certificate.
-/
def of_forall_pos_uniform
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (huniform :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          |normalizedLogKernelRate F n x - rate x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_eventually_pos_uniform
    (by
      filter_upwards with n x hx
      exact hpos n x hx)
    huniform

/--
A uniform normalized-log certificate gives a unit-constant uniform
exponential-rate sandwich.
-/
def toUniformExponentialRateCertificateOn
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformNormalizedLogRateCertificateOn F rate s) :
    UniformExponentialRateCertificateOn F rate s :=
  UniformExponentialRateCertificateOn.of_eventually_pos_normalizedLogKernelRate_uniform
    C.eventually_pos C.uniform

/--
A scalar exact exponential-rate certificate is uniform on every parameter set
when viewed as a parameter-constant kernel.
-/
def of_constant_exponentialRateCertificate
    {α : Type*} {p : ℕ → ℝ} {rate : ℝ} {s : Set α}
    (C : ExponentialRateCertificate p rate) :
    UniformNormalizedLogRateCertificateOn
      (fun n (_x : α) => p n) (fun _x : α => rate) s :=
  of_eventually_pos_uniform
    (by
      filter_upwards [C.eventually_pos] with n hnpos x hx
      exact hnpos)
    (by
      intro ε hε
      have hlog :
          ∀ᶠ n : ℕ in atTop, |logDecay p n - rate| ≤ ε :=
        by
          rcases (Metric.tendsto_atTop.1 C.has_rate) ε hε with ⟨N, hN⟩
          exact eventually_atTop.2 ⟨N, by
            intro n hn
            have hdist := hN n hn
            have habs : |logDecay p n - rate| < ε := by
              simpa [Real.dist_eq] using hdist
            exact le_of_lt habs⟩
      filter_upwards [hlog, eventually_gt_atTop 0] with n hnlog hnpos x hx
      rw [normalizedLogKernelRate_eq_logDecay_at_of_ne
        (F := fun n (_x : α) => p n) (Nat.ne_of_gt hnpos) x]
      simpa using hnlog)

/--
Compact-local normalized-log estimates on a compact superset give a uniform
normalized-log certificate on the target set.
-/
def of_locally_uniform_on_compact_superset
    {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hlocal :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ n : ℕ in atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate F n y - rate y| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_eventually_pos_uniform hpos
    (AppliedModelingLib.Math.eventually_uniform_abs_sub_le_on_subset_of_eventually_local_uniform_on_compact
      hKcompact hsub hlocal)

/--
Pointwise normalized-log convergence plus local asymptotic equicontinuity on a
compact superset gives a uniform normalized-log certificate on the target set.

This is the common bridge from fixed-parameter large-deviation certificates to
the compact-uniform certificates needed by continuum Laplace arguments.  The
remaining analytic work is isolated in the local oscillation hypotheses for
the limiting rate and the normalized log-kernels.
-/
def of_pointwise_tendsto_locally_equicontinuous_on_compact_superset
    {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hpoint :
      ∀ x : α, x ∈ K →
        Tendsto (fun n : ℕ => normalizedLogKernelRate F n x)
          atTop (𝓝 (rate x)))
    (hrate_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ y : α, y ∈ K → y ∈ U → |rate y - rate x| ≤ ε)
    (hlog_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ n : ℕ in atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate F n y -
                  normalizedLogKernelRate F n x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_locally_uniform_on_compact_superset hKcompact hsub hpos
    (by
      intro x hx ε hε
      let δ : ℝ := ε / 3
      have hδpos : 0 < δ := by
        dsimp [δ]
        linarith
      have hδsum : δ + δ + δ = ε := by
        dsimp [δ]
        ring
      rcases hrate_local x hx δ hδpos with
        ⟨Urate, hUrate_open, hxUrate, hrate⟩
      rcases hlog_local x hx δ hδpos with
        ⟨Ulog, hUlog_open, hxUlog, hlog⟩
      refine ⟨Urate ∩ Ulog, hUrate_open.inter hUlog_open,
        ⟨hxUrate, hxUlog⟩, ?_⟩
      have hpoint_eventual :
          ∀ᶠ n : ℕ in atTop,
            |normalizedLogKernelRate F n x - rate x| ≤ δ := by
        rcases (Metric.tendsto_atTop.1 (hpoint x hx)) δ hδpos with
          ⟨N, hN⟩
        exact eventually_atTop.2 ⟨N, by
          intro n hn
          have hdist := hN n hn
          exact le_of_lt (by simpa [Real.dist_eq] using hdist)⟩
      filter_upwards [hlog, hpoint_eventual] with n hnlog hnpoint y hy hyU
      have hlog_bound :
          |normalizedLogKernelRate F n y -
            normalizedLogKernelRate F n x| ≤ δ :=
        hnlog y hy hyU.2
      have hrate_bound : |rate y - rate x| ≤ δ :=
        hrate y hy hyU.1
      have hlog_upper :
          normalizedLogKernelRate F n y -
            normalizedLogKernelRate F n x ≤ δ :=
        (abs_sub_le_iff.mp hlog_bound).1
      have hlog_lower :
          normalizedLogKernelRate F n x -
            normalizedLogKernelRate F n y ≤ δ :=
        (abs_sub_le_iff.mp hlog_bound).2
      have hpoint_upper :
          normalizedLogKernelRate F n x - rate x ≤ δ :=
        (abs_sub_le_iff.mp hnpoint).1
      have hpoint_lower :
          rate x - normalizedLogKernelRate F n x ≤ δ :=
        (abs_sub_le_iff.mp hnpoint).2
      have hrate_yx : |rate x - rate y| ≤ δ := by
        simpa [abs_sub_comm] using hrate_bound
      have hrate_upper : rate y - rate x ≤ δ :=
        (abs_sub_le_iff.mp hrate_bound).1
      have hrate_lower : rate x - rate y ≤ δ :=
        (abs_sub_le_iff.mp hrate_yx).1
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [hlog_upper, hlog_lower, hpoint_upper,
        hpoint_lower, hrate_upper, hrate_lower, hδsum])

/--
Pointwise normalized-log convergence plus local asymptotic equicontinuity,
with the limiting rate's local oscillation discharged from continuity on the
compact superset.
-/
def of_pointwise_tendsto_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hpoint :
      ∀ x : α, x ∈ K →
        Tendsto (fun n : ℕ => normalizedLogKernelRate F n x)
          atTop (𝓝 (rate x)))
    (hrate_cont : ∀ x : α, x ∈ K → ContinuousAt rate x)
    (hlog_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ n : ℕ in atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate F n y -
                  normalizedLogKernelRate F n x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_pointwise_tendsto_locally_equicontinuous_on_compact_superset
    hKcompact hsub hpos hpoint
    (fun x hx ε hε => by
      rcases
        AppliedModelingLib.Math.exists_open_abs_sub_le_of_continuousAt
          (hrate_cont x hx) hε with
        ⟨U, hUopen, hxU, hU⟩
      exact ⟨U, hUopen, hxU, fun y _hy hyU => hU y hyU⟩)
    hlog_local

/--
Pointwise normalized-log convergence plus an eventual uniform Lipschitz bound
on the compact superset gives a uniform normalized-log certificate on the
target set.
-/
def of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    {α : Type*} [PseudoMetricSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hpoint :
      ∀ x : α, x ∈ K →
        Tendsto (fun n : ℕ => normalizedLogKernelRate F n x)
          atTop (𝓝 (rate x)))
    (hrate_cont : ∀ x : α, x ∈ K → ContinuousAt rate x)
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ K → ∀ y : α, y ∈ K →
          |normalizedLogKernelRate F n y -
            normalizedLogKernelRate F n x| ≤ L * dist y x) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_pointwise_tendsto_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos hpoint hrate_cont
    (AppliedModelingLib.Math.eventually_local_abs_sub_le_of_eventually_lipschitz_on
      hL hlog_lipschitz)

/--
Fixed-parameter exact exponential-rate certificates, plus local asymptotic
equicontinuity on a compact superset, give a uniform normalized-log
certificate on the target set.  The separate `hpos` premise is the genuinely
uniform positivity side condition; pointwise certificates alone only provide
pointwise eventual positivity.
-/
def of_pointwise_exponentialRateCertificate_locally_equicontinuous_on_compact_superset
    {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hcert :
      ∀ x : α, x ∈ K →
        ExponentialRateCertificate (fun n : ℕ => F n x) (rate x))
    (hrate_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ y : α, y ∈ K → y ∈ U → |rate y - rate x| ≤ ε)
    (hlog_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ n : ℕ in atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate F n y -
                  normalizedLogKernelRate F n x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_pointwise_tendsto_locally_equicontinuous_on_compact_superset
    hKcompact hsub hpos
    (fun x hx =>
      normalizedLogKernelRate_tendsto_of_exponentialRateCertificate
        (hcert x hx))
    hrate_local hlog_local

/--
Fixed-parameter exact exponential-rate certificates plus local asymptotic
equicontinuity, with limiting-rate oscillation discharged from continuity on
the compact superset.
-/
def of_pointwise_exponentialRateCertificate_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hcert :
      ∀ x : α, x ∈ K →
        ExponentialRateCertificate (fun n : ℕ => F n x) (rate x))
    (hrate_cont : ∀ x : α, x ∈ K → ContinuousAt rate x)
    (hlog_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ n : ℕ in atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate F n y -
                  normalizedLogKernelRate F n x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_pointwise_tendsto_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos
    (fun x hx =>
      normalizedLogKernelRate_tendsto_of_exponentialRateCertificate
        (hcert x hx))
    hrate_cont hlog_local

/--
Fixed-parameter exact exponential-rate certificates plus an eventual uniform
Lipschitz bound on the compact superset give a uniform normalized-log
certificate on the target set.
-/
def of_pointwise_exponentialRateCertificate_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    {α : Type*} [PseudoMetricSpace α]
    {F : ℕ → α → ℝ} {rate : α → ℝ} {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x)
    (hcert :
      ∀ x : α, x ∈ K →
        ExponentialRateCertificate (fun n : ℕ => F n x) (rate x))
    (hrate_cont : ∀ x : α, x ∈ K → ContinuousAt rate x)
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ K → ∀ y : α, y ∈ K →
          |normalizedLogKernelRate F n y -
            normalizedLogKernelRate F n x| ≤ L * dist y x) :
    UniformNormalizedLogRateCertificateOn F rate s :=
  of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos
    (fun x hx =>
      normalizedLogKernelRate_tendsto_of_exponentialRateCertificate
        (hcert x hx))
    hrate_cont hL hlog_lipschitz

/--
Restrict a uniform normalized-log certificate to a subset.
-/
def mono
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s t : Set α}
    (C : UniformNormalizedLogRateCertificateOn F rate t) (hsub : s ⊆ t) :
    UniformNormalizedLogRateCertificateOn F rate s where
  eventually_pos := by
    filter_upwards [C.eventually_pos] with n hn x hx
    exact hn x (hsub hx)
  uniform := by
    intro ε hε
    filter_upwards [C.uniform ε hε] with n hn x hx
    exact hn x (hsub hx)

/--
The certificate's normalized-log convergence in the raw source form
`-log F_n(x) / n`, away from the harmless `n = 0` convention in
`normalizedLogKernelRate`.
-/
theorem uniform_raw_log
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformNormalizedLogRateCertificateOn F rate s) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        |(-Real.log (F n x) / (n : ℝ)) - rate x| ≤ ε := by
  intro ε hε
  filter_upwards [C.uniform ε hε, eventually_gt_atTop 0] with n hn hnpos x hx
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
  simpa [normalizedLogKernelRate, hn_ne] using hn x hx

/-- Raw source-form normalized-log convergence for a certificate on `Set.univ`. -/
theorem uniform_raw_log_univ
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ}
    (C : UniformNormalizedLogRateCertificateOn F rate Set.univ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - rate x| ≤ ε := by
  intro ε hε
  filter_upwards [C.uniform_raw_log ε hε] with n hn x
  exact hn x (Set.mem_univ x)

/--
Lower exponential envelope extracted from a uniform normalized-log certificate.
If the limiting rate is at least `δ` below `targetRate` on `t`, then eventually
`exp (-n * targetRate)` lower-bounds the kernel on `t`.
-/
theorem eventually_exp_neg_targetRate_le_of_rate_add_le
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ}
    {s t : Set α}
    (C : UniformNormalizedLogRateCertificateOn F rate s)
    (hsub : t ⊆ s) {targetRate δ : ℝ}
    (hδpos : 0 < δ)
    (hrate : ∀ x : α, x ∈ t → rate x + δ ≤ targetRate) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ t →
        Real.exp (-(n : ℝ) * targetRate) ≤ F n x := by
  filter_upwards
    [C.eventually_pos, C.uniform δ hδpos, eventually_gt_atTop 0]
    with n hpos hunif hnpos x hx
  have hx_s : x ∈ s := hsub hx
  have hF_pos : 0 < F n x := hpos x hx_s
  have hnorm_le : normalizedLogKernelRate F n x ≤ targetRate := by
    have hnorm_le_delta :
        normalizedLogKernelRate F n x ≤ rate x + δ := by
      have habs := hunif x hx_s
      have hle : normalizedLogKernelRate F n x - rate x ≤ δ :=
        (abs_sub_le_iff.mp habs).1
      linarith
    exact hnorm_le_delta.trans (hrate x hx)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hnorm_eq :
      normalizedLogKernelRate F n x =
        -Real.log (F n x) / (n : ℝ) := by
    simp [normalizedLogKernelRate, hn_ne]
  rw [hnorm_eq] at hnorm_le
  have hmul :
      -Real.log (F n x) ≤ targetRate * (n : ℝ) :=
    (div_le_iff₀ hnreal).mp hnorm_le
  have hlog_ge :
      -(n : ℝ) * targetRate ≤ Real.log (F n x) := by
    nlinarith
  simpa [Real.exp_log hF_pos] using Real.exp_le_exp.mpr hlog_ge

/--
Weighted lower exponential envelope extracted from a uniform normalized-log
certificate and an almost-everywhere lower bound on the weight over the
restricted set.
-/
theorem eventually_ae_const_exp_le_weighted_kernel_of_rate_add_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {rate weight : α → ℝ}
    {s t : Set α}
    (C : UniformNormalizedLogRateCertificateOn F rate s)
    (ht_meas : MeasurableSet t)
    (hsub : t ⊆ s) {targetRate δ c : ℝ}
    (hcpos : 0 < c) (hδpos : 0 < δ)
    (hweight_lower : ∀ᵐ x ∂μ.restrict t, c ≤ weight x)
    (hrate : ∀ x : α, x ∈ t → rate x + δ ≤ targetRate) :
    ∀ᶠ n : ℕ in atTop,
      ∀ᵐ x ∂μ.restrict t,
        c * Real.exp (-(n : ℝ) * targetRate) ≤ weight x * F n x := by
  have hlower :=
    C.eventually_exp_neg_targetRate_le_of_rate_add_le
      hsub hδpos hrate
  filter_upwards [hlower] with n hn
  filter_upwards [hweight_lower, ae_restrict_mem ht_meas] with x hw hx
  have hkernel_lower :
      Real.exp (-(n : ℝ) * targetRate) ≤ F n x :=
    hn x hx
  have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * targetRate) :=
    (Real.exp_pos _).le
  have hweight_nonneg : 0 ≤ weight x := hcpos.le.trans hw
  calc
    c * Real.exp (-(n : ℝ) * targetRate)
        ≤ weight x * Real.exp (-(n : ℝ) * targetRate) :=
          mul_le_mul_of_nonneg_right hw hexp_nonneg
    _ ≤ weight x * F n x :=
          mul_le_mul_of_nonneg_left hkernel_lower hweight_nonneg

end UniformNormalizedLogRateCertificateOn

/--
Zero-rate weighted-kernel integral theorem from pointwise exponential-rate
certificates and near-minimizer sets with slack.

Unlike the uniform-normalized-log variants below, this theorem only assumes
pointwise rate certificates on each near-minimizer set.  The proof extracts a
positive-measure subset on which the pointwise prefactors and burn-in
thresholds can be made common by countability, then applies the generic
integral lower-bound skeleton.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_pointwiseExponentialRateCertificate_nearRate_sets
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x)
    (hupper_const :
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B)
    (hkernel_meas : ∀ n : ℕ, Measurable (kernel n))
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  ∀ x : α, x ∈ nearMinimizers →
                    ExponentialRateCertificate
                      (fun n : ℕ => kernel n x) (rate x)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  refine
    integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
      μ hBpos hkernel_int hkernel_nonneg hupper_const ?_
  intro targetRate htarget
  rcases hnear_sets targetRate htarget with
    ⟨nearMinimizers, c, δ, hmeas, hμpos, hcpos, hδpos,
      hkernel_set_int, hweight_lower, hrate, hcert⟩
  have hpoint_lower :
      ∀ x : α, x ∈ nearMinimizers →
        HasExpLowerBoundWithConst (fun n : ℕ => kernel n x) targetRate := by
    intro x hx
    exact
      (hcert x hx).hasExpLowerBoundWithConst_of_gt
        (by
          have hxrate := hrate x hx
          linarith)
  rcases
      exists_positive_measure_subset_eventually_ae_const_exp_le_of_pointwise_expLowerBounds
        μ hmeas hkernel_meas hμpos hpoint_lower with
    ⟨subsetMinimizers, kernelConst, hsubset_meas, hsubset_pos,
      hkernelConst_pos, hsubset, hkernel_lower⟩
  refine
    ⟨subsetMinimizers, c * kernelConst, hsubset_pos,
      mul_pos hcpos hkernelConst_pos, ?_, ?_⟩
  · intro n
    exact (hkernel_set_int n).mono_set hsubset
  · have hweight_lower_subset :
        ∀ᵐ x ∂μ.restrict subsetMinimizers, c ≤ weight x :=
      ae_restrict_of_ae_restrict_of_subset hsubset hweight_lower
    filter_upwards [hkernel_lower] with n hkernel_lower_n
    filter_upwards [hweight_lower_subset, hkernel_lower_n] with x hw hk
    have hkernelConst_exp_nonneg :
        0 ≤ kernelConst * Real.exp (-(n : ℝ) * targetRate) :=
      mul_nonneg hkernelConst_pos.le (Real.exp_pos _).le
    have hweight_nonneg : 0 ≤ weight x := hcpos.le.trans hw
    calc
      (c * kernelConst) * Real.exp (-(n : ℝ) * targetRate)
          = c * (kernelConst * Real.exp (-(n : ℝ) * targetRate)) := by ring
      _ ≤ weight x * (kernelConst * Real.exp (-(n : ℝ) * targetRate)) :=
          mul_le_mul_of_nonneg_right hw hkernelConst_exp_nonneg
      _ ≤ weight x * kernel n x :=
          mul_le_mul_of_nonneg_left hk hweight_nonneg

/--
Zero-rate weighted-kernel integral theorem from a uniform normalized-log
certificate and near-minimizer sets with slack.  For each positive target
rate, the caller supplies a positive-measure set on which the limiting rate is
strictly below that target and the weight is a.e. bounded below by a positive
constant. The uniform normalized-log certificate supplies the required
eventual exponential lower envelope on that set.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_nearRate_sets
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x)
    (hupper_const :
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            nearMinimizers ⊆ certSet ∧
              (∀ n : ℕ,
                IntegrableOn
                  (fun x : α => weight x * kernel n x)
                  nearMinimizers μ) ∧
                (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                  ∀ x : α, x ∈ nearMinimizers →
                    rate x + δ ≤ targetRate) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  refine
    integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
      μ hBpos hkernel_int hkernel_nonneg hupper_const ?_
  intro targetRate htarget
  rcases hnear_sets targetRate htarget with
    ⟨nearMinimizers, c, δ, hmeas, hμpos, hcpos, hδpos, hsub,
      hkernel_set_int, hweight_lower, hrate⟩
  refine ⟨nearMinimizers, c, hμpos, hcpos, hkernel_set_int, ?_⟩
  exact
    C.eventually_ae_const_exp_le_weighted_kernel_of_rate_add_le
      (μ := μ) hmeas hsub hcpos hδpos hweight_lower hrate

/--
Zero-rate weighted-kernel integral theorem with local normalized-log
certificates.  For each target rate, the caller may choose a positive-measure
near-minimizer set and prove uniform normalized-log convergence only on that
set.  This is the typical compact-local shape of continuum Laplace lower
bounds.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_localUniformNormalizedLogRateCertificate_nearRate_sets
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x)
    (hupper_const :
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  UniformNormalizedLogRateCertificateOn
                    kernel rate nearMinimizers) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  refine
    integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
      μ hBpos hkernel_int hkernel_nonneg hupper_const ?_
  intro targetRate htarget
  rcases hnear_sets targetRate htarget with
    ⟨nearMinimizers, c, δ, hmeas, hμpos, hcpos, hδpos,
      hkernel_set_int, hweight_lower, hrate, C⟩
  refine ⟨nearMinimizers, c, hμpos, hcpos, hkernel_set_int, ?_⟩
  exact
    C.eventually_ae_const_exp_le_weighted_kernel_of_rate_add_le
      (μ := μ) hmeas (fun _x hx => hx) hcpos hδpos hweight_lower hrate

/--
Zero-rate weighted-kernel integral theorem from a uniform normalized-log
certificate and the weighted near-essential-infimum interface at rate zero.
This is the source-shaped bridge for Laplace lower bounds where every
near-minimizer neighborhood contains positive measure on which the objective
weight is uniformly positive.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x)
    (hupper_const :
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B)
    (C : UniformNormalizedLogRateCertificateOn kernel rate Set.univ)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  refine
    integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
      μ hBpos hkernel_int hkernel_nonneg hupper_const ?_
  intro targetRate htarget
  let ε : ℝ := targetRate / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hweighted_near ε hεpos with
    ⟨nearMinimizers, c, hμpos, hcpos, hnear⟩
  refine ⟨nearMinimizers, c, hμpos, hcpos, fun n => (hkernel_int n).integrableOn, ?_⟩
  filter_upwards [C.eventually_pos, C.uniform ε hεpos, eventually_gt_atTop 0]
    with n hpos hunif hnpos
  filter_upwards [hnear] with x hx
  have hkernel_pos : 0 < kernel n x := hpos x (Set.mem_univ x)
  have hnorm_le : normalizedLogKernelRate kernel n x ≤ targetRate := by
    have hnorm_le_eps : normalizedLogKernelRate kernel n x ≤ rate x + ε := by
      have habs := hunif x (Set.mem_univ x)
      have hle : normalizedLogKernelRate kernel n x - rate x ≤ ε :=
        (abs_sub_le_iff.mp habs).1
      linarith
    have hrate_le : rate x + ε ≤ targetRate := by
      have hx_rate : rate x ≤ targetRate / 2 := by
        simpa [ε] using hx.2
      dsimp [ε]
      linarith
    exact hnorm_le_eps.trans hrate_le
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hnorm_eq :
      normalizedLogKernelRate kernel n x =
        -Real.log (kernel n x) / (n : ℝ) := by
    simp [normalizedLogKernelRate, hn_ne]
  rw [hnorm_eq] at hnorm_le
  have hmul :
      -Real.log (kernel n x) ≤ targetRate * (n : ℝ) :=
    (div_le_iff₀ hnreal).mp hnorm_le
  have hlog_ge :
      -(n : ℝ) * targetRate ≤ Real.log (kernel n x) := by
    nlinarith
  have hkernel_lower :
      Real.exp (-(n : ℝ) * targetRate) ≤ kernel n x := by
    simpa [Real.exp_log hkernel_pos] using Real.exp_le_exp.mpr hlog_ge
  have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * targetRate) :=
    (Real.exp_pos _).le
  have hweight_nonneg : 0 ≤ weight x := hcpos.le.trans hx.1
  calc
    c * Real.exp (-(n : ℝ) * targetRate)
        ≤ weight x * Real.exp (-(n : ℝ) * targetRate) :=
          mul_le_mul_of_nonneg_right hx.1 hexp_nonneg
    _ ≤ weight x * kernel n x :=
          mul_le_mul_of_nonneg_left hkernel_lower hweight_nonneg

/--
Zero-rate weighted-kernel integral theorem from a uniform normalized-log
certificate on a set that contains the integration measure almost everywhere,
and the weighted near-essential-infimum interface at rate zero.  This is the
cell-local version for restricted measures.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x)
    (hupper_const :
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  refine
    integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
      μ hBpos hkernel_int hkernel_nonneg hupper_const ?_
  intro targetRate htarget
  let ε : ℝ := targetRate / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hweighted_near ε hεpos with
    ⟨nearMinimizers, c, hμpos, hcpos, hnear⟩
  refine ⟨nearMinimizers, c, hμpos, hcpos, fun n => (hkernel_int n).integrableOn, ?_⟩
  filter_upwards [C.eventually_pos, C.uniform ε hεpos, eventually_gt_atTop 0]
    with n hpos hunif hnpos
  filter_upwards [hnear, ae_restrict_of_ae hcertSet_ae] with x hx hx_cert
  have hkernel_pos : 0 < kernel n x := hpos x hx_cert
  have hnorm_le : normalizedLogKernelRate kernel n x ≤ targetRate := by
    have hnorm_le_eps : normalizedLogKernelRate kernel n x ≤ rate x + ε := by
      have habs := hunif x hx_cert
      have hle : normalizedLogKernelRate kernel n x - rate x ≤ ε :=
        (abs_sub_le_iff.mp habs).1
      linarith
    have hrate_le : rate x + ε ≤ targetRate := by
      have hx_rate : rate x ≤ targetRate / 2 := by
        simpa [ε] using hx.2
      dsimp [ε]
      linarith
    exact hnorm_le_eps.trans hrate_le
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hnorm_eq :
      normalizedLogKernelRate kernel n x =
        -Real.log (kernel n x) / (n : ℝ) := by
    simp [normalizedLogKernelRate, hn_ne]
  rw [hnorm_eq] at hnorm_le
  have hmul :
      -Real.log (kernel n x) ≤ targetRate * (n : ℝ) :=
    (div_le_iff₀ hnreal).mp hnorm_le
  have hlog_ge :
      -(n : ℝ) * targetRate ≤ Real.log (kernel n x) := by
    nlinarith
  have hkernel_lower :
      Real.exp (-(n : ℝ) * targetRate) ≤ kernel n x := by
    simpa [Real.exp_log hkernel_pos] using Real.exp_le_exp.mpr hlog_ge
  have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * targetRate) :=
    (Real.exp_pos _).le
  have hweight_nonneg : 0 ≤ weight x := hcpos.le.trans hx.1
  calc
    c * Real.exp (-(n : ℝ) * targetRate)
        ≤ weight x * Real.exp (-(n : ℝ) * targetRate) :=
          mul_le_mul_of_nonneg_right hx.1 hexp_nonneg
    _ ≤ weight x * kernel n x :=
          mul_le_mul_of_nonneg_left hkernel_lower hweight_nonneg

/--
Construct the explicit near-minimizer sets used by continuum Laplace lower
bounds.  A continuous zero of the limiting rate in the closure of the cell's
interior, together with a continuous positive weight, gives positive-measure
sets on which the weight is uniformly positive, the rate is within any target
gap, and a global uniform normalized-log certificate restricts locally.
-/
theorem localUniformNormalizedLogRateCertificate_nearRate_sets_of_continuousAt_zero_weight_pos_restrict_closure_interior_of_cell_subset_certSet
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    (hkernel_int :
      ∀ n : ℕ,
        Integrable (fun x : α => weight x * kernel n x) (μ.restrict cell))
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcell_subset_certSet : cell ⊆ certSet)
    (x0 : α)
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < (μ.restrict cell).real nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ n : ℕ,
                IntegrableOn
                  (fun x : α => weight x * kernel n x)
                  nearMinimizers (μ.restrict cell)) ∧
                (∀ᵐ x ∂(μ.restrict cell).restrict nearMinimizers,
                  c ≤ weight x) ∧
                  (∀ x : α, x ∈ nearMinimizers →
                    rate x + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel rate nearMinimizers := by
  intro targetRate htarget
  let ε : ℝ := targetRate / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  let c : ℝ := weight x0 / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hw_target : {y : ℝ | c < y} ∈ 𝓝 (weight x0) :=
    IsOpen.mem_nhds isOpen_Ioi (by dsimp [c]; linarith)
  have hrate_target : {y : ℝ | y < ε} ∈ 𝓝 (rate x0) := by
    rw [hrate_x0]
    exact IsOpen.mem_nhds isOpen_Iio hεpos
  have hw_pre : {x : α | c < weight x} ∈ 𝓝 x0 :=
    hweight_cont hw_target
  have hrate_pre : {x : α | rate x < ε} ∈ 𝓝 x0 :=
    hrate_cont hrate_target
  have hpre :
      ({x : α | c < weight x} ∩ {x : α | rate x < ε}) ∈ 𝓝 x0 :=
    Filter.inter_mem hw_pre hrate_pre
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  let nearMinimizers : Set α := cell ∩ U
  have hnear_meas : MeasurableSet nearMinimizers :=
    hcell.inter hUopen.measurableSet
  have hlocal_pos : 0 < μ (cell ∩ U) :=
    HasAEEssentialInfimum.local_pos_of_mem_closure_interior
      μ hclosure U hUopen hxU
  have hrestrict_pos : 0 < (μ.restrict cell) nearMinimizers := by
    rw [Measure.restrict_apply hnear_meas]
    have hset_eq : (cell ∩ U) ∩ cell = cell ∩ U := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.1.2⟩
      · intro hx
        exact ⟨hx, hx.1⟩
    simpa [nearMinimizers, hset_eq] using hlocal_pos
  have hnear_real_pos : 0 < (μ.restrict cell).real nearMinimizers :=
    ENNReal.toReal_pos (ne_of_gt hrestrict_pos)
      (measure_ne_top (μ.restrict cell) nearMinimizers)
  refine
    ⟨nearMinimizers, c, ε, hnear_meas, hnear_real_pos, hcpos, hεpos,
      ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hkernel_int n).integrableOn
  · exact
      ae_restrict_of_forall_mem hnear_meas (by
        intro x hx
        have hxU' : x ∈ U := hx.2
        exact le_of_lt (hUsub hxU').1)
  · intro x hx
    have hxU' : x ∈ U := hx.2
    have hrate_lt : rate x < ε := (hUsub hxU').2
    have hrate_le_half : rate x ≤ targetRate / 2 := by
      dsimp [ε] at hrate_lt
      linarith
    dsimp [ε]
    linarith
  · exact C.mono (fun x hx => hcell_subset_certSet hx.1)

/--
Restricted-cell continuous zero-rate bridge for weighted kernels.  A
continuous limiting rate that vanishes at a closure/interior-supported point,
together with a continuous positive weight there, supplies the weighted
near-essential-infimum witness needed by the zero-rate normalized-log theorem.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {B : ℝ}
    (x0 : α)
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ n : ℕ,
        Integrable (fun x : α => weight x * kernel n x) (μ.restrict cell))
    (hkernel_nonneg :
      ∀ n : ℕ,
        ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x * kernel n x)
    (hupper_const :
      ∀ᶠ n : ℕ in atTop,
        (∫ x, weight x * kernel n x ∂μ.restrict cell) ≤ B)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ.restrict cell, x ∈ certSet)
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ.restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    (μ.restrict cell) hBpos hkernel_int hkernel_nonneg hupper_const C
    hcertSet_ae
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict_closure_interior
      (μ := μ) hcell x0 hrate_x0 hrate_cont hweight_cont
      hweight_x0_pos hclosure)

/--
A nonnegative bounded measurable kernel can multiply an integrable weight
without losing integrability.  This packages the common source-side step where
an error-probability kernel is bounded uniformly in the sample size.
-/
theorem integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {K : ℝ}
    (hweight_int : Integrable weight μ)
    (hkernel_meas : ∀ n : ℕ, AEStronglyMeasurable (kernel n) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K) :
    ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ := by
  intro n
  refine hweight_int.mul_bdd (c := K) (hkernel_meas n) ?_
  filter_upwards [hkernel_bound n] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/--
A nonnegative integrable weight times a probability-style kernel bounded by
`1` is integrable.  This is the common version for source kernels that are
ordinary probabilities rather than two-sided error sums.
-/
theorem integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ}
    (hweight_int : Integrable weight μ)
    (hkernel_meas : ∀ n : ℕ, AEStronglyMeasurable (kernel n) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ 1) :
    ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ :=
  integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
    μ (K := 1) hweight_int hkernel_meas hkernel_bound

/--
Eventual version of
`integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const`.
This is the common source-model situation where measurability and a uniform
a.e. kernel bound are established only after ignoring finitely many sample
sizes.
-/
theorem eventually_integrable_weight_mul_kernel_of_integrable_weight_of_eventually_ae_kernel_between_zero_const
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {K : ℝ}
    (hweight_int : Integrable weight μ)
    (hkernel_meas :
      ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (kernel n) μ)
    (hkernel_bound :
      ∀ᶠ n : ℕ in atTop,
        ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      Integrable (fun x : α => weight x * kernel n x) μ := by
  filter_upwards [hkernel_meas, hkernel_bound] with n hn_meas hn_bound
  refine hweight_int.mul_bdd (c := K) hn_meas ?_
  filter_upwards [hn_bound] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/--
A nonnegative integrable weight times a nonnegative kernel bounded by a fixed
constant has a positive constant upper bound on its integral.  This packages
the routine upper-bound side condition in weighted error-probability Laplace
arguments whose kernels are bounded by a constant other than `1`.
-/
theorem exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_const
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B := by
  let B : ℝ := ∫ x, K * weight x ∂μ + 1
  have hKweight_int : Integrable (fun x : α => K * weight x) μ :=
    hweight_int.const_mul K
  have hKweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ K * weight x := by
    filter_upwards [hweight_nonneg] with x hw
    exact mul_nonneg hK_nonneg hw
  have hKweight_integral_nonneg : 0 ≤ ∫ x, K * weight x ∂μ :=
    integral_nonneg_of_ae hKweight_nonneg
  have hBpos : 0 < B := by
    dsimp [B]
    linarith
  refine ⟨B, hBpos, ?_⟩
  filter_upwards with n
  have hle_ae :
      ∀ᵐ x ∂μ, weight x * kernel n x ≤ K * weight x := by
    filter_upwards [hweight_nonneg, hkernel_bound n] with x hw hk
    have hmul := mul_le_mul_of_nonneg_left hk.2 hw
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hle_integral :
      (∫ x, weight x * kernel n x ∂μ) ≤ ∫ x, K * weight x ∂μ :=
    integral_mono_ae (hkernel_int n) hKweight_int hle_ae
  dsimp [B]
  linarith

/--
Eventual version of
`exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_const`.
This is useful when product integrability and the a.e. kernel bound are only
known after discarding finitely many sample sizes.
-/
theorem exists_pos_const_eventually_integral_weightedKernel_le_of_eventually_ae_kernel_between_zero_const
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ᶠ n : ℕ in atTop,
        Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_bound :
      ∀ᶠ n : ℕ in atTop,
        ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B := by
  let B : ℝ := ∫ x, K * weight x ∂μ + 1
  have hKweight_int : Integrable (fun x : α => K * weight x) μ :=
    hweight_int.const_mul K
  have hKweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ K * weight x := by
    filter_upwards [hweight_nonneg] with x hw
    exact mul_nonneg hK_nonneg hw
  have hKweight_integral_nonneg : 0 ≤ ∫ x, K * weight x ∂μ :=
    integral_nonneg_of_ae hKweight_nonneg
  have hBpos : 0 < B := by
    dsimp [B]
    linarith
  refine ⟨B, hBpos, ?_⟩
  filter_upwards [hkernel_int, hkernel_bound] with n hn_int hn_bound
  have hle_ae :
      ∀ᵐ x ∂μ, weight x * kernel n x ≤ K * weight x := by
    filter_upwards [hweight_nonneg, hn_bound] with x hw hk
    have hmul := mul_le_mul_of_nonneg_left hk.2 hw
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hle_integral :
      (∫ x, weight x * kernel n x ∂μ) ≤ ∫ x, K * weight x ∂μ :=
    integral_mono_ae hn_int hKweight_int hle_ae
  dsimp [B]
  linarith

/--
A nonnegative integrable weight times a probability kernel bounded by `1` has
a positive constant upper bound on its integral.  This packages the routine
upper-bound side condition in weighted error-probability Laplace arguments.
-/
theorem exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ}
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ 1) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n : ℕ in atTop, (∫ x, weight x * kernel n x ∂μ) ≤ B := by
  exact
    exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_const
      (μ := μ) (K := 1) (by norm_num) hweight_int hweight_nonneg
      hkernel_int hkernel_unit

/--
Bounded-kernel zero-rate theorem from pointwise exponential-rate certificates
on near-minimizer sets.  The bounded-kernel assumptions provide the constant
upper bound and nonnegativity side of the integral argument.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseExponentialRateCertificate_nearRate_sets
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K)
    (hkernel_meas : ∀ n : ℕ, Measurable (kernel n))
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  ∀ x : α, x ∈ nearMinimizers →
                    ExponentialRateCertificate
                      (fun n : ℕ => kernel n x) (rate x)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x := by
    intro n
    filter_upwards [hweight_nonneg, hkernel_bound n] with x hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hupper_const⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_const
      μ hK_nonneg hweight_int hweight_nonneg hkernel_int hkernel_bound
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_pointwiseExponentialRateCertificate_nearRate_sets
      μ hBpos hkernel_int hkernel_nonneg hupper_const hkernel_meas
      hnear_sets

/--
Restricted-cell continuous zero-rate bridge for bounded kernels from
pointwise exponential-rate certificates.  The near-minimizer sets are built
directly from continuity of the limiting rate and positive weight at a
zero-rate point in the closure of the cell interior, so no compact-uniform
normalized-log convergence is required.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseExponentialRateCertificate_continuousAt_zero_weight_pos_restrict_closure_interior_of_cell_subset_certSet
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {K : ℝ}
    (x0 : α)
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight (μ.restrict cell))
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ,
        Integrable (fun x : α => weight x * kernel n x) (μ.restrict cell))
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ.restrict cell,
        0 ≤ kernel n x ∧ kernel n x ≤ K)
    (hkernel_meas : ∀ n : ℕ, Measurable (kernel n))
    (hcell_subset_certSet : cell ⊆ certSet)
    (hcert :
      ∀ x : α, x ∈ certSet →
        ExponentialRateCertificate (fun n : ℕ => kernel n x) (rate x))
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ.restrict cell)
      0 := by
  refine
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseExponentialRateCertificate_nearRate_sets
      (μ := μ.restrict cell) (weight := weight) (kernel := kernel)
      (rate := rate) (K := K) hK_nonneg hweight_int hweight_nonneg
      hkernel_int hkernel_bound hkernel_meas ?_
  intro targetRate htarget
  let ε : ℝ := targetRate / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  let c : ℝ := weight x0 / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hw_target : {y : ℝ | c < y} ∈ 𝓝 (weight x0) :=
    IsOpen.mem_nhds isOpen_Ioi (by dsimp [c]; linarith)
  have hrate_target : {y : ℝ | y < ε} ∈ 𝓝 (rate x0) := by
    rw [hrate_x0]
    exact IsOpen.mem_nhds isOpen_Iio hεpos
  have hw_pre : {x : α | c < weight x} ∈ 𝓝 x0 :=
    hweight_cont hw_target
  have hrate_pre : {x : α | rate x < ε} ∈ 𝓝 x0 :=
    hrate_cont hrate_target
  have hpre :
      ({x : α | c < weight x} ∩ {x : α | rate x < ε}) ∈ 𝓝 x0 :=
    Filter.inter_mem hw_pre hrate_pre
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  let nearMinimizers : Set α := cell ∩ U
  have hnear_meas : MeasurableSet nearMinimizers :=
    hcell.inter hUopen.measurableSet
  have hlocal_pos : 0 < μ (cell ∩ U) :=
    HasAEEssentialInfimum.local_pos_of_mem_closure_interior
      μ hclosure U hUopen hxU
  have hrestrict_pos : 0 < (μ.restrict cell) nearMinimizers := by
    rw [Measure.restrict_apply hnear_meas]
    have hset_eq : (cell ∩ U) ∩ cell = cell ∩ U := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.1.2⟩
      · intro hx
        exact ⟨hx, hx.1⟩
    simpa [nearMinimizers, hset_eq] using hlocal_pos
  have hnear_real_pos : 0 < (μ.restrict cell).real nearMinimizers :=
    ENNReal.toReal_pos (ne_of_gt hrestrict_pos)
      (measure_ne_top (μ.restrict cell) nearMinimizers)
  refine
    ⟨nearMinimizers, c, ε, hnear_meas, hnear_real_pos, hcpos, hεpos,
      ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hkernel_int n).integrableOn
  · exact
      ae_restrict_of_forall_mem hnear_meas (by
        intro x hx
        have hxU' : x ∈ U := hx.2
        exact le_of_lt (hUsub hxU').1)
  · intro x hx
    have hxU' : x ∈ U := hx.2
    have hrate_lt : rate x < ε := (hUsub hxU').2
    have hrate_le_half : rate x ≤ targetRate / 2 := by
      dsimp [ε] at hrate_lt
      linarith
    dsimp [ε]
    linarith
  · intro x hx
    exact hcert x (hcell_subset_certSet hx.1)

/--
Zero-rate weighted-kernel theorem for kernels bounded by a fixed nonnegative
constant.  Nonnegative integrable weights and `0 ≤ kernel ≤ K` provide the
constant upper bound and nonnegativity assumptions; the lower bound comes from
a uniform normalized-log certificate and the weighted near-essential-infimum
interface.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x := by
    intro n
    filter_upwards [hweight_nonneg, hkernel_bound n] with x hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hupper_const⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_const
      μ hK_nonneg hweight_int hweight_nonneg hkernel_int hkernel_bound
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
      μ hBpos hkernel_int hkernel_nonneg hupper_const C hcertSet_ae
      hweighted_near

/--
Bounded-kernel zero-rate theorem with product integrability derived from
kernel measurability and a uniform a.e. bound.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_meas : ∀ n : ℕ, AEStronglyMeasurable (kernel n) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      μ hweight_int hkernel_meas hkernel_bound
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
      μ hK_nonneg hweight_int hweight_nonneg hkernel_int hkernel_bound C
      hcertSet_ae hweighted_near

/--
Bounded-kernel zero-rate theorem where the uniform normalized-log certificate
is built from pointwise exact-rate certificates and an eventual Lipschitz
estimate on a compact certificate set.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseCertificates_eventually_lipschitz_on_compact_weightedNearInf_of_ae_mem_certSet
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α} {K L : ℝ}
    (hcertSet_compact : IsCompact certSet)
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K)
    (hpos :
      ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ certSet → 0 < kernel n x)
    (hcert :
      ∀ x : α, x ∈ certSet →
        ExponentialRateCertificate (fun n : ℕ => kernel n x) (rate x))
    (hrate_cont :
      ∀ x : α, x ∈ certSet → ContinuousAt rate x)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ certSet → ∀ y : α, y ∈ certSet →
          |normalizedLogKernelRate kernel n y -
            normalizedLogKernelRate kernel n x| ≤ L * dist y x)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  let C : UniformNormalizedLogRateCertificateOn kernel rate certSet :=
    UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
      hcertSet_compact (fun _ hx => hx) hpos hcert hrate_cont hL
      hlog_lipschitz
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
      μ hK_nonneg hweight_int hweight_nonneg hkernel_int hkernel_bound C
      hcertSet_ae hweighted_near

/--
Bounded-kernel version of the local-certificate zero-rate theorem.  This is
the same bridge as the probability-kernel version, but supports kernels such
as `1 - P_k` that are bounded by a fixed constant rather than by `1`.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  UniformNormalizedLogRateCertificateOn
                    kernel rate nearMinimizers) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x := by
    intro n
    filter_upwards [hweight_nonneg, hkernel_bound n] with x hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hupper_const⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_const
      μ hK_nonneg hweight_int hweight_nonneg hkernel_int hkernel_bound
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_localUniformNormalizedLogRateCertificate_nearRate_sets
      μ hBpos hkernel_int hkernel_nonneg hupper_const hnear_sets

/--
Bounded-kernel local-certificate zero-rate theorem with product integrability
derived from kernel measurability and a uniform a.e. bound.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_kernel_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_meas : ∀ n : ℕ, AEStronglyMeasurable (kernel n) μ)
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  UniformNormalizedLogRateCertificateOn
                    kernel rate nearMinimizers) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      μ hweight_int hkernel_meas hkernel_bound
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
      μ hK_nonneg hweight_int hweight_nonneg hkernel_int hkernel_bound
      hnear_sets

/--
Zero-rate weighted-kernel theorem for probability kernels.  Nonnegative
integrable weights and `0 ≤ kernel ≤ 1` provide the constant upper bound and
nonnegativity assumptions; the lower bound comes from a uniform normalized-log
certificate and the weighted near-essential-infimum interface.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α}
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ 1)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x := by
    intro n
    filter_upwards [hweight_nonneg, hkernel_unit n] with x hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hupper_const⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_one
      μ hweight_int hweight_nonneg hkernel_int hkernel_unit
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
      μ hBpos hkernel_int hkernel_nonneg hupper_const C hcertSet_ae
      hweighted_near

/--
Probability-kernel zero-rate theorem with product integrability derived from
kernel measurability and the a.e. probability bound `0 ≤ kernel ≤ 1`.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    {certSet : Set α}
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_meas : ∀ n : ℕ, AEStronglyMeasurable (kernel n) μ)
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ 1)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    (μ := μ) (K := 1) (by norm_num) hweight_int hweight_nonneg
    hkernel_meas hkernel_unit C hcertSet_ae hweighted_near

/--
Probability-kernel version of the local-certificate zero-rate theorem.  The
constant upper bound and nonnegativity side conditions are derived from
nonnegative integrable weights and `0 ≤ kernel ≤ 1`.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ, Integrable (fun x : α => weight x * kernel n x) μ)
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ 1)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  UniformNormalizedLogRateCertificateOn
                    kernel rate nearMinimizers) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 := by
  have hkernel_nonneg :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel n x := by
    intro n
    filter_upwards [hweight_nonneg, hkernel_unit n] with x hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hupper_const⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_ae_kernel_between_zero_one
      μ hweight_int hweight_nonneg hkernel_int hkernel_unit
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_localUniformNormalizedLogRateCertificate_nearRate_sets
      μ hBpos hkernel_int hkernel_nonneg hupper_const hnear_sets

/--
Probability-kernel local-certificate zero-rate theorem with product
integrability derived from kernel measurability and `0 ≤ kernel ≤ 1`.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_kernel_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    (hweight_int : Integrable weight μ)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hkernel_meas : ∀ n : ℕ, AEStronglyMeasurable (kernel n) μ)
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ, 0 ≤ kernel n x ∧ kernel n x ≤ 1)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set α, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ n : ℕ,
              IntegrableOn
                (fun x : α => weight x * kernel n x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : α, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  UniformNormalizedLogRateCertificateOn
                    kernel rate nearMinimizers) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_kernel_aestronglyMeasurable
    (μ := μ) (K := 1) (by norm_num) hweight_int hweight_nonneg
    hkernel_meas hkernel_unit hnear_sets

/--
Restricted-cell continuous zero-rate bridge for bounded kernels.  This is the
source-shaped form for continuous error-kernel integrals whose kernels are
bounded by a fixed nonnegative constant: a normalized-log certificate on an
a.e.-full cell-local set and a continuous positive-weight zero-rate minimizer
imply exact rate zero.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {K : ℝ}
    (x0 : α)
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight (μ.restrict cell))
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ,
        Integrable (fun x : α => weight x * kernel n x) (μ.restrict cell))
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ.restrict cell,
        0 ≤ kernel n x ∧ kernel n x ≤ K)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ.restrict cell, x ∈ certSet)
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ.restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    (μ.restrict cell) hK_nonneg hweight_int hweight_nonneg hkernel_int
    hkernel_bound C hcertSet_ae
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict_closure_interior
      (μ := μ) hcell x0 hrate_x0 hrate_cont hweight_cont
      hweight_x0_pos hclosure)

/--
Restricted-cell continuous zero-rate bridge for bounded kernels, with product
integrability derived from restricted-kernel measurability and the a.e. bound.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ} {K : ℝ}
    (x0 : α)
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight (μ.restrict cell))
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hkernel_meas :
      ∀ n : ℕ, AEStronglyMeasurable (kernel n) (μ.restrict cell))
    (hkernel_bound :
      ∀ n : ℕ, ∀ᵐ x ∂μ.restrict cell,
        0 ≤ kernel n x ∧ kernel n x ≤ K)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ.restrict cell, x ∈ certSet)
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ.restrict cell)
      0 := by
  have hkernel_int :
      ∀ n : ℕ,
        Integrable (fun x : α => weight x * kernel n x) (μ.restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      (μ.restrict cell) hweight_int hkernel_meas hkernel_bound
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      μ hcell x0 hK_nonneg hweight_int hweight_nonneg hkernel_int
      hkernel_bound C hcertSet_ae hrate_x0 hrate_cont hweight_cont
      hweight_x0_pos hclosure

/--
Restricted-cell continuous zero-rate bridge for probability kernels.  This is
the source-shaped form for continuous error-probability integrals: a
normalized-log certificate on an a.e.-full cell-local set, `0 ≤ kernel ≤ 1`,
and a continuous positive-weight zero-rate minimizer imply exact rate zero.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    (x0 : α)
    (hweight_int : Integrable weight (μ.restrict cell))
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hkernel_int :
      ∀ n : ℕ,
        Integrable (fun x : α => weight x * kernel n x) (μ.restrict cell))
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ.restrict cell,
        0 ≤ kernel n x ∧ kernel n x ≤ 1)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ.restrict cell, x ∈ certSet)
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ.restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    (μ.restrict cell) hweight_int hweight_nonneg hkernel_int hkernel_unit C
    hcertSet_ae
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict_closure_interior
      (μ := μ) hcell x0 hrate_x0 hrate_cont hweight_cont
      hweight_x0_pos hclosure)

/--
Restricted-cell continuous zero-rate bridge for probability kernels, with
product integrability derived from restricted-kernel measurability and
`0 ≤ kernel ≤ 1`.
-/
theorem weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell certSet : Set α} (hcell : MeasurableSet cell)
    {weight : α → ℝ} {kernel : ℕ → α → ℝ} {rate : α → ℝ}
    (x0 : α)
    (hweight_int : Integrable weight (μ.restrict cell))
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hkernel_meas :
      ∀ n : ℕ, AEStronglyMeasurable (kernel n) (μ.restrict cell))
    (hkernel_unit :
      ∀ n : ℕ, ∀ᵐ x ∂μ.restrict cell,
        0 ≤ kernel n x ∧ kernel n x ≤ 1)
    (C : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ.restrict cell, x ∈ certSet)
    (hrate_x0 : rate x0 = 0)
    (hrate_cont : ContinuousAt rate x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    HasExponentialRate
      (fun n : ℕ => ∫ x, weight x * kernel n x ∂μ.restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    (μ := μ) hcell x0 (K := 1) (by norm_num) hweight_int
    hweight_nonneg hkernel_meas hkernel_unit C hcertSet_ae hrate_x0
    hrate_cont hweight_cont hweight_x0_pos hclosure

/--
For positive kernels, `normalizedLogKernelRate` is exactly the exponent that
rewrites the kernel as `exp (-n * phi_n)` away from `n = 0`.
-/
theorem exp_neg_mul_normalizedLogKernelRate_eq_of_pos
    {α : Type*} {F : ℕ → α → ℝ} {n : ℕ} (hn : n ≠ 0) (x : α)
    (hF_pos : 0 < F n x) :
    Real.exp (-(n : ℝ) * normalizedLogKernelRate F n x) = F n x := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hlog :
      -(n : ℝ) * normalizedLogKernelRate F n x = Real.log (F n x) := by
    simp [normalizedLogKernelRate, hn]
    field_simp [hnreal]
  rw [hlog]
  exact Real.exp_log hF_pos

/--
Eventual a.e. exponential representation for a kernel whose positivity holds
eventually a.e.  This is the common bridge from a normalized-log definition
`phi_n = -log kernel_n / n` to a Laplace theorem stated for
`exp (-n * phi_n)`.
-/
theorem eventually_ae_kernel_eq_exp_neg_mul_normalizedLogKernelRate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ}
    (hF_pos : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂μ, 0 < F n x) :
    ∀ᶠ n : ℕ in atTop,
      ∀ᵐ x ∂μ,
        F n x = Real.exp (-(n : ℝ) * normalizedLogKernelRate F n x) := by
  filter_upwards [hF_pos, eventually_gt_atTop 0] with n hnpos_ae hnpos
  filter_upwards [hnpos_ae] with x hxpos
  exact (exp_neg_mul_normalizedLogKernelRate_eq_of_pos
    (F := F) (Nat.ne_of_gt hnpos) x hxpos).symm

/--
Exact exponential kernels have zero normalized-log error away from the initial
sample size.  This discharges the uniform-log hypothesis in Laplace wrappers
when the kernel is literally `exp (-n * phi x)`.
-/
theorem uniform_logRate_tendsto_of_exact_exp
    {α : Type*} (phi : α → ℝ) :
    ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α,
          |(-Real.log (Real.exp (-(n : ℝ) * phi x)) / (n : ℝ)) -
              phi x| ≤ ε := by
  intro ε hε
  filter_upwards [eventually_gt_atTop 0] with n hnpos x
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnpos
  rw [Real.log_exp]
  have hdiv : (n : ℝ) * phi x / (n : ℝ) = phi x := by
    field_simp [hn_ne]
  simpa [hdiv] using hε.le

/--
Weighted compact-Laplace skeleton for uniformly positive weights.  This is a
convenience wrapper around
`weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_weightedEssentialInf`
for the common case where the objective weight is bounded below by a positive
constant almost everywhere.
-/
theorem weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_essentialInf_uniformWeightLower
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    HasExponentialRate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_weightedEssentialInf
    μ w phiSeq phi hF_int hWpos
    (hw_lower.mono fun _x hx => le_trans hcpos.le hx)
    hw_bound hess
    (HasPositiveWeightNearAEEssentialInfimum.of_uniform_ae_lower_bound
      hess hcpos hw_lower)
    huniform

/--
Certificate form of the uniformly positive weighted compact-Laplace theorem.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_essentialInf_uniformWeightLower
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    μ w phiSeq phi hF_int hWpos
    (hw_lower.mono fun _x hx => le_trans hcpos.le hx)
    hw_bound hess
    (HasPositiveWeightNearAEEssentialInfimum.of_uniform_ae_lower_bound
      hess hcpos hw_lower)
    huniform

/--
Weighted compact-Laplace certificate for source-shaped kernels
`exp (-n * phiSeq n x)` when the limiting rate function has a continuous
global minimizer and the objective weight is uniformly positive.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_essentialInf_uniformWeightLower
    μ w phiSeq phi hF_int hWpos hcpos hw_lower hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_open_pos
      x0 hmin hx0 hcont)
    huniform

/--
Weighted compact-Laplace certificate for source-shaped kernels
`exp (-n * phiSeq n x)` when the limiting rate function has a continuous
global minimizer and the objective weight is continuous and positive at that
minimizer.  This is often the natural source assumption: the weight need not be
uniformly bounded away from zero on the whole space.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_continuous_min_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x))) μ)
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_x0_pos : 0 < w x0)
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    μ w phiSeq phi hF_int hWpos hw_nonneg hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_open_pos
      x0 hmin hx0 hphi_cont)
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_open_pos
      x0 hx0 hphi_cont hw_cont hw_x0_pos)
    huniform

/--
Restricted-cell weighted compact-Laplace certificate for source-shaped kernels
`exp (-n * phiSeq n x)`, using an explicit positive-mass condition around the
cell minimizer.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U))
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_essentialInf_uniformWeightLower
    (μ.restrict s) w phiSeq phi hF_int hWpos hcpos hw_lower hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict
      hs x0 hmin hx0 hcont hlocal_pos)
    huniform

/--
Restricted-cell weighted compact-Laplace certificate with a continuous positive
weight at the cell minimizer instead of a cell-wide positive lower bound.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U))
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    (μ.restrict s) w phiSeq phi hF_int hWpos hw_nonneg hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict
      hs x0 hmin hx0 hphi_cont hlocal_pos)
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict
      hs x0 hx0 hphi_cont hw_cont hw_pos hlocal_pos)
    huniform

/--
Restricted-cell weighted compact-Laplace certificate for source-shaped kernels
where local positive mass follows from the minimizer lying in the closure of
the cell interior.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior s))
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_essentialInf_uniformWeightLower
    (μ.restrict s) w phiSeq phi hF_int hWpos hcpos hw_lower hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict_closure_interior
      hs x0 hmin hx0 hcont hclosure)
    huniform

/--
Restricted-cell weighted compact-Laplace certificate with a continuous positive
weight at the minimizer and local mass supplied by closure/interior support.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hclosure : x0 ∈ closure (interior s))
    (huniform : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    (μ.restrict s) w phiSeq phi hF_int hWpos hw_nonneg hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict_closure_interior
      hs x0 hmin hx0 hphi_cont hclosure)
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict_closure_interior
      hs x0 hx0 hphi_cont hw_cont hw_pos hclosure)
    huniform

/--
Restricted-cell weighted compact-Laplace certificate with uniform convergence
required only on the restricted cell.  This is the natural source shape for
partitioned continuum proofs: values outside the cell do not affect the
restricted integral.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s → |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate := by
  classical
  let phiSeqOn : ℕ → α → ℝ :=
    fun n x => if x ∈ s then phiSeq n x else phi x
  have hF_int_on :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeqOn n x)))
        (μ.restrict s) := by
    intro n
    refine (hF_int n).congr ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [phiSeqOn, hx]
  have huniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ x : α, |phiSeqOn n x - phi x| ≤ ε := by
    intro ε hε
    filter_upwards [huniform_on ε hε] with n hn x
    by_cases hx : x ∈ s
    · simpa [phiSeqOn, hx] using hn x hx
    · simpa [phiSeqOn, hx] using hε.le
  have hcert :
      ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeqOn n x))
            ∂μ.restrict s)
        rate :=
    weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_uniformWeightLower
      μ hs w phiSeqOn phi hF_int_on hWpos hcpos hw_lower hw_bound
      x0 hmin hx0 hcont hlocal_pos huniform
  refine ExponentialRateCertificate.congr ?_ hcert
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [phiSeqOn, hx]

/--
Restricted-cell weighted compact-Laplace certificate with uniform convergence
required only on the restricted cell, and with a continuous positive weight at
the cell minimizer instead of a cell-wide positive lower bound.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s → |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate := by
  classical
  let phiSeqOn : ℕ → α → ℝ :=
    fun n x => if x ∈ s then phiSeq n x else phi x
  have hF_int_on :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeqOn n x)))
        (μ.restrict s) := by
    intro n
    refine (hF_int n).congr ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [phiSeqOn, hx]
  have huniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ x : α, |phiSeqOn n x - phi x| ≤ ε := by
    intro ε hε
    filter_upwards [huniform_on ε hε] with n hn x
    by_cases hx : x ∈ s
    · simpa [phiSeqOn, hx] using hn x hx
    · simpa [phiSeqOn, hx] using hε.le
  have hcert :
      ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeqOn n x))
            ∂μ.restrict s)
        rate :=
    weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_weight_pos
      μ hs w phiSeqOn phi hF_int_on hWpos hw_nonneg hw_bound
      x0 hmin hx0 hphi_cont hw_cont hw_pos hlocal_pos huniform
  refine ExponentialRateCertificate.congr ?_ hcert
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [phiSeqOn, hx]

/--
Restricted-cell weighted compact-Laplace certificate with uniform convergence
required only on the restricted cell, and with local positive mass supplied by
the minimizer lying in the closure of the cell interior.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior s))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s → |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate := by
  classical
  let phiSeqOn : ℕ → α → ℝ :=
    fun n x => if x ∈ s then phiSeq n x else phi x
  have hF_int_on :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeqOn n x)))
        (μ.restrict s) := by
    intro n
    refine (hF_int n).congr ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [phiSeqOn, hx]
  have huniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ x : α, |phiSeqOn n x - phi x| ≤ ε := by
    intro ε hε
    filter_upwards [huniform_on ε hε] with n hn x
    by_cases hx : x ∈ s
    · simpa [phiSeqOn, hx] using hn x hx
    · simpa [phiSeqOn, hx] using hε.le
  have hcert :
      ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeqOn n x))
            ∂μ.restrict s)
        rate :=
    weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_uniformWeightLower
      μ hs w phiSeqOn phi hF_int_on hWpos hcpos hw_lower hw_bound
      x0 hmin hx0 hcont hclosure huniform
  refine ExponentialRateCertificate.congr ?_ hcert
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [phiSeqOn, hx]

/--
Restricted-cell weighted compact-Laplace certificate with uniform convergence
required only on the restricted cell, with local positive mass from
closure/interior support and local positive weight at the minimizer.
-/
theorem weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phiSeq : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeq n x)))
        (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hclosure : x0 ∈ closure (interior s))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s → |phiSeq n x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeq n x)) ∂μ.restrict s)
      rate := by
  classical
  let phiSeqOn : ℕ → α → ℝ :=
    fun n x => if x ∈ s then phiSeq n x else phi x
  have hF_int_on :
      ∀ n : ℕ, Integrable
        (fun x : α => w x * Real.exp (-(n : ℝ) * (phiSeqOn n x)))
        (μ.restrict s) := by
    intro n
    refine (hF_int n).congr ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [phiSeqOn, hx]
  have huniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ x : α, |phiSeqOn n x - phi x| ≤ ε := by
    intro ε hε
    filter_upwards [huniform_on ε hε] with n hn x
    by_cases hx : x ∈ s
    · simpa [phiSeqOn, hx] using hn x hx
    · simpa [phiSeqOn, hx] using hε.le
  have hcert :
      ExponentialRateCertificate
        (fun n : ℕ =>
          ∫ x, w x * Real.exp (-(n : ℝ) * (phiSeqOn n x))
            ∂μ.restrict s)
        rate :=
    weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_weight_pos
      μ hs w phiSeqOn phi hF_int_on hWpos hw_nonneg hw_bound
      x0 hmin hx0 hphi_cont hw_cont hw_pos hclosure huniform
  refine ExponentialRateCertificate.congr ?_ hcert
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [phiSeqOn, hx]

/--
Positive-kernel compact-Laplace certificate for the common continuous-minimum
case with uniformly positive objective weights.  This removes the explicit
essential-infimum and positive-near-minimum certificates when the limiting rate
function has a global minimizer and the measure gives positive mass to every
nonempty open set.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) μ)
    (hw_int : Integrable w μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    μ w F phi hF_int hw_int hWpos
    (hw_lower.mono fun _x hx => le_trans hcpos.le hx)
    hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_open_pos
      x0 hmin hx0 hcont)
    (HasPositiveWeightNearAEEssentialInfimum.of_uniform_ae_lower_bound
      (HasAEEssentialInfimum.of_continuousAt_global_min_open_pos
        x0 hmin hx0 hcont)
      hcpos hw_lower)
    hF_pos huniform_log

/--
Positive-kernel compact-Laplace certificate for a continuous limiting rate with
a global minimizer and an objective weight that is continuous and positive at
that minimizer.  Global nonnegativity and boundedness of the weight remain
visible, while the positive-near-minimizer condition is derived locally.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) μ)
    (hw_int : Integrable w μ)
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_x0_pos : 0 < w x0)
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    μ w F phi hF_int hw_int hWpos hw_nonneg hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_open_pos
      x0 hmin hx0 hphi_cont)
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_open_pos
      x0 hx0 hphi_cont hw_cont hw_x0_pos)
    hF_pos huniform_log

/--
Restricted-cell positive-kernel compact-Laplace certificate.  The minimizer need
only lie in a cell `s`, and every open neighborhood of that minimizer must
intersect `s` in positive ambient measure.  This is the form needed when a
continuum objective is split into finitely many measurable cells.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U))
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ.restrict s)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    (μ.restrict s) w F phi hF_int hw_int hWpos
    (hw_lower.mono fun _x hx => le_trans hcpos.le hx)
    hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict
      hs x0 hmin hx0 hcont hlocal_pos)
    (HasPositiveWeightNearAEEssentialInfimum.of_uniform_ae_lower_bound
      (HasAEEssentialInfimum.of_continuousAt_global_min_restrict
        hs x0 hmin hx0 hcont hlocal_pos)
      hcpos hw_lower)
    hF_pos huniform_log

/--
Restricted-cell positive-kernel compact-Laplace certificate with a continuous
positive weight at the cell minimizer instead of a cell-wide lower bound.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U))
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ.restrict s)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    (μ.restrict s) w F phi hF_int hw_int hWpos hw_nonneg hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict
      hs x0 hmin hx0 hphi_cont hlocal_pos)
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict
      hs x0 hx0 hphi_cont hw_cont hw_pos hlocal_pos)
    hF_pos huniform_log

/--
Restricted-cell positive-kernel compact-Laplace certificate where local
positive cell mass is supplied by `x0 ∈ closure (interior s)` under an
open-positive ambient measure.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior s))
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ.restrict s)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    (μ.restrict s) w F phi hF_int hw_int hWpos
    (hw_lower.mono fun _x hx => le_trans hcpos.le hx)
    hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict_closure_interior
      hs x0 hmin hx0 hcont hclosure)
    (HasPositiveWeightNearAEEssentialInfimum.of_uniform_ae_lower_bound
      (HasAEEssentialInfimum.of_continuousAt_global_min_restrict_closure_interior
        hs x0 hmin hx0 hcont hclosure)
      hcpos hw_lower)
    hF_pos huniform_log

/--
Restricted-cell positive-kernel compact-Laplace certificate with a continuous
positive weight at the minimizer and local mass from closure/interior support.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hclosure : x0 ∈ closure (interior s))
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ.restrict s)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    (μ.restrict s) w F phi hF_int hw_int hWpos hw_nonneg hw_bound
    (HasAEEssentialInfimum.of_continuousAt_global_min_restrict_closure_interior
      hs x0 hmin hx0 hphi_cont hclosure)
    (HasPositiveWeightNearAEEssentialInfimum.of_continuousAt_pos_at_min_restrict_closure_interior
      hs x0 hx0 hphi_cont hw_cont hw_pos hclosure)
    hF_pos huniform_log

/--
Restricted-cell positive-kernel compact-Laplace certificate where the
normalized-log convergence is only required on the restricted cell.  This is
the natural generic form for integrals over a strict comparison domain:
outside the cell, the kernel is irrelevant to the restricted integral.
-/
theorem weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_on_restrict_closure_interior_weight_pos
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (F : ℕ → α → ℝ) (phi : α → ℝ)
    {rate W : ℝ}
    (hF_int :
      ∀ n : ℕ, Integrable (fun x : α => w x * F n x) (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hw_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hw_cont : ContinuousAt w x0)
    (hw_pos : 0 < w x0)
    (hclosure : x0 ∈ closure (interior s))
    (hF_pos : ∀ n x, 0 < F n x)
    (huniform_log_on : ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s →
          |(-Real.log (F n x) / (n : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun n : ℕ => ∫ x, w x * F n x ∂μ.restrict s)
      rate := by
  classical
  let Fcell : ℕ → α → ℝ := fun n x =>
    if x ∈ s then F n x else Real.exp (-(n : ℝ) * phi x)
  have hFcell_int :
      ∀ n : ℕ,
        Integrable (fun x : α => w x * Fcell n x) (μ.restrict s) := by
    intro n
    refine (hF_int n).congr ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [Fcell, hx]
  have hFcell_pos : ∀ n x, 0 < Fcell n x := by
    intro n x
    by_cases hx : x ∈ s
    · simpa [Fcell, hx] using hF_pos n x
    · simp [Fcell, hx, Real.exp_pos]
  have huniform_global :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ x : α, |(-Real.log (Fcell n x) / (n : ℝ)) - phi x| ≤ ε := by
    intro ε hε
    filter_upwards [huniform_log_on ε hε, eventually_gt_atTop 0] with
      n hn_uniform hn_pos x
    by_cases hx : x ∈ s
    · simpa [Fcell, hx] using hn_uniform x hx
    · have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hn_pos
      have hraw :
          -Real.log (Fcell n x) / (n : ℝ) = phi x := by
        simp [Fcell, hx, Real.log_exp]
        field_simp [hn_ne]
      simpa [hraw] using hε.le
  have hcert_cell :
      ExponentialRateCertificate
        (fun n : ℕ => ∫ x, w x * Fcell n x ∂μ.restrict s)
        rate :=
    weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
      μ hs w Fcell phi hFcell_int hw_int hWpos hw_nonneg hw_bound
      x0 hmin hx0 hphi_cont hw_cont hw_pos hclosure hFcell_pos
      huniform_global
  refine ExponentialRateCertificate.congr ?_ hcert_cell
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [Fcell, hx]

/--
Exact-exponential compact-Laplace certificate for the common continuous-minimum
case with uniformly positive objective weights.  This is the specialization of
the positive-kernel wrapper to kernels of the form `exp (-n * phi x)`.
-/
theorem weightedExactExponentialIntegral_exponentialRateCertificate_of_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (w : α → ℝ) (phi : α → ℝ) {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp (-(n : ℝ) * phi x)) μ)
    (hw_int : Integrable w μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * phi x) ∂μ)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_uniformWeightLower
    μ w (fun n x => Real.exp (-(n : ℝ) * phi x)) phi hF_int hw_int
    hWpos hcpos hw_lower hw_bound x0 hmin hx0 hcont
    (fun _n _x => Real.exp_pos _)
    (uniform_logRate_tendsto_of_exact_exp phi)

/--
Restricted-cell exact-exponential compact-Laplace certificate.  This is the
cell-local specialization for kernels `exp (-n * phi x)`.
-/
theorem weightedExactExponentialIntegral_exponentialRateCertificate_of_restrict_continuous_min_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phi : α → ℝ) {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp (-(n : ℝ) * phi x))
          (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos : ∀ U : Set α, IsOpen U → x0 ∈ U → 0 < μ (s ∩ U)) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * phi x) ∂μ.restrict s)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_uniformWeightLower
    μ hs w (fun n x => Real.exp (-(n : ℝ) * phi x)) phi hF_int hw_int
    hWpos hcpos hw_lower hw_bound x0 hmin hx0 hcont hlocal_pos
    (fun _n _x => Real.exp_pos _)
    (uniform_logRate_tendsto_of_exact_exp phi)

/--
Restricted-cell exact-exponential compact-Laplace certificate where the local
positive-mass condition follows from closure/interior support.
-/
theorem weightedExactExponentialIntegral_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (phi : α → ℝ) {rate W c : ℝ}
    (hF_int :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp (-(n : ℝ) * phi x))
          (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmin : ∀ x : α, x ∈ s → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior s)) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp (-(n : ℝ) * phi x) ∂μ.restrict s)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_uniformWeightLower
    μ hs w (fun n x => Real.exp (-(n : ℝ) * phi x)) phi hF_int hw_int
    hWpos hcpos hw_lower hw_bound x0 hmin hx0 hcont hclosure
    (fun _n _x => Real.exp_pos _)
    (uniform_logRate_tendsto_of_exact_exp phi)

/--
Exact positive-exponential compact-Laplace certificate.  This is the
supremum-form wrapper for kernels `exp (n * rho x)`, obtained from the
standard infimum-form theorem by setting `phi = -rho`.
-/
theorem weightedExactPositiveExponentialIntegral_exponentialRateCertificate_of_continuous_max_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (w : α → ℝ) (rho : α → ℝ) {supValue W c : ℝ}
    (hF_int :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp ((n : ℝ) * rho x)) μ)
    (hw_int : Integrable w μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ, w x ≤ W)
    (x0 : α)
    (hmax : ∀ x : α, rho x ≤ supValue)
    (hx0 : rho x0 = supValue)
    (hcont : ContinuousAt rho x0) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp ((n : ℝ) * rho x) ∂μ)
      (-supValue) := by
  let phi : α → ℝ := fun x => -rho x
  have hF_int_phi :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp (-(n : ℝ) * phi x)) μ := by
    intro n
    simpa [phi] using hF_int n
  have hmin_phi : ∀ x : α, -supValue ≤ phi x := by
    intro x
    dsimp [phi]
    linarith [hmax x]
  have hx0_phi : phi x0 = -supValue := by
    dsimp [phi]
    linarith
  have hcont_phi : ContinuousAt phi x0 := hcont.neg
  have hcert :=
    weightedExactExponentialIntegral_exponentialRateCertificate_of_continuous_min_uniformWeightLower
      μ w phi hF_int_phi hw_int hWpos hcpos hw_lower hw_bound x0
      hmin_phi hx0_phi hcont_phi
  simpa [phi] using hcert

/--
Restricted-cell exact positive-exponential compact-Laplace certificate.  This
is the supremum-form wrapper for kernels `exp (n * rho x)`, obtained from the
standard infimum-form theorem by setting `phi = -rho`.  It is tailored to
source statements that define objectives by maximizing a payoff `rho`.
-/
theorem weightedExactPositiveExponentialIntegral_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {s : Set α} (hs : MeasurableSet s)
    (w : α → ℝ) (rho : α → ℝ) {supValue W c : ℝ}
    (hF_int :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp ((n : ℝ) * rho x))
          (μ.restrict s))
    (hw_int : Integrable w (μ.restrict s))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hw_lower : ∀ᵐ x ∂μ.restrict s, c ≤ w x)
    (hw_bound : ∀ᵐ x ∂μ.restrict s, w x ≤ W)
    (x0 : α)
    (hmax : ∀ x : α, x ∈ s → rho x ≤ supValue)
    (hx0 : rho x0 = supValue)
    (hcont : ContinuousAt rho x0)
    (hclosure : x0 ∈ closure (interior s)) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∫ x, w x * Real.exp ((n : ℝ) * rho x) ∂μ.restrict s)
      (-supValue) := by
  let phi : α → ℝ := fun x => -rho x
  have hF_int_phi :
      ∀ n : ℕ,
        Integrable
          (fun x : α => w x * Real.exp (-(n : ℝ) * phi x))
          (μ.restrict s) := by
    intro n
    simpa [phi] using hF_int n
  have hmin_phi : ∀ x : α, x ∈ s → -supValue ≤ phi x := by
    intro x hx
    dsimp [phi]
    linarith [hmax x hx]
  have hx0_phi : phi x0 = -supValue := by
    dsimp [phi]
    linarith
  have hcont_phi : ContinuousAt phi x0 := hcont.neg
  have hcert :=
    weightedExactExponentialIntegral_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
      μ hs w phi hF_int_phi hw_int hWpos hcpos hw_lower hw_bound x0
      hmin_phi hx0_phi hcont_phi hclosure
  simpa [phi] using hcert

end

end Probability
end AppliedModelingLib

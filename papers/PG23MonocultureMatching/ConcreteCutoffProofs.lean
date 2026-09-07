import PG23MonocultureMatching.ConcreteModel
import AppliedModelingLib.Foundations.Probability.RealDistribution
import Mathlib.Tactic

/-!
# PG23 Concrete Cutoff Proofs

This module continues the literal continuum construction in `ConcreteModel`.
It proves the scalar clearing facts used in the paper's Equal Cutoffs Lemma
from measure and support semantics rather than accepting a strict-demand or
cutoff-uniqueness package.

Source anchors: `source_tex/model.tex:1-20,22-44,48-75` and
`source_tex/proofs.tex:5-35,38-52,58-133`.
-/

namespace PG23MonocultureMatching

open Filter MeasureTheory Set
open scoped Topology
open AL16SupplyDemandMatching
open AppliedModelingLib.Matching

universe v

variable {College : Type v} [Fintype College] [Nonempty College]

/-- Support of a continuous pushforward is the closure of the source-support image. -/
private theorem support_map_eq_closure_image_support
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [HereditarilyLindelofSpace α]
    (μ : Measure α) (f : α -> β) (hf : Continuous f) :
    (Measure.map f μ).support = closure (f '' μ.support) := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_closure
    rw [mem_ae_map_iff hf.measurable.aemeasurable isClosed_closure.measurableSet]
    filter_upwards [Measure.support_mem_ae (μ := μ)] with x hx
    exact subset_closure ⟨x, hx, rfl⟩
  · apply closure_minimal
    · rintro _ ⟨x, hx, rfl⟩
      rw [Measure.support_eq_forall_isOpen]
      intro U hfxU hU
      rw [Measure.map_apply hf.measurable hU.measurableSet]
      exact (Measure.mem_support_iff_forall x).mp hx (f ⁻¹' U)
        (hf.continuousAt (hU.mem_nhds hfxU))
    · exact Measure.isClosed_support

/-- The support of a product measure is the product of the factor supports. -/
private theorem support_prod_eq_prod_support
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [OpensMeasurableSpace (α × β)]
    [HereditarilyLindelofSpace α] [HereditarilyLindelofSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    (μ.prod ν).support = μ.support ×ˢ ν.support := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed
      (Measure.isClosed_support.prod Measure.isClosed_support)
    change ∀ᵐ z ∂μ.prod ν, z ∈ μ.support ×ˢ ν.support
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (Measure.isClosed_support.prod Measure.isClosed_support).measurableSet]
    filter_upwards [Measure.support_mem_ae (μ := μ)] with x hx
    filter_upwards [Measure.support_mem_ae (μ := ν)] with y hy
    exact ⟨hx, hy⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U hxyU hU
    rcases mem_nhds_prod_iff'.mp (hU.mem_nhds hxyU) with
      ⟨V, W, hV, hxV, hW, hyW, hVW⟩
    have hμV : 0 < μ V :=
      (Measure.mem_support_iff_forall x).mp hx V (hV.mem_nhds hxV)
    have hνW : 0 < ν W :=
      (Measure.mem_support_iff_forall y).mp hy W (hW.mem_nhds hyW)
    have hprod : 0 < μ.prod ν (V ×ˢ W) := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos hμV.ne' hνW.ne'
    exact lt_of_lt_of_le hprod (measure_mono hVW)

/-- Independent pairing preserves connectedness of measure supports. -/
private theorem isPreconnected_support_prod
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [OpensMeasurableSpace (α × β)]
    [HereditarilyLindelofSpace α] [HereditarilyLindelofSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (hμ : IsPreconnected μ.support) (hν : IsPreconnected ν.support) :
    IsPreconnected (μ.prod ν).support := by
  rw [support_prod_eq_prod_support μ ν]
  exact hμ.prod hν

/-- The sum of two independent laws with connected supports has connected support. -/
private theorem isPreconnected_support_map_add
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (hμ : IsPreconnected μ.support) (hν : IsPreconnected ν.support) :
    IsPreconnected
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (μ.prod ν)).support := by
  have hadd : Continuous (fun z : ℝ × ℝ => z.1 + z.2) :=
    continuous_fst.add continuous_snd
  rw [support_map_eq_closure_image_support (μ.prod ν) _ hadd]
  exact ((isPreconnected_support_prod μ ν hμ hν).image _ hadd.continuousOn).closure

/--
For the primitive sum law, summing one value-support point and one
noise-support point gives a point in the pushforward support.
-/
theorem pg23_sumLaw_mem_support_of_mem_support
    (valueLaw noiseLaw : Measure ℝ) [SFinite valueLaw] [SFinite noiseLaw]
    {v x : ℝ} (hv : v ∈ valueLaw.support) (hx : x ∈ noiseLaw.support) :
    v + x ∈
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod noiseLaw)).support := by
  have hadd : Continuous (fun z : ℝ × ℝ => z.1 + z.2) :=
    continuous_fst.add continuous_snd
  rw [support_map_eq_closure_image_support (valueLaw.prod noiseLaw) _ hadd]
  rw [support_prod_eq_prod_support valueLaw noiseLaw]
  exact subset_closure ⟨(v, x), ⟨hv, hx⟩, rfl⟩

/--
Every open neighborhood of a support point of the primitive sum law contains
the sum of a value-support point and a noise-support point.
-/
theorem pg23_sumLaw_support_open_meets_support_sum
    (valueLaw noiseLaw : Measure ℝ) [SFinite valueLaw] [SFinite noiseLaw]
    {y : ℝ} {U : Set ℝ}
    (hy :
      y ∈
        (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
          (valueLaw.prod noiseLaw)).support)
    (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ v ∈ valueLaw.support, ∃ x ∈ noiseLaw.support, v + x ∈ U := by
  have hadd : Continuous (fun z : ℝ × ℝ => z.1 + z.2) :=
    continuous_fst.add continuous_snd
  rw [support_map_eq_closure_image_support (valueLaw.prod noiseLaw) _ hadd] at hy
  rcases mem_closure_iff.1 hy U hU hyU with ⟨z, hzU, hzsum⟩
  rcases hzsum with ⟨w, hw, rfl⟩
  rw [support_prod_eq_prod_support valueLaw noiseLaw] at hw
  exact ⟨w.1, hw.1, w.2, hw.2, hzU⟩

/-- Public PG23-local wrapper for connectedness of independent primitive sums. -/
theorem pg23_isPreconnected_support_map_add
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (hμ : IsPreconnected μ.support) (hν : IsPreconnected ν.support) :
    IsPreconnected
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (μ.prod ν)).support :=
  isPreconnected_support_map_add μ ν hμ hν

/-- The highest literal estimated score an applicant receives across colleges. -/
noncomputable def pg23SourceMaxScore (theta : PG23ApplicantType College) : ℝ :=
  (Finset.univ : Finset College).sup' Finset.univ_nonempty
    (fun c => pg23SourceScore theta c)

/-- The largest coordinate in the iid polyculture noise vector. -/
noncomputable def pg23PolycultureMaxNoise (noise : College -> ℝ) : ℝ :=
  (Finset.univ : Finset College).sup' Finset.univ_nonempty noise

/-- A finite coordinate maximum is continuous in the product topology. -/
theorem pg23PolycultureMaxNoise_continuous :
    Continuous (pg23PolycultureMaxNoise (College := College)) := by
  unfold pg23PolycultureMaxNoise
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun c _ => by fun_prop

/-- A finite coordinate maximum is measurable. -/
theorem pg23PolycultureMaxNoise_measurable :
    Measurable (pg23PolycultureMaxNoise (College := College)) :=
  pg23PolycultureMaxNoise_continuous.measurable

/-- The induced distribution of the largest iid polyculture noise draw. -/
noncomputable def pg23PolycultureMaxNoiseLaw (noiseLaw : Measure ℝ) : Measure ℝ :=
  Measure.map pg23PolycultureMaxNoise (Measure.pi fun _ : College => noiseLaw)

/-- The largest iid noise draw has a probability law. -/
theorem pg23PolycultureMaxNoiseLaw_isProbabilityMeasure
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] :
    IsProbabilityMeasure (pg23PolycultureMaxNoiseLaw (College := College) noiseLaw) := by
  unfold pg23PolycultureMaxNoiseLaw
  exact Measure.isProbabilityMeasure_map
    pg23PolycultureMaxNoise_measurable.aemeasurable

/-- With finitely many iid coordinates, the maximum-noise law has the original support. -/
theorem pg23PolycultureMaxNoiseLaw_support
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] :
    (pg23PolycultureMaxNoiseLaw (College := College) noiseLaw).support =
      noiseLaw.support := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed Measure.isClosed_support
    unfold pg23PolycultureMaxNoiseLaw
    rw [mem_ae_map_iff pg23PolycultureMaxNoise_measurable.aemeasurable
      Measure.isClosed_support.measurableSet]
    have hall : ∀ᵐ noise ∂Measure.pi (fun _ : College => noiseLaw),
        ∀ c : College, noise c ∈ noiseLaw.support := by
      rw [ae_all_iff]
      intro c
      exact Measure.tendsto_eval_ae_ae.eventually
        (Measure.support_mem_ae (μ := noiseLaw))
    filter_upwards [hall] with noise hnoise
    rcases Finset.exists_mem_eq_sup' Finset.univ_nonempty noise with ⟨c, _, hc⟩
    change pg23PolycultureMaxNoise noise ∈ noiseLaw.support
    simpa only [pg23PolycultureMaxNoise, hc] using hnoise c
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    unfold pg23PolycultureMaxNoiseLaw
    rw [Measure.map_apply pg23PolycultureMaxNoise_measurable hU.measurableSet]
    rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hxU) with
      ⟨ε, hε, hballU⟩
    have hnoiseBall : 0 < noiseLaw (Metric.ball x ε) :=
      (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hε)
    have hpiBall : 0 < Measure.pi (fun _ : College => noiseLaw)
        (Set.univ.pi fun _ : College => Metric.ball x ε) := by
      rw [Measure.pi_pi]
      exact bot_lt_iff_ne_bot.mpr <|
        Finset.prod_ne_zero_iff.mpr fun _ _ => hnoiseBall.ne'
    apply lt_of_lt_of_le hpiBall
    apply measure_mono
    intro noise hnoise
    change pg23PolycultureMaxNoise noise ∈ U
    rcases Finset.exists_mem_eq_sup' Finset.univ_nonempty noise with ⟨c, _, hc⟩
    apply hballU
    simpa only [pg23PolycultureMaxNoise, hc] using hnoise c (Set.mem_univ c)

/-- The largest coordinate in a fixed nonempty active set of iid polyculture noise draws. -/
noncomputable def pg23PolycultureActiveMaxNoise
    (active : Finset College) (hactive : active.Nonempty)
    (noise : College -> ℝ) : ℝ :=
  active.sup' hactive noise

/-- A finite active-set coordinate maximum is continuous in the product topology. -/
theorem pg23PolycultureActiveMaxNoise_continuous
    (active : Finset College) (hactive : active.Nonempty) :
    Continuous (pg23PolycultureActiveMaxNoise active hactive) := by
  unfold pg23PolycultureActiveMaxNoise
  exact Continuous.finset_sup'_apply hactive fun c _ => by fun_prop

/-- A finite active-set coordinate maximum is measurable. -/
theorem pg23PolycultureActiveMaxNoise_measurable
    (active : Finset College) (hactive : active.Nonempty) :
    Measurable (pg23PolycultureActiveMaxNoise active hactive) :=
  (pg23PolycultureActiveMaxNoise_continuous active hactive).measurable

/-- The induced distribution of the largest iid noise draw in a fixed active set. -/
noncomputable def pg23PolycultureActiveMaxNoiseLaw
    (noiseLaw : Measure ℝ) (active : Finset College) (hactive : active.Nonempty) :
    Measure ℝ :=
  Measure.map (pg23PolycultureActiveMaxNoise active hactive)
    (Measure.pi fun _ : College => noiseLaw)

/-- The largest active iid noise draw has a probability law. -/
theorem pg23PolycultureActiveMaxNoiseLaw_isProbabilityMeasure
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset College) (hactive : active.Nonempty) :
    IsProbabilityMeasure
      (pg23PolycultureActiveMaxNoiseLaw noiseLaw active hactive) := by
  unfold pg23PolycultureActiveMaxNoiseLaw
  exact Measure.isProbabilityMeasure_map
    (pg23PolycultureActiveMaxNoise_measurable active hactive).aemeasurable

/--
With a fixed nonempty active set of iid coordinates, the active maximum-noise
law has the original one-dimensional support.
-/
theorem pg23PolycultureActiveMaxNoiseLaw_support
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset College) (hactive : active.Nonempty) :
    (pg23PolycultureActiveMaxNoiseLaw noiseLaw active hactive).support =
      noiseLaw.support := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed Measure.isClosed_support
    unfold pg23PolycultureActiveMaxNoiseLaw
    rw [mem_ae_map_iff
      (pg23PolycultureActiveMaxNoise_measurable active hactive).aemeasurable
      Measure.isClosed_support.measurableSet]
    have hall : ∀ᵐ noise ∂Measure.pi (fun _ : College => noiseLaw),
        ∀ c : College, noise c ∈ noiseLaw.support := by
      rw [ae_all_iff]
      intro c
      exact Measure.tendsto_eval_ae_ae.eventually
        (Measure.support_mem_ae (μ := noiseLaw))
    filter_upwards [hall] with noise hnoise
    rcases Finset.exists_mem_eq_sup' hactive noise with ⟨c, hc, hc_eq⟩
    change pg23PolycultureActiveMaxNoise active hactive noise ∈ noiseLaw.support
    simpa [pg23PolycultureActiveMaxNoise, hc_eq] using hnoise c
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    unfold pg23PolycultureActiveMaxNoiseLaw
    rw [Measure.map_apply
      (pg23PolycultureActiveMaxNoise_measurable active hactive) hU.measurableSet]
    rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hxU) with
      ⟨ε, hε, hballU⟩
    have hnoiseBall : 0 < noiseLaw (Metric.ball x ε) :=
      (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hε)
    have hpiBall : 0 < Measure.pi (fun _ : College => noiseLaw)
        (Set.univ.pi fun _ : College => Metric.ball x ε) := by
      rw [Measure.pi_pi]
      exact bot_lt_iff_ne_bot.mpr <|
        Finset.prod_ne_zero_iff.mpr fun _ _ => hnoiseBall.ne'
    apply lt_of_lt_of_le hpiBall
    apply measure_mono
    intro noise hnoise
    change pg23PolycultureActiveMaxNoise active hactive noise ∈ U
    rcases Finset.exists_mem_eq_sup' hactive noise with ⟨c, _hc, hc_eq⟩
    apply hballU
    simpa [pg23PolycultureActiveMaxNoise, hc_eq] using hnoise c (Set.mem_univ c)

/--
Connected primitive value and noise supports make the score
`value + max_{c in active} noise_c` connected for every fixed nonempty active
application set.
-/
theorem pg23PolycultureActiveMaxScoreLaw_connectedSupport
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (active : Finset College) (hactive : active.Nonempty) :
    IsPreconnected
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod
          (pg23PolycultureActiveMaxNoiseLaw noiseLaw active hactive))).support := by
  letI : IsProbabilityMeasure
      (pg23PolycultureActiveMaxNoiseLaw noiseLaw active hactive) :=
    pg23PolycultureActiveMaxNoiseLaw_isProbabilityMeasure noiseLaw active hactive
  apply isPreconnected_support_map_add valueLaw
    (pg23PolycultureActiveMaxNoiseLaw noiseLaw active hactive) hvalue
  rw [pg23PolycultureActiveMaxNoiseLaw_support]
  exact hnoise

/-- The finite maximum of the literal score coordinates is measurable. -/
theorem pg23SourceMaxScore_measurable :
    Measurable (pg23SourceMaxScore (College := College)) := by
  unfold pg23SourceMaxScore
  have hmeas : Measurable
      ((Finset.univ : Finset College).sup' Finset.univ_nonempty
        (fun c => fun theta : PG23ApplicantType College => theta.2 c)) :=
    Finset.measurable_sup' Finset.univ_nonempty (fun c _ => by fun_prop)
  convert hmeas using 1
  funext theta
  simp only [Finset.sup'_apply, pg23SourceScore]

/-- In monoculture the literal maximum score is the common score `v + X`. -/
@[simp]
theorem pg23SourceMaxScore_monoculture
    (value noise : ℝ) (ranking : PG23Ranking College) :
    pg23SourceMaxScore (pg23MonocultureType value noise ranking) = value + noise := by
  unfold pg23SourceMaxScore
  exact Finset.sup'_const (s := Finset.univ) Finset.univ_nonempty (value + noise)

/-- In polyculture the literal maximum score is `v + max_c X_c`. -/
@[simp]
theorem pg23SourceMaxScore_polyculture
    (value : ℝ) (ranking : PG23Ranking College) (noise : College -> ℝ) :
    pg23SourceMaxScore (pg23PolycultureType value ranking noise) =
      value + pg23PolycultureMaxNoise noise := by
  unfold pg23SourceMaxScore pg23PolycultureMaxNoise
  exact (Finset.add_sup' Finset.univ noise value Finset.univ_nonempty).symm

/-- The distribution of the highest estimated score in a literal type law. -/
noncomputable def pg23SourceMaxScoreLaw
    (typeLaw : Measure (PG23ApplicantType College)) : Measure ℝ :=
  Measure.map pg23SourceMaxScore typeLaw

/-- The monoculture maximum-score law is the law of the primitive sum `v + X`. -/
theorem pg23MonocultureSourceMaxScoreLaw_eq_sumLaw
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    pg23SourceMaxScoreLaw
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) =
      Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (valueLaw.prod noiseLaw) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  have hdrop : MeasurePreserving
      (Prod.map Prod.fst id)
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw)
      (valueLaw.prod noiseLaw) := by
    simpa using (MeasureTheory.measurePreserving_fst (μ := valueLaw)
      (ν := pg23UniformRankingLaw (College := College))).prod
        (MeasurePreserving.id noiseLaw)
  unfold pg23SourceMaxScoreLaw pg23MonocultureTypeLaw
  rw [Measure.map_map pg23SourceMaxScore_measurable
    pg23MonocultureSampleToType_measurable]
  rw [← hdrop.map_eq]
  rw [Measure.map_map (by fun_prop :
    Measurable (fun z : ℝ × ℝ => z.1 + z.2)) hdrop.measurable]
  apply Measure.map_congr
  filter_upwards [] with sample
  simp [pg23MonocultureSampleToType]

/-- The polyculture maximum-score law is the law of `v + max_c X_c`. -/
theorem pg23PolycultureSourceMaxScoreLaw_eq_sumMaxNoiseLaw
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    pg23SourceMaxScoreLaw
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) =
      Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod (pg23PolycultureMaxNoiseLaw (College := College) noiseLaw)) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  let iidNoiseLaw : Measure (College -> ℝ) := Measure.pi fun _ : College => noiseLaw
  have hdrop : MeasurePreserving
      (Prod.map Prod.fst id)
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod iidNoiseLaw)
      (valueLaw.prod iidNoiseLaw) := by
    simpa using (MeasureTheory.measurePreserving_fst (μ := valueLaw)
      (ν := pg23UniformRankingLaw (College := College))).prod
        (MeasurePreserving.id iidNoiseLaw)
  have hmax : MeasurePreserving
      (pg23PolycultureMaxNoise (College := College)) iidNoiseLaw
      (pg23PolycultureMaxNoiseLaw (College := College) noiseLaw) := by
    exact ⟨pg23PolycultureMaxNoise_measurable, rfl⟩
  have hproject := ((MeasurePreserving.id valueLaw).prod hmax).comp hdrop
  unfold pg23SourceMaxScoreLaw pg23PolycultureTypeLaw
  change Measure.map pg23SourceMaxScore
      (Measure.map pg23PolycultureSampleToType
        ((valueLaw.prod pg23UniformRankingLaw).prod iidNoiseLaw)) = _
  rw [Measure.map_map pg23SourceMaxScore_measurable
    pg23PolycultureSampleToType_measurable]
  rw [← hproject.map_eq]
  rw [Measure.map_map (by fun_prop :
    Measurable (fun z : ℝ × ℝ => z.1 + z.2)) hproject.measurable]
  apply Measure.map_congr
  filter_upwards [] with sample
  simp [pg23PolycultureSampleToType, Function.comp_def]

/-- Source connected-support primitives imply connected monoculture maximum scores. -/
theorem pg23MonocultureSourceMaxScoreLaw_connectedSupport
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw) :
    IsPreconnected
      (pg23SourceMaxScoreLaw
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)).support := by
  rw [pg23MonocultureSourceMaxScoreLaw_eq_sumLaw]
  exact isPreconnected_support_map_add valueLaw noiseLaw hvalue hnoise

/-- Source connected-support primitives imply connected polyculture maximum scores. -/
theorem pg23PolycultureSourceMaxScoreLaw_connectedSupport
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw) :
    IsPreconnected
      (pg23SourceMaxScoreLaw
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)).support := by
  letI : IsProbabilityMeasure
      (pg23PolycultureMaxNoiseLaw (College := College) noiseLaw) :=
    pg23PolycultureMaxNoiseLaw_isProbabilityMeasure noiseLaw
  rw [pg23PolycultureSourceMaxScoreLaw_eq_sumMaxNoiseLaw]
  apply isPreconnected_support_map_add valueLaw
    (pg23PolycultureMaxNoiseLaw (College := College) noiseLaw) hvalue
  rw [pg23PolycultureMaxNoiseLaw_support]
  exact hnoise

/-- Taking the highest-score marginal preserves total probability. -/
theorem pg23SourceMaxScoreLaw_isProbabilityMeasure
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw] :
    IsProbabilityMeasure (pg23SourceMaxScoreLaw typeLaw) := by
  unfold pg23SourceMaxScoreLaw
  exact Measure.isProbabilityMeasure_map
    pg23SourceMaxScore_measurable.aemeasurable

/-- A common raw cutoff is affordable somewhere exactly when it is at most the maximum score. -/
theorem pg23CommonCutoff_affordable_iff_maxScore
    (p : ℝ) (theta : PG23ApplicantType College) :
    (∃ c : College, pg23Affordable (fun _ : College => p) theta c) ↔
      p ≤ pg23SourceMaxScore theta := by
  simp only [pg23Affordable, pg23SourceMaxScore, Finset.le_sup'_iff,
    Finset.mem_univ, true_and]

/-- A common-cutoff applicant is matched exactly on the weak maximum-score tail. -/
theorem pg23CommonCutoff_matched_iff_maxScore
    (p : ℝ) (theta : PG23ApplicantType College) :
    (∃ c : College,
      pg23SourceChoice (fun _ : College => p) theta = some c) ↔
      p ≤ pg23SourceMaxScore theta := by
  rw [pg23SourceChoice_some_iff, pg23CommonCutoff_affordable_iff_maxScore]

/-- The induced maximum-score tail is the literal type-law mass of matched applicants. -/
theorem pg23SourceMaxScoreLaw_weakTail_eq_matchedMass
    (typeLaw : Measure (PG23ApplicantType College)) (p : ℝ) :
    (pg23SourceMaxScoreLaw typeLaw).real (Ici p) =
      typeLaw.real {theta | ∃ c : College,
        pg23SourceChoice (fun _ : College => p) theta = some c} := by
  unfold pg23SourceMaxScoreLaw
  rw [map_measureReal_apply pg23SourceMaxScore_measurable]
  · congr 1
    ext theta
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq]
    exact (pg23CommonCutoff_matched_iff_maxScore p theta).symm
  · exact measurableSet_Ici

/-- Literal aggregate demand summed over colleges is the mass of matched applicants. -/
theorem pg23SourceAggregateDemand_sum_eq_matchedMass
    (typeLaw : Measure (PG23ApplicantType College)) [IsFiniteMeasure typeLaw]
    (p : ℝ) :
    (∑ c : College,
      pg23SourceAggregateDemand typeLaw (fun _ : College => p) c) =
      typeLaw.real {theta | ∃ c : College,
        pg23SourceChoice (fun _ : College => p) theta = some c} := by
  classical
  let choice : PG23ApplicantType College -> Option College :=
    pg23SourceChoice (fun _ : College => p)
  have hsum := MeasureTheory.sum_measureReal_preimage_singleton
    (μ := typeLaw) ((Finset.univ : Finset College).image some)
    (f := choice) (fun o _ => by
      simpa [choice] using
        (pg23SourceChoice_fiber_measurable (College := College)
          (fun _ : College => p) o))
  calc
    (∑ c : College,
        pg23SourceAggregateDemand typeLaw (fun _ : College => p) c) =
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
          pg23SourceChoice (fun _ : College => p) theta = some c} := by
      congr 1
      ext theta
      simp [choice, eq_comm]

/-- Exact equal-capacity clearing at a common cutoff is its maximum-score tail equation. -/
theorem pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
    (typeLaw : Measure (PG23ApplicantType College)) [IsFiniteMeasure typeLaw]
    {s p : ℝ}
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand typeLaw)
      (fun _ : College => s / (Fintype.card College : ℝ))
      (fun _ : College => p)) :
    (pg23SourceMaxScoreLaw typeLaw).real (Ici p) = s := by
  rw [pg23SourceMaxScoreLaw_weakTail_eq_matchedMass]
  rw [← pg23SourceAggregateDemand_sum_eq_matchedMass]
  calc
    (∑ c : College,
        pg23SourceAggregateDemand typeLaw (fun _ : College => p) c) =
        ∑ _c : College, s / (Fintype.card College : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _
      exact hclear c
    _ = s := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card College : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- Values for which the shifted common cutoff lies inside the noise support. -/
def pg23NoiseInteriorCutoffRegion (noiseLaw : Measure ℝ) (p : ℝ) : Set ℝ :=
  {v | p - v ∈ interior noiseLaw.support}

private theorem mem_interior_of_between_mem_preconnected
    {s : Set ℝ} (hs : IsPreconnected s)
    {x z y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxz : x < z) (hzy : z < y) :
    z ∈ interior s := by
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Ioo_mem_nhds hxz hzy)
  intro w hw
  exact hs.Icc_subset hx hy ⟨hw.1.le, hw.2.le⟩

/--
Connected support makes the lower CDF strictly increasing on the support
interior.  This is the support-safe content of `proofs.tex:9-24`; it avoids
the printed endpoint equalities, which are false in the presence of endpoint
atoms.
-/
theorem pg23_lowerCDFMass_strictMonoOn_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : pg23ConnectedSupport law) :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass law) (interior law.support) := by
  intro x hx y hy hxy
  let mid : ℝ := (x + y) / 2
  have hx_mid : x < mid := by
    dsimp [mid]
    linarith
  have hmid_y : mid < y := by
    dsimp [mid]
    linarith
  have hmid_support : mid ∈ law.support :=
    hconnected.Icc_subset (interior_subset hx) (interior_subset hy)
      ⟨hx_mid.le, hmid_y.le⟩
  have hIoo_pos : 0 < law (Ioo x y) :=
    (Measure.mem_support_iff_forall mid).mp hmid_support
      (Ioo x y) (Ioo_mem_nhds hx_mid hmid_y)
  have hIoc_pos : 0 < law (Ioc x y) :=
    lt_of_lt_of_le hIoo_pos (measure_mono Ioo_subset_Ioc_self)
  have hIoc_real_pos : 0 < AppliedModelingLib.Probability.intervalOCMass law x y := by
    exact ENNReal.toReal_pos hIoc_pos.ne' (measure_ne_top law _)
  have hdiff :
      AppliedModelingLib.Probability.intervalOCMass law x y =
        AppliedModelingLib.Probability.lowerCDFMass law y -
          AppliedModelingLib.Probability.lowerCDFMass law x := by
    rw [AppliedModelingLib.Probability.intervalOCMass_eq_cdf_sub law hxy.le,
      ← AppliedModelingLib.Probability.lowerCDFMass_eq_cdf law y,
      ← AppliedModelingLib.Probability.lowerCDFMass_eq_cdf law x]
  linarith

/--
At every interior support point of a connected-support probability law, the
lower CDF is strictly between zero and one.
-/
theorem pg23_lowerCDFMass_mem_Ioo_of_mem_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : pg23ConnectedSupport law)
    {x : ℝ} (hx : x ∈ interior law.support) :
    AppliedModelingLib.Probability.lowerCDFMass law x ∈ Ioo (0 : ℝ) 1 := by
  have hstrict := pg23_lowerCDFMass_strictMonoOn_interior_support law hconnected
  have hnhds : interior law.support ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  let left : ℝ := x - δ / 2
  have hleft_ball : left ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [left]
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hleft : left ∈ interior law.support := hball hleft_ball
  have hleft_lt : left < x := by
    dsimp [left]
    linarith
  let right : ℝ := x + δ / 2
  have hright_ball : right ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [right]
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hright : right ∈ interior law.support := hball hright_ball
  have hx_right : x < right := by
    dsimp [right]
    linarith
  constructor
  · exact lt_of_le_of_lt
      (AppliedModelingLib.Probability.lowerCDFMass_nonneg law left)
      (hstrict hleft hx hleft_lt)
  · exact lt_of_lt_of_le
      (hstrict hx hright hx_right)
      (AppliedModelingLib.Probability.lowerCDFMass_le_one law right)

/--
The powered CDFs used for finite iid maxima are also strictly increasing on
the support interior.
-/
theorem pg23_lowerCDFMass_pow_strictMonoOn_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : pg23ConnectedSupport law)
    {n : ℕ} (hn : 0 < n) :
    StrictMonoOn
      (fun x : ℝ => (AppliedModelingLib.Probability.lowerCDFMass law x) ^ n)
      (interior law.support) := by
  intro x hx y hy hxy
  have hstrict :=
    pg23_lowerCDFMass_strictMonoOn_interior_support law hconnected hx hy hxy
  exact pow_lt_pow_left₀ hstrict
    (AppliedModelingLib.Probability.lowerCDFMass_nonneg law x) (Nat.ne_of_gt hn)

/--
At every interior support point, every positive power of the lower CDF lies in
`(0,1)`.
-/
theorem pg23_lowerCDFMass_pow_mem_Ioo_of_mem_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : pg23ConnectedSupport law)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : x ∈ interior law.support) :
    (AppliedModelingLib.Probability.lowerCDFMass law x) ^ n ∈ Ioo (0 : ℝ) 1 := by
  have hmem := pg23_lowerCDFMass_mem_Ioo_of_mem_interior_support law hconnected hx
  exact ⟨pow_pos hmem.1 n,
    pow_lt_one₀ hmem.1.le hmem.2 (Nat.ne_of_gt hn)⟩

/--
Any open interval that meets the support interior has positive real measure.
This is the support-interior form of `proofs.tex:26-35`.
-/
theorem pg23_openInterval_measureReal_pos_of_intersects_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law] {a b : ℝ}
    (hintersects : (Ioo a b ∩ interior law.support).Nonempty) :
    0 < law.real (Ioo a b) := by
  rcases hintersects with ⟨x, hx_interval, hx_interior⟩
  have hpos : 0 < law (Ioo a b) :=
    (Measure.mem_support_iff_forall x).mp (interior_subset hx_interior)
      (Ioo a b) (Ioo_mem_nhds hx_interval.1 hx_interval.2)
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top law _)

/-- Crossing pairs in connected value/noise supports force an interior-noise value. -/
private theorem exists_value_mem_noise_interior_of_crossing_pairs
    (valueLaw noiseLaw : Measure ℝ)
    (hvalue : IsPreconnected valueLaw.support)
    (hnoise : IsPreconnected noiseLaw.support)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {p vLow vHigh xLow xHigh : ℝ}
    (hvLow : vLow ∈ valueLaw.support) (hvHigh : vHigh ∈ valueLaw.support)
    (hxLow : xLow ∈ noiseLaw.support) (hxHigh : xHigh ∈ noiseLaw.support)
    (hlow : vLow + xLow < p) (hhigh : p < vHigh + xHigh) :
    ∃ v ∈ valueLaw.support, p - v ∈ interior noiseLaw.support := by
  by_cases hv_order : vHigh ≤ vLow
  · refine ⟨vHigh, hvHigh, ?_⟩
    apply mem_interior_of_between_mem_preconnected hnoise hxLow hxHigh
    · linarith
    · linarith
  · have hvLow_lt_vHigh : vLow < vHigh := lt_of_not_ge hv_order
    rcases lt_trichotomy xLow xHigh with hx_order | hx_eq | hx_order
    · let left : ℝ := max vLow (p - xHigh)
      let right : ℝ := min vHigh (p - xLow)
      have hleft_right : left < right := by
        dsimp [left, right]
        apply lt_min
        · apply max_lt hvLow_lt_vHigh
          linarith
        · apply max_lt
          · linarith
          · linarith
      let v : ℝ := (left + right) / 2
      have hleft_v : left < v := by
        dsimp [v]
        linarith
      have hv_right : v < right := by
        dsimp [v]
        linarith
      have hv_support : v ∈ valueLaw.support := by
        apply hvalue.Icc_subset hvLow hvHigh
        constructor
        · exact (le_max_left vLow (p - xHigh)).trans hleft_v.le
        · exact hv_right.le.trans (min_le_left vHigh (p - xLow))
      refine ⟨v, hv_support, ?_⟩
      apply mem_interior_of_between_mem_preconnected hnoise hxLow hxHigh
      · have hv_upper : v < p - xLow :=
          hv_right.trans_le (min_le_right vHigh (p - xLow))
        linarith
      · have hv_lower : p - xHigh < v :=
          (le_max_right vLow (p - xHigh)).trans_lt hleft_v
        linarith
    · subst xHigh
      rcases hnoise_nondegenerate with ⟨x, y, hx, hy, hxy⟩
      by_cases hxb : x < xLow
      · let threshold : ℝ := p - xLow
        let right : ℝ := min vHigh (p - x)
        have hthreshold_right : threshold < right := by
          dsimp [threshold, right]
          apply lt_min
          · linarith
          · linarith
        let v : ℝ := (threshold + right) / 2
        have hthreshold_v : threshold < v := by
          dsimp [v]
          linarith
        have hv_right : v < right := by
          dsimp [v]
          linarith
        have hv_support : v ∈ valueLaw.support := by
          apply hvalue.Icc_subset hvLow hvHigh
          constructor
          · exact (le_of_lt (by dsimp [threshold] at hthreshold_v; linarith))
          · exact hv_right.le.trans (min_le_left vHigh (p - x))
        refine ⟨v, hv_support, ?_⟩
        apply mem_interior_of_between_mem_preconnected hnoise hx hxLow
        · have hv_upper : v < p - x :=
            hv_right.trans_le (min_le_right vHigh (p - x))
          linarith
        · dsimp [threshold] at hthreshold_v
          linarith
      · have hxLow_lt_y : xLow < y := by linarith
        let threshold : ℝ := p - xLow
        let left : ℝ := max vLow (p - y)
        have hleft_threshold : left < threshold := by
          dsimp [left, threshold]
          apply max_lt
          · linarith
          · linarith
        let v : ℝ := (left + threshold) / 2
        have hleft_v : left < v := by
          dsimp [v]
          linarith
        have hv_threshold : v < threshold := by
          dsimp [v]
          linarith
        have hv_support : v ∈ valueLaw.support := by
          apply hvalue.Icc_subset hvLow hvHigh
          constructor
          · exact (le_max_left vLow (p - y)).trans hleft_v.le
          · exact le_of_lt (by dsimp [threshold] at hv_threshold; linarith)
        refine ⟨v, hv_support, ?_⟩
        apply mem_interior_of_between_mem_preconnected hnoise hxLow hy
        · dsimp [threshold] at hv_threshold
          linarith
        · have hv_lower : p - y < v :=
            (le_max_right vLow (p - y)).trans_lt hleft_v
          linarith
    · let left : ℝ := p - xLow
      let right : ℝ := p - xHigh
      have hleft_right : left < right := by
        dsimp [left, right]
        linarith
      let v : ℝ := (left + right) / 2
      have hleft_v : left < v := by
        dsimp [v]
        linarith
      have hv_right : v < right := by
        dsimp [v]
        linarith
      have hv_support : v ∈ valueLaw.support := by
        apply hvalue.Icc_subset hvLow hvHigh
        constructor <;> dsimp [left, right] at hleft_v hv_right <;> linarith
      refine ⟨v, hv_support, ?_⟩
      apply mem_interior_of_between_mem_preconnected hnoise hxHigh hxLow
      · dsimp [right] at hv_right
        linarith
      · dsimp [left] at hleft_v
        linarith

/--
An interior weak-tail clearing mass gives positive value mass to the literal
noise-interior cutoff region.  This support formulation remains valid for
unbounded supports and endpoint atoms.  Noise nondegeneracy is explicit
because deterministic noise makes the paper's strict comparisons false.
-/
theorem pg23NoiseInteriorCutoffRegion_measure_pos_of_sum_weakTail
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {p s : ℝ} (hs : 0 < s ∧ s < 1)
    (hlevel :
      Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (valueLaw.prod noiseLaw)
        ({p} : Set ℝ) = 0)
    (htail :
      (Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        (valueLaw.prod noiseLaw)).real (Ici p) = s) :
    0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw p) := by
  let productLaw : Measure (ℝ × ℝ) := valueLaw.prod noiseLaw
  let sumLaw : Measure ℝ :=
    Measure.map (fun z : ℝ × ℝ => z.1 + z.2) productLaw
  letI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  letI : IsProbabilityMeasure sumLaw := by
    dsimp [sumLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop :
      AEMeasurable (fun z : ℝ × ℝ => z.1 + z.2) productLaw)
  change sumLaw ({p} : Set ℝ) = 0 at hlevel
  change sumLaw.real (Ici p) = s at htail
  have hlow_real : sumLaw.real (Iio p) = 1 - s := by
    have hcompl := MeasureTheory.probReal_compl_eq_one_sub
      (μ := sumLaw) (s := Ici p) measurableSet_Ici
    have hIci_compl : (Ici p)ᶜ = Iio p := by
      ext z
      simp
    rw [hIci_compl, htail] at hcompl
    exact hcompl
  have hlow_real_pos : 0 < sumLaw.real (Iio p) := by
    rw [hlow_real]
    linarith
  have hlow_pos : 0 < sumLaw (Iio p) :=
    (ENNReal.toReal_pos_iff.mp hlow_real_pos).1
  have hIci_union : Ici p = ({p} : Set ℝ) ∪ Ioi p := by
    ext z
    simp [le_iff_eq_or_lt]
  have hdisjoint : Disjoint ({p} : Set ℝ) (Ioi p) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact (lt_irrefl p) hzp
  have hlevel_real : sumLaw.real ({p} : Set ℝ) = 0 := by
    simp [Measure.real, hlevel]
  have hhigh_real : sumLaw.real (Ioi p) = s := by
    have hunion := measureReal_union (μ := sumLaw) hdisjoint measurableSet_Ioi
    rw [← hIci_union, htail, hlevel_real] at hunion
    linarith
  have hhigh_real_pos : 0 < sumLaw.real (Ioi p) := by
    rw [hhigh_real]
    exact hs.1
  have hhigh_pos : 0 < sumLaw (Ioi p) :=
    (ENNReal.toReal_pos_iff.mp hhigh_real_pos).1
  have hadd_meas : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := by fun_prop
  have hlow_product :
      0 < productLaw ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Iio p) := by
    rw [← Measure.map_apply hadd_meas measurableSet_Iio]
    exact hlow_pos
  have hhigh_product :
      0 < productLaw ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Ioi p) := by
    rw [← Measure.map_apply hadd_meas measurableSet_Ioi]
    exact hhigh_pos
  rcases Measure.nonempty_inter_support_of_pos hlow_product with
    ⟨low, hlow_crossing, hlow_support⟩
  rcases Measure.nonempty_inter_support_of_pos hhigh_product with
    ⟨high, hhigh_crossing, hhigh_support⟩
  have hproduct_support : productLaw.support = valueLaw.support ×ˢ noiseLaw.support :=
    support_prod_eq_prod_support valueLaw noiseLaw
  rw [hproduct_support] at hlow_support hhigh_support
  change low.1 + low.2 < p at hlow_crossing
  change p < high.1 + high.2 at hhigh_crossing
  rcases exists_value_mem_noise_interior_of_crossing_pairs
      valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate
      hlow_support.1 hhigh_support.1 hlow_support.2 hhigh_support.2
      hlow_crossing hhigh_crossing with
    ⟨v, hv_support, hv_region⟩
  have hopen : IsOpen (pg23NoiseInteriorCutoffRegion noiseLaw p) := by
    unfold pg23NoiseInteriorCutoffRegion
    exact isOpen_interior.preimage (continuous_const.sub continuous_id)
  exact (Measure.mem_support_iff_forall v).mp hv_support _
    (hopen.mem_nhds hv_region)

/-- Coordinate score-level nullity makes every maximum-score level set null. -/
theorem pg23SourceMaxScoreLaw_level_null_of_scoreLevelNull
    (typeLaw : Measure (PG23ApplicantType College))
    (hlevel : pg23SourceScoreLevelNull typeLaw) (p : ℝ) :
    pg23SourceMaxScoreLaw typeLaw ({p} : Set ℝ) = 0 := by
  unfold pg23SourceMaxScoreLaw
  rw [Measure.map_apply pg23SourceMaxScore_measurable (MeasurableSet.singleton p)]
  apply measure_mono_null
    (t := ⋃ c : College, {theta | pg23SourceScore theta c = p})
  · intro theta htheta
    change pg23SourceMaxScore theta = p at htheta
    rcases Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun c : College => pg23SourceScore theta c) with
      ⟨c, _hc, hc⟩
    apply Set.mem_iUnion.2
    refine ⟨c, ?_⟩
    change pg23SourceScore theta c = p
    simpa [pg23SourceMaxScore, hc] using htheta
  · exact measure_iUnion_null fun c => hlevel c p

/-- Score-level nullity turns the literal weak clearing tail into the paper's strict tail. -/
theorem pg23SourceMarketClearing_commonCutoff_strictTail_eq_supply
    (typeLaw : Measure (PG23ApplicantType College)) [IsFiniteMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    {s p : ℝ}
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand typeLaw)
      (fun _ : College => s / (Fintype.card College : ℝ))
      (fun _ : College => p)) :
    (pg23SourceMaxScoreLaw typeLaw).real (Ioi p) = s := by
  letI : IsFiniteMeasure (pg23SourceMaxScoreLaw typeLaw) := by
    unfold pg23SourceMaxScoreLaw
    infer_instance
  have hweak := pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
    typeLaw hclear
  have hlevel_measure :=
    pg23SourceMaxScoreLaw_level_null_of_scoreLevelNull typeLaw hlevel p
  have hlevel_real :
      (pg23SourceMaxScoreLaw typeLaw).real ({p} : Set ℝ) = 0 := by
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
  have hunion := measureReal_union
    (μ := pg23SourceMaxScoreLaw typeLaw) hdisjoint measurableSet_Ioi
  rw [← hIci_union, hweak, hlevel_real] at hunion
  linarith

/--
The monoculture shared cutoff has positive value mass on the paper's exact
noise-interior region, without finite support endpoints.
-/
theorem pg23MonocultureNoiseInteriorCutoffRegion_measure_pos_of_marketClearing
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    {S p : ℝ} (hS : 0 < S ∧ S < 1)
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
      (fun _ : College => S / (Fintype.card College : ℝ))
      (fun _ : College => p)) :
    0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw p) := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  have hlevel_max := pg23SourceMaxScoreLaw_level_null_of_scoreLevelNull
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) hlevel p
  have htail := pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) hclear
  rw [pg23MonocultureSourceMaxScoreLaw_eq_sumLaw] at hlevel_max htail
  exact pg23NoiseInteriorCutoffRegion_measure_pos_of_sum_weakTail
    valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hS hlevel_max htail

/--
The polyculture shared cutoff has positive value mass on the same primitive
noise-interior region; the finite iid maximum has exactly the base support.
-/
theorem pg23PolycultureNoiseInteriorCutoffRegion_measure_pos_of_marketClearing
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    {S p : ℝ} (hS : 0 < S ∧ S < 1)
    (hclear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
      (fun _ : College => S / (Fintype.card College : ℝ))
      (fun _ : College => p)) :
    0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw p) := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  let maxNoiseLaw := pg23PolycultureMaxNoiseLaw (College := College) noiseLaw
  letI : IsProbabilityMeasure maxNoiseLaw :=
    pg23PolycultureMaxNoiseLaw_isProbabilityMeasure noiseLaw
  have hmax_connected : pg23ConnectedSupport maxNoiseLaw := by
    unfold pg23ConnectedSupport maxNoiseLaw
    rw [pg23PolycultureMaxNoiseLaw_support]
    exact hnoise
  have hmax_nondegenerate :
      ∃ x y : ℝ, x ∈ maxNoiseLaw.support ∧ y ∈ maxNoiseLaw.support ∧ x < y := by
    simpa [maxNoiseLaw, pg23PolycultureMaxNoiseLaw_support] using hnoise_nondegenerate
  have hlevel_max := pg23SourceMaxScoreLaw_level_null_of_scoreLevelNull
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) hlevel p
  have htail := pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) hclear
  rw [pg23PolycultureSourceMaxScoreLaw_eq_sumMaxNoiseLaw] at hlevel_max htail
  have hpos := pg23NoiseInteriorCutoffRegion_measure_pos_of_sum_weakTail
    valueLaw maxNoiseLaw hvalue hmax_connected hmax_nondegenerate hS hlevel_max htail
  simpa [pg23NoiseInteriorCutoffRegion, maxNoiseLaw,
    pg23PolycultureMaxNoiseLaw_support] using hpos

/--
A nonatomic connected-support law puts any strict interior upper-tail
threshold in the interior of its support.
-/
theorem pg23_mem_interior_support_of_upperTailMass_eq
    (law : Measure ℝ) [IsProbabilityMeasure law] [NoAtoms law]
    (hconnected : pg23ConnectedSupport law)
    {s p : ℝ} (hs : 0 < s ∧ s < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass law p = s) :
    p ∈ interior law.support := by
  change law.real (Ioi p) = s at htail
  have hhigh_real_pos : 0 < law.real (Ioi p) := by
    rw [htail]
    exact hs.1
  have hhigh_pos : 0 < law (Ioi p) :=
    (ENNReal.toReal_pos_iff.mp hhigh_real_pos).1
  have hIic_real : law.real (Iic p) = 1 - s := by
    have hcompl := MeasureTheory.probReal_compl_eq_one_sub
      (μ := law) (s := Ioi p) measurableSet_Ioi
    have hIoi_compl : (Ioi p)ᶜ = Iic p := by
      ext z
      simp
    rw [hIoi_compl, htail] at hcompl
    exact hcompl
  have hIic_union : Iic p = Iio p ∪ ({p} : Set ℝ) := by
    ext z
    simp [le_iff_lt_or_eq]
  have hdisjoint : Disjoint (Iio p) ({p} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    simp only [Set.mem_singleton_iff] at hzp
    subst z
    exact (lt_irrefl p) hz
  have hatom_real : law.real ({p} : Set ℝ) = 0 := by
    simp [Measure.real, (measure_singleton p : law ({p} : Set ℝ) = 0)]
  have hlow_real : law.real (Iio p) = 1 - s := by
    have hunion := measureReal_union (μ := law) hdisjoint (MeasurableSet.singleton p)
    rw [← hIic_union, hIic_real, hatom_real] at hunion
    linarith
  have hlow_real_pos : 0 < law.real (Iio p) := by
    rw [hlow_real]
    linarith
  have hlow_pos : 0 < law (Iio p) :=
    (ENNReal.toReal_pos_iff.mp hlow_real_pos).1
  rcases Measure.nonempty_inter_support_of_pos hlow_pos with
    ⟨lo, hlo, hlo_support⟩
  rcases Measure.nonempty_inter_support_of_pos hhigh_pos with
    ⟨hi, hhi, hhi_support⟩
  exact mem_interior_of_between_mem_preconnected
    hconnected hlo_support hhi_support hlo hhi

/-- Interior support gives the source's two-sided local mass condition. -/
theorem pg23_twoSidedPositiveIntervalMass_of_mem_interior_support
    (law : Measure ℝ) {p : ℝ} (hp : p ∈ interior law.support) :
    AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass law p := by
  have hnhds : interior law.support ∈ 𝓝 p := isOpen_interior.mem_nhds hp
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  constructor
  · intro ε hε
    let d : ℝ := min ε δ / 2
    have hd : 0 < d := div_pos (lt_min hε hδ) (by norm_num)
    have hd_lt_ε : d < ε := by
      dsimp [d]
      have hmin := min_le_left ε δ
      linarith
    have hd_lt_δ : d < δ := by
      dsimp [d]
      have hmin := min_le_right ε δ
      linarith
    let z : ℝ := p - d
    have hz_ball : z ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [z]
      rw [abs_of_nonpos]
      · linarith
      · linarith
    have hz_support : z ∈ law.support := interior_subset (hball hz_ball)
    have hIoo : Ioo (p - ε) p ∈ 𝓝 z :=
      Ioo_mem_nhds (by dsimp [z]; linarith) (by dsimp [z]; linarith)
    have hIoc : Ioc (p - ε) p ∈ 𝓝 z :=
      Filter.mem_of_superset hIoo Ioo_subset_Ioc_self
    exact (Measure.mem_support_iff_forall z).mp hz_support _ hIoc
  · intro ε hε
    let d : ℝ := min ε δ / 2
    have hd : 0 < d := div_pos (lt_min hε hδ) (by norm_num)
    have hd_lt_ε : d < ε := by
      dsimp [d]
      have hmin := min_le_left ε δ
      linarith
    have hd_lt_δ : d < δ := by
      dsimp [d]
      have hmin := min_le_right ε δ
      linarith
    let z : ℝ := p + d
    have hz_ball : z ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [z]
      rw [abs_of_nonneg]
      · linarith
      · linarith
    have hz_support : z ∈ law.support := interior_subset (hball hz_ball)
    have hIoo : Ioo p (p + ε) ∈ 𝓝 z :=
      Ioo_mem_nhds (by dsimp [z]; linarith) (by dsimp [z]; linarith)
    have hIoc : Ioc p (p + ε) ∈ 𝓝 z :=
      Filter.mem_of_superset hIoo Ioo_subset_Ioc_self
    exact (Measure.mem_support_iff_forall z).mp hz_support _ hIoc

/-- The corrected source primitives derive the local mass used in Lemma 10. -/
theorem pg23_twoSidedPositiveIntervalMass_of_connectedSupport_noAtoms_upperTailMass_eq
    (law : Measure ℝ) [IsProbabilityMeasure law] [NoAtoms law]
    (hconnected : pg23ConnectedSupport law)
    {s p : ℝ} (hs : 0 < s ∧ s < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass law p = s) :
    AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass law p :=
  pg23_twoSidedPositiveIntervalMass_of_mem_interior_support law
    (pg23_mem_interior_support_of_upperTailMass_eq law hconnected hs htail)

/--
On a probability law with connected support, an interior weak upper-tail mass
determines its cutoff uniquely.  This is the support-safe form of the strict
scalar-clearing step in `proofs.tex:70-123`; it does not use finite support
endpoints or endpoint CDF values.
-/
theorem pg23_cutoff_eq_of_connectedSupport_weakTail_eq
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : IsPreconnected law.support)
    {s x y : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hx : law.real (Ici x) = s) (hy : law.real (Ici y) = s) :
    x = y := by
  have hnot_lt : ∀ {a b : ℝ},
      law.real (Ici a) = s -> law.real (Ici b) = s -> ¬ a < b := by
    intro a b ha hb hab
    have hhigh_real_pos : 0 < law.real (Ici b) := by
      rw [hb]
      exact hs_pos
    have hlow_real_eq : law.real (Iio a) = 1 - s := by
      have hcompl := MeasureTheory.probReal_compl_eq_one_sub
        (μ := law) (s := Ici a) measurableSet_Ici
      have hIci_compl : (Ici a)ᶜ = Iio a := by
        ext z
        simp
      rw [hIci_compl, ha] at hcompl
      exact hcompl
    have hlow_real_pos : 0 < law.real (Iio a) := by
      rw [hlow_real_eq]
      linarith
    have hhigh_pos : 0 < law (Ici b) :=
      (ENNReal.toReal_pos_iff.mp hhigh_real_pos).1
    have hlow_pos : 0 < law (Iio a) :=
      (ENNReal.toReal_pos_iff.mp hlow_real_pos).1
    rcases Measure.nonempty_inter_support_of_pos hlow_pos with
      ⟨lo, hlo_a, hlo_support⟩
    rcases Measure.nonempty_inter_support_of_pos hhigh_pos with
      ⟨hi, hb_hi, hhi_support⟩
    let mid : ℝ := (a + b) / 2
    have ha_mid : a < mid := by
      dsimp [mid]
      linarith
    have hmid_b : mid < b := by
      dsimp [mid]
      linarith
    have hlo_mid : lo ≤ mid :=
      le_trans (le_of_lt hlo_a) (le_of_lt ha_mid)
    have hmid_hi : mid ≤ hi :=
      le_trans (le_of_lt hmid_b) hb_hi
    have hmid_support : mid ∈ law.support :=
      hconnected.Icc_subset hlo_support hhi_support ⟨hlo_mid, hmid_hi⟩
    have hopen_pos : 0 < law (Ioo a b) :=
      (Measure.mem_support_iff_forall mid).mp hmid_support
        (Ioo a b) (Ioo_mem_nhds ha_mid hmid_b)
    have hopen_real_pos : 0 < law.real (Ioo a b) :=
      ENNReal.toReal_pos hopen_pos.ne' (measure_ne_top law _)
    have hdiff_subset : Ioo a b ⊆ Ici a \ Ici b := by
      intro z hz
      exact ⟨le_of_lt hz.1, not_le_of_gt hz.2⟩
    have hdiff_real_pos : 0 < law.real (Ici a \ Ici b) :=
      lt_of_lt_of_le hopen_real_pos
        (measureReal_mono hdiff_subset (measure_ne_top law _))
    have hb_subset : Ici b ⊆ Ici a := by
      intro z hz
      exact (le_of_lt hab).trans hz
    have hdiff_eq : law.real (Ici a \ Ici b) = 0 := by
      rw [measureReal_diff hb_subset measurableSet_Ici, ha, hb]
      exact sub_self s
    rw [hdiff_eq] at hdiff_real_pos
    exact (lt_irrefl 0) hdiff_real_pos
  apply le_antisymm
  · exact le_of_not_gt (hnot_lt hy hx)
  · exact le_of_not_gt (hnot_lt hx hy)

/--
A connected-support probability law's strict upper-tail mass in `(0,1)`
determines its cutoff uniquely.
-/
theorem pg23_cutoff_eq_of_connectedSupport_strictTail_eq
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : IsPreconnected law.support)
    {s x y : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hx : law.real (Ioi x) = s) (hy : law.real (Ioi y) = s) :
    x = y := by
  have hnot_lt : ∀ {a b : ℝ},
      law.real (Ioi a) = s -> law.real (Ioi b) = s -> ¬ a < b := by
    intro a b ha hb hab
    have hhigh_real_pos : 0 < law.real (Ioi b) := by
      rw [hb]
      exact hs_pos
    have hlow_real_eq : law.real (Iic a) = 1 - s := by
      have hcompl := MeasureTheory.probReal_compl_eq_one_sub
        (μ := law) (s := Ioi a) measurableSet_Ioi
      have hIoi_compl : (Ioi a)ᶜ = Iic a := by
        ext z
        simp
      rw [hIoi_compl, ha] at hcompl
      exact hcompl
    have hlow_real_pos : 0 < law.real (Iic a) := by
      rw [hlow_real_eq]
      linarith
    have hhigh_pos : 0 < law (Ioi b) :=
      (ENNReal.toReal_pos_iff.mp hhigh_real_pos).1
    have hlow_pos : 0 < law (Iic a) :=
      (ENNReal.toReal_pos_iff.mp hlow_real_pos).1
    rcases Measure.nonempty_inter_support_of_pos hlow_pos with
      ⟨lo, hlo_a, hlo_support⟩
    rcases Measure.nonempty_inter_support_of_pos hhigh_pos with
      ⟨hi, hb_hi, hhi_support⟩
    let mid : ℝ := (a + b) / 2
    have ha_mid : a < mid := by
      dsimp [mid]
      linarith
    have hmid_b : mid < b := by
      dsimp [mid]
      linarith
    have hlo_mid : lo ≤ mid :=
      le_trans hlo_a (le_of_lt ha_mid)
    have hmid_hi : mid ≤ hi :=
      le_trans (le_of_lt hmid_b) (le_of_lt hb_hi)
    have hmid_support : mid ∈ law.support :=
      hconnected.Icc_subset hlo_support hhi_support ⟨hlo_mid, hmid_hi⟩
    have hopen_pos : 0 < law (Ioo a b) :=
      (Measure.mem_support_iff_forall mid).mp hmid_support
        (Ioo a b) (Ioo_mem_nhds ha_mid hmid_b)
    have hopen_real_pos : 0 < law.real (Ioo a b) :=
      ENNReal.toReal_pos hopen_pos.ne' (measure_ne_top law _)
    have hdiff_subset : Ioo a b ⊆ Ioi a \ Ioi b := by
      intro z hz
      exact ⟨hz.1, not_lt_of_ge (le_of_lt hz.2)⟩
    have hdiff_real_pos : 0 < law.real (Ioi a \ Ioi b) :=
      lt_of_lt_of_le hopen_real_pos
        (measureReal_mono hdiff_subset (measure_ne_top law _))
    have hb_subset : Ioi b ⊆ Ioi a := by
      intro z hz
      exact lt_trans hab hz
    have hdiff_eq : law.real (Ioi a \ Ioi b) = 0 := by
      rw [measureReal_diff hb_subset measurableSet_Ioi, ha, hb]
      exact sub_self s
    rw [hdiff_eq] at hdiff_real_pos
    exact (lt_irrefl 0) hdiff_real_pos
  apply le_antisymm
  · exact le_of_not_gt (hnot_lt hy hx)
  · exact le_of_not_gt (hnot_lt hx hy)

/--
Two common raw cutoffs cannot both clear the same interior total supply when
the induced maximum-score law has connected support.
-/
theorem pg23SourceMarketClearing_commonCutoff_unique
    (typeLaw : Measure (PG23ApplicantType College))
    [IsProbabilityMeasure typeLaw]
    (hscore_connected : IsPreconnected (pg23SourceMaxScoreLaw typeLaw).support)
    {s p q : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hp : pg23SourceMarketClearing
      (pg23SourceAggregateDemand typeLaw)
      (fun _ : College => s / (Fintype.card College : ℝ))
      (fun _ : College => p))
    (hq : pg23SourceMarketClearing
      (pg23SourceAggregateDemand typeLaw)
      (fun _ : College => s / (Fintype.card College : ℝ))
      (fun _ : College => q)) :
    p = q := by
  letI : IsProbabilityMeasure (pg23SourceMaxScoreLaw typeLaw) :=
    pg23SourceMaxScoreLaw_isProbabilityMeasure typeLaw
  exact pg23_cutoff_eq_of_connectedSupport_weakTail_eq
    (pg23SourceMaxScoreLaw typeLaw) hscore_connected hs_pos hs_lt_one
    (pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply typeLaw hp)
    (pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply typeLaw hq)

/--
The normalized clearing cutoff is unique once literal relabeling symmetry and
connected support of the induced maximum-score law are established.  The
proof constructs the A-L least and greatest cutoffs, proves both are constant,
and identifies their raw scalar values by the checked tail-mass argument.
-/
theorem pg23NormalizedMarketClearing_unique_of_relabel_maxScoreConnected
    (typeLaw : Measure (PG23ApplicantType College))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (htop_rank : ∀ c : College,
      typeLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hscore_connected : IsPreconnected (pg23SourceMaxScoreLaw typeLaw).support)
    (s : ℝ) (hs : 0 < s ∧ s < 1)
    (hrelabel : ∀ (sigma : Equiv.Perm College) (Q : AL16Cutoff College),
      al16SourceMarketClearing
        (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
        (fun _ : College => s / (Fintype.card College : ℝ)) Q ->
      al16SourceMarketClearing
        (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
        (fun _ : College => s / (Fintype.card College : ℝ))
        (pg23RelabelNormalizedCutoff sigma Q)) :
    ∀ Q R : AL16Cutoff College,
      al16SourceMarketClearing
          (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
          (fun _ : College => s / (Fintype.card College : ℝ)) Q ->
      al16SourceMarketClearing
          (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
          (fun _ : College => s / (Fintype.card College : ℝ)) R ->
      Q = R := by
  letI : IsProbabilityMeasure (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure typeLaw
  have hstrict : al16SourceStrictPreferences (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_strictPreferences_of_raw typeLaw hlevel
  have hcapacity_pos : ∀ c : College,
      0 < s / (Fintype.card College : ℝ) := by
    intro c
    have hcardpos : (0 : ℝ) < Fintype.card College := by
      exact_mod_cast Fintype.card_pos
    exact div_pos hs.1 hcardpos
  let valid : AL16Cutoff College -> Prop :=
    al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
      (fun _ : College => s / (Fintype.card College : ℝ))
  have hne : ∃ Q : AL16Cutoff College, valid Q :=
    al16SourceMarketClearing_nonempty_of_concrete_continuum_primitives
      (pg23NormalizedTypeLaw typeLaw)
      (fun _ : College => s / (Fintype.card College : ℝ))
      hcapacity_pos hstrict
  let L : CompleteLatticeOn valid al16CutoffLe :=
    al16SourceMarketClearing_completeLattice_of_concrete_continuum_primitives
      (pg23NormalizedTypeLaw typeLaw)
      (fun _ : College => s / (Fintype.card College : ℝ)) hstrict hne
  rcases L.exists_least hne with ⟨bot, hbot⟩
  rcases L.exists_greatest hne with ⟨top, htop⟩
  have hrelabel_valid : ∀ (sigma : Equiv.Perm College) (Q : AL16Cutoff College),
      valid Q -> valid (pg23RelabelNormalizedCutoff sigma Q) := by
    intro sigma Q hQ
    exact hrelabel sigma Q hQ
  rcases pg23NormalizedCutoff_constant_of_relabel_fixed bot (fun sigma =>
      pg23RelabelNormalizedCutoff_eq_of_least valid bot hbot
        hrelabel_valid sigma) with ⟨botValue, hbotValue⟩
  rcases pg23NormalizedCutoff_constant_of_relabel_fixed top (fun sigma =>
      pg23RelabelNormalizedCutoff_eq_of_greatest valid top htop
        hrelabel_valid sigma) with ⟨topValue, htopValue⟩
  have hbot_interior : ∀ c : College,
      0 < al16CutoffValue bot c ∧ al16CutoffValue bot c < 1 :=
    pg23NormalizedMarketClearing_cutoff_interior typeLaw hlevel htop_rank
      s hs (fun _ : College => s / (Fintype.card College : ℝ))
      (fun _ => rfl) bot hbot.1
  have htop_interior : ∀ c : College,
      0 < al16CutoffValue top c ∧ al16CutoffValue top c < 1 :=
    pg23NormalizedMarketClearing_cutoff_interior typeLaw hlevel htop_rank
      s hs (fun _ : College => s / (Fintype.card College : ℝ))
      (fun _ => rfl) top htop.1
  have hbot_raw := pg23SourceMarketClearing_of_normalized typeLaw
    (fun _ : College => s / (Fintype.card College : ℝ)) bot
    hbot_interior hbot.1
  have htop_raw := pg23SourceMarketClearing_of_normalized typeLaw
    (fun _ : College => s / (Fintype.card College : ℝ)) top
    htop_interior htop.1
  have hbot_denormalized : pg23DenormalizedCutoff bot =
      fun _ : College => pg23ScoreDenormalize botValue := by
    funext c
    unfold pg23DenormalizedCutoff
    rw [hbotValue c]
  have htop_denormalized : pg23DenormalizedCutoff top =
      fun _ : College => pg23ScoreDenormalize topValue := by
    funext c
    unfold pg23DenormalizedCutoff
    rw [htopValue c]
  rw [hbot_denormalized] at hbot_raw
  rw [htop_denormalized] at htop_raw
  have hraw_value_eq :
      pg23ScoreDenormalize botValue = pg23ScoreDenormalize topValue :=
    pg23SourceMarketClearing_commonCutoff_unique typeLaw hscore_connected
      hs.1 hs.2 hbot_raw htop_raw
  have hraw_cutoff_eq : pg23DenormalizedCutoff bot =
      pg23DenormalizedCutoff top := by
    rw [hbot_denormalized, htop_denormalized, hraw_value_eq]
  have hbot_top : bot = top := by
    calc
      bot = pg23NormalizedCutoff (pg23DenormalizedCutoff bot) :=
        (pg23NormalizedCutoff_denormalized_eq bot hbot_interior).symm
      _ = pg23NormalizedCutoff (pg23DenormalizedCutoff top) := by
        rw [hraw_cutoff_eq]
      _ = top := pg23NormalizedCutoff_denormalized_eq top htop_interior
  exact L.unique_of_least_greatest_eq hbot htop hbot_top

/-- Literal monoculture raw clearing cutoffs are unique from the source support primitives. -/
theorem pg23MonocultureSourceMarketClearing_unique
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (s : ℝ) (hs : 0 < s ∧ s < 1) :
    ∀ P Q : College -> ℝ,
      pg23SourceMarketClearing
          (pg23SourceAggregateDemand
            (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
          (fun _ : College => s / (Fintype.card College : ℝ)) P ->
      pg23SourceMarketClearing
          (pg23SourceAggregateDemand
            (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
          (fun _ : College => s / (Fintype.card College : ℝ)) Q ->
      P = Q := by
  let typeLaw := pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  have hscore_connected :=
    pg23MonocultureSourceMaxScoreLaw_connectedSupport
      (College := College) valueLaw noiseLaw hvalue hnoise
  have hnormalized_unique :=
    pg23NormalizedMarketClearing_unique_of_relabel_maxScoreConnected
      typeLaw hlevel
      (pg23MonocultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
      hscore_connected s hs (fun sigma R hR =>
        pg23MonocultureNormalizedMarketClearing_relabel
          valueLaw noiseLaw hlevel s hs
          (fun _ : College => s / (Fintype.card College : ℝ))
          (fun _ => rfl) sigma R hR)
  intro P Q hP hQ
  have hnormalized : pg23NormalizedCutoff P = pg23NormalizedCutoff Q :=
    hnormalized_unique (pg23NormalizedCutoff P) (pg23NormalizedCutoff Q)
      (pg23NormalizedMarketClearing_of_raw typeLaw _ P hP)
      (pg23NormalizedMarketClearing_of_raw typeLaw _ Q hQ)
  funext c
  exact pg23ScoreNormalize_strictMono.injective (congrFun hnormalized c)

/-- Literal polyculture raw clearing cutoffs are unique from the source support primitives. -/
theorem pg23PolycultureSourceMarketClearing_unique
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (s : ℝ) (hs : 0 < s ∧ s < 1) :
    ∀ P Q : College -> ℝ,
      pg23SourceMarketClearing
          (pg23SourceAggregateDemand
            (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
          (fun _ : College => s / (Fintype.card College : ℝ)) P ->
      pg23SourceMarketClearing
          (pg23SourceAggregateDemand
            (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
          (fun _ : College => s / (Fintype.card College : ℝ)) Q ->
      P = Q := by
  let typeLaw := pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  have hscore_connected :=
    pg23PolycultureSourceMaxScoreLaw_connectedSupport
      (College := College) valueLaw noiseLaw hvalue hnoise
  have hnormalized_unique :=
    pg23NormalizedMarketClearing_unique_of_relabel_maxScoreConnected
      typeLaw hlevel
      (pg23PolycultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
      hscore_connected s hs (fun sigma R hR =>
        pg23PolycultureNormalizedMarketClearing_relabel
          valueLaw noiseLaw hlevel s hs
          (fun _ : College => s / (Fintype.card College : ℝ))
          (fun _ => rfl) sigma R hR)
  intro P Q hP hQ
  have hnormalized : pg23NormalizedCutoff P = pg23NormalizedCutoff Q :=
    hnormalized_unique (pg23NormalizedCutoff P) (pg23NormalizedCutoff Q)
      (pg23NormalizedMarketClearing_of_raw typeLaw _ P hP)
      (pg23NormalizedMarketClearing_of_raw typeLaw _ Q hQ)
  funext c
  exact pg23ScoreNormalize_strictMono.injective (congrFun hnormalized c)

end PG23MonocultureMatching

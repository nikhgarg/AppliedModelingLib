import PRPKG24AccuracyDiversity.MainTheorems

/-!
# PRPKG Appendix D.2: Density Source Bridge

This module records the semantic probability bridge used in the bounded
branch. The source writes that `D` has a PDF whose upper-endpoint asymptotic
is `c * (M - x)^(beta - 1)`.

The lower-level reflected-density helper accepts a local density `g`, its
local integrability, and an upper-tail mass identity. The literal
`withDensity` PDF endpoints below derive those facts from the source-shaped
probability law instead of receiving them as premises. Neither route accepts
the resulting CDF-power tail law or a split certificate as a premise.
-/

namespace PRPKG24AccuracyDiversity

open Filter Topology
open scoped BigOperators

/--
The source PDF asymptotic gives the reflected-CDF power-tail sandwich once
the PDF notation is connected to the probability measure by the explicit
local mass-as-integral identity.
-/
theorem lemmaD2_reflected_cdf_power_sandwich_of_density_ratio
    {baseMeasure : MeasureTheory.Measure ℝ} {M beta c : ℝ} {g : ℝ → ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (h_integrable :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ))) :
    BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c :=
  BoundedTailCDFPowerSandwich.of_reflectedCDFMass_upper_endpoint_density_ratio_integral
    hbeta_pos hc_pos h_integrable hmass hratio

/--
A literal real-valued PDF representation turns the measure's closed upper-tail
mass into a Lebesgue integral.  The density is nonnegative and measurable, so
the `withDensity` mass and the real set integral agree exactly.
-/
theorem measureReal_Ici_eq_integral_of_pdf
    {baseMeasure : MeasureTheory.Measure ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f) :
    baseMeasure.real (Set.Ici a) = ∫ y in Set.Ici a, f y := by
  rw [hpdf, MeasureTheory.measureReal_def,
    MeasureTheory.withDensity_apply _ measurableSet_Ici]
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (μ := MeasureTheory.volume.restrict (Set.Ici a))
    (by filter_upwards with y; exact hf_nonneg y)
    hf_measurable.aestronglyMeasurable.restrict).symm

/--
For a probability law represented by a nonnegative measurable PDF, global
Lebesgue integrability is a consequence of the `withDensity` representation,
not an additional source assumption.
-/
theorem integrable_pdf_of_probability
    {baseMeasure : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f) :
    MeasureTheory.Integrable f := by
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    hf_measurable.aestronglyMeasurable
    (by filter_upwards with y; exact hf_nonneg y)).mp
  rw [← MeasureTheory.setLIntegral_univ,
    ← MeasureTheory.withDensity_apply _ MeasurableSet.univ, ← hpdf]
  simp

/--
If a `withDensity` PDF law has support at most `M`, then its chosen density
representative vanishes almost everywhere above `M`.  This discharges the
upper-support fact needed by the reflection substitution from the source's
bounded-support premise rather than asking callers to restate it for `f`.
-/
theorem pdf_zero_above_of_ae_upper_bound
    {baseMeasure : MeasureTheory.Measure ℝ} {f : ℝ → ℝ} {L M : ℝ}
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M) :
    f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi M)] fun _ => 0 := by
  have htail_base : baseMeasure (Set.Ioi M) = 0 := by
    have hnot : ∀ᵐ y ∂baseMeasure, y ∉ Set.Ioi M := by
      filter_upwards [h_base_bounds] with y hy
      exact not_lt_of_ge hy.2
    have hzero := MeasureTheory.ae_iff.mp hnot
    simpa only [Set.mem_Ioi, not_not] using hzero
  have hdensity_zero :
      MeasureTheory.volume
          ({y | ENNReal.ofReal (f y) ≠ 0} ∩ Set.Ioi M) = 0 := by
    rw [hpdf] at htail_base
    exact (MeasureTheory.withDensity_apply_eq_zero
      (ENNReal.measurable_ofReal.comp hf_measurable)).mp htail_base
  change ∀ᵐ y ∂MeasureTheory.volume.restrict (Set.Ioi M), f y = 0
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  apply MeasureTheory.ae_iff.mpr
  refine MeasureTheory.measure_mono_null ?_ hdensity_zero
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push Not at hy
  refine ⟨?_, hy.1⟩
  intro hzero
  apply hy.2
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) (hf_nonneg y)

/--
For a PDF that vanishes almost everywhere above its upper endpoint, reflection
changes the upper-tail mass into the local integral of `u ↦ f (M - u)`.  This
is the measure-theoretic content hidden by the source phrase "has pdf".
-/
theorem upper_endpoint_mass_eq_reflected_density_integral_of_pdf
    {baseMeasure : MeasureTheory.Measure ℝ} {f : ℝ → ℝ} {M x : ℝ}
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hf_zero_above :
      f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi M)] fun _ => 0)
    (hx_pos : 0 < x) :
    baseMeasure.real (Set.Ici (M - x)) =
      ∫ u in Set.Ioo (0 : ℝ) x, f (M - u) := by
  have htail_zero : ∫ y in Set.Ioi M, f y = 0 := by
    rw [← MeasureTheory.integral_zero]
    exact MeasureTheory.integral_congr_ae hf_zero_above
  have hIoi_left : MeasureTheory.IntegrableOn f (Set.Ioi (M - x)) :=
    hf_integrable.integrableOn
  have hIoi_right : MeasureTheory.IntegrableOn f (Set.Ioi M) :=
    hf_integrable.integrableOn
  have hsplit := intervalIntegral.integral_interval_add_Ioi hIoi_left hIoi_right
  have hIoi_eq_interval :
      (∫ y in Set.Ioi (M - x), f y) = ∫ y in M - x..M, f y := by
    rw [← hsplit, htail_zero, add_zero]
  calc
    baseMeasure.real (Set.Ici (M - x)) =
        ∫ y in Set.Ici (M - x), f y :=
      measureReal_Ici_eq_integral_of_pdf hpdf hf_nonneg hf_measurable
    _ = ∫ y in Set.Ioi (M - x), f y :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    _ = ∫ y in M - x..M, f y := hIoi_eq_interval
    _ = ∫ u in (0 : ℝ)..x, f (M - u) := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := x) f M).symm
    _ = ∫ u in Set.Ioc (0 : ℝ) x, f (M - u) :=
      intervalIntegral.integral_of_le hx_pos.le
    _ = ∫ u in Set.Ioo (0 : ℝ) x, f (M - u) :=
      MeasureTheory.integral_Ioc_eq_integral_Ioo

/--
Global integrability of the PDF gives the local reflected-density
integrability needed by the density-to-tail calculus bridge.
-/
theorem reflected_density_locally_integrable_of_pdf
    {f : ℝ → ℝ} {M : ℝ}
    (hf_integrable : MeasureTheory.Integrable f) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      MeasureTheory.IntegrableOn (fun u => f (M - u))
        (Set.Ioo (0 : ℝ) x) := by
  filter_upwards [self_mem_nhdsWithin] with x hx_pos
  have hinterval :
      IntervalIntegrable f MeasureTheory.volume (M - x) M :=
    hf_integrable.intervalIntegrable
  have hreflected :
      IntervalIntegrable (fun u => f (M - u))
        MeasureTheory.volume (0 : ℝ) x := by
    simpa using (hinterval.comp_sub_left M).symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hx_pos.le).1 hreflected

/--
The source PDF convention, made literal as a `withDensity` probability law,
implies the reflected-CDF power-tail sandwich.  Unlike the lower-level bridge,
this theorem does not assume either local integrability or the tail-mass
integral identity: both are derived from the PDF model.
-/
theorem lemmaD2_reflected_cdf_power_sandwich_of_pdf
    {baseMeasure : MeasureTheory.Measure ℝ} {f : ℝ → ℝ} {M beta c : ℝ}
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hf_zero_above :
      f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi M)] fun _ => 0)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ))) :
    BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c := by
  apply lemmaD2_reflected_cdf_power_sandwich_of_density_ratio
    (g := fun u => f (M - u)) hbeta_pos hc_pos
  · exact reflected_density_locally_integrable_of_pdf hf_integrable
  · filter_upwards [self_mem_nhdsWithin] with x hx_pos
    exact upper_endpoint_mass_eq_reflected_density_integral_of_pdf
      hpdf hf_nonneg hf_measurable hf_integrable hf_zero_above hx_pos
  · exact hratio

/--
Source Lemma D.2's fixed-rank integral asymptotic from the actual bounded
iid source measure and density-ratio convention.  Bounded support supplies
the tail control after the density-to-CDF bridge; no split certificate is
assumed by this theorem.
-/
theorem lemmaD2_bounded_fixed_rank_integral_asymptotic_of_density_ratio
    {beta c M L : ℝ} {j : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (g : ℝ → ℝ)
    (h_integrable :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) j)
      (fun a =>
        boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) := by
  let tail : BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c :=
    lemmaD2_reflected_cdf_power_sandwich_of_density_ratio
      hbeta_pos hc_pos h_integrable hmass hratio
  exact
    (paper_lemmaD2_bounded_split_certificate_of_cdf_power_sandwich_monotone_bounded_support
      tail hwidth_pos
      (AppliedModelingLib.Probability.reflectedCDFMass_measurable baseMeasure M)
      (AppliedModelingLib.Probability.reflectedCDFMass_mono baseMeasure M)
      (fun x => AppliedModelingLib.Probability.reflectedCDFMass_nonneg baseMeasure M x)
      (fun x => AppliedModelingLib.Probability.reflectedCDFMass_le_one baseMeasure M x)
      (fun x hx =>
        AppliedModelingLib.Probability.reflectedCDFMass_eq_one_of_ae_bounds
          baseMeasure h_base_bounds hx)).integralTerm_asymptoticEquivalent

/--
Source Lemma 1's top-`k` loss asymptotic from the same density-ratio model.
The only analytic source premises are the local density ratio, local
integrability, and the mass-as-integral connection.
-/
theorem lemma1_bounded_topk_loss_asymptotic_of_density_ratio
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (g : ℝ → ℝ)
    (h_integrable :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)))
    (k_pos : 0 < k) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) := by
  let tail : BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c :=
    lemmaD2_reflected_cdf_power_sandwich_of_density_ratio
      hbeta_pos hc_pos h_integrable hmass hratio
  exact
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
      baseMeasure h_base_bounds tail k_pos hwidth_pos

/--
Source Lemma D.2's fixed-rank integral asymptotic under a literal PDF model.
The reflected CDF tail law is derived in this module from the source density
asymptotic and is not supplied as a certificate.
-/
theorem lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf
    {beta c M L : ℝ} {j : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) j)
      (fun a =>
        boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) := by
  have hf_zero_above :=
    pdf_zero_above_of_ae_upper_bound
      hpdf hf_nonneg hf_measurable h_base_bounds
  exact
    lemmaD2_bounded_fixed_rank_integral_asymptotic_of_density_ratio
      baseMeasure h_base_bounds hwidth_pos hbeta_pos hc_pos
      (fun u => f (M - u))
      (reflected_density_locally_integrable_of_pdf hf_integrable)
      (by
        filter_upwards [self_mem_nhdsWithin] with x hx_pos
        exact upper_endpoint_mass_eq_reflected_density_integral_of_pdf
          hpdf hf_nonneg hf_measurable hf_integrable hf_zero_above hx_pos)
      hratio

/--
Source Lemma 1's top-`k` loss asymptotic under the literal PDF model.  This is
the same source route as the fixed-rank theorem above, assembled over the
finite top-`k` prefix.
-/
theorem lemma1_bounded_topk_loss_asymptotic_of_pdf
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)))
    (k_pos : 0 < k) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) := by
  have hf_zero_above :=
    pdf_zero_above_of_ae_upper_bound
      hpdf hf_nonneg hf_measurable h_base_bounds
  exact
    lemma1_bounded_topk_loss_asymptotic_of_density_ratio
      baseMeasure h_base_bounds hwidth_pos hbeta_pos hc_pos
      (fun u => f (M - u))
      (reflected_density_locally_integrable_of_pdf hf_integrable)
      (by
        filter_upwards [self_mem_nhdsWithin] with x hx_pos
        exact upper_endpoint_mass_eq_reflected_density_integral_of_pdf
          hpdf hf_nonneg hf_measurable hf_integrable hf_zero_above hx_pos)
      hratio k_pos

/--
Source Theorem 1(ii)'s equation-(6) endpoint under its literal PDF model.

The source writes a left-limit at the finite upper endpoint `M`.  Here `f` is
made into an actual nonnegative measurable Lebesgue density of the iid law,
and the displayed ratio is stated in that same left-limit form.  The
`withDensity` bridge derives the local integrability, reflected tail-mass
identity, and a.e. density vanishing above `M` internally.

The allocation theorem below additionally uses nonnegative item values, a
finite lower support endpoint `L`, a positive upper endpoint, and positive
support width.  Those are visible here rather than being inferred from the
source's phrase "bounded from above"; translating a merely upper-bounded law
to this normalization is not part of this endpoint.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_pdf_sequence_formula
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_finite_mean : MeasureTheory.Integrable (fun x : ℝ => x) baseMeasure)
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun x : ℝ => f x / ((M - x) ^ (beta - 1)))
        (nhdsWithin M (Set.Iio M)) (nhds c))
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) := by
  have hf_integrable : MeasureTheory.Integrable f :=
    integrable_pdf_of_probability hpdf hf_nonneg hf_measurable
  have hf_zero_above :
      f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi M)] fun _ => 0 :=
    pdf_zero_above_of_ae_upper_bound
      hpdf hf_nonneg hf_measurable h_base_bounds
  have hratio_normalized :
      Tendsto (fun x : ℝ => f x / (c * (M - x) ^ (beta - 1)))
        (nhdsWithin M (Set.Iio M)) (nhds (1 : ℝ)) := by
    have hnormal := hratio.div_const c
    have hfun :
        (fun x : ℝ => f x / ((M - x) ^ (beta - 1)) / c) =
          (fun x : ℝ => f x / (c * (M - x) ^ (beta - 1))) := by
      funext x
      simp only [div_eq_mul_inv]
      ring
    rw [hfun] at hnormal
    convert hnormal using 1
    field_simp [ne_of_gt hc_pos]
  have hratio_reflected :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)) := by
    have hsub :
        Tendsto (fun u : ℝ => M - u)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhdsWithin M (Set.Iio M)) := by
      have hcont :
          ContinuousWithinAt (fun u : ℝ => M - u) (Set.Ioi (0 : ℝ)) 0 :=
        (continuous_const.sub continuous_id).continuousAt.continuousWithinAt
      simpa using hcont.tendsto_nhdsWithin (t := Set.Iio M) (by
        intro u hu
        exact sub_lt_self M hu)
    have hcomp := hratio_normalized.comp hsub
    have heq :
        (fun x : ℝ => f x / (c * (M - x) ^ (beta - 1))) ∘
            (fun u : ℝ => M - u) =
          (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1))) := by
      funext u
      simp only [Function.comp_apply]
      have hsubsub : M - (M - u) = u := by ring
      rw [hsubsub]
    rw [heq] at hcomp
    exact hcomp
  exact
    paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_nonnegative_support
      baseMeasure h_base_bounds h_nonneg hM_pos
      (lemmaD2_reflected_cdf_power_sandwich_of_pdf
        hpdf hf_nonneg hf_measurable hf_integrable hf_zero_above
        hbeta_pos hc_pos hratio_reflected)
      likelihood hlike_pos k_pos hwidth_pos seq

end PRPKG24AccuracyDiversity

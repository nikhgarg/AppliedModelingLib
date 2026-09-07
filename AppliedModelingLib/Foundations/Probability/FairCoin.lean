import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open ProbabilityTheory

namespace AppliedModelingLib
namespace FairCoin

theorem measureReal_inter_ge_one_sub_add
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {P Q : Set α}
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    {epsP epsQ : ℝ}
    (hprobP : 1 - epsP ≤ μ.real P)
    (hprobQ : 1 - epsQ ≤ μ.real Q) :
    1 - epsP - epsQ ≤ μ.real (P ∩ Q) := by
  have hPcompl :
      μ.real Pᶜ ≤ epsP := by
    have hcompl :
        μ.real Pᶜ = 1 - μ.real P :=
      probReal_compl_eq_one_sub (μ := μ) hP
    linarith
  have hQcompl :
      μ.real Qᶜ ≤ epsQ := by
    have hcompl :
        μ.real Qᶜ = 1 - μ.real Q :=
      probReal_compl_eq_one_sub (μ := μ) hQ
    linarith
  have hbad :
      μ.real (Pᶜ ∪ Qᶜ) ≤ epsP + epsQ := by
    exact (measureReal_union_le (μ := μ) Pᶜ Qᶜ).trans
      (add_le_add hPcompl hQcompl)
  have hcompl_inter :
      μ.real (P ∩ Q)ᶜ = 1 - μ.real (P ∩ Q) :=
    probReal_compl_eq_one_sub (μ := μ) (hP.inter hQ)
  have hdeMorgan : (P ∩ Q)ᶜ = Pᶜ ∪ Qᶜ := by
    ext a
    by_cases hpa : a ∈ P <;> by_cases hqa : a ∈ Q <;> simp [hpa, hqa]
  have hbad_inter :
      μ.real (P ∩ Q)ᶜ ≤ epsP + epsQ := by
    rwa [hdeMorgan]
  linarith

theorem measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : ι → α → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset ι} {a b ε : ℝ}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    (hε : 0 ≤ ε) :
    μ.real
        {ω | ε ≤
          ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  let centered : ι → α → ℝ :=
    fun i ω => X i ω - ∫ x, X i x ∂μ
  have hcenter_indep : iIndepFun centered μ := by
    exact h_indep.comp
      (fun i x => x - ∫ y, X i y ∂μ)
      (fun _ => measurable_id.sub measurable_const)
  have hsub :
      ∀ i ∈ s,
        HasSubgaussianMGF
          (centered i)
          ((‖b - a‖₊ / 2) ^ 2) μ := by
    intro i hi
    exact hasSubgaussianMGF_of_mem_Icc (h_meas i hi) (h_bound i hi)
  simpa [centered] using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) hcenter_indep (s := s) hsub hε)

theorem measure_sum_half_mean_indicator_le_third_le_exp
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : ι → α → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset ι}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean_neg :
      ∀ i ∈ s, (∫ ω, (-X i ω) ∂μ) = -(1 / 2 : ℝ)) :
    μ.real
        {ω | (∑ i ∈ s, X i ω) ≤ (s.card : ℝ) / 3} ≤
      Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  let Y : ι → α → ℝ := fun i ω => -X i ω
  have hY_indep : iIndepFun Y μ := by
    exact h_indep.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hY_meas : ∀ i ∈ s, AEMeasurable (Y i) μ := by
    intro i hi
    exact (h_meas i hi).neg
  have hY_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1 : ℝ) 0 := by
    intro i hi
    filter_upwards [h_bound i hi] with ω hω
    exact ⟨by linarith [hω.2], by linarith [hω.1]⟩
  have htail :=
    measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (μ := μ) (X := Y) hY_indep (s := s)
      (a := (-1 : ℝ)) (b := 0) (ε := (s.card : ℝ) / 6)
      hY_meas hY_bound (by positivity)
  refine le_trans ?_ htail
  refine measureReal_mono (μ := μ) ?_ (measure_ne_top μ _)
  intro ω hω
  have hsum_eq :
      (∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ)) =
        (s.card : ℝ) / 2 - ∑ i ∈ s, X i ω := by
    calc
      (∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ))
          = ∑ i ∈ s, (-X i ω + (1 / 2 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hmean_neg i hi]
              simp [Y]
      _ = (s.card : ℝ) / 2 - ∑ i ∈ s, X i ω := by
              rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
              simp
              ring
  change (s.card : ℝ) / 3 ≥ ∑ i ∈ s, X i ω at hω
  change (s.card : ℝ) / 6 ≤
    ∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ)
  rw [hsum_eq]
  nlinarith

noncomputable def fairMeasure : Measure Bool :=
  ((PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure : Measure Bool)

noncomputable def productMeasure (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => fairMeasure)

theorem fairMeasure_isProbabilityMeasure : IsProbabilityMeasure fairMeasure := by
  simpa [fairMeasure] using
    (inferInstance : IsProbabilityMeasure (PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure)

theorem productMeasure_isProbabilityMeasure (ι : Type*) :
    IsProbabilityMeasure (productMeasure ι) := by
  let P : ι → Measure Bool := fun _ => fairMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairMeasure_isProbabilityMeasure
  simpa [productMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ

theorem indicator_iIndepFun
    {ι : Type*} (keep : Bool) :
    iIndepFun
      (fun i (side : ι → Bool) => if side i = keep then (1 : ℝ) else 0)
      (productMeasure ι) := by
  let P : ι → Measure Bool := fun _ => fairMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairMeasure_isProbabilityMeasure
  have hcoord :
      iIndepFun (fun i (side : ι → Bool) => side i)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := ι) (𝓧 := fun _ => Bool)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ => Bool) (mΩ := fun _ => by infer_instance)
        (P := P) hμ (X := fun i : ι => (fun b : Bool => b))
        (mX := fun _ => measurable_id)
  simpa [productMeasure, P] using hcoord.comp
    (fun _ b => if b = keep then (1 : ℝ) else 0)
    (fun _ => measurable_of_finite _)

theorem indicator_integral
    {ι : Type*} (i : ι) (keep : Bool) :
  (∫ side : ι → Bool,
        (if side i = keep then (1 : ℝ) else 0) ∂productMeasure ι) =
      1 / 2 := by
  let P : ι → Measure Bool := fun _ => fairMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairMeasure_isProbabilityMeasure
  haveI : IsProbabilityMeasure (Measure.infinitePi P) :=
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ
  let f : Bool → ℝ := fun b => if b = keep then 1 else 0
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun side : ι → Bool => side i)
          (productMeasure ι)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ side : ι → Bool,
        (if side i = keep then (1 : ℝ) else 0) ∂productMeasure ι)
        = ∫ side : ι → Bool, f (side i) ∂productMeasure ι := by rfl
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun side : ι → Bool => side i) (productMeasure ι) := by
        exact (integral_map
          (μ := productMeasure ι)
          (φ := fun side : ι → Bool => side i)
          (f := f) (measurable_pi_apply i).aemeasurable hf).symm
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun side : ι → Bool => side i) (Measure.infinitePi P) := by
      simp [productMeasure, P]
    _ = ∫ b : Bool, f b ∂fairMeasure := by
        rw [show
            (Measure.map (fun side : ι → Bool => side i) (Measure.infinitePi P))
              = fairMeasure from by
              simpa [P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := ι) (X := fun _ : ι => Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hμ i)]
    _ = 1 / 2 := by
        cases keep <;>
          simp [f, fairMeasure, PMF.integral_eq_sum, PMF.bernoulli]

theorem indicator_lower_tail_le_exp
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (productMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  haveI : IsProbabilityMeasure (productMeasure ι) :=
    productMeasure_isProbabilityMeasure ι
  refine measure_sum_half_mean_indicator_le_third_le_exp
    (μ := productMeasure ι)
    (X := fun i side => if side i = keep then (1 : ℝ) else 0)
    (indicator_iIndepFun keep)
    (s := s) ?_ ?_ ?_
  · intro i _hi
    exact ((measurable_of_finite
      (fun b : Bool => if b = keep then (1 : ℝ) else 0)).comp
        (measurable_pi_apply i)).aemeasurable
  · intro i _hi
    exact ae_of_all _ fun side => by
      by_cases h : side i = keep <;> simp [h]
  · intro i _hi
    rw [integral_neg]
    simp [indicator_integral i keep]

theorem indicator_lower_tail_le_exp_card
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (productMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp (-(s.card : ℝ) / 18) := by
  have hraw := indicator_lower_tail_le_exp s keep
  have hsum :
      ((∑ _i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ) =
        (s.card : ℝ) / 4 := by
    simp
    ring
  have hexp :
      -((s.card : ℝ) / 6) ^ 2 / (2 * ((s.card : ℝ) / 4)) =
        -(s.card : ℝ) / 18 := by
    by_cases hcard : s.card = 0
    · simp [hcard]
    · have hcard_ne : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast hcard
      field_simp [hcard_ne]
      ring
  rw [hsum] at hraw
  simpa [hexp] using hraw

theorem indicator_lower_tail_le_exp_card_relaxed
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (productMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp (-(s.card : ℝ) / 36) := by
  exact le_trans (indicator_lower_tail_le_exp_card s keep)
    (Real.exp_le_exp.mpr (by
      have hnonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
      nlinarith))

end FairCoin
end AppliedModelingLib

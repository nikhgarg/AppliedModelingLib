import KR21Monoculture.W11FiniteProduct
import KR21Monoculture.W11ScoreTransport
import KR21Monoculture.W11SourceLawTransport
import Mathlib.MeasureTheory.Integral.Pi

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-!
# Arbitrary finite score cells for the corrected Theorem 5 route

The concrete two-, three-, and four-candidate modules establish the first
instances of this construction.  This module lifts the score-density `L¹`
curve to every finite `Candidate n = Fin (n + 2)` carrier.  It uses the
canonical finite product volume on functions and an explicit, measure-
preserving last-coordinate split; no dominated-differentiation certificate is
an input.
-/

/-- Transport a density through a measure-preserving measurable equivalence. -/
private theorem map_withDensity_eq_withDensity_comp_symm
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (he : MeasurePreserving e μ ν) (density : α → ℝ≥0∞) :
    (μ.withDensity density).map e = ν.withDensity (density ∘ e.symm) := by
  ext s hs
  calc
    (μ.withDensity density).map e s =
        ∫⁻ x in e ⁻¹' s, density x ∂μ := by
      rw [e.map_apply, withDensity_apply density
        (e.measurableSet_preimage.mpr hs)]
    _ = ∫⁻ y in s, (density ∘ e.symm) y ∂ν := by
      simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
        he.setLIntegral_comp_preimage_emb e.measurableEmbedding
          (fun y => density (e.symm y)) s
    _ = (ν.withDensity (density ∘ e.symm)) s := by
      rw [withDensity_apply _ hs]

private noncomputable def w11CandidateLastSplit (n : ℕ) :
    (Candidate (n + 1) → ℝ) ≃ᵐ (ℝ × (Candidate n → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 3) => ℝ) (Fin.last (n + 2))

private theorem w11CandidateLastSplit_measurePreserving (n : ℕ) :
    MeasurePreserving (w11CandidateLastSplit n) := by
  unfold w11CandidateLastSplit
  simpa only [Candidate] using
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 3) => ℝ) (Fin.last (n + 2))

private def w11CandidateInitValue {n : ℕ}
    (value : Candidate (n + 1) → ℝ) : Candidate n → ℝ :=
  fun i => value (Fin.castSucc i)

private theorem w11CandidateLastSplit_snd_apply {n : ℕ}
    (z : Candidate (n + 1) → ℝ) (i : Candidate n) :
    (w11CandidateLastSplit n z).2 i = z (Fin.castSucc i) := by
  simp [w11CandidateLastSplit, Fin.init_def]

private theorem w11CandidateLastSplit_fst_apply {n : ℕ}
    (z : Candidate (n + 1) → ℝ) :
    (w11CandidateLastSplit n z).1 = z (Fin.last (n + 2)) := by
  simp [w11CandidateLastSplit]

/-- The finite candidate score-density curve represented in `L¹`. -/
noncomputable def w11CandidateScoreDensityL1 :
    (n : ℕ) → (f : ℝ → ℝ) → Integrable f volume →
      (value : Candidate n → ℝ) → ℝ → (Candidate n → ℝ) →₁[volume] ℝ
  | 0, f, hf, value, theta =>
      Lp.compMeasurePreserving
        (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ)
        (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
        (l1ExternalProduct
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
          (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
  | n + 1, f, hf, value, theta =>
      Lp.compMeasurePreserving
        (w11CandidateLastSplit n)
        (w11CandidateLastSplit_measurePreserving n)
        (l1ExternalProduct
          (scoreTranslateL1 (theta * value (Fin.last (n + 2))) (hf.toL1 f))
          (w11CandidateScoreDensityL1 n f hf (w11CandidateInitValue value) theta))

/-- The pointwise iid score density on the canonical finite function carrier. -/
def w11CandidateScoreDensity {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (theta : ℝ) (score : Candidate n → ℝ) : ℝ :=
  ∏ i : Candidate n, f (score i - theta * value i)

private theorem w11CandidateScoreDensity_zero_split
    (f : ℝ → ℝ) (value : Candidate 0 → ℝ) (theta : ℝ)
    (score : Candidate 0 → ℝ) :
    w11CandidateScoreDensity f value theta score =
      f (((MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) score).1 - theta * value 0) *
        f (((MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) score).2 - theta * value 1) := by
  rw [w11CandidateScoreDensity, Fin.prod_univ_two]
  rfl

private theorem w11CandidateScoreDensity_succ_split {n : ℕ}
    (f : ℝ → ℝ) (value : Candidate (n + 1) → ℝ) (theta : ℝ)
    (score : Candidate (n + 1) → ℝ) :
    w11CandidateScoreDensity f value theta score =
      w11CandidateScoreDensity f (w11CandidateInitValue value) theta
        (w11CandidateLastSplit n score).2 *
        f ((w11CandidateLastSplit n score).1 - theta * value (Fin.last (n + 2))) := by
  rw [w11CandidateScoreDensity, Fin.prod_univ_castSucc]
  change
    (∏ i, f (score (Fin.castSucc i) - theta * value (Fin.castSucc i))) *
        f (score (Fin.last (n + 2)) - theta * value (Fin.last (n + 2))) =
      (∏ i, f ((w11CandidateLastSplit n score).2 i -
        theta * w11CandidateInitValue value i)) *
        f ((w11CandidateLastSplit n score).1 - theta * value (Fin.last (n + 2)))
  rw [w11CandidateLastSplit_fst_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [w11CandidateLastSplit_snd_apply]
  rfl

/--
The explicit finite iid score density agrees almost everywhere with the
recursive `L¹` representative.  The result is proved by the same
last-coordinate product split used for the derivative, so the carrier
identification is a checked measure-preserving equivalence rather than an
implicit finite-dimensional convention.
-/
theorem w11CandidateScoreDensity_ae_eq_l1
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate n → ℝ) (theta : ℝ) :
    w11CandidateScoreDensity f value theta =ᵐ[volume]
      w11CandidateScoreDensityL1 n f hf value theta := by
  induction n with
  | zero =>
      let e : (Candidate 0 → ℝ) ≃ᵐ (ℝ × ℝ) :=
        MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ
      let hmeasure : MeasurePreserving e :=
        volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
      let left : ℝ →₁[volume] ℝ :=
        scoreTranslateL1 (theta * value 0) (hf.toL1 f)
      let right : ℝ →₁[volume] ℝ :=
        scoreTranslateL1 (theta * value 1) (hf.toL1 f)
      have htransport :
          w11CandidateScoreDensityL1 0 f hf value theta =ᵐ[volume]
            fun score => l1ExternalProduct left right (e score) := by
        exact Lp.coeFn_compMeasurePreserving (l1ExternalProduct left right) hmeasure
      have hproduct :
          (fun score => l1ExternalProduct left right (e score)) =ᵐ[volume]
            fun score => left (e score).1 * right (e score).2 := by
        simpa only [Function.comp_apply] using
          hmeasure.quasiMeasurePreserving.ae_eq_comp
            (l1ExternalProduct_ae_eq left right)
      have hleft : left =ᵐ[volume]
          fun x => f (x - theta * value 0) := by
        have htranslate := scoreTranslateL1_ae_eq (theta * value 0) (hf.toL1 f)
        have hbase :
            (fun x => (hf.toL1 f) (x - theta * value 0)) =ᵐ[volume]
              fun x => f (x - theta * value 0) := by
          simpa only [Function.comp_apply] using
            (measurePreserving_sub_right volume (theta * value 0)).quasiMeasurePreserving.ae_eq_comp
              hf.coeFn_toL1
        exact htranslate.trans hbase
      have hright : right =ᵐ[volume]
          fun x => f (x - theta * value 1) := by
        have htranslate := scoreTranslateL1_ae_eq (theta * value 1) (hf.toL1 f)
        have hbase :
            (fun x => (hf.toL1 f) (x - theta * value 1)) =ᵐ[volume]
              fun x => f (x - theta * value 1) := by
          simpa only [Function.comp_apply] using
            (measurePreserving_sub_right volume (theta * value 1)).quasiMeasurePreserving.ae_eq_comp
              hf.coeFn_toL1
        exact htranslate.trans hbase
      have hleft_pull :
          (fun score : Candidate 0 → ℝ => left (score 0)) =ᵐ[volume]
            fun score => f (score 0 - theta * value 0) :=
        by
          simpa only [Function.comp_apply] using
            (Measure.quasiMeasurePreserving_eval
              (fun _ : Candidate 0 => (volume : Measure ℝ)) 0).ae_eq_comp
              hleft
      have hright_pull :
          (fun score : Candidate 0 → ℝ => right (score 1)) =ᵐ[volume]
            fun score => f (score 1 - theta * value 1) :=
        by
          simpa only [Function.comp_apply] using
            (Measure.quasiMeasurePreserving_eval
              (fun _ : Candidate 0 => (volume : Measure ℝ)) 1).ae_eq_comp
              hright
      filter_upwards [htransport, hproduct, hleft_pull, hright_pull] with
          score htransport hproduct hleft hright
      calc
        w11CandidateScoreDensity f value theta score =
            f ((e score).1 - theta * value 0) *
              f ((e score).2 - theta * value 1) := by
          simpa [e] using w11CandidateScoreDensity_zero_split f value theta score
        _ = left (e score).1 * right (e score).2 := by
          simpa [e] using congrArg₂ (· * ·) hleft.symm hright.symm
        _ = l1ExternalProduct left right (e score) := hproduct.symm
        _ = w11CandidateScoreDensityL1 0 f hf value theta score := htransport.symm
  | succ n ih =>
      let e : (Candidate (n + 1) → ℝ) ≃ᵐ (ℝ × (Candidate n → ℝ)) :=
        w11CandidateLastSplit n
      let hmeasure : MeasurePreserving e := w11CandidateLastSplit_measurePreserving n
      let left : ℝ →₁[volume] ℝ :=
        scoreTranslateL1 (theta * value (Fin.last (n + 2))) (hf.toL1 f)
      let right : (Candidate n → ℝ) →₁[volume] ℝ :=
        w11CandidateScoreDensityL1 n f hf (w11CandidateInitValue value) theta
      have htransport :
          w11CandidateScoreDensityL1 (n + 1) f hf value theta =ᵐ[volume]
            fun score => l1ExternalProduct left right (e score) := by
        exact Lp.coeFn_compMeasurePreserving (l1ExternalProduct left right) hmeasure
      have hproduct :
          (fun score => l1ExternalProduct left right (e score)) =ᵐ[volume]
            fun score => left (e score).1 * right (e score).2 := by
        simpa only [Function.comp_apply] using
          hmeasure.quasiMeasurePreserving.ae_eq_comp
            (l1ExternalProduct_ae_eq left right)
      have hinit :
          w11CandidateScoreDensity f (w11CandidateInitValue value) theta =ᵐ[volume]
            right := ih (w11CandidateInitValue value)
      have hsnd_measure :
          Measure.QuasiMeasurePreserving
            (fun score : Candidate (n + 1) → ℝ => (e score).2)
            volume volume := by
        exact MeasureTheory.Measure.quasiMeasurePreserving_snd.comp
          hmeasure.quasiMeasurePreserving
      have hinit_pull :
          (fun score : Candidate (n + 1) → ℝ =>
            w11CandidateScoreDensity f (w11CandidateInitValue value) theta (e score).2) =ᵐ[
              volume]
            fun score => right (e score).2 :=
        by
          simpa only [Function.comp_apply] using hsnd_measure.ae_eq_comp hinit
      have hleft : left =ᵐ[volume]
          fun x => f (x - theta * value (Fin.last (n + 2))) := by
        have htranslate := scoreTranslateL1_ae_eq
          (theta * value (Fin.last (n + 2))) (hf.toL1 f)
        have hbase :
            (fun x => (hf.toL1 f) (x - theta * value (Fin.last (n + 2)))) =ᵐ[volume]
              fun x => f (x - theta * value (Fin.last (n + 2))) := by
          simpa only [Function.comp_apply] using
            (measurePreserving_sub_right volume (theta * value (Fin.last (n + 2)))
              ).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1
        exact htranslate.trans hbase
      have hlast_pull :
          (fun score : Candidate (n + 1) → ℝ => left (score (Fin.last (n + 2)))) =ᵐ[
              volume]
            fun score => f (score (Fin.last (n + 2)) - theta * value (Fin.last (n + 2))) :=
        by
          simpa only [Function.comp_apply] using
            (Measure.quasiMeasurePreserving_eval
              (fun _ : Candidate (n + 1) => (volume : Measure ℝ))
              (Fin.last (n + 2))).ae_eq_comp hleft
      filter_upwards [htransport, hproduct, hinit_pull, hlast_pull] with
          score htransport hproduct hinit hlast
      calc
        w11CandidateScoreDensity f value theta score =
            w11CandidateScoreDensity f (w11CandidateInitValue value) theta (e score).2 *
              f ((e score).1 - theta * value (Fin.last (n + 2))) := by
          simpa [e] using w11CandidateScoreDensity_succ_split f value theta score
        _ = right (e score).2 * left (e score).1 := by
          rw [hinit]
          rw [show (e score).1 = score (Fin.last (n + 2)) by simp [e,
            w11CandidateLastSplit_fst_apply]]
          rw [← hlast]
        _ = left (e score).1 * right (e score).2 := by ring
        _ = l1ExternalProduct left right (e score) := hproduct.symm
        _ = w11CandidateScoreDensityL1 (n + 1) f hf value theta score := htransport.symm

/-- The nonnegative extended-real density associated with the finite iid score density. -/
noncomputable def w11CandidateScoreDensityENN {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (theta : ℝ) : (Candidate n → ℝ) → ℝ≥0∞ :=
  fun score => ENNReal.ofReal (w11CandidateScoreDensity f value theta score)

/-- The arbitrary-finite corrected score law before normalization is discharged. -/
noncomputable def w11CandidateScoreLaw {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (theta : ℝ) : Measure (Candidate n → ℝ) :=
  volume.withDensity (w11CandidateScoreDensityENN f value theta)

/-- The explicit arbitrary-finite score density is measurable when the base density is measurable. -/
theorem measurable_w11CandidateScoreDensity {n : ℕ}
    (f : ℝ → ℝ) (hf : Measurable f) (value : Candidate n → ℝ) (theta : ℝ) :
    Measurable (w11CandidateScoreDensity f value theta) := by
  unfold w11CandidateScoreDensity
  apply Finset.measurable_fun_prod
  intro i _
  exact hf.comp ((measurable_pi_apply i).sub measurable_const)

/-- The corresponding extended-real density is measurable. -/
theorem measurable_w11CandidateScoreDensityENN {n : ℕ}
    (f : ℝ → ℝ) (hf : Measurable f) (value : Candidate n → ℝ) (theta : ℝ) :
    Measurable (w11CandidateScoreDensityENN f value theta) := by
  simpa [w11CandidateScoreDensityENN] using
    (measurable_w11CandidateScoreDensity f hf value theta).ennreal_ofReal

/-- The finite score law is the finite product of its translated coordinate laws. -/
private theorem w11CandidateScoreLaw_eq_pi_translatedNoiseLaw
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (hf_measurable : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (value : Candidate n → ℝ) (theta : ℝ) :
    w11CandidateScoreLaw f value theta =
      Measure.pi (fun i : Candidate n =>
        w11TranslatedNoiseLaw f (theta * value i)) := by
  induction n with
  | zero =>
      let e : (Candidate 0 → ℝ) ≃ᵐ (ℝ × ℝ) :=
        MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ
      let hmeasure : MeasurePreserving e :=
        volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
      letI : ∀ i : Candidate 0,
          IsFiniteMeasure (w11TranslatedNoiseLaw f (theta * value i)) := fun i => by
        unfold w11TranslatedNoiseLaw
        exact MeasureTheory.isFiniteMeasure_withDensity_ofReal
          (hf.comp_sub_right (theta * value i)).hasFiniteIntegral
      apply (MeasurableEquiv.map_measurableEquiv_injective e)
      calc
        (w11CandidateScoreLaw f value theta).map e =
            (volume.prod volume).withDensity
              (w11CandidateScoreDensityENN f value theta ∘ e.symm) := by
          exact map_withDensity_eq_withDensity_comp_symm e volume (volume.prod volume)
            hmeasure (w11CandidateScoreDensityENN f value theta)
        _ = (w11TranslatedNoiseLaw f (theta * value 0)).prod
              (w11TranslatedNoiseLaw f (theta * value 1)) := by
          let g0 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 0))
          let g1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 1))
          have hg0 : Measurable g0 := by
            exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
          have hg1 : Measurable g1 := by
            exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
          change
            (volume.prod volume).withDensity
              (w11CandidateScoreDensityENN f value theta ∘ e.symm) =
              (volume.withDensity g0).prod (volume.withDensity g1)
          rw [prod_withDensity hg0 hg1]
          congr 1
          funext z
          change
            ENNReal.ofReal (w11CandidateScoreDensity f value theta (e.symm z)) =
              g0 z.1 * g1 z.2
          rw [w11CandidateScoreDensity_zero_split]
          simp [e]
          rw [ENNReal.ofReal_mul (h_nonnegative _)]
        _ = (Measure.pi (fun i : Candidate 0 =>
              w11TranslatedNoiseLaw f (theta * value i))).map e := by
          symm
          simpa [e, Candidate] using
            (measurePreserving_piFinTwo
              (fun i : Candidate 0 => w11TranslatedNoiseLaw f (theta * value i))).map_eq
  | succ n ih =>
      let e : (Candidate (n + 1) → ℝ) ≃ᵐ (ℝ × (Candidate n → ℝ)) :=
        w11CandidateLastSplit n
      let hmeasure : MeasurePreserving e := w11CandidateLastSplit_measurePreserving n
      let initValue : Candidate n → ℝ := w11CandidateInitValue value
      let shift : ℝ := theta * value (Fin.last (n + 2))
      letI : ∀ i : Candidate (n + 1),
          IsFiniteMeasure (w11TranslatedNoiseLaw f (theta * value i)) := fun i => by
        unfold w11TranslatedNoiseLaw
        exact MeasureTheory.isFiniteMeasure_withDensity_ofReal
          (hf.comp_sub_right (theta * value i)).hasFiniteIntegral
      apply (MeasurableEquiv.map_measurableEquiv_injective e)
      calc
        (w11CandidateScoreLaw f value theta).map e =
            (volume.prod volume).withDensity
              (w11CandidateScoreDensityENN f value theta ∘ e.symm) := by
          exact map_withDensity_eq_withDensity_comp_symm e volume (volume.prod volume)
            hmeasure (w11CandidateScoreDensityENN f value theta)
        _ = (w11TranslatedNoiseLaw f shift).prod
              (w11CandidateScoreLaw f initValue theta) := by
          let glast : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - shift))
          let ginit : (Candidate n → ℝ) → ℝ≥0∞ :=
            w11CandidateScoreDensityENN f initValue theta
          have hglast : Measurable glast := by
            exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
          have hginit : Measurable ginit :=
            measurable_w11CandidateScoreDensityENN f hf_measurable initValue theta
          change
            (volume.prod volume).withDensity
              (w11CandidateScoreDensityENN f value theta ∘ e.symm) =
              (volume.withDensity glast).prod (volume.withDensity ginit)
          rw [prod_withDensity hglast hginit]
          congr 1
          funext z
          change
            ENNReal.ofReal (w11CandidateScoreDensity f value theta (e.symm z)) =
              glast z.1 * ginit z.2
          rw [w11CandidateScoreDensity_succ_split]
          simp [e]
          rw [ENNReal.ofReal_mul (by
            unfold w11CandidateScoreDensity
            exact Finset.prod_nonneg fun i _ => h_nonnegative _)]
          rw [mul_comm]
          rfl
        _ = (w11TranslatedNoiseLaw f shift).prod
              (Measure.pi (fun i : Candidate n =>
                w11TranslatedNoiseLaw f (theta * initValue i))) := by
          rw [ih initValue]
        _ = (Measure.pi (fun i : Candidate (n + 1) =>
              w11TranslatedNoiseLaw f (theta * value i))).map e := by
          symm
          simpa [e, w11CandidateLastSplit, initValue, shift, w11CandidateInitValue, Candidate] using
            (measurePreserving_piFinSuccAbove
              (fun i : Candidate (n + 1) =>
                w11TranslatedNoiseLaw f (theta * value i))
              (Fin.last (n + 2))).map_eq

/-- Independent source-noise draws on the arbitrary finite candidate carrier. -/
noncomputable def w11CandidateNoiseLaw {n : ℕ} (f : ℝ → ℝ) :
    Measure (Candidate n → ℝ) :=
  Measure.pi (fun _ : Candidate n => w11BaseNoiseLaw f)

/-- Normalized independent source-noise coordinates form an actual probability law. -/
theorem w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
    (n : ℕ) (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  unfold w11CandidateNoiseLaw
  infer_instance

/-- Add the deterministic value-dependent score shift to every source-noise coordinate. -/
def w11CandidateAdditiveScoreMap {n : ℕ}
    (value : Candidate n → ℝ) (theta : ℝ) :
    (Candidate n → ℝ) → Candidate n → ℝ :=
  fun noise i => noise i + theta * value i

/-- The arbitrary finite additive score map is measurable. -/
theorem measurable_w11CandidateAdditiveScoreMap {n : ℕ}
    (value : Candidate n → ℝ) (theta : ℝ) :
    Measurable (w11CandidateAdditiveScoreMap value theta) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).add measurable_const

/--
The arbitrary finite corrected score law is the pushforward of independent
source-noise draws under the displayed coordinatewise additive score map.
-/
theorem w11CandidateScoreLaw_eq_map_w11CandidateNoiseLaw
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (hf_measurable : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (value : Candidate n → ℝ) (theta : ℝ) :
    w11CandidateScoreLaw f value theta =
      (w11CandidateNoiseLaw f).map (w11CandidateAdditiveScoreMap value theta) := by
  letI : IsFiniteMeasure (w11BaseNoiseLaw f) := by
    unfold w11BaseNoiseLaw
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  calc
    w11CandidateScoreLaw f value theta =
        Measure.pi (fun i : Candidate n =>
          w11TranslatedNoiseLaw f (theta * value i)) :=
      w11CandidateScoreLaw_eq_pi_translatedNoiseLaw
        n f hf hf_measurable h_nonnegative value theta
    _ = Measure.pi (fun i : Candidate n =>
          (w11BaseNoiseLaw f).map (fun x : ℝ => x + theta * value i)) := by
      congr 1
      funext i
      symm
      exact w11BaseNoiseLaw_map_addRight_eq_translatedNoiseLaw
        f hf h_nonnegative (theta * value i)
    _ = (Measure.pi (fun _ : Candidate n => w11BaseNoiseLaw f)).map
          (fun noise i => noise i + theta * value i) := by
      symm
      exact Measure.pi_map_pi fun i =>
        (measurable_id.add measurable_const).aemeasurable
    _ = (w11CandidateNoiseLaw f).map
          (w11CandidateAdditiveScoreMap value theta) := rfl

/-- Pointwise nonnegativity of the finite score density follows from the base density. -/
theorem w11CandidateScoreDensity_nonneg {n : ℕ}
    (f : ℝ → ℝ) (h_nonnegative : ∀ x, 0 ≤ f x)
    (value : Candidate n → ℝ) (theta : ℝ) (score : Candidate n → ℝ) :
    0 ≤ w11CandidateScoreDensity f value theta score := by
  unfold w11CandidateScoreDensity
  exact Finset.prod_nonneg fun i _ => h_nonnegative _

/-- The finite iid score density is integrable under the base `L¹` hypothesis. -/
theorem integrable_w11CandidateScoreDensity {n : ℕ}
    (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate n → ℝ) (theta : ℝ) :
    Integrable (w11CandidateScoreDensity f value theta) volume := by
  unfold w11CandidateScoreDensity
  exact Integrable.fintype_prod fun i => hf.comp_sub_right (theta * value i)

/-- The explicit finite iid score law is probabilistic under base-density normalization. -/
theorem w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (theta : ℝ) :
    IsProbabilityMeasure (w11CandidateScoreLaw f value theta) := by
  have hbase_integral : ∫ x, f x = 1 := by
    apply ENNReal.ofReal_eq_one.mp
    calc
      ENNReal.ofReal (∫ x, f x ∂volume) =
          ∫⁻ x, ENNReal.ofReal (f x) ∂volume := by
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf
          (Filter.Eventually.of_forall h_nonnegative)
      _ = 1 := hnormalized
  have hshift_integral (i : Candidate n) :
      ∫ x, f (x - theta * value i) ∂volume = 1 := by
    calc
      ∫ x, f (x - theta * value i) ∂volume = ∫ x, f x ∂volume := by
        simpa only [Function.comp_apply] using
          (measurePreserving_sub_right volume (theta * value i)).integral_comp
            (measurableEmbedding_subRight (theta * value i)) f
      _ = 1 := hbase_integral
  have hscore_integral :
      ∫ score, w11CandidateScoreDensity f value theta score ∂volume = 1 := by
    let g : Candidate n → ℝ → ℝ := fun i x => f (x - theta * value i)
    unfold w11CandidateScoreDensity
    change
      ∫ score : Candidate n → ℝ,
        ∏ i : Candidate n, g i (score i)
          ∂Measure.pi (fun _ : Candidate n => (volume : Measure ℝ)) = 1
    rw [integral_fintype_prod_eq_prod g]
    simp only [g, hshift_integral, Finset.prod_const, one_pow]
  have hdensity_integrable :
      Integrable (w11CandidateScoreDensity f value theta) volume :=
    integrable_w11CandidateScoreDensity f hf value theta
  have hlintegral :
      ∫⁻ score, w11CandidateScoreDensityENN f value theta score ∂volume = 1 := by
    calc
      ∫⁻ score, w11CandidateScoreDensityENN f value theta score ∂volume =
          ENNReal.ofReal (∫ score, w11CandidateScoreDensity f value theta score ∂volume) := by
        symm
        simpa only [w11CandidateScoreDensityENN] using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdensity_integrable
            (Filter.Eventually.of_forall fun score =>
              w11CandidateScoreDensity_nonneg f h_nonnegative value theta score))
      _ = 1 := by rw [hscore_integral]; simp
  unfold w11CandidateScoreLaw
  exact isProbabilityMeasure_withDensity_of_lintegral_eq_one volume
    (w11CandidateScoreDensityENN f value theta) hlintegral

/--
Every finite iid score-density curve is differentiable in `L¹` under the
global corrected `W^{1,1}` hypotheses.  The proof is an induction over the
candidate carrier: the last score coordinate is split by a measure-preserving
finite-product equivalence, and the binary bounded bilinear `L¹` product map
propagates differentiability.
-/
theorem w11CandidateScoreDensityL1_differentiableAt_of_global_W11
    (n : ℕ) (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate n → ℝ) (theta : ℝ) :
    DifferentiableAt ℝ (w11CandidateScoreDensityL1 n f hf value) theta := by
  induction n with
  | zero =>
      have h0 : DifferentiableAt ℝ
          (fun t => scoreTranslateL1 (t * value 0) (hf.toL1 f)) theta :=
        (scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
          absolute_continuity derivative_ae_eq theta (value 0)).differentiableAt
      have h1 : DifferentiableAt ℝ
          (fun t => scoreTranslateL1 (t * value 1) (hf.toL1 f)) theta :=
        (scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
          absolute_continuity derivative_ae_eq theta (value 1)).differentiableAt
      have hproduct : DifferentiableAt ℝ
          (fun t => l1ExternalProduct
            (scoreTranslateL1 (t * value 0) (hf.toL1 f))
            (scoreTranslateL1 (t * value 1) (hf.toL1 f))) theta := by
        exact
          (isBoundedBilinearMap_l1ExternalProduct.differentiableAt _).comp theta
            (h0.prodMk h1)
      exact
        (ContinuousLinearMap.differentiableAt
          ((Lp.compMeasurePreservingₗᵢ ℝ
          (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ)
          (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).toContinuousLinearMap)).comp
          theta hproduct
  | succ n ih =>
      have hlast : DifferentiableAt ℝ
          (fun t => scoreTranslateL1
            (t * value (Fin.last (n + 2))) (hf.toL1 f)) theta :=
        (scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
          absolute_continuity derivative_ae_eq theta
          (value (Fin.last (n + 2)))).differentiableAt
      have hinit : DifferentiableAt ℝ
          (w11CandidateScoreDensityL1 n f hf (w11CandidateInitValue value)) theta :=
        ih (w11CandidateInitValue value)
      have hproduct : DifferentiableAt ℝ
          (fun t => l1ExternalProduct
            (scoreTranslateL1
              (t * value (Fin.last (n + 2))) (hf.toL1 f))
            (w11CandidateScoreDensityL1 n f hf (w11CandidateInitValue value) t)) theta := by
        exact
          (isBoundedBilinearMap_l1ExternalProduct.differentiableAt _).comp theta
            (hlast.prodMk hinit)
      exact
        (ContinuousLinearMap.differentiableAt
          ((Lp.compMeasurePreservingₗᵢ ℝ (w11CandidateLastSplit n)
          (w11CandidateLastSplit_measurePreserving n)).toContinuousLinearMap)
          ).comp theta hproduct

/-- The fixed score-space event selecting a ranking on an arbitrary finite candidate carrier. -/
noncomputable def w11CandidateRankingEvent {n : ℕ} (pi : Ranking n) :
    Set (Candidate n → ℝ) :=
  {score | rankByScore score = pi}

/-- Fixed arbitrary-finite score-ranking cells are measurable. -/
theorem measurableSet_w11CandidateRankingEvent {n : ℕ} (pi : Ranking n) :
    MeasurableSet (w11CandidateRankingEvent pi) := by
  exact measurableSet_rankByScore_eq (fun score : Candidate n → ℝ => score)
    (fun i => measurable_pi_apply i) pi

/-- Integration over an arbitrary score-space event, bundled as a bounded `L¹` functional. -/
noncomputable def w11CandidateSetIntegralCLM {n : ℕ}
    (s : Set (Candidate n → ℝ)) :
    ((Candidate n → ℝ) →₁[volume] ℝ) →L[ℝ] ℝ :=
  L1.integralCLM.comp
    (LpToLpRestrictCLM (Candidate n → ℝ) ℝ ℝ volume 1 s)

theorem w11CandidateSetIntegralCLM_apply {n : ℕ}
    (s : Set (Candidate n → ℝ)) (z : (Candidate n → ℝ) →₁[volume] ℝ) :
    w11CandidateSetIntegralCLM s z = ∫ score in s, z score := by
  rw [w11CandidateSetIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  apply integral_congr_ae
  exact LpToLpRestrictCLM_coeFn ℝ s z

/-- The corrected arbitrary-finite score-ranking atom, represented by its `L¹` density curve. -/
noncomputable def w11CandidateScoreL1RankingAtom
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) : ℝ :=
  w11CandidateSetIntegralCLM (w11CandidateRankingEvent pi)
    (w11CandidateScoreDensityL1 n f hf value theta)

/-- The actual measure-theoretic mass of a fixed arbitrary-finite score-ranking cell. -/
noncomputable def w11CandidateScoreLawRankingAtom
    (f : ℝ → ℝ) (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) : ℝ :=
  (w11CandidateScoreLaw f value theta).real (w11CandidateRankingEvent pi)

/--
The actual arbitrary-finite score-law atom equals the fixed-event integral of
the checked `L¹` density representative.  Nonnegativity is explicit because
the law is represented by an `ofReal` density.
-/
theorem w11CandidateScoreLawRankingAtom_eq_scoreL1Atom
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) :
    w11CandidateScoreLawRankingAtom f value pi theta =
      w11CandidateScoreL1RankingAtom n f hf value pi theta := by
  let s : Set (Candidate n → ℝ) := w11CandidateRankingEvent pi
  have hdensity_integrable :
      Integrable (w11CandidateScoreDensity f value theta) volume :=
    integrable_w11CandidateScoreDensity f hf value theta
  have hnonnegative_event :
      0 ≤ ∫ score in s, w11CandidateScoreDensity f value theta score := by
    apply integral_nonneg
    intro score
    exact w11CandidateScoreDensity_nonneg f h_nonnegative value theta score
  have hlintegral :
      ENNReal.ofReal (∫ score in s, w11CandidateScoreDensity f value theta score) =
        ∫⁻ score in s, w11CandidateScoreDensityENN f value theta score := by
    simpa only [w11CandidateScoreDensityENN, IntegrableOn] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict s) hdensity_integrable.integrableOn
        (Filter.Eventually.of_forall fun score =>
          w11CandidateScoreDensity_nonneg f h_nonnegative value theta score))
  calc
    w11CandidateScoreLawRankingAtom f value pi theta =
        ∫ score in s, w11CandidateScoreDensity f value theta score := by
      unfold w11CandidateScoreLawRankingAtom w11CandidateScoreLaw
      rw [Measure.real_def,
        withDensity_apply _ (measurableSet_w11CandidateRankingEvent pi), ← hlintegral]
      exact ENNReal.toReal_ofReal hnonnegative_event
    _ = w11CandidateScoreL1RankingAtom n f hf value pi theta := by
      unfold w11CandidateScoreL1RankingAtom
      rw [w11CandidateSetIntegralCLM_apply]
      apply setIntegral_congr_ae
      · exact measurableSet_w11CandidateRankingEvent pi
      · filter_upwards [w11CandidateScoreDensity_ae_eq_l1 n f hf value theta] with
          score hscore _
        exact hscore

/--
Every fixed arbitrary-finite score-ranking atom is differentiable under the
corrected global `W^{1,1}` hypotheses.  This result is obtained by composing
the finite `L¹` score-density derivative with a fixed-event bounded linear
functional; it has no pointwise domination premise.
-/
theorem w11CandidateScoreL1RankingAtom_differentiableAt_of_global_W11
    (n : ℕ) (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) :
    DifferentiableAt ℝ (w11CandidateScoreL1RankingAtom n f hf value pi) theta := by
  unfold w11CandidateScoreL1RankingAtom
  exact (w11CandidateSetIntegralCLM (w11CandidateRankingEvent pi)).differentiableAt.comp
    theta (w11CandidateScoreDensityL1_differentiableAt_of_global_W11
      n f derivative hf hderivative absolute_continuity derivative_ae_eq value theta)

/--
The actual arbitrary-finite corrected score-law mass of a fixed ranking cell
is differentiable under global `W^{1,1}` regularity.  The result applies to
the displayed density law itself, not merely to an abstract `L¹` curve.
-/
theorem w11CandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    (n : ℕ) (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) :
    DifferentiableAt ℝ (w11CandidateScoreLawRankingAtom f value pi) theta := by
  apply (w11CandidateScoreL1RankingAtom_differentiableAt_of_global_W11
    n f derivative hf hderivative absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => by
    exact (w11CandidateScoreLawRankingAtom_eq_scoreL1Atom
      n f hf h_nonnegative value pi t)

/-- The coordinatewise additive map has the source model's literal score-vector form. -/
theorem w11CandidateAdditiveScoreMap_eq_additiveScores {n : ℕ}
    (value : Candidate n → ℝ) (theta : ℝ) (noise : Candidate n → ℝ) :
    w11CandidateAdditiveScoreMap value theta noise =
      fun i => theta * value i + noise i := by
  funext i
  simp only [w11CandidateAdditiveScoreMap]
  ring

/-- The additive source-ranking cell is the literal preimage of the score-space cell. -/
theorem w11CandidateAdditiveRankingCell_eq_preimage {n : ℕ}
    (value : Candidate n → ℝ) (theta : ℝ) (pi : Ranking n) :
    {noise | rankByScore (fun i => theta * value i + noise i) = pi} =
      (w11CandidateAdditiveScoreMap value theta) ⁻¹'
        w11CandidateRankingEvent pi := by
  ext noise
  simp only [Set.mem_setOf_eq, Set.mem_preimage, w11CandidateRankingEvent]
  rw [w11CandidateAdditiveScoreMap_eq_additiveScores]

/-- The source-scaled-noise ranking atom on the arbitrary finite carrier. -/
noncomputable def w11CandidateScaledNoiseRankingAtom {n : ℕ}
    (f : ℝ → ℝ) (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) : ℝ :=
  (w11CandidateNoiseLaw f).real
    {noise | rankByScore (fun i => value i + noise i / theta) = pi}

/--
At positive accuracy, the actual arbitrary finite source-noise atom equals
the actual score-space-law atom.
-/
theorem w11CandidateScaledNoiseRankingAtom_eq_scoreLawRankingAtom
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f volume)
    (hf_measurable : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (value : Candidate n → ℝ) (pi : Ranking n) {theta : ℝ} (htheta : 0 < theta) :
    w11CandidateScaledNoiseRankingAtom f value pi theta =
      w11CandidateScoreLawRankingAtom f value pi theta := by
  have hscaled :
      {noise : Candidate n → ℝ |
        rankByScore (fun i => value i + noise i / theta) = pi} =
        {noise : Candidate n → ℝ |
          rankByScore (fun i => theta * value i + noise i) = pi} :=
    scaledNoiseRankingCell_preimage_eq_additiveScore value
      (fun noise : Candidate n → ℝ => noise) htheta pi
  unfold w11CandidateScaledNoiseRankingAtom w11CandidateScoreLawRankingAtom
  rw [hscaled, w11CandidateAdditiveRankingCell_eq_preimage,
    w11CandidateScoreLaw_eq_map_w11CandidateNoiseLaw
      n f hf hf_measurable h_nonnegative value theta]
  change
    ((w11CandidateNoiseLaw f)
      ((w11CandidateAdditiveScoreMap value theta) ⁻¹'
        w11CandidateRankingEvent pi)).toReal =
      ((Measure.map (w11CandidateAdditiveScoreMap value theta)
        (w11CandidateNoiseLaw f))
        (w11CandidateRankingEvent pi)).toReal
  rw [Measure.map_apply (measurable_w11CandidateAdditiveScoreMap value theta)
    (measurableSet_w11CandidateRankingEvent pi)]

/--
The arbitrary finite source-scaled-noise ranking atom is differentiable under
the corrected global `W^{1,1}` assumptions.
-/
theorem w11CandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
    (n : ℕ) (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate n → ℝ) (pi : Ranking n) {theta : ℝ} (htheta : 0 < theta) :
    DifferentiableAt ℝ (w11CandidateScaledNoiseRankingAtom f value pi) theta := by
  apply (w11CandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    n f derivative hf hderivative h_nonnegative absolute_continuity derivative_ae_eq
    value pi theta).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds htheta] with t ht
  exact w11CandidateScaledNoiseRankingAtom_eq_scoreLawRankingAtom
    n f hf hf_measurable h_nonnegative value pi ht

end KR21Monoculture

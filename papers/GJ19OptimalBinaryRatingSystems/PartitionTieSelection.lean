import GJ19OptimalBinaryRatingSystems.SourceTheorem31
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Set.Union

/-!
# Selection among value-maximizing interval partitions

The primary objective counts every pair separated by an interval boundary,
including the bottom-to-top pair. Coordinatewise maxima and minima of ordered
cutpoint vectors preserve the supermodular inequality for this objective.
-/

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open MeasureTheory Set Filter AppliedModelingLib.Probability
open scoped BigOperators Topology Classical

/-- A displayed boundary separates the lower and higher qualities. -/
def cutpointSeparatesPair {M : ℕ} (cut : Fin M → ℝ) (q : ℝ × ℝ) : Prop :=
  ∃ i, q.1 ≤ cut i ∧ cut i < q.2

/-- Separation under either partition persists under their meet or join. -/
theorem cutpointSeparatesPair_inf_or_sup {M : ℕ}
    (s t : Fin M → ℝ) (q : ℝ × ℝ)
    (h : cutpointSeparatesPair s q ∨ cutpointSeparatesPair t q) :
    cutpointSeparatesPair (s ⊓ t) q ∨ cutpointSeparatesPair (s ⊔ t) q := by
  rcases h with ⟨i, hlo, hhi⟩ | ⟨i, hlo, hhi⟩
  · rcases le_total (s i) (t i) with hle | hle
    · exact Or.inl ⟨i, by simpa [Pi.inf_apply, min_eq_left hle] using hlo,
        by simpa [Pi.inf_apply, min_eq_left hle] using hhi⟩
    · exact Or.inr ⟨i, by simpa [Pi.sup_apply, max_eq_left hle] using hlo,
        by simpa [Pi.sup_apply, max_eq_left hle] using hhi⟩
  · rcases le_total (s i) (t i) with hle | hle
    · exact Or.inr ⟨i, by simpa [Pi.sup_apply, max_eq_right hle] using hlo,
        by simpa [Pi.sup_apply, max_eq_right hle] using hhi⟩
    · exact Or.inl ⟨i, by simpa [Pi.inf_apply, min_eq_right hle] using hlo,
        by simpa [Pi.inf_apply, min_eq_right hle] using hhi⟩

/-- For ordered partitions, a pair separated by both remains separated by both. -/
theorem cutpointSeparatesPair_inf_and_sup {M : ℕ}
    (s t : Fin M → ℝ) (hs : Monotone s) (ht : Monotone t) (q : ℝ × ℝ)
    (hqs : cutpointSeparatesPair s q) (hqt : cutpointSeparatesPair t q) :
    cutpointSeparatesPair (s ⊓ t) q ∧ cutpointSeparatesPair (s ⊔ t) q := by
  rcases hqs with ⟨i, hsi, hsi'⟩
  rcases hqt with ⟨j, htj, htj'⟩
  rcases le_total i j with hij | hji
  · constructor
    · exact ⟨j, le_min (hsi.trans (hs hij)) htj,
        (min_le_right _ _).trans_lt htj'⟩
    · exact ⟨i, hsi.trans (le_max_left _ _),
        max_lt hsi' ((ht hij).trans_lt htj')⟩
  · constructor
    · exact ⟨i, le_min hsi (htj.trans (ht hji)),
        (min_le_left _ _).trans_lt hsi'⟩
    · exact ⟨j, htj.trans (le_max_right _ _),
        max_lt ((hs hji).trans_lt hsi') htj'⟩

/-- The separation indicator is supermodular in ordered cutpoints. -/
theorem cutpointSeparatesPair_indicator_supermodular {M : ℕ}
    (s t : Fin M → ℝ) (hs : Monotone s) (ht : Monotone t) (q : ℝ × ℝ) :
    (if cutpointSeparatesPair s q then (1 : ℝ) else 0) +
        (if cutpointSeparatesPair t q then (1 : ℝ) else 0) ≤
      (if cutpointSeparatesPair (s ⊓ t) q then (1 : ℝ) else 0) +
        (if cutpointSeparatesPair (s ⊔ t) q then (1 : ℝ) else 0) := by
  classical
  by_cases hqs : cutpointSeparatesPair s q
  · by_cases hqt : cutpointSeparatesPair t q
    · obtain ⟨hmin, hmax⟩ := cutpointSeparatesPair_inf_and_sup s t hs ht q hqs hqt
      simp [hqs, hqt, hmin, hmax]
    · have h := cutpointSeparatesPair_inf_or_sup s t q (Or.inl hqs)
      rcases h with h | h <;> simp [hqs, hqt, h] <;> split_ifs <;> norm_num
  · by_cases hqt : cutpointSeparatesPair t q
    · have h := cutpointSeparatesPair_inf_or_sup s t q (Or.inr hqt)
      rcases h with h | h <;> simp [hqs, hqt, h] <;> split_ifs <;> norm_num
    · simp [hqs, hqt]
      split_ifs <;> norm_num

/-- Nonnegative weighted separation value over the normalized quality square. -/
def cutpointSeparationValue {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (cut : Fin M → ℝ) : ℝ :=
  ∫ q in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    if cutpointSeparatesPair cut q then weight q else 0 ∂(volume.prod volume)

/-- The set of quality pairs separated by a finite cutpoint vector is measurable. -/
theorem measurableSet_cutpointSeparatesPair {M : ℕ} (cut : Fin M → ℝ) :
    MeasurableSet {q : ℝ × ℝ | cutpointSeparatesPair cut q} := by
  classical
  have heq : {q : ℝ × ℝ | cutpointSeparatesPair cut q} =
      ⋃ i : Fin M, {q : ℝ × ℝ | q.1 ≤ cut i ∧ cut i < q.2} := by
    ext q
    simp [cutpointSeparatesPair]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (measurable_fst measurableSet_Iic).inter (measurable_snd measurableSet_Ioi)

/-- Integrability of the exact weighted separation indicator. -/
theorem integrable_cutpointSeparationIntegrand {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume)) (cut : Fin M → ℝ) :
    Integrable (fun q => if cutpointSeparatesPair cut q then weight q else 0)
      ((volume.prod volume).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  classical
  exact hweight.indicator (measurableSet_cutpointSeparatesPair cut)

/-- The source's all-cross-cell primary value is supermodular. -/
theorem cutpointSeparationValue_supermodular {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume))
    (hweight_nonneg : ∀ᵐ q ∂(volume.prod volume).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), q.1 < q.2 → 0 ≤ weight q)
    (s t : Fin M → ℝ) (hs : Monotone s) (ht : Monotone t) :
    cutpointSeparationValue weight s + cutpointSeparationValue weight t ≤
      cutpointSeparationValue weight (s ⊓ t) + cutpointSeparationValue weight (s ⊔ t) := by
  classical
  unfold cutpointSeparationValue
  rw [← integral_add (integrable_cutpointSeparationIntegrand weight hweight s)
      (integrable_cutpointSeparationIntegrand weight hweight t),
    ← integral_add (integrable_cutpointSeparationIntegrand weight hweight (s ⊓ t))
      (integrable_cutpointSeparationIntegrand weight hweight (s ⊔ t))]
  apply integral_mono_ae
    ((integrable_cutpointSeparationIntegrand weight hweight s).add
      (integrable_cutpointSeparationIntegrand weight hweight t))
    ((integrable_cutpointSeparationIntegrand weight hweight (s ⊓ t)).add
      (integrable_cutpointSeparationIntegrand weight hweight (s ⊔ t)))
  filter_upwards [hweight_nonneg] with q hq
  by_cases hlt : q.1 < q.2
  · have h := mul_le_mul_of_nonneg_left
      (cutpointSeparatesPair_indicator_supermodular s t hs ht q) (hq hlt)
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  · have hzero : ∀ cut : Fin M → ℝ, ¬ cutpointSeparatesPair cut q := by
      intro cut ⟨i, hlo, hhi⟩
      exact hlt (hlo.trans_lt hhi)
    simp only [Pi.add_apply, hzero, ite_false, add_zero, le_refl]

/-- Moving a finite set of cutpoints changes separation only near their boundary
lines, which have zero Lebesgue measure. -/
theorem continuous_cutpointSeparationValue {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume)) : Continuous (cutpointSeparationValue (M := M) weight) := by
  classical
  let μ := (volume.prod volume).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  apply continuous_iff_continuousAt.mpr
  intro s
  have hne : ∀ᵐ q ∂μ, ∀ i : Fin M, q.1 ≠ s i ∧ q.2 ≠ s i := by
    apply ae_mono Measure.restrict_le_self
    change ∀ᵐ q ∂(volume.prod volume), ∀ i : Fin M, q.1 ≠ s i ∧ q.2 ≠ s i
    rw [ae_all_iff]
    intro i
    have hfst : ∀ᵐ (q : ℝ × ℝ) ∂(volume.prod volume), q.1 ≠ s i := by
      rw [ae_iff]
      simpa only [not_not, ← Measure.volume_eq_prod ℝ ℝ] using
        AppliedModelingLib.volume_prod_vertical_line (s i)
    have hsnd : ∀ᵐ (q : ℝ × ℝ) ∂(volume.prod volume), q.2 ≠ s i := by
      rw [ae_iff]
      simpa only [not_not, ← Measure.volume_eq_prod ℝ ℝ] using
        AppliedModelingLib.volume_prod_horizontal_line (s i)
    exact hfst.and hsnd
  have hlim : ∀ᵐ q ∂μ,
      Filter.Tendsto
        (fun t : Fin M → ℝ => if cutpointSeparatesPair t q then weight q else 0)
        (𝓝 s) (𝓝 (if cutpointSeparatesPair s q then weight q else 0)) := by
    filter_upwards [hne] with q hq
    have hi : ∀ i : Fin M, ∀ᶠ t : Fin M → ℝ in 𝓝 s,
        (q.1 ≤ t i ∧ t i < q.2 ↔ q.1 ≤ s i ∧ s i < q.2) := by
      intro i
      have hcoord : Filter.Tendsto (fun t : Fin M → ℝ => t i) (𝓝 s) (𝓝 (s i)) :=
        (continuous_apply i).tendsto s
      filter_upwards
        [eventually_const_le_iff_of_tendsto_of_ne hcoord (hq i).1,
          eventually_lt_const_iff_of_tendsto_of_ne hcoord (hq i).2]
        with t hlo hhi
      exact and_congr hlo hhi
    have hall : ∀ᶠ t : Fin M → ℝ in 𝓝 s, ∀ i : Fin M,
        (q.1 ≤ t i ∧ t i < q.2 ↔ q.1 ≤ s i ∧ s i < q.2) :=
      Filter.eventually_all.mpr hi
    refine (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Fin M → ℝ => if cutpointSeparatesPair s q then weight q else 0)
      (𝓝 s) (𝓝 (if cutpointSeparatesPair s q then weight q else 0))).congr' ?_
    filter_upwards [hall] with t ht
    have heq : cutpointSeparatesPair t q ↔ cutpointSeparatesPair s q :=
      exists_congr fun i => ht i
    simp only [heq]
  have hbound : ∀ᶠ t : Fin M → ℝ in 𝓝 s, ∀ᵐ q ∂μ,
      ‖if cutpointSeparatesPair t q then weight q else 0‖ ≤ ‖weight q‖ := by
    exact Filter.Eventually.of_forall fun t => ae_of_all μ fun q => by
      split_ifs <;> simp
  have hmeas : ∀ᶠ t : Fin M → ℝ in 𝓝 s,
      AEStronglyMeasurable
        (fun q => if cutpointSeparatesPair t q then weight q else 0) μ :=
    Filter.Eventually.of_forall fun t =>
      (integrable_cutpointSeparationIntegrand weight hweight t).aestronglyMeasurable
  exact tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (bound := fun q => ‖weight q‖) hmeas hbound hweight.norm hlim

/-- The source ordered cutpoints, represented only on the displayed range. -/
def finiteOrderedCutpointSet (M : ℕ) : Set (Fin (M + 1) → ℝ) :=
  {s | Monotone s ∧ s 0 = 0 ∧ s (Fin.last M) = 1}

/-- Finite ordered cutpoints form a compact set. -/
theorem isCompact_finiteOrderedCutpointSet (M : ℕ) :
    IsCompact (finiteOrderedCutpointSet M) := by
  have hclosed : IsClosed (finiteOrderedCutpointSet M) :=
    isClosed_monotone.inter
      ((isClosed_eq (continuous_apply 0) continuous_const).inter
        (isClosed_eq (continuous_apply (Fin.last M)) continuous_const))
  apply isCompact_Icc.of_isClosed_subset hclosed
    (s := Icc (fun _ : Fin (M + 1) => (0 : ℝ)) (fun _ => (1 : ℝ)))
  intro s hs
  constructor
  · intro i
    rw [← hs.2.1]
    exact hs.1 (Fin.zero_le i)
  · intro i
    rw [← hs.2.2]
    exact hs.1 (Fin.le_last i)

/-- Ordered cutpoints are closed under coordinatewise minimum and maximum. -/
theorem finiteOrderedCutpointSet_inf_sup {M : ℕ}
    (s t : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M)
    (ht : t ∈ finiteOrderedCutpointSet M) :
    s ⊓ t ∈ finiteOrderedCutpointSet M ∧ s ⊔ t ∈ finiteOrderedCutpointSet M := by
  constructor
  · exact ⟨hs.1.inf ht.1, by simp [hs.2.1, ht.2.1],
      by simp [hs.2.2, ht.2.2]⟩
  · exact ⟨hs.1.sup ht.1, by simp [hs.2.1, ht.2.1],
      by simp [hs.2.2, ht.2.2]⟩

/-- A continuous supermodular objective on a compact finite-vector sublattice
has a greatest maximizer. The auxiliary sum selects it without any uniqueness
assumption on the primary objective. -/
theorem exists_greatest_value_maximizer {M : ℕ}
    (K : Set (Fin M → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (hinf : ∀ s ∈ K, ∀ t ∈ K, s ⊓ t ∈ K)
    (hsup : ∀ s ∈ K, ∀ t ∈ K, s ⊔ t ∈ K)
    (V : (Fin M → ℝ) → ℝ) (hV : Continuous V)
    (hmod : ∀ s ∈ K, ∀ t ∈ K, V s + V t ≤ V (s ⊓ t) + V (s ⊔ t)) :
    ∃ s ∈ K, IsMaxOn V K s ∧
      ∀ t ∈ K, V t = V s → t ≤ s := by
  obtain ⟨s₀, hs₀, hmax₀⟩ := hK.exists_isMaxOn hne hV.continuousOn
  let F := K ∩ {s | V s = V s₀}
  have hF : IsCompact F := hK.inter_right (isClosed_eq hV continuous_const)
  have hFne : F.Nonempty := ⟨s₀, hs₀, rfl⟩
  have hsum : Continuous (fun s : Fin M → ℝ => ∑ i, s i) :=
    continuous_finset_sum Finset.univ fun i _ => continuous_apply i
  obtain ⟨s, hs, hsummax⟩ := hF.exists_isMaxOn hFne hsum.continuousOn
  have hsK : s ∈ K := hs.1
  have hsvalue : V s = V s₀ := hs.2
  have hmax : IsMaxOn V K s := by
    intro t ht
    rw [hsvalue]
    exact hmax₀ ht
  refine ⟨s, hsK, hmax, ?_⟩
  intro t ht hvalue i
  have hjoinK := hsup s hsK t ht
  have hmeetK := hinf s hsK t ht
  have hjoinvalue : V (s ⊔ t) = V s := by
    have hineq := hmod s hsK t ht
    have hmeet : V (s ⊓ t) ≤ V s := hmax hmeetK
    have hjoin : V (s ⊔ t) ≤ V s := hmax hjoinK
    linarith
  have hjoinF : s ⊔ t ∈ F := ⟨hjoinK, hjoinvalue.trans hsvalue⟩
  have hsumle := hsummax hjoinF
  by_contra hnot
  have hlt : s i < t i := lt_of_not_ge hnot
  have hsumlt : (∑ j, s j) < ∑ j, (s ⊔ t) j := by
    apply Finset.sum_lt_sum
    · intro j _
      exact le_max_left _ _
    · exact ⟨i, Finset.mem_univ _, (lt_max_iff.mpr (Or.inr hlt))⟩
  exact (not_lt_of_ge hsumle) hsumlt

/-- Positive cell counts admit an ordered partition. -/
theorem finiteOrderedCutpointSet_nonempty {M : ℕ} (hM : 0 < M) :
    (finiteOrderedCutpointSet M).Nonempty := by
  refine ⟨fun i => equispacedIntervalCutpoint M i.val, ?_⟩
  constructor
  · intro i j hij
    exact monotone_equispacedIntervalCutpoint M hij
  constructor
  · simp [equispacedIntervalCutpoint]
  · simp [equispacedIntervalCutpoint, hM.ne']

/-- The full weighted separation objective has a greatest optimal partition. -/
theorem exists_greatest_cutpointSeparationValue_maximizer {M : ℕ} (hM : 0 < M)
    (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume)) (hweight_nonneg : ∀ᵐ q ∂(volume.prod volume).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), q.1 < q.2 → 0 ≤ weight q) :
    ∃ s ∈ finiteOrderedCutpointSet M,
      IsMaxOn (cutpointSeparationValue weight) (finiteOrderedCutpointSet M) s ∧
      ∀ t ∈ finiteOrderedCutpointSet M,
        cutpointSeparationValue weight t = cutpointSeparationValue weight s → t ≤ s := by
  exact exists_greatest_value_maximizer (finiteOrderedCutpointSet M)
    (isCompact_finiteOrderedCutpointSet M) (finiteOrderedCutpointSet_nonempty hM)
    (fun s hs t ht => (finiteOrderedCutpointSet_inf_sup s t hs ht).1)
    (fun s hs t ht => (finiteOrderedCutpointSet_inf_sup s t hs ht).2)
    (cutpointSeparationValue weight) (continuous_cutpointSeparationValue weight hweight)
    (fun s hs t ht => cutpointSeparationValue_supermodular weight hweight
      hweight_nonneg s t hs.1 ht.1)

/-- Increasing sample rates improves every endpoint-aware adjacent exponent. -/
theorem binaryEndpointAwareAdjacentRate_mono_sampleRate {m : ℕ}
    (levels g g' : Fin (m + 2) → ℝ) (hlevels : BinaryEndpointLevelVector levels)
    (hg : ∀ i, 0 < g i) (hg' : ∀ i, 0 < g' i) (hle : g ≤ g')
    (i : Fin (m + 1)) :
    binaryEndpointAwareAdjacentRate levels g i ≤ binaryEndpointAwareAdjacentRate levels g' i := by
  by_cases hfirst : i.val = 0
  · rw [binaryEndpointAwareAdjacentRate_first levels g i hfirst,
      binaryEndpointAwareAdjacentRate_first levels g' i hfirst]
    apply mul_le_mul_of_nonneg_right (hle _)
    apply neg_nonneg.mpr
    exact Real.log_nonpos
      (sub_nonneg.mpr (BinaryEndpointLevelVector_le_one hlevels _))
      (sub_le_self _ (BinaryEndpointLevelVector_nonneg hlevels _))
  · by_cases hlast : i.val = m
    · rw [binaryEndpointAwareAdjacentRate_last levels g i hfirst hlast,
        binaryEndpointAwareAdjacentRate_last levels g' i hfirst hlast]
      apply mul_le_mul_of_nonneg_right (hle _)
      exact neg_nonneg.mpr (Real.log_nonpos
        (BinaryEndpointLevelVector_nonneg hlevels _)
        (BinaryEndpointLevelVector_le_one hlevels _))
    · rw [binaryEndpointAwareAdjacentRate_interior levels g i hfirst hlast,
        binaryEndpointAwareAdjacentRate_interior levels g' i hfirst hlast]
      apply weightedBernoulliClosedThresholdRate_le_of_weights_le
        (hg _) (hg _) (hg' _) (hg' _) (hle _) (hle _)
      · exact BinaryEndpointLevelVector_pos_of_not_first hlevels _ (by
          simp [adjacentHighIndex])
      · exact BinaryEndpointLevelVector_lt_one_of_not_last hlevels _ (by
          change i.val + 1 ≠ m + 1
          omega)
      · exact BinaryEndpointLevelVector_pos_of_not_first hlevels _ hfirst
      · exact BinaryEndpointLevelVector_lt_one_of_not_last hlevels _ (by
          change i.val ≠ m + 1
          exact Nat.ne_of_lt i.isLt)

/-- Increasing sample rates improves the minimum adjacent exponent. -/
theorem binaryEndpointAwareAdjacentRateObjective_mono_sampleRate {m : ℕ}
    (levels g g' : Fin (m + 2) → ℝ) (hlevels : BinaryEndpointLevelVector levels)
    (hg : ∀ i, 0 < g i) (hg' : ∀ i, 0 < g' i) (hle : g ≤ g') :
    binaryEndpointAwareAdjacentRateObjective levels g ≤
      binaryEndpointAwareAdjacentRateObjective levels g' := by
  apply AppliedModelingLib.le_finiteMin
  intro i
  exact (AppliedModelingLib.finiteMin_le _ i).trans
    (binaryEndpointAwareAdjacentRate_mono_sampleRate levels g g' hlevels hg hg' hle i)

/-- Sampling rates determined by the lower endpoint of each source cell. -/
def finiteCutpointSampleRate {M : ℕ} (g : ℝ → ℝ) (cut : Fin (M + 1) → ℝ) : Fin M → ℝ :=
  fun i => g (cut i.castSucc)

/-- Displayed feasible cutpoints belong to the source quality interval. -/
theorem finiteOrderedCutpointSet_mem_quality {M : ℕ} (s : Fin (M + 1) → ℝ)
    (hs : s ∈ finiteOrderedCutpointSet M) (i : Fin (M + 1)) :
    s i ∈ sourceQualityDomain := by
  constructor
  · rw [← hs.2.1]
    exact hs.1 (Fin.zero_le i)
  · rw [← hs.2.2]
    exact hs.1 (Fin.le_last i)

/-- The finite-vector rates are exactly the source infima over closed cells. -/
theorem finiteCutpointSampleRate_eq_cellInf {M : ℕ} (g : ℝ → ℝ)
    (hg : SourceMatchingFunction g) (s : Fin (M + 1) → ℝ)
    (hs : s ∈ finiteOrderedCutpointSet M) (i : Fin M) :
    finiteCutpointSampleRate g s i = sInf (g '' Icc (s i.castSucc) (s i.succ)) := by
  symm
  apply MonotoneOn.sInf_image_Icc (hs.1 (Fin.castSucc_le_succ i))
  apply hg.1.mono
  intro x hx
  exact ⟨(finiteOrderedCutpointSet_mem_quality s hs i.castSucc).1.trans hx.1,
    hx.2.trans (finiteOrderedCutpointSet_mem_quality s hs i.succ).2⟩

/-- Source matching assumptions make every cell sampling rate positive. -/
theorem finiteCutpointSampleRate_pos {M : ℕ} (g : ℝ → ℝ) (hg : SourceMatchingFunction g)
    (s : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M) (i : Fin M) :
    0 < finiteCutpointSampleRate g s i := by
  obtain ⟨c, hc, hclt⟩ := hg.2.2
  exact hc.trans (hclt _ (finiteOrderedCutpointSet_mem_quality s hs i.castSucc))

/-- The greatest value-optimal cutpoints have the greatest cell sampling rates. -/
theorem finiteCutpointSampleRate_mono {M : ℕ} (g : ℝ → ℝ) (hg : SourceMatchingFunction g)
    (s t : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M)
    (ht : t ∈ finiteOrderedCutpointSet M) (hle : s ≤ t) :
    finiteCutpointSampleRate g s ≤ finiteCutpointSampleRate g t := by
  intro i
  exact hg.1 (finiteOrderedCutpointSet_mem_quality s hs i.castSucc)
    (finiteOrderedCutpointSet_mem_quality t ht i.castSucc) (hle i.castSucc)

/-- With exactly two endpoint-normalized levels, feasibility forces the
source's deterministic endpoint vector `[0, 1]`. -/
theorem binaryEndpointLevelVector_eq_canonical_two
    (levels : Fin (0 + 2) → ℝ) (hlevels : BinaryEndpointLevelVector levels) :
    levels = canonicalUniformEqualizedEndpointLevels 0 := by
  funext i
  fin_cases i
  · exact hlevels.1.trans
      (canonicalUniformEqualizedEndpointLevels_levelVector 0).1.symm
  · exact hlevels.2.1.trans
      (canonicalUniformEqualizedEndpointLevels_levelVector 0).2.1.symm

/-- For the real-valued displayed adjacent-rate formula, the unique two-level
endpoint vector has value zero.  The separate support-safe/actual-error
endpoint has infinite rate because its error is eventually zero. -/
theorem binaryEndpointAwareAdjacentRateObjective_two_levels_eq_zero
    (sampleRate levels : Fin (0 + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels) :
    binaryEndpointAwareAdjacentRateObjective levels sampleRate = 0 := by
  rw [binaryEndpointLevelVector_eq_canonical_two levels hlevels]
  unfold binaryEndpointAwareAdjacentRateObjective
  exact
    AppliedModelingLib.finiteMin_eq_of_forall
      (fun i : Fin (0 + 1) =>
        binaryEndpointAwareAdjacentRate
          (canonicalUniformEqualizedEndpointLevels 0) sampleRate i)
      0
      (by
        intro i
        fin_cases i
        simp [canonicalUniformEqualizedEndpointLevels,
          canonicalTinyEndpointLevels, binaryEndpointAwareAdjacentRate,
          adjacentHighIndex, Real.log_zero])

/-- General value-then-rate selection over finite ordered cutpoints. Tied
partitions are compared using the greatest primary maximizer and monotonicity
of the source matching function. No primary uniqueness or secondary optimality
premise is supplied. -/
theorem exists_finite_cutpoint_lexicographic_maximizer {m : ℕ} (hm : 0 < m)
    (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume))
    (hweight_nonneg : ∀ᵐ q ∂(volume.prod volume).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), q.1 < q.2 → 0 ≤ weight q)
    (g : ℝ → ℝ) (hg : SourceMatchingFunction g) :
    ∃ s : Fin ((m + 2) + 1) → ℝ, ∃ levels : Fin (m + 2) → ℝ,
      s ∈ finiteOrderedCutpointSet (m + 2) ∧
      BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels (finiteCutpointSampleRate g s) ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin ((m + 2) + 1) → ℝ) × (Fin (m + 2) → ℝ) =>
          design.1 ∈ finiteOrderedCutpointSet (m + 2) ∧ BinaryEndpointLevelVector design.2)
        (fun design => cutpointSeparationValue weight design.1)
        (fun design => binaryEndpointAwareAdjacentRateObjective design.2
          (finiteCutpointSampleRate g design.1)) (s, levels) := by
  obtain ⟨s, hs, hvalue, hgreatest⟩ :=
    exists_greatest_cutpointSeparationValue_maximizer (by omega : 0 < m + 2)
      weight hweight hweight_nonneg
  have hpos := finiteCutpointSampleRate_pos g hg s hs
  have hexists : ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels (finiteCutpointSampleRate g s) := by
    by_cases hmone : m = 1
    · subst m
      exact binaryEndpointAwareAdjacentRatesEqualize_existsUnique_one
        (finiteCutpointSampleRate g s) (fun i => hpos _) (fun i => hpos _)
    · exact binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped (by omega)
        (finiteCutpointSampleRate g s) (by
          intro k hk
          rw [binaryEndpointSampleRateNat_of_lt _ hk]
          exact hpos ⟨k, hk⟩)
  obtain ⟨levels, ⟨hlevels, hequal⟩, _hunique⟩ := hexists
  have hoptimal := binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
    (by omega : 0 < m) (finiteCutpointSampleRate g s) levels hlevels
    (fun i => hpos _) (fun i => hpos _) hequal
  refine ⟨s, levels, hs, hlevels, hequal, ?_⟩
  apply theorem31_partition_endpoint_two_stage_lexicographic_optimality
    (fun s => s ∈ finiteOrderedCutpointSet (m + 2))
    (fun _ levels => BinaryEndpointLevelVector levels)
    (cutpointSeparationValue weight)
    (fun s levels => binaryEndpointAwareAdjacentRateObjective levels (finiteCutpointSampleRate g s))
    s levels ⟨hs, hvalue⟩ hlevels
  intro t candidate ht hc hsame
  calc
    binaryEndpointAwareAdjacentRateObjective candidate (finiteCutpointSampleRate g t) ≤
        binaryEndpointAwareAdjacentRateObjective candidate (finiteCutpointSampleRate g s) :=
      binaryEndpointAwareAdjacentRateObjective_mono_sampleRate candidate
        (finiteCutpointSampleRate g t) (finiteCutpointSampleRate g s) hc
        (finiteCutpointSampleRate_pos g hg t ht) hpos
        (finiteCutpointSampleRate_mono g hg t s ht hs (hgreatest t ht hsame))
    _ ≤ binaryEndpointAwareAdjacentRateObjective levels (finiteCutpointSampleRate g s) :=
      hoptimal.le hc

/-- Extend only the displayed cutpoints, constantly after the last endpoint. -/
def finiteCutpointExtension {M : ℕ} (s : Fin (M + 1) → ℝ) (k : ℕ) : ℝ :=
  s ⟨min k M, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem finiteCutpointExtension_of_le {M : ℕ} (s : Fin (M + 1) → ℝ)
    {k : ℕ} (hk : k ≤ M) : finiteCutpointExtension s k = s ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [finiteCutpointExtension, Nat.min_eq_left hk]

theorem finiteCutpointExtension_mono {M : ℕ} (s : Fin (M + 1) → ℝ)
    (hs : Monotone s) : Monotone (finiteCutpointExtension s) := by
  intro i j hij
  exact hs (min_le_min_right _ hij)

/-- The full source equation-(20) objective, with every ordered cell pair. -/
def allCrossCellValue {M : ℕ} (weight : ℝ × ℝ → ℝ) (s : Fin (M + 1) → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin M, if i < j then
    ∫ q in Ioc (s i.castSucc) (s i.succ) ×ˢ Ioc (s j.castSucc) (s j.succ),
      weight q ∂(volume.prod volume)
    else 0

/-- Source discretizations have strictly increasing displayed endpoints. -/
def sourceStrictCutpointSet (M : ℕ) : Set (Fin (M + 1) → ℝ) :=
  {s | StrictMono s ∧ s 0 = 0 ∧ s (Fin.last M) = 1}

theorem sourceStrictCutpointSet_subset {M : ℕ} :
    sourceStrictCutpointSet M ⊆ finiteOrderedCutpointSet M := by
  intro s hs
  exact ⟨hs.1.monotone, hs.2⟩

/-- Lower-closed source cells. Only the last cell includes its upper endpoint,
so the cells partition the full source quality interval `[0,1]`. -/
def sourceFiniteCell {M : ℕ} (s : Fin (M + 1) → ℝ) (i : Fin M) : Set ℝ :=
  if i.val + 1 = M then Icc (s i.castSucc) (s i.succ)
  else Ico (s i.castSucc) (s i.succ)

/-- The source cell sampling rates are infima on the disjoint source cells. -/
def sourceFiniteSampleRate {M : ℕ} (g : ℝ → ℝ) (s : Fin (M + 1) → ℝ) : Fin M → ℝ :=
  fun i => sInf (g '' sourceFiniteCell s i)

/-- The source primary objective integrates every ordered pair of source cells. -/
def sourceAllCrossCellValue {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (s : Fin (M + 1) → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin M, if i < j then
    ∫ q in sourceFiniteCell s i ×ˢ sourceFiniteCell s j,
      weight q ∂(volume.prod volume)
    else 0

theorem sourceFiniteCell_subset_closed {M : ℕ} (s : Fin (M + 1) → ℝ) (i : Fin M) :
    sourceFiniteCell s i ⊆ Icc (s i.castSucc) (s i.succ) := by
  unfold sourceFiniteCell
  split_ifs
  · exact Subset.rfl
  · exact Ico_subset_Icc_self

theorem sourceFiniteCell_lower_mem {M : ℕ} (s : Fin (M + 1) → ℝ)
    (hs : s ∈ sourceStrictCutpointSet M) (i : Fin M) :
    s i.castSucc ∈ sourceFiniteCell s i := by
  have hlt := hs.1 (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  unfold sourceFiniteCell
  split_ifs <;> simp [hlt.le, hlt]

/-- Distinct source cells are disjoint, including at a matching-function jump. -/
theorem sourceFiniteCell_pairwise_disjoint {M : ℕ} (s : Fin (M + 1) → ℝ)
    (hs : s ∈ sourceStrictCutpointSet M) :
    Pairwise (fun i j : Fin M => Disjoint (sourceFiniteCell s i) (sourceFiniteCell s j)) := by
  suffices h : ∀ i j : Fin M, i < j →
      Disjoint (sourceFiniteCell s i) (sourceFiniteCell s j) by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact h i j hlt
    · exact (h j i hlt).symm
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hilast : i.val + 1 ≠ M := by omega
  have hleft : x < s i.succ := by
    have hx' : x ∈ Ico (s i.castSucc) (s i.succ) := by
      simpa [sourceFiniteCell, hilast] using hx
    exact hx'.2
  have hright := (sourceFiniteCell_subset_closed s j hy).1
  exact (not_lt_of_ge (hright.trans' (hs.1.monotone
    (show i.succ ≤ j.castSucc from hij)))) hleft

/-- The lower-closed cells cover precisely the entire source quality interval. -/
theorem mem_sourceQualityDomain_iff_exists_sourceFiniteCell {M : ℕ} (hM : 0 < M)
    (s : Fin (M + 1) → ℝ) (hs : s ∈ sourceStrictCutpointSet M) (x : ℝ) :
    x ∈ sourceQualityDomain ↔ ∃ i : Fin M, x ∈ sourceFiniteCell s i := by
  have hsweak := sourceStrictCutpointSet_subset hs
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · refine ⟨⟨M - 1, by omega⟩, ?_⟩
      have hlast : (⟨M - 1, by omega⟩ : Fin M).succ = Fin.last M := by
        apply Fin.ext
        simp
        omega
      simp only [sourceFiniteCell, Nat.sub_add_cancel (by omega : 1 ≤ M)]
      refine ⟨?_, ?_⟩
      · rw [hx1]
        exact (finiteOrderedCutpointSet_mem_quality s hsweak _).2
      · rw [hlast, hs.2.2, hx1]
    · let cut := finiteCutpointExtension s
      have hcut0 : cut 0 = 0 := by
        change finiteCutpointExtension s 0 = 0
        rw [finiteCutpointExtension_of_le s (Nat.zero_le M)]
        exact hs.2.1
      have hcutM : cut M = 1 := by
        change finiteCutpointExtension s M = 1
        rw [finiteCutpointExtension_of_le s le_rfl]
        exact hs.2.2
      have hmem : x ∈ Ico (cut 0) (cut M) := by
        rw [hcut0, hcutM]
        exact ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (Ico_subset_biUnion_Ico M cut hmem)
      have hiM : i < M := Finset.mem_range.mp hi
      refine ⟨⟨i, hiM⟩, ?_⟩
      have hxi' : x ∈ Ico (s (⟨i, hiM⟩ : Fin M).castSucc)
          (s (⟨i, hiM⟩ : Fin M).succ) := by
        simpa only [cut, finiteCutpointExtension_of_le s (Nat.le_of_lt hiM),
          finiteCutpointExtension_of_le s (Nat.succ_le_of_lt hiM)] using hxi
      unfold sourceFiniteCell
      split_ifs
      · exact Ico_subset_Icc_self hxi'
      · exact hxi'
  · rintro ⟨i, hi⟩
    have hclosed := sourceFiniteCell_subset_closed s i hi
    exact ⟨(finiteOrderedCutpointSet_mem_quality s hsweak i.castSucc).1.trans hclosed.1,
      hclosed.2.trans (finiteOrderedCutpointSet_mem_quality s hsweak i.succ).2⟩

/-- Source cell infima equal the matching function at the included lower endpoint.
No continuity or right-continuity of the matching function is required. -/
theorem sourceFiniteSampleRate_eq_finiteCutpointSampleRate {M : ℕ} (g : ℝ → ℝ)
    (hg : SourceMatchingFunction g) (s : Fin (M + 1) → ℝ)
    (hs : s ∈ sourceStrictCutpointSet M) :
    sourceFiniteSampleRate g s = finiteCutpointSampleRate g s := by
  funext i
  apply IsLeast.csInf_eq
  refine ⟨⟨s i.castSucc, sourceFiniteCell_lower_mem s hs i, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hsweak := sourceStrictCutpointSet_subset hs
  have hclosed := sourceFiniteCell_subset_closed s i hx
  apply hg.1 (finiteOrderedCutpointSet_mem_quality s hsweak i.castSucc)
    ⟨(finiteOrderedCutpointSet_mem_quality s hsweak i.castSucc).1.trans hclosed.1,
      hclosed.2.trans (finiteOrderedCutpointSet_mem_quality s hsweak i.succ).2⟩ hclosed.1

/-- Endpoint ownership affects source rates but not Lebesgue integrals. -/
theorem sourceFiniteCell_ae_eq_Ioc {M : ℕ} (s : Fin (M + 1) → ℝ) (i : Fin M) :
    sourceFiniteCell s i =ᵐ[volume] Ioc (s i.castSucc) (s i.succ) := by
  unfold sourceFiniteCell
  split_ifs
  · exact Ioc_ae_eq_Icc.symm
  · exact Ico_ae_eq_Ioc

/-- The source-cell objective equals the integration helper for every weight. -/
theorem sourceAllCrossCellValue_eq_allCrossCellValue {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (s : Fin (M + 1) → ℝ) :
    sourceAllCrossCellValue weight s = allCrossCellValue weight s := by
  unfold sourceAllCrossCellValue allCrossCellValue
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact setIntegral_congr_set (Measure.set_prod_ae_eq
      (sourceFiniteCell_ae_eq_Ioc s i) (sourceFiniteCell_ae_eq_Ioc s j))
  · rfl

/-- On a pair of ordered cells, separation agrees exactly with their index order. -/
theorem cutpointSeparatesPair_iff_cell_lt {M : ℕ} (s : Fin (M + 1) → ℝ)
    (hs : Monotone s) (i j : Fin M) (q : ℝ × ℝ)
    (hq : q ∈ Ioc (s i.castSucc) (s i.succ) ×ˢ Ioc (s j.castSucc) (s j.succ)) :
    cutpointSeparatesPair s q ↔ i < j := by
  constructor
  · rintro ⟨k, hlo, hhi⟩
    by_contra hnot
    have hji : j ≤ i := le_of_not_gt hnot
    by_cases hki : k ≤ i.castSucc
    · exact (not_le_of_gt hq.1.1) (hlo.trans (hs hki))
    · have hjk : j.succ ≤ k := by
        change j.val + 1 ≤ k.val
        have hik : i.val < k.val := lt_of_not_ge hki
        exact (Nat.succ_le_of_lt (lt_of_le_of_lt hji hik))
      exact (not_lt_of_ge (hq.2.2.trans (hs hjk))) hhi
  · intro hij
    refine ⟨i.succ, hq.1.2, ?_⟩
    have hindex : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    exact (hs hindex).trans_lt hq.2.1

/-- Lebesgue integration ignores the two zero-endpoint boundary lines. -/
theorem unitSquare_Icc_ae_eq_Ioc :
    Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 =ᵐ[volume.prod volume]
      Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  have hfst : ∀ᵐ (q : ℝ × ℝ) ∂(volume.prod volume), q.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ← Measure.volume_eq_prod ℝ ℝ] using
      AppliedModelingLib.volume_prod_vertical_line 0
  have hsnd : ∀ᵐ (q : ℝ × ℝ) ∂(volume.prod volume), q.2 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ← Measure.volume_eq_prod ℝ ℝ] using
      AppliedModelingLib.volume_prod_horizontal_line 0
  filter_upwards [hfst, hsnd] with q hf hs
  apply propext
  constructor
  · rintro ⟨⟨hlo, hhi⟩, ⟨hlo', hhi'⟩⟩
    exact ⟨⟨lt_of_le_of_ne hlo hf.symm, hhi⟩, ⟨lt_of_le_of_ne hlo' hs.symm, hhi'⟩⟩
  · rintro ⟨⟨hlo, hhi⟩, ⟨hlo', hhi'⟩⟩
    exact ⟨⟨hlo.le, hhi⟩, ⟨hlo'.le, hhi'⟩⟩

/-- The separation integral equals the paper's sum over all cross-cell rectangles. -/
theorem cutpointSeparationValue_eq_allCrossCellValue {M : ℕ}
    (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume))
    (s : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M) :
    cutpointSeparationValue weight s = allCrossCellValue weight s := by
  let cut := finiteCutpointExtension s
  let P := FiniteMeasurableSetPartition.orderedRealIocNatCutpoints volume M cut
    (finiteCutpointExtension_mono s hs.1)
  have hcut0 : cut 0 = 0 := by
    dsimp [cut]
    rw [finiteCutpointExtension_of_le s (Nat.zero_le M)]
    exact hs.2.1
  have hcutM : cut M = 1 := by
    dsimp [cut]
    rw [finiteCutpointExtension_of_le s le_rfl]
    exact hs.2.2
  have hpiece : ∀ i : Fin M, P.pieceSet i = Ioc (s i.castSucc) (s i.succ) := by
    intro i
    change Ioc (finiteCutpointExtension s i.val) (finiteCutpointExtension s (i.val + 1)) = _
    rw [finiteCutpointExtension_of_le s (Nat.le_of_lt i.isLt),
      finiteCutpointExtension_of_le s (Nat.succ_le_of_lt i.isLt)]
    rfl
  have hsubset : ∀ i j : Fin M,
      P.pieceSet i ×ˢ P.pieceSet j ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro i j q hq
    rw [hpiece i, hpiece j] at hq
    exact ⟨⟨(finiteOrderedCutpointSet_mem_quality s hs i.castSucc).1.trans hq.1.1.le,
      hq.1.2.trans (finiteOrderedCutpointSet_mem_quality s hs i.succ).2⟩,
      ⟨(finiteOrderedCutpointSet_mem_quality s hs j.castSucc).1.trans hq.2.1.le,
      hq.2.2.trans (finiteOrderedCutpointSet_mem_quality s hs j.succ).2⟩⟩
  let f : ℝ × ℝ → ℝ := fun q => if cutpointSeparatesPair s q then weight q else 0
  have hf : ∀ ij : Fin M × Fin M, IntegrableOn f ((P.prod P).pieceSet ij) (volume.prod volume) := by
    intro ij
    exact IntegrableOn.mono_set (integrable_cutpointSeparationIntegrand weight hweight s)
      (hsubset ij.1 ij.2)
  have hdecomp := (P.prod P).setIntegral_eq_sum_componentIntegral f hf
  have hsupport : (P.prod P).support = Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    change Ioc (cut 0) (cut M) ×ˢ Ioc (cut 0) (cut M) = _
    rw [hcut0, hcutM]
  unfold cutpointSeparationValue
  rw [setIntegral_congr_set unitSquare_Icc_ae_eq_Ioc, ← hsupport, hdecomp]
  rw [Fintype.sum_prod_type]
  unfold allCrossCellValue
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (∫ q in P.pieceSet i ×ˢ P.pieceSet j, f q ∂(volume.prod volume)) = _
  rw [hpiece i, hpiece j]
  by_cases hij : i < j
  · rw [if_pos hij]
    apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc)
    intro q hq
    exact if_pos ((cutpointSeparatesPair_iff_cell_lt s hs.1 i j q hq).mpr hij)
  · rw [if_neg hij]
    have hzero : (∫ q in Ioc (s i.castSucc) (s i.succ) ×ˢ Ioc (s j.castSucc) (s j.succ),
        f q ∂(volume.prod volume)) = ∫ q in Ioc (s i.castSucc) (s i.succ) ×ˢ
        Ioc (s j.castSucc) (s j.succ), (0 : ℝ) ∂(volume.prod volume) := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc)
      intro q hq
      exact if_neg (fun h => hij ((cutpointSeparatesPair_iff_cell_lt s hs.1 i j q hq).mp h))
    simpa using hzero

/-- A new boundary inside an old cell strictly increases primary value when all
ordered quality pairs receive positive weight. -/
theorem cutpointSeparationValue_lt_of_insert_boundary {M : ℕ}
    (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume))
    (hweight_pos : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      q.1 < q.2 → 0 < weight q)
    (s t : Fin M → ℝ) (hrange : Set.range s ⊆ Set.range t)
    (a y b : ℝ) (ha : 0 ≤ a) (hay : a < y) (hyb : y < b) (hb : b ≤ 1)
    (hnew : y ∈ Set.range t) (hgap : ∀ i, s i ≤ a ∨ b ≤ s i) :
    cutpointSeparationValue weight s < cutpointSeparationValue weight t := by
  let square := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let μ := (volume.prod volume).restrict square
  let f : (Fin M → ℝ) → ℝ × ℝ → ℝ :=
    fun cut q => if cutpointSeparatesPair cut q then weight q else 0
  have hint : ∀ cut, Integrable (f cut) μ :=
    integrable_cutpointSeparationIntegrand weight hweight
  have hsep : ∀ q, cutpointSeparatesPair s q → cutpointSeparatesPair t q := by
    rintro q ⟨i, hlo, hhi⟩
    obtain ⟨j, hj⟩ := hrange ⟨i, rfl⟩
    exact ⟨j, by simpa only [hj] using hlo, by simpa only [hj] using hhi⟩
  have hnonneg : ∀ᵐ q ∂μ, 0 ≤ f t q - f s q := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    by_cases hs : cutpointSeparatesPair s q
    · simp [f, hs, hsep q hs]
    · by_cases ht : cutpointSeparatesPair t q
      · have hlt : q.1 < q.2 := by
          obtain ⟨i, hlo, hhi⟩ := ht
          exact hlo.trans_lt hhi
        have hw := (hweight_pos q hq hlt).le
        simpa only [f, if_pos ht, if_neg hs, sub_zero] using hw
      · simp [f, hs, ht]
  let R := Ioo a y ×ˢ Ioo y b
  have hRsub : R ⊆ square := by
    intro q hq
    exact ⟨⟨ha.trans hq.1.1.le, hq.1.2.le.trans (hyb.le.trans hb)⟩,
      ⟨(ha.trans hay.le).trans hq.2.1.le, hq.2.2.le.trans hb⟩⟩
  have hRpos : 0 < μ R := by
    have hpos := (isOpen_Ioo.prod isOpen_Ioo).measure_pos (volume.prod volume)
      (Set.Nonempty.prod (nonempty_Ioo.mpr hay) (nonempty_Ioo.mpr hyb))
    change 0 < ((volume.prod volume).restrict square) R
    rw [Measure.restrict_apply (measurableSet_Ioo.prod measurableSet_Ioo),
      inter_eq_left.mpr hRsub]
    exact hpos
  have hsupport : R ⊆ Function.support (fun q => f t q - f s q) := by
    intro q hq
    have hs : ¬ cutpointSeparatesPair s q := by
      rintro ⟨i, hlo, hhi⟩
      rcases hgap i with h | h
      · exact (not_le_of_gt hq.1.1) (hlo.trans h)
      · exact (not_lt_of_ge (hq.2.2.le.trans h)) hhi
    obtain ⟨j, hj⟩ := hnew
    have ht : cutpointSeparatesPair t q := ⟨j, by rw [hj]; exact hq.1.2.le,
      by rw [hj]; exact hq.2.1⟩
    have hw := hweight_pos q (hRsub hq) (hq.1.2.trans hq.2.1)
    change f t q - f s q ≠ 0
    simpa only [f, if_pos ht, if_neg hs, sub_zero] using hw.ne'
  have hpos : 0 < ∫ q, f t q - f s q ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg ((hint t).sub (hint s))).mpr
      (hRpos.trans_le (measure_mono hsupport))
  rw [integral_sub (hint t) (hint s)] at hpos
  exact sub_pos.mp hpos

/-- Sorting a finite vector preserves its values, including repeated values. -/
theorem exists_monotone_vector_same_range {M : ℕ} (v : Fin M → ℝ) :
    ∃ t : Fin M → ℝ, Monotone t ∧ Set.range t = Set.range v := by
  let l := (List.ofFn v).mergeSort (· ≤ ·)
  have hlen : l.length = M := by simp [l]
  let t : Fin M → ℝ := fun i => l.get (Fin.cast hlen.symm i)
  have hmono : Monotone t := by
    intro i j hij
    exact (List.sortedLE_mergeSort.monotone_get) hij
  have hmem : ∀ x, x ∈ l ↔ x ∈ Set.range v := by
    intro x
    exact (List.mergeSort_perm (List.ofFn v) _).mem_iff.trans (List.mem_ofFn' v x)
  refine ⟨t, hmono, ?_⟩
  ext x
  constructor
  · rintro ⟨i, hi⟩
    apply (hmem x).mp
    rw [← hi]
    exact List.get_mem l _
  · intro hx
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((hmem x).mpr hx)
    refine ⟨Fin.cast hlen j, ?_⟩
    simpa [t] using hj

/-- Every nonconstant ordered endpoint vector has a positive-length cell. -/
theorem finiteOrderedCutpointSet_exists_positive_gap {M : ℕ}
    (s : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M) :
    ∃ j : Fin M, s j.castSucc < s j.succ := by
  by_contra hnot
  push Not at hnot
  have hstep : ∀ j : Fin M, s j.succ = s j.castSucc := by
    intro j
    exact le_antisymm (hnot j) (hs.1 (Fin.castSucc_le_succ j))
  have hconst : ∀ i : Fin (M + 1), s i = s 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hstep i).trans ih
  have h01 : (1 : ℝ) = 0 := hs.2.2.symm.trans ((hconst _).trans hs.2.1)
  norm_num at h01

/-- Positive pair weights rule out empty cells at a primary maximum. -/
theorem strictMono_of_cutpointSeparationValue_maximizer {M : ℕ}
    (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume))
    (hweight_pos : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      q.1 < q.2 → 0 < weight q)
    (s : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M)
    (hmax : IsMaxOn (cutpointSeparationValue weight) (finiteOrderedCutpointSet M) s) :
    StrictMono s := by
  by_contra hnot
  have hninj : ¬ Function.Injective s := fun h => hnot (hs.1.strictMono_of_injective h)
  simp only [Function.Injective, not_forall] at hninj
  obtain ⟨i, j, heq, hne⟩ := hninj
  obtain ⟨k, hgap⟩ := finiteOrderedCutpointSet_exists_positive_gap s hs
  let a := s k.castSucc
  let b := s k.succ
  let y := (a + b) / 2
  have hay : a < y := left_lt_add_div_two.mpr hgap
  have hyb : y < b := add_div_two_lt_right.mpr hgap
  have ha : 0 ≤ a := (finiteOrderedCutpointSet_mem_quality s hs k.castSucc).1
  have hb : b ≤ 1 := (finiteOrderedCutpointSet_mem_quality s hs k.succ).2
  let v := Function.update s i y
  have hsubset : Set.range s ⊆ Set.range v := by
    rintro x ⟨l, rfl⟩
    by_cases hli : l = i
    · subst l
      refine ⟨j, ?_⟩
      change Function.update s i y j = s i
      rw [Function.update_of_ne (Ne.symm hne)]
      exact heq.symm
    · exact ⟨l, Function.update_of_ne hli _ _⟩
  have hyv : y ∈ Set.range v := ⟨i, Function.update_self _ _ _⟩
  have hv : ∀ l, v l ∈ Icc (0 : ℝ) 1 := by
    intro l
    change Function.update s i y l ∈ Icc (0 : ℝ) 1
    by_cases hli : l = i
    · subst l
      rw [Function.update_self]
      exact ⟨ha.trans hay.le, hyb.le.trans hb⟩
    · rw [Function.update_of_ne hli]
      exact finiteOrderedCutpointSet_mem_quality s hs l
  obtain ⟨t, htmono, htrange⟩ := exists_monotone_vector_same_range v
  have hsubset' : Set.range s ⊆ Set.range t := by rw [htrange]; exact hsubset
  have hyt : y ∈ Set.range t := by rw [htrange]; exact hyv
  have htmem : ∀ l, t l ∈ Icc (0 : ℝ) 1 := by
    intro l
    obtain ⟨r, hr⟩ := htrange.subset ⟨l, rfl⟩
    rw [← hr]
    exact hv r
  have ht0 : t 0 = 0 := by
    obtain ⟨l, hl⟩ := hsubset' ⟨0, hs.2.1⟩
    exact le_antisymm ((htmono (Fin.zero_le l)).trans hl.le) (htmem 0).1
  have htlast : t (Fin.last M) = 1 := by
    obtain ⟨l, hl⟩ := hsubset' ⟨Fin.last M, hs.2.2⟩
    exact le_antisymm (htmem _).2 (hl.symm.le.trans (htmono (Fin.le_last l)))
  have ht : t ∈ finiteOrderedCutpointSet M := ⟨htmono, ht0, htlast⟩
  have hsplit : ∀ l, s l ≤ a ∨ b ≤ s l := by
    intro l
    by_cases hl : l ≤ k.castSucc
    · exact Or.inl (hs.1 hl)
    · exact Or.inr (hs.1 (show k.succ ≤ l from Nat.succ_le_of_lt (lt_of_not_ge hl)))
  have himprove := cutpointSeparationValue_lt_of_insert_boundary weight hweight hweight_pos
    s t hsubset' a y b ha hay hyb hb hyt hsplit
  exact (not_lt_of_ge (hmax ht)) himprove

/-- Full cross-cell value, strict source cells, and global optimization of the
paper's displayed adjacent-rate formula. The identification of that formula
with the exponent of the actual `W - W_k` remains a separate claim. -/
theorem exists_strict_allCrossCell_lexicographic_formula {m : ℕ} (hm : 0 < m)
    (weight : ℝ × ℝ → ℝ)
    (hweight : IntegrableOn weight (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume))
    (hweight_pos : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      q.1 < q.2 → 0 < weight q)
    (g : ℝ → ℝ) (hg : SourceMatchingFunction g) :
    ∃ s : Fin ((m + 2) + 1) → ℝ, ∃ levels : Fin (m + 2) → ℝ,
      s ∈ finiteOrderedCutpointSet (m + 2) ∧ StrictMono s ∧
      BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels (finiteCutpointSampleRate g s) ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin ((m + 2) + 1) → ℝ) × (Fin (m + 2) → ℝ) =>
          design.1 ∈ finiteOrderedCutpointSet (m + 2) ∧ BinaryEndpointLevelVector design.2)
        (fun design => allCrossCellValue weight design.1)
        (fun design => binaryEndpointAwareAdjacentRateObjective design.2
          (finiteCutpointSampleRate g design.1)) (s, levels) := by
  have hnonneg : ∀ᵐ q ∂(volume.prod volume).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), q.1 < q.2 → 0 ≤ weight q := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    exact fun hlt => (hweight_pos q hq hlt).le
  obtain ⟨s, levels, hs, hlevels, hequal, hlex⟩ :=
    exists_finite_cutpoint_lexicographic_maximizer hm weight hweight hnonneg g hg
  have hmax : IsMaxOn (cutpointSeparationValue weight) (finiteOrderedCutpointSet (m + 2)) s := by
    intro t ht
    rcases hlex.2 (t, levels) ⟨ht, hlevels⟩ with hlt | heq
    · exact hlt.le
    · exact heq.1.le
  refine ⟨s, levels, hs, strictMono_of_cutpointSeparationValue_maximizer
    weight hweight hweight_pos s hs hmax, hlevels, hequal, ⟨hs, hlevels⟩, ?_⟩
  intro design hd
  have h := hlex.2 design hd
  simpa only [cutpointSeparationValue_eq_allCrossCellValue weight hweight s hs,
    cutpointSeparationValue_eq_allCrossCellValue weight hweight design.1 hd.1] using h

/-- Ordered source quality pairs; the first coordinate is the lower quality.
Thus `weight (low, high)` denotes the paper's `w(high, low)`. -/
def sourceOrderedQualityPairs : Set (ℝ × ℝ) :=
  (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {q | q.1 < q.2}

theorem measurableSet_sourceOrderedQualityPairs : MeasurableSet sourceOrderedQualityPairs :=
  (measurableSet_Icc.prod measurableSet_Icc).inter (isOpen_lt continuous_fst continuous_snd).measurableSet

/-- The source-faithful two-level rule: the lower source cell receives `0`
and the upper source cell, including their shared cutpoint, receives `1`. -/
def sourceTwoLevelSuccessProbability (s : Fin ((0 + 2) + 1) → ℝ)
    (θ : ℝ) : ℝ :=
  if θ < s (1 : Fin ((0 + 2) + 1)) then 0 else 1

theorem sourceTwoLevelSuccessProbability_nonneg
    (s : Fin ((0 + 2) + 1) → ℝ) (θ : ℝ) :
    0 ≤ sourceTwoLevelSuccessProbability s θ := by
  by_cases h : θ < s (1 : Fin ((0 + 2) + 1)) <;>
    simp [sourceTwoLevelSuccessProbability, h]

theorem sourceTwoLevelSuccessProbability_le_one
    (s : Fin ((0 + 2) + 1) → ℝ) (θ : ℝ) :
    sourceTwoLevelSuccessProbability s θ ≤ 1 := by
  by_cases h : θ < s (1 : Fin ((0 + 2) + 1)) <;>
    simp [sourceTwoLevelSuccessProbability, h]

/-- The literal population pair objective for the two-level source rule. -/
def sourceTwoLevelPairValue (s : Fin ((0 + 2) + 1) → ℝ)
    (q : ℝ × ℝ) : ℝ :=
  (if sourceTwoLevelSuccessProbability s q.1 <
      sourceTwoLevelSuccessProbability s q.2 then 1 else 0) -
    (if sourceTwoLevelSuccessProbability s q.2 <
      sourceTwoLevelSuccessProbability s q.1 then 1 else 0)

/-- The source population objective `W` for a two-level rule. -/
noncomputable def sourceTwoLevelLimitingValue
    (weight : ℝ × ℝ → ℝ) (s : Fin ((0 + 2) + 1) → ℝ) : ℝ :=
  ∫ q in sourceOrderedQualityPairs, weight q * sourceTwoLevelPairValue s q
    ∂(volume.prod volume)

/-- The literal source finite-sample objective `W_k` for the two-level rule,
using the paper's floor match counts and strict-order-minus-inversion `P_k`. -/
noncomputable def sourceTwoLevelFloorValue
    (weight : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (s : Fin ((0 + 2) + 1) → ℝ) (k : ℕ) : ℝ :=
  ∫ q in sourceOrderedQualityPairs,
    weight q *
      twoSampleFloorPkObjectiveProb
        (binaryRatingModel (sourceTwoLevelSuccessProbability s)
          (sourceTwoLevelSuccessProbability_nonneg s)
          (sourceTwoLevelSuccessProbability_le_one s))
        g q.2 q.1 k ∂(volume.prod volume)

/-- Source normalization itself implies the integrability needed by the
finite-cutpoint existence argument. No condition outside ordered pairs is used. -/
theorem integrableOn_of_source_weight_normalized (weight : ℝ × ℝ → ℝ)
    (hnorm : ∫ q in sourceOrderedQualityPairs, weight q ∂(volume.prod volume) = 1) :
    IntegrableOn weight sourceOrderedQualityPairs (volume.prod volume) := by
  by_contra hnot
  rw [integral_undef hnot] at hnorm
  norm_num at hnorm

/-- Uniform positivity of the source matching function makes the literal
two-level empirical objective equal its population objective after one common
finite horizon. -/
theorem sourceTwoLevelFloorValue_eventually_eq_limitingValue
    (weight : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (hg : SourceMatchingFunction g)
    (s : Fin ((0 + 2) + 1) → ℝ) :
    sourceTwoLevelFloorValue weight g s =ᶠ[Filter.atTop]
      fun _ => sourceTwoLevelLimitingValue weight s := by
  rcases hg.2.2 with ⟨c, hc, hlower⟩
  have hcounts := eventually_floorSampleCount_pos_of_uniform_lower
    g hc (fun θ hθ => (hlower θ hθ).le)
  filter_upwards [hcounts] with k hk
  unfold sourceTwoLevelFloorValue sourceTwoLevelLimitingValue
  apply setIntegral_congr_fun measurableSet_sourceOrderedQualityPairs
  intro q hq
  apply congrArg (weight q * ·)
  unfold twoSampleFloorPkObjectiveProb
  by_cases hlo : q.1 < s (1 : Fin ((0 + 2) + 1))
  · have hpLo : sourceTwoLevelSuccessProbability s q.1 = 0 := by
      simp [sourceTwoLevelSuccessProbability, hlo]
    by_cases hhi : q.2 < s (1 : Fin ((0 + 2) + 1))
    · have hpHi : sourceTwoLevelSuccessProbability s q.2 = 0 := by
        simp [sourceTwoLevelSuccessProbability, hhi]
      have h :=
        realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_zero_of_same_endpoint
          (sourceTwoLevelSuccessProbability s)
          (sourceTwoLevelSuccessProbability_nonneg s)
          (sourceTwoLevelSuccessProbability_le_one s)
          q.2 q.1 false (by simpa using hpHi) (by simpa using hpLo)
          (floorSampleCount g q.2 k) (floorSampleCount g q.1 k)
          (hk q.2 hq.1.2) (hk q.1 hq.1.1)
      simpa [sourceTwoLevelPairValue, binaryRatingModel, hpHi, hpLo] using h
    · have hpHi : sourceTwoLevelSuccessProbability s q.2 = 1 := by
        simp [sourceTwoLevelSuccessProbability, hhi]
      have h :=
        realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_one_of_one_zero
          (sourceTwoLevelSuccessProbability s)
          (sourceTwoLevelSuccessProbability_nonneg s)
          (sourceTwoLevelSuccessProbability_le_one s)
          q.2 q.1 hpHi hpLo
          (floorSampleCount g q.2 k) (floorSampleCount g q.1 k)
          (hk q.2 hq.1.2) (hk q.1 hq.1.1)
      convert h using 1
      norm_num [sourceTwoLevelPairValue, binaryRatingModel, hpHi, hpLo]
  · have hpLo : sourceTwoLevelSuccessProbability s q.1 = 1 := by
      simp [sourceTwoLevelSuccessProbability, hlo]
    have hhi : ¬q.2 < s (1 : Fin ((0 + 2) + 1)) := by
      exact not_lt_of_ge ((le_of_not_gt hlo).trans hq.2.le)
    have hpHi : sourceTwoLevelSuccessProbability s q.2 = 1 := by
      simp [sourceTwoLevelSuccessProbability, hhi]
    have h :=
      realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_zero_of_same_endpoint
        (sourceTwoLevelSuccessProbability s)
        (sourceTwoLevelSuccessProbability_nonneg s)
        (sourceTwoLevelSuccessProbability_le_one s)
        q.2 q.1 true (by simpa using hpHi) (by simpa using hpLo)
        (floorSampleCount g q.2 k) (floorSampleCount g q.1 k)
        (hk q.2 hq.1.2) (hk q.1 hq.1.1)
    simpa [sourceTwoLevelPairValue, binaryRatingModel, hpHi, hpLo] using h

/-- The literal two-level source error `W - W_k` is eventually zero and hence
has infinite extended exponential rate. -/
theorem sourceTwoLevelWError_hasExtendedExponentialRate_top
    (weight : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (hg : SourceMatchingFunction g)
    (s : Fin ((0 + 2) + 1) → ℝ) :
    HasExtendedExponentialRate
      (fun k => sourceTwoLevelLimitingValue weight s -
        sourceTwoLevelFloorValue weight g s k) ⊤ := by
  apply HasExtendedExponentialRate.infinite
  filter_upwards [sourceTwoLevelFloorValue_eventually_eq_limitingValue
    weight g hg s] with k hk
  rw [hk]
  ring

/-- Restricting weights to the source triangle does not change a cross-cell sum. -/
theorem allCrossCellValue_source_triangle_indicator {M : ℕ} (weight : ℝ × ℝ → ℝ)
    (s : Fin (M + 1) → ℝ) (hs : s ∈ finiteOrderedCutpointSet M) :
    allCrossCellValue (sourceOrderedQualityPairs.indicator weight) s =
      allCrossCellValue weight s := by
  unfold allCrossCellValue
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc)
    intro q hq
    apply Set.indicator_of_mem
    refine ⟨?_, ?_⟩
    · exact ⟨⟨(finiteOrderedCutpointSet_mem_quality s hs i.castSucc).1.trans hq.1.1.le,
        hq.1.2.trans (finiteOrderedCutpointSet_mem_quality s hs i.succ).2⟩,
        ⟨(finiteOrderedCutpointSet_mem_quality s hs j.castSucc).1.trans hq.2.1.le,
        hq.2.2.trans (finiteOrderedCutpointSet_mem_quality s hs j.succ).2⟩⟩
    · exact (hq.1.2.trans (hs.1 (show i.succ ≤ j.castSucc from hij))).trans_lt hq.2.1
  · rfl

/-- Source-weight and source-matching version of the global formula optimizer.
The full cross-cell objective is used, and value ties are resolved in the proof;
no unique primary optimizer or preselected tied-rate optimum is assumed. -/
theorem exists_source_weight_allCrossCell_lexicographic_formula {m : ℕ} (hm : 0 < m)
    (weight : ℝ × ℝ → ℝ)
    (hweight_pos : ∀ q ∈ sourceOrderedQualityPairs, 0 < weight q)
    (hweight_norm : ∫ q in sourceOrderedQualityPairs, weight q ∂(volume.prod volume) = 1)
    (g : ℝ → ℝ) (hg : SourceMatchingFunction g) :
    ∃ s : Fin ((m + 2) + 1) → ℝ, ∃ levels : Fin (m + 2) → ℝ,
      s ∈ finiteOrderedCutpointSet (m + 2) ∧ StrictMono s ∧
      BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels (finiteCutpointSampleRate g s) ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin ((m + 2) + 1) → ℝ) × (Fin (m + 2) → ℝ) =>
          design.1 ∈ finiteOrderedCutpointSet (m + 2) ∧ BinaryEndpointLevelVector design.2)
        (fun design => allCrossCellValue weight design.1)
        (fun design => binaryEndpointAwareAdjacentRateObjective design.2
          (finiteCutpointSampleRate g design.1)) (s, levels) := by
  let w := sourceOrderedQualityPairs.indicator weight
  have hw : IntegrableOn w (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) :=
    ((integrable_indicator_iff measurableSet_sourceOrderedQualityPairs).mpr
      (integrableOn_of_source_weight_normalized weight hweight_norm)).integrableOn
  have hwpos : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      q.1 < q.2 → 0 < w q := by
    intro q hq hlt
    change 0 < sourceOrderedQualityPairs.indicator weight q
    rw [Set.indicator_of_mem (show q ∈ sourceOrderedQualityPairs from ⟨hq, hlt⟩)]
    exact hweight_pos q ⟨hq, hlt⟩
  obtain ⟨s, levels, hs, hstrict, hlevels, hequal, hlex⟩ :=
    exists_strict_allCrossCell_lexicographic_formula hm w hw hwpos g hg
  refine ⟨s, levels, hs, hstrict, hlevels, hequal, ⟨hs, hlevels⟩, ?_⟩
  intro design hd
  have h := hlex.2 design hd
  simpa only [w, allCrossCellValue_source_triangle_indicator weight s hs,
    allCrossCellValue_source_triangle_indicator weight design.1 hd.1] using h

/-- Source-facing optimization over strict partitions with consistent lower-closed
cells for both their matching-rate infima and their value integrals. This proves
optimization of the displayed formula, separately from its `W - W_k` meaning. -/
theorem theorem31_source_matching_function_lexicographic_formula {m : ℕ} (hm : 0 < m)
    (weight : ℝ × ℝ → ℝ)
    (hweight_pos : ∀ q ∈ sourceOrderedQualityPairs, 0 < weight q)
    (hweight_norm : ∫ q in sourceOrderedQualityPairs, weight q ∂(volume.prod volume) = 1)
    (g : ℝ → ℝ) (hg : SourceMatchingFunction g) :
    ∃ s : Fin ((m + 2) + 1) → ℝ, ∃ levels : Fin (m + 2) → ℝ,
      s ∈ sourceStrictCutpointSet (m + 2) ∧
      BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels (sourceFiniteSampleRate g s) ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin ((m + 2) + 1) → ℝ) × (Fin (m + 2) → ℝ) =>
          design.1 ∈ sourceStrictCutpointSet (m + 2) ∧ BinaryEndpointLevelVector design.2)
        (fun design => sourceAllCrossCellValue weight design.1)
        (fun design => binaryEndpointAwareAdjacentRateObjective design.2
          (sourceFiniteSampleRate g design.1)) (s, levels) := by
  obtain ⟨s, levels, hs, hstrict, hlevels, hequal, hlex⟩ :=
    exists_source_weight_allCrossCell_lexicographic_formula hm weight hweight_pos hweight_norm g hg
  have hsSource : s ∈ sourceStrictCutpointSet (m + 2) := ⟨hstrict, hs.2⟩
  refine ⟨s, levels, hsSource, hlevels, ?_, ⟨hsSource, hlevels⟩, ?_⟩
  · simpa only [sourceFiniteSampleRate_eq_finiteCutpointSampleRate g hg s hsSource] using hequal
  · intro design hd
    have h := hlex.2 design ⟨sourceStrictCutpointSet_subset hd.1, hd.2⟩
    simpa only [sourceAllCrossCellValue_eq_allCrossCellValue,
      sourceFiniteSampleRate_eq_finiteCutpointSampleRate g hg s hsSource,
      sourceFiniteSampleRate_eq_finiteCutpointSampleRate g hg design.1 hd.1] using h

end

end GJ19OptimalBinaryRatingSystems

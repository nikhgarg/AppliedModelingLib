import KR21Monoculture.AppendixCGenericSourceLawTransport

/-!
# Appendix C Lemma 3: arbitrary-finite coordinate-swap core

This module formalizes the source proof's actual finite-product step.  A
coordinate swap is represented as a measurable equivalence of the full score
space, preserves product Lebesgue measure, and weak well-ordering is lifted
from the two swapped factors to the whole finite iid density.  The transition
cell comparison below is derived from score geometry and this change of
variables argument; it does not take a transition-mass inequality as an
assumption.
-/

open AppliedModelingLib Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

noncomputable section

/-- The source proof's swap of coordinates `0` and `i` on a finite score vector. -/
def appendixCGeneralLemma3Swap {n : ℕ} (i : Candidate n) :
    (Candidate n → ℝ) ≃ᵐ (Candidate n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Candidate n => ℝ) (Equiv.swap 0 i)

@[simp]
theorem appendixCGeneralLemma3Swap_apply_zero {n : ℕ}
    (i : Candidate n) (score : Candidate n → ℝ) :
    appendixCGeneralLemma3Swap i score 0 = score i := by
  simpa [appendixCGeneralLemma3Swap] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Candidate n => ℝ) (Equiv.swap 0 i) score i)

@[simp]
theorem appendixCGeneralLemma3Swap_apply_i {n : ℕ}
    (i : Candidate n) (score : Candidate n → ℝ) :
    appendixCGeneralLemma3Swap i score i = score 0 := by
  simpa [appendixCGeneralLemma3Swap] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Candidate n => ℝ) (Equiv.swap 0 i) score 0)

@[simp]
theorem appendixCGeneralLemma3Swap_apply_of_ne {n : ℕ}
    {i k : Candidate n} (hk0 : k ≠ 0) (hki : k ≠ i)
    (score : Candidate n → ℝ) :
    appendixCGeneralLemma3Swap i score k = score k := by
  simpa [appendixCGeneralLemma3Swap, Equiv.swap_apply_def, hk0, hki] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Candidate n => ℝ) (Equiv.swap 0 i) score k)

/-- Swapping two coordinates preserves finite-dimensional Lebesgue measure. -/
theorem appendixCGeneralLemma3Swap_measurePreserving_volume {n : ℕ}
    (i : Candidate n) :
    MeasurePreserving (appendixCGeneralLemma3Swap i)
      (volume : Measure (Candidate n → ℝ)) volume := by
  simpa [appendixCGeneralLemma3Swap] using
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Candidate n => ℝ) (Equiv.swap 0 i))

/--
Factor a finite product into the two coordinates used by the Appendix C swap
and the untouched coordinates.  This is the arbitrary-finite replacement for
the three-factor algebra in the original implementation.
-/
theorem appendixCGeneralLemma3_prod_factor_zero_i {n : ℕ}
    {i : Candidate n} (hi : i ≠ 0) (g : Candidate n → ℝ) :
    (∏ k : Candidate n, g k) =
      g 0 * g i * (∏ k ∈ (Finset.univ.erase i).erase 0, g k) := by
  calc
    (∏ k : Candidate n, g k) =
        (∏ k ∈ Finset.univ.erase i, g k) * g i :=
      (Finset.prod_erase_mul Finset.univ g (Finset.mem_univ i)).symm
    _ = ((∏ k ∈ (Finset.univ.erase i).erase 0, g k) * g 0) * g i := by
      have hzero : 0 ∈ Finset.univ.erase i := by
        exact Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ _⟩
      rw [← Finset.prod_erase_mul (Finset.univ.erase i) g hzero]
    _ = g 0 * g i * (∏ k ∈ (Finset.univ.erase i).erase 0, g k) := by
      ring

/--
Weak well-ordering compares the full finite iid score density before and after
the source proof's `0`/`i` coordinate swap.  All untouched density factors are
carried explicitly, so this result does not rely on a three-candidate product
or on a named transition-mass premise.
-/
theorem appendixCGeneralLemma3_scoreDensity_swap_le {n : ℕ}
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    {value score : Candidate n → ℝ} {i : Candidate n}
    (hi : i ≠ 0) (hvalue : value i < value 0) (hscore : score 0 < score i) :
    w11CandidateScoreDensity f value 1 score ≤
      w11CandidateScoreDensity f value 1 (appendixCGeneralLemma3Swap i score) := by
  let rest : Finset (Candidate n) := (Finset.univ.erase i).erase 0
  let g : Candidate n → ℝ := fun k => f (score k - value k)
  let gswap : Candidate n → ℝ :=
    fun k => f (appendixCGeneralLemma3Swap i score k - value k)
  have hfactor : ∀ h : Candidate n → ℝ,
      (∏ k : Candidate n, h k) = h 0 * h i * (∏ k ∈ rest, h k) := by
    intro h
    simpa [rest] using appendixCGeneralLemma3_prod_factor_zero_i hi h
  have hrest_eq : (∏ k ∈ rest, gswap k) = ∏ k ∈ rest, g k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      exact (Finset.mem_erase.mp hk).1
    have hki : k ≠ i := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp [g, gswap, appendixCGeneralLemma3Swap_apply_of_ne hk0 hki]
  have hrest_nonneg : 0 ≤ ∏ k ∈ rest, g k := by
    apply Finset.prod_nonneg
    intro k _
    exact hnonneg _
  have hpair :
      f (score 0 - value 0) * f (score i - value i) ≤
        f (score i - value 0) * f (score 0 - value i) :=
    weaklyWellOrderedNoise_swap_middle_density_le hf hvalue hscore
  have hproduct :
      f (score 0 - value 0) * f (score i - value i) * (∏ k ∈ rest, g k) ≤
        f (score i - value 0) * f (score 0 - value i) * (∏ k ∈ rest, g k) :=
    mul_le_mul_of_nonneg_right hpair hrest_nonneg
  calc
    w11CandidateScoreDensity f value 1 score =
        f (score 0 - value 0) * f (score i - value i) * (∏ k ∈ rest, g k) := by
      unfold w11CandidateScoreDensity
      simpa [g] using hfactor g
    _ ≤ f (score i - value 0) * f (score 0 - value i) * (∏ k ∈ rest, g k) :=
      hproduct
    _ = w11CandidateScoreDensity f value 1 (appendixCGeneralLemma3Swap i score) := by
      unfold w11CandidateScoreDensity
      simp only [one_mul]
      change f (score i - value 0) * f (score 0 - value i) * (∏ k ∈ rest, g k) =
        ∏ k : Candidate n, gswap k
      rw [hfactor gswap, hrest_eq]
      simp [g, gswap]

/-- A candidate is a strict score top when every other coordinate is smaller. -/
def appendixCGeneralLemma3StrictTop {n : ℕ}
    (score : Candidate n → ℝ) (c : Candidate n) : Prop :=
  ∀ d : Candidate n, d ≠ c → score d < score c

/-- The score vector obtained by contracting each coordinate toward its value. -/
def appendixCGeneralLemma3ContractedScore {n : ℕ}
    (t : ℝ) (value score : Candidate n → ℝ) : Candidate n → ℝ :=
  fun c => AppliedModelingLib.Probability.rumContractScore t (value c) (score c)

/-- Strict-top cells are measurable from coordinatewise score measurability. -/
theorem measurableSet_appendixCGeneralLemma3StrictTop
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Candidate n → ℝ)
    (hscore : ∀ c : Candidate n, Measurable (fun omega => score omega c))
    (c : Candidate n) :
    MeasurableSet {omega | appendixCGeneralLemma3StrictTop (score omega) c} := by
  let others : Finset (Candidate n) := Finset.univ.erase c
  have hset :
      {omega | appendixCGeneralLemma3StrictTop (score omega) c} =
        ⋂ d ∈ others, {omega | score omega d < score omega c} := by
    ext omega
    constructor
    · intro h
      rw [Set.mem_iInter₂]
      intro d hd
      exact h d (Finset.mem_erase.mp hd).1
    · intro h
      intro d hdc
      rw [Set.mem_iInter₂] at h
      exact h d (Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ _⟩)
  rw [hset]
  refine Finset.measurableSet_biInter others ?_
  intro d _
  exact measurableSet_lt (hscore d) (hscore c)

/-- Each coordinate of the contracted score vector is measurable. -/
theorem measurable_appendixCGeneralLemma3ContractedScore_coordinate
    {n : ℕ} (t : ℝ) (value : Candidate n → ℝ) (c : Candidate n) :
    Measurable (fun score : Candidate n → ℝ =>
      appendixCGeneralLemma3ContractedScore t value score c) := by
  unfold appendixCGeneralLemma3ContractedScore AppliedModelingLib.Probability.rumContractScore
  exact measurable_const.add
    (measurable_const.mul ((measurable_pi_apply c).sub measurable_const))

/--
The strict transition cell from a raw top to a contracted top.  Strict cells
are used here because the absolutely continuous score law discharges ties
separately; this keeps the source swap geometry pointwise.
-/
def appendixCGeneralLemma3TransitionCell {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ)
    (rawTop contractTop : Candidate n) : Set (Candidate n → ℝ) :=
  {score |
    appendixCGeneralLemma3StrictTop score rawTop ∧
      appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value score) contractTop}

theorem measurableSet_appendixCGeneralLemma3TransitionCell {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ)
    (rawTop contractTop : Candidate n) :
    MeasurableSet
      (appendixCGeneralLemma3TransitionCell value t rawTop contractTop) := by
  unfold appendixCGeneralLemma3TransitionCell
  refine (measurableSet_appendixCGeneralLemma3StrictTop
    (fun score : Candidate n → ℝ => score)
    (fun c => measurable_pi_apply c) rawTop).inter ?_
  exact measurableSet_appendixCGeneralLemma3StrictTop
    (appendixCGeneralLemma3ContractedScore t value)
    (measurable_appendixCGeneralLemma3ContractedScore_coordinate t value)
    contractTop

/--
If candidate `i` is a strict contracted top while candidate zero has a larger
true value, then `i`'s raw score was strictly above zero's.  This is the
source proof's implicit score comparison needed for its density swap.
-/
theorem appendixCGeneralLemma3_raw_i_gt_raw_zero_of_strict_contracted_top
    {n : ℕ} {t : ℝ} {value score : Candidate n → ℝ} {i : Candidate n}
    (ht0 : 0 ≤ t) (htlt1 : t < 1) (hi : i ≠ 0)
    (hvalue : value i < value 0)
    (hcontract : appendixCGeneralLemma3StrictTop
      (appendixCGeneralLemma3ContractedScore t value score) i) :
    score 0 < score i := by
  by_contra hnot
  have hraw : score i ≤ score 0 := le_of_not_gt hnot
  have hcontract_le :
      AppliedModelingLib.Probability.rumContractScore t (value 0) (score 0) ≤
        AppliedModelingLib.Probability.rumContractScore t (value i) (score i) :=
    le_of_lt (hcontract 0 (Ne.symm hi))
  have hvalue_le : value 0 ≤ value i :=
    AppliedModelingLib.Probability.rumContractScore_value_le_of_raw_le_and_contract_ge
      (xi := value i) (xj := value 0) (ri := score i) (rj := score 0)
      ht0 htlt1 hraw hcontract_le
  linarith

/-- Contraction is strictly increasing in the true value at a fixed raw score. -/
theorem appendixCGeneralLemma3_contract_strict_in_value_same_raw
    {t xi xj r : ℝ} (htlt1 : t < 1) (hx : xj < xi) :
    AppliedModelingLib.Probability.rumContractScore t xj r <
      AppliedModelingLib.Probability.rumContractScore t xi r := by
  have hcoef : 0 < 1 - t := by linarith
  have hgap : 0 < xi - xj := sub_pos.mpr hx
  have hdiff :
      0 < AppliedModelingLib.Probability.rumContractScore t xi r -
        AppliedModelingLib.Probability.rumContractScore t xj r := by
    rw [AppliedModelingLib.Probability.rumContractScore_sub]
    nlinarith [mul_pos hcoef hgap]
  linarith

/--
The pointwise coordinate-swap geometry in the proof of Appendix C Lemma 3.
Every strict transition from raw winner `j` to contracted winner `i` maps to a
strict transition from the same raw winner `j` to contracted winner zero.
-/
theorem appendixCGeneralLemma3_swap_maps_strict_transition
    {n : ℕ} {t : ℝ} {value : Candidate n → ℝ}
    {i j : Candidate n} (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hi : i ≠ 0) (hj0 : j ≠ 0) (hji : j ≠ i)
    (hvalue : value i < value 0)
    (score : Candidate n → ℝ)
    (hraw : appendixCGeneralLemma3StrictTop score j)
    (hcontract : appendixCGeneralLemma3StrictTop
      (appendixCGeneralLemma3ContractedScore t value score) i) :
    appendixCGeneralLemma3StrictTop (appendixCGeneralLemma3Swap i score) j ∧
      appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value
          (appendixCGeneralLemma3Swap i score)) 0 := by
  have hraw_i0 : score 0 < score i :=
    appendixCGeneralLemma3_raw_i_gt_raw_zero_of_strict_contracted_top
      ht0 htlt1 hi hvalue hcontract
  have hswap_j : appendixCGeneralLemma3Swap i score j = score j :=
    appendixCGeneralLemma3Swap_apply_of_ne hj0 hji score
  simp only [appendixCGeneralLemma3StrictTop] at hraw hcontract ⊢
  constructor
  · intro d hdj
    by_cases hd0 : d = 0
    · subst d
      rw [appendixCGeneralLemma3Swap_apply_zero, hswap_j]
      exact hraw i (Ne.symm hji)
    · by_cases hdi : d = i
      · subst d
        rw [appendixCGeneralLemma3Swap_apply_i, hswap_j]
        exact hraw 0 (Ne.symm hj0)
      · rw [appendixCGeneralLemma3Swap_apply_of_ne hd0 hdi, hswap_j]
        exact hraw d hdj
  · intro d hd0
    by_cases hdi : d = i
    · subst d
      change AppliedModelingLib.Probability.rumContractScore t (value i)
          (appendixCGeneralLemma3Swap i score i) <
        AppliedModelingLib.Probability.rumContractScore t (value 0)
          (appendixCGeneralLemma3Swap i score 0)
      rw [appendixCGeneralLemma3Swap_apply_i,
        appendixCGeneralLemma3Swap_apply_zero]
      exact AppliedModelingLib.Probability.rumContractScore_preserves_strict_order
        ht0 (le_of_lt htlt1) hvalue hraw_i0
    · have hcontract_di :
          AppliedModelingLib.Probability.rumContractScore t (value d) (score d) <
            AppliedModelingLib.Probability.rumContractScore t (value i) (score i) :=
        hcontract d hdi
      have hincrease :
          AppliedModelingLib.Probability.rumContractScore t (value i) (score i) <
            AppliedModelingLib.Probability.rumContractScore t (value 0) (score i) :=
        appendixCGeneralLemma3_contract_strict_in_value_same_raw htlt1 hvalue
      change AppliedModelingLib.Probability.rumContractScore t (value d)
          (appendixCGeneralLemma3Swap i score d) <
        AppliedModelingLib.Probability.rumContractScore t (value 0)
          (appendixCGeneralLemma3Swap i score 0)
      rw [appendixCGeneralLemma3Swap_apply_zero]
      calc
        AppliedModelingLib.Probability.rumContractScore t (value d)
            (appendixCGeneralLemma3Swap i score d) =
            AppliedModelingLib.Probability.rumContractScore t (value d) (score d) := by
              rw [appendixCGeneralLemma3Swap_apply_of_ne hd0 hdi]
        _ < AppliedModelingLib.Probability.rumContractScore t (value i) (score i) :=
          hcontract_di
        _ < AppliedModelingLib.Probability.rumContractScore t (value 0) (score i) :=
          hincrease

/-- The swap maps the source strict transition cell into its zero-top target cell. -/
theorem appendixCGeneralLemma3Swap_maps_transitionCell
    {n : ℕ} {t : ℝ} {value : Candidate n → ℝ}
    {i j : Candidate n} (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hi : i ≠ 0) (hj0 : j ≠ 0) (hji : j ≠ i)
    (hvalue : value i < value 0) :
    ∀ score ∈ appendixCGeneralLemma3TransitionCell value t j i,
      appendixCGeneralLemma3Swap i score ∈
        appendixCGeneralLemma3TransitionCell value t j 0 := by
  intro score hscore
  change appendixCGeneralLemma3StrictTop score j ∧
      appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value score) i at hscore
  change appendixCGeneralLemma3StrictTop (appendixCGeneralLemma3Swap i score) j ∧
      appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value
          (appendixCGeneralLemma3Swap i score)) 0
  exact appendixCGeneralLemma3_swap_maps_strict_transition
    ht0 htlt1 hi hj0 hji hvalue score hscore.1 hscore.2

/--
The arbitrary-finite, strict-cell mass comparison used by Appendix C Lemma 3.
It is obtained from the actual swap, event inclusion, and product-density
inequality; no transition-mass comparison is assumed.
-/
theorem appendixCGeneralLemma3_transitionCell_measure_le
    {n : ℕ} {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    (hfmeas : Measurable f) (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    {t : ℝ} {value : Candidate n → ℝ} {i j : Candidate n}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hi : i ≠ 0) (hj0 : j ≠ 0) (hji : j ≠ i)
    (hvalue : value i < value 0) :
    (volume : Measure (Candidate n → ℝ)).withDensity
      (w11CandidateScoreDensityENN f value 1)
      (appendixCGeneralLemma3TransitionCell value t j i) ≤
    (volume : Measure (Candidate n → ℝ)).withDensity
      (w11CandidateScoreDensityENN f value 1)
      (appendixCGeneralLemma3TransitionCell value t j 0) := by
  refine withDensity_measure_le_of_measurableEquiv_image_subset_density_le
    (volume : Measure (Candidate n → ℝ))
    (appendixCGeneralLemma3Swap i)
    (appendixCGeneralLemma3Swap_measurePreserving_volume i)
    (w11CandidateScoreDensityENN f value 1)
    (measurableSet_appendixCGeneralLemma3TransitionCell value t j i)
    (measurableSet_appendixCGeneralLemma3TransitionCell value t j 0)
    (appendixCGeneralLemma3Swap_maps_transitionCell
      ht0 htlt1 hi hj0 hji hvalue) ?_
  intro score hscore
  unfold w11CandidateScoreDensityENN
  apply ENNReal.ofReal_le_ofReal
  change appendixCGeneralLemma3StrictTop score j ∧
      appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value score) i at hscore
  exact appendixCGeneralLemma3_scoreDensity_swap_le hf hnonneg hi hvalue
    (appendixCGeneralLemma3_raw_i_gt_raw_zero_of_strict_contracted_top
      ht0 htlt1 hi hvalue hscore.2)

/--
The strict incoming mass for candidate `i`: some strictly lower-valued raw
winner becomes the strict contracted winner `i`.  This is the finite union of
the source proof's `S_{j\to i}` cells.
-/
noncomputable def appendixCGeneralLemma3IncomingCell {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ) (i : Candidate n) :
    Set (Candidate n → ℝ) :=
  ⋃ j ∈ Finset.univ.filter (fun j => value j < value i),
    appendixCGeneralLemma3TransitionCell value t j i

/-- The strict incoming mass for the highest-valued candidate zero. -/
noncomputable def appendixCGeneralLemma3IncomingZeroCell {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ) : Set (Candidate n → ℝ) :=
  ⋃ j ∈ Finset.univ.erase 0,
    appendixCGeneralLemma3TransitionCell value t j 0

theorem measurableSet_appendixCGeneralLemma3IncomingCell {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ) (i : Candidate n) :
    MeasurableSet (appendixCGeneralLemma3IncomingCell value t i) := by
  classical
  unfold appendixCGeneralLemma3IncomingCell
  apply Finset.measurableSet_biUnion
  intro j hj
  exact measurableSet_appendixCGeneralLemma3TransitionCell value t j i

theorem measurableSet_appendixCGeneralLemma3IncomingZeroCell {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ) :
    MeasurableSet (appendixCGeneralLemma3IncomingZeroCell value t) := by
  classical
  unfold appendixCGeneralLemma3IncomingZeroCell
  apply Finset.measurableSet_biUnion
  intro j hj
  exact measurableSet_appendixCGeneralLemma3TransitionCell value t j 0

/--
The source's full `S_{j\to i}` union has no more score-law mass than the
corresponding incoming union for zero.  The argument is one global
change-of-variables application, so it does not need an invalid sum-over-cells
identity when cells are represented as strict events.
-/
theorem appendixCGeneralLemma3_incomingCell_measure_le_incomingZeroCell
    {n : ℕ} {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    (hfmeas : Measurable f) (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    {t : ℝ} {value : Candidate n → ℝ} {i : Candidate n}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hi : i ≠ 0) (hvalue : value i < value 0) :
    (volume : Measure (Candidate n → ℝ)).withDensity
      (w11CandidateScoreDensityENN f value 1)
      (appendixCGeneralLemma3IncomingCell value t i) ≤
    (volume : Measure (Candidate n → ℝ)).withDensity
      (w11CandidateScoreDensityENN f value 1)
      (appendixCGeneralLemma3IncomingZeroCell value t) := by
  classical
  refine withDensity_measure_le_of_measurableEquiv_image_subset_density_le
    (volume : Measure (Candidate n → ℝ))
    (appendixCGeneralLemma3Swap i)
    (appendixCGeneralLemma3Swap_measurePreserving_volume i)
    (w11CandidateScoreDensityENN f value 1)
    (measurableSet_appendixCGeneralLemma3IncomingCell value t i)
    (measurableSet_appendixCGeneralLemma3IncomingZeroCell value t) ?_ ?_
  · intro score hscore
    change score ∈ ⋃ j ∈ Finset.univ.filter (fun j => value j < value i),
      appendixCGeneralLemma3TransitionCell value t j i at hscore
    rw [Set.mem_iUnion₂] at hscore
    rcases hscore with ⟨j, hj, hcell⟩
    have hjvalue : value j < value i := Finset.mem_filter.mp hj |>.2
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      linarith
    have hji : j ≠ i := by
      intro h
      subst j
      linarith
    change appendixCGeneralLemma3Swap i score ∈
      ⋃ j ∈ Finset.univ.erase 0,
        appendixCGeneralLemma3TransitionCell value t j 0
    rw [Set.mem_iUnion₂]
    refine ⟨j, Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ _⟩, ?_⟩
    exact appendixCGeneralLemma3Swap_maps_transitionCell
      ht0 htlt1 hi hj0 hji hvalue score hcell
  · intro score hscore
    unfold w11CandidateScoreDensityENN
    apply ENNReal.ofReal_le_ofReal
    change score ∈ ⋃ j ∈ Finset.univ.filter (fun j => value j < value i),
      appendixCGeneralLemma3TransitionCell value t j i at hscore
    rw [Set.mem_iUnion₂] at hscore
    rcases hscore with ⟨j, hj, hcell⟩
    change appendixCGeneralLemma3StrictTop score j ∧
        appendixCGeneralLemma3StrictTop
          (appendixCGeneralLemma3ContractedScore t value score) i at hcell
    exact appendixCGeneralLemma3_scoreDensity_swap_le hf hnonneg hi hvalue
      (appendixCGeneralLemma3_raw_i_gt_raw_zero_of_strict_contracted_top
        ht0 htlt1 hi hvalue hcell.2)

/-- Pairwise score distinctness, separated from the ranking tie convention. -/
def appendixCGeneralLemma3NoTies {n : ℕ}
    (score : Candidate n → ℝ) : Prop :=
  ∀ a b : Candidate n, a ≠ b → score a ≠ score b

/-- A tie-free score vector has the expected strict-top characterization of first choice. -/
theorem appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
    {n : ℕ} {score : Candidate n → ℝ} {c : Candidate n}
    (hnoTie : appendixCGeneralLemma3NoTies score) :
    appendixCGeneralLemma3StrictTop score c ↔
      firstChoice (rankByScore score) = c := by
  constructor
  · intro htop
    have hbest : bestInSet (rankByScore score) Finset.univ = c :=
      bestInSet_rankByScore_univ_eq_of_strict_top htop
    simpa using hbest
  · intro hfirst
    intro d hdc
    have hle : score d ≤ score c := by
      apply rankByScore_weaklyOrdersScores score
      calc
        rankOf (rankByScore score) c = 0 := by
          rw [← hfirst]
          exact rankOf_firstChoice (rankByScore score)
        _ ≤ rankOf (rankByScore score) d := bot_le
    exact lt_of_le_of_ne hle (hnoTie d c hdc)

/-- The finite iid score-density law assigns zero mass to every raw-score tie plane. -/
theorem appendixCGeneralLemma3_score_noTies_ae
    {n : ℕ} (f : ℝ → ℝ) (value : Candidate n → ℝ) :
    ∀ᵐ score ∂(volume : Measure (Candidate n → ℝ)).withDensity
      (w11CandidateScoreDensityENN f value 1),
      appendixCGeneralLemma3NoTies score := by
  classical
  unfold appendixCGeneralLemma3NoTies
  refine Filter.eventually_all.2 ?_
  intro a
  refine Filter.eventually_all.2 ?_
  intro b
  by_cases hab : a = b
  · exact Filter.Eventually.of_forall fun _ hne => (hne hab).elim
  · have hzero :
        ((volume : Measure (Candidate n → ℝ)).withDensity
          (w11CandidateScoreDensityENN f value 1))
          {score | score a = score b} = 0 := by
        refine measure_mono_null ?_
          (withDensity_realPi_eval_sub_eq_measure_zero
            (w11CandidateScoreDensityENN f value 1) hab 0)
        intro score hscore
        change score a - score b = 0
        change score a = score b at hscore
        linarith
    have hae : ∀ᵐ score ∂(volume : Measure (Candidate n → ℝ)).withDensity
        (w11CandidateScoreDensityENN f value 1), score a ≠ score b := by
      simpa using (measure_eq_zero_iff_ae_notMem.1 hzero)
    exact hae.mono fun _ hne _ => hne

/-- Positive contraction keeps the contracted-score tie locus on an affine hyperplane. -/
theorem appendixCGeneralLemma3_contractedScore_noTies_ae
    {n : ℕ} (f : ℝ → ℝ) (value : Candidate n → ℝ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ score ∂(volume : Measure (Candidate n → ℝ)).withDensity
      (w11CandidateScoreDensityENN f value 1),
      appendixCGeneralLemma3NoTies
        (appendixCGeneralLemma3ContractedScore t value score) := by
  classical
  unfold appendixCGeneralLemma3NoTies
  refine Filter.eventually_all.2 ?_
  intro a
  refine Filter.eventually_all.2 ?_
  intro b
  by_cases hab : a = b
  · exact Filter.Eventually.of_forall fun _ hne => (hne hab).elim
  · let offset : ℝ := (t - 1) * (value a - value b) / t
    have hzero :
        ((volume : Measure (Candidate n → ℝ)).withDensity
          (w11CandidateScoreDensityENN f value 1))
          {score |
            appendixCGeneralLemma3ContractedScore t value score a =
              appendixCGeneralLemma3ContractedScore t value score b} = 0 := by
        refine measure_mono_null ?_
          (withDensity_realPi_eval_sub_eq_measure_zero
            (w11CandidateScoreDensityENN f value 1) hab offset)
        intro score hscore
        change score a - score b = offset
        change AppliedModelingLib.Probability.rumContractScore t (value a) (score a) =
          AppliedModelingLib.Probability.rumContractScore t (value b) (score b) at hscore
        have hdiff :
            AppliedModelingLib.Probability.rumContractScore t (value a) (score a) -
              AppliedModelingLib.Probability.rumContractScore t (value b) (score b) = 0 :=
          sub_eq_zero.mpr hscore
        rw [AppliedModelingLib.Probability.rumContractScore_sub] at hdiff
        dsimp [offset]
        apply (eq_div_iff (ne_of_gt ht)).2
        nlinarith
    have hae : ∀ᵐ score ∂(volume : Measure (Candidate n → ℝ)).withDensity
        (w11CandidateScoreDensityENN f value 1),
        appendixCGeneralLemma3ContractedScore t value score a ≠
          appendixCGeneralLemma3ContractedScore t value score b := by
      simpa using (measure_eq_zero_iff_ae_notMem.1 hzero)
    exact hae.mono fun _ hne _ => hne

/-- A genuine contraction strictly favors a strictly higher value even if its raw score only ties. -/
theorem appendixCGeneralLemma3_contract_strict_of_value_lt_raw_le
    {t xi xj ri rj : ℝ} (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hx : xj < xi) (hr : rj ≤ ri) :
    AppliedModelingLib.Probability.rumContractScore t xj rj <
      AppliedModelingLib.Probability.rumContractScore t xi ri := by
  have h1t : 0 < 1 - t := by linarith
  have hxgap : 0 < xi - xj := sub_pos.mpr hx
  have hrgap : 0 ≤ ri - rj := sub_nonneg.mpr hr
  have hdiff :
      0 < AppliedModelingLib.Probability.rumContractScore t xi ri -
        AppliedModelingLib.Probability.rumContractScore t xj rj := by
    rw [AppliedModelingLib.Probability.rumContractScore_sub]
    have hvalueTerm : 0 < (1 - t) * (xi - xj) := mul_pos h1t hxgap
    have hrawTerm : 0 ≤ t * (ri - rj) := mul_nonneg ht0 hrgap
    linarith
  linarith

/-- The canonical raw winner has a weakly maximal raw score. -/
theorem appendixCGeneralLemma3_rawWinner_maximizes
    {n : ℕ} (score : Candidate n → ℝ) (d : Candidate n) :
    score d ≤ score (firstChoice (rankByScore score)) := by
  apply rankByScore_weaklyOrdersScores score
  calc
    rankOf (rankByScore score) (firstChoice (rankByScore score)) = 0 :=
      rankOf_firstChoice (rankByScore score)
    _ ≤ rankOf (rankByScore score) d := bot_le

/-- The canonical contracted winner has a weakly maximal contracted score. -/
theorem appendixCGeneralLemma3_contractedWinner_maximizes
    {n : ℕ} (t : ℝ) (value score : Candidate n → ℝ) (d : Candidate n) :
    appendixCGeneralLemma3ContractedScore t value score d ≤
      appendixCGeneralLemma3ContractedScore t value score
        (firstChoice (rankByScore (appendixCGeneralLemma3ContractedScore t value score))) := by
  apply rankByScore_weaklyOrdersScores
    (appendixCGeneralLemma3ContractedScore t value score)
  calc
    rankOf (rankByScore (appendixCGeneralLemma3ContractedScore t value score))
        (firstChoice (rankByScore (appendixCGeneralLemma3ContractedScore t value score))) = 0 :=
      rankOf_firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score))
    _ ≤ rankOf (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) d :=
      bot_le

/-- Moving to the contracted canonical winner cannot lower its true value. -/
theorem appendixCGeneralLemma3_rawWinner_value_le_contractedWinner
    {n : ℕ} {t : ℝ} {value score : Candidate n → ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1) :
    value (firstChoice (rankByScore score)) ≤
      value (firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score))) := by
  apply AppliedModelingLib.Probability.rumContractScore_value_le_of_raw_max_and_contract_max
    ht0 htlt1
  · exact appendixCGeneralLemma3_rawWinner_maximizes score
  · intro d
    exact appendixCGeneralLemma3_contractedWinner_maximizes t value score d

/-- A uniquely highest-valued candidate cannot leave first place under contraction. -/
theorem appendixCGeneralLemma3_zero_stays_firstChoice
    {n : ℕ} {t : ℝ} {value score : Candidate n → ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hzeroValue : ∀ d : Candidate n, d ≠ 0 → value d < value 0)
    (hraw : firstChoice (rankByScore score) = 0) :
    firstChoice
      (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0 := by
  have htop : appendixCGeneralLemma3StrictTop
      (appendixCGeneralLemma3ContractedScore t value score) 0 := by
    intro d hd
    have hrawMax : score d ≤ score 0 := by
      rw [← hraw]
      exact appendixCGeneralLemma3_rawWinner_maximizes score d
    exact appendixCGeneralLemma3_contract_strict_of_value_lt_raw_le
      ht0 htlt1 (hzeroValue d hd) hrawMax
  have hbest : bestInSet
      (rankByScore (appendixCGeneralLemma3ContractedScore t value score))
      Finset.univ = 0 :=
    bestInSet_rankByScore_univ_eq_of_strict_top htop
  simpa using hbest

/-- The raw and contracted canonical first-choice maps are measurable. -/
theorem measurable_appendixCGeneralLemma3_firstChoicePair
    {n : ℕ} (t : ℝ) (value : Candidate n → ℝ) :
    Measurable (fun score : Candidate n → ℝ =>
      (firstChoice (rankByScore score),
        firstChoice
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)))) := by
  have hraw : Measurable (fun score : Candidate n → ℝ => rankByScore score) :=
    measurable_rankByScore (fun score : Candidate n → ℝ => score)
      (fun c => measurable_pi_apply c)
  have hcontract : Measurable (fun score : Candidate n → ℝ =>
      rankByScore (appendixCGeneralLemma3ContractedScore t value score)) :=
    measurable_rankByScore (appendixCGeneralLemma3ContractedScore t value)
      (measurable_appendixCGeneralLemma3ContractedScore_coordinate t value)
  exact Measurable.prod
    ((measurable_of_finite firstChoice).comp hraw)
    ((measurable_of_finite firstChoice).comp hcontract)

/-- The actual rank-based event corresponding to a lower-valued arrival into `i`. -/
abbrev appendixCGeneralLemma3IncomingRankEvent {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ) (i : Candidate n)
    (score : Candidate n → ℝ) : Prop :=
  firstChoice (rankByScore score) ≠ i ∧
    firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i ∧
      value (firstChoice (rankByScore score)) < value i

/-- The actual rank-based event corresponding to an arrival into candidate zero. -/
abbrev appendixCGeneralLemma3IncomingZeroRankEvent {n : ℕ}
    (value : Candidate n → ℝ) (t : ℝ) (score : Candidate n → ℝ) : Prop :=
  firstChoice (rankByScore score) ≠ 0 ∧
    firstChoice
      (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0

/-- Off ties, the semantic incoming event is exactly the union of strict source cells. -/
theorem appendixCGeneralLemma3_mem_incomingCell_iff_incomingRankEvent
    {n : ℕ} {value score : Candidate n → ℝ} {t : ℝ} {i : Candidate n}
    (hrawNoTies : appendixCGeneralLemma3NoTies score)
    (hcontractNoTies : appendixCGeneralLemma3NoTies
      (appendixCGeneralLemma3ContractedScore t value score)) :
    score ∈ appendixCGeneralLemma3IncomingCell value t i ↔
      appendixCGeneralLemma3IncomingRankEvent value t i score := by
  classical
  constructor
  · intro hmem
    change score ∈ ⋃ j ∈ Finset.univ.filter (fun j => value j < value i),
      appendixCGeneralLemma3TransitionCell value t j i at hmem
    rw [Set.mem_iUnion₂] at hmem
    rcases hmem with ⟨j, hj, hcell⟩
    have hjvalue : value j < value i := Finset.mem_filter.mp hj |>.2
    change appendixCGeneralLemma3StrictTop score j ∧
        appendixCGeneralLemma3StrictTop
          (appendixCGeneralLemma3ContractedScore t value score) i at hcell
    have hrawFirst : firstChoice (rankByScore score) = j :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hrawNoTies).mp hcell.1
    have hcontractFirst : firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hcontractNoTies).mp hcell.2
    unfold appendixCGeneralLemma3IncomingRankEvent
    refine ⟨?_, hcontractFirst, ?_⟩
    · rw [hrawFirst]
      intro hji
      exact (ne_of_lt hjvalue) (congrArg value hji)
    · rw [hrawFirst]
      exact hjvalue
  · intro hmem
    unfold appendixCGeneralLemma3IncomingRankEvent at hmem
    let j : Candidate n := firstChoice (rankByScore score)
    have hrawFirst : firstChoice (rankByScore score) = j := rfl
    have hrawTop : appendixCGeneralLemma3StrictTop score j :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hrawNoTies).mpr hrawFirst
    have hcontractTop : appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value score) i :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hcontractNoTies).mpr hmem.2.1
    change score ∈ ⋃ j ∈ Finset.univ.filter (fun j => value j < value i),
      appendixCGeneralLemma3TransitionCell value t j i
    rw [Set.mem_iUnion₂]
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa [j] using hmem.2.2
    · exact ⟨hrawTop, hcontractTop⟩

/-- Off ties, the semantic zero-arrival event is exactly the strict zero-cell union. -/
theorem appendixCGeneralLemma3_mem_incomingZeroCell_iff_incomingZeroRankEvent
    {n : ℕ} {value score : Candidate n → ℝ} {t : ℝ}
    (hrawNoTies : appendixCGeneralLemma3NoTies score)
    (hcontractNoTies : appendixCGeneralLemma3NoTies
      (appendixCGeneralLemma3ContractedScore t value score)) :
    score ∈ appendixCGeneralLemma3IncomingZeroCell value t ↔
      appendixCGeneralLemma3IncomingZeroRankEvent value t score := by
  classical
  constructor
  · intro hmem
    change score ∈ ⋃ j ∈ Finset.univ.erase 0,
      appendixCGeneralLemma3TransitionCell value t j 0 at hmem
    rw [Set.mem_iUnion₂] at hmem
    rcases hmem with ⟨j, hj, hcell⟩
    have hj0 : j ≠ 0 := Finset.mem_erase.mp hj |>.1
    change appendixCGeneralLemma3StrictTop score j ∧
        appendixCGeneralLemma3StrictTop
          (appendixCGeneralLemma3ContractedScore t value score) 0 at hcell
    have hrawFirst : firstChoice (rankByScore score) = j :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hrawNoTies).mp hcell.1
    have hcontractFirst : firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0 :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hcontractNoTies).mp hcell.2
    unfold appendixCGeneralLemma3IncomingZeroRankEvent
    refine ⟨?_, hcontractFirst⟩
    rw [hrawFirst]
    exact hj0
  · intro hmem
    unfold appendixCGeneralLemma3IncomingZeroRankEvent at hmem
    let j : Candidate n := firstChoice (rankByScore score)
    have hrawFirst : firstChoice (rankByScore score) = j := rfl
    have hrawTop : appendixCGeneralLemma3StrictTop score j :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hrawNoTies).mpr hrawFirst
    have hcontractTop : appendixCGeneralLemma3StrictTop
        (appendixCGeneralLemma3ContractedScore t value score) 0 :=
      (appendixCGeneralLemma3_strictTop_iff_firstChoice_of_noTies
        hcontractNoTies).mpr hmem.2
    change score ∈ ⋃ j ∈ Finset.univ.erase 0,
      appendixCGeneralLemma3TransitionCell value t j 0
    rw [Set.mem_iUnion₂]
    refine ⟨j, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · simpa [j] using hmem.1
    · exact ⟨hrawTop, hcontractTop⟩

/-- Pointwise accounting: a gain by `i` is an arrival into `i` from a lower value. -/
theorem appendixCGeneralLemma3_delta_indicator_le_incomingRankEvent
    {n : ℕ} {t : ℝ} {value score : Candidate n → ℝ} {i : Candidate n}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hvalueInjective : Function.Injective value) :
    (if firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i
      then (1 : ℝ) else 0) -
      (if firstChoice (rankByScore score) = i then (1 : ℝ) else 0) ≤
    (if appendixCGeneralLemma3IncomingRankEvent value t i score
      then (1 : ℝ) else 0) - (if False then (1 : ℝ) else 0) := by
  classical
  change
    (if (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = i
      then (1 : ℝ) else 0) -
      (if (rankByScore score) 0 = i then (1 : ℝ) else 0) ≤
    (if appendixCGeneralLemma3IncomingRankEvent value t i score
      then (1 : ℝ) else 0) - (if False then (1 : ℝ) else 0)
  by_cases hcontract :
      (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = i
  · by_cases hraw : (rankByScore score) 0 = i
    · have hnonneg : 0 ≤
          (if appendixCGeneralLemma3IncomingRankEvent value t i score
            then (1 : ℝ) else 0) := by
        split <;> norm_num
      rw [if_pos hcontract, if_pos hraw]
      simpa using hnonneg
    · have hvalueLe : value ((rankByScore score) 0) ≤ value i := by
        rw [← hcontract]
        simpa only [firstChoice] using
          (appendixCGeneralLemma3_rawWinner_value_le_contractedWinner
            (score := score) ht0 htlt1)
      have hvalueNe : value ((rankByScore score) 0) ≠ value i := by
        intro h
        apply hraw
        exact hvalueInjective h
      have hvalueLt : value ((rankByScore score) 0) < value i :=
        lt_of_le_of_ne hvalueLe hvalueNe
      have hin : appendixCGeneralLemma3IncomingRankEvent value t i score := by
        change (rankByScore score) 0 ≠ i ∧
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = i ∧
            value ((rankByScore score) 0) < value i
        exact ⟨hraw, hcontract, hvalueLt⟩
      rw [if_pos hcontract, if_neg hraw, if_pos hin]
      norm_num
  · have hrawNonneg : 0 ≤ (if (rankByScore score) 0 = i then (1 : ℝ) else 0) := by
      split <;> norm_num
    have hinNonneg : 0 ≤
        (if appendixCGeneralLemma3IncomingRankEvent value t i score
          then (1 : ℝ) else 0) := by
      split <;> norm_num
    have hmain :
        -(if (rankByScore score) 0 = i then (1 : ℝ) else 0) ≤
          (if appendixCGeneralLemma3IncomingRankEvent value t i score
            then (1 : ℝ) else 0) :=
      (neg_nonpos.mpr hrawNonneg).trans hinNonneg
    simpa [hcontract] using hmain

/-- Pointwise accounting: an arrival into zero is bounded by zero's probability gain. -/
theorem appendixCGeneralLemma3_incomingZeroRankEvent_indicator_le_delta
    {n : ℕ} {t : ℝ} {value score : Candidate n → ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hzeroValue : ∀ d : Candidate n, d ≠ 0 → value d < value 0) :
    (if appendixCGeneralLemma3IncomingZeroRankEvent value t score
      then (1 : ℝ) else 0) - (if False then (1 : ℝ) else 0) ≤
    (if firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0
      then (1 : ℝ) else 0) -
      (if firstChoice (rankByScore score) = 0 then (1 : ℝ) else 0) := by
  classical
  change
    (if appendixCGeneralLemma3IncomingZeroRankEvent value t score
      then (1 : ℝ) else 0) - (if False then (1 : ℝ) else 0) ≤
    (if (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = 0
      then (1 : ℝ) else 0) -
      (if (rankByScore score) 0 = 0 then (1 : ℝ) else 0)
  by_cases hraw : (rankByScore score) 0 = 0
  · have hraw' : firstChoice (rankByScore score) = 0 := by
      simpa only [firstChoice] using hraw
    have hcontract' : firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0 :=
      appendixCGeneralLemma3_zero_stays_firstChoice ht0 htlt1 hzeroValue hraw'
    have hcontract :
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = 0 := by
      simpa only [firstChoice] using hcontract'
    have hin : ¬ appendixCGeneralLemma3IncomingZeroRankEvent value t score := by
      intro hin
      change (rankByScore score) 0 ≠ 0 ∧
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = 0 at hin
      exact hin.1 hraw
    simp [hraw, hcontract, hin]
  · by_cases hcontract :
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = 0
    · have hin : appendixCGeneralLemma3IncomingZeroRankEvent value t score := by
        change (rankByScore score) 0 ≠ 0 ∧
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = 0
        exact ⟨hraw, hcontract⟩
      rw [if_pos hin, if_pos hcontract, if_neg hraw]
      norm_num
    · have hin : ¬ appendixCGeneralLemma3IncomingZeroRankEvent value t score := by
        intro hin
        change (rankByScore score) 0 ≠ 0 ∧
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) 0 = 0 at hin
        exact hcontract hin.2
      simp [hraw, hcontract, hin]

/-- Probability accounting for the gain of an arbitrary non-top candidate. -/
theorem appendixCGeneralLemma3_delta_le_incomingRankEvent
    {n : ℕ} (μ : Measure (Candidate n → ℝ)) [IsProbabilityMeasure μ]
    {t : ℝ} {value : Candidate n → ℝ} {i : Candidate n}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hvalueInjective : Function.Injective value) :
    measureProb μ (fun score => firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i) -
      measureProb μ (fun score => firstChoice (rankByScore score) = i) ≤
    measureProb μ (appendixCGeneralLemma3IncomingRankEvent value t i) := by
  classical
  let firstPair : (Candidate n → ℝ) → Candidate n × Candidate n := fun score =>
    (firstChoice (rankByScore score),
      firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)))
  have hpair : Measurable firstPair := by
    simpa [firstPair] using
      (measurable_appendixCGeneralLemma3_firstChoicePair t value)
  simpa [firstPair, appendixCGeneralLemma3IncomingRankEvent] using
    (measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
      (μ := μ) (f := firstPair) hpair
      (p := fun pair : Candidate n × Candidate n => pair.2 = i)
      (q := fun pair : Candidate n × Candidate n => pair.1 = i)
      (r := fun pair : Candidate n × Candidate n =>
        pair.1 ≠ i ∧ pair.2 = i ∧ value pair.1 < value i)
      (s := fun _ : Candidate n × Candidate n => False)
      MeasurableSet.of_discrete MeasurableSet.of_discrete
      MeasurableSet.of_discrete MeasurableSet.of_discrete
      (by
        intro score
        exact appendixCGeneralLemma3_delta_indicator_le_incomingRankEvent
          ht0 htlt1 hvalueInjective))

/-- Probability accounting for the gain of the highest-valued candidate zero. -/
theorem appendixCGeneralLemma3_incomingZeroRankEvent_le_delta
    {n : ℕ} (μ : Measure (Candidate n → ℝ)) [IsProbabilityMeasure μ]
    {t : ℝ} {value : Candidate n → ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hzeroValue : ∀ d : Candidate n, d ≠ 0 → value d < value 0) :
    measureProb μ (appendixCGeneralLemma3IncomingZeroRankEvent value t) ≤
      measureProb μ (fun score => firstChoice
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0) -
        measureProb μ (fun score => firstChoice (rankByScore score) = 0) := by
  classical
  let firstPair : (Candidate n → ℝ) → Candidate n × Candidate n := fun score =>
    (firstChoice (rankByScore score),
      firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)))
  have hpair : Measurable firstPair := by
    simpa [firstPair] using
      (measurable_appendixCGeneralLemma3_firstChoicePair t value)
  simpa [firstPair, appendixCGeneralLemma3IncomingZeroRankEvent] using
    (measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
      (μ := μ) (f := firstPair) hpair
      (p := fun pair : Candidate n × Candidate n => pair.1 ≠ 0 ∧ pair.2 = 0)
      (q := fun _ : Candidate n × Candidate n => False)
      (r := fun pair : Candidate n × Candidate n => pair.2 = 0)
      (s := fun pair : Candidate n × Candidate n => pair.1 = 0)
      MeasurableSet.of_discrete MeasurableSet.of_discrete
      MeasurableSet.of_discrete MeasurableSet.of_discrete
      (by
        intro score
        exact appendixCGeneralLemma3_incomingZeroRankEvent_indicator_le_delta
          ht0 htlt1 hzeroValue))

/--
Appendix C Lemma 3 on the actual arbitrary-finite iid score-density law.
The proof derives the transition comparison, tie bridge, and probability
accounting from the density and contraction geometry; it accepts no
transition-mass or conclusion-shaped certificate.
-/
theorem appendixCGeneralLemma3_scoreLaw_delta_le_top_delta
    {n : ℕ} {f : ℝ → ℝ}
    (hf : WeaklyWellOrderedNoise f) (hfmeas : Measurable f)
    (hfintegrable : Integrable f volume)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    {t : ℝ} {value : Candidate n → ℝ} {i : Candidate n}
    (ht0 : 0 ≤ t) (htpos : 0 < t) (htlt1 : t < 1)
    (hi : i ≠ 0) (hvalue : value i < value 0)
    (hvalueInjective : Function.Injective value)
    (hzeroValue : ∀ d : Candidate n, d ≠ 0 → value d < value 0) :
    measureProb (w11CandidateScoreLaw f value 1) (fun score => firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i) -
      measureProb (w11CandidateScoreLaw f value 1)
        (fun score => firstChoice (rankByScore score) = i) ≤
    measureProb (w11CandidateScoreLaw f value 1) (fun score => firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0) -
      measureProb (w11CandidateScoreLaw f value 1)
        (fun score => firstChoice (rankByScore score) = 0) := by
  classical
  let μ : Measure (Candidate n → ℝ) := w11CandidateScoreLaw f value 1
  letI : IsProbabilityMeasure μ :=
    w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization
      n f hfintegrable hnonneg hnormalized value 1
  have hdeltaI :
      measureProb μ (fun score => firstChoice
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i) -
        measureProb μ (fun score => firstChoice (rankByScore score) = i) ≤
      measureProb μ (appendixCGeneralLemma3IncomingRankEvent value t i) :=
    appendixCGeneralLemma3_delta_le_incomingRankEvent μ
      ht0 htlt1 hvalueInjective
  have hdeltaZero :
      measureProb μ (appendixCGeneralLemma3IncomingZeroRankEvent value t) ≤
        measureProb μ (fun score => firstChoice
            (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0) -
          measureProb μ (fun score => firstChoice (rankByScore score) = 0) :=
    appendixCGeneralLemma3_incomingZeroRankEvent_le_delta μ
      ht0 htlt1 hzeroValue
  have hrawNoTies : ∀ᵐ score ∂μ, appendixCGeneralLemma3NoTies score := by
    simpa [μ, w11CandidateScoreLaw] using
      (appendixCGeneralLemma3_score_noTies_ae f value)
  have hcontractNoTies : ∀ᵐ score ∂μ,
      appendixCGeneralLemma3NoTies
        (appendixCGeneralLemma3ContractedScore t value score) := by
    simpa [μ, w11CandidateScoreLaw] using
      (appendixCGeneralLemma3_contractedScore_noTies_ae f value htpos)
  have hIncomingEq :
      μ {score | appendixCGeneralLemma3IncomingRankEvent value t i score} =
        μ (appendixCGeneralLemma3IncomingCell value t i) := by
    apply measure_congr
    filter_upwards [hrawNoTies, hcontractNoTies] with score hraw hcontract
    exact propext
      (appendixCGeneralLemma3_mem_incomingCell_iff_incomingRankEvent
        hraw hcontract).symm
  have hIncomingZeroEq :
      μ {score | appendixCGeneralLemma3IncomingZeroRankEvent value t score} =
        μ (appendixCGeneralLemma3IncomingZeroCell value t) := by
    apply measure_congr
    filter_upwards [hrawNoTies, hcontractNoTies] with score hraw hcontract
    exact propext
      (appendixCGeneralLemma3_mem_incomingZeroCell_iff_incomingZeroRankEvent
        hraw hcontract).symm
  have hmass :
      μ (appendixCGeneralLemma3IncomingCell value t i) ≤
        μ (appendixCGeneralLemma3IncomingZeroCell value t) := by
    simpa [μ, w11CandidateScoreLaw] using
      (appendixCGeneralLemma3_incomingCell_measure_le_incomingZeroCell
        hf hfmeas hnonneg ht0 htlt1 hi hvalue)
  have hIncomingLe :
      measureProb μ (appendixCGeneralLemma3IncomingRankEvent value t i) ≤
        measureProb μ (appendixCGeneralLemma3IncomingZeroRankEvent value t) := by
    apply measureProb_le_of_measure_le μ
      (appendixCGeneralLemma3IncomingRankEvent value t i)
      (appendixCGeneralLemma3IncomingZeroRankEvent value t)
    rw [hIncomingEq, hIncomingZeroEq]
    exact hmass
  change
    measureProb μ (fun score => firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i) -
      measureProb μ (fun score => firstChoice (rankByScore score) = i) ≤
    measureProb μ (fun score => firstChoice
        (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0) -
      measureProb μ (fun score => firstChoice (rankByScore score) = 0)
  linarith

/-- Event probabilities transport through an explicitly measurable pushforward map. -/
theorem appendixCGeneralLemma3_measureProb_comp_eq_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (g : α → β) (hg : Measurable g)
    (p : β → Prop) (hp : MeasurableSet {b | p b}) :
    measureProb μ (fun a => p (g a)) = measureProb (μ.map g) p := by
  unfold measureProb
  rw [Measure.map_apply hg hp]
  rfl

/--
Literal arbitrary-finite source-law form of Appendix C Lemma 3.  The source
specifies two marginal iid laws; the proof couples them with one iid innovation
vector and ranks the raw scores `x_i + eps_i / theta` at both accuracies.  The
canonical carrier represents the printed labels as `x_1, ..., x_{n+2}` at
indices `0, ..., n + 1`, so `StrictAnti value` is exactly the source condition
`x_1 > ... > x_{n+2}`.
-/
theorem appendixCGeneralLemma3_sourceRaw_delta_le_top_delta
    {n : ℕ} {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) (hfmeas : Measurable f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA)
    {i : Candidate n} (hi : i ≠ 0) :
    measureProb (w11CandidateNoiseLaw (n := n) f) (fun noise =>
        firstChoice (rankByScore (appendixCRawScoreMap value thetaA noise)) = i) -
      measureProb (w11CandidateNoiseLaw (n := n) f) (fun noise =>
        firstChoice (rankByScore (appendixCRawScoreMap value thetaH noise)) = i) ≤
    measureProb (w11CandidateNoiseLaw (n := n) f) (fun noise =>
        firstChoice (rankByScore (appendixCRawScoreMap value thetaA noise)) = 0) -
      measureProb (w11CandidateNoiseLaw (n := n) f) (fun noise =>
        firstChoice (rankByScore (appendixCRawScoreMap value thetaH noise)) = 0) := by
  classical
  by_cases hthetaEq : thetaA = thetaH
  · subst thetaA
    simp
  · have hthetaHA' : thetaH < thetaA :=
      lt_of_le_of_ne hthetaHA (Ne.symm hthetaEq)
    have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA'
    let t : ℝ := thetaH / thetaA
    have htpos : 0 < t := by
      dsimp [t]
      exact div_pos hthetaH hthetaA
    have ht0 : 0 ≤ t := htpos.le
    have htlt1 : t < 1 := by
      dsimp [t]
      exact (div_lt_one hthetaA).mpr hthetaHA'
    have hvalueI : value i < value 0 := by
      exact hvalueOrder (Fin.pos_iff_ne_zero.mpr hi)
    have hzeroValue : ∀ d : Candidate n, d ≠ 0 → value d < value 0 := by
      intro d hd
      exact hvalueOrder (Fin.pos_iff_ne_zero.mpr hd)
    have hpos : ∀ z : ℝ, 0 < f z := hf.pos_of_nonneg hnonneg
    have hfintegrable : Integrable f volume :=
      appendixC_integrable_of_normalized_positive_density
        hfmeas hpos hnormalized
    let g : ℝ → ℝ := appendixCScaledNoiseDensity f thetaH
    have hgstrict : StrictlyWellOrderedNoise g := by
      simpa [g] using appendixCScaledNoiseDensity_strictlyWellOrdered hf hthetaH
    have hgmeas : Measurable g := by
      simpa [g] using appendixCScaledNoiseDensity_measurable hfmeas thetaH
    have hgintegrable : Integrable g volume := by
      simpa [g] using appendixCScaledNoiseDensity_integrable hfintegrable hthetaH
    have hgnonneg : ∀ z : ℝ, 0 ≤ g z := by
      intro z
      simpa [g] using (appendixCScaledNoiseDensity_pos hthetaH hpos z).le
    have hgnormalized : ∫⁻ z, ENNReal.ofReal (g z) ∂volume = 1 := by
      simpa [g] using appendixCScaledNoiseDensity_normalized
        f hfintegrable hpos hnormalized hthetaH
    let μnoise : Measure (Candidate n → ℝ) := w11CandidateNoiseLaw (n := n) f
    let μscore : Measure (Candidate n → ℝ) := w11CandidateScoreLaw g value 1
    have hmapH : μnoise.map (appendixCRawScoreMap value thetaH) = μscore := by
      simpa [μnoise, μscore] using
        (w11CandidateNoiseLaw_map_rawScore_eq_candidateScoreLaw
          (n := n) f hfintegrable hfmeas hpos hnormalized hthetaH value)
    have hrawEvent (c : Candidate n) :
        MeasurableSet {score : Candidate n → ℝ |
          firstChoice (rankByScore score) = c} := by
      have hrank : Measurable (fun score : Candidate n → ℝ => rankByScore score) :=
        measurable_rankByScore (fun score : Candidate n → ℝ => score)
          (fun k => measurable_pi_apply k)
      simpa only [Set.preimage_setOf_eq] using
        (hrank (show MeasurableSet {pi : Ranking n | firstChoice pi = c}
          from MeasurableSet.of_discrete))
    have hcontractEvent (c : Candidate n) :
        MeasurableSet {score : Candidate n → ℝ |
          firstChoice
            (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = c} := by
      have hrank : Measurable (fun score : Candidate n → ℝ =>
          rankByScore (appendixCGeneralLemma3ContractedScore t value score)) :=
        measurable_rankByScore (appendixCGeneralLemma3ContractedScore t value)
          (measurable_appendixCGeneralLemma3ContractedScore_coordinate t value)
      simpa only [Set.preimage_setOf_eq] using
        (hrank (show MeasurableSet {pi : Ranking n | firstChoice pi = c}
          from MeasurableSet.of_discrete))
    have hrawTransport (c : Candidate n) :
        measureProb μnoise (fun noise =>
          firstChoice (rankByScore (appendixCRawScoreMap value thetaH noise)) = c) =
        measureProb μscore (fun score => firstChoice (rankByScore score) = c) := by
      calc
        measureProb μnoise (fun noise =>
            firstChoice (rankByScore (appendixCRawScoreMap value thetaH noise)) = c) =
          measureProb (μnoise.map (appendixCRawScoreMap value thetaH))
            (fun score => firstChoice (rankByScore score) = c) :=
          appendixCGeneralLemma3_measureProb_comp_eq_map μnoise
            (appendixCRawScoreMap value thetaH)
            (measurable_appendixCRawScoreMap value thetaH) _ (hrawEvent c)
        _ = measureProb μscore (fun score => firstChoice (rankByScore score) = c) := by
          rw [hmapH]
    have hrawA_eq_contract_rawH (noise : Candidate n → ℝ) :
        appendixCRawScoreMap value thetaA noise =
          appendixCGeneralLemma3ContractedScore t value
            (appendixCRawScoreMap value thetaH noise) := by
      funext c
      dsimp [t]
      exact appendixCRawScoreMap_eq_contract hthetaA hthetaH value noise c
    have hcontractTransport (c : Candidate n) :
        measureProb μnoise (fun noise =>
          firstChoice (rankByScore (appendixCRawScoreMap value thetaA noise)) = c) =
        measureProb μscore (fun score => firstChoice
          (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = c) := by
      calc
        measureProb μnoise (fun noise =>
            firstChoice (rankByScore (appendixCRawScoreMap value thetaA noise)) = c) =
          measureProb μnoise (fun noise => firstChoice
            (rankByScore (appendixCGeneralLemma3ContractedScore t value
              (appendixCRawScoreMap value thetaH noise))) = c) := by
            congr 1
            funext noise
            rw [hrawA_eq_contract_rawH noise]
        _ = measureProb (μnoise.map (appendixCRawScoreMap value thetaH))
            (fun score => firstChoice
              (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = c) :=
          appendixCGeneralLemma3_measureProb_comp_eq_map μnoise
            (appendixCRawScoreMap value thetaH)
            (measurable_appendixCRawScoreMap value thetaH) _ (hcontractEvent c)
        _ = measureProb μscore (fun score => firstChoice
            (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = c) := by
          rw [hmapH]
    have hscoreDelta :
        measureProb μscore (fun score => firstChoice
            (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = i) -
          measureProb μscore (fun score => firstChoice (rankByScore score) = i) ≤
        measureProb μscore (fun score => firstChoice
            (rankByScore (appendixCGeneralLemma3ContractedScore t value score)) = 0) -
          measureProb μscore (fun score => firstChoice (rankByScore score) = 0) := by
      simpa [μscore] using
        (appendixCGeneralLemma3_scoreLaw_delta_le_top_delta
          hgstrict.weak hgmeas hgintegrable hgnonneg hgnormalized
          ht0 htpos htlt1 hi hvalueI hvalueOrder.injective hzeroValue)
    change
      measureProb μnoise (fun noise =>
          firstChoice (rankByScore (appendixCRawScoreMap value thetaA noise)) = i) -
        measureProb μnoise (fun noise =>
          firstChoice (rankByScore (appendixCRawScoreMap value thetaH noise)) = i) ≤
      measureProb μnoise (fun noise =>
          firstChoice (rankByScore (appendixCRawScoreMap value thetaA noise)) = 0) -
        measureProb μnoise (fun noise =>
          firstChoice (rankByScore (appendixCRawScoreMap value thetaH noise)) = 0)
    rw [hcontractTransport i, hrawTransport i, hcontractTransport 0, hrawTransport 0]
    exact hscoreDelta

end

end KR21Monoculture

import KR21Monoculture.GumbelRUMPlackettLuce
import KR21Monoculture.ExponentialRaceOrderReindex
import KR21Monoculture.PlackettLuceFullRankingProduct
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteDensity
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite heterogeneous exponential races

This file develops the measure calculation behind the finite
Gumbel--Plackett--Luce bridge.  It deliberately starts from the literal
product of exponential measures, rather than a sampled ranking law.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace KR21Monoculture

noncomputable section

/-- The product density of independent, not necessarily identically
distributed, exponential coordinates. -/
def heterogeneousExponentialDensity {m : ℕ} (rate : Fin m → ℝ) :
    (Fin m → ℝ) → ℝ≥0∞ :=
  fun x => ∏ i : Fin m, exponentialPDF (rate i) (x i)

theorem measurable_heterogeneousExponentialDensity {m : ℕ} (rate : Fin m → ℝ) :
    Measurable (heterogeneousExponentialDensity rate) := by
  unfold heterogeneousExponentialDensity
  exact Finset.measurable_prod Finset.univ fun i _ =>
    (AppliedModelingLib.Probability.PoissonProcess.measurable_exponentialPDF
      (rate i)).comp (measurable_pi_apply i)

/-- The total rate of the positions at or after `j`. -/
def exponentialRaceSuffixRate {m : ℕ} (rate : Fin m → ℝ) (j : Fin m) : ℝ :=
  (Finset.univ.filter (fun i => j ≤ i)).sum rate

theorem exponentialRaceSuffixRate_pos {m : ℕ} (rate : Fin m → ℝ)
    (hrate : ∀ i, 0 < rate i) (j : Fin m) :
    0 < exponentialRaceSuffixRate rate j := by
  unfold exponentialRaceSuffixRate
  refine Finset.sum_pos' (fun i _ => (hrate i).le) ?_
  exact ⟨j, by simp, hrate j⟩

/-- The sequential product of competing-exponential first-arrival ratios in a
fixed ordering of positions. -/
def exponentialRaceOrderWeight {m : ℕ} (rate : Fin m → ℝ) : ℝ :=
  ∏ j : Fin m, rate j / exponentialRaceSuffixRate rate j

/-- Strictly increasing arrival vectors in their displayed coordinate order. -/
def strictIncreasingExponentialCell (m : ℕ) : Set (Fin m → ℝ) :=
  {time | ∀ p q : Fin m, p < q → time p < time q}

theorem measurableSet_strictIncreasingExponentialCell (m : ℕ) :
    MeasurableSet (strictIncreasingExponentialCell m) := by
  rw [show strictIncreasingExponentialCell m =
      ⋂ p : Fin m, ⋂ q : Fin m,
        if p < q then
          {time : Fin m → ℝ | time p < time q}
        else Set.univ by
      ext time
      simp [strictIncreasingExponentialCell]]
  apply MeasurableSet.iInter
  intro p
  apply MeasurableSet.iInter
  intro q
  by_cases hpq : p < q
  · simpa [hpq] using
      (measurableSet_lt (measurable_pi_apply p) (measurable_pi_apply q))
  · simp [hpq]

/-- A finite product of positive-rate exponential laws has its literal
heterogeneous product density with respect to finite-dimensional volume. -/
theorem pi_expMeasure_eq_withDensity_heterogeneous
    {m : ℕ} (rate : Fin m → ℝ) (hrate : ∀ i, 0 < rate i) :
    Measure.pi (fun i : Fin m => expMeasure (rate i)) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (heterogeneousExponentialDensity rate) := by
  letI : ∀ i : Fin m, IsProbabilityMeasure (expMeasure (rate i)) := fun i =>
    isProbabilityMeasure_expMeasure (hrate i)
  induction m with
  | zero =>
      let e := MeasurableEquiv.ofUniqueOfUnique (Fin 0 → ℝ) Unit
      have hdens : heterogeneousExponentialDensity rate = 1 := by
        funext x
        simp [heterogeneousExponentialDensity]
      apply e.map_measurableEquiv_injective
      rw [hdens, withDensity_one, volume_pi]
      exact
        ((MeasureTheory.measurePreserving_pi_empty
          (fun i : Fin 0 => expMeasure (rate i))).map_eq).trans
          ((MeasureTheory.measurePreserving_pi_empty
            (fun _ : Fin 0 => (volume : Measure ℝ))).map_eq).symm
  | succ q ih =>
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (q + 1) => ℝ) (Fin.last q)
      let headRate : ℝ := rate (Fin.last q)
      let tailRate : Fin q → ℝ := fun i => rate i.castSucc
      let g : ℝ × (Fin q → ℝ) → ℝ≥0∞ := fun p =>
        exponentialPDF headRate p.1 * heterogeneousExponentialDensity tailRate p.2
      have hheadRate : 0 < headRate := by
        exact hrate _
      have htailRate : ∀ i, 0 < tailRate i := by
        intro i
        exact hrate _
      have hg : Measurable g := by
        exact ((AppliedModelingLib.Probability.PoissonProcess.measurable_exponentialPDF
          headRate).comp measurable_fst).mul
          ((measurable_heterogeneousExponentialDensity tailRate).comp measurable_snd)
      have hdens : heterogeneousExponentialDensity rate = g ∘ e := by
        funext x
        dsimp [heterogeneousExponentialDensity, g, Function.comp_apply, e,
          headRate, tailRate]
        rw [Fin.prod_univ_succAbove
          (fun i : Fin (q + 1) => exponentialPDF (rate i) (x i)) (Fin.last q)]
        apply congrArg (fun z => exponentialPDF (rate (Fin.last q))
          (x (Fin.last q)) * z)
        apply Finset.prod_congr rfl
        intro i _hi
        simp [Fin.succAbove_last_apply, Fin.removeNth_last, Fin.init]
      apply e.map_measurableEquiv_injective
      calc
        Measure.map e (Measure.pi (fun i : Fin (q + 1) => expMeasure (rate i))) =
            (expMeasure headRate).prod
              (Measure.pi (fun i : Fin q => expMeasure (tailRate i))) := by
          simpa [e, headRate, tailRate, Fin.succAbove_last] using
            (MeasureTheory.measurePreserving_piFinSuccAbove
              (fun i : Fin (q + 1) => expMeasure (rate i)) (Fin.last q)).map_eq
        _ = (volume.prod volume).withDensity g := by
          rw [ih tailRate htailRate]
          change (volume.withDensity (exponentialPDF headRate)).prod
              (volume.withDensity (heterogeneousExponentialDensity tailRate)) =
            (volume.prod volume).withDensity
              (fun p => exponentialPDF headRate p.1 *
                heterogeneousExponentialDensity tailRate p.2)
          rw [MeasureTheory.prod_withDensity
            (AppliedModelingLib.Probability.PoissonProcess.measurable_exponentialPDF headRate)
            (measurable_heterogeneousExponentialDensity tailRate)]
        _ = Measure.map e ((volume : Measure (Fin (q + 1) → ℝ)).withDensity
            (heterogeneousExponentialDensity rate)) := by
          rw [hdens]
          symm
          exact AppliedModelingLib.Probability.PoissonProcess.map_withDensity_comp_of_measurePreserving
            (MeasureTheory.volume_preserving_piFinSuccAbove
              (fun _ : Fin (q + 1) => ℝ) (Fin.last q)) g hg

/-- Reversing the finite double sum in the ordered-gap change of variables.
The coefficient of a gap at position `j` is the sum of all rates at positions
at or after `j`. -/
theorem sum_rate_mul_cumulativeArrivalLinearMap_eq_sum_suffixRate_mul
    {m : ℕ} (rate gap : Fin m → ℝ) :
    (∑ i : Fin m, rate i *
      AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i) =
      ∑ j : Fin m, exponentialRaceSuffixRate rate j * gap j := by
  rw [AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap_apply]
  unfold AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalVector
    exponentialRaceSuffixRate
  calc
    (∑ i : Fin m, rate i * ∑ j : {j : Fin m // j ≤ i}, gap j) =
        ∑ i : Fin m, ∑ j : {j : Fin m // j ≤ i}, rate i * gap j := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i),
          rate i * gap j := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [← Finset.sum_subtype_eq_sum_filter]
          simp
    _ = ∑ j : Fin m, ∑ i ∈ Finset.univ.filter (fun i : Fin m => j ≤ i),
          rate i * gap j := by
          classical
          calc
            (∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i),
                rate i * gap j) =
                ∑ i : Fin m, ∑ j : Fin m,
                  if j ≤ i then rate i * gap j else 0 := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    rw [Finset.sum_filter]
            _ = ∑ j : Fin m, ∑ i : Fin m,
                  if j ≤ i then rate i * gap j else 0 := by
                    exact Finset.sum_comm
            _ = ∑ j : Fin m, ∑ i ∈ Finset.univ.filter (fun i : Fin m => j ≤ i),
                  rate i * gap j := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    rw [Finset.sum_filter]
    _ = ∑ j : Fin m,
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => j ≤ i), rate i) * gap j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_mul]

/-- A cumulative coordinate is the sum of the gaps in its finite initial
segment. -/
theorem cumulativeArrivalLinearMap_apply_eq_sum_filter {m : ℕ}
    (gap : Fin m → ℝ) (i : Fin m) :
    AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), gap j := by
  rw [AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap_apply]
  unfold AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalVector
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp

/-- Consecutive cumulative coordinates differ by their new gap. -/
theorem cumulativeArrivalLinearMap_succ_eq_add
    {n : ℕ} (gap : Fin (n + 2) → ℝ) (i : Fin (n + 1)) :
    AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap i.succ =
      AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap i.castSucc +
        gap i.succ := by
  rw [cumulativeArrivalLinearMap_apply_eq_sum_filter,
    cumulativeArrivalLinearMap_apply_eq_sum_filter]
  have hfilter :
      Finset.univ.filter (fun j : Fin (n + 2) => j ≤ i.succ) =
        insert i.succ (Finset.univ.filter (fun j : Fin (n + 2) => j ≤ i.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i.succ
      · exact Or.inl hji
      · right
        rcases Fin.succ_le_or_le_castSucc j i with hle | hle
        · exact False.elim (hji (le_antisymm hj hle))
        · exact hle
    · rintro (rfl | hj)
      · exact le_rfl
      · exact hj.trans (Fin.castSucc_le_succ i)
  rw [hfilter, Finset.sum_insert]
  · ac_rfl
  · simp

/-- The first cumulative coordinate is the first gap. -/
theorem cumulativeArrivalLinearMap_zero_eq
    {n : ℕ} (gap : Fin (n + 2) → ℝ) :
    AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap 0 =
      gap 0 := by
  rw [cumulativeArrivalLinearMap_apply_eq_sum_filter]
  have hfilter :
      Finset.univ.filter (fun j : Fin (n + 2) => j ≤ (0 : Fin (n + 2))) = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact Fin.le_zero_iff
  rw [hfilter, Finset.sum_singleton]

/-- A strictly increasing cumulative-arrival vector has positive noninitial
gaps. -/
theorem gap_succ_pos_of_strictIncreasingExponentialCell
    {n : ℕ} (gap : Fin (n + 2) → ℝ)
    (hstrict : AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap
      (n + 2) gap ∈ strictIncreasingExponentialCell (n + 2))
    (i : Fin (n + 1)) :
    0 < gap i.succ := by
  have hlt := hstrict i.castSucc i.succ (show i.castSucc < i.succ from
    Fin.castSucc_lt_succ)
  rw [cumulativeArrivalLinearMap_succ_eq_add] at hlt
  linarith

/-- An exponential product density vanishes when one coordinate is negative. -/
theorem heterogeneousExponentialDensity_eq_zero_of_exists_neg
    {m : ℕ} (rate x : Fin m → ℝ) (hneg : ∃ i, x i < 0) :
    heterogeneousExponentialDensity rate x = 0 := by
  rcases hneg with ⟨i, hi⟩
  unfold heterogeneousExponentialDensity
  exact Finset.prod_eq_zero (Finset.mem_univ i) (exponentialPDF_of_neg hi)

/-- If a cumulative vector is strictly increasing, a negative gap can only be
the first one, where it forces the arrival-time density to vanish. -/
theorem heterogeneousExponentialDensity_cumulativeArrivalLinearMap_eq_zero_of_strict_and_exists_neg
    {n : ℕ} (rate gap : Fin (n + 2) → ℝ)
    (hstrict : AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap
      (n + 2) gap ∈ strictIncreasingExponentialCell (n + 2))
    (hneg : ∃ i, gap i < 0) :
    heterogeneousExponentialDensity rate
        (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap) = 0 := by
  rcases hneg with ⟨i, hi⟩
  revert hi
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    apply heterogeneousExponentialDensity_eq_zero_of_exists_neg
    refine ⟨0, ?_⟩
    rw [cumulativeArrivalLinearMap_zero_eq]
    exact hi
  · intro hi
    exact False.elim ((not_lt_of_ge
      (gap_succ_pos_of_strictIncreasingExponentialCell gap hstrict j).le) hi)

/-- Positive gaps give strictly increasing cumulative arrival times. -/
theorem strictIncreasingExponentialCell_cumulativeArrivalLinearMap_of_pos
    {m : ℕ} (gap : Fin m → ℝ) (hgap : ∀ i, 0 < gap i) :
    AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap ∈
      strictIncreasingExponentialCell m := by
  intro p q hpq
  rw [cumulativeArrivalLinearMap_apply_eq_sum_filter,
    cumulativeArrivalLinearMap_apply_eq_sum_filter]
  refine Finset.sum_lt_sum_of_subset (f := gap) (i := q) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans hpq.le
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, le_rfl⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le_of_gt hpq
  · exact hgap q
  · intro j _hj _hnot
    exact (hgap j).le

/-- Positive gaps also make every cumulative arrival coordinate positive. -/
theorem cumulativeArrivalLinearMap_pos_of_pos {m : ℕ}
    (gap : Fin m → ℝ) (hgap : ∀ i, 0 < gap i) (i : Fin m) :
    0 < AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i := by
  rw [cumulativeArrivalLinearMap_apply_eq_sum_filter]
  refine Finset.sum_pos' (fun j _ => (hgap j).le) ?_
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_rfl⟩, hgap i⟩

/-- The exponential factor in the ordered-gap change of variables collects
the rates at or after each gap position. -/
theorem prod_exp_neg_rate_cumulativeArrivalLinearMap_eq_prod_exp_neg_suffixRate
    {m : ℕ} (rate gap : Fin m → ℝ) :
    (∏ i : Fin m,
      Real.exp (-(rate i *
        AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i))) =
      ∏ j : Fin m,
        Real.exp (-(exponentialRaceSuffixRate rate j * gap j)) := by
  calc
    (∏ i : Fin m,
        Real.exp (-(rate i *
          AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i))) =
        Real.exp (∑ i : Fin m,
          -(rate i *
            AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i)) := by
          rw [Real.exp_sum]
    _ = Real.exp (-∑ i : Fin m,
          rate i *
            AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i) := by
          congr 1
          rw [Finset.sum_neg_distrib]
    _ = Real.exp (-∑ j : Fin m, exponentialRaceSuffixRate rate j * gap j) := by
          rw [sum_rate_mul_cumulativeArrivalLinearMap_eq_sum_suffixRate_mul]
    _ = Real.exp (∑ j : Fin m,
          -(exponentialRaceSuffixRate rate j * gap j)) := by
          congr 1
          rw [Finset.sum_neg_distrib]
    _ = ∏ j : Fin m,
        Real.exp (-(exponentialRaceSuffixRate rate j * gap j)) := by
          rw [Real.exp_sum]

/-- The real scalar multiplying the gap-product density is exactly the
sequential product of rate ratios. -/
theorem prod_rate_eq_exponentialRaceOrderWeight_mul_prod_suffixRate
    {m : ℕ} (rate : Fin m → ℝ) (hrate : ∀ i, 0 < rate i) :
    (∏ i : Fin m, rate i) =
      exponentialRaceOrderWeight rate *
        ∏ i : Fin m, exponentialRaceSuffixRate rate i := by
  unfold exponentialRaceOrderWeight
  rw [Finset.prod_div_distrib]
  have hsuffix_ne : (∏ i : Fin m, exponentialRaceSuffixRate rate i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i _hi
    exact ne_of_gt (exponentialRaceSuffixRate_pos rate hrate i)
  field_simp

/-- On positive gaps, the real-valued factors in the arrival-time density
factor into the ordered-race coefficient and the suffix-rate gap density. -/
theorem prod_rate_exp_neg_cumulativeArrivalLinearMap_eq_orderWeight_mul_prod_suffix
    {m : ℕ} (rate gap : Fin m → ℝ) (hrate : ∀ i, 0 < rate i) :
    (∏ i : Fin m, rate i *
      Real.exp (-(rate i *
        AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i))) =
      exponentialRaceOrderWeight rate *
        ∏ j : Fin m, exponentialRaceSuffixRate rate j *
          Real.exp (-(exponentialRaceSuffixRate rate j * gap j)) := by
  rw [Finset.prod_mul_distrib,
    prod_rate_eq_exponentialRaceOrderWeight_mul_prod_suffixRate rate hrate,
    prod_exp_neg_rate_cumulativeArrivalLinearMap_eq_prod_exp_neg_suffixRate]
  calc
    (exponentialRaceOrderWeight rate * ∏ i : Fin m,
        exponentialRaceSuffixRate rate i) *
        ∏ j : Fin m, Real.exp (-(exponentialRaceSuffixRate rate j * gap j)) =
        exponentialRaceOrderWeight rate *
          ((∏ i : Fin m, exponentialRaceSuffixRate rate i) *
            ∏ j : Fin m, Real.exp (-(exponentialRaceSuffixRate rate j * gap j))) := by
              ac_rfl
    _ = _ := by
      rw [← Finset.prod_mul_distrib]

/-- On positive gap coordinates, the heterogeneous exponential arrival-time
density is the ordered-race coefficient times the suffix-rate gap density. -/
theorem heterogeneousExponentialDensity_cumulativeArrivalLinearMap_eq_orderWeight
    {m : ℕ} (rate gap : Fin m → ℝ) (hrate : ∀ i, 0 < rate i)
    (hgap : ∀ i, 0 < gap i) :
    heterogeneousExponentialDensity rate
        (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap) =
      ENNReal.ofReal (exponentialRaceOrderWeight rate) *
        heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap := by
  unfold heterogeneousExponentialDensity
  have harrival_nonneg : ∀ i : Fin m, 0 ≤
      AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i := by
    intro i
    exact (cumulativeArrivalLinearMap_pos_of_pos gap hgap i).le
  have harrival_pdf : ∀ i : Fin m,
      exponentialPDF (rate i)
        (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i) =
        ENNReal.ofReal (rate i * Real.exp (-(rate i *
          AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i))) := by
    intro i
    exact exponentialPDF_of_nonneg (harrival_nonneg i)
  have hgap_pdf : ∀ i : Fin m,
      exponentialPDF (exponentialRaceSuffixRate rate i) (gap i) =
        ENNReal.ofReal (exponentialRaceSuffixRate rate i *
          Real.exp (-(exponentialRaceSuffixRate rate i * gap i))) := by
    intro i
    exact exponentialPDF_of_nonneg (hgap i).le
  have horder_nonneg : 0 ≤ exponentialRaceOrderWeight rate := by
    unfold exponentialRaceOrderWeight
    apply Finset.prod_nonneg
    intro i _hi
    exact div_nonneg (hrate i).le (exponentialRaceSuffixRate_pos rate hrate i).le
  simp_rw [harrival_pdf, hgap_pdf]
  calc
    (∏ i : Fin m, ENNReal.ofReal (rate i * Real.exp (-(rate i *
        AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i)))) =
        ENNReal.ofReal (∏ i : Fin m, rate i * Real.exp (-(rate i *
          AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap m gap i))) := by
            symm
            apply ENNReal.ofReal_prod_of_nonneg
            intro i _hi
            exact mul_nonneg (hrate i).le (le_of_lt (Real.exp_pos _))
    _ = ENNReal.ofReal (exponentialRaceOrderWeight rate *
          ∏ j : Fin m, exponentialRaceSuffixRate rate j *
            Real.exp (-(exponentialRaceSuffixRate rate j * gap j))) := by
          rw [prod_rate_exp_neg_cumulativeArrivalLinearMap_eq_orderWeight_mul_prod_suffix
            rate gap hrate]
    _ = ENNReal.ofReal (exponentialRaceOrderWeight rate) *
          ENNReal.ofReal (∏ j : Fin m, exponentialRaceSuffixRate rate j *
            Real.exp (-(exponentialRaceSuffixRate rate j * gap j))) := by
          rw [ENNReal.ofReal_mul]
          exact horder_nonneg
    _ = ENNReal.ofReal (exponentialRaceOrderWeight rate) *
          ∏ j : Fin m, ENNReal.ofReal (exponentialRaceSuffixRate rate j *
            Real.exp (-(exponentialRaceSuffixRate rate j * gap j))) := by
          rw [ENNReal.ofReal_prod_of_nonneg]
          intro i _hi
          exact mul_nonneg (exponentialRaceSuffixRate_pos rate hrate i).le
            (le_of_lt (Real.exp_pos _))

/-- Away from coordinate-zero boundaries, the strict-order indicator pulls
back under cumulative coordinates to the suffix-rate exponential density. -/
theorem strictIncreasing_indicator_heterogeneousExponentialDensity_cumulativeArrivalLinearMap
    {n : ℕ} (rate gap : Fin (n + 2) → ℝ) (hrate : ∀ i, 0 < rate i)
    (hgap_ne_zero : ∀ i, gap i ≠ 0) :
    (strictIncreasingExponentialCell (n + 2)).indicator
        (heterogeneousExponentialDensity rate)
        (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap) =
      ENNReal.ofReal (exponentialRaceOrderWeight rate) *
        heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap := by
  by_cases hgap_pos : ∀ i, 0 < gap i
  · rw [Set.indicator_of_mem
      (strictIncreasingExponentialCell_cumulativeArrivalLinearMap_of_pos gap hgap_pos)]
    exact heterogeneousExponentialDensity_cumulativeArrivalLinearMap_eq_orderWeight
      rate gap hrate hgap_pos
  · push Not at hgap_pos
    rcases hgap_pos with ⟨i, hi⟩
    have hneg : gap i < 0 := lt_of_le_of_ne hi (hgap_ne_zero i)
    have hneg_exists : ∃ j, gap j < 0 := ⟨i, hneg⟩
    rw [heterogeneousExponentialDensity_eq_zero_of_exists_neg
      (exponentialRaceSuffixRate rate) gap hneg_exists, mul_zero]
    by_cases hstrict :
        AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap ∈
          strictIncreasingExponentialCell (n + 2)
    · rw [Set.indicator_of_mem hstrict,
        heterogeneousExponentialDensity_cumulativeArrivalLinearMap_eq_zero_of_strict_and_exists_neg
          rate gap hstrict hneg_exists]
    · rw [Set.indicator_of_notMem hstrict]

/-- Lebesgue-almost every finite gap vector avoids every coordinate-zero
boundary. -/
theorem ae_all_gap_coordinates_ne_zero (n : ℕ) :
    ∀ᵐ gap : Fin (n + 2) → ℝ ∂(volume : Measure (Fin (n + 2) → ℝ)),
      ∀ i, gap i ≠ 0 := by
  rw [volume_pi, Filter.eventually_all]
  intro i
  exact Measure.ae_eval_ne (fun _ : Fin (n + 2) => (volume : Measure ℝ)) i 0

/-- The ordered-cell density identity holds Lebesgue-a.e.; the only discarded
set is the union of coordinate-zero hyperplanes. -/
theorem strictIncreasing_indicator_density_cumulativeArrivalLinearMap_ae
    (n : ℕ) (rate : Fin (n + 2) → ℝ) (hrate : ∀ i, 0 < rate i) :
    (fun gap : Fin (n + 2) → ℝ =>
      (strictIncreasingExponentialCell (n + 2)).indicator
        (heterogeneousExponentialDensity rate)
        (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap)) =ᵐ[
          volume]
      fun gap => ENNReal.ofReal (exponentialRaceOrderWeight rate) *
        heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap := by
  filter_upwards [ae_all_gap_coordinates_ne_zero n] with gap hgap_ne_zero
  exact strictIncreasing_indicator_heterogeneousExponentialDensity_cumulativeArrivalLinearMap
    rate gap hrate hgap_ne_zero

/-- The probability that independent positive-rate exponentials arrive in a
fixed strict coordinate order is the sequential product of suffix-rate
ratios. This is proved by a finite-dimensional density change of variables. -/
theorem pi_expMeasure_strictIncreasingExponentialCell_eq_orderWeight
    (n : ℕ) (rate : Fin (n + 2) → ℝ) (hrate : ∀ i, 0 < rate i) :
    Measure.pi (fun i : Fin (n + 2) => expMeasure (rate i))
        (strictIncreasingExponentialCell (n + 2)) =
      ENNReal.ofReal (exponentialRaceOrderWeight rate) := by
  have hsuffix_pos : ∀ i : Fin (n + 2),
      0 < exponentialRaceSuffixRate rate i := by
    intro i
    exact exponentialRaceSuffixRate_pos rate hrate i
  letI : ∀ i : Fin (n + 2),
      IsProbabilityMeasure (expMeasure (exponentialRaceSuffixRate rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hsuffix_pos i)
  have hcell : MeasurableSet (strictIncreasingExponentialCell (n + 2)) :=
    measurableSet_strictIncreasingExponentialCell (n + 2)
  have hindicator_meas : Measurable
      ((strictIncreasingExponentialCell (n + 2)).indicator
        (heterogeneousExponentialDensity rate)) :=
    (measurable_heterogeneousExponentialDensity rate).indicator hcell
  have hsuffix_integral :
      ∫⁻ gap : Fin (n + 2) → ℝ,
        heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap ∂volume = 1 := by
    calc
      (∫⁻ gap : Fin (n + 2) → ℝ,
          heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap ∂volume) =
          ((volume : Measure (Fin (n + 2) → ℝ)).withDensity
            (heterogeneousExponentialDensity (exponentialRaceSuffixRate rate))) Set.univ := by
              rw [← MeasureTheory.setLIntegral_univ]
              exact (MeasureTheory.withDensity_apply _ MeasurableSet.univ).symm
      _ = Measure.pi (fun i : Fin (n + 2) =>
          expMeasure (exponentialRaceSuffixRate rate i)) Set.univ := by
            rw [pi_expMeasure_eq_withDensity_heterogeneous
              (exponentialRaceSuffixRate rate) hsuffix_pos]
      _ = 1 := by
        exact measure_univ
  calc
    Measure.pi (fun i : Fin (n + 2) => expMeasure (rate i))
        (strictIncreasingExponentialCell (n + 2)) =
        ((volume : Measure (Fin (n + 2) → ℝ)).withDensity
          (heterogeneousExponentialDensity rate))
          (strictIncreasingExponentialCell (n + 2)) := by
            rw [pi_expMeasure_eq_withDensity_heterogeneous rate hrate]
    _ = ∫⁻ time in strictIncreasingExponentialCell (n + 2),
        heterogeneousExponentialDensity rate time ∂volume := by
          exact MeasureTheory.withDensity_apply _ hcell
    _ = ∫⁻ time : Fin (n + 2) → ℝ,
        (strictIncreasingExponentialCell (n + 2)).indicator
          (heterogeneousExponentialDensity rate) time ∂volume := by
          exact (MeasureTheory.lintegral_indicator hcell _).symm
    _ = ∫⁻ gap : Fin (n + 2) → ℝ,
        (strictIncreasingExponentialCell (n + 2)).indicator
          (heterogeneousExponentialDensity rate)
          (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap (n + 2) gap) ∂volume := by
          exact (AppliedModelingLib.Probability.PoissonProcess.cumulativeArrivalLinearMap_volume_preserving
            (n + 2)).lintegral_comp hindicator_meas |>.symm
    _ = ∫⁻ gap : Fin (n + 2) → ℝ,
        ENNReal.ofReal (exponentialRaceOrderWeight rate) *
          heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap ∂volume := by
          exact MeasureTheory.lintegral_congr_ae
            (strictIncreasing_indicator_density_cumulativeArrivalLinearMap_ae n rate hrate)
    _ = ENNReal.ofReal (exponentialRaceOrderWeight rate) *
        ∫⁻ gap : Fin (n + 2) → ℝ,
          heterogeneousExponentialDensity (exponentialRaceSuffixRate rate) gap ∂volume := by
            exact MeasureTheory.lintegral_const_mul _
              (measurable_heterogeneousExponentialDensity (exponentialRaceSuffixRate rate))
    _ = ENNReal.ofReal (exponentialRaceOrderWeight rate) := by
      rw [hsuffix_integral, mul_one]

/-- The analytic suffix-rate product is definitionally the standard ordered
Plackett--Luce full-ranking atom after candidates are reindexed by that
ranking. -/
theorem exponentialRaceOrderWeight_reindexed_eq_fullRankingOrderedAtomWeight
    {n : ℕ} (baseWeight : Candidate n → ℝ) (ranking : Ranking n) :
    exponentialRaceOrderWeight (fun position : Candidate n => baseWeight (ranking position)) =
      fullRankingOrderedAtomWeight baseWeight ranking := by
  rfl

/-- The literal heterogeneous exponential race has exactly the independently
defined finite Plackett--Luce ranking atom. -/
theorem strictExponentialRaceOrderCell_measure_eq_plackettLuceRankingPMF
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    (Measure.pi fun i : Candidate n =>
      expMeasure (plackettLuceWeight theta value i))
      (strictExponentialRaceOrderCell ranking) =
        plackettLuceRankingPMF theta value ranking := by
  let rate : Candidate n → ℝ := plackettLuceWeight theta value
  have hrate : ∀ i : Candidate n, 0 < rate i := by
    intro i
    exact plackettLuceWeight_pos theta value i
  calc
    (Measure.pi fun i : Candidate n => expMeasure (plackettLuceWeight theta value i))
        (strictExponentialRaceOrderCell ranking) =
        (Measure.pi fun position : Candidate n => expMeasure (rate (ranking position)))
          (strictIncreasingRaceCoordinateCell n) := by
            simpa [rate] using
              (strictExponentialRaceOrderCell_measure_eq_reindexedIncreasing
                rate hrate ranking)
    _ = (Measure.pi fun position : Fin (n + 2) => expMeasure (rate (ranking position)))
          (strictIncreasingExponentialCell (n + 2)) := by
            rfl
    _ = ENNReal.ofReal (exponentialRaceOrderWeight
          (fun position : Fin (n + 2) => rate (ranking position))) := by
            exact pi_expMeasure_strictIncreasingExponentialCell_eq_orderWeight n
              (fun position : Fin (n + 2) => rate (ranking position))
              (fun position => hrate (ranking position))
    _ = ENNReal.ofReal (fullRankingOrderedAtomWeight rate ranking) := by
          rw [exponentialRaceOrderWeight_reindexed_eq_fullRankingOrderedAtomWeight]
    _ = ENNReal.ofReal
        ((plackettLuceRankingPMF theta value ranking).toReal) := by
          rw [plackettLuceRankingPMF_apply_toReal_eq_orderedProduct]
    _ = plackettLuceRankingPMF theta value ranking := by
          exact ENNReal.ofReal_toReal
            ((plackettLuceRankingPMF theta value).apply_ne_top ranking)


end

end KR21Monoculture

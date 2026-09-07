import AppliedModelingLib.Foundations.Probability.PoissonSuspensionExponentialSplit
import Mathlib.Tactic

/-!
# Reflected difference of independent exponential variables

This module isolates the measure calculation behind the stable M/M/1
one-arrival response recursion.  If independent exponential variables have
rates `theta` and `lambda`, then the positive part of their difference has an
atom at zero and an exponential positive branch.  The proof is an explicit
change of variables on the product density; it is not an invocation of a
queueing or stationary-process theorem.

The initial result below keeps the second coordinate after the change of
variables.  That joint form is useful because it records the exact branch
mass and will later compose with an independent service-time exponential.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

/-- The open branch on which the first exponential exceeds the second. -/
def exponentialDifferencePositiveCarrier : Set (ℝ × ℝ) :=
  {p | p.2 < p.1}

/-- Subtract the second coordinate while retaining it. -/
def exponentialDifferenceUnshear : (ℝ × ℝ) → ℝ × ℝ :=
  fun p => (p.1 - p.2, p.2)

theorem measurable_exponentialDifferenceUnshear :
    Measurable exponentialDifferenceUnshear := by
  exact measurable_fst.sub measurable_snd |>.prodMk measurable_snd

theorem measurableSet_exponentialDifferencePositiveCarrier :
    MeasurableSet exponentialDifferencePositiveCarrier := by
  exact measurableSet_lt measurable_snd measurable_fst

/-- The subtracting shear preserves two-dimensional Lebesgue measure. -/
theorem exponentialDifferenceUnshear_measurePreserving :
    MeasurePreserving exponentialDifferenceUnshear
      (volume.prod volume) (volume.prod volume) := by
  simpa [exponentialDifferenceUnshear] using
    (measurePreserving_sub_prod (volume : Measure Real) (volume : Measure Real))

/-- Density of an independent pair of exponentials with potentially different
rates. -/
def exponentialPairDensity (leftRate rightRate : ℝ) : (ℝ × ℝ) → ℝ≥0∞ :=
  fun p => exponentialPDF leftRate p.1 * exponentialPDF rightRate p.2

theorem measurable_exponentialPairDensity (leftRate rightRate : Real) :
    Measurable (exponentialPairDensity leftRate rightRate) := by
  exact ((measurable_exponentialPDFReal leftRate).ennreal_ofReal.comp measurable_fst).mul
    ((measurable_exponentialPDFReal rightRate).ennreal_ofReal.comp measurable_snd)

/-- Restricting an exponential pair to the strict positive-difference branch,
written as a density on the ambient plane. -/
def exponentialDifferencePositiveInputDensity
    (leftRate rightRate : ℝ) : (ℝ × ℝ) → ℝ≥0∞ :=
  exponentialDifferencePositiveCarrier.indicator
    (exponentialPairDensity leftRate rightRate)

/-- The factorized output density after subtracting the second coordinate on
the positive-difference branch. -/
def exponentialDifferencePositiveOutputDensity
    (leftRate rightRate : ℝ) : (ℝ × ℝ) → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (rightRate / (leftRate + rightRate)) *
    exponentialPairDensity leftRate (leftRate + rightRate) p

theorem measurable_exponentialDifferencePositiveOutputDensity
    (leftRate rightRate : Real) :
    Measurable (exponentialDifferencePositiveOutputDensity leftRate rightRate) := by
  exact measurable_const.mul (measurable_exponentialPairDensity _ _)

/-- Independent exponential coordinates have their product density relative to
two-dimensional Lebesgue measure. -/
theorem expMeasure_prod_eq_withDensity_exponentialPair
    (leftRate rightRate : Real) :
    (expMeasure leftRate).prod (expMeasure rightRate) =
      (volume.prod volume).withDensity
        (exponentialPairDensity leftRate rightRate) := by
  change (volume.withDensity (exponentialPDF leftRate)).prod
      (volume.withDensity (exponentialPDF rightRate)) = _
  simpa [exponentialPairDensity] using
    (MeasureTheory.prod_withDensity
      (μ := volume) (ν := volume)
      ((measurable_exponentialPDFReal leftRate).ennreal_ofReal)
      ((measurable_exponentialPDFReal rightRate).ennreal_ofReal))

/-- The strict diagonal is Lebesgue-null in the two-dimensional ambient
space.  This is the only boundary where the open positive branch and the
closed reflected map differ. -/
theorem ae_fst_sub_snd_ne_zero_volume_prod :
    ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, p.1 - p.2 ≠ 0 := by
  let f : ℝ × ℝ → ℝ × ℝ := exponentialDifferenceUnshear
  have hbase : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume, q.1 ≠ 0 := by
    refine MeasureTheory.ae_of_ae_map (μ := volume.prod volume) (f := Prod.fst)
      (p := fun x : ℝ => x ≠ 0) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬ x ≠ 0} = {0} := by
      ext x
      simp
    rw [hset, Measure.smul_apply, Real.volume_singleton]
    simp
  have hmap : ∀ᵐ q : ℝ × ℝ ∂Measure.map f (volume.prod volume),
      q.1 ≠ 0 := by
    rw [exponentialDifferenceUnshear_measurePreserving.map_eq]
    exact hbase
  have hpull := Measure.tendsto_ae_map
    measurable_exponentialDifferenceUnshear.aemeasurable hmap
  simpa [f, exponentialDifferenceUnshear] using hpull

/-- Two independent exponential coordinates do not tie almost surely.  This
is the direct continuous-law transport of the ambient diagonal-null fact and
does not require their rates to agree. -/
theorem ae_fst_ne_snd_expMeasure_prod (leftRate rightRate : Real) :
    ∀ᵐ p : ℝ × ℝ ∂(expMeasure leftRate).prod (expMeasure rightRate),
      p.1 ≠ p.2 := by
  rw [expMeasure_prod_eq_withDensity_exponentialPair]
  apply (MeasureTheory.withDensity_absolutelyContinuous (volume.prod volume)
    (exponentialPairDensity leftRate rightRate)).ae_le
  simpa [sub_ne_zero] using ae_fst_sub_snd_ne_zero_volume_prod

private theorem exponentialDifferencePositive_density_eq_output_comp_unshear
    {leftRate rightRate : Real}
    (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (p : ℝ × ℝ) (hp : p.1 - p.2 ≠ 0) :
    exponentialDifferencePositiveInputDensity leftRate rightRate p =
      exponentialDifferencePositiveOutputDensity leftRate rightRate
        (exponentialDifferenceUnshear p) := by
  rcases p with ⟨r, a⟩
  change r - a ≠ 0 at hp
  simp only [exponentialDifferencePositiveInputDensity,
    exponentialDifferencePositiveOutputDensity, exponentialPairDensity,
    exponentialDifferenceUnshear]
  by_cases hpositive : a < r
  · have hmem : (r, a) ∈ exponentialDifferencePositiveCarrier := hpositive
    rw [Set.indicator_of_mem hmem]
    change exponentialPDF leftRate r * exponentialPDF rightRate a = _
    by_cases ha : 0 <= a
    · have hr : 0 <= r := le_trans ha hpositive.le
      have hdifference : 0 <= r - a := sub_nonneg.mpr hpositive.le
      rw [exponentialPDF_of_nonneg hr, exponentialPDF_of_nonneg ha,
        exponentialPDF_of_nonneg hdifference,
        exponentialPDF_of_nonneg ha]
      have hsum_pos : 0 < leftRate + rightRate := add_pos hleft hright
      have hratio_nonneg : 0 <= rightRate / (leftRate + rightRate) :=
        div_nonneg hright.le hsum_pos.le
      have hleft_exp_nonneg :
          0 <= leftRate * Real.exp (-(leftRate * (r - a))) := by positivity
      have hsum_exp_nonneg :
          0 <= (leftRate + rightRate) * Real.exp
            (-((leftRate + rightRate) * a)) := by positivity
      have hsource_left_nonneg :
          0 <= leftRate * Real.exp (-(leftRate * r)) := by positivity
      have harg :
          -(leftRate * r) + -(rightRate * a) =
            -(leftRate * (r - a)) + -((leftRate + rightRate) * a) := by
        ring
      calc
        ENNReal.ofReal (leftRate * Real.exp (-(leftRate * r))) *
            ENNReal.ofReal (rightRate * Real.exp (-(rightRate * a))) =
            ENNReal.ofReal
              ((leftRate * Real.exp (-(leftRate * r))) *
                (rightRate * Real.exp (-(rightRate * a)))) :=
          (ENNReal.ofReal_mul hsource_left_nonneg).symm
        _ = ENNReal.ofReal
              ((rightRate / (leftRate + rightRate)) *
                ((leftRate * Real.exp (-(leftRate * (r - a)))) *
                  ((leftRate + rightRate) * Real.exp
                    (-((leftRate + rightRate) * a))))) := by
              congr 1
              calc
                leftRate * Real.exp (-(leftRate * r)) *
                    (rightRate * Real.exp (-(rightRate * a))) =
                    leftRate * rightRate *
                      (Real.exp (-(leftRate * r)) *
                        Real.exp (-(rightRate * a))) := by ring
                _ = leftRate * rightRate *
                      (Real.exp (-(leftRate * (r - a))) *
                        Real.exp (-((leftRate + rightRate) * a))) := by
                      rw [<- Real.exp_add, harg, Real.exp_add]
                _ = (rightRate / (leftRate + rightRate)) *
                      (leftRate * Real.exp (-(leftRate * (r - a))) *
                        ((leftRate + rightRate) * Real.exp
                          (-((leftRate + rightRate) * a)))) := by
                      field_simp [ne_of_gt hsum_pos]
        _ = ENNReal.ofReal (rightRate / (leftRate + rightRate)) *
              (ENNReal.ofReal (leftRate * Real.exp (-(leftRate * (r - a)))) *
                ENNReal.ofReal ((leftRate + rightRate) * Real.exp
                  (-((leftRate + rightRate) * a)))) := by
              rw [ENNReal.ofReal_mul hratio_nonneg,
                ENNReal.ofReal_mul hleft_exp_nonneg]
    · have ha_neg : a < 0 := lt_of_not_ge ha
      rw [exponentialPDF_of_neg ha_neg, exponentialPDF_of_neg ha_neg]
      simp
  · have hnotmem : (r, a) ∉ exponentialDifferencePositiveCarrier := hpositive
    rw [Set.indicator_of_notMem hnotmem]
    have hnonpositive : r - a <= 0 := sub_nonpos.mpr (le_of_not_gt hpositive)
    have hnegative : r - a < 0 := lt_of_le_of_ne hnonpositive hp
    rw [exponentialPDF_of_neg hnegative]
    simp

/-- On the strict positive branch, subtracting the second exponential factor
produces an independent exponential residual of rate `leftRate` and a new
second coordinate of rate `leftRate + rightRate`.  The branch mass is
`rightRate / (leftRate + rightRate)`. -/
theorem map_exponentialDifferenceUnshear_expMeasure_prod_restrict_positive
    {leftRate rightRate : Real} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map exponentialDifferenceUnshear
      (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
        exponentialDifferencePositiveCarrier) =
      ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
        ((expMeasure leftRate).prod (expMeasure (leftRate + rightRate))) := by
  have hdensity :
      exponentialDifferencePositiveInputDensity leftRate rightRate =ᵐ[volume.prod volume]
        exponentialDifferencePositiveOutputDensity leftRate rightRate ∘
          exponentialDifferenceUnshear := by
    filter_upwards [ae_fst_sub_snd_ne_zero_volume_prod] with p hp
    exact exponentialDifferencePositive_density_eq_output_comp_unshear
      hleft hright p hp
  calc
    Measure.map exponentialDifferenceUnshear
        (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
          exponentialDifferencePositiveCarrier) =
        Measure.map exponentialDifferenceUnshear
          ((volume.prod volume).withDensity
            (exponentialDifferencePositiveInputDensity leftRate rightRate)) := by
          rw [expMeasure_prod_eq_withDensity_exponentialPair,
            MeasureTheory.restrict_withDensity
              measurableSet_exponentialDifferencePositiveCarrier,
            <- MeasureTheory.withDensity_indicator
              measurableSet_exponentialDifferencePositiveCarrier]
          rfl
    _ = Measure.map exponentialDifferenceUnshear
          ((volume.prod volume).withDensity
            (exponentialDifferencePositiveOutputDensity leftRate rightRate ∘
              exponentialDifferenceUnshear)) := by
          congr 1
          exact MeasureTheory.withDensity_congr_ae hdensity
    _ = (volume.prod volume).withDensity
          (exponentialDifferencePositiveOutputDensity leftRate rightRate) :=
      AppliedModelingLib.Probability.PoissonProcess.map_withDensity_comp_of_measurePreserving
        exponentialDifferenceUnshear_measurePreserving
        (exponentialDifferencePositiveOutputDensity leftRate rightRate)
        (measurable_exponentialDifferencePositiveOutputDensity _ _)
    _ = ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
          ((expMeasure leftRate).prod (expMeasure (leftRate + rightRate))) := by
      rw [expMeasure_prod_eq_withDensity_exponentialPair,
        <- MeasureTheory.withDensity_smul
          (ENNReal.ofReal (rightRate / (leftRate + rightRate)))
          (measurable_exponentialPairDensity _ _)]
      change (volume.prod volume).withDensity
          (fun p => ENNReal.ofReal (rightRate / (leftRate + rightRate)) *
            exponentialPairDensity leftRate (leftRate + rightRate) p) =
        (volume.prod volume).withDensity
          (fun p => ENNReal.ofReal (rightRate / (leftRate + rightRate)) *
            exponentialPairDensity leftRate (leftRate + rightRate) p)
      rfl

/-- Marginalizing the retained second coordinate gives the positive residual
branch itself. -/
theorem map_sub_expMeasure_prod_restrict_positive
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (fun p : ℝ × ℝ => p.1 - p.2)
      (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
        exponentialDifferencePositiveCarrier) =
      ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
        expMeasure leftRate := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure (leftRate + rightRate)) :=
    isProbabilityMeasure_expMeasure (add_pos hleft hright)
  calc
    Measure.map (fun p : ℝ × ℝ => p.1 - p.2)
        (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
          exponentialDifferencePositiveCarrier) =
        Measure.map Prod.fst
          (Measure.map exponentialDifferenceUnshear
            (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
              exponentialDifferencePositiveCarrier)) := by
          rw [Measure.map_map measurable_fst
            measurable_exponentialDifferenceUnshear]
          rfl
    _ = Measure.map Prod.fst
          (ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
            ((expMeasure leftRate).prod (expMeasure (leftRate + rightRate)))) := by
          rw [map_exponentialDifferenceUnshear_expMeasure_prod_restrict_positive
            hleft hright]
    _ = ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
          expMeasure leftRate := by
          rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul]

/-- The positive-difference branch has exactly its displayed mixture mass. -/
theorem expMeasure_prod_measure_exponentialDifferencePositiveCarrier
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    ((expMeasure leftRate).prod (expMeasure rightRate))
      exponentialDifferencePositiveCarrier =
      ENNReal.ofReal (rightRate / (leftRate + rightRate)) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (expMeasure (leftRate + rightRate)) :=
    isProbabilityMeasure_expMeasure (add_pos hleft hright)
  have hjoint := map_exponentialDifferenceUnshear_expMeasure_prod_restrict_positive
    hleft hright
  have huniv := congrArg (fun m : Measure (ℝ × ℝ) => m Set.univ) hjoint
  simpa [Measure.map_apply measurable_exponentialDifferenceUnshear
    MeasurableSet.univ, Measure.restrict_apply,
    exponentialDifferencePositiveCarrier] using huniv

/-- The complementary branch has the remaining mixture mass. -/
theorem expMeasure_prod_measure_exponentialDifferencePositiveCarrier_compl
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    ((expMeasure leftRate).prod (expMeasure rightRate))
      exponentialDifferencePositiveCarrierᶜ =
      ENNReal.ofReal (leftRate / (leftRate + rightRate)) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  have hsum_pos : 0 < leftRate + rightRate := add_pos hleft hright
  have hratio_nonneg : 0 ≤ rightRate / (leftRate + rightRate) :=
    div_nonneg hright.le hsum_pos.le
  rw [measure_compl measurableSet_exponentialDifferencePositiveCarrier
    (measure_ne_top _ _), measure_univ,
    expMeasure_prod_measure_exponentialDifferencePositiveCarrier hleft hright]
  calc
    1 - ENNReal.ofReal (rightRate / (leftRate + rightRate)) =
        ENNReal.ofReal (1 - rightRate / (leftRate + rightRate)) := by
          rw [ENNReal.ofReal_sub 1 hratio_nonneg]
          norm_num
    _ = ENNReal.ofReal (leftRate / (leftRate + rightRate)) := by
          congr 1
          field_simp [ne_of_gt hsum_pos]
          linarith

/-- The reflected difference used by the Lindley response update. -/
def exponentialReflectedDifference (p : ℝ × ℝ) : ℝ :=
  max (p.1 - p.2) 0

theorem measurable_exponentialReflectedDifference :
    Measurable exponentialReflectedDifference := by
  exact (measurable_fst.sub measurable_snd).max measurable_const

private theorem map_exponentialReflectedDifference_restrict_positive
    {leftRate rightRate : ℝ} :
    Measure.map exponentialReflectedDifference
      (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
        exponentialDifferencePositiveCarrier) =
      Measure.map (fun p : ℝ × ℝ => p.1 - p.2)
        (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
          exponentialDifferencePositiveCarrier) := by
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem
    measurableSet_exponentialDifferencePositiveCarrier] with p hp
  unfold exponentialReflectedDifference
  exact max_eq_left (sub_nonneg.mpr hp.le)

private theorem map_exponentialReflectedDifference_restrict_positive_compl
    {leftRate rightRate : ℝ} :
    Measure.map exponentialReflectedDifference
      (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
        exponentialDifferencePositiveCarrierᶜ) =
      (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
        exponentialDifferencePositiveCarrierᶜ) Set.univ • Measure.dirac 0 := by
  calc
    Measure.map exponentialReflectedDifference
        (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
          exponentialDifferencePositiveCarrierᶜ) =
        Measure.map (fun _ : ℝ × ℝ => 0)
          (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
            exponentialDifferencePositiveCarrierᶜ) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem
            measurableSet_exponentialDifferencePositiveCarrier.compl] with p hp
          unfold exponentialReflectedDifference
          exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hp))
    _ = (((expMeasure leftRate).prod (expMeasure rightRate)).restrict
          exponentialDifferencePositiveCarrierᶜ) Set.univ • Measure.dirac 0 :=
      Measure.map_const _ 0

/-- Exact law of the reflected difference of independent exponentials.  The
strict positive branch is exponential with rate `leftRate`; the complement
is an atom at zero. -/
theorem map_exponentialReflectedDifference_expMeasure_prod
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map exponentialReflectedDifference
      ((expMeasure leftRate).prod (expMeasure rightRate)) =
      ENNReal.ofReal (leftRate / (leftRate + rightRate)) • Measure.dirac 0 +
        ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
          expMeasure leftRate := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  let pair : Measure (ℝ × ℝ) :=
    (expMeasure leftRate).prod (expMeasure rightRate)
  have hsplit : pair = pair.restrict exponentialDifferencePositiveCarrier +
      pair.restrict exponentialDifferencePositiveCarrierᶜ := by
    simpa [pair] using
      (Measure.restrict_add_restrict_compl
        (μ := (expMeasure leftRate).prod (expMeasure rightRate))
        measurableSet_exponentialDifferencePositiveCarrier).symm
  calc
    Measure.map exponentialReflectedDifference pair =
        Measure.map exponentialReflectedDifference
          (pair.restrict exponentialDifferencePositiveCarrier +
            pair.restrict exponentialDifferencePositiveCarrierᶜ) := by
          exact congrArg (Measure.map exponentialReflectedDifference) hsplit
    _ =
        Measure.map exponentialReflectedDifference
          (pair.restrict exponentialDifferencePositiveCarrier) +
        Measure.map exponentialReflectedDifference
          (pair.restrict exponentialDifferencePositiveCarrierᶜ) := by
          exact Measure.map_add _ _ measurable_exponentialReflectedDifference
    _ = ENNReal.ofReal (rightRate / (leftRate + rightRate)) • expMeasure leftRate +
        ENNReal.ofReal (leftRate / (leftRate + rightRate)) • Measure.dirac 0 := by
          rw [map_exponentialReflectedDifference_restrict_positive,
            map_sub_expMeasure_prod_restrict_positive hleft hright,
            map_exponentialReflectedDifference_restrict_positive_compl,
            Measure.restrict_apply MeasurableSet.univ,
            Set.univ_inter,
            expMeasure_prod_measure_exponentialDifferencePositiveCarrier_compl
              hleft hright]
    _ = ENNReal.ofReal (leftRate / (leftRate + rightRate)) • Measure.dirac 0 +
        ENNReal.ofReal (rightRate / (leftRate + rightRate)) • expMeasure leftRate := by
          rw [add_comm]

end

end AppliedModelingLib.Probability

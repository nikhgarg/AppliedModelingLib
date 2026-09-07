import PG23MonocultureMatching.MainTheorems
import PRPKG24AccuracyDiversity.Uniform

/-!
# Paper Assumptions: Monoculture in Matching Markets

This file names paper-source conditions that remain visible inputs to the
paper-facing theorem rows.  Each declaration should correspond to an explicit
source condition, not a proof convenience.
-/

open Filter Topology
open scoped ProbabilityTheory
open MeasureTheory

namespace PG23MonocultureMatching

open AppliedModelingLib.Matching

universe u v w

/--
The source defines `v_S` by the value tail equation `η((v_S, ∞)) = S`.

This assumption alias exposes that paper condition at the PG23 interface while
reusing the generic upper-tail certificate in the probability library.
-/
-- audit-premise: AppliedModelingLib.Probability.upperTailMass η threshold = capacity
abbrev source_assumption_value_threshold
    (η : Measure ℝ) (capacity threshold : ℝ) : Prop :=
  AppliedModelingLib.Probability.UpperTailThresholdCertificate η capacity threshold

/--
The source model assumes applicant values are supported on the finite interval
`[vMin, vMax]`.

This is the primitive support condition used to prove that any cutoff clearing
an interior capacity lies strictly between the value-plus-noise endpoints.
-/
-- audit-premise: ∀ᵐ v ∂η, v ∈ Set.Icc vMin vMax
abbrev source_assumption_value_support
    (η : Measure ℝ) (vMin vMax : ℝ) : Prop :=
  ∀ᵐ v ∂η, v ∈ Set.Icc vMin vMax

/--
Source-visible variance certificate for PG23 Definition 2.

The paper assumes maximum concentration in the main theorems, but also states
the reusable sufficient condition used in Example 1: a variance bound for the
maximum order statistic that tends to zero.  This record keeps that optional
stronger route explicit when a concrete noise law is being verified; Lean
derives the Chebyshev deviation estimate from the variance premise.
-/
-- audit-premise: PG23 Definition 2 variance certificate for the iid maximum order statistic
structure ExpectedMaximumVarianceSourceModel
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (varianceBound : ℕ → ℝ) : Prop where
  variance_zero : Tendsto varianceBound atTop (nhds 0)
  memLp :
    ∀ᶠ n : ℕ in atTop,
      MemLp
        (fun sample : Fin (n + 1) → ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
  variance_bound :
    ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.variance
        (fun sample : Fin (n + 1) → ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) ≤
      varianceBound n

/--
Legacy name retained for existing PG23 theorem packages.  Its fields are now
the actual variance-bound data; the Chebyshev inequality is derived in Lean.
-/
abbrev ExpectedMaximumChebyshevSourceModel
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (varianceBound : ℕ → ℝ) : Prop :=
  ExpectedMaximumVarianceSourceModel baseNoiseLaw varianceBound

theorem expectedMaximumConcentrating_of_variance_source_model
    {baseNoiseLaw : Measure ℝ} [IsProbabilityMeasure baseNoiseLaw]
    {varianceBound : ℕ → ℝ}
    (H : ExpectedMaximumVarianceSourceModel baseNoiseLaw varianceBound) :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) :=
  maximumOrderStatisticConcentratingAroundExpected_of_variance_bound
    (sampleLaw := fun n : ℕ =>
      Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
    (varianceBound := varianceBound)
    (fun _n => by infer_instance)
    H.variance_zero H.memLp H.variance_bound

/--
Compatibility name for older PG23 wrappers.  The premise is definitionally the
same variance/L2 certificate; Chebyshev's inequality is derived by Lean.
-/
theorem expectedMaximumConcentrating_of_chebyshev_source_model
    {baseNoiseLaw : Measure ℝ} [IsProbabilityMeasure baseNoiseLaw]
    {varianceBound : ℕ → ℝ}
    (H : ExpectedMaximumChebyshevSourceModel baseNoiseLaw varianceBound) :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) :=
  expectedMaximumConcentrating_of_variance_source_model H

/--
PG23 Example 1: iid uniform `[0,1]` noise satisfies the variance source model
used to prove Definition 2.

The proof reuses the PRPKG uniform order-statistic formula for the expected
maximum and Popoviciu's bounded-variance inequality.  For `n + 1` iid samples,
`E[max] = (n + 1)/(n + 2)`, so
`Var(max) ≤ (1 - E[max]) * E[max] ≤ 1/(n + 2)`.
-/
theorem expectedMaximumVarianceSourceModel_uniform01 :
    ExpectedMaximumVarianceSourceModel
      PRPKG24AccuracyDiversity.uniform01Measure
      (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ))) := by
  constructor
  · have hden :
        Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    exact Filter.Tendsto.const_div_atTop hden (1 : ℝ)
  · filter_upwards with n
    let μn : Measure (Fin (n + 1) → ℝ) :=
      Measure.pi
        (fun _ : Fin (n + 1) =>
          PRPKG24AccuracyDiversity.uniform01Measure)
    let X : (Fin (n + 1) → ℝ) → ℝ :=
      fun sample =>
        AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))
    have hboundsX : ∀ᵐ sample ∂μn, X sample ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards
        [PRPKG24AccuracyDiversity.uniform01ProductMeasure_all_bounds_ae
          (n + 1)] with sample hsample
      exact ⟨
        AppliedModelingLib.Probability.le_upperOrderStatistic_of_forall_le
          (fun i => (hsample i).1)
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1)),
        AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
          (fun i => (hsample i).2)
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))⟩
    have hmeas :
        AEStronglyMeasurable X μn :=
      (AppliedModelingLib.Probability.upperOrderStatistic_measurable
        (AppliedModelingLib.Probability.topSampleRank (n := n + 1))).aestronglyMeasurable
    simpa [μn, X] using
      (MeasureTheory.memLp_of_bounded hboundsX hmeas 2)
  · filter_upwards with n
    let μn : Measure (Fin (n + 1) → ℝ) :=
      Measure.pi
        (fun _ : Fin (n + 1) =>
          PRPKG24AccuracyDiversity.uniform01Measure)
    let X : (Fin (n + 1) → ℝ) → ℝ :=
      fun sample =>
        AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))
    have hboundsX : ∀ᵐ sample ∂μn, X sample ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards
        [PRPKG24AccuracyDiversity.uniform01ProductMeasure_all_bounds_ae
          (n + 1)] with sample hsample
      exact ⟨
        AppliedModelingLib.Probability.le_upperOrderStatistic_of_forall_le
          (fun i => (hsample i).1)
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1)),
        AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
          (fun i => (hsample i).2)
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))⟩
    have hmeas :
        AEMeasurable X μn :=
      (AppliedModelingLib.Probability.upperOrderStatistic_measurable
        (AppliedModelingLib.Probability.topSampleRank (n := n + 1))).aemeasurable
    have hvar :
        ProbabilityTheory.variance X μn ≤
          (1 - μn[X]) * (μn[X] - 0) :=
      ProbabilityTheory.variance_le_sub_mul_sub
        (μ := μn) (X := X) (a := 0) (b := 1) hboundsX hmeas
    have hmean :
        μn[X] =
          (((n + 1 : ℕ) : ℝ) / ((((n + 1 : ℕ) : ℝ) + 1))) := by
      have hraw :=
        PRPKG24AccuracyDiversity.uniform01ProductMeasure_expectedUpperOrderStatistic_eq
          (q := n + 1)
          (rankFromTop :=
            AppliedModelingLib.Probability.topSampleRank (n := n + 1))
      simpa [μn, X, AppliedModelingLib.Probability.expectedUpperOrderStatistic,
        AppliedModelingLib.Probability.topSampleRank] using hraw
    have hgap_bound :
        (1 - μn[X]) * (μn[X] - 0) ≤
          1 / (((n + 2 : ℕ) : ℝ)) := by
      rw [hmean]
      have hden_pos : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
      have hsucc_rewrite :
          (((n + 1 : ℕ) : ℝ) + 1) = (((n + 2 : ℕ) : ℝ)) := by
        have hnat : n + 1 + 1 = n + 2 := by omega
        exact_mod_cast hnat
      rw [hsucc_rewrite]
      have hnonneg : 0 ≤ (((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ))) := by
        positivity
      have hle_one :
          (((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ)) ≤ 1) := by
        rw [div_le_one hden_pos]
        norm_num
      calc
        (1 - ((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ))) *
            (((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ)) - 0)
            ≤ 1 *
              (1 / (((n + 2 : ℕ) : ℝ))) := by
              have hleft_nonneg :
                  0 ≤ 1 - ((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ)) := by
                linarith
              have hleft_le :
                  1 - ((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ)) ≤
                    1 / (((n + 2 : ℕ) : ℝ)) := by
                rw [sub_le_iff_le_add]
                rw [← add_div]
                have hsum :
                    (1 : ℝ) + ((n + 1 : ℕ) : ℝ) =
                      (((n + 2 : ℕ) : ℝ)) := by
                  have hnat : 1 + (n + 1) = n + 2 := by omega
                  exact_mod_cast hnat
                rw [hsum]
                exact le_of_eq (div_self hden_pos.ne').symm
              have hright_le :
                  ((n + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ)) - 0 ≤ 1 := by
                simpa using hle_one
              nlinarith [mul_le_mul hleft_le hright_le (by simpa using hnonneg)
                (by positivity :
                  0 ≤ 1 / (((n + 2 : ℕ) : ℝ)))]
        _ = 1 / (((n + 2 : ℕ) : ℝ)) := by ring
    exact hvar.trans hgap_bound

/--
Source model package for the preferred PG23 Lemma 2 equal-cutoff route.

This record groups the A-L cutoff lattice interface with the paper's
coordinate representation, swap symmetry, scalar clearing equation, iid
single-cutoff demand formula, and support endpoint bounds.  The proof-facing
theorems project these fields and derive uniqueness of the market-clearing
cutoff and equality of the cutoff selected by any stable matching.
-/
-- audit-premise: PG23 Lemma 2 source coordinate/symmetry/scalar-clearing/support clauses for the concrete iid cutoff model
structure Lemma2EqualCutoffsSourceModel
    {Student : Type u} {College : Type v}
    (M : CutoffMarket Student College)
    (CollegeCoord : Type w) [DecidableEq CollegeCoord]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    (valueCDF : ℝ → ℝ)
    (vMin vMax xMin xMax : ℝ) : Prop where
  coord_ext :
    ∀ P Q : M.Cutoff, coord P = coord Q → P = Q
  order :
    ∀ P Q : M.Cutoff,
      L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q)
  swap :
    ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
      ∃ Q : M.Cutoff,
        M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d
  clearing :
    ∀ P : M.Cutoff, ∀ x : ℝ,
      M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply
  access_integrable :
    ∀ z : ℝ,
      Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => z) college) η
  demand_eq :
    ∀ z : ℝ,
      demand z =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => z) college ∂η
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  value_nonempty : vMin < vMax
  cutoff_bounds :
    ∀ P : M.Cutoff, ∀ x : ℝ,
      M.MarketClearing P → (∀ c, coord P c = x) →
        vMin + xMin < x ∧ x < vMax + xMax

/--
Source model package for PG23 Lemma 2 with the scalar demand function defined
by the paper's iid integral formula.

This removes the proof-only demand equality and integrability fields from the
paper-facing boundary.  Integrability is supplied by the shared affordability
library for bounded iid single-cutoff crossing probabilities.
-/
-- audit-premise: PG23 Lemma 2 source clauses with scalar demand definitionally equal to the iid integral formula
structure Lemma2EqualCutoffsIntegralSourceModel
    {Student : Type u} {College : Type v}
    (M : CutoffMarket Student College)
    (CollegeCoord : Type w) [DecidableEq CollegeCoord]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (supply : ℝ)
    (valueCDF : ℝ → ℝ)
    (vMin vMax xMin xMax : ℝ) : Prop where
  coord_ext :
    ∀ P Q : M.Cutoff, coord P = coord Q → P = Q
  order :
    ∀ P Q : M.Cutoff,
      L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q)
  swap :
    ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
      ∃ Q : M.Cutoff,
        M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d
  clearing :
    ∀ P : M.Cutoff, ∀ x : ℝ,
      M.MarketClearing P → (∀ c, coord P c = x) →
        (∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => x) college ∂η) = supply
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  value_nonempty : vMin < vMax
  cutoff_bounds :
    ∀ P : M.Cutoff, ∀ x : ℝ,
      M.MarketClearing P → (∀ c, coord P c = x) →
        vMin + xMin < x ∧ x < vMax + xMax

/--
Source model package for the concrete iid PG23 Theorem 3 differential-access
route.

The proof-facing theorem derives monoculture invariance and polyculture
monotonicity from the iid cutoff model.  The remaining source inputs are the
one-dimensional noise CDF support facts used to get strict improvement on the
interior support region.
-/
-- audit-premise: PG23 Theorem 3 concrete iid noise support/CDF clauses
structure Theorem3DifferentialAccessSourceModel
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (xMin xMax : ℝ) : Prop where
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1

/--
Source model package for the strengthened PG23 Theorem 2 positive-interval
route.

This record groups the paper's demand-representation, clearing, support, and
interval-witness clauses for the concrete iid cutoff model.  The proof-facing
theorem projects these fields and derives the weak access comparison,
positive interval mass, and eventual strict polyculture access improvement.
-/
-- audit-premise: PG23 Theorem 2 source demand/clearing/support/interval clauses for the concrete iid cutoff model
structure Theorem2PositiveIntervalSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoDemand polyDemand : ℕ → ℝ → ℝ)
    (commonMonoDemand : ℝ → ℝ)
    (monoCutoff polyCutoff : ℕ → ℝ)
    (commonMonoSupply : ℝ)
    (valueCDF : ℝ → ℝ)
    (vS valueSupply xMin xMax vMin vMax a b : ℝ) : Prop where
  mono_clear :
    ∀ m, monoDemand m (monoCutoff m) = valueSupply
  mono_demand_eq :
    ∀ m : ℕ, ∀ z : ℝ,
      monoDemand m z =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η
  poly_eq :
    ∀ m, polyDemand m (polyCutoff m) =
      ∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m) ∂η
  concentrating :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
  value_threshold :
    source_assumption_value_threshold η valueSupply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  poly_clear :
    ∀ m,
      ∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m) ∂η = valueSupply
  common_clear :
    ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply
  common_eq :
    ∀ z : ℝ,
      commonMonoDemand z =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  threshold_le_interval_left : vS ≤ a
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax

/--
Source model package for the PG23 Theorem 2 route with the demand functions
defined by their source integral formulas.

This removes the proof-only equality fields saying that named demand functions
equal those integrals; the paper-facing boundary is the clearing equations for
the integral formulas themselves, plus concentration/support/interval clauses.
-/
-- audit-premise: PG23 Theorem 2 source clauses with demand functions definitionally equal to their integral formulas
structure Theorem2PositiveIntervalIntegralSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoCutoff polyCutoff : ℕ → ℝ)
    (valueCDF : ℝ → ℝ)
    (vS valueSupply xMin xMax vMin vMax a b : ℝ) : Prop where
  mono_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) ∂η) =
        valueSupply
  poly_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m) ∂η) =
        valueSupply
  concentrating :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
  value_threshold :
    source_assumption_value_threshold η valueSupply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  common_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff m) (topFirm 0) ∂η) =
        valueSupply
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  threshold_le_interval_left : vS ≤ a
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax

/--
Source model package for the PG23 Theorem 2 route with the monoculture
clearing equations derived from the common single-cutoff integral formula.

For iid product noise and a constant cutoff, a named college's crossing
probability is the one-dimensional upper-tail probability, independently of
the number of colleges.  Thus the common monoculture clearing equation implies
the per-market monoculture clearing equations used by the proof.
-/
-- audit-premise: PG23 Theorem 2 source clauses with monoculture clearing derived from the common iid single-cutoff integral
structure Theorem2PositiveIntervalCommonIntegralSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoCutoff polyCutoff : ℕ → ℝ)
    (valueCDF : ℝ → ℝ)
    (vS valueSupply xMin xMax vMin vMax a b : ℝ) : Prop where
  poly_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m) ∂η) =
        valueSupply
  concentrating :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
  value_threshold :
    source_assumption_value_threshold η valueSupply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  common_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff m) (topFirm 0) ∂η) =
        valueSupply
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  threshold_le_interval_left : vS ≤ a
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax

theorem theorem2_positive_interval_integral_source_model_of_common_integral
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {baseNoiseLaw : Measure ℝ} [IsProbabilityMeasure baseNoiseLaw]
    {topFirm : ∀ m : ℕ, Fin (m + 1)}
    {monoCutoff polyCutoff : ℕ → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (source :
      Theorem2PositiveIntervalCommonIntegralSourceModel
        η baseNoiseLaw topFirm monoCutoff polyCutoff valueCDF
        vS valueSupply xMin xMax vMin vMax a b) :
    Theorem2PositiveIntervalIntegralSourceModel
      η baseNoiseLaw topFirm monoCutoff polyCutoff valueCDF
      vS valueSupply xMin xMax vMin vMax a b :=
  { mono_clear := by
      intro m
      calc
        (∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) ∂η) =
            ∫ v,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
                v (fun _ : Fin (0 + 1) => monoCutoff m) (topFirm 0) ∂η := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun v => by
            change
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
                  v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
                  v (fun _ : Fin (0 + 1) => monoCutoff m) (topFirm 0)
            rw [
              AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass
                (μ := baseNoiseLaw) (v := v) (P := monoCutoff m)
                (c := topFirm m),
              AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass
                (μ := baseNoiseLaw) (v := v) (P := monoCutoff m)
                (c := topFirm 0)])
        _ = valueSupply := source.common_clear m
    poly_clear := source.poly_clear
    concentrating := source.concentrating
    value_threshold := source.value_threshold
    threshold_interior := source.threshold_interior
    common_clear := source.common_clear
    value_support := source.value_support
    value_cdf_strict := source.value_cdf_strict
    noise_cdf_strict := source.noise_cdf_strict
    noise_left := source.noise_left
    noise_right := source.noise_right
    value_measure_eq := source.value_measure_eq
    interval_left := source.interval_left
    interval_right := source.interval_right
    interval_order := source.interval_order
    threshold_le_interval_left := source.threshold_le_interval_left
    interval_lower_support := source.interval_lower_support
    interval_upper_support := source.interval_upper_support }

/--
Theorem 2 source model with Definition 2 discharged by a visible variance/L2
certificate for the iid maximum order statistic.

This is a sufficient-condition source package, useful for concrete
distributions and examples.  The main paper theorem may still use
`Theorem2PositiveIntervalIntegralSourceModel` directly because maximum
concentration is itself a named paper assumption.
-/
-- audit-premise: PG23 Theorem 2 source clauses plus a variance/L2 certificate proving Definition 2
structure Theorem2PositiveIntervalChebyshevIntegralSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoCutoff polyCutoff : ℕ → ℝ)
    (valueCDF : ℝ → ℝ)
    (vS valueSupply xMin xMax vMin vMax a b : ℝ)
    (varianceBound : ℕ → ℝ) : Prop where
  maximum_order :
    ExpectedMaximumVarianceSourceModel baseNoiseLaw varianceBound
  mono_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) ∂η) =
        valueSupply
  poly_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m) ∂η) =
        valueSupply
  value_threshold :
    source_assumption_value_threshold η valueSupply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  common_clear :
    ∀ m : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff m) (topFirm 0) ∂η) =
        valueSupply
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  threshold_le_interval_left : vS ≤ a
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax

theorem theorem2_positive_interval_integral_source_model_of_chebyshev
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {baseNoiseLaw : Measure ℝ} [IsProbabilityMeasure baseNoiseLaw]
    {topFirm : ∀ m : ℕ, Fin (m + 1)}
    {monoCutoff polyCutoff : ℕ → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    {varianceBound : ℕ → ℝ}
    (source :
      Theorem2PositiveIntervalChebyshevIntegralSourceModel
        η baseNoiseLaw topFirm monoCutoff polyCutoff valueCDF
        vS valueSupply xMin xMax vMin vMax a b varianceBound) :
    Theorem2PositiveIntervalIntegralSourceModel
      η baseNoiseLaw topFirm monoCutoff polyCutoff valueCDF
      vS valueSupply xMin xMax vMin vMax a b :=
  { mono_clear := source.mono_clear
    poly_clear := source.poly_clear
    concentrating :=
      expectedMaximumConcentrating_of_variance_source_model
        source.maximum_order
    value_threshold := source.value_threshold
    threshold_interior := source.threshold_interior
    common_clear := source.common_clear
    value_support := source.value_support
    value_cdf_strict := source.value_cdf_strict
    noise_cdf_strict := source.noise_cdf_strict
    noise_left := source.noise_left
    noise_right := source.noise_right
    value_measure_eq := source.value_measure_eq
    interval_left := source.interval_left
    interval_right := source.interval_right
    interval_order := source.interval_order
    threshold_le_interval_left := source.threshold_le_interval_left
    interval_lower_support := source.interval_lower_support
    interval_upper_support := source.interval_upper_support }

/--
Source model package for the strengthened PG23 Theorem 1 full-welfare route.

This record groups the paper's maximum-concentration, supply-cutoff,
market-clearing, support, no-atom, interval, and welfare-integral clauses for
the concrete iid cutoff model.  The proof-facing theorem derives the
low/high match probability limits, monoculture invariance, polyculture welfare
convergence, and strict monoculture welfare suboptimality.
-/
-- audit-premise: PG23 Theorem 1 source clauses for the concrete iid cutoff model and welfare integrals
structure Theorem1FullWelfareSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    (polyCutoff monoCutoff : ℕ → ℝ)
    (commonMonoDemand : ℝ → ℝ)
    (valueCDF : ℝ → ℝ)
    (vS supply commonMonoSupply vMin vMax xMin xMax a b : ℝ)
    (polyWelfare monoWelfare : ℕ → ℝ) (optimalWelfare : ℝ) : Prop where
  concentrating :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
  value_threshold :
    source_assumption_value_threshold η supply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  poly_clear :
    ∀ n,
      ∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n) ∂η = supply
  common_clear :
    ∀ n : ℕ, commonMonoDemand (monoCutoff n) = commonMonoSupply
  common_eq :
    ∀ z : ℝ,
      commonMonoDemand z =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η
  common_supply_eq : commonMonoSupply = supply
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  no_atom : η {vS} = 0
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax
  polyWelfare_eq :
    ∀ n : ℕ, polyWelfare n =
      ∫ v : ℝ,
        v *
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η
  monoWelfare_eq :
    ∀ n : ℕ, monoWelfare n =
      ∫ v : ℝ,
        v *
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η
  optimalWelfare_eq :
    optimalWelfare =
      ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η

/--
Source model package for PG23 Theorem 1 with the common monoculture demand
and welfare quantities defined by their paper integral formulas.

This keeps the real source conditions visible while removing definitional
plumbing fields for the common demand function and welfare notation.
-/
-- audit-premise: PG23 Theorem 1 source clauses with common demand and welfare quantities definitionally equal to their integral formulas
structure Theorem1FullWelfareIntegralSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    (polyCutoff monoCutoff : ℕ → ℝ)
    (valueCDF : ℝ → ℝ)
    (vS supply vMin vMax xMin xMax a b : ℝ) : Prop where
  concentrating :
    maximumOrderStatisticConcentratingAroundExpected
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
  value_threshold :
    source_assumption_value_threshold η supply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  poly_clear :
    ∀ n : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n) ∂η) =
        supply
  common_clear :
    ∀ n : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff n) (topFirm 0) ∂η) =
        supply
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  no_atom : η {vS} = 0
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax

/--
Theorem 1 full-welfare source model with Definition 2 discharged by a visible
variance/L2 certificate for the iid maximum order statistic.

This sufficient-condition package is intended for concrete noise distributions
and examples.  It derives the preferred integral source model while keeping
the paper's main maximum-concentration assumption available as the shorter
source-facing route.
-/
-- audit-premise: PG23 Theorem 1 source clauses plus a variance/L2 certificate proving Definition 2
structure Theorem1FullWelfareChebyshevIntegralSourceModel
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    (polyCutoff monoCutoff : ℕ → ℝ)
    (valueCDF : ℝ → ℝ)
    (vS supply vMin vMax xMin xMax a b : ℝ)
    (varianceBound : ℕ → ℝ) : Prop where
  maximum_order :
    ExpectedMaximumVarianceSourceModel baseNoiseLaw varianceBound
  value_threshold :
    source_assumption_value_threshold η supply vS
  threshold_interior :
    vS ∈ Set.Ioo vMin vMax
  poly_clear :
    ∀ n : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n) ∂η) =
        supply
  common_clear :
    ∀ n : ℕ,
      (∫ v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff n) (topFirm 0) ∂η) =
        supply
  value_support :
    source_assumption_value_support η vMin vMax
  value_cdf_strict :
    StrictMonoOn valueCDF (Set.Ioo vMin vMax)
  noise_cdf_strict :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
      (Set.Icc xMin xMax)
  noise_left :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0
  noise_right :
    AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1
  value_measure_eq :
    ∀ a b : ℝ,
      a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
        η.real (Set.Ioo a b) = valueCDF b - valueCDF a
  no_atom : η {vS} = 0
  interval_left : a ∈ Set.Ioo vMin vMax
  interval_right : b ∈ Set.Ioo vMin vMax
  interval_order : a < b
  interval_lower_support : xMin < monoCutoff 0 - b
  interval_upper_support : monoCutoff 0 - a < xMax

theorem theorem1_full_welfare_integral_source_model_of_chebyshev
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {baseNoiseLaw : Measure ℝ} [IsProbabilityMeasure baseNoiseLaw]
    {topFirm : ∀ n : ℕ, Fin (n + 1)}
    {polyCutoff monoCutoff : ℕ → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS supply vMin vMax xMin xMax a b : ℝ}
    {varianceBound : ℕ → ℝ}
    (source :
      Theorem1FullWelfareChebyshevIntegralSourceModel
        η baseNoiseLaw topFirm polyCutoff monoCutoff valueCDF
        vS supply vMin vMax xMin xMax a b varianceBound) :
    Theorem1FullWelfareIntegralSourceModel
      η baseNoiseLaw topFirm polyCutoff monoCutoff valueCDF
      vS supply vMin vMax xMin xMax a b :=
  { concentrating :=
      expectedMaximumConcentrating_of_variance_source_model
        source.maximum_order
    value_threshold := source.value_threshold
    threshold_interior := source.threshold_interior
    poly_clear := source.poly_clear
    common_clear := source.common_clear
    value_support := source.value_support
    value_cdf_strict := source.value_cdf_strict
    noise_cdf_strict := source.noise_cdf_strict
    noise_left := source.noise_left
    noise_right := source.noise_right
    value_measure_eq := source.value_measure_eq
    no_atom := source.no_atom
    interval_left := source.interval_left
    interval_right := source.interval_right
    interval_order := source.interval_order
    interval_lower_support := source.interval_lower_support
    interval_upper_support := source.interval_upper_support }

end PG23MonocultureMatching

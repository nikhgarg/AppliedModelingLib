import AL16SupplyDemandMatching.MainTheorems
import AppliedModelingLib.Foundations.Math.MonotoneContinuity
import AppliedModelingLib.Markets.Matching.Affordability
import AppliedModelingLib.Markets.Matching.ContinuumCutoff
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Monoculture in Matching Markets: Top-Down Formalization Surface

This file starts the PG23 formalization at the theorem seams needed for fast
closeout.  It uses the reusable cutoff-market interface for the
Azevedo-Leshno layer, then exposes the remaining PG23 analytic work as named,
source-shaped propositions.
-/

open Filter Topology

namespace PG23MonocultureMatching

open AppliedModelingLib.Matching
open MeasureTheory

universe u v

variable {Student : Type u} {College : Type v}
variable (M : CutoffMarket Student College)

/-- PG23 Lemma 1 surface: the A-L supply/demand bridge used by the paper. -/
abbrev lemma1_supplyDemandBridge (_I : SupplyDemandInterface M) : Prop :=
  ∀ μ : M.Matching,
    M.Stable μ ↔
      ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P

/-- Lemma 1 follows immediately from the reusable A-L surface. -/
theorem lemma1_supplyDemandBridge_of_AL
    (I : SupplyDemandInterface M) :
    lemma1_supplyDemandBridge M I := by
  intro μ
  exact I.stable_iff_exists_marketClearing_cutoff μ

/--
The PG23 equal-cutoff proof uses the A-L lattice theorem to obtain least and
greatest market-clearing cutoffs, then proves by symmetry/strict monotonicity
that those extrema coincide.
-/
structure EqualCutoffExtremaRoute (L : CutoffLatticeInterface M) where
  leastCutoff : M.Cutoff
  greatestCutoff : M.Cutoff
  least_is_least :
    M.MarketClearing leastCutoff ∧
      ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff leastCutoff P
  greatest_is_greatest :
    M.MarketClearing greatestCutoff ∧
      ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P greatestCutoff
  extrema_coincide : leastCutoff = greatestCutoff

/--
Build the equal-cutoff extrema route from the A-L lattice extrema and a direct
proof that any least and greatest market-clearing cutoffs coincide.
-/
noncomputable def equalCutoffExtremaRoute_of_lattice_extrema_coincide
    (L : CutoffLatticeInterface M)
    (hcoincide :
      ∀ bot top : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        bot = top) :
    EqualCutoffExtremaRoute M L := by
  classical
  let bot : M.Cutoff := Classical.choose L.exists_least_marketClearing
  let top : M.Cutoff := Classical.choose L.exists_greatest_marketClearing
  have hbot :
      M.MarketClearing bot ∧
        ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P :=
    Classical.choose_spec L.exists_least_marketClearing
  have htop :
      M.MarketClearing top ∧
        ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top :=
    Classical.choose_spec L.exists_greatest_marketClearing
  exact
    { leastCutoff := bot
      greatestCutoff := top
      least_is_least := hbot
      greatest_is_greatest := htop
      extrema_coincide := hcoincide bot top hbot htop }

/--
PG23 Lemma 2 consequence: once the least and greatest market-clearing cutoffs
coincide, the market-clearing cutoff is unique.
-/
theorem lemma2_unique_marketClearing_cutoff_of_extrema_route
    {L : CutoffLatticeInterface M}
    (R : EqualCutoffExtremaRoute M L) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  AL16SupplyDemandMatching.theoremA1_unique_marketClearing_cutoff_of_least_greatest_eq M L
    R.least_is_least R.greatest_is_greatest R.extrema_coincide

/--
PG23 Lemma 2 consequence in the form used by the source proof: the A-L lattice
theorem supplies least and greatest cutoffs, so it is enough to prove those
two extrema coincide.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide
    (L : CutoffLatticeInterface M)
    (hcoincide :
      ∀ bot top : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        bot = top) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_extrema_route M
    (equalCutoffExtremaRoute_of_lattice_extrema_coincide M L hcoincide)

/--
PG23 Lemma 1 plus Lemma 2 consequence: under the equal-cutoff/uniqueness
route, the cutoff selected for a stable matching is independent of which
stable matching is chosen.
-/
theorem lemma2_stableMatching_cutoffs_equal_of_lattice_extrema_coincide
    (I : SupplyDemandInterface M) (L : CutoffLatticeInterface M)
    (hcoincide :
      ∀ bot top : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        bot = top)
    {μ ν : M.Matching} (hμ : M.Stable μ) (hν : M.Stable ν) :
    AL16SupplyDemandMatching.stableMatchingMarketClearingCutoff M I hμ =
      AL16SupplyDemandMatching.stableMatchingMarketClearingCutoff M I hν :=
  AL16SupplyDemandMatching.stableMatchingMarketClearingCutoff_eq_of_unique_marketClearing
    M I hμ hν
      (lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide
        M L hcoincide)

/--
PG23 Lemma 2 source-shaped scalar route.  Once the symmetry argument shows
every market-clearing cutoff is a constant cutoff, and strict monotonicity of
the common-cutoff demand equation shows the scalar clearing value is unique,
the market-clearing cutoff itself is unique.

`constantValue P x` means that cutoff vector `P` is the common scalar cutoff
`x`; the paper-specific model supplies this predicate and proves its
extensionality.
-/
theorem lemma2_unique_marketClearing_cutoff_of_constant_scalar_unique
    (constantValue : M.Cutoff → ℝ → Prop)
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hscalar_unique :
      ∀ P Q : M.Cutoff, ∀ x y : ℝ,
        M.MarketClearing P → M.MarketClearing Q →
          constantValue P x → constantValue Q y → x = y)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q := by
  intro P Q hP hQ
  rcases hconstant P hP with ⟨x, hx⟩
  rcases hconstant Q hQ with ⟨y, hy⟩
  have hxy : x = y := hscalar_unique P Q x y hP hQ hx hy
  exact hconstant_ext P Q x hx (by simpa [hxy] using hy)

/--
PG23 Lemma 2 lattice route with source-shaped equal-cutoff ingredients.  The
A-L lattice theorem supplies least and greatest market-clearing cutoffs; the
paper-specific symmetry/strict-monotonicity work supplies constant-cutoff
values and uniqueness of the common scalar.  This builds the same extrema
route as the black-box `hcoincide` theorem, but with explicit source-facing
subclaims.
-/
noncomputable def equalCutoffExtremaRoute_of_lattice_constant_scalar_unique
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hscalar_unique :
      ∀ P Q : M.Cutoff, ∀ x y : ℝ,
        M.MarketClearing P → M.MarketClearing Q →
          constantValue P x → constantValue Q y → x = y)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    EqualCutoffExtremaRoute M L := by
  refine equalCutoffExtremaRoute_of_lattice_extrema_coincide M L ?_
  intro bot top hbot htop
  exact
    lemma2_unique_marketClearing_cutoff_of_constant_scalar_unique
      M constantValue hconstant hscalar_unique hconstant_ext
      bot top hbot.1 htop.1

/--
PG23 Lemma 2 consequence from the A-L lattice theorem plus explicit
constant-scalar uniqueness ingredients.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_constant_scalar_unique
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hscalar_unique :
      ∀ P Q : M.Cutoff, ∀ x y : ℝ,
        M.MarketClearing P → M.MarketClearing Q →
          constantValue P x → constantValue Q y → x = y)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_extrema_route M
    (equalCutoffExtremaRoute_of_lattice_constant_scalar_unique
      M L constantValue hconstant hscalar_unique hconstant_ext)

/--
Scalar clearing uniqueness: a strictly decreasing scalar demand equation can
clear a fixed supply at at most one cutoff.
-/
theorem scalarClearing_unique_of_strict_antitone_demand
    {demand : ℝ → ℝ} {supply x y : ℝ}
    (hstrict : ∀ a b : ℝ, a < b → demand b < demand a)
    (hx : demand x = supply) (hy : demand y = supply) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlt_demand : demand y < demand x := hstrict x y hlt
    rw [hx, hy] at hlt_demand
    exact (lt_irrefl supply) hlt_demand
  · have hlt_demand : demand x < demand y := hstrict y x hgt
    rw [hx, hy] at hlt_demand
    exact (lt_irrefl supply) hlt_demand

/--
Scalar clearing uniqueness from the paper's integrated-access contradiction
route.  This is the aggregate-demand form used in the Equal Cutoffs Lemma:
raising a common cutoff weakly lowers every applicant's access probability and
strictly lowers it on a positive-measure set, so the aggregate demand integral
is strictly lower.  Therefore two distinct scalar cutoffs cannot both clear
the same supply.
-/
theorem scalarClearing_unique_of_integrated_access_gap
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {access : ℝ → Applicant → ℝ} {demand : ℝ → ℝ} {supply x y : ℝ}
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x < y → ∀ a : Applicant, access y a ≤ access x a)
    (hstrict_pos :
      ∀ x y : ℝ, x < y → 0 < μ {a | access y a < access x a})
    (hx : demand x = supply) (hy : demand y = supply) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlt_integral :
        (∫ a, access y a ∂μ) < ∫ a, access x a ∂μ :=
      AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
        μ (haccess_int y) (haccess_int x) (hweak x y hlt)
        (hstrict_pos x y hlt)
    rw [← hdemand_eq y, ← hdemand_eq x, hy, hx] at hlt_integral
    exact (lt_irrefl supply) hlt_integral
  · have hlt_integral :
        (∫ a, access x a ∂μ) < ∫ a, access y a ∂μ :=
      AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
        μ (haccess_int x) (haccess_int y) (hweak y x hgt)
        (hstrict_pos y x hgt)
    rw [← hdemand_eq x, ← hdemand_eq y, hx, hy] at hlt_integral
    exact (lt_irrefl supply) hlt_integral

/--
The integrated-access comparison used in the Equal Cutoffs Lemma also gives
the strict scalar-demand monotonicity needed by coordinate-cutoff uniqueness
routes.
-/
theorem strict_antitone_demand_of_integrated_access_gap
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {access : ℝ → Applicant → ℝ} {demand : ℝ → ℝ}
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x < y → ∀ a : Applicant, access y a ≤ access x a)
    (hstrict_pos :
      ∀ x y : ℝ, x < y → 0 < μ {a | access y a < access x a}) :
    ∀ x y : ℝ, x < y → demand y < demand x := by
  intro x y hxy
  have hlt_integral :
      (∫ a, access y a ∂μ) < ∫ a, access x a ∂μ :=
    AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
      μ (haccess_int y) (haccess_int x) (hweak x y hxy)
      (hstrict_pos x y hxy)
  rw [hdemand_eq y, hdemand_eq x]
  exact hlt_integral

/--
Weak scalar-demand antitonicity from pointwise access monotonicity.  This is
the non-strict counterpart of the integrated-access strictness lemma: if a
higher cutoff weakly lowers every applicant's access probability, then the
aggregate demand curve is weakly decreasing.
-/
theorem antitone_demand_of_integrated_access_mono
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant)
    {access : ℝ → Applicant → ℝ} {demand : ℝ → ℝ}
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x ≤ y → ∀ a : Applicant, access y a ≤ access x a) :
    ∀ x y : ℝ, x ≤ y → demand y ≤ demand x := by
  intro x y hxy
  rw [hdemand_eq y, hdemand_eq x]
  exact
    MeasureTheory.integral_mono
      (haccess_int y) (haccess_int x) (hweak x y hxy)

/--
Strict access loss on a positive-measure applicant set from the source CDF
formula and a connected-support interval witness.  This is the local analytic
step in PG23 Lemma 2: for two common cutoff values `x < y`, the access formula
`1 - F(P - v)` is strictly lower at the higher cutoff on a value interval of
positive applicant measure.
-/
theorem strict_access_loss_measure_pos_of_cdf_formula_support_subinterval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {access : ℝ → ℝ → ℝ}
    {cdf valueCDF : ℝ → ℝ} {vMin vMax a b x y : ℝ}
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_cross_strict :
      ∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v))
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hmeasure_eq : μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    0 < μ {v : ℝ | access y v < access x v} := by
  let I : Set ℝ := {v : ℝ | access y v < access x v}
  have hsub : Set.Ioo a b ⊆ I := by
    intro v hv
    have hcdf := hcdf_cross_strict v hv
    have hstrict : access y v < access x v := by
      rw [hformula y v, hformula x v]
      linarith
    simpa [I] using hstrict
  have hreal : 0 < μ.real I :=
    have hstrict : valueCDF a < valueCDF b :=
      hvalue_cdf_strict ha hb hab
    have hinterval_pos : 0 < μ.real (Set.Ioo a b) := by
      rw [hmeasure_eq]
      linarith
    lt_of_lt_of_le hinterval_pos
      (measureReal_mono (μ := μ) hsub (measure_ne_top μ I))
  exact AppliedModelingLib.measure_pos_of_measureReal_pos μ I hreal

/--
Uniform strict access-loss premise for Lemma 2 from source interval witnesses.
For every pair of distinct scalar cutoffs, the source provides a subinterval
of values on which the shifted CDF is strictly ordered and whose applicant
measure is positive by the support-CDF formula.
-/
theorem strict_access_loss_measure_pos_of_cdf_formula_interval_witnesses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {access : ℝ → ℝ → ℝ}
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ x y : ℝ, x < y → 0 < μ {v : ℝ | access y v < access x v} := by
  intro x y hxy
  rcases hwitness x y hxy with
    ⟨a, b, ha, hb, hab, hcdf_cross_strict, hmeasure_eq⟩
  exact
    strict_access_loss_measure_pos_of_cdf_formula_support_subinterval
      μ hformula hcdf_cross_strict ha hb hab hvalue_cdf_strict hmeasure_eq

/--
Strict scalar-demand monotonicity derived from the paper's CDF access formula
and support-interval witnesses.  This is the demand-curve version of the
integrated-access contradiction used in Lemma 2.
-/
theorem strict_antitone_demand_of_cdf_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {access : ℝ → ℝ → ℝ} {demand : ℝ → ℝ}
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ x y : ℝ, x < y → demand y < demand x :=
  strict_antitone_demand_of_integrated_access_gap
    μ haccess_int hdemand_eq
    (by
      intro x y hxy v
      rw [hformula y v, hformula x v]
      have hcdf_le : cdf (x - v) ≤ cdf (y - v) := hcdf_mono (by linarith)
      linarith)
    (strict_access_loss_measure_pos_of_cdf_formula_interval_witnesses
      μ hformula hvalue_cdf_strict hwitness)

/--
Weak demand antitonicity from the source CDF access formula.  CDF monotonicity
alone gives the weak direction; no positive-measure strictness witness is
needed.
-/
theorem antitone_demand_of_cdf_integrated_access
    (μ : Measure ℝ)
    {access : ℝ → ℝ → ℝ} {demand : ℝ → ℝ}
    {cdf : ℝ → ℝ}
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf) :
    ∀ x y : ℝ, x ≤ y → demand y ≤ demand x :=
  antitone_demand_of_integrated_access_mono
    μ haccess_int hdemand_eq
    (by
      intro x y hxy v
      rw [hformula y v, hformula x v]
      have hcdf_le : cdf (x - v) ≤ cdf (y - v) := hcdf_mono (by linarith)
      linarith)

/--
Strict scalar-demand monotonicity for the concrete iid single-cutoff access
probability.  The shared matching library supplies the source CDF formula
`Pr[v + X > z] = 1 - F(z - v)`.
-/
theorem strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    {demand : ℝ → ℝ}
    {valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ x y : ℝ, x < y → demand y < demand x :=
  strict_antitone_demand_of_cdf_integrated_access_gap
    μ haccess_int hdemand_eq
    (by
      intro z v
      simpa using
        (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
          noiseLaw v z college))
    (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw)
    hvalue_cdf_strict hwitness

/--
Weak demand antitonicity for the concrete iid single-cutoff access
probability.  This derives the Corollary 4 monotone-demand premise from the
same matching-library CDF formula used elsewhere in the PG23 source routes.
-/
theorem antitone_demand_of_iid_single_cutoff_integrated_access
    (μ : Measure ℝ)
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    {demand : ℝ → ℝ}
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ) :
    ∀ x y : ℝ, x ≤ y → demand y ≤ demand x :=
  antitone_demand_of_cdf_integrated_access
    μ haccess_int hdemand_eq
    (by
      intro z v
      simpa using
        (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
          noiseLaw v z college))
    (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw)

/--
Scalar clearing uniqueness with the weak and strict access comparisons
derived from the paper's CDF representation.  Monotonicity of the CDF gives
pointwise weak access decline as the common cutoff increases; support-interval
witnesses give strict decline on a positive-measure applicant set.
-/
theorem scalarClearing_unique_of_cdf_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {access : ℝ → ℝ → ℝ} {demand : ℝ → ℝ} {supply x y : ℝ}
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hx : demand x = supply) (hy : demand y = supply) :
    x = y :=
  scalarClearing_unique_of_integrated_access_gap
    μ haccess_int hdemand_eq
    (by
      intro x y hxy v
      rw [hformula y v, hformula x v]
      have hcdf_le : cdf (x - v) ≤ cdf (y - v) := hcdf_mono (by linarith)
      linarith)
    (strict_access_loss_measure_pos_of_cdf_formula_interval_witnesses
      μ hformula hvalue_cdf_strict hwitness)
    hx hy

/--
PG23 Lemma 2 scalar uniqueness from the source common-cutoff demand equation.
If every constant market-clearing cutoff clears the same scalar demand equation
and that scalar demand is strictly decreasing in the common cutoff, then the
scalar cutoff value is unique.
-/
theorem lemma2_scalar_unique_of_strict_antitone_demand
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : M.Cutoff, ∀ x y : ℝ,
      M.MarketClearing P → M.MarketClearing Q →
        constantValue P x → constantValue Q y → x = y := by
  intro P Q x y hP hQ hx hy
  exact
    scalarClearing_unique_of_strict_antitone_demand
      hstrict (hclearing P x hP hx) (hclearing Q y hQ hy)

/--
PG23 Lemma 2 scalar uniqueness from the paper's integrated-access proof.  The
source proof does not need an abstract strict scalar-demand premise: it proves
strict aggregate-demand decline by integrating pointwise weak access decline
with strict decline on a positive-measure applicant set.
-/
theorem lemma2_scalar_unique_of_integrated_access_gap
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (constantValue : M.Cutoff → ℝ → Prop)
    (access : ℝ → Applicant → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x < y → ∀ a : Applicant, access y a ≤ access x a)
    (hstrict_pos :
      ∀ x y : ℝ, x < y → 0 < μ {a | access y a < access x a}) :
    ∀ P Q : M.Cutoff, ∀ x y : ℝ,
      M.MarketClearing P → M.MarketClearing Q →
        constantValue P x → constantValue Q y → x = y := by
  intro P Q x y hP hQ hx hy
  exact
    scalarClearing_unique_of_integrated_access_gap
      μ haccess_int hdemand_eq hweak hstrict_pos
      (hclearing P x hP hx) (hclearing Q y hQ hy)

/--
PG23 Lemma 2 scalar uniqueness with the integrated-access comparison derived
from the source CDF/support representation.
-/
theorem lemma2_scalar_unique_of_cdf_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (constantValue : M.Cutoff → ℝ → Prop)
    (access : ℝ → ℝ → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ P Q : M.Cutoff, ∀ x y : ℝ,
      M.MarketClearing P → M.MarketClearing Q →
        constantValue P x → constantValue Q y → x = y := by
  intro P Q x y hP hQ hx hy
  exact
    scalarClearing_unique_of_cdf_integrated_access_gap
      μ haccess_int hdemand_eq hformula hcdf_mono hvalue_cdf_strict hwitness
      (hclearing P x hP hx) (hclearing Q y hQ hy)

/--
PG23 Lemma 2 scalar uniqueness for the concrete iid single-cutoff access
probability.  The matching-library iid formula supplies
`Pr[v + X > P] = 1 - F(P - v)`; only the source support interval witnesses for
strict CDF movement remain as model-specific inputs.
-/
theorem lemma2_scalar_unique_of_iid_single_cutoff_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ P Q : M.Cutoff, ∀ x y : ℝ,
      M.MarketClearing P → M.MarketClearing Q →
        constantValue P x → constantValue Q y → x = y := by
  intro P Q x y hP hQ hx hy
  exact
    scalarClearing_unique_of_cdf_integrated_access_gap
      (μ := μ)
      (access := fun z v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => z) college)
      (demand := demand) (supply := supply)
      (cdf := AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
      (valueCDF := valueCDF) (vMin := vMin) (vMax := vMax)
      haccess_int hdemand_eq
      (by
        intro z v
        exact
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
            noiseLaw v z college)
      (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw)
      hvalue_cdf_strict hwitness
      (hclearing P x hP hx) (hclearing Q y hQ hy)

/--
Support-overlap witnesses imply the lower-CDF strictness witnesses needed by
the iid single-cutoff access route.  For `x < y`, if a whole value interval has
both shifted cutoffs `x - v` and `y - v` inside the strict noise support, then
strict monotonicity of the noise CDF gives the required pointwise CDF
inequality on that interval.
-/
theorem lowerCDFMass_interval_witnesses_of_support_interval_witnesses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hsupport_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            x - v ∈ Set.Ioo xMin xMax ∧
              y - v ∈ Set.Ioo xMin xMax) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ x y : ℝ, x < y →
      ∃ a b : ℝ,
        a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
        (∀ v ∈ Set.Ioo a b,
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
        μ.real (Set.Ioo a b) = valueCDF b - valueCDF a := by
  intro x y hxy
  rcases hsupport_witness x y hxy with
    ⟨a, b, ha, hb, hab, hshift_mem, hmeasure_eq⟩
  refine ⟨a, b, ha, hb, hab, ?_, hmeasure_eq⟩
  intro v hv
  exact hnoise_cdf_strict (hshift_mem v hv).1 (hshift_mem v hv).2 (by linarith)

/--
Lower-support witnesses imply the strict lower-CDF witnesses needed by the
paper's equal-cutoff proof.  The source interval only has to keep the lower
shifted cutoff `x - v` inside the noise support; if the higher shifted cutoff
`y - v` is outside the support to the right, the CDF endpoint value still gives
strict inequality.
-/
theorem lowerCDFMass_interval_witnesses_of_lower_support_interval_witnesses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hlower_support_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, x - v ∈ Set.Ioo xMin xMax) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ x y : ℝ, x < y →
      ∃ a b : ℝ,
        a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
        (∀ v ∈ Set.Ioo a b,
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
        μ.real (Set.Ioo a b) = valueCDF b - valueCDF a := by
  intro x y hxy
  rcases hlower_support_witness x y hxy with
    ⟨a, b, ha, hb, hab, hshift_mem, hmeasure_eq⟩
  refine ⟨a, b, ha, hb, hab, ?_, hmeasure_eq⟩
  intro v hv
  exact
    AppliedModelingLib.Probability.lowerCDFMass_lt_of_left_mem_Ioo_of_lt
      noiseLaw hnoise_cdf_strict hleft hright (hshift_mem v hv) (by linarith)

/--
A pointwise interior overlap witness generates the support-overlap interval
used by the equal-cutoff proof.  This is the paper's geometric step: if, for
two scalar cutoffs, there is an applicant value strictly inside the value
support whose two shifted noise thresholds are strictly inside the noise
support, openness gives a whole value interval with the same property; the
source value-CDF formula gives that interval positive real measure.
-/
theorem support_interval_witnesses_of_point_overlap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hpoint :
      ∀ x y : ℝ, x < y →
        ∃ v0 : ℝ,
          v0 ∈ Set.Ioo vMin vMax ∧
            x - v0 ∈ Set.Ioo xMin xMax ∧
            y - v0 ∈ Set.Ioo xMin xMax) :
    ∀ x y : ℝ, x < y →
      ∃ a b : ℝ,
        a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
        (∀ v ∈ Set.Ioo a b,
          x - v ∈ Set.Ioo xMin xMax ∧
            y - v ∈ Set.Ioo xMin xMax) ∧
        μ.real (Set.Ioo a b) = valueCDF b - valueCDF a := by
  intro x y hxy
  rcases hpoint x y hxy with ⟨v0, hv0, hxv0, hyv0⟩
  have hx_cont : ContinuousAt (fun v : ℝ => x - v) v0 :=
    continuousAt_const.sub continuousAt_id
  have hy_cont : ContinuousAt (fun v : ℝ => y - v) v0 :=
    continuousAt_const.sub continuousAt_id
  have hP :
      ∀ᶠ v in 𝓝 v0,
        v ∈ Set.Ioo vMin vMax ∧
          x - v ∈ Set.Ioo xMin xMax ∧
          y - v ∈ Set.Ioo xMin xMax := by
    filter_upwards
      [Ioo_mem_nhds hv0.1 hv0.2,
        hx_cont.eventually (Ioo_mem_nhds hxv0.1 hxv0.2),
        hy_cont.eventually (Ioo_mem_nhds hyv0.1 hyv0.2)] with v hv hxv hyv
    exact ⟨hv, hxv, hyv⟩
  rcases
    AppliedModelingLib.exists_Icc_subset_eventually_nhds
      (x := v0)
      (P := fun v : ℝ =>
        v ∈ Set.Ioo vMin vMax ∧
          x - v ∈ Set.Ioo xMin xMax ∧
          y - v ∈ Set.Ioo xMin xMax)
      hP with
    ⟨a, b, hab, _hv0ab, hsub⟩
  have haP := hsub a ⟨le_rfl, hab.le⟩
  have hbP := hsub b ⟨hab.le, le_rfl⟩
  refine ⟨a, b, haP.1, hbP.1, hab, ?_, hvalue_measure_eq a b haP.1 hbP.1 hab⟩
  intro v hv
  have hvP := hsub v ⟨hv.1.le, hv.2.le⟩
  exact ⟨hvP.2.1, hvP.2.2⟩

/--
A pointwise lower-support witness generates the source interval used in the
paper's Equal Cutoffs proof.  Only the lower shifted cutoff must lie in the
noise support; strictness for the higher cutoff is handled separately by the
CDF endpoint argument.
-/
theorem lower_support_interval_witnesses_of_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hpoint :
      ∀ x y : ℝ, x < y →
        ∃ v0 : ℝ,
          v0 ∈ Set.Ioo vMin vMax ∧ x - v0 ∈ Set.Ioo xMin xMax) :
    ∀ x y : ℝ, x < y →
      ∃ a b : ℝ,
        a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
        (∀ v ∈ Set.Ioo a b, x - v ∈ Set.Ioo xMin xMax) ∧
        μ.real (Set.Ioo a b) = valueCDF b - valueCDF a := by
  intro x y hxy
  rcases hpoint x y hxy with ⟨v0, hv0, hxv0⟩
  have hx_cont : ContinuousAt (fun v : ℝ => x - v) v0 :=
    continuousAt_const.sub continuousAt_id
  have hP :
      ∀ᶠ v in 𝓝 v0,
        v ∈ Set.Ioo vMin vMax ∧ x - v ∈ Set.Ioo xMin xMax := by
    filter_upwards
      [Ioo_mem_nhds hv0.1 hv0.2,
        hx_cont.eventually (Ioo_mem_nhds hxv0.1 hxv0.2)] with v hv hxv
    exact ⟨hv, hxv⟩
  rcases
    AppliedModelingLib.exists_Icc_subset_eventually_nhds
      (x := v0)
      (P := fun v : ℝ =>
        v ∈ Set.Ioo vMin vMax ∧ x - v ∈ Set.Ioo xMin xMax)
      hP with
    ⟨a, b, hab, _hv0ab, hsub⟩
  have haP := hsub a ⟨le_rfl, hab.le⟩
  have hbP := hsub b ⟨hab.le, le_rfl⟩
  refine ⟨a, b, haP.1, hbP.1, hab, ?_, hvalue_measure_eq a b haP.1 hbP.1 hab⟩
  intro v hv
  exact (hsub v ⟨hv.1.le, hv.2.le⟩).2

/--
Single-pair version of the lower-support interval construction.  This is
useful when the endpoint-bound proof is available only for the particular
market-clearing cutoff pair under comparison.
-/
theorem lower_support_interval_witness_of_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax x v0 : ℝ}
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hv0 : v0 ∈ Set.Ioo vMin vMax)
    (hxv0 : x - v0 ∈ Set.Ioo xMin xMax) :
    ∃ a b : ℝ,
      a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
      (∀ v ∈ Set.Ioo a b, x - v ∈ Set.Ioo xMin xMax) ∧
      μ.real (Set.Ioo a b) = valueCDF b - valueCDF a := by
  have hx_cont : ContinuousAt (fun v : ℝ => x - v) v0 :=
    continuousAt_const.sub continuousAt_id
  have hP :
      ∀ᶠ v in 𝓝 v0,
        v ∈ Set.Ioo vMin vMax ∧ x - v ∈ Set.Ioo xMin xMax := by
    filter_upwards
      [Ioo_mem_nhds hv0.1 hv0.2,
        hx_cont.eventually (Ioo_mem_nhds hxv0.1 hxv0.2)] with v hv hxv
    exact ⟨hv, hxv⟩
  rcases
    AppliedModelingLib.exists_Icc_subset_eventually_nhds
      (x := v0)
      (P := fun v : ℝ =>
        v ∈ Set.Ioo vMin vMax ∧ x - v ∈ Set.Ioo xMin xMax)
      hP with
    ⟨a, b, hab, _hv0ab, hsub⟩
  have haP := hsub a ⟨le_rfl, hab.le⟩
  have hbP := hsub b ⟨hab.le, le_rfl⟩
  refine ⟨a, b, haP.1, hbP.1, hab, ?_, hvalue_measure_eq a b haP.1 hbP.1 hab⟩
  intro v hv
  exact (hsub v ⟨hv.1.le, hv.2.le⟩).2

/--
If applicant values lie in `[vMin, vMax]` almost surely and the noise lower
CDF is zero at `xMin`, then a scalar iid single-cutoff demand is one whenever
the cutoff is at or below the lowest feasible value-plus-noise score.
-/
theorem single_cutoff_integral_eq_one_of_cutoff_le_lower_sum
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n) {P vMin vMax xMin : ℝ}
    (hvalue_support : ∀ᵐ v ∂μ, v ∈ Set.Icc vMin vMax)
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hP : P ≤ vMin + xMin) :
    (∫ v,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        v (fun _ : Fin n => P) college ∂μ) = 1 := by
  have hpoint :
      (fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => P) college) =ᶠ[ae μ]
        fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [hvalue_support] with v hv
    rw
      [AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
        noiseLaw v P college]
    have hshift : P - v ≤ xMin := by
      linarith [hv.1]
    have hcdf_le :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) ≤ 0 := by
      simpa [hleft] using
        (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw hshift)
    have hcdf_nonneg :
        0 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) :=
      AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw (P - v)
    have hcdf :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) = 0 :=
      le_antisymm hcdf_le hcdf_nonneg
    linarith
  calc
    (∫ v,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        v (fun _ : Fin n => P) college ∂μ)
        = ∫ _v : ℝ, (1 : ℝ) ∂μ :=
      integral_congr_ae hpoint
    _ = 1 := by
      simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]

/--
If applicant values lie in `[vMin, vMax]` almost surely and the noise lower
CDF is one at `xMax`, then a scalar iid single-cutoff demand is zero whenever
the cutoff is at or above the highest feasible value-plus-noise score.
-/
theorem single_cutoff_integral_eq_zero_of_upper_sum_le_cutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n) {P vMin vMax xMax : ℝ}
    (hvalue_support : ∀ᵐ v ∂μ, v ∈ Set.Icc vMin vMax)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hP : vMax + xMax ≤ P) :
    (∫ v,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        v (fun _ : Fin n => P) college ∂μ) = 0 := by
  have hpoint :
      (fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => P) college) =ᶠ[ae μ]
        fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hvalue_support] with v hv
    rw
      [AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
        noiseLaw v P college]
    have hshift : xMax ≤ P - v := by
      linarith [hv.2]
    have hcdf_ge :
        1 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) := by
      simpa [hright] using
        (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw hshift)
    have hcdf_le :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) ≤ 1 :=
      AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw (P - v)
    have hcdf :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) = 1 :=
      le_antisymm hcdf_le hcdf_ge
    linarith
  calc
    (∫ v,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        v (fun _ : Fin n => P) college ∂μ)
        = ∫ _v : ℝ, (0 : ℝ) ∂μ :=
      integral_congr_ae hpoint
    _ = 0 := by
      simp

/--
An iid single-college clearing cutoff for an interior capacity must lie strictly
between the value-plus-noise support endpoints.
-/
theorem single_cutoff_clearing_cutoff_sum_bounds_of_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n) {demand : ℝ → ℝ}
    {P capacity vMin vMax xMin xMax : ℝ}
    (hvalue_support : ∀ᵐ v ∂μ, v ∈ Set.Icc vMin vMax)
    (hcapacity_pos : 0 < capacity)
    (hcapacity_lt_one : capacity < 1)
    (hclear : demand P = capacity)
    (hdemand_eq :
      demand P =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => P) college ∂μ)
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1) :
    vMin + xMin < P ∧ P < vMax + xMax := by
  constructor
  · by_contra hnot
    have hP : P ≤ vMin + xMin := le_of_not_gt hnot
    have htail :
        (∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => P) college ∂μ) = 1 :=
      single_cutoff_integral_eq_one_of_cutoff_le_lower_sum
        μ noiseLaw college hvalue_support hleft hP
    have hcapacity_eq : capacity = 1 := by
      rw [← hclear, hdemand_eq]
      exact htail
    linarith
  · by_contra hnot
    have hP : vMax + xMax ≤ P := le_of_not_gt hnot
    have htail :
        (∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => P) college ∂μ) = 0 :=
      single_cutoff_integral_eq_zero_of_upper_sum_le_cutoff
        μ noiseLaw college hvalue_support hright hP
    have hcapacity_eq : capacity = 0 := by
      rw [← hclear, hdemand_eq]
      exact htail
    linarith

/--
The all-college iid crossing probability is one below the lower feasible
value-plus-noise endpoint.
-/
theorem cutoff_crossing_integral_eq_one_of_cutoff_le_lower_sum
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {P vMin vMax xMin : ℝ}
    (hvalue_support : ∀ᵐ v ∂μ, v ∈ Set.Icc vMin vMax)
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hP : P ≤ vMin + xMin) :
    (∫ v,
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ) = 1 := by
  have hpoint :
      (fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v (fun _ => P)) =ᶠ[ae μ]
        fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [hvalue_support] with v hv
    rw
      [AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow
        noiseLaw v P]
    have hshift : P - v ≤ xMin := by
      linarith [hv.1]
    have hcdf_le :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) ≤ 0 := by
      simpa [hleft] using
        (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw hshift)
    have hcdf_nonneg :
        0 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) :=
      AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw (P - v)
    have hcdf :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) = 0 :=
      le_antisymm hcdf_le hcdf_nonneg
    have hn : n ≠ 0 := NeZero.ne n
    simp [hcdf, hn]
  calc
    (∫ v,
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ)
        = ∫ _v : ℝ, (1 : ℝ) ∂μ :=
      integral_congr_ae hpoint
    _ = 1 := by
      simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]

/--
The all-college iid crossing probability is zero above the upper feasible
value-plus-noise endpoint.
-/
theorem cutoff_crossing_integral_eq_zero_of_upper_sum_le_cutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {P vMin vMax xMax : ℝ}
    (hvalue_support : ∀ᵐ v ∂μ, v ∈ Set.Icc vMin vMax)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hP : vMax + xMax ≤ P) :
    (∫ v,
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ) = 0 := by
  have hpoint :
      (fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v (fun _ => P)) =ᶠ[ae μ]
        fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hvalue_support] with v hv
    rw
      [AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow
        noiseLaw v P]
    have hshift : xMax ≤ P - v := by
      linarith [hv.2]
    have hcdf_ge :
        1 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) := by
      simpa [hright] using
        (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw hshift)
    have hcdf_le :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) ≤ 1 :=
      AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw (P - v)
    have hcdf :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) = 1 :=
      le_antisymm hcdf_le hcdf_ge
    simp [hcdf]
  calc
    (∫ v,
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ)
        = ∫ _v : ℝ, (0 : ℝ) ∂μ :=
      integral_congr_ae hpoint
    _ = 0 := by
      simp

/--
An all-college iid clearing cutoff for an interior capacity must lie strictly
between the value-plus-noise support endpoints.
-/
theorem cutoff_crossing_clearing_cutoff_sum_bounds_of_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {P capacity vMin vMax xMin xMax : ℝ}
    (hvalue_support : ∀ᵐ v ∂μ, v ∈ Set.Icc vMin vMax)
    (hcapacity_pos : 0 < capacity)
    (hcapacity_lt_one : capacity < 1)
    (hclear :
      (∫ v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ) =
        capacity)
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1) :
    vMin + xMin < P ∧ P < vMax + xMax := by
  constructor
  · by_contra hnot
    have hP : P ≤ vMin + xMin := le_of_not_gt hnot
    have htail :
        (∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ) = 1 :=
      cutoff_crossing_integral_eq_one_of_cutoff_le_lower_sum
        μ noiseLaw hvalue_support hleft hP
    have hcapacity_eq : capacity = 1 := by
      rw [← hclear]
      exact htail
    linarith
  · by_contra hnot
    have hP : vMax + xMax ≤ P := le_of_not_gt hnot
    have htail :
        (∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            (Finset.univ : Finset (Fin n)) v (fun _ => P) ∂μ) = 0 :=
      cutoff_crossing_integral_eq_zero_of_upper_sum_le_cutoff
        μ noiseLaw hvalue_support hright hP
    have hcapacity_eq : capacity = 0 := by
      rw [← hclear]
      exact htail
    linarith

/--
If a scalar cutoff lies between the smallest and largest feasible
value-plus-noise scores, then the paper's lower-support interval is nonempty:
there is an interior applicant value whose shifted lower cutoff is inside the
noise support.
-/
theorem exists_lower_support_point_of_sum_bounds
    {vMin vMax xMin xMax x : ℝ}
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hlower : vMin + xMin < x)
    (hupper : x < vMax + xMax) :
    ∃ v0 : ℝ,
      v0 ∈ Set.Ioo vMin vMax ∧ x - v0 ∈ Set.Ioo xMin xMax := by
  let lo : ℝ := max vMin (x - xMax)
  let hi : ℝ := min vMax (x - xMin)
  have hvMin_lt_hi : vMin < hi := by
    dsimp [hi]
    exact lt_min hvalue_nonempty (by linarith)
  have hxLower_lt_hi : x - xMax < hi := by
    dsimp [hi]
    exact lt_min (by linarith) (by linarith)
  have hlo_lt_hi : lo < hi := by
    dsimp [lo]
    exact max_lt hvMin_lt_hi hxLower_lt_hi
  rcases exists_between hlo_lt_hi with ⟨v0, hlo, hhi⟩
  refine ⟨v0, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt (le_max_left vMin (x - xMax)) hlo
  · exact lt_of_lt_of_le hhi (min_le_left vMax (x - xMin))
  · have hv0_lt_upper : v0 < x - xMin :=
      lt_of_lt_of_le hhi (min_le_right vMax (x - xMin))
    linarith
  · have hxLower_lt_v0 : x - xMax < v0 :=
      lt_of_le_of_lt (le_max_right vMin (x - xMax)) hlo
    linarith

/--
The paper's endpoint cutoff bounds produce the pointwise lower-support witness
used in the Equal Cutoffs proof.
-/
theorem lower_support_point_of_cutoff_sum_bounds
    {vMin vMax xMin xMax : ℝ}
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_bounds :
      ∀ x y : ℝ, x < y → vMin + xMin < x ∧ x < vMax + xMax) :
    ∀ x y : ℝ, x < y →
      ∃ v0 : ℝ,
        v0 ∈ Set.Ioo vMin vMax ∧ x - v0 ∈ Set.Ioo xMin xMax := by
  intro x y hxy
  rcases hcutoff_bounds x y hxy with ⟨hlower, hupper⟩
  exact
    exists_lower_support_point_of_sum_bounds hvalue_nonempty hnoise_nonempty
      hlower hupper

/--
Strict scalar-demand monotonicity for the concrete iid single-cutoff access
probability, with the support witness derived from primitive source support
bounds.  This removes the separate `hcommon_witness` premise in top-level
Theorem 1/2 routes: the lower-support interval is constructed from the
value/noise support endpoints, then converted to the CDF strictness witness.
-/
theorem strict_antitone_demand_of_iid_single_cutoff_lower_support_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    {demand : ℝ → ℝ}
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_bounds :
      ∀ x y : ℝ, x < y → vMin + xMin < x ∧ x < vMax + xMax) :
    ∀ x y : ℝ, x < y → demand y < demand x := by
  exact
    strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
      (μ := μ) (noiseLaw := noiseLaw) (college := college)
      (demand := demand) (valueCDF := valueCDF)
      (vMin := vMin) (vMax := vMax)
      haccess_int hdemand_eq hvalue_cdf_strict
      (lowerCDFMass_interval_witnesses_of_lower_support_interval_witnesses
        μ noiseLaw hnoise_cdf_strict hleft hright
        (lower_support_interval_witnesses_of_point
          μ hvalue_measure_eq
          (lower_support_point_of_cutoff_sum_bounds
            hvalue_nonempty hnoise_nonempty hcutoff_bounds)))

/--
Single-pair strict access loss from a lower-support point.  The lower shifted
cutoff lies inside the noise support, while the higher shifted cutoff is
handled by the upper endpoint value of the noise CDF.
-/
theorem strict_access_loss_measure_pos_of_lower_support_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {access : ℝ → ℝ → ℝ}
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax x y v0 : ℝ}
    (hformula :
      ∀ z v : ℝ,
        access z v =
          1 - AppliedModelingLib.Probability.lowerCDFMass noiseLaw (z - v))
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hxy : x < y)
    (hv0 : v0 ∈ Set.Ioo vMin vMax)
    (hxv0 : x - v0 ∈ Set.Ioo xMin xMax) :
    0 < μ {v : ℝ | access y v < access x v} := by
  rcases
    lower_support_interval_witness_of_point
      μ hvalue_measure_eq hv0 hxv0 with
    ⟨a, b, ha, hb, hab, hshift_mem, hmeasure_eq⟩
  exact
    strict_access_loss_measure_pos_of_cdf_formula_support_subinterval
      μ hformula
      (by
        intro v hv
        exact
          AppliedModelingLib.Probability.lowerCDFMass_lt_of_left_mem_Ioo_of_lt
            noiseLaw hnoise_cdf_strict hleft hright (hshift_mem v hv)
            (by linarith))
      ha hb hab hvalue_cdf_strict hmeasure_eq

/--
Pairwise strict scalar-demand decrease for concrete iid single-cutoff access,
derived from primitive support bounds on the lower cutoff.  This is the local
version needed for actual clearing-cutoff pairs: it avoids assuming the demand
curve is strictly decreasing on cutoff values outside the source support.
-/
theorem iid_single_cutoff_demand_lt_of_lower_support_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    {demand : ℝ → ℝ}
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax x y : ℝ}
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hxy : x < y)
    (hcutoff_bounds : vMin + xMin < x ∧ x < vMax + xMax) :
    demand y < demand x := by
  rcases
    exists_lower_support_point_of_sum_bounds
      hvalue_nonempty hnoise_nonempty hcutoff_bounds.1 hcutoff_bounds.2 with
    ⟨v0, hv0, hxv0⟩
  have hweak :
      ∀ v : ℝ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => y) college ≤
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => x) college := by
    intro v
    rw
      [AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
        noiseLaw v y college,
       AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
        noiseLaw v x college]
    have hcdf_le :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) ≤
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v) :=
      AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw (by linarith)
    linarith
  have hstrict_pos :
      0 <
        μ {v : ℝ |
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => y) college <
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => x) college} :=
    strict_access_loss_measure_pos_of_lower_support_point
      (μ := μ) (noiseLaw := noiseLaw)
      (access := fun z v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => z) college)
      (valueCDF := valueCDF) (vMin := vMin) (vMax := vMax)
      (xMin := xMin) (xMax := xMax) (x := x) (y := y) (v0 := v0)
      (by
        intro z v
        exact
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
            noiseLaw v z college)
      hvalue_cdf_strict hnoise_cdf_strict hleft hright
      hvalue_measure_eq hxy hv0 hxv0
  rw [hdemand_eq y, hdemand_eq x]
  exact
    AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
      μ (haccess_int y) (haccess_int x) hweak hstrict_pos

/--
PG23 Lemma 2 from the source scalar-demand route: symmetry gives constant
cutoffs, market clearing becomes a scalar demand equation, strict decrease of
that demand equation gives scalar uniqueness, and extensionality turns equal
scalars into equal cutoff vectors.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_strict_antitone_demand
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_constant_scalar_unique
    M L constantValue hconstant
    (lemma2_scalar_unique_of_strict_antitone_demand
      M constantValue demand supply hclearing hstrict)
    hconstant_ext

/--
PG23 Lemma 2 from the paper's integrated-access route.  Symmetry gives
constant market-clearing cutoff vectors; the common scalar clearing equation
is represented as an applicant-access integral; weak monotonicity in the
cutoff plus strict loss on a positive-measure set gives uniqueness of the
common scalar cutoff.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_integrated_access_gap
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (access : ℝ → Applicant → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x < y → ∀ a : Applicant, access y a ≤ access x a)
    (hstrict_pos :
      ∀ x y : ℝ, x < y → 0 < μ {a | access y a < access x a})
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_constant_scalar_unique
    M L constantValue hconstant
    (lemma2_scalar_unique_of_integrated_access_gap
      M μ constantValue access demand supply hclearing haccess_int
      hdemand_eq hweak hstrict_pos)
    hconstant_ext

/--
PG23 Lemma 2 from the CDF/support version of the paper's integrated-access
route.  This removes the abstract weak/strict access comparison premises from
the equal-cutoff theorem surface.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_cdf_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (access : ℝ → ℝ → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_constant_scalar_unique
    M L constantValue hconstant
    (lemma2_scalar_unique_of_cdf_integrated_access_gap
      M μ constantValue access demand supply hclearing haccess_int
      hdemand_eq hformula hcdf_mono hvalue_cdf_strict hwitness)
    hconstant_ext

/--
PG23 Lemma 2 from the concrete iid single-cutoff access route.  This derives
the CDF access formula from the shared matching library and then applies the
integrated support-interval argument.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_constant_scalar_unique
    M L constantValue hconstant
    (lemma2_scalar_unique_of_iid_single_cutoff_integrated_access_gap
      M μ noiseLaw college constantValue demand supply hclearing
      haccess_int hdemand_eq hvalue_cdf_strict hwitness)
    hconstant_ext

/--
PG23 Lemma 2 from concrete iid single-cutoff access and paper-style
support-overlap witnesses.  Strict lower-CDF movement is derived internally
from strict CDF monotonicity on the noise support.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_support_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hsupport_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            x - v ∈ Set.Ioo xMin xMax ∧
              y - v ∈ Set.Ioo xMin xMax) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_integrated_access_gap
    M μ noiseLaw college L constantValue demand supply hconstant hclearing
    haccess_int hdemand_eq hvalue_cdf_strict
    (lowerCDFMass_interval_witnesses_of_support_interval_witnesses
      μ noiseLaw hnoise_cdf_strict hsupport_witness)
    hconstant_ext

/--
PG23 Lemma 2 from concrete iid single-cutoff access and pointwise support
overlap.  Lean turns the pointwise overlap into a positive-measure interval,
then derives strict lower-CDF movement from noise-CDF monotonicity.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_support_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hpoint :
      ∀ x y : ℝ, x < y →
        ∃ v0 : ℝ,
          v0 ∈ Set.Ioo vMin vMax ∧
            x - v0 ∈ Set.Ioo xMin xMax ∧
            y - v0 ∈ Set.Ioo xMin xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_support_interval
    M μ noiseLaw college L constantValue demand supply hconstant hclearing
    haccess_int hdemand_eq hvalue_cdf_strict hnoise_cdf_strict
    (support_interval_witnesses_of_point_overlap μ hvalue_measure_eq hpoint)
    hconstant_ext

/--
PG23 Lemma 2 from concrete iid single-cutoff access and the paper's
lower-support interval.  This is closer to the written proof than the
support-overlap route: the interval only keeps `P_- - v` inside `(X_-, X_+)`.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_lower_support_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hlower_support_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, x - v ∈ Set.Ioo xMin xMax) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_integrated_access_gap
    M μ noiseLaw college L constantValue demand supply hconstant hclearing
    haccess_int hdemand_eq hvalue_cdf_strict
    (lowerCDFMass_interval_witnesses_of_lower_support_interval_witnesses
      μ noiseLaw hnoise_cdf_strict hleft hright hlower_support_witness)
    hconstant_ext

/--
PG23 Lemma 2 from concrete iid single-cutoff access and a pointwise lower
support witness.  Openness turns the point into the positive interval used in
the paper's proof.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_lower_support_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hpoint :
      ∀ x y : ℝ, x < y →
        ∃ v0 : ℝ,
          v0 ∈ Set.Ioo vMin vMax ∧ x - v0 ∈ Set.Ioo xMin xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_lower_support_interval
    M μ noiseLaw college L constantValue demand supply hconstant hclearing
    haccess_int hdemand_eq hvalue_cdf_strict hnoise_cdf_strict hleft hright
    (lower_support_interval_witnesses_of_point μ hvalue_measure_eq hpoint)
    hconstant_ext

/--
PG23 Lemma 2 from concrete iid single-cutoff access and the source endpoint
cutoff bounds.  The bounds `V_- + X_- < x < V_+ + X_+` generate the
lower-support point used by the written proof's interval
`(x - X_+, x - X_-)`.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_lower_support_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hconstant :
      ∀ P : M.Cutoff, M.MarketClearing P → ∃ x : ℝ, constantValue P x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_bounds :
      ∀ x y : ℝ, x < y → vMin + xMin < x ∧ x < vMax + xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_iid_single_cutoff_lower_support_point
    M μ noiseLaw college L constantValue demand supply hconstant hclearing
    haccess_int hdemand_eq hvalue_cdf_strict hnoise_cdf_strict hleft hright
    hvalue_measure_eq
    (lower_support_point_of_cutoff_sum_bounds hvalue_nonempty hnoise_nonempty
      hcutoff_bounds)
    hconstant_ext

/--
PG23 Lemma 2 from the source extrema route.  The paper only needs the least
and greatest market-clearing cutoffs to be constant by symmetry; strict
decrease of the scalar clearing equation then identifies those two extrema,
and the A-L lattice theorem gives uniqueness of all market-clearing cutoffs.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_constant_strict_antitone_demand
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide M L (by
    intro bot top hbot htop
    rcases hleast_constant bot hbot with ⟨x, hx⟩
    rcases hgreatest_constant top htop with ⟨y, hy⟩
    have hxy : x = y :=
      scalarClearing_unique_of_strict_antitone_demand
        hstrict (hclearing bot x hbot.1 hx) (hclearing top y htop.1 hy)
    exact hconstant_ext bot top x hx (by simpa [hxy] using hy))

/--
PG23 Lemma 2 from the paper's extrema/integral route.  This is closer to the
written proof of the Equal Cutoffs Lemma: A-L supplies least and greatest
clearing cutoffs, symmetry makes those extrema constant, and the integrated
access comparison rules out distinct common cutoff values.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_integrated_access_gap
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (access : ℝ → Applicant → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x < y → ∀ a : Applicant, access y a ≤ access x a)
    (hstrict_pos :
      ∀ x y : ℝ, x < y → 0 < μ {a | access y a < access x a})
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide M L (by
    intro bot top hbot htop
    rcases hleast_constant bot hbot with ⟨x, hx⟩
    rcases hgreatest_constant top htop with ⟨y, hy⟩
    have hxy : x = y :=
      scalarClearing_unique_of_integrated_access_gap
        μ haccess_int hdemand_eq hweak hstrict_pos
        (hclearing bot x hbot.1 hx) (hclearing top y htop.1 hy)
    exact hconstant_ext bot top x hx (by simpa [hxy] using hy))

/--
PG23 Lemma 2 from the closest source route with the CDF/support access
comparison derived internally.  A-L supplies least and greatest clearing
cutoffs, symmetry makes those two cutoffs constant, and the CDF/support
integral argument identifies their scalar values.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_cdf_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (access : ℝ → ℝ → ℝ)
    (demand : ℝ → ℝ) (supply : ℝ)
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide M L (by
    intro bot top hbot htop
    rcases hleast_constant bot hbot with ⟨x, hx⟩
    rcases hgreatest_constant top htop with ⟨y, hy⟩
    have hxy : x = y :=
      scalarClearing_unique_of_cdf_integrated_access_gap
        μ haccess_int hdemand_eq hformula hcdf_mono hvalue_cdf_strict hwitness
        (hclearing bot x hbot.1 hx) (hclearing top y htop.1 hy)
    exact hconstant_ext bot top x hx (by simpa [hxy] using hy))

/--
PG23 Lemma 2 from the extrema route and concrete iid single-cutoff access.
This is the tightest current source-shaped route: A-L gives extrema, symmetry
makes them constant, and iid cutoff crossing plus support witnesses rule out
two distinct scalar clearing values.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_integrated_access_gap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide M L (by
    intro bot top hbot htop
    rcases hleast_constant bot hbot with ⟨x, hx⟩
    rcases hgreatest_constant top htop with ⟨y, hy⟩
    have hxy : x = y :=
      scalarClearing_unique_of_cdf_integrated_access_gap
        (μ := μ)
        (access := fun z v =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => z) college)
        (demand := demand) (supply := supply)
        (cdf := AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (valueCDF := valueCDF) (vMin := vMin) (vMax := vMax)
        haccess_int hdemand_eq
        (by
          intro z v
          exact
            AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
              noiseLaw v z college)
        (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw)
        hvalue_cdf_strict hwitness
        (hclearing bot x hbot.1 hx) (hclearing top y htop.1 hy)
    exact hconstant_ext bot top x hx (by simpa [hxy] using hy))

/--
PG23 Lemma 2 from extrema, iid single-cutoff access, and paper-style
support-overlap witnesses.  This is the closest current theorem to the written
Equal Cutoffs proof using an iid noise support interval.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_support_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hsupport_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            x - v ∈ Set.Ioo xMin xMax ∧
              y - v ∈ Set.Ioo xMin xMax) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_integrated_access_gap
    M μ noiseLaw college L constantValue demand supply hleast_constant
    hgreatest_constant hclearing haccess_int hdemand_eq hvalue_cdf_strict
    (lowerCDFMass_interval_witnesses_of_support_interval_witnesses
      μ noiseLaw hnoise_cdf_strict hsupport_witness)
    hconstant_ext

/--
PG23 Lemma 2 from extrema, iid single-cutoff access, and pointwise support
overlap.  This is the tightest current source-shaped route for the Equal
Cutoffs proof.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_support_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hpoint :
      ∀ x y : ℝ, x < y →
        ∃ v0 : ℝ,
          v0 ∈ Set.Ioo vMin vMax ∧
            x - v0 ∈ Set.Ioo xMin xMax ∧
            y - v0 ∈ Set.Ioo xMin xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_support_interval
    M μ noiseLaw college L constantValue demand supply hleast_constant
    hgreatest_constant hclearing haccess_int hdemand_eq hvalue_cdf_strict
    hnoise_cdf_strict
    (support_interval_witnesses_of_point_overlap μ hvalue_measure_eq hpoint)
    hconstant_ext

/--
PG23 Lemma 2 from extrema, iid single-cutoff access, and the paper's lower
support interval.  A-L supplies extrema; the strict aggregate contradiction
uses the interval where the lower cutoff shift lies inside the noise support.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_lower_support_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hlower_support_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, x - v ∈ Set.Ioo xMin xMax) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_integrated_access_gap
    M μ noiseLaw college L constantValue demand supply hleast_constant
    hgreatest_constant hclearing haccess_int hdemand_eq hvalue_cdf_strict
    (lowerCDFMass_interval_witnesses_of_lower_support_interval_witnesses
      μ noiseLaw hnoise_cdf_strict hleft hright hlower_support_witness)
    hconstant_ext

/--
PG23 Lemma 2 from extrema, iid single-cutoff access, and a pointwise lower
support witness.  This matches the source's use of the interval
`(P_- - X_+, P_- - X_-)` after proving it intersects the value support.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_lower_support_point
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hpoint :
      ∀ x y : ℝ, x < y →
        ∃ v0 : ℝ,
          v0 ∈ Set.Ioo vMin vMax ∧ x - v0 ∈ Set.Ioo xMin xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_lower_support_interval
    M μ noiseLaw college L constantValue demand supply hleast_constant
    hgreatest_constant hclearing haccess_int hdemand_eq hvalue_cdf_strict
    hnoise_cdf_strict hleft hright
    (lower_support_interval_witnesses_of_point μ hvalue_measure_eq hpoint)
    hconstant_ext

/--
PG23 Lemma 2 from extrema, iid single-cutoff access, and the source endpoint
cutoff bounds.  This removes the point-overlap premise by deriving the
intersection of `(x - X_+, x - X_-)` with the value support from
`V_- + X_- < x < V_+ + X_+`.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_lower_support_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_bounds :
      ∀ x y : ℝ, x < y → vMin + xMin < x ∧ x < vMax + xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_lower_support_point
    M μ noiseLaw college L constantValue demand supply hleast_constant
    hgreatest_constant hclearing haccess_int hdemand_eq hvalue_cdf_strict
    hnoise_cdf_strict hleft hright hvalue_measure_eq
    (lower_support_point_of_cutoff_sum_bounds hvalue_nonempty hnoise_nonempty
      hcutoff_bounds)
    hconstant_ext

/--
PG23 Lemma 2 from extrema, iid single-cutoff access, and source endpoint
bounds for the actual constant market-clearing cutoffs.  This is the closest
Lean route to the written proof: after A-L supplies least/greatest clearing
cutoffs and symmetry makes them constant, the lower cutoff's score bounds
produce the interval `(P_- - X_+, P_- - X_-)` used in the strict aggregate
demand contradiction.
-/
theorem lemma2_unique_marketClearing_cutoff_of_lattice_extrema_iid_single_cutoff_clearing_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (constantValue : M.Cutoff → ℝ → Prop)
    (demand : ℝ → ℝ) (supply : ℝ)
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hleast_constant :
      ∀ bot : M.Cutoff,
        (M.MarketClearing bot ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P) →
        ∃ x : ℝ, constantValue bot x)
    (hgreatest_constant :
      ∀ top : M.Cutoff,
        (M.MarketClearing top ∧
          ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top) →
        ∃ x : ℝ, constantValue top x)
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_bounds :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → constantValue P x →
          vMin + xMin < x ∧ x < vMax + xMax)
    (hconstant_ext :
      ∀ P Q : M.Cutoff, ∀ x : ℝ,
        constantValue P x → constantValue Q x → P = Q) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_lattice_extrema_coincide M L (by
    intro bot top hbot htop
    rcases hleast_constant bot hbot with ⟨x, hx⟩
    rcases hgreatest_constant top htop with ⟨y, hy⟩
    have hformula :
        ∀ z v : ℝ,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college =
            1 - AppliedModelingLib.Probability.lowerCDFMass noiseLaw (z - v) := by
      intro z v
      exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
          noiseLaw v z college
    have hxy : x = y := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hweak :
            ∀ v : ℝ,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => y) college ≤
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => x) college := by
          intro v
          rw [hformula y v, hformula x v]
          have hcdf_le :
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) ≤
                AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v) :=
            AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw (by linarith)
          linarith
        rcases
          exists_lower_support_point_of_sum_bounds hvalue_nonempty
            hnoise_nonempty (hcutoff_bounds bot x hbot.1 hx).1
            (hcutoff_bounds bot x hbot.1 hx).2 with
          ⟨v0, hv0, hxv0⟩
        have hstrict_pos :
            0 <
              μ {v : ℝ |
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                    (Measure.pi (fun _ : Fin n => noiseLaw))
                    v (fun _ : Fin n => y) college <
                  AppliedModelingLib.Matching.singleCutoffCrossingProbability
                    (Measure.pi (fun _ : Fin n => noiseLaw))
                    v (fun _ : Fin n => x) college} :=
          strict_access_loss_measure_pos_of_lower_support_point
            (μ := μ) (noiseLaw := noiseLaw)
            (access := fun z v =>
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => z) college)
            hformula hvalue_cdf_strict hnoise_cdf_strict hleft hright
            hvalue_measure_eq hlt hv0 hxv0
        have hlt_integral :
            (∫ v,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => y) college ∂μ) <
              ∫ v,
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => x) college ∂μ :=
          AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
            μ (haccess_int y) (haccess_int x) hweak hstrict_pos
        rw [← hdemand_eq y, ← hdemand_eq x,
          hclearing top y htop.1 hy, hclearing bot x hbot.1 hx] at hlt_integral
        exact (lt_irrefl supply) hlt_integral
      · have hweak :
            ∀ v : ℝ,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => x) college ≤
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => y) college := by
          intro v
          rw [hformula x v, hformula y v]
          have hcdf_le :
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v) ≤
                AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) :=
            AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw (by linarith)
          linarith
        rcases
          exists_lower_support_point_of_sum_bounds hvalue_nonempty
            hnoise_nonempty (hcutoff_bounds top y htop.1 hy).1
            (hcutoff_bounds top y htop.1 hy).2 with
          ⟨v0, hv0, hyv0⟩
        have hstrict_pos :
            0 <
              μ {v : ℝ |
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                    (Measure.pi (fun _ : Fin n => noiseLaw))
                    v (fun _ : Fin n => x) college <
                  AppliedModelingLib.Matching.singleCutoffCrossingProbability
                    (Measure.pi (fun _ : Fin n => noiseLaw))
                    v (fun _ : Fin n => y) college} :=
          strict_access_loss_measure_pos_of_lower_support_point
            (μ := μ) (noiseLaw := noiseLaw)
            (access := fun z v =>
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => z) college)
            hformula hvalue_cdf_strict hnoise_cdf_strict hleft hright
            hvalue_measure_eq hgt hv0 hyv0
        have hlt_integral :
            (∫ v,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => x) college ∂μ) <
              ∫ v,
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => y) college ∂μ :=
          AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
            μ (haccess_int x) (haccess_int y) hweak hstrict_pos
        rw [← hdemand_eq x, ← hdemand_eq y,
          hclearing bot x hbot.1 hx, hclearing top y htop.1 hy] at hlt_integral
        exact (lt_irrefl supply) hlt_integral
    exact hconstant_ext bot top x hx (by simpa [hxy] using hy))

/--
Coordinatewise symmetry step in PG23 Lemma 2.  If the market-clearing set of
real cutoff vectors is closed under coordinate swaps, then its coordinatewise
least and greatest elements have constant coordinates.
-/
theorem lemma2_extrema_constantCoordinates_of_coordinatewise_symmetry
    {College : Type v} [DecidableEq College]
    {marketClearing : (College → ℝ) → Prop}
    {bot top : College → ℝ}
    (hbot :
      marketClearing bot ∧
        ∀ P : College → ℝ, marketClearing P → CoordinatewiseLe bot P)
    (htop :
      marketClearing top ∧
        ∀ P : College → ℝ, marketClearing P → CoordinatewiseLe P top)
    (hswap :
      ∀ P : College → ℝ, marketClearing P → ∀ c d : College,
        marketClearing (coordinateSwap P c d)) :
    ConstantCoordinates bot ∧ ConstantCoordinates top :=
  constantCoordinates_of_coordinatewise_extrema_swap_closed
    (Z := {P : College → ℝ | marketClearing P})
    hbot.1 htop.1 hbot.2 htop.2 hswap

/--
PG23 Lemma 2 coordinate-cutoff route.  For a concrete cutoff-vector market,
the A-L lattice theorem supplies coordinatewise least and greatest
market-clearing cutoffs; permutation symmetry makes the extrema constant; and
strict decrease of the scalar clearing equation makes the two constants equal,
so every market-clearing cutoff vector is unique.
-/
theorem lemma2_unique_coordinate_marketClearing_cutoff_of_symmetry_strict_antitone_demand
    {College : Type v} [DecidableEq College]
    {marketClearing : (College → ℝ) → Prop}
    {bot top : College → ℝ}
    {demand : ℝ → ℝ} {supply : ℝ}
    (hbot :
      marketClearing bot ∧
        ∀ P : College → ℝ, marketClearing P → CoordinatewiseLe bot P)
    (htop :
      marketClearing top ∧
        ∀ P : College → ℝ, marketClearing P → CoordinatewiseLe P top)
    (hswap :
      ∀ P : College → ℝ, marketClearing P → ∀ c d : College,
        marketClearing (coordinateSwap P c d))
    (hclearing :
      ∀ P : College → ℝ, ∀ x : ℝ,
        marketClearing P → (∀ c, P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : College → ℝ, marketClearing P → marketClearing Q → P = Q :=
  unique_coordinatewise_cutoff_of_swap_closed_strict_antitone_scalar_clearing
    (Z := {P : College → ℝ | marketClearing P})
    hbot.1 htop.1 hbot.2 htop.2 hswap hclearing hstrict

/--
PG23 Lemma 2 coordinate-cutoff route directly from the A-L lattice surface.
The complete lattice supplies the least and greatest market-clearing cutoffs;
the paper-specific symmetry and strict scalar clearing arguments then make the
clearing cutoff vector unique.
-/
theorem lemma2_unique_coordinate_marketClearing_cutoff_of_complete_lattice_symmetry_strict_antitone_demand
    {College : Type v} [DecidableEq College]
    {marketClearing : (College → ℝ) → Prop}
    {demand : ℝ → ℝ} {supply : ℝ}
    (hne : ∃ P : College → ℝ, marketClearing P)
    (L : CompleteLatticeOn marketClearing CoordinatewiseLe)
    (hswap :
      ∀ P : College → ℝ, marketClearing P → ∀ c d : College,
        marketClearing (coordinateSwap P c d))
    (hclearing :
      ∀ P : College → ℝ, ∀ x : ℝ,
        marketClearing P → (∀ c, P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : College → ℝ, marketClearing P → marketClearing Q → P = Q :=
  unique_coordinatewise_cutoff_of_complete_lattice_swap_closed_strict_antitone_scalar_clearing
    hne L hswap hclearing hstrict

/--
PG23 Lemma 2 route from an A-L cutoff lattice plus an explicit coordinate
representation.  This is the source-model version of the equal-cutoff proof:
the A-L lattice provides extrema for the abstract cutoff objects, `coord`
turns those cutoffs into real vectors, source symmetry gives coordinate-swap
closure, and strict scalar clearing identifies the constant extrema.
-/
theorem lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_strict_antitone_demand
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {demand : ℝ → ℝ} {supply : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  L.unique_marketClearing_of_coordinate_symmetry_strict_antitone_scalar_clearing
    coord hcoord_ext horder hswap hclearing hstrict

/--
PG23 Lemma 2 coordinate-cutoff route with the paper's integrated-access
strictness argument exposed directly.  This removes the abstract
`strict scalar demand` premise from the coordinate source-model route: pointwise
weak access monotonicity plus positive-measure strict access loss gives the
strict scalar clearing equation internally.
-/
theorem lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_integrated_access_gap
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {access : ℝ → Applicant → ℝ} {demand : ℝ → ℝ} {supply : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ a, access z a ∂μ)
    (hweak :
      ∀ x y : ℝ, x < y → ∀ a : Applicant, access y a ≤ access x a)
    (hstrict_pos :
      ∀ x y : ℝ, x < y → 0 < μ {a | access y a < access x a}) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_strict_antitone_demand
    M L coord hcoord_ext horder hswap hclearing
    (strict_antitone_demand_of_integrated_access_gap
      μ haccess_int hdemand_eq hweak hstrict_pos)

/--
PG23 Lemma 2 coordinate-cutoff route with strict scalar clearing derived from
the source CDF/support representation.  This specializes the integrated-access
coordinate route to the access formula `1 - F(z - v)` used in the paper.
-/
theorem lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_cdf_integrated_access_gap
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {access : ℝ → ℝ → ℝ} {demand : ℝ → ℝ} {supply : ℝ}
    {cdf valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (haccess_int : ∀ z : ℝ, Integrable (access z) μ)
    (hdemand_eq :
      ∀ z : ℝ, demand z = ∫ v, access z v ∂μ)
    (hformula : ∀ z v, access z v = 1 - cdf (z - v))
    (hcdf_mono : Monotone cdf)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b, cdf (x - v) < cdf (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_strict_antitone_demand
    M L coord hcoord_ext horder hswap hclearing
    (strict_antitone_demand_of_cdf_integrated_access_gap
      μ haccess_int hdemand_eq hformula hcdf_mono hvalue_cdf_strict
      hwitness)

/--
PG23 Lemma 2 coordinate-cutoff route with the concrete iid single-cutoff
access formula.  This is the coordinate version closest to the paper model:
A-L supplies cutoff extrema, symmetry makes them scalar, and the iid
single-cutoff access formula plus support witnesses give strict scalar
clearing.
-/
theorem lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_iid_single_cutoff_integrated_access_gap
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {demand : ℝ → ℝ} {supply : ℝ}
    {valueCDF : ℝ → ℝ} {vMin vMax : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hwitness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v)) ∧
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_strict_antitone_demand
    M L coord hcoord_ext horder hswap hclearing
    (strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
      μ noiseLaw college haccess_int hdemand_eq hvalue_cdf_strict hwitness)

/--
PG23 Lemma 2 coordinate-cutoff route with the paper's lower-support endpoint
bounds kept at the actual clearing cutoffs.  This avoids exposing separate
premises saying that the A-L least and greatest cutoffs are constant: the
coordinate lattice and swap-closure proof derive those constants internally,
then the endpoint support argument identifies their scalar values.
-/
theorem lemma2_unique_marketClearing_cutoff_of_cutoff_lattice_coordinate_symmetry_iid_single_cutoff_clearing_bounds
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (college : Fin n)
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {demand : ℝ → ℝ} {supply : ℝ}
    {valueCDF : ℝ → ℝ} {vMin vMax xMin xMax : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (haccess_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college) μ)
    (hdemand_eq :
      ∀ z : ℝ,
        demand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college ∂μ)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          μ.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_bounds :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) →
          vMin + xMin < x ∧ x < vMax + xMax) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q := by
  classical
  let bot : M.Cutoff := L.leastMarketClearingCutoff
  let top : M.Cutoff := L.greatestMarketClearingCutoff
  have hbot_mc : M.MarketClearing bot := by
    simpa [bot] using L.leastMarketClearingCutoff_marketClearing
  have htop_mc : M.MarketClearing top := by
    simpa [top] using L.greatestMarketClearingCutoff_marketClearing
  have hleast :
      ∀ P : M.Cutoff, M.MarketClearing P →
        L.leCutoff bot P := by
    intro P hP
    simpa [bot] using L.leastMarketClearingCutoff_le hP
  have hgreatest :
      ∀ P : M.Cutoff, M.MarketClearing P →
        L.leCutoff P top := by
    intro P hP
    simpa [top] using L.le_greatestMarketClearingCutoff hP
  let Z : Set (CollegeCoord → ℝ) :=
    {R | ∃ P : M.Cutoff, M.MarketClearing P ∧ coord P = R}
  have hbotZ : coord bot ∈ Z := ⟨bot, hbot_mc, rfl⟩
  have htopZ : coord top ∈ Z := ⟨top, htop_mc, rfl⟩
  have hleast_coord :
      ∀ R : CollegeCoord → ℝ, R ∈ Z →
        CoordinatewiseLe (coord bot) R := by
    intro R hR
    rcases hR with ⟨P, hP, rfl⟩
    exact horder bot P (hleast P hP)
  have hgreatest_coord :
      ∀ R : CollegeCoord → ℝ, R ∈ Z →
        CoordinatewiseLe R (coord top) := by
    intro R hR
    rcases hR with ⟨P, hP, rfl⟩
    exact horder P top (hgreatest P hP)
  have hswap_coord :
      ∀ R : CollegeCoord → ℝ, R ∈ Z → ∀ c d : CollegeCoord,
        coordinateSwap R c d ∈ Z := by
    intro R hR c d
    rcases hR with ⟨P, hP, rfl⟩
    rcases hswap P hP c d with ⟨Q, hQ, hcoordQ⟩
    exact ⟨Q, hQ, hcoordQ⟩
  have hconst :
      ConstantCoordinates (coord bot) ∧ ConstantCoordinates (coord top) :=
    constantCoordinates_of_coordinatewise_extrema_swap_closed
      (Z := Z) hbotZ htopZ hleast_coord hgreatest_coord hswap_coord
  rcases hconst.1 with ⟨x, hx⟩
  rcases hconst.2 with ⟨y, hy⟩
  have hformula :
      ∀ z v : ℝ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            v (fun _ : Fin n => z) college =
          1 - AppliedModelingLib.Probability.lowerCDFMass noiseLaw (z - v) := by
    intro z v
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass
        noiseLaw v z college
  have hxy : x = y := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hweak :
          ∀ v : ℝ,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => y) college ≤
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => x) college := by
        intro v
        rw [hformula y v, hformula x v]
        have hcdf_le :
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) ≤
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v) :=
          AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw (by linarith)
        linarith
      rcases
        exists_lower_support_point_of_sum_bounds hvalue_nonempty
          hnoise_nonempty (hcutoff_bounds bot x hbot_mc hx).1
          (hcutoff_bounds bot x hbot_mc hx).2 with
        ⟨v0, hv0, hxv0⟩
      have hstrict_pos :
          0 <
            μ {v : ℝ |
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => y) college <
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => x) college} :=
        strict_access_loss_measure_pos_of_lower_support_point
          (μ := μ) (noiseLaw := noiseLaw)
          (access := fun z v =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college)
          hformula hvalue_cdf_strict hnoise_cdf_strict hleft hright
          hvalue_measure_eq hlt hv0 hxv0
      have hlt_integral :
          (∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => y) college ∂μ) <
            ∫ v,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => x) college ∂μ :=
        AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
          μ (haccess_int y) (haccess_int x) hweak hstrict_pos
      rw [← hdemand_eq y, ← hdemand_eq x,
        hclearing top y htop_mc hy, hclearing bot x hbot_mc hx] at hlt_integral
      exact (lt_irrefl supply) hlt_integral
    · have hweak :
          ∀ v : ℝ,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => x) college ≤
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => y) college := by
        intro v
        rw [hformula x v, hformula y v]
        have hcdf_le :
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (y - v) ≤
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw (x - v) :=
          AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw (by linarith)
        linarith
      rcases
        exists_lower_support_point_of_sum_bounds hvalue_nonempty
          hnoise_nonempty (hcutoff_bounds top y htop_mc hy).1
          (hcutoff_bounds top y htop_mc hy).2 with
        ⟨v0, hv0, hyv0⟩
      have hstrict_pos :
          0 <
            μ {v : ℝ |
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => x) college <
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin n => noiseLaw))
                  v (fun _ : Fin n => y) college} :=
        strict_access_loss_measure_pos_of_lower_support_point
          (μ := μ) (noiseLaw := noiseLaw)
          (access := fun z v =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => z) college)
          hformula hvalue_cdf_strict hnoise_cdf_strict hleft hright
          hvalue_measure_eq hgt hv0 hyv0
      have hlt_integral :
          (∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              v (fun _ : Fin n => x) college ∂μ) <
            ∫ v,
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                v (fun _ : Fin n => y) college ∂μ :=
        AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
          μ (haccess_int x) (haccess_int y) hweak hstrict_pos
      rw [← hdemand_eq x, ← hdemand_eq y,
        hclearing bot x hbot_mc hx, hclearing top y htop_mc hy] at hlt_integral
      exact (lt_irrefl supply) hlt_integral
  have hbot_top_coord : coord bot = coord top := by
    funext c
    rw [hx c, hy c, hxy]
  have hbot_top : bot = top := hcoord_ext bot top hbot_top_coord
  intro P Q hP hQ
  have hP_coord : coord P = coord bot := by
    funext c
    have hbot_le_P : coord bot c ≤ coord P c :=
      horder bot P (hleast P hP) c
    have hP_le_bot : coord P c ≤ coord bot c := by
      have hP_le_top : coord P c ≤ coord top c :=
        horder P top (hgreatest P hP) c
      simpa [hbot_top] using hP_le_top
    exact le_antisymm hP_le_bot hbot_le_P
  have hQ_coord : coord Q = coord bot := by
    funext c
    have hbot_le_Q : coord bot c ≤ coord Q c :=
      horder bot Q (hleast Q hQ) c
    have hQ_le_bot : coord Q c ≤ coord bot c := by
      have hQ_le_top : coord Q c ≤ coord top c :=
        horder Q top (hgreatest Q hQ) c
      simpa [hbot_top] using hQ_le_top
    exact le_antisymm hQ_le_bot hbot_le_Q
  exact (hcoord_ext P bot hP_coord).trans (hcoord_ext Q bot hQ_coord).symm

/--
PG23 Corollary 4 cutoff comparison, scalar aggregate route.  If monoculture
and polyculture clear the same supply, monoculture demand is weakly decreasing
in the common cutoff, and at the polyculture cutoff the polyculture demand is
strictly larger than monoculture demand, then the monoculture clearing cutoff
must be strictly below the polyculture clearing cutoff.
-/
theorem corollary4_mono_cutoff_lt_poly_cutoff_of_same_supply
    {monoDemand polyDemand : ℝ → ℝ} {Pmono Ppoly supply : ℝ}
    (hmono_clear : monoDemand Pmono = supply)
    (hpoly_clear : polyDemand Ppoly = supply)
    (hmono_antitone : ∀ a b : ℝ, a ≤ b → monoDemand b ≤ monoDemand a)
    (hstrict_at_poly : monoDemand Ppoly < polyDemand Ppoly) :
    Pmono < Ppoly := by
  by_contra hnot
  have hge : Ppoly ≤ Pmono := le_of_not_gt hnot
  have hmono_le : monoDemand Pmono ≤ monoDemand Ppoly :=
    hmono_antitone Ppoly Pmono hge
  have hstrict : monoDemand Pmono < polyDemand Ppoly :=
    lt_of_le_of_lt hmono_le hstrict_at_poly
  rw [hmono_clear, hpoly_clear] at hstrict
  exact (lt_irrefl supply) hstrict

/--
PG23 Corollary 4 non-strict cutoff comparison.  If the monoculture demand
curve is strictly decreasing, both regimes clear the same supply, and at the
polyculture cutoff monoculture demand is weakly below polyculture demand, then
the monoculture cutoff is weakly below the polyculture cutoff.
-/
theorem corollary4_mono_cutoff_le_poly_cutoff_of_same_supply_strict_mono
    {monoDemand polyDemand : ℝ → ℝ} {Pmono Ppoly supply : ℝ}
    (hmono_clear : monoDemand Pmono = supply)
    (hpoly_clear : polyDemand Ppoly = supply)
    (hmono_strict : ∀ a b : ℝ, a < b → monoDemand b < monoDemand a)
    (hweak_at_poly : monoDemand Ppoly ≤ polyDemand Ppoly) :
    Pmono ≤ Ppoly := by
  by_contra hnot
  have hlt : Ppoly < Pmono := lt_of_not_ge hnot
  have hstrict : monoDemand Pmono < monoDemand Ppoly :=
    hmono_strict Ppoly Pmono hlt
  have hweak_supply : monoDemand Ppoly ≤ supply := by
    simpa [hpoly_clear] using hweak_at_poly
  have hstrict_supply : supply < monoDemand Ppoly := by
    simpa [hmono_clear] using hstrict
  exact (not_lt_of_ge hweak_supply) hstrict_supply

/--
PG23 Corollary 4 non-strict cutoff comparison with only the local strictness
needed for the actual clearing cutoffs.  This is the source-shaped form used
when strict demand decrease is derived from support bounds only at the
candidate polyculture/monoculture cutoff pair.
-/
theorem corollary4_mono_cutoff_le_poly_cutoff_of_same_supply_pair_strict
    {monoDemand polyDemand : ℝ → ℝ} {Pmono Ppoly supply : ℝ}
    (hmono_clear : monoDemand Pmono = supply)
    (hpoly_clear : polyDemand Ppoly = supply)
    (hmono_pair_strict :
      Ppoly < Pmono → monoDemand Pmono < monoDemand Ppoly)
    (hweak_at_poly : monoDemand Ppoly ≤ polyDemand Ppoly) :
    Pmono ≤ Ppoly := by
  by_contra hnot
  have hlt : Ppoly < Pmono := lt_of_not_ge hnot
  have hstrict : monoDemand Pmono < monoDemand Ppoly :=
    hmono_pair_strict hlt
  have hweak_supply : monoDemand Ppoly ≤ supply := by
    simpa [hpoly_clear] using hweak_at_poly
  have hstrict_supply : supply < monoDemand Ppoly := by
    simpa [hmono_clear] using hstrict
  exact (not_lt_of_ge hweak_supply) hstrict_supply

/--
PG23 aggregate-demand strict gap from pointwise access.  If demand at a fixed
cutoff is the integral of applicant access probabilities, polyculture access
weakly dominates monoculture access for every applicant, and the dominance is
strict on a positive-measure set, then the aggregate polyculture demand is
strictly larger at that cutoff.
-/
theorem corollary4_strict_demand_gap_of_pointwise_access
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {monoDemandAtCutoff polyDemandAtCutoff : ℝ}
    {monoAccess polyAccess : Applicant → ℝ}
    (hmono_int : Integrable monoAccess μ)
    (hpoly_int : Integrable polyAccess μ)
    (hmono_eq : monoDemandAtCutoff = ∫ a, monoAccess a ∂μ)
    (hpoly_eq : polyDemandAtCutoff = ∫ a, polyAccess a ∂μ)
    (hle : ∀ a, monoAccess a ≤ polyAccess a)
    (hstrict_pos : 0 < μ {a | monoAccess a < polyAccess a}) :
    monoDemandAtCutoff < polyDemandAtCutoff := by
  rw [hmono_eq, hpoly_eq]
  exact
    AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
      μ hmono_int hpoly_int hle hstrict_pos

/--
PG23 aggregate-demand weak gap from pointwise access.  This is the
non-strict counterpart used when Theorem 2 only needs the weak cutoff
comparison for top-choice dominance.
-/
theorem corollary4_weak_demand_gap_of_pointwise_access
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant)
    {monoDemandAtCutoff polyDemandAtCutoff : ℝ}
    {monoAccess polyAccess : Applicant → ℝ}
    (hmono_int : Integrable monoAccess μ)
    (hpoly_int : Integrable polyAccess μ)
    (hmono_eq : monoDemandAtCutoff = ∫ a, monoAccess a ∂μ)
    (hpoly_eq : polyDemandAtCutoff = ∫ a, polyAccess a ∂μ)
    (hle : ∀ a, monoAccess a ≤ polyAccess a) :
    monoDemandAtCutoff ≤ polyDemandAtCutoff := by
  rw [hmono_eq, hpoly_eq]
  exact MeasureTheory.integral_mono hmono_int hpoly_int hle

/--
PG23 Corollary 4 from the integrated source access comparison.  This is the
source route used in Theorem 2: the strict demand gap at the polyculture
cutoff is derived from pointwise weak improvement and strict improvement on a
positive-measure applicant set, then the scalar cutoff comparison follows.
-/
theorem corollary4_mono_cutoff_lt_poly_cutoff_of_integrated_access_gap
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {monoDemand polyDemand : ℝ → ℝ} {Pmono Ppoly supply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : Applicant → ℝ}
    (hmono_clear : monoDemand Pmono = supply)
    (hpoly_clear : polyDemand Ppoly = supply)
    (hmono_antitone : ∀ a b : ℝ, a ≤ b → monoDemand b ≤ monoDemand a)
    (hmono_int : Integrable monoAccessAtPoly μ)
    (hpoly_int : Integrable polyAccessAtPoly μ)
    (hmono_eq :
      monoDemand Ppoly = ∫ a, monoAccessAtPoly a ∂μ)
    (hpoly_eq :
      polyDemand Ppoly = ∫ a, polyAccessAtPoly a ∂μ)
    (hle : ∀ a, monoAccessAtPoly a ≤ polyAccessAtPoly a)
    (hstrict_pos :
      0 < μ {a | monoAccessAtPoly a < polyAccessAtPoly a}) :
    Pmono < Ppoly :=
  corollary4_mono_cutoff_lt_poly_cutoff_of_same_supply
    hmono_clear hpoly_clear hmono_antitone
    (corollary4_strict_demand_gap_of_pointwise_access
      μ hmono_int hpoly_int hmono_eq hpoly_eq hle hstrict_pos)

/--
PG23 Corollary 4 from the weak integrated source access comparison.  This is
the route Theorem 2 needs for top-choice dominance: pointwise weak access
dominance gives a weak aggregate demand gap at the polyculture cutoff, and
strict monotonicity of the monoculture demand curve turns that into
`P_mono <= P_poly`.
-/
theorem corollary4_mono_cutoff_le_poly_cutoff_of_integrated_weak_access_strict_mono
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant)
    {monoDemand polyDemand : ℝ → ℝ} {Pmono Ppoly supply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : Applicant → ℝ}
    (hmono_clear : monoDemand Pmono = supply)
    (hpoly_clear : polyDemand Ppoly = supply)
    (hmono_strict : ∀ a b : ℝ, a < b → monoDemand b < monoDemand a)
    (hmono_int : Integrable monoAccessAtPoly μ)
    (hpoly_int : Integrable polyAccessAtPoly μ)
    (hmono_eq :
      monoDemand Ppoly = ∫ a, monoAccessAtPoly a ∂μ)
    (hpoly_eq :
      polyDemand Ppoly = ∫ a, polyAccessAtPoly a ∂μ)
    (hle : ∀ a, monoAccessAtPoly a ≤ polyAccessAtPoly a) :
    Pmono ≤ Ppoly :=
  corollary4_mono_cutoff_le_poly_cutoff_of_same_supply_strict_mono
    hmono_clear hpoly_clear hmono_strict
    (corollary4_weak_demand_gap_of_pointwise_access
      μ hmono_int hpoly_int hmono_eq hpoly_eq hle)

/--
PG23 Corollary 4 from weak integrated access with only local strictness at
the actual cutoff pair.  This avoids exposing a global strict-demand premise
when support arguments prove strictness only for the cutoffs used by the
market-clearing comparison.
-/
theorem corollary4_mono_cutoff_le_poly_cutoff_of_integrated_weak_access_pair_strict
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant)
    {monoDemand polyDemand : ℝ → ℝ} {Pmono Ppoly supply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : Applicant → ℝ}
    (hmono_clear : monoDemand Pmono = supply)
    (hpoly_clear : polyDemand Ppoly = supply)
    (hmono_pair_strict :
      Ppoly < Pmono → monoDemand Pmono < monoDemand Ppoly)
    (hmono_int : Integrable monoAccessAtPoly μ)
    (hpoly_int : Integrable polyAccessAtPoly μ)
    (hmono_eq :
      monoDemand Ppoly = ∫ a, monoAccessAtPoly a ∂μ)
    (hpoly_eq :
      polyDemand Ppoly = ∫ a, polyAccessAtPoly a ∂μ)
    (hle : ∀ a, monoAccessAtPoly a ≤ polyAccessAtPoly a) :
    Pmono ≤ Ppoly :=
  corollary4_mono_cutoff_le_poly_cutoff_of_same_supply_pair_strict
    hmono_clear hpoly_clear hmono_pair_strict
    (corollary4_weak_demand_gap_of_pointwise_access
      μ hmono_int hpoly_int hmono_eq hpoly_eq hle)

/-- No feasible application-set deviation gives higher ex-ante payoff. -/
def NoProfitableApplicationDeviation {College : Type v}
    (payoff : Finset College → ℝ) (topChoiceSet : Finset College)
    (feasible : Finset College → Prop) : Prop :=
  ∀ deviation : Finset College,
    feasible deviation → payoff deviation ≤ payoff topChoiceSet

/--
Finite ex-ante application payoff under a shared equal-cutoff success chance.
When all colleges have the same cutoff, each applied college contributes the
same nonnegative chance factor times the applicant's utility for that college.
-/
def equalCutoffApplicationPayoff {College : Type v}
    (commonSuccessChance : ℝ) (utility : College → ℝ)
    (applicationSet : Finset College) : ℝ :=
  commonSuccessChance * ∑ c ∈ applicationSet, utility c

/--
Per-college success probabilities collapse to the shared equal-cutoff payoff
when the applied colleges all have the same success chance.
-/
theorem applicationPayoffByCollegeChance_eq_equalCutoffApplicationPayoff
    {College : Type v} [DecidableEq College]
    (successChance utility : College → ℝ) (commonSuccessChance : ℝ)
    (applicationSet : Finset College)
    (hcommon :
      ∀ c : College, c ∈ applicationSet →
        successChance c = commonSuccessChance) :
    (∑ c ∈ applicationSet, successChance c * utility c) =
      equalCutoffApplicationPayoff commonSuccessChance utility applicationSet := by
  classical
  unfold equalCutoffApplicationPayoff
  calc
    (∑ c ∈ applicationSet, successChance c * utility c) =
        ∑ c ∈ applicationSet, commonSuccessChance * utility c := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      rw [hcommon c hc]
    _ = commonSuccessChance * ∑ c ∈ applicationSet, utility c := by
      rw [Finset.mul_sum]

/--
PG23 Proposition 6, finite application-strategy route.  Once equal cutoffs
make the ex-ante payoff of any feasible same-size application set equal to the
sum of firm utilities in that set, applying to the top `k` firms has no
profitable deviation.
-/
theorem proposition6_nashEquilibrium_of_equal_cutoff_payoff_sum
    {College : Type v} [DecidableEq College]
    {topChoiceSet : Finset College} {feasible : Finset College → Prop}
    {payoff : Finset College → ℝ} {utility : College → ℝ}
    (hfeasible_card :
      ∀ deviation : Finset College,
        feasible deviation → deviation.card = topChoiceSet.card)
    (hpayoff_sum :
      ∀ deviation : Finset College,
        feasible deviation → payoff deviation = ∑ c ∈ deviation, utility c)
    (htop_payoff_sum :
      payoff topChoiceSet = ∑ c ∈ topChoiceSet, utility c)
    (htop :
      ∀ c ∈ topChoiceSet, ∀ d, d ∉ topChoiceSet → utility d ≤ utility c) :
    NoProfitableApplicationDeviation payoff topChoiceSet feasible := by
  intro deviation hdeviation
  rw [hpayoff_sum deviation hdeviation, htop_payoff_sum]
  exact
    AppliedModelingLib.Matching.applicationUtility_sum_le_topSet_sum
      (hfeasible_card deviation hdeviation) htop

/--
PG23 Proposition 6, finite equal-cutoff route with explicit ex-ante payoff
semantics.  If equal cutoffs make every applied college contribute the same
nonnegative success chance, then among same-size feasible application sets the
top-`k` set weakly maximizes ex-ante payoff.
-/
theorem proposition6_nashEquilibrium_of_equal_cutoff_common_success_chance
    {College : Type v} [DecidableEq College]
    {topChoiceSet : Finset College} {feasible : Finset College → Prop}
    {commonSuccessChance : ℝ} {utility : College → ℝ}
    (hchance_nonneg : 0 ≤ commonSuccessChance)
    (hfeasible_card :
      ∀ deviation : Finset College,
        feasible deviation → deviation.card = topChoiceSet.card)
    (htop :
      ∀ c ∈ topChoiceSet, ∀ d, d ∉ topChoiceSet → utility d ≤ utility c) :
    NoProfitableApplicationDeviation
      (equalCutoffApplicationPayoff commonSuccessChance utility)
      topChoiceSet feasible := by
  intro deviation hdeviation
  unfold equalCutoffApplicationPayoff
  exact
    mul_le_mul_of_nonneg_left
      (AppliedModelingLib.Matching.applicationUtility_sum_le_topSet_sum
        (hfeasible_card deviation hdeviation) htop)
      hchance_nonneg

/--
Utility from the applicant's favorite successful applied college, with an
outside-option value when no applied college succeeds.  This is the finite
payoff shape behind the differential-access Nash sentence: success outcomes
are realized after the ex-ante application set is chosen.
-/
noncomputable def favoriteSuccessfulApplicationUtility {College : Type v}
    [DecidableEq College] (outsideUtility : ℝ) (utility : College → ℝ)
    (applicationSet successful : Finset College) : ℝ :=
  if h : (applicationSet ∩ successful).Nonempty then
    (applicationSet ∩ successful).sup' h utility
  else
    outsideUtility

/--
Given a deviation and the top-choice set, map successful deviation-only
applications to the corresponding missing top-choice applications, while
leaving successful common applications fixed.  The equivalence argument is the
explicit equal-cardinality coupling used by the favorite-success payoff proof.
-/
def mappedSuccessfulApplicationsByTopDifference {College : Type v}
    [DecidableEq College] (deviation topChoiceSet : Finset College)
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    (successful : Finset College) : Finset College :=
  ((deviation ∩ topChoiceSet) ∩ successful) ∪
    (((deviation \ topChoiceSet) ∩ successful).attach.image
      (fun d : {c // c ∈ (deviation \ topChoiceSet) ∩ successful} =>
        (e ⟨d.1, (Finset.mem_inter.mp d.2).1⟩).1))

/--
The mapped success set lies inside the top-choice application set.
-/
theorem mappedSuccessfulApplicationsByTopDifference_subset_top
    {College : Type v} [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    (successful : Finset College) :
    mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful ⊆
      topChoiceSet := by
  classical
  intro c hc
  rw [mappedSuccessfulApplicationsByTopDifference] at hc
  rcases Finset.mem_union.mp hc with hc_common | hc_image
  · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hc_common).1).2
  · rcases Finset.mem_image.mp hc_image with ⟨d, _hd, rfl⟩
    exact (Finset.mem_sdiff.mp (e ⟨d.1, (Finset.mem_inter.mp d.2).1⟩).2).1

/--
The finite permutation that swaps deviation-only colleges with the paired
missing top-choice colleges and fixes all other colleges.
-/
def topDifferenceSwapFun {College : Type v} [DecidableEq College]
    (deviation topChoiceSet : Finset College)
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    (c : College) : College :=
  if hdev : c ∈ deviation \ topChoiceSet then
    (e ⟨c, hdev⟩).1
  else if htop : c ∈ topChoiceSet \ deviation then
    (e.symm ⟨c, htop⟩).1
  else
    c

theorem topDifferenceSwapFun_apply_left
    {College : Type v} [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    {c : College} (hc : c ∈ deviation \ topChoiceSet) :
    topDifferenceSwapFun deviation topChoiceSet e c = (e ⟨c, hc⟩).1 := by
  simp [topDifferenceSwapFun, hc]

theorem topDifferenceSwapFun_apply_right
    {College : Type v} [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    {c : College} (hc : c ∈ topChoiceSet \ deviation) :
    topDifferenceSwapFun deviation topChoiceSet e c = (e.symm ⟨c, hc⟩).1 := by
  have hnot_dev : c ∉ deviation \ topChoiceSet := by
    intro hdev
    exact (Finset.mem_sdiff.mp hdev).2 (Finset.mem_sdiff.mp hc).1
  simp [topDifferenceSwapFun, hnot_dev, hc]

theorem topDifferenceSwapFun_apply_fixed
    {College : Type v} [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    {c : College}
    (hdev : c ∉ deviation \ topChoiceSet)
    (htop : c ∉ topChoiceSet \ deviation) :
    topDifferenceSwapFun deviation topChoiceSet e c = c := by
  simp [topDifferenceSwapFun, hdev, htop]

theorem topDifferenceSwapFun_involutive
    {College : Type v} [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    (c : College) :
    topDifferenceSwapFun deviation topChoiceSet e
        (topDifferenceSwapFun deviation topChoiceSet e c) = c := by
  classical
  by_cases hdev : c ∈ deviation \ topChoiceSet
  · have htop_image : (e ⟨c, hdev⟩).1 ∈ topChoiceSet \ deviation :=
      (e ⟨c, hdev⟩).2
    have hnot_dev_image : (e ⟨c, hdev⟩).1 ∉ deviation \ topChoiceSet := by
      intro hbad
      exact (Finset.mem_sdiff.mp hbad).2 (Finset.mem_sdiff.mp htop_image).1
    calc
      topDifferenceSwapFun deviation topChoiceSet e
          (topDifferenceSwapFun deviation topChoiceSet e c) =
          topDifferenceSwapFun deviation topChoiceSet e (e ⟨c, hdev⟩).1 := by
        rw [topDifferenceSwapFun_apply_left e hdev]
      _ = (e.symm ⟨(e ⟨c, hdev⟩).1, htop_image⟩).1 := by
        simp [topDifferenceSwapFun, hnot_dev_image, htop_image]
      _ = c := by
        simpa using congrArg Subtype.val (e.symm_apply_apply ⟨c, hdev⟩)
  · by_cases htop : c ∈ topChoiceSet \ deviation
    · have hdev_image : (e.symm ⟨c, htop⟩).1 ∈ deviation \ topChoiceSet :=
        (e.symm ⟨c, htop⟩).2
      calc
        topDifferenceSwapFun deviation topChoiceSet e
            (topDifferenceSwapFun deviation topChoiceSet e c) =
            topDifferenceSwapFun deviation topChoiceSet e (e.symm ⟨c, htop⟩).1 := by
          rw [topDifferenceSwapFun_apply_right e htop]
        _ = (e ⟨(e.symm ⟨c, htop⟩).1, hdev_image⟩).1 := by
          simp [topDifferenceSwapFun, hdev_image]
        _ = c := by
          simpa using congrArg Subtype.val (e.apply_symm_apply ⟨c, htop⟩)
    · simp [topDifferenceSwapFun_apply_fixed e hdev htop]

/-- The swap permutation induced by a deviation/top-choice difference pairing. -/
def topDifferenceSwap {College : Type v} [DecidableEq College]
    (deviation topChoiceSet : Finset College)
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation}) : Equiv.Perm College where
  toFun := topDifferenceSwapFun deviation topChoiceSet e
  invFun := topDifferenceSwapFun deviation topChoiceSet e
  left_inv := topDifferenceSwapFun_involutive e
  right_inv := topDifferenceSwapFun_involutive e

/--
The mapped successful top-choice set is the top-choice part of the success set
after the difference-swap reindexing.
-/
theorem mappedSuccessfulApplicationsByTopDifference_filter_eq_top_filter_swap
    {College : Type v} [Fintype College] [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    (outcome : College → Bool) :
    mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e
        ((Finset.univ : Finset College).filter fun c => outcome c = true) =
      topChoiceSet ∩
        ((Finset.univ : Finset College).filter fun c =>
          outcome ((topDifferenceSwap deviation topChoiceSet e).symm c) = true) := by
  classical
  ext c
  constructor
  · intro hc
    have hc_top :
        c ∈ topChoiceSet :=
      mappedSuccessfulApplicationsByTopDifference_subset_top e _ hc
    rw [Finset.mem_inter]
    refine ⟨hc_top, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    rw [mappedSuccessfulApplicationsByTopDifference] at hc
    rcases Finset.mem_union.mp hc with hc_common | hc_image
    · have hc_common_pair :
          c ∈ deviation ∩ topChoiceSet :=
        (Finset.mem_inter.mp hc_common).1
      have hc_success :
          c ∈ (Finset.univ : Finset College).filter fun c => outcome c = true :=
        (Finset.mem_inter.mp hc_common).2
      have hout : outcome c = true :=
        (Finset.mem_filter.mp hc_success).2
      have hnot_dev : c ∉ deviation \ topChoiceSet := by
        intro hbad
        exact (Finset.mem_sdiff.mp hbad).2 (Finset.mem_inter.mp hc_common_pair).2
      have hnot_top : c ∉ topChoiceSet \ deviation := by
        intro hbad
        exact (Finset.mem_sdiff.mp hbad).2 (Finset.mem_inter.mp hc_common_pair).1
      have hsymm :
          (topDifferenceSwap deviation topChoiceSet e).symm c = c := by
        change topDifferenceSwapFun deviation topChoiceSet e c = c
        exact topDifferenceSwapFun_apply_fixed e hnot_dev hnot_top
      simpa [hsymm] using hout
    · rcases Finset.mem_image.mp hc_image with ⟨d, _hd, rfl⟩
      let ddiff : {x // x ∈ deviation \ topChoiceSet} :=
        ⟨d.1, (Finset.mem_inter.mp d.2).1⟩
      have hd_success :
          d.1 ∈ (Finset.univ : Finset College).filter fun c => outcome c = true :=
        (Finset.mem_inter.mp d.2).2
      have hout : outcome d.1 = true :=
        (Finset.mem_filter.mp hd_success).2
      have htop_image : (e ddiff).1 ∈ topChoiceSet \ deviation :=
        (e ddiff).2
      have hsymm :
          (topDifferenceSwap deviation topChoiceSet e).symm (e ddiff).1 = d.1 := by
        change topDifferenceSwapFun deviation topChoiceSet e (e ddiff).1 = d.1
        calc
          topDifferenceSwapFun deviation topChoiceSet e (e ddiff).1 =
              (e.symm ⟨(e ddiff).1, htop_image⟩).1 := by
            exact topDifferenceSwapFun_apply_right e htop_image
          _ = d.1 := by
            simpa [ddiff] using congrArg Subtype.val (e.symm_apply_apply ddiff)
      simpa [ddiff, hsymm] using hout
  · intro hc
    have hc_top : c ∈ topChoiceSet := (Finset.mem_inter.mp hc).1
    have hc_success :
        c ∈ (Finset.univ : Finset College).filter fun c =>
          outcome ((topDifferenceSwap deviation topChoiceSet e).symm c) = true :=
      (Finset.mem_inter.mp hc).2
    have hout :
        outcome ((topDifferenceSwap deviation topChoiceSet e).symm c) = true :=
      (Finset.mem_filter.mp hc_success).2
    by_cases hc_dev : c ∈ deviation
    · have hnot_devdiff : c ∉ deviation \ topChoiceSet := by
        intro hbad
        exact (Finset.mem_sdiff.mp hbad).2 hc_top
      have hnot_topdiff : c ∉ topChoiceSet \ deviation := by
        intro hbad
        exact (Finset.mem_sdiff.mp hbad).2 hc_dev
      have hsymm :
          (topDifferenceSwap deviation topChoiceSet e).symm c = c := by
        change topDifferenceSwapFun deviation topChoiceSet e c = c
        exact topDifferenceSwapFun_apply_fixed e hnot_devdiff hnot_topdiff
      have hout_c : outcome c = true := by
        simpa [hsymm] using hout
      rw [mappedSuccessfulApplicationsByTopDifference]
      refine Finset.mem_union_left _ ?_
      rw [Finset.mem_inter, Finset.mem_inter]
      exact ⟨⟨hc_dev, hc_top⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ c, hout_c⟩⟩
    · have htopdiff : c ∈ topChoiceSet \ deviation :=
        Finset.mem_sdiff.mpr ⟨hc_top, hc_dev⟩
      let ctop : {x // x ∈ topChoiceSet \ deviation} := ⟨c, htopdiff⟩
      let ddiff : {x // x ∈ deviation \ topChoiceSet} := e.symm ctop
      have hsymm :
          (topDifferenceSwap deviation topChoiceSet e).symm c = ddiff.1 := by
        change topDifferenceSwapFun deviation topChoiceSet e c = ddiff.1
        exact topDifferenceSwapFun_apply_right e htopdiff
      have hout_d : outcome ddiff.1 = true := by
        simpa [hsymm] using hout
      rw [mappedSuccessfulApplicationsByTopDifference]
      refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ?_
      refine ⟨⟨ddiff.1, ?_⟩, by simp, ?_⟩
      · rw [Finset.mem_inter]
        exact ⟨ddiff.2,
          Finset.mem_filter.mpr ⟨Finset.mem_univ ddiff.1, hout_d⟩⟩
      · simpa [ctop, ddiff] using congrArg Subtype.val (e.apply_symm_apply ctop)

/-- Favorite-success utility only depends on successes inside the application set. -/
theorem favoriteSuccessfulApplicationUtility_inter_success
    {College : Type v} [DecidableEq College]
    (outsideUtility : ℝ) (utility : College → ℝ)
    (applicationSet successful : Finset College) :
    favoriteSuccessfulApplicationUtility outsideUtility utility applicationSet
        (applicationSet ∩ successful) =
      favoriteSuccessfulApplicationUtility outsideUtility utility applicationSet successful := by
  classical
  unfold favoriteSuccessfulApplicationUtility
  have hinter :
      applicationSet ∩ (applicationSet ∩ successful) =
        applicationSet ∩ successful := by
    ext c
    constructor
    · intro hc
      exact (Finset.mem_inter.mp hc).2
    · intro hc
      rw [Finset.mem_inter]
      exact ⟨(Finset.mem_inter.mp hc).1, hc⟩
  simp [hinter]

/--
Expected favorite-success payoff under a finite law over success sets.
-/
noncomputable def expectedFavoriteSuccessfulApplicationUtility
    {College : Type v} [Fintype College] [DecidableEq College]
    (successLaw : PMF (Finset College)) (outsideUtility : ℝ)
    (utility : College → ℝ) (applicationSet : Finset College) : ℝ :=
  AppliedModelingLib.pmfExp successLaw
    (fun successful =>
      favoriteSuccessfulApplicationUtility outsideUtility utility applicationSet successful)

/--
Iid equal-cutoff success law: every college has an independent identically
distributed success indicator.  The application set is an argument only so this
law can inhabit the same interface as strategy-dependent success laws; equal
cutoffs make the indicator law application-set invariant.
-/
noncomputable def iidEqualCutoffSuccessLaw {College : Type v}
    [Fintype College] [DecidableEq College]
    (successAtom : PMF Bool) (_applicationSet : Finset College) :
    PMF (Finset College) :=
  (AppliedModelingLib.pmfProduct College Bool successAtom).map
    (fun outcome : College → Bool =>
      (Finset.univ : Finset College).filter fun c => outcome c = true)

/--
The iid equal-cutoff success law discharges the favorite-success coupling:
swapping deviation-only and missing top-choice success indicators is just a
finite reindexing of iid coordinates.
-/
theorem iidEqualCutoffSuccessLaw_favoriteSuccess_coupling
    {College : Type v} [Fintype College] [DecidableEq College]
    (successAtom : PMF Bool) (outsideUtility : ℝ) (utility : College → ℝ)
    (deviation topChoiceSet : Finset College)
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation}) :
    AppliedModelingLib.pmfExp (iidEqualCutoffSuccessLaw successAtom deviation)
        (fun successful =>
          favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
            (mappedSuccessfulApplicationsByTopDifference
              deviation topChoiceSet e successful)) =
      expectedFavoriteSuccessfulApplicationUtility
        (iidEqualCutoffSuccessLaw successAtom topChoiceSet)
        outsideUtility utility topChoiceSet := by
  classical
  let successSet : (College → Bool) → Finset College :=
    fun outcome =>
      (Finset.univ : Finset College).filter fun c => outcome c = true
  let swap : Equiv.Perm College := topDifferenceSwap deviation topChoiceSet e
  calc
    AppliedModelingLib.pmfExp (iidEqualCutoffSuccessLaw successAtom deviation)
        (fun successful =>
          favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
            (mappedSuccessfulApplicationsByTopDifference
              deviation topChoiceSet e successful)) =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct College Bool successAtom)
          (fun outcome =>
            favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
              (mappedSuccessfulApplicationsByTopDifference
                deviation topChoiceSet e (successSet outcome))) := by
      simp [iidEqualCutoffSuccessLaw, successSet, AppliedModelingLib.pmfExp_map]
    _ =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct College Bool successAtom)
          (fun outcome =>
            favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
              (topChoiceSet ∩ successSet (fun c => outcome (swap.symm c)))) := by
      refine congrArg (AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct College Bool successAtom)) ?_
      funext outcome
      have hmap :=
        mappedSuccessfulApplicationsByTopDifference_filter_eq_top_filter_swap
          (deviation := deviation) (topChoiceSet := topChoiceSet) e outcome
      simpa [successSet, swap] using congrArg
        (favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet) hmap
    _ =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct College Bool successAtom)
          (fun outcome =>
            favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
              (successSet (fun c => outcome (swap.symm c)))) := by
      refine congrArg (AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct College Bool successAtom)) ?_
      funext outcome
      exact favoriteSuccessfulApplicationUtility_inter_success
        outsideUtility utility topChoiceSet (successSet (fun c => outcome (swap.symm c)))
    _ =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct College Bool successAtom)
          (fun outcome =>
            favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
              (successSet outcome)) := by
      simpa [successSet, swap] using
        (AppliedModelingLib.pmfExp_pmfProduct_equiv
          (e := swap) (μ := successAtom)
          (F := fun outcome : College → Bool =>
            favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
              (successSet outcome)))
    _ =
        expectedFavoriteSuccessfulApplicationUtility
          (iidEqualCutoffSuccessLaw successAtom topChoiceSet)
          outsideUtility utility topChoiceSet := by
      simp [expectedFavoriteSuccessfulApplicationUtility, iidEqualCutoffSuccessLaw,
        successSet, AppliedModelingLib.pmfExp_map]

/--
Pointwise coupling inequality for favorite-success payoffs.  Common successful
applications remain available, and each successful deviation-only college is
replaced by a missing top-choice college that is weakly preferred.
-/
theorem favoriteSuccessfulApplicationUtility_le_mapped_top
    {College : Type v} [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (outsideUtility : ℝ) (utility : College → ℝ)
    (htop :
      ∀ c ∈ topChoiceSet, ∀ d, d ∉ topChoiceSet → utility d ≤ utility c)
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation})
    (successful : Finset College) :
    favoriteSuccessfulApplicationUtility outsideUtility utility deviation successful ≤
      favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
        (mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful) := by
  classical
  unfold favoriteSuccessfulApplicationUtility
  by_cases hdev : (deviation ∩ successful).Nonempty
  · have htop_nonempty :
        (topChoiceSet ∩
          mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful).Nonempty := by
      rcases hdev with ⟨d, hd⟩
      by_cases hdtop : d ∈ topChoiceSet
      · refine ⟨d, ?_⟩
        rw [Finset.mem_inter]
        constructor
        · exact hdtop
        · rw [mappedSuccessfulApplicationsByTopDifference]
          exact Finset.mem_union_left _
            (by
              rw [Finset.mem_inter, Finset.mem_inter]
              exact ⟨⟨(Finset.mem_inter.mp hd).1, hdtop⟩,
                (Finset.mem_inter.mp hd).2⟩)
      · let ddiff : {c // c ∈ deviation \ topChoiceSet} :=
          ⟨d, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hd).1, hdtop⟩⟩
        refine ⟨(e ddiff).1, ?_⟩
        rw [Finset.mem_inter]
        constructor
        · exact (Finset.mem_sdiff.mp (e ddiff).2).1
        · rw [mappedSuccessfulApplicationsByTopDifference]
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨d, ?_⟩, by simp, ?_⟩
          · rw [Finset.mem_inter]
            exact ⟨ddiff.2, (Finset.mem_inter.mp hd).2⟩
          · rfl
    simp only [hdev, htop_nonempty, dite_true]
    refine Finset.sup'_le hdev utility (fun d hd => ?_)
    by_cases hdtop : d ∈ topChoiceSet
    · have hmem :
          d ∈ topChoiceSet ∩
            mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful := by
        rw [Finset.mem_inter]
        constructor
        · exact hdtop
        · rw [mappedSuccessfulApplicationsByTopDifference]
          exact Finset.mem_union_left _
            (by
              rw [Finset.mem_inter, Finset.mem_inter]
              exact ⟨⟨(Finset.mem_inter.mp hd).1, hdtop⟩,
                (Finset.mem_inter.mp hd).2⟩)
      exact
        Finset.le_sup'
          (s := topChoiceSet ∩
            mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful)
          (f := utility) (b := d) hmem
    · let ddiff : {c // c ∈ deviation \ topChoiceSet} :=
        ⟨d, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hd).1, hdtop⟩⟩
      have hmem :
          (e ddiff).1 ∈ topChoiceSet ∩
            mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful := by
        rw [Finset.mem_inter]
        constructor
        · exact (Finset.mem_sdiff.mp (e ddiff).2).1
        · rw [mappedSuccessfulApplicationsByTopDifference]
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨d, ?_⟩, by simp, ?_⟩
          · rw [Finset.mem_inter]
            exact ⟨ddiff.2, (Finset.mem_inter.mp hd).2⟩
          · rfl
      exact
        le_trans
          (htop (e ddiff).1 (Finset.mem_sdiff.mp (e ddiff).2).1 d hdtop)
          (Finset.le_sup'
            (s := topChoiceSet ∩
              mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful)
            (f := utility) (b := (e ddiff).1) hmem)
  · have hsource_empty : deviation ∩ successful = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hdev
    have htop_empty :
        ¬ (topChoiceSet ∩
          mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful).Nonempty := by
      intro hmapped_nonempty
      rcases hmapped_nonempty with ⟨c, hc⟩
      have hc_mapped :
          c ∈ mappedSuccessfulApplicationsByTopDifference deviation topChoiceSet e successful :=
        (Finset.mem_inter.mp hc).2
      rw [mappedSuccessfulApplicationsByTopDifference] at hc_mapped
      rcases Finset.mem_union.mp hc_mapped with hc_common | hc_image
      · have hc_dev_success : c ∈ deviation ∩ successful := by
          rw [Finset.mem_inter]
          exact ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hc_common).1).1,
            (Finset.mem_inter.mp hc_common).2⟩
        rw [hsource_empty] at hc_dev_success
        simpa using hc_dev_success
      · rcases Finset.mem_image.mp hc_image with ⟨d, _hd, hcd⟩
        have hd_dev_success : d.1 ∈ deviation ∩ successful := by
          rw [Finset.mem_inter]
          exact ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp d.2).1).1,
            (Finset.mem_inter.mp d.2).2⟩
        rw [hsource_empty] at hd_dev_success
        simpa using hd_dev_success
    simp [hdev, htop_empty]

/--
The pointwise favorite-success coupling lifts through finite expectation.
-/
theorem expectedFavoriteSuccessfulApplicationUtility_le_mapped_top
    {College : Type v} [Fintype College] [DecidableEq College]
    {deviation topChoiceSet : Finset College}
    (successLaw : PMF (Finset College)) (outsideUtility : ℝ)
    (utility : College → ℝ)
    (htop :
      ∀ c ∈ topChoiceSet, ∀ d, d ∉ topChoiceSet → utility d ≤ utility c)
    (e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation}) :
    expectedFavoriteSuccessfulApplicationUtility
        successLaw outsideUtility utility deviation ≤
      AppliedModelingLib.pmfExp successLaw
        (fun successful =>
          favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
            (mappedSuccessfulApplicationsByTopDifference
              deviation topChoiceSet e successful)) := by
  classical
  unfold expectedFavoriteSuccessfulApplicationUtility
  exact
    AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le successLaw _ _ (fun successful =>
      favoriteSuccessfulApplicationUtility_le_mapped_top
        outsideUtility utility htop e successful)

/--
PG23 Proposition 6, favorite-success ex-ante payoff route.  Equal cutoffs enter
through the explicit coupling premise: for every feasible same-size deviation,
the success law after relabeling deviation-only applications to the missing
top-choice applications has the same expected top-choice favorite-success
payoff as the top-choice law itself.
-/
theorem proposition6_nashEquilibrium_of_equal_cutoff_favorite_success_coupling
    {College : Type v} [Fintype College] [DecidableEq College]
    {topChoiceSet : Finset College} {feasible : Finset College → Prop}
    (successLaw : Finset College → PMF (Finset College))
    (outsideUtility : ℝ) (utility : College → ℝ)
    (hfeasible_card :
      ∀ deviation : Finset College,
        feasible deviation → deviation.card = topChoiceSet.card)
    (htop :
      ∀ c ∈ topChoiceSet, ∀ d, d ∉ topChoiceSet → utility d ≤ utility c)
    (hequalCutoff_coupling :
      ∀ (deviation : Finset College) (hdeviation : feasible deviation),
        ∀ e : {d // d ∈ deviation \ topChoiceSet} ≃
          {c // c ∈ topChoiceSet \ deviation},
          AppliedModelingLib.pmfExp (successLaw deviation)
            (fun successful =>
              favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
                (mappedSuccessfulApplicationsByTopDifference
                  deviation topChoiceSet e successful)) =
            expectedFavoriteSuccessfulApplicationUtility
              (successLaw topChoiceSet) outsideUtility utility topChoiceSet) :
    NoProfitableApplicationDeviation
      (fun applicationSet =>
        expectedFavoriteSuccessfulApplicationUtility
          (successLaw applicationSet) outsideUtility utility applicationSet)
      topChoiceSet feasible := by
  classical
  intro deviation hdeviation
  have hcard_diff :
      (deviation \ topChoiceSet).card = (topChoiceSet \ deviation).card := by
    simpa [eq_comm] using
      (Finset.card_sdiff_eq_card_sdiff_iff
        (s := topChoiceSet) (t := deviation)).2
        (hfeasible_card deviation hdeviation).symm
  have hcard_sdiff_subtype :
      Fintype.card ↥(deviation \ topChoiceSet) =
        Fintype.card ↥(topChoiceSet \ deviation) := by
    rw [Fintype.card_coe (deviation \ topChoiceSet)]
    rw [Fintype.card_coe (topChoiceSet \ deviation)]
    exact hcard_diff
  let e : {d // d ∈ deviation \ topChoiceSet} ≃
      {c // c ∈ topChoiceSet \ deviation} :=
    Fintype.equivOfCardEq hcard_sdiff_subtype
  calc
    expectedFavoriteSuccessfulApplicationUtility
        (successLaw deviation) outsideUtility utility deviation ≤
        AppliedModelingLib.pmfExp (successLaw deviation)
          (fun successful =>
            favoriteSuccessfulApplicationUtility outsideUtility utility topChoiceSet
              (mappedSuccessfulApplicationsByTopDifference
                deviation topChoiceSet e successful)) := by
      exact
        expectedFavoriteSuccessfulApplicationUtility_le_mapped_top
          (successLaw deviation) outsideUtility utility htop e
    _ =
        expectedFavoriteSuccessfulApplicationUtility
          (successLaw topChoiceSet) outsideUtility utility topChoiceSet := by
      exact hequalCutoff_coupling deviation hdeviation e

/--
PG23 Proposition 6, iid equal-cutoff favorite-success route.  The common
cutoff condition is represented by an application-set-invariant iid success
indicator law, so the equal-cutoff coupling premise is derived by finite
product-law reindexing.
-/
theorem proposition6_nashEquilibrium_of_iid_equal_cutoff_favorite_success
    {College : Type v} [Fintype College] [DecidableEq College]
    {topChoiceSet : Finset College} {feasible : Finset College → Prop}
    (successAtom : PMF Bool)
    (outsideUtility : ℝ) (utility : College → ℝ)
    (hfeasible_card :
      ∀ deviation : Finset College,
        feasible deviation → deviation.card = topChoiceSet.card)
    (htop :
      ∀ c ∈ topChoiceSet, ∀ d, d ∉ topChoiceSet → utility d ≤ utility c) :
    NoProfitableApplicationDeviation
      (fun applicationSet =>
        expectedFavoriteSuccessfulApplicationUtility
          (iidEqualCutoffSuccessLaw successAtom applicationSet)
          outsideUtility utility applicationSet)
      topChoiceSet feasible := by
  classical
  exact
    proposition6_nashEquilibrium_of_equal_cutoff_favorite_success_coupling
      (topChoiceSet := topChoiceSet)
      (feasible := feasible)
      (successLaw := iidEqualCutoffSuccessLaw successAtom)
      (outsideUtility := outsideUtility)
      (utility := utility)
      hfeasible_card
      htop
      (fun deviation _hdeviation e =>
        iidEqualCutoffSuccessLaw_favoriteSuccess_coupling
          successAtom outsideUtility utility deviation topChoiceSet e)

/--
PG23 Theorem 1, probability part: polyculture match probabilities converge to
the optimal threshold rule, while monoculture match probabilities are constant
in the number of firms.
-/
def theorem1_wisdomProbabilityConclusion
    (polyMatch monoMatch : ℕ → ℝ → ℝ) (vS : ℝ) : Prop :=
  (∀ v : ℝ, v < vS → Tendsto (fun m : ℕ => polyMatch m v) atTop (nhds 0)) ∧
  (∀ v : ℝ, vS < v → Tendsto (fun m : ℕ => polyMatch m v) atTop (nhds 1)) ∧
  (∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)

/--
PG23 Theorem 1, firm-welfare part.  Polyculture welfare approaches the
noise-free optimum, while monoculture welfare is constant in the number of
firms and strictly below the optimum.
-/
def theorem1_wisdomFirmWelfareConclusion
    (polyWelfare monoWelfare : ℕ → ℝ) (optimalWelfare : ℝ) : Prop :=
  Tendsto polyWelfare atTop (nhds optimalWelfare) ∧
  (∀ m n : ℕ, monoWelfare m = monoWelfare n) ∧
  monoWelfare 0 < optimalWelfare

/--
The optimal step-rule match probability in PG23 Theorem 1: applicants strictly
above the efficient cutoff are matched, and applicants below it are not.
-/
noncomputable def theorem1_optimalStepMatchProbability (vS v : ℝ) : ℝ :=
  if vS < v then 1 else 0

/--
The efficient step-rule admission mass is the upper-tail mass above the supply
cutoff.
-/
theorem theorem1_optimalStepMatchProbability_integral_eq_upperTailMass
    (η : Measure ℝ) (vS : ℝ) :
    (∫ v : ℝ, theorem1_optimalStepMatchProbability vS v ∂η) =
      AppliedModelingLib.Probability.upperTailMass η vS := by
  have hfun :
      (fun v : ℝ => theorem1_optimalStepMatchProbability vS v) =
        (Set.Ioi vS).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext v
    by_cases hv : vS < v <;>
      simp [theorem1_optimalStepMatchProbability, Set.indicator, hv]
  rw [hfun]
  simpa [AppliedModelingLib.Probability.upperTailMass, Measure.real] using
    (MeasureTheory.integral_indicator_one
      (μ := η) (s := Set.Ioi vS) measurableSet_Ioi)

/-- The efficient step-rule match probability is integrable under a finite value measure. -/
theorem theorem1_optimalStepMatchProbability_integrable
    (η : Measure ℝ) [IsFiniteMeasure η] (vS : ℝ) :
    Integrable (fun v : ℝ => theorem1_optimalStepMatchProbability vS v) η := by
  have hindicator :
      Integrable ((Set.Ioi vS).indicator (fun _ : ℝ => (1 : ℝ))) η :=
    (integrable_const (μ := η) (c := (1 : ℝ))).indicator measurableSet_Ioi
  simpa [theorem1_optimalStepMatchProbability, Set.indicator] using hindicator

/--
If applicant value has integrable absolute value, then the value-weighted
efficient step rule is integrable.
-/
theorem theorem1_optimalStepMatchProbability_value_integrable_of_abs_integrable
    (η : Measure ℝ) [IsFiniteMeasure η] (vS : ℝ)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η) :
    Integrable
      (fun v : ℝ => v * theorem1_optimalStepMatchProbability vS v) η := by
  have hid : Integrable (fun v : ℝ => v) η := by
    refine Integrable.mono' habs_integrable
      measurable_id.aestronglyMeasurable ?_
    filter_upwards with v
    simp [Real.norm_eq_abs]
  have hindicator :
      Integrable ((Set.Ioi vS).indicator (fun v : ℝ => v)) η :=
    hid.indicator measurableSet_Ioi
  simpa [theorem1_optimalStepMatchProbability, Set.indicator] using hindicator

/--
Source-shaped certificate for the strict monoculture welfare gap in PG23
Theorem 1.

The paper's argument is a threshold rearrangement: the monoculture admission
probability has the same total admitted mass as the efficient upper-tail rule,
but it is fractional on a positive-measure set away from the efficient cutoff.
Moving that mass to the upper tail strictly raises value-weighted welfare.
-/
structure Theorem1MonocultureStrictSuboptimalityCertificate
    (η : Measure ℝ) (monoMatchAtZero : ℝ → ℝ) (vS : ℝ) : Prop where
  mono_integrable : Integrable monoMatchAtZero η
  step_integrable :
    Integrable (fun v : ℝ => theorem1_optimalStepMatchProbability vS v) η
  mono_value_integrable :
    Integrable (fun v : ℝ => v * monoMatchAtZero v) η
  step_value_integrable :
    Integrable
      (fun v : ℝ => v * theorem1_optimalStepMatchProbability vS v) η
  mono_probability_bounds :
    ∀ v : ℝ, 0 ≤ monoMatchAtZero v ∧ monoMatchAtZero v ≤ 1
  same_mass_as_supply_tail :
    (∫ v : ℝ, monoMatchAtZero v ∂η) =
      ∫ v : ℝ, theorem1_optimalStepMatchProbability vS v ∂η
  fractional_off_supply_cutoff :
    0 < η {v : ℝ |
      v ≠ vS ∧ 0 < monoMatchAtZero v ∧ monoMatchAtZero v < 1}

/--
PG23 source-region constructor for the monoculture strict-suboptimality
certificate.  Market clearing supplies equal admitted mass; iid single-cutoff
noise support supplies a positive-measure region where monoculture admission is
strictly fractional away from the efficient cutoff.
-/
theorem theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_source_region
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm0 : Fin (0 + 1))
    {monoCutoff0 vS supply commonMonoSupply xMin xMax : ℝ}
    {commonMonoDemand : ℝ → ℝ} {region : Set ℝ}
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hcommon_clear0 :
      commonMonoDemand monoCutoff0 = commonMonoSupply)
    (hcommon_eq0 :
      commonMonoDemand monoCutoff0 =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hcommon_supply_eq : commonMonoSupply = supply)
    (hmono_integrable :
      Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0) η)
    (hmono_value_integrable :
      Integrable
        (fun v : ℝ =>
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0) η)
    (hstep_integrable :
      Integrable (fun v : ℝ => theorem1_optimalStepMatchProbability vS v) η)
    (hstep_value_integrable :
      Integrable
        (fun v : ℝ => v * theorem1_optimalStepMatchProbability vS v) η)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_positive : 0 < η region)
    (hregion_off_cutoff : ∀ v ∈ region, v ≠ vS)
    (hregion_support :
      ∀ v ∈ region, monoCutoff0 - v ∈ Set.Ioo xMin xMax) :
    Theorem1MonocultureStrictSuboptimalityCertificate
      η
      (fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0)
      vS := by
  refine
    { mono_integrable := hmono_integrable
      step_integrable := hstep_integrable
      mono_value_integrable := hmono_value_integrable
      step_value_integrable := hstep_value_integrable
      mono_probability_bounds := ?_
      same_mass_as_supply_tail := ?_
      fractional_off_supply_cutoff := ?_ }
  · intro v
    constructor
    · exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_nonneg
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0
    · exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_one
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0
  · have hstep_mass :
        (∫ v : ℝ, theorem1_optimalStepMatchProbability vS v ∂η) =
          supply := by
      rw [theorem1_optimalStepMatchProbability_integral_eq_upperTailMass]
      exact hsupply.tail_eq_capacity
    calc
      (∫ v : ℝ,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η) =
          commonMonoDemand monoCutoff0 := hcommon_eq0.symm
      _ = commonMonoSupply := hcommon_clear0
      _ = supply := hcommon_supply_eq
      _ = ∫ v : ℝ, theorem1_optimalStepMatchProbability vS v ∂η :=
        hstep_mass.symm
  · have hsubset :
        region ⊆
          {v : ℝ |
            v ≠ vS ∧
              0 <
                AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
                  v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∧
              AppliedModelingLib.Matching.singleCutoffCrossingProbability
                  (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
                  v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 < 1} := by
      intro v hv
      have hcdf_mem :
          AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (monoCutoff0 - v) ∈
            Set.Ioo (0 : ℝ) 1 :=
        AppliedModelingLib.Probability.lowerCDFMass_mem_Ioo_of_strictMonoOn_Icc_endpoint_values
          baseNoiseLaw hcdf_strict hleft hright (hregion_support v hv)
      exact
        ⟨hregion_off_cutoff v hv,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_pos_of_lowerCDFMass_lt_one
            baseNoiseLaw topFirm0 hcdf_mem.2,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_lt_one_of_lowerCDFMass_pos
            baseNoiseLaw topFirm0 hcdf_mem.1⟩
    exact lt_of_lt_of_le hregion_positive (measure_mono hsubset)

/--
PG23 source-region constructor using the paper's usual no-atom condition at the
efficient cutoff.  A positive-measure interior region may contain `v_S`; after
removing the null singleton, it still has positive measure and lies away from
the efficient cutoff.
-/
theorem theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_no_atom_region
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm0 : Fin (0 + 1))
    {monoCutoff0 vS supply commonMonoSupply xMin xMax : ℝ}
    {commonMonoDemand : ℝ → ℝ} {region : Set ℝ}
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hcommon_clear0 :
      commonMonoDemand monoCutoff0 = commonMonoSupply)
    (hcommon_eq0 :
      commonMonoDemand monoCutoff0 =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hcommon_supply_eq : commonMonoSupply = supply)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_positive : 0 < η.real region)
    (hno_atom : η ({vS} : Set ℝ) = 0)
    (hregion_support :
      ∀ v ∈ region, monoCutoff0 - v ∈ Set.Ioo xMin xMax) :
    Theorem1MonocultureStrictSuboptimalityCertificate
      η
      (fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0)
      vS := by
  have hsingleton_real : η.real ({vS} : Set ℝ) = 0 := by
    simp [Measure.real, hno_atom]
  have hdiff_real : η.real (region \ ({vS} : Set ℝ)) = η.real region := by
    exact
      measureReal_diff_null
        (μ := η) (s₁ := region) (s₂ := ({vS} : Set ℝ))
        hsingleton_real
  have hdiff_positive : 0 < η (region \ ({vS} : Set ℝ)) := by
    refine AppliedModelingLib.measure_pos_of_measureReal_pos η
      (region \ ({vS} : Set ℝ)) ?_
    rwa [hdiff_real]
  exact
    theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_source_region
      η baseNoiseLaw topFirm0 hsupply hcommon_clear0 hcommon_eq0
      hcommon_supply_eq
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
        baseNoiseLaw η monoCutoff0 topFirm0)
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_value_mul_integrable_of_abs_integrable
        baseNoiseLaw η monoCutoff0 topFirm0 habs_integrable)
      (theorem1_optimalStepMatchProbability_integrable η vS)
      (theorem1_optimalStepMatchProbability_value_integrable_of_abs_integrable
        η vS habs_integrable)
      hcdf_strict hleft hright
      hdiff_positive
      (by
        intro v hv
        exact hv.2)
      (by
        intro v hv
        exact hregion_support v hv.1)

/--
PG23 source-interval constructor for the monoculture strict-suboptimality
certificate.  The paper's interval argument gives an interior value interval
where iid single-cutoff admission is fractional.  Strict interior CDF growth
and the interval-mass formula show that this interval remains positive after
removing the efficient cutoff point, so this strict-suboptimality certificate
does not need a separate atomlessness premise.
-/
theorem theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_interval_region
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm0 : Fin (0 + 1))
    {monoCutoff0 vS supply commonMonoSupply vMin vMax xMin xMax a b : ℝ}
    {commonMonoDemand valueCDF : ℝ → ℝ}
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hcommon_clear0 :
      commonMonoDemand monoCutoff0 = commonMonoSupply)
    (hcommon_eq0 :
      commonMonoDemand monoCutoff0 =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hcommon_supply_eq : commonMonoSupply = supply)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hregion_support :
      ∀ v ∈ Set.Ioo a b, monoCutoff0 - v ∈ Set.Ioo xMin xMax) :
    Theorem1MonocultureStrictSuboptimalityCertificate
      η
      (fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
          v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0)
      vS := by
  let region : Set ℝ := Set.Ioo a b \ ({vS} : Set ℝ)
  have hregion_positive_real : 0 < η.real region := by
    dsimp [region]
    exact
      AppliedModelingLib.Probability.measureReal_Ioo_diff_singleton_pos_of_strictCDFOn
        (μ := η) (valueCDF := valueCDF) ha hb hab
        hvalue_cdf_strict hvalue_measure_eq
  have hregion_positive : 0 < η region :=
    AppliedModelingLib.measure_pos_of_measureReal_pos η region hregion_positive_real
  exact
    theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_source_region
      η baseNoiseLaw topFirm0 hsupply hcommon_clear0 hcommon_eq0
      hcommon_supply_eq
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
        baseNoiseLaw η monoCutoff0 topFirm0)
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_value_mul_integrable_of_abs_integrable
        baseNoiseLaw η monoCutoff0 topFirm0 habs_integrable)
      (theorem1_optimalStepMatchProbability_integrable η vS)
      (theorem1_optimalStepMatchProbability_value_integrable_of_abs_integrable
        η vS habs_integrable)
      hcdf_strict hleft hright
      hregion_positive
      (by
        intro v hv
        exact hv.2)
      (by
        intro v hv
        exact hregion_support v hv.1)

/--
PG23 monoculture strict suboptimality from the threshold rearrangement
certificate used in the source proof.
-/
theorem theorem1_monoWelfare_strictSuboptimal_of_rearrangement
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {monoMatchAtZero : ℝ → ℝ} {vS : ℝ}
    {monoWelfareAtZero optimalWelfare : ℝ}
    (hcert :
      Theorem1MonocultureStrictSuboptimalityCertificate
        η monoMatchAtZero vS)
    (hmonoWelfare_eq :
      monoWelfareAtZero =
        ∫ v : ℝ, v * monoMatchAtZero v ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η) :
    monoWelfareAtZero < optimalWelfare := by
  rw [hmonoWelfare_eq, hoptimalWelfare_eq]
  have hlt :
      (∫ v : ℝ, v * monoMatchAtZero v ∂η) <
        ∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂η :=
    AppliedModelingLib.integral_value_mul_lt_upperTailStep_of_same_mass_fractional
      (μ := η) (threshold := vS) (q := monoMatchAtZero)
      hcert.mono_integrable
      (by
        simpa [theorem1_optimalStepMatchProbability] using
          hcert.step_integrable)
      hcert.mono_value_integrable
      (by
        simpa [theorem1_optimalStepMatchProbability] using
          hcert.step_value_integrable)
      hcert.mono_probability_bounds
      (by
        simpa [theorem1_optimalStepMatchProbability] using
          hcert.same_mass_as_supply_tail)
      hcert.fractional_off_supply_cutoff
  simpa [theorem1_optimalStepMatchProbability] using hlt

/--
PG23 monoculture strict suboptimality directly from the source iid
single-cutoff/no-atom region.  This is the paper-facing version of the
threshold-rearrangement welfare gap: the certificate is constructed internally
from source primitives before applying the rearrangement inequality.
-/
theorem theorem1_monoWelfare_strictSuboptimal_of_iid_single_cutoff_no_atom_region
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm0 : Fin (0 + 1))
    {monoCutoff0 vS supply commonMonoSupply xMin xMax : ℝ}
    {commonMonoDemand : ℝ → ℝ} {region : Set ℝ}
    {monoWelfareAtZero optimalWelfare : ℝ}
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hcommon_clear0 :
      commonMonoDemand monoCutoff0 = commonMonoSupply)
    (hcommon_eq0 :
      commonMonoDemand monoCutoff0 =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hcommon_supply_eq : commonMonoSupply = supply)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_positive : 0 < η.real region)
    (hno_atom : η ({vS} : Set ℝ) = 0)
    (hregion_support :
      ∀ v ∈ region, monoCutoff0 - v ∈ Set.Ioo xMin xMax)
    (hmonoWelfare_eq :
      monoWelfareAtZero =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η) :
    monoWelfareAtZero < optimalWelfare :=
  theorem1_monoWelfare_strictSuboptimal_of_rearrangement
    (theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_no_atom_region
      η baseNoiseLaw topFirm0 hsupply hcommon_clear0 hcommon_eq0
      hcommon_supply_eq habs_integrable hcdf_strict hleft hright
      hregion_positive hno_atom hregion_support)
    hmonoWelfare_eq hoptimalWelfare_eq

/--
PG23 monoculture strict suboptimality directly from the source interval
argument, without a separate atomlessness premise for the strict gap.
-/
theorem theorem1_monoWelfare_strictSuboptimal_of_iid_single_cutoff_interval_region
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm0 : Fin (0 + 1))
    {monoCutoff0 vS supply commonMonoSupply vMin vMax xMin xMax a b : ℝ}
    {commonMonoDemand valueCDF : ℝ → ℝ}
    {monoWelfareAtZero optimalWelfare : ℝ}
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hcommon_clear0 :
      commonMonoDemand monoCutoff0 = commonMonoSupply)
    (hcommon_eq0 :
      commonMonoDemand monoCutoff0 =
        ∫ v,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hcommon_supply_eq : commonMonoSupply = supply)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hregion_support :
      ∀ v ∈ Set.Ioo a b, monoCutoff0 - v ∈ Set.Ioo xMin xMax)
    (hmonoWelfare_eq :
      monoWelfareAtZero =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => monoCutoff0) topFirm0 ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η) :
    monoWelfareAtZero < optimalWelfare :=
  theorem1_monoWelfare_strictSuboptimal_of_rearrangement
    (theorem1_monoStrictSuboptimalityCertificate_of_iid_single_cutoff_interval_region
      η baseNoiseLaw topFirm0 hsupply hcommon_clear0 hcommon_eq0
      hcommon_supply_eq habs_integrable hvalue_cdf_strict hvalue_measure_eq
      hcdf_strict hleft hright ha hb hab hregion_support)
    hmonoWelfare_eq hoptimalWelfare_eq

/--
Dominated-convergence welfare bridge for the polyculture part of PG23
Theorem 1.  The paper proves the probability step-function limit first; this
lemma turns that pointwise limit into convergence of expected matched value,
with the analytic side conditions exposed explicitly.
-/
theorem theorem1_polyWelfare_tendsto_of_probability_step_integral
    {η : Measure ℝ} {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpoly_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun v : ℝ => v * polyMatch n v) η)
    (hpoly_prob_bounds :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        0 ≤ polyMatch n v ∧ polyMatch n v ≤ 1)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ, v * polyMatch n v ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η) :
    Tendsto polyWelfare atTop (nhds optimalWelfare) := by
  have hbound :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        ‖v * polyMatch n v‖ ≤ |v| := by
    intro n
    filter_upwards [hpoly_prob_bounds n] with v hv
    have h_abs_prob : |polyMatch n v| ≤ 1 := by
      exact abs_le.2 ⟨by linarith [hv.1], hv.2⟩
    calc
      ‖v * polyMatch n v‖ = |v * polyMatch n v| := by
        simp [Real.norm_eq_abs]
      _ = |v| * |polyMatch n v| := by
        rw [abs_mul]
      _ ≤ |v| * 1 :=
        mul_le_mul_of_nonneg_left h_abs_prob (abs_nonneg v)
      _ = |v| := by ring
  have hlim :
      ∀ᵐ v : ℝ ∂η,
        Tendsto (fun n : ℕ => v * polyMatch n v) atTop
          (nhds (v * theorem1_optimalStepMatchProbability vS v)) := by
    have hne_ae :
        ∀ᵐ v : ℝ ∂η, v ∈ ({vS} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr hno_atom
    filter_upwards [hne_ae] with v hv_ne
    have hv_ne' : v ≠ vS := by
      simpa using hv_ne
    rcases lt_or_gt_of_ne hv_ne' with hv_lt | hv_gt
    · have hmatch : Tendsto (fun n : ℕ => polyMatch n v) atTop (nhds 0) :=
        hprob.1 v hv_lt
      have hmul :
          Tendsto (fun n : ℕ => v * polyMatch n v) atTop (nhds (v * 0)) :=
        tendsto_const_nhds.mul hmatch
      simpa [theorem1_optimalStepMatchProbability, not_lt_of_gt hv_lt]
        using hmul
    · have hmatch : Tendsto (fun n : ℕ => polyMatch n v) atTop (nhds 1) :=
        hprob.2.1 v hv_gt
      have hmul :
          Tendsto (fun n : ℕ => v * polyMatch n v) atTop (nhds (v * 1)) :=
        tendsto_const_nhds.mul hmatch
      simpa [theorem1_optimalStepMatchProbability, hv_gt] using hmul
  have htendsto_integral :
      Tendsto
        (fun n : ℕ => ∫ v : ℝ, v * polyMatch n v ∂η)
        atTop
        (nhds
          (∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := η) (G := ℝ)
      (fun v : ℝ => |v|)
      hpoly_meas habs_integrable hbound hlim
  have hseq :
      Tendsto polyWelfare atTop
        (nhds
          (∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)) :=
    htendsto_integral.congr' (by
    filter_upwards with n
    exact (hpolyWelfare_eq n).symm)
  simpa [hoptimalWelfare_eq] using hseq

/--
PG23 Theorem 1 welfare conclusion from the probability theorem plus explicit
integral semantics and the source's monoculture strict-suboptimality step.
-/
theorem theorem1_wisdomFirmWelfare_of_probability_step_integral
    {η : Measure ℝ} {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpoly_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun v : ℝ => v * polyMatch n v) η)
    (hpoly_prob_bounds :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        0 ≤ polyMatch n v ∧ polyMatch n v ≤ 1)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ, v * polyMatch n v ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ, v * monoMatch n v ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFirmWelfareConclusion
      polyWelfare monoWelfare optimalWelfare := by
  refine ⟨?_, ?_, hmono_suboptimal⟩
  · exact
      theorem1_polyWelfare_tendsto_of_probability_step_integral
        (η := η) (monoMatch := monoMatch)
        hprob hno_atom habs_integrable hpoly_meas hpoly_prob_bounds
        hpolyWelfare_eq hoptimalWelfare_eq
  · intro m n
    have hfun :
        (fun v : ℝ => v * monoMatch m v) =
          (fun v : ℝ => v * monoMatch n v) := by
      funext v
      rw [hprob.2.2 v m n]
    rw [hmonoWelfare_eq m, hmonoWelfare_eq n, hfun]

/--
PG23 Theorem 1 welfare conclusion from the probability theorem, explicit
integral semantics, and the source threshold-rearrangement certificate for
monoculture strict suboptimality.
-/
theorem theorem1_wisdomFirmWelfare_of_probability_step_integral_and_mono_rearrangement
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpoly_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun v : ℝ => v * polyMatch n v) η)
    (hpoly_prob_bounds :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        0 ≤ polyMatch n v ∧ polyMatch n v ≤ 1)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ, v * polyMatch n v ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ, v * monoMatch n v ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_rearrangement :
      Theorem1MonocultureStrictSuboptimalityCertificate
        η (monoMatch 0) vS) :
    theorem1_wisdomFirmWelfareConclusion
      polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFirmWelfare_of_probability_step_integral
    (η := η) (polyMatch := polyMatch) (monoMatch := monoMatch) (vS := vS)
    hprob hno_atom habs_integrable hpoly_meas hpoly_prob_bounds
    hpolyWelfare_eq hmonoWelfare_eq hoptimalWelfare_eq
    (theorem1_monoWelfare_strictSuboptimal_of_rearrangement
      hmono_rearrangement (hmonoWelfare_eq 0) hoptimalWelfare_eq)

/--
PG23 Theorem 1 full source statement: the probability step-function
conclusion plus the corresponding firm-welfare conclusion.
-/
def theorem1_wisdomFullConclusion
    (polyMatch monoMatch : ℕ → ℝ → ℝ) (vS : ℝ)
    (polyWelfare monoWelfare : ℕ → ℝ) (optimalWelfare : ℝ) : Prop :=
  theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS ∧
  theorem1_wisdomFirmWelfareConclusion
    polyWelfare monoWelfare optimalWelfare

/--
Theorem 1 full conclusion from the probability route and an explicit welfare
bridge.  The welfare bridge is the separate measure/integration step turning
the source probability limits into expected firm welfare convergence.
-/
theorem theorem1_wisdomFull_of_probability_and_welfare
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      polyMatch monoMatch vS polyWelfare monoWelfare optimalWelfare :=
  ⟨hprob, hwelfare⟩

/--
PG23 Theorem 1 full conclusion from the probability theorem, explicit welfare
integrals, and the source threshold-rearrangement certificate for monoculture
strict suboptimality.
-/
theorem theorem1_wisdomFull_of_probability_step_integral_and_mono_rearrangement
    {η : Measure ℝ} [IsProbabilityMeasure η]
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpoly_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun v : ℝ => v * polyMatch n v) η)
    (hpoly_prob_bounds :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        0 ≤ polyMatch n v ∧ polyMatch n v ≤ 1)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ, v * polyMatch n v ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ, v * monoMatch n v ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_rearrangement :
      Theorem1MonocultureStrictSuboptimalityCertificate
        η (monoMatch 0) vS) :
    theorem1_wisdomFullConclusion
      polyMatch monoMatch vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare hprob
    (theorem1_wisdomFirmWelfare_of_probability_step_integral_and_mono_rearrangement
      hprob hno_atom habs_integrable hpoly_meas hpoly_prob_bounds
      hpolyWelfare_eq hmonoWelfare_eq hoptimalWelfare_eq
      hmono_rearrangement)

/--
Theorem 1 full source clauses.  This projection exposes the paper-facing
probability and welfare conclusions directly: low-value polyculture match
probability vanishes, high-value polyculture match probability tends to one,
monoculture match probability is invariant in the number of firms, polyculture
welfare approaches the optimum, monoculture welfare is invariant, and
monoculture welfare is strictly suboptimal.
-/
theorem theorem1_wisdomFull_source_clauses
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (h :
      theorem1_wisdomFullConclusion
        polyMatch monoMatch vS polyWelfare monoWelfare optimalWelfare) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ m : ℕ in atTop, polyMatch m v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ m : ℕ in atTop, 1 - ε < polyMatch m v) ∧
    (∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) ∧
    Tendsto polyWelfare atTop (nhds optimalWelfare) ∧
    (∀ m n : ℕ, monoWelfare m = monoWelfare n) ∧
    monoWelfare 0 < optimalWelfare := by
  refine ⟨?_, ?_, h.1.2.2, h.2.1, h.2.2.1, h.2.2.2⟩
  · intro v ε hv hε
    exact (h.1.1 v hv) (isOpen_Iio.mem_nhds hε)
  · intro v ε hv hε
    have hmem : (1 : ℝ) ∈ Set.Ioi (1 - ε) := by
      simp
      linarith
    exact (h.1.2.1 v hv) (isOpen_Ioi.mem_nhds hmem)

/--
The one-sided threshold-location estimates used in PG23 Lemma 10 imply
convergence of the moving threshold.  The source proof obtains these two
eventual inequalities from market clearing, the low/high maximum-concentration
bounds, and the connected support/quantile argument.
-/
theorem lemma10_threshold_tendsto_of_one_sided_eventual_bounds
    {threshold : ℕ → ℝ} {vS : ℝ}
    (hupper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, threshold n - vS < ε)
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, vS - threshold n < ε) :
    Tendsto threshold atTop (nhds vS) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hclose :
      ∀ᶠ n : ℕ in atTop, dist (threshold n) vS < ε := by
    filter_upwards [hupper ε hε, hlower ε hε] with n hn_upper hn_lower
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact Filter.eventually_atTop.1 hclose

/--
PG23 Lemma 10 threshold convergence from the source quantile/tail bracket
argument.

The source proof derives these two shifted upper-tail brackets by splitting
the market-clearing integral at `threshold n - ε / 2` and
`threshold n + ε / 2`, then using connected support around the supply cutoff.
This theorem performs the common final quantile-stability step.
-/
theorem lemma10_threshold_tendsto_of_shifted_tail_brackets
    (η : Measure ℝ) [MeasureTheory.IsFiniteMeasure η]
    {threshold : ℕ → ℝ} {vS : ℝ}
    (hupper :
      ∀ ε : ℝ, 0 < ε →
        ∃ q : ℝ,
          AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < q ∧
            ∀ᶠ n : ℕ in atTop,
              q <
                AppliedModelingLib.Probability.upperTailMass
                  η (threshold n - ε / 2))
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∃ q : ℝ,
          (∀ᶠ n : ℕ in atTop,
            AppliedModelingLib.Probability.upperTailMass
              η (threshold n + ε / 2) < q) ∧
            q <
              AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2)) :
    Tendsto threshold atTop (nhds vS) :=
  AppliedModelingLib.Probability.tendsto_of_eventual_shifted_upperTailMass_brackets
    η hupper hlower

/--
PG23 Lemma 10 threshold convergence from the market-clearing tail-split
inequalities.

This formalizes the source proof step saying "take epsilon sufficiently
small" after the integral split.  The strict tail inequalities around `vS`
are the connected-support/supply-cutoff input; the two split hypotheses are
the upper- and lower-location inequalities obtained from market clearing and
the low/high match-probability bounds.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_tail_split
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {threshold : ℕ → ℝ} {vS supply : ℝ}
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hupper_split :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) <
            (supply - δ) / (1 - δ) →
          ∀ᶠ n : ℕ in atTop,
            (supply - δ) / (1 - δ) <
              AppliedModelingLib.Probability.upperTailMass
                η (threshold n - ε / 2))
    (hlower_split :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        supply / (1 - δ) <
            AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2) →
          ∀ᶠ n : ℕ in atTop,
            AppliedModelingLib.Probability.upperTailMass
              η (threshold n + ε / 2) <
                supply / (1 - δ)) :
    Tendsto threshold atTop (nhds vS) := by
  refine lemma10_threshold_tendsto_of_shifted_tail_brackets η ?_ ?_
  · intro ε hε
    have htail_nonneg :
        0 ≤ AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) :=
      AppliedModelingLib.Probability.upperTailMass_nonneg η (vS + ε / 2)
    have htail_le_one :
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) ≤ 1 :=
      AppliedModelingLib.Probability.upperTailMass_le_one η (vS + ε / 2)
    rcases
        AppliedModelingLib.Probability.exists_epsilon_sub_div_one_sub_between_of_lt
          htail_nonneg htail_le_one (hstrict_right ε hε) with
      ⟨δ, hδ_pos, hδ_lt_one, hbetween⟩
    refine ⟨(supply - δ) / (1 - δ), hbetween, ?_⟩
    exact hupper_split ε δ hε hδ_pos hδ_lt_one hbetween
  · intro ε hε
    have htail_le_one :
        AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2) ≤ 1 :=
      AppliedModelingLib.Probability.upperTailMass_le_one η (vS - ε / 2)
    rcases
      AppliedModelingLib.Probability.exists_epsilon_div_one_sub_between_of_lt
          htail_le_one (hstrict_left ε hε) with
      ⟨δ, hδ_pos, hδ_lt_one, hbetween⟩
    refine ⟨supply / (1 - δ), ?_, hbetween⟩
    exact hlower_split ε δ hε hδ_pos hδ_lt_one hbetween

/-- Scalar algebra for the upper-location half of the Lemma 10 split. -/
theorem lemma10_tail_lower_bound_of_supply_lt_low_tail_convex
    {supply δ A : ℝ} (hδ_lt_one : δ < 1)
    (hbound : supply < (1 - A) * δ + A) :
    (supply - δ) / (1 - δ) < A := by
  have hden_pos : 0 < 1 - δ := by linarith
  rw [div_lt_iff₀ hden_pos]
  nlinarith

/-- Scalar algebra for the lower-location half of the Lemma 10 split. -/
theorem lemma10_tail_upper_bound_of_high_tail_lt_supply
    {supply δ A : ℝ} (hδ_lt_one : δ < 1)
    (hbound : (1 - δ) * A < supply) :
    A < supply / (1 - δ) := by
  have hden_pos : 0 < 1 - δ := by linarith
  rw [lt_div_iff₀ hden_pos]
  nlinarith

/-- Non-strict scalar algebra for the upper-location half of Lemma 10. -/
theorem lemma10_tail_lower_bound_of_supply_le_low_tail_convex
    {supply δ A : ℝ} (hδ_lt_one : δ < 1)
    (hbound : supply ≤ (1 - A) * δ + A) :
    (supply - δ) / (1 - δ) ≤ A := by
  have hden_pos : 0 < 1 - δ := by linarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Non-strict scalar algebra for the lower-location half of Lemma 10. -/
theorem lemma10_tail_upper_bound_of_high_tail_le_supply
    {supply δ A : ℝ} (hδ_lt_one : δ < 1)
    (hbound : (1 - δ) * A ≤ supply) :
    A ≤ supply / (1 - δ) := by
  have hden_pos : 0 < 1 - δ := by linarith
  rw [le_div_iff₀ hden_pos]
  nlinarith

/--
PG23 Lemma 10 threshold convergence from the scalar inequalities produced by
the market-clearing integral split.

The upper scalar inequality corresponds to
`S < (1 - A) * δ + A`.  The lower scalar inequality corresponds to
`(1 - δ) * A < S`.  This theorem performs the remaining algebra and quantile
stability steps.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_scalar_split
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {threshold : ℕ → ℝ} {vS supply : ℝ}
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hupper_scalar :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) <
            (supply - δ) / (1 - δ) →
          ∀ᶠ n : ℕ in atTop,
            supply <
              (1 -
                  AppliedModelingLib.Probability.upperTailMass
                    η (threshold n - ε / 2)) * δ +
                AppliedModelingLib.Probability.upperTailMass
                  η (threshold n - ε / 2))
    (hlower_scalar :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        supply / (1 - δ) <
            AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2) →
          ∀ᶠ n : ℕ in atTop,
            (1 - δ) *
                AppliedModelingLib.Probability.upperTailMass
                  η (threshold n + ε / 2) <
              supply) :
    Tendsto threshold atTop (nhds vS) := by
  refine
    lemma10_threshold_tendsto_of_marketClearing_tail_split
      (η := η) (threshold := threshold) (vS := vS) (supply := supply)
      hstrict_right hstrict_left ?_ ?_
  · intro ε δ hε hδ_pos hδ_lt_one hbetween
    have hscalar :=
      hupper_scalar ε δ hε hδ_pos hδ_lt_one hbetween
    filter_upwards [hscalar] with n hn
    exact
      lemma10_tail_lower_bound_of_supply_lt_low_tail_convex
        hδ_lt_one hn
  · intro ε δ hε hδ_pos hδ_lt_one hbetween
    have hscalar :=
      hlower_scalar ε δ hε hδ_pos hδ_lt_one hbetween
    filter_upwards [hscalar] with n hn
    exact
      lemma10_tail_upper_bound_of_high_tail_lt_supply
        hδ_lt_one hn

/--
Nonstrict variant of the scalar market-clearing split.

The fixed `vS`-side tail inequalities remain strict, but the threshold-side
split consequences can be non-strict.  This is enough for convergence because
the quantile-stability argument uses a smaller radius internally.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_scalar_split_le
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {threshold : ℕ → ℝ} {vS supply : ℝ}
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hupper_scalar :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) <
            (supply - δ) / (1 - δ) →
          ∀ᶠ n : ℕ in atTop,
            supply ≤
              (1 -
                  AppliedModelingLib.Probability.upperTailMass
                    η (threshold n - ε / 2)) * δ +
                AppliedModelingLib.Probability.upperTailMass
                  η (threshold n - ε / 2))
    (hlower_scalar :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        supply / (1 - δ) <
            AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2) →
          ∀ᶠ n : ℕ in atTop,
            (1 - δ) *
                AppliedModelingLib.Probability.upperTailMass
                  η (threshold n + ε / 2) ≤
              supply) :
    Tendsto threshold atTop (nhds vS) := by
  refine
    AppliedModelingLib.Probability.tendsto_of_eventual_shifted_upperTailMass_brackets_le
      η ?_ ?_
  · intro ε hε
    have htail_nonneg :
        0 ≤ AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) :=
      AppliedModelingLib.Probability.upperTailMass_nonneg η (vS + ε / 2)
    have htail_le_one :
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) ≤ 1 :=
      AppliedModelingLib.Probability.upperTailMass_le_one η (vS + ε / 2)
    rcases
        AppliedModelingLib.Probability.exists_epsilon_sub_div_one_sub_between_of_lt
          htail_nonneg htail_le_one (hstrict_right ε hε) with
      ⟨δ, hδ_pos, hδ_lt_one, hbetween⟩
    refine ⟨(supply - δ) / (1 - δ), hbetween, ?_⟩
    have hscalar :=
      hupper_scalar ε δ hε hδ_pos hδ_lt_one hbetween
    filter_upwards [hscalar] with n hn
    exact
      lemma10_tail_lower_bound_of_supply_le_low_tail_convex
        hδ_lt_one hn
  · intro ε hε
    have htail_le_one :
        AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2) ≤ 1 :=
      AppliedModelingLib.Probability.upperTailMass_le_one η (vS - ε / 2)
    rcases
      AppliedModelingLib.Probability.exists_epsilon_div_one_sub_between_of_lt
          htail_le_one (hstrict_left ε hε) with
      ⟨δ, hδ_pos, hδ_lt_one, hbetween⟩
    refine ⟨supply / (1 - δ), ?_, hbetween⟩
    have hscalar :=
      hlower_scalar ε δ hε hδ_pos hδ_lt_one hbetween
    filter_upwards [hscalar] with n hn
    exact
      lemma10_tail_upper_bound_of_high_tail_le_supply
        hδ_lt_one hn

/--
The upper-location scalar inequality in PG23 Lemma 10 follows from market
clearing and a two-piece pointwise upper bound on the match probability.
-/
theorem lemma10_upper_scalar_split_of_integral_bounds
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {matchProb : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {supply : ℝ}
    (hint : ∀ n, Integrable (matchProb n) η)
    (hclear : ∀ n, ∫ v, matchProb n v ∂η = supply)
    (hpositive_left :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 < η (Set.Iic (threshold n - ε / 2)))
    (hlow :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, v ≤ threshold n - ε / 2 → matchProb n v < δ)
    (hhigh :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n - ε / 2 < v → matchProb n v ≤ 1) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      ∀ᶠ n : ℕ in atTop,
        supply <
          (1 -
              AppliedModelingLib.Probability.upperTailMass
                η (threshold n - ε / 2)) * δ +
            AppliedModelingLib.Probability.upperTailMass
              η (threshold n - ε / 2) := by
  intro ε δ hε hδ_pos hδ_lt_one
  filter_upwards
    [hpositive_left ε δ hε hδ_pos hδ_lt_one,
      hlow ε δ hε hδ_pos hδ_lt_one,
      hhigh ε δ hε hδ_pos hδ_lt_one] with n hpos hlow_n hhigh_n
  let t : ℝ := threshold n - ε / 2
  have hsplit :
      ∫ v, matchProb n v ∂η <
        δ * η.real (Set.Iic t) +
          (1 : ℝ) * η.real (Set.Iic t)ᶜ := by
    exact
      AppliedModelingLib.integral_lt_measureReal_mul_add_compl_of_lt_on_of_le_on_compl
        η measurableSet_Iic (hint n) hpos
        (by
          intro v hv
          exact hlow_n v (by simpa [t] using hv))
        (by
          intro v hv
          exact hhigh_n v (by simpa [t] using hv))
  have hleft :
      η.real (Set.Iic t) =
        1 - AppliedModelingLib.Probability.upperTailMass η t := by
    have hsum :=
      AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one η t
    dsimp [AppliedModelingLib.Probability.lowerCDFMass] at hsum
    linarith
  have hright :
      η.real ((Set.Iic t)ᶜ) =
        AppliedModelingLib.Probability.upperTailMass η t := by
    simp [AppliedModelingLib.Probability.upperTailMass, Set.compl_Iic]
  rw [hclear n] at hsplit
  rw [hleft, hright] at hsplit
  simpa [t, mul_comm, mul_left_comm, mul_assoc] using hsplit

/--
The lower-location scalar inequality in PG23 Lemma 10 follows from market
clearing and a two-piece pointwise lower bound on the match probability.
-/
theorem lemma10_lower_scalar_split_of_integral_bounds
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {matchProb : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {supply : ℝ}
    (hint : ∀ n, Integrable (matchProb n) η)
    (hclear : ∀ n, ∫ v, matchProb n v ∂η = supply)
    (hpositive_right :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 < η (Set.Ioi (threshold n + ε / 2)))
    (hhigh :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n + ε / 2 < v → 1 - δ < matchProb n v)
    (hlow_nonneg :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, ¬ threshold n + ε / 2 < v → 0 ≤ matchProb n v) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      ∀ᶠ n : ℕ in atTop,
        (1 - δ) *
            AppliedModelingLib.Probability.upperTailMass
              η (threshold n + ε / 2) <
          supply := by
  intro ε δ hε hδ_pos hδ_lt_one
  filter_upwards
    [hpositive_right ε δ hε hδ_pos hδ_lt_one,
      hhigh ε δ hε hδ_pos hδ_lt_one,
      hlow_nonneg ε δ hε hδ_pos hδ_lt_one] with n hpos hhigh_n hlow_n
  let t : ℝ := threshold n + ε / 2
  have hsplit :
      (1 - δ) * η.real (Set.Ioi t) <
        ∫ v, matchProb n v ∂η := by
    exact
      AppliedModelingLib.measureReal_mul_lt_integral_of_lt_on_of_nonneg_on_compl
        η measurableSet_Ioi (hint n) hpos
        (by
          intro v hv
          exact hhigh_n v (by simpa [t] using hv))
        (by
          intro v hv
          exact hlow_n v (by simpa [t] using hv))
  rw [hclear n] at hsplit
  simpa [t, AppliedModelingLib.Probability.upperTailMass] using hsplit

/--
Nonstrict upper-location scalar inequality in PG23 Lemma 10 from market
clearing and a two-piece pointwise upper bound.
-/
theorem lemma10_upper_scalar_split_le_of_integral_bounds
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {matchProb : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {supply : ℝ}
    (hint : ∀ n, Integrable (matchProb n) η)
    (hclear : ∀ n, ∫ v, matchProb n v ∂η = supply)
    (hlow :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, v ≤ threshold n - ε / 2 → matchProb n v ≤ δ)
    (hhigh :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n - ε / 2 < v → matchProb n v ≤ 1) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      ∀ᶠ n : ℕ in atTop,
        supply ≤
          (1 -
              AppliedModelingLib.Probability.upperTailMass
                η (threshold n - ε / 2)) * δ +
            AppliedModelingLib.Probability.upperTailMass
              η (threshold n - ε / 2) := by
  intro ε δ hε hδ_pos hδ_lt_one
  filter_upwards
    [hlow ε δ hε hδ_pos hδ_lt_one,
      hhigh ε δ hε hδ_pos hδ_lt_one] with n hlow_n hhigh_n
  let t : ℝ := threshold n - ε / 2
  have hsplit :
      ∫ v, matchProb n v ∂η ≤
        δ * η.real (Set.Iic t) +
          (1 : ℝ) * η.real (Set.Iic t)ᶜ := by
    exact
      AppliedModelingLib.integral_le_measureReal_mul_add_compl_of_le_on_of_le_on_compl
        η measurableSet_Iic (hint n)
        (by
          intro v hv
          exact hlow_n v (by simpa [t] using hv))
        (by
          intro v hv
          exact hhigh_n v (by simpa [t] using hv))
  have hleft :
      η.real (Set.Iic t) =
        1 - AppliedModelingLib.Probability.upperTailMass η t := by
    have hsum :=
      AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one η t
    dsimp [AppliedModelingLib.Probability.lowerCDFMass] at hsum
    linarith
  have hright :
      η.real ((Set.Iic t)ᶜ) =
        AppliedModelingLib.Probability.upperTailMass η t := by
    simp [AppliedModelingLib.Probability.upperTailMass, Set.compl_Iic]
  rw [hclear n] at hsplit
  rw [hleft, hright] at hsplit
  simpa [t, mul_comm, mul_left_comm, mul_assoc] using hsplit

/--
Nonstrict lower-location scalar inequality in PG23 Lemma 10 from market
clearing and a two-piece pointwise lower bound.
-/
theorem lemma10_lower_scalar_split_le_of_integral_bounds
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {matchProb : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {supply : ℝ}
    (hint : ∀ n, Integrable (matchProb n) η)
    (hclear : ∀ n, ∫ v, matchProb n v ∂η = supply)
    (hhigh :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n + ε / 2 < v → 1 - δ ≤ matchProb n v)
    (hlow_nonneg :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, ¬ threshold n + ε / 2 < v → 0 ≤ matchProb n v) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      ∀ᶠ n : ℕ in atTop,
        (1 - δ) *
            AppliedModelingLib.Probability.upperTailMass
              η (threshold n + ε / 2) ≤
          supply := by
  intro ε δ hε hδ_pos hδ_lt_one
  filter_upwards
    [hhigh ε δ hε hδ_pos hδ_lt_one,
      hlow_nonneg ε δ hε hδ_pos hδ_lt_one] with n hhigh_n hlow_n
  let t : ℝ := threshold n + ε / 2
  have hsplit :
      (1 - δ) * η.real (Set.Ioi t) ≤
        ∫ v, matchProb n v ∂η := by
    exact
      AppliedModelingLib.measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
        η measurableSet_Ioi (hint n)
        (by
          intro v hv
          exact hhigh_n v (by simpa [t] using hv))
        (by
          intro v hv
          exact hlow_n v (by simpa [t] using hv))
  rw [hclear n] at hsplit
  simpa [t, AppliedModelingLib.Probability.upperTailMass] using hsplit

/--
PG23 Lemma 10 threshold convergence from market clearing, pointwise low/high
probability bounds, and connected-support tail separation.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {matchProb : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {vS supply : ℝ}
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hint : ∀ n, Integrable (matchProb n) η)
    (hclear : ∀ n, ∫ v, matchProb n v ∂η = supply)
    (hpositive_left :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 < η (Set.Iic (threshold n - ε / 2)))
    (hupper_low :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, v ≤ threshold n - ε / 2 → matchProb n v < δ)
    (hupper_high :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n - ε / 2 < v → matchProb n v ≤ 1)
    (hpositive_right :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 < η (Set.Ioi (threshold n + ε / 2)))
    (hlower_high :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n + ε / 2 < v → 1 - δ < matchProb n v)
    (hlower_low_nonneg :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, ¬ threshold n + ε / 2 < v → 0 ≤ matchProb n v) :
    Tendsto threshold atTop (nhds vS) :=
  lemma10_threshold_tendsto_of_marketClearing_scalar_split
    (η := η) (threshold := threshold) (vS := vS) (supply := supply)
    hstrict_right hstrict_left
    (fun ε δ hε hδ_pos hδ_lt_one _hbetween =>
      lemma10_upper_scalar_split_of_integral_bounds
        (η := η) (matchProb := matchProb) (threshold := threshold)
        (supply := supply) hint hclear hpositive_left hupper_low
        hupper_high ε δ hε hδ_pos hδ_lt_one)
    (fun ε δ hε hδ_pos hδ_lt_one _hbetween =>
      lemma10_lower_scalar_split_of_integral_bounds
        (η := η) (matchProb := matchProb) (threshold := threshold)
        (supply := supply) hint hclear hpositive_right hlower_high
        hlower_low_nonneg ε δ hε hδ_pos hδ_lt_one)

/--
Nonstrict integral-split route for PG23 Lemma 10.

This removes the moving-side positive-mass premises.  The integral split only
needs weak upper and lower bounds; strictness enters through the fixed
connected-support tail separation around `vS`.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split_le
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {matchProb : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {vS supply : ℝ}
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hint : ∀ n, Integrable (matchProb n) η)
    (hclear : ∀ n, ∫ v, matchProb n v ∂η = supply)
    (hupper_low :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, v ≤ threshold n - ε / 2 → matchProb n v ≤ δ)
    (hupper_high :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n - ε / 2 < v → matchProb n v ≤ 1)
    (hlower_high :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, threshold n + ε / 2 < v → 1 - δ ≤ matchProb n v)
    (hlower_low_nonneg :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ, ¬ threshold n + ε / 2 < v → 0 ≤ matchProb n v) :
    Tendsto threshold atTop (nhds vS) :=
  lemma10_threshold_tendsto_of_marketClearing_scalar_split_le
    (η := η) (threshold := threshold) (vS := vS) (supply := supply)
    hstrict_right hstrict_left
    (fun ε δ hε hδ_pos hδ_lt_one _hbetween =>
      lemma10_upper_scalar_split_le_of_integral_bounds
        (η := η) (matchProb := matchProb) (threshold := threshold)
        (supply := supply) hint hclear hupper_low hupper_high
        ε δ hε hδ_pos hδ_lt_one)
    (fun ε δ hε hδ_pos hδ_lt_one _hbetween =>
      lemma10_lower_scalar_split_le_of_integral_bounds
        (η := η) (matchProb := matchProb) (threshold := threshold)
        (supply := supply) hint hclear hlower_high hlower_low_nonneg
        ε δ hε hδ_pos hδ_lt_one)

/--
PG23 Lemma 10 threshold convergence for the concrete shared-cutoff
cutoff-crossing probability, deriving the global `0 ≤ p ≤ 1` parts of the
integral split from probability semantics.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split_cutoff_probability_bounds
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hint :
      ∀ n, Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n)) η)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hpositive_left :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 <
            η (Set.Iic
              (cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n - ε / 2)))
    (hupper_low :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            v ≤
              cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n - ε / 2 →
              AppliedModelingLib.Matching.cutoffCrossingProbability
                (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
                (fun _ => cutoff n) < δ)
    (hpositive_right :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 <
            η (Set.Ioi
              (cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + ε / 2)))
    (hlower_high :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + ε / 2 < v →
              1 - δ <
                AppliedModelingLib.Matching.cutoffCrossingProbability
                  (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
                  (fun _ => cutoff n)) :
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) := by
  refine
    lemma10_threshold_tendsto_of_marketClearing_integral_split
      (η := η)
      (matchProb := fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      (threshold := fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      (vS := vS) (supply := supply)
      hstrict_right hstrict_left hint hclear hpositive_left hupper_low ?_
      hpositive_right hlower_high ?_
  · intro ε δ hε hδ hδ_lt_one
    filter_upwards with n v hv
    haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
    exact
      AppliedModelingLib.Matching.cutoffCrossingProbability_le_one
        (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
        (fun _ => cutoff n)
  · intro ε δ hε hδ hδ_lt_one
    filter_upwards with n v hv
    exact
      AppliedModelingLib.Matching.cutoffCrossingProbability_nonneg
        (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
        (fun _ => cutoff n)

/--
PG23 Lemma 10 threshold convergence from market clearing and maximum
concentration, deriving the strict low/high pointwise split bounds from the
expected-maximum concentration hypothesis.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split_expected_max
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc :
      AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw))
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hint :
      ∀ n, Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n)) η)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hpositive_left :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 <
            η (Set.Iic
              (cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n - ε / 2)))
    (hpositive_right :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          0 <
            η (Set.Ioi
              (cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + ε / 2))) :
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) := by
  refine
    lemma10_threshold_tendsto_of_marketClearing_integral_split_cutoff_probability_bounds
      (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
      (vS := vS) (supply := supply)
      hprob hstrict_right hstrict_left hint hclear hpositive_left ?_
      hpositive_right ?_
  · intro ε δ hε hδ_pos hδ_lt_one
    have hε3 : 0 < ε / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (ε / 3) < δ :=
      hconc (ε / 3) hε3 (isOpen_Iio.mem_nhds hδ_pos)
    filter_upwards [hdev] with n hn v hv
    haveI : MeasureTheory.IsFiniteMeasure (sampleLaw n) := by
      haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
      infer_instance
    have hsep :
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n +
            ε / 3 ≤
          cutoff n - v := by
      linarith
    exact
      lt_of_le_of_lt
        (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
          (sampleLaw n) hsep)
        hn
  · intro ε δ hε hδ_pos hδ_lt_one
    have hε3 : 0 < ε / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (ε / 3) < δ :=
      hconc (ε / 3) hε3 (isOpen_Iio.mem_nhds hδ_pos)
    filter_upwards [hdev] with n hn v hv
    haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
    have hsep :
        cutoff n - v <
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            ε / 3 := by
      linarith
    have hfail_lt :
        1 -
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => cutoff n) <
          δ :=
      lt_of_le_of_lt
        (AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
          (sampleLaw n) hε3 hsep)
        hn
    linarith

/--
Nonstrict shared-cutoff probability route for PG23 Lemma 10, with the
probability-side `0 ≤ p ≤ 1` bounds derived from measure semantics.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split_cutoff_probability_bounds_le
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hint :
      ∀ n, Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n)) η)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hupper_low :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            v ≤
              cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n - ε / 2 →
              AppliedModelingLib.Matching.cutoffCrossingProbability
                (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
                (fun _ => cutoff n) ≤ δ)
    (hlower_high :
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + ε / 2 < v →
              1 - δ ≤
                AppliedModelingLib.Matching.cutoffCrossingProbability
                  (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
                  (fun _ => cutoff n)) :
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) := by
  refine
    lemma10_threshold_tendsto_of_marketClearing_integral_split_le
      (η := η)
      (matchProb := fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      (threshold := fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      (vS := vS) (supply := supply)
      hstrict_right hstrict_left hint hclear hupper_low ?_
      hlower_high ?_
  · intro ε δ hε hδ hδ_lt_one
    filter_upwards with n v hv
    haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
    exact
      AppliedModelingLib.Matching.cutoffCrossingProbability_le_one
        (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
        (fun _ => cutoff n)
  · intro ε δ hε hδ hδ_lt_one
    filter_upwards with n v hv
    exact
      AppliedModelingLib.Matching.cutoffCrossingProbability_nonneg
        (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
        (fun _ => cutoff n)

/--
PG23 Lemma 10 threshold convergence from market clearing and maximum
concentration, with no moving-side-mass assumptions.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split_expected_max_no_side_mass
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc :
      AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw))
    (hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < supply)
    (hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        supply < AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2))
    (hint :
      ∀ n, Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n)) η)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply) :
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) := by
  refine
    lemma10_threshold_tendsto_of_marketClearing_integral_split_cutoff_probability_bounds_le
      (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
      (vS := vS) (supply := supply)
      hprob hstrict_right hstrict_left hint hclear ?_ ?_
  · intro ε δ hε hδ_pos hδ_lt_one
    have hε3 : 0 < ε / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (ε / 3) < δ :=
      hconc (ε / 3) hε3 (isOpen_Iio.mem_nhds hδ_pos)
    filter_upwards [hdev] with n hn v hv
    haveI : MeasureTheory.IsFiniteMeasure (sampleLaw n) := by
      haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
      infer_instance
    have hsep :
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n +
            ε / 3 ≤
          cutoff n - v := by
      linarith
    exact
      le_of_lt
        (lt_of_le_of_lt
          (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
            (sampleLaw n) hsep)
          hn)
  · intro ε δ hε hδ_pos hδ_lt_one
    have hε3 : 0 < ε / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (ε / 3) < δ :=
      hconc (ε / 3) hε3 (isOpen_Iio.mem_nhds hδ_pos)
    filter_upwards [hdev] with n hn v hv
    haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
    have hsep :
        cutoff n - v <
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            ε / 3 := by
      linarith
    have hfail_lt :
        1 -
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => cutoff n) <
          δ :=
      lt_of_le_of_lt
        (AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
          (sampleLaw n) hε3 hsep)
        hn
    linarith

/--
PG23 Lemma 10 threshold convergence from source-shaped supply cutoff data.

The strict tail separation around `vS` is derived from the fact that `vS`
clears the supply in the value distribution and every one-sided neighborhood
of `vS` has positive mass.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_integral_split_expected_max_supply_cutoff
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc :
      AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hint :
      ∀ n, Integrable
        (fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n)) η)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply) :
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) :=
  lemma10_threshold_tendsto_of_marketClearing_integral_split_expected_max_no_side_mass
    (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
    (vS := vS) (supply := supply)
    hprob hconc
    (hsupply.strict_right_tail_of_positive_interval hmass)
    (hsupply.strict_left_tail_of_positive_interval hmass)
    hint hclear

/--
PG23 Lemma 10 threshold convergence from source-shaped supply cutoff data and
market clearing.  Integrability of the cutoff-crossing probability over values
is derived from monotonicity and boundedness of probabilities.
-/
theorem lemma10_threshold_tendsto_of_marketClearing_expected_max_supply_cutoff
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc :
      AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply) :
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) :=
  lemma10_threshold_tendsto_of_marketClearing_integral_split_expected_max_supply_cutoff
    (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
    (vS := vS) (supply := supply)
    hprob hconc hsupply hmass
    (fun n => by
      haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
      exact
        AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (sampleLaw n) η (Finset.univ : Finset (Fin (n + 1)))
          (fun _ => cutoff n))
    hclear

/--
Source-style eventual version of the PG23 Theorem 1 probability conclusion.
-/
def theorem1_wisdomProbabilityEventualConclusion
    (polyMatch monoMatch : ℕ → ℝ → ℝ) (vS : ℝ) : Prop :=
  (∀ v ε, v < vS → 0 < ε →
    ∀ᶠ m : ℕ in atTop, polyMatch m v < ε) ∧
  (∀ v ε, vS < v → 0 < ε →
    ∀ᶠ m : ℕ in atTop, 1 - ε < polyMatch m v) ∧
  (∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)

/--
Theorem 1 appendix-style error certificate.  The remaining analytic proof
must derive the low/high polyculture error bounds from the maximum-order
threshold lemma; monoculture invariance is the equal-cutoff consequence for
the shared-noise model.
-/
structure Theorem1WisdomErrorCertificate
    (polyMatch monoMatch : ℕ → ℝ → ℝ) (vS : ℝ) where
  lowError : ℕ → ℝ
  highError : ℕ → ℝ
  lowError_tendsto_zero : Tendsto lowError atTop (nhds 0)
  highError_tendsto_zero : Tendsto highError atTop (nhds 0)
  low_value_bound :
    ∀ v, v < vS →
      ∀ᶠ m : ℕ in atTop, polyMatch m v ≤ lowError m
  high_value_bound :
    ∀ v, vS < v →
      ∀ᶠ m : ℕ in atTop, 1 - highError m ≤ polyMatch m v
  monoculture_invariant :
    ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v

/--
PG23 Theorem 1 source-style probability conclusion from the visible error
certificate.
-/
theorem theorem1_wisdomProbability_eventual_bounds_of_error_certificate
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (cert : Theorem1WisdomErrorCertificate polyMatch monoMatch vS) :
    theorem1_wisdomProbabilityEventualConclusion polyMatch monoMatch vS := by
  constructor
  · intro v ε hv hε
    have hsmall : ∀ᶠ m : ℕ in atTop, cert.lowError m < ε :=
      cert.lowError_tendsto_zero (isOpen_Iio.mem_nhds hε)
    filter_upwards [cert.low_value_bound v hv, hsmall] with m hbound herr
    exact lt_of_le_of_lt hbound herr
  · constructor
    · intro v ε hv hε
      have hsmall : ∀ᶠ m : ℕ in atTop, cert.highError m < ε :=
        cert.highError_tendsto_zero (isOpen_Iio.mem_nhds hε)
      filter_upwards [cert.high_value_bound v hv, hsmall] with m hbound herr
      have hstrict : 1 - ε < 1 - cert.highError m := by
        linarith
      exact lt_of_lt_of_le hstrict hbound
    · exact cert.monoculture_invariant

/--
Theorem 1 probability part in source-style eventual form: the polyculture
probability is eventually below any epsilon for low values and eventually
above `1 - epsilon` for high values, while monoculture is invariant in the
number of firms.
-/
theorem theorem1_wisdomProbability_eventually_bounds
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (h : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ m : ℕ in atTop, polyMatch m v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ m : ℕ in atTop, 1 - ε < polyMatch m v) ∧
    (∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) := by
  constructor
  · intro v ε hv hε
    exact (h.1 v hv) (isOpen_Iio.mem_nhds hε)
  · constructor
    · intro v ε hv hε
      have hmem : (1 : ℝ) ∈ Set.Ioi (1 - ε) := by
        simp
        linarith
      exact (h.2.1 v hv) (isOpen_Ioi.mem_nhds hmem)
    · exact h.2.2

/--
PG23 Definition 1 bridge: the paper's `X^(m)` maximum-order statistic is the
top order statistic of a nonempty finite noise sample.
-/
noncomputable def definition1_maximumOrderStatistic {m : ℕ} [NeZero m]
    (noise : Fin m → ℝ) : ℝ :=
  AppliedModelingLib.Probability.upperOrderStatistic noise
    (AppliedModelingLib.Matching.topSampleRank (n := m))

/--
For a shared cutoff `P`, the paper event `v + X^(m) > P` is equivalent to
some polyculture noisy score crossing `P`.
-/
theorem definition1_noisyScore_crosses_shared_cutoff_iff
    {m : ℕ} [NeZero m] (noise : Fin m → ℝ) (v P : ℝ) :
    (∃ c : Fin m, P < AppliedModelingLib.Matching.noisyScore v noise c) ↔
      P - v < definition1_maximumOrderStatistic noise := by
  simpa [definition1_maximumOrderStatistic] using
    AppliedModelingLib.Matching.exists_constant_cutoff_noisyScore_iff_topOrderStatistic_gt
      noise v P

/--
Probability version of the Definition 1 bridge: under a shared cutoff, the
polyculture match event has the same probability as the maximum-order-statistic
tail event.
-/
theorem definition1_sharedCutoff_matchProbability_eq_topOrderCrossingProbability
    {m : ℕ} [NeZero m]
    (noiseLaw : Measure (Fin m → ℝ)) (v P : ℝ) :
    AppliedModelingLib.Matching.cutoffCrossingProbability noiseLaw
        (Finset.univ : Finset (Fin m)) v (fun _ => P) =
      AppliedModelingLib.Matching.topOrderCrossingProbability noiseLaw (P - v) :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_eq_topOrderCrossingProbability
    noiseLaw v P

/--
PG23 Definition 2, reusable form: the maximum order statistic concentrates
around the supplied center sequence.  In the paper, the center is
`E[X^(n)]`.
-/
abbrev maximumOrderStatisticConcentrating
    (sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ))
    (center : ℕ → ℝ) : Prop :=
  AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw center

/--
PG23 Definition 2 in the source's expected-maximum form: the maximum order
statistic concentrates around `E[X^(n)]`.
-/
abbrev maximumOrderStatisticConcentratingAroundExpected
    (sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)) : Prop :=
  maximumOrderStatisticConcentrating sampleLaw
    (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw)

/--
PG23 Definition 2 as a predicate on the paper's noise law.  The integrability
clause records the finite-expectation domain implicit in the source notation
`E[X^(n)]`; the second clause is the corresponding convergence in probability.
-/
def pg23MaximumConcentratingNoiseLaw
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] : Prop :=
  (∀ n : ℕ, Integrable
    (fun sample : Fin (n + 1) → ℝ =>
      AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
    (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))) ∧
  maximumOrderStatisticConcentratingAroundExpected
    (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))

/--
Chebyshev bridge to PG23 Definition 2.  If a variance bound for the maximum
order statistic tends to zero and supplies the usual Chebyshev tail estimate,
then the paper's maximum-concentration condition follows.
-/
theorem maximumOrderStatisticConcentratingAroundExpected_of_chebyshev_variance_bound
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound : ℕ → ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2) :
    maximumOrderStatisticConcentratingAroundExpected sampleLaw :=
  AppliedModelingLib.Probability.TopOrderDeviationConcentrating.of_chebyshev_bound
    hvariance_zero hchebyshev

/--
Variance-bound bridge to PG23 Definition 2.  The paper-facing input is an
eventual bound on the variance of the maximum order statistic itself; the
shared probability library derives Chebyshev's deviation estimate internally.
-/
theorem maximumOrderStatisticConcentratingAroundExpected_of_variance_bound
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound : ℕ → ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ varianceBound n) :
    maximumOrderStatisticConcentratingAroundExpected sampleLaw :=
  AppliedModelingLib.Probability.TopOrderDeviationConcentrating.of_variance_bound
    (sampleLaw := sampleLaw)
    (varianceBound := varianceBound)
    (fun n => by
      letI : IsProbabilityMeasure (sampleLaw n) := hprob n
      infer_instance)
    hvariance_zero hmem hvariance_bound

/--
PG23 Lemma 10 low-value threshold step: if the shared cutoff threshold is
eventually above the maximum-order-statistic center by a fixed positive gap,
then the polyculture crossing probability tends to zero.
-/
theorem lemma10_lowValue_threshold_probability_tendsto_zero
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center threshold : ℕ → ℝ}
    (hfinite : ∀ n, MeasureTheory.IsFiniteMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw center)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ᶠ n : ℕ in atTop, center n + ε ≤ threshold n) :
    Tendsto
      (fun n : ℕ =>
        AppliedModelingLib.Matching.topOrderCrossingProbability
          (sampleLaw n) (threshold n))
      atTop (nhds 0) :=
  AppliedModelingLib.Probability.topOrderCrossingProbability_tendsto_zero_of_eventually_center_add_le
    hfinite hconc hε hsep

/--
PG23 Lemma 10 high-value threshold step: if the shared cutoff threshold is
eventually below the maximum-order-statistic center by a fixed positive gap,
then the failure-to-cross probability tends to zero.
-/
theorem lemma10_highValue_failure_probability_tendsto_zero
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center threshold : ℕ → ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw center)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ᶠ n : ℕ in atTop, threshold n < center n - ε) :
    Tendsto
      (fun n : ℕ =>
        1 - AppliedModelingLib.Matching.topOrderCrossingProbability
          (sampleLaw n) (threshold n))
      atTop (nhds 0) :=
  AppliedModelingLib.Probability.one_sub_topOrderCrossingProbability_tendsto_zero_of_eventually_lt_center_sub
    hprob hconc hε hsep

/--
PG23 Theorem 1 probability route from Lemma 10: once the polyculture threshold
`P_poly - E[X^(m)]` converges to `vS`, maximum concentration gives the source
low-value and high-value convergence claims.
-/
theorem theorem1_wisdomProbability_of_max_concentration_threshold
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw center)
    (hthreshold :
      Tendsto (fun n : ℕ => cutoff n - center n) atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.topOrderCrossingProbability
          (sampleLaw n) (cutoff n - v))
      monoMatch vS := by
  refine ⟨?_, ?_, hmono⟩
  · intro v hv
    let gap : ℝ := (vS - v) / 2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    have htarget : v + gap < vS := by
      dsimp [gap]
      linarith
    have hnear :
        ∀ᶠ n : ℕ in atTop, v + gap < cutoff n - center n :=
      hthreshold (isOpen_Ioi.mem_nhds htarget)
    have hsep :
        ∀ᶠ n : ℕ in atTop, center n + gap ≤ cutoff n - v := by
      filter_upwards [hnear] with n hn
      linarith
    exact
      lemma10_lowValue_threshold_probability_tendsto_zero
        (sampleLaw := sampleLaw)
        (center := center)
        (threshold := fun n : ℕ => cutoff n - v)
        (fun n => by
          haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
          infer_instance)
        hconc hgap_pos hsep
  · intro v hv
    let gap : ℝ := (v - vS) / 2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    have htarget : vS < v - gap := by
      dsimp [gap]
      linarith
    have hnear :
        ∀ᶠ n : ℕ in atTop, cutoff n - center n < v - gap :=
      hthreshold (isOpen_Iio.mem_nhds htarget)
    have hsep :
        ∀ᶠ n : ℕ in atTop, cutoff n - v < center n - gap := by
      filter_upwards [hnear] with n hn
      linarith
    have hfail :
        Tendsto
          (fun n : ℕ =>
            1 -
              AppliedModelingLib.Matching.topOrderCrossingProbability
                (sampleLaw n) (cutoff n - v))
          atTop (nhds 0) :=
      lemma10_highValue_failure_probability_tendsto_zero
        (sampleLaw := sampleLaw)
        (center := center)
        (threshold := fun n : ℕ => cutoff n - v)
        hprob hconc hgap_pos hsep
    have hsum :
        Tendsto
          (fun n : ℕ =>
            1 - (1 -
              AppliedModelingLib.Matching.topOrderCrossingProbability
                (sampleLaw n) (cutoff n - v)))
          atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hfail
    simpa using hsum

/--
Expected-maximum version of the PG23 Theorem 1 probability route.  This is the
source-shaped specialization where the threshold gap is
`P_poly - E[X^(m)]`.
-/
theorem theorem1_wisdomProbability_of_expected_max_concentration_threshold
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.topOrderCrossingProbability
          (sampleLaw n) (cutoff n - v))
      monoMatch vS :=
  theorem1_wisdomProbability_of_max_concentration_threshold
    (sampleLaw := sampleLaw)
    (center := AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw)
    (cutoff := cutoff)
    hprob hconc hthreshold hmono

/--
Expected-maximum threshold route in the paper's shared-cutoff probability
form.  This packages Definition 1's event bridge into Theorem 1, so the
conclusion talks directly about `Pr[v + X_c > P_poly]` under a common
polyculture cutoff rather than an abstract top-order crossing probability.
-/
theorem theorem1_wisdomProbability_of_expected_max_shared_cutoff_threshold
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS := by
  have htop :
      theorem1_wisdomProbabilityConclusion
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.topOrderCrossingProbability
            (sampleLaw n) (cutoff n - v))
        monoMatch vS :=
    theorem1_wisdomProbability_of_expected_max_concentration_threshold
      (sampleLaw := sampleLaw)
      (cutoff := cutoff)
      hprob hconc hthreshold hmono
  refine ⟨?_, ?_, htop.2.2⟩
  · intro v hv
    simpa [AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_eq_topOrderCrossingProbability]
      using htop.1 v hv
  · intro v hv
    simpa [AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_eq_topOrderCrossingProbability]
      using htop.2.1 v hv

/--
PG23 Theorem 1 shared-cutoff probability route from a Chebyshev variance
bound.  This packages the common Example 1-style proof path: variance of the
maximum order statistic tends to zero, hence maximum concentration, hence the
polyculture step-function limit once the expected-maximum cutoff threshold
converges to `vS`.
-/
theorem theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_threshold
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS :=
  theorem1_wisdomProbability_of_expected_max_shared_cutoff_threshold
    (sampleLaw := sampleLaw)
    (cutoff := cutoff)
    hprob
      (maximumOrderStatisticConcentratingAroundExpected_of_chebyshev_variance_bound
        hvariance_zero hchebyshev)
    hthreshold hmono

/--
PG23 Theorem 1 shared-cutoff probability route from Chebyshev and the source
one-sided threshold-location estimates.  This exposes Lemma 10 part (iii) as
the two inequalities proved by the market-clearing/quantile argument rather
than a single opaque convergence input.
-/
theorem theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_one_sided_threshold
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold_upper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            vS < ε)
    (hthreshold_lower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n) <
            ε)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS :=
  theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_threshold
    hprob hvariance_zero hchebyshev
    (lemma10_threshold_tendsto_of_one_sided_eventual_bounds
      hthreshold_upper hthreshold_lower)
    hmono

/--
PG23 Theorem 1 shared-cutoff probability route from Chebyshev and the source
market-clearing proof of Lemma 10.  The moving polyculture threshold
`P_poly - E[X^(m)]` is located by supply clearing at `vS`, local positive mass
around `vS`, and the polyculture market-clearing equality.
-/
theorem theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS := by
  have hconc :
      AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw) :=
    maximumOrderStatisticConcentratingAroundExpected_of_chebyshev_variance_bound
      hvariance_zero hchebyshev
  have hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS) :=
    lemma10_threshold_tendsto_of_marketClearing_expected_max_supply_cutoff
      (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
      (vS := vS) (supply := supply)
      hprob hconc hsupply hmass hclear
  exact
    theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_threshold
      hprob hvariance_zero hchebyshev hthreshold hmono

/--
PG23 Theorem 1 shared-cutoff probability route directly from Definition 2
maximum concentration and the source market-clearing proof of Lemma 10.  This
is the paper-facing version of the route; the Chebyshev/variance lemma remains
an optional way to prove Definition 2 for concrete distributions.
-/
theorem theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS supply : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS := by
  have hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS) :=
    lemma10_threshold_tendsto_of_marketClearing_expected_max_supply_cutoff
      (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
      (vS := vS) (supply := supply)
      hprob hconc hsupply hmass hclear
  exact
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_threshold
      (sampleLaw := sampleLaw) (cutoff := cutoff)
      hprob hconc hthreshold hmono

/--
PG23 Theorem 1 shared-cutoff probability route with monoculture invariance
derived from a common scalar monoculture cutoff.  In the source monoculture
model a named firm's crossing event is one-dimensional; if the scalar
monoculture cutoff is the same across market sizes, Lean derives the
`monoMatch` invariance premise used by the generic Theorem 1 route.
-/
theorem theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {varianceBound polyCutoff monoCutoff : ℕ → ℝ}
    {vS supply : ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS := by
  have hprob :
      ∀ n : ℕ,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := by
    intro n
    infer_instance
  have hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) := by
    intro v m n
    rw [
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
      hmono_cutoff m n]
  exact
    theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η)
      (sampleLaw := fun n : ℕ =>
        Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
      (varianceBound := varianceBound)
      (cutoff := polyCutoff)
      (monoMatch := fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      (vS := vS) (supply := supply)
      hprob hvariance_zero hchebyshev hsupply hmass hclear hmono

/--
PG23 Theorem 1 shared-cutoff probability route directly from Definition 2,
with monoculture invariance derived from a common scalar monoculture cutoff.
-/
theorem theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {polyCutoff monoCutoff : ℕ → ℝ}
    {vS supply : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n) :
    theorem1_wisdomProbabilityConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS := by
  have hprob :
      ∀ n : ℕ,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := by
    intro n
    infer_instance
  have hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) := by
    intro v m n
    rw [
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
      hmono_cutoff m n]
  exact
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η)
      (sampleLaw := fun n : ℕ =>
        Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
      (cutoff := polyCutoff)
      (monoMatch := fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      (vS := vS) (supply := supply)
      hprob hconc hsupply hmass hclear hmono

/--
PG23 Theorem 1 full route from the source shared-cutoff Chebyshev argument.
The probability part is proved from maximum-order-statistic variance control;
the welfare part remains the explicit source welfare bridge.
-/
theorem theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_and_welfare
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare
    (theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_threshold
      hprob hvariance_zero hchebyshev hthreshold hmono)
    hwelfare

/--
PG23 Theorem 1 full route from Chebyshev, source one-sided threshold-location
estimates, and the explicit welfare bridge.
-/
theorem theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_one_sided_and_welfare
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold_upper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            vS < ε)
    (hthreshold_lower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n) <
            ε)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare
    (theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_one_sided_threshold
      hprob hvariance_zero hchebyshev hthreshold_upper
      hthreshold_lower hmono)
    hwelfare

/--
PG23 Theorem 1 full route from Chebyshev and the source market-clearing proof
of Lemma 10.  The probability conclusion no longer exposes the intermediate
one-sided threshold-location inequalities; those are derived from the supply
cutoff, local positive mass, and market-clearing equality.
-/
theorem theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_and_welfare
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS supply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare
    (theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η) (sampleLaw := sampleLaw) (varianceBound := varianceBound)
      (cutoff := cutoff) (monoMatch := monoMatch) (vS := vS)
      (supply := supply)
      hprob hvariance_zero hchebyshev hsupply hmass hclear hmono)
    hwelfare

/--
PG23 Theorem 1 full route from Definition 2 maximum concentration and the
source market-clearing proof of Lemma 10.  The probability conclusion uses
the paper's concentration hypothesis directly; the welfare conclusion remains
the explicit welfare bridge.
-/
theorem theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_and_welfare
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS supply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => cutoff n) ∂η = supply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      monoMatch vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare
    (theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η) (sampleLaw := sampleLaw) (cutoff := cutoff)
      (monoMatch := monoMatch) (vS := vS) (supply := supply)
      hprob hconc hsupply hmass hclear hmono)
    hwelfare

/--
PG23 Theorem 1 full route with monoculture invariance derived from a common
scalar monoculture cutoff.  This combines the common-cutoff probability route
with the existing explicit welfare bridge.
-/
theorem theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_welfare
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {varianceBound polyCutoff monoCutoff : ℕ → ℝ}
    {vS supply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare
    (theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
      η baseNoiseLaw topFirm hvariance_zero hchebyshev hsupply hmass
      hclear hmono_cutoff)
    hwelfare

/--
PG23 Theorem 1 full route with monoculture invariance derived from a common
scalar monoculture cutoff, using Definition 2 maximum concentration directly.
-/
theorem theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_welfare
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {polyCutoff monoCutoff : ℕ → ℝ}
    {vS supply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (hwelfare :
      theorem1_wisdomFirmWelfareConclusion
        polyWelfare monoWelfare optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_probability_and_welfare
    (theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
      η baseNoiseLaw topFirm hconc hsupply hmass hclear hmono_cutoff)
    hwelfare

/--
PG23 Theorem 1 full route with common monoculture cutoff and explicit integral
welfare semantics.  Compared with the generic integral-welfare route, this
derives the monoculture invariance clause from the concrete iid single-cutoff
model instead of exposing it as a premise.
-/
theorem theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_integral_welfare
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {varianceBound polyCutoff monoCutoff : ℕ → ℝ}
    {vS supply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare := by
  have hprob :
      ∀ n : ℕ,
        IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := by
    intro n
    infer_instance
  have hstep :
      theorem1_wisdomProbabilityConclusion
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n))
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
        vS :=
    theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
      η baseNoiseLaw topFirm hvariance_zero hchebyshev hsupply hmass
      hclear hmono_cutoff
  have hpoly_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun v : ℝ =>
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n)) η := by
    intro n
    haveI : IsFiniteMeasure
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := by
      haveI : IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := hprob n
      infer_instance
    exact
      AppliedModelingLib.Matching.cutoffCrossingProbability_value_mul_aestronglyMeasurable
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
        η (Finset.univ : Finset (Fin (n + 1)))
        (fun _ => polyCutoff n)
  have hpoly_prob_bounds :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        0 ≤
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∧
          AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ≤ 1 := by
    intro n
    filter_upwards with v
    haveI : IsProbabilityMeasure
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := hprob n
    exact
      ⟨AppliedModelingLib.Matching.cutoffCrossingProbability_nonneg
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n),
        AppliedModelingLib.Matching.cutoffCrossingProbability_le_one
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n)⟩
  exact
    theorem1_wisdomFull_of_probability_and_welfare hstep
      (theorem1_wisdomFirmWelfare_of_probability_step_integral
        (η := η)
        (polyMatch := fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n))
        (monoMatch := fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
        (vS := vS)
        hstep hno_atom habs_integrable hpoly_meas hpoly_prob_bounds
        hpolyWelfare_eq hmonoWelfare_eq hoptimalWelfare_eq
        hmono_suboptimal)

/--
PG23 Theorem 1 full route with common monoculture cutoff and explicit integral
welfare semantics, using Definition 2 maximum concentration directly.
-/
theorem theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_integral_welfare
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {polyCutoff monoCutoff : ℕ → ℝ}
    {vS supply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare := by
  have hprob :
      ∀ n : ℕ,
        IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := by
    intro n
    infer_instance
  have hstep :
      theorem1_wisdomProbabilityConclusion
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n))
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
        vS :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
      η baseNoiseLaw topFirm hconc hsupply hmass hclear hmono_cutoff
  have hpoly_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun v : ℝ =>
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n)) η := by
    intro n
    haveI : IsFiniteMeasure
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := by
      haveI : IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := hprob n
      infer_instance
    exact
      AppliedModelingLib.Matching.cutoffCrossingProbability_value_mul_aestronglyMeasurable
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
        η (Finset.univ : Finset (Fin (n + 1)))
        (fun _ => polyCutoff n)
  have hpoly_prob_bounds :
      ∀ n : ℕ, ∀ᵐ v : ℝ ∂η,
        0 ≤
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∧
          AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ≤ 1 := by
    intro n
    filter_upwards with v
    haveI : IsProbabilityMeasure
        (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) := hprob n
    exact
      ⟨AppliedModelingLib.Matching.cutoffCrossingProbability_nonneg
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n),
        AppliedModelingLib.Matching.cutoffCrossingProbability_le_one
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n)⟩
  exact
    theorem1_wisdomFull_of_probability_and_welfare hstep
      (theorem1_wisdomFirmWelfare_of_probability_step_integral
        (η := η)
        (polyMatch := fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n))
        (monoMatch := fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
        (vS := vS)
        hstep hno_atom habs_integrable hpoly_meas hpoly_prob_bounds
        hpolyWelfare_eq hmonoWelfare_eq hoptimalWelfare_eq
        hmono_suboptimal)

/--
PG23 Lemma 10 in the paper's three-part threshold form.  The threshold is
`P_poly - E[X^(m)]`: below it by a fixed margin, matching is unlikely; above
it by a fixed margin, matching is likely; and the threshold converges to the
efficient value cutoff `vS`.
-/
structure Lemma10ThresholdCertificate
    (polyMatch : ℕ → ℝ → ℝ) (threshold : ℕ → ℝ) (vS : ℝ) where
  low_value_bound :
    ∀ ε δ, 0 < ε → 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        ∀ v : ℝ, v < threshold n - δ / 3 → polyMatch n v < ε
  high_value_bound :
    ∀ ε δ, 0 < ε → 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        ∀ v : ℝ, threshold n + δ / 3 < v → 1 - ε < polyMatch n v
  threshold_tendsto : Tendsto threshold atTop (nhds vS)

/--
Lemma 10 low/high bounds from maximum concentration in the source
expected-maximum shared-cutoff setting.  This proves the probability parts of
the paper's Lemma 10 from Definition 2 and records the source threshold
convergence as the remaining threshold-location input.
-/
theorem lemma10_thresholdCertificate_of_expected_max_shared_cutoff
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          cutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    Lemma10ThresholdCertificate
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      vS := by
  refine
    { low_value_bound := ?_
      high_value_bound := ?_
      threshold_tendsto := hthreshold }
  · intro ε δ hε hδ
    have hδ3 : 0 < δ / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (δ / 3) < ε :=
      hconc (δ / 3) hδ3 (isOpen_Iio.mem_nhds hε)
    filter_upwards [hdev] with n hn v hv
    haveI : MeasureTheory.IsFiniteMeasure (sampleLaw n) := by
      haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
      infer_instance
    have hsep :
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n +
            δ / 3 ≤
          cutoff n - v := by
      linarith
    exact
      lt_of_le_of_lt
        (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
          (sampleLaw n) hsep)
        hn
  · intro ε δ hε hδ
    have hδ3 : 0 < δ / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (δ / 3) < ε :=
      hconc (δ / 3) hδ3 (isOpen_Iio.mem_nhds hε)
    filter_upwards [hdev] with n hn v hv
    haveI : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := hprob n
    have hsep :
        cutoff n - v <
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            δ / 3 := by
      linarith
    have hfail_le :
        1 -
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => cutoff n) <
          ε :=
      lt_of_le_of_lt
        (AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
          (sampleLaw n) hδ3 hsep)
        hn
    linarith

/--
Lemma 10 threshold certificate from the expected-maximum shared-cutoff route
and the source proof's one-sided threshold-location estimates.  This exposes
the paper's part (iii) proof obligations instead of taking threshold
convergence as a single opaque premise.
-/
theorem lemma10_thresholdCertificate_of_expected_max_shared_cutoff_one_sided_location
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hupper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            vS < ε)
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n) <
            ε) :
    Lemma10ThresholdCertificate
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      vS :=
  lemma10_thresholdCertificate_of_expected_max_shared_cutoff
    hprob hconc
    (lemma10_threshold_tendsto_of_one_sided_eventual_bounds
      hupper hlower)

/--
Lemma 10 threshold certificate from maximum concentration plus the source
market-clearing tail-bracket obligations.

This is a sharper source-facing route than taking either threshold
convergence or one-sided location estimates directly: the remaining hypotheses
are the two shifted upper-tail brackets produced by the integral-splitting and
connected-support part of the paper proof.
-/
theorem lemma10_thresholdCertificate_of_expected_max_shared_cutoff_tail_brackets
    (η : Measure ℝ) [MeasureTheory.IsFiniteMeasure η]
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hupper :
      ∀ ε : ℝ, 0 < ε →
        ∃ q : ℝ,
          AppliedModelingLib.Probability.upperTailMass η (vS + ε / 2) < q ∧
            ∀ᶠ n : ℕ in atTop,
              q <
                AppliedModelingLib.Probability.upperTailMass
                  η
                  (cutoff n -
                    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                      sampleLaw n - ε / 2))
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∃ q : ℝ,
          (∀ᶠ n : ℕ in atTop,
            AppliedModelingLib.Probability.upperTailMass
              η
              (cutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + ε / 2) < q) ∧
            q <
              AppliedModelingLib.Probability.upperTailMass η (vS - ε / 2)) :
    Lemma10ThresholdCertificate
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => cutoff n))
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      vS :=
  lemma10_thresholdCertificate_of_expected_max_shared_cutoff
    (sampleLaw := sampleLaw) (cutoff := cutoff) (vS := vS)
    hprob hconc
    (lemma10_threshold_tendsto_of_shifted_tail_brackets
      (η := η)
      (threshold := fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      (vS := vS)
      hupper hlower)

/--
PG23 Lemma 10 in direct source form from the expected-maximum shared-cutoff
route and the source proof's one-sided threshold-location estimates.  This
unpacks the low-value bound, high-value bound, and threshold convergence
clauses without exposing a certificate object.
-/
theorem lemma10_threePart_of_expected_max_shared_cutoff_one_sided_location
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {cutoff : ℕ → ℝ} {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentratingAroundExpected sampleLaw)
    (hupper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            vS < ε)
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n) <
            ε) :
    (∀ ε δ, 0 < ε → 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        ∀ v : ℝ,
          v <
            cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
              δ / 3 →
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => cutoff n) < ε) ∧
    (∀ ε δ, 0 < ε → 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        ∀ v : ℝ,
          cutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n +
              δ / 3 < v →
            1 - ε <
              AppliedModelingLib.Matching.cutoffCrossingProbability
                (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
                (fun _ => cutoff n)) ∧
    Tendsto
      (fun n : ℕ =>
        cutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      atTop (nhds vS) := by
  let cert :=
    lemma10_thresholdCertificate_of_expected_max_shared_cutoff_one_sided_location
      (sampleLaw := sampleLaw) (cutoff := cutoff) (vS := vS)
      hprob hconc hupper hlower
  exact
    ⟨cert.low_value_bound, cert.high_value_bound, cert.threshold_tendsto⟩

/--
Theorem 1 from the paper's Lemma 10 threshold certificate.  This mirrors the
source proof: Lemma 10 gives low/high probability bounds relative to the
moving threshold, and the threshold convergence identifies the limit as the
efficient value cutoff.
-/
theorem theorem1_wisdomProbability_eventual_of_lemma10_threshold_certificate
    {polyMatch monoMatch : ℕ → ℝ → ℝ} {threshold : ℕ → ℝ} {vS : ℝ}
    (cert : Lemma10ThresholdCertificate polyMatch threshold vS)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v) :
    theorem1_wisdomProbabilityEventualConclusion polyMatch monoMatch vS := by
  constructor
  · intro v ε hv hε
    let δ : ℝ := vS - v
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hmem : vS ∈ Set.Ioi (vS - δ / 3) := by
      simp
      linarith
    have hthreshold :
        ∀ᶠ n : ℕ in atTop, vS - δ / 3 < threshold n :=
      cert.threshold_tendsto (isOpen_Ioi.mem_nhds hmem)
    have hlow := cert.low_value_bound ε δ hε hδ
    filter_upwards [hthreshold, hlow] with n hn_threshold hn_low
    exact hn_low v (by dsimp [δ] at hn_threshold ⊢; linarith)
  · constructor
    · intro v ε hv hε
      let δ : ℝ := v - vS
      have hδ : 0 < δ := by
        dsimp [δ]
        linarith
      have hmem : vS ∈ Set.Iio (vS + δ / 3) := by
        simp
        linarith
      have hthreshold :
          ∀ᶠ n : ℕ in atTop, threshold n < vS + δ / 3 :=
        cert.threshold_tendsto (isOpen_Iio.mem_nhds hmem)
      have hhigh := cert.high_value_bound ε δ hε hδ
      filter_upwards [hthreshold, hhigh] with n hn_threshold hn_high
      exact hn_high v (by dsimp [δ] at hn_threshold ⊢; linarith)
    · exact hmono

/--
Differential-access monotonicity ingredient: when one applicant can apply to a
subset of another applicant's active colleges, their polyculture affordance
probability is weakly lower under the same cutoff vector.
-/
theorem theorem3_polycultureAffordanceProbability_mono_active
    {m : ℕ} [MeasurableSpace (Fin m → ℝ)]
    (noiseLaw : Measure (Fin m → ℝ)) [IsFiniteMeasure noiseLaw]
    {active larger : Finset (Fin m)} {v : ℝ} {cutoff : Fin m → ℝ}
    (hsubset : active ⊆ larger) :
    AppliedModelingLib.Matching.cutoffCrossingProbability noiseLaw active v cutoff ≤
      AppliedModelingLib.Matching.cutoffCrossingProbability noiseLaw larger v cutoff :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_mono_active
    noiseLaw hsubset

/--
PG23 Theorem 2, paper-facing comparison skeleton: monoculture weakly dominates
polyculture for top-choice probability, and high-value applicants eventually
have higher match probability under polyculture.
-/
structure Theorem2TopChoiceAndMatchConclusion
    (monoTop polyTop monoMatch polyMatch : ℕ → ℝ → ℝ) (vS : ℝ) : Prop where
  top_choice_mono_ge_poly :
    ∀ m v, polyTop m v ≤ monoTop m v
  high_value_poly_eventually_beats_mono :
    ∀ v, vS < v →
      ∀ᶠ m : ℕ in atTop, monoMatch m v < polyMatch m v

/--
PG23 Theorem 2, source-shaped region form.  Part (iii) of the source theorem
does not assert the eventual match-probability advantage for every value above
`vS`; it asserts it on a positive-measure interval above `vS` and below the
monoculture upper threshold.
-/
structure Theorem2TopChoiceAndMatchPositiveRegionConclusion
    (monoTop polyTop monoMatch polyMatch : ℕ → ℝ → ℝ)
    (η : Measure ℝ) (region : Set ℝ) : Prop where
  top_choice_mono_ge_poly :
    ∀ m v, polyTop m v ≤ monoTop m v
  region_positive :
    0 < η.real region
  region_poly_eventually_beats_mono :
    ∀ v ∈ region,
      ∀ᶠ m : ℕ in atTop, monoMatch m v < polyMatch m v

/--
PG23 Theorem 2 positive-region source clauses unpacked from the theorem
record.  This lets the paper-facing interface expose the three source clauses
directly rather than asking reviewers to inspect the record fields.
-/
theorem theorem2_topChoiceAndMatchPositiveRegion_source_clauses
    {monoTop polyTop monoMatch polyMatch : ℕ → ℝ → ℝ}
    {η : Measure ℝ} {region : Set ℝ}
    (h :
      Theorem2TopChoiceAndMatchPositiveRegionConclusion
        monoTop polyTop monoMatch polyMatch η region) :
    (∀ m v, polyTop m v ≤ monoTop m v) ∧
      0 < η.real region ∧
      (∀ v ∈ region,
        ∀ᶠ m : ℕ in atTop, monoMatch m v < polyMatch m v) :=
  ⟨h.top_choice_mono_ge_poly,
    h.region_positive,
    h.region_poly_eventually_beats_mono⟩

/--
PG23 Theorem 2(ii) target: every matched applicant in monoculture is matched
to their top available choice.
-/
def Theorem2MonocultureTopChoiceConclusion
    (matched topChoice : ℝ → Prop) : Prop :=
  ∀ v : ℝ, matched v → topChoice v

/--
PG23 Theorem 2(ii), source-shaped event route.  In monoculture, all active
colleges use the same score for the applicant and all cutoffs are equal.  So
if the applicant can afford any active college, their top active college is
also affordable; the source demand rule then matches them to that top choice.
-/
theorem theorem2_monocultureTopChoice_of_sharedScore_affordance
    {matched topChoice : ℝ → Prop}
    {active : ℝ → Finset College}
    {top : ℝ → College}
    {score : ℝ → College → ℝ}
    {cutoff : ℝ}
    (hmatch_affords :
      ∀ v, matched v →
        AppliedModelingLib.Matching.cutoffCrossedOn
          (active v) (score v) (fun _ : College => cutoff))
    (htop_mem : ∀ v, top v ∈ active v)
    (hshared_score :
      ∀ v c, c ∈ active v → score v c = score v (top v))
    (htop_affordable_choice :
      ∀ v, top v ∈ active v → cutoff < score v (top v) → topChoice v) :
    Theorem2MonocultureTopChoiceConclusion matched topChoice := by
  intro v hmatched
  rcases hmatch_affords v hmatched with ⟨c, hc, hcross⟩
  have htop_cross : cutoff < score v (top v) := by
    simpa [hshared_score v c hc] using hcross
  exact htop_affordable_choice v (htop_mem v) htop_cross

/--
PG23 Theorem 2 match-probability implication.  The high-value strict
polyculture advantage follows from Theorem 1's convergence to one for
polyculture, monoculture invariance in the number of firms, and the source
fact that the monoculture high-value match probability is strictly below one.
-/
theorem theorem2_topChoiceAndMatch_of_wisdomProbability
    {monoTop polyTop monoMatch polyMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (htop : ∀ m v, polyTop m v ≤ monoTop m v)
    (hwisdom : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      monoTop polyTop monoMatch polyMatch vS := by
  refine ⟨htop, ?_⟩
  intro v hv
  let mono0 : ℝ := monoMatch 0 v
  let gap : ℝ := (1 - mono0) / 2
  have hgap_pos : 0 < gap := by
    dsimp [gap, mono0]
    linarith [hmono_lt_one v hv]
  have hmem : (1 : ℝ) ∈ Set.Ioi (1 - gap) := by
    simp
    linarith
  have hpoly_event :
      ∀ᶠ m : ℕ in atTop, 1 - gap < polyMatch m v :=
    (hwisdom.2.1 v hv) (isOpen_Ioi.mem_nhds hmem)
  filter_upwards [hpoly_event] with m hm
  have hmono_eq : monoMatch m v = mono0 := by
    dsimp [mono0]
    exact hwisdom.2.2 v m 0
  have hmono_lt_threshold : mono0 < 1 - gap := by
    dsimp [gap, mono0]
    linarith [hmono_lt_one v hv]
  linarith

/--
PG23 Theorem 2 region route from Theorem 1.  On any positive-measure region
whose values are above the wisdom threshold and whose monoculture match
probability is strictly below one, Theorem 1 gives eventual strict
polyculture match advantage.
-/
theorem theorem2_topChoiceAndMatchPositiveRegion_of_wisdomProbability
    {monoTop polyTop monoMatch polyMatch : ℕ → ℝ → ℝ}
    {η : Measure ℝ} {region : Set ℝ} {vS : ℝ}
    (htop : ∀ m v, polyTop m v ≤ monoTop m v)
    (hwisdom : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lt_one : ∀ v ∈ region, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      monoTop polyTop monoMatch polyMatch η region := by
  refine ⟨htop, hregion_positive, ?_⟩
  intro v hvregion
  let mono0 : ℝ := monoMatch 0 v
  let gap : ℝ := (1 - mono0) / 2
  have hgap_pos : 0 < gap := by
    dsimp [gap, mono0]
    linarith [hmono_lt_one v hvregion]
  have hmem : (1 : ℝ) ∈ Set.Ioi (1 - gap) := by
    simp
    linarith
  have hpoly_event :
      ∀ᶠ m : ℕ in atTop, 1 - gap < polyMatch m v :=
    (hwisdom.2.1 v (hregion_above v hvregion))
      (isOpen_Ioi.mem_nhds hmem)
  filter_upwards [hpoly_event] with m hm
  have hmono_eq : monoMatch m v = mono0 := by
    dsimp [mono0]
    exact hwisdom.2.2 v m 0
  have hmono_lt_threshold : mono0 < 1 - gap := by
    dsimp [gap, mono0]
    linarith [hmono_lt_one v hvregion]
  linarith

/--
PG23 Theorem 2 source-shaped route.  The top-choice comparison is derived
from the cutoff inequality `P_mono <= P_poly` and the fact that both
top-choice probabilities are single-college crossing probabilities for the
same noise law.  The high-value overall-match comparison is then inherited
from Theorem 1 as above.
-/
theorem theorem2_topChoiceAndMatch_of_cutoffComparison_and_wisdomProbability
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoCutoff polyCutoff : ℕ → ℝ}
    {monoMatch polyMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hcutoff : ∀ m, monoCutoff m ≤ polyCutoff m)
    (hwisdom : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch polyMatch vS := by
  refine
    theorem2_topChoiceAndMatch_of_wisdomProbability
      (monoTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (polyTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (monoMatch := monoMatch) (polyMatch := polyMatch) (vS := vS)
      ?_ hwisdom hmono_lt_one
  intro m v
  haveI : MeasureTheory.IsFiniteMeasure (noiseLaw m) := by
    haveI : MeasureTheory.IsProbabilityMeasure (noiseLaw m) := hprob m
    infer_instance
  exact
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_constant_mono_cutoff
      (noiseLaw m) v (topFirm m) (hcutoff m)

/--
PG23 Theorem 2 positive-region route from the cutoff comparison.  This is the
region-valued analogue of
`theorem2_topChoiceAndMatch_of_cutoffComparison_and_wisdomProbability`: the
cutoff inequality supplies the pointwise top-choice comparison, and Theorem 1
supplies the high-value match-probability separation on any positive-measure
region above the wisdom threshold.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_cutoffComparison_and_wisdomProbability
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoCutoff polyCutoff : ℕ → ℝ}
    {monoMatch polyMatch : ℕ → ℝ → ℝ}
    {η : Measure ℝ} {region : Set ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hcutoff : ∀ m, monoCutoff m ≤ polyCutoff m)
    (hwisdom : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lt_one_region : ∀ v ∈ region, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch polyMatch η region := by
  refine
    theorem2_topChoiceAndMatchPositiveRegion_of_wisdomProbability
      (monoTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (polyTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (monoMatch := monoMatch) (polyMatch := polyMatch)
      (η := η) (region := region) (vS := vS)
      ?_ hwisdom hregion_positive hregion_above hmono_lt_one_region
  intro m v
  haveI : MeasureTheory.IsFiniteMeasure (noiseLaw m) := by
    haveI : MeasureTheory.IsProbabilityMeasure (noiseLaw m) := hprob m
    infer_instance
  exact
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_constant_mono_cutoff
      (noiseLaw m) v (topFirm m) (hcutoff m)

/--
PG23 Theorem 2 positive-region route from the paper-level cutoff comparison
and Definition 2 maximum concentration.  Compared with the integrated-access
route, this theorem consumes the already-proved Corollary 4-style cutoff
inequality as a single premise instead of restating the integral demand-gap
proof.  The monoculture strict-below-one region condition is derived from the
exact lower-CDF positivity needed by the iid single-cutoff probability formula.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_cutoffComparison_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_iid_region
    (η : Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {monoCutoff polyCutoff : ℕ → ℝ}
    {region : Set ℝ} {vS supply : ℝ}
    (hcutoff : ∀ m, monoCutoff m ≤ polyCutoff m)
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lowerCDF_pos :
      ∀ v ∈ region,
        0 <
          AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw
            (monoCutoff 0 - v)) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hprob :
      ∀ m,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) := by
    intro m
    infer_instance
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n))
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
        vS :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff
      η baseNoiseLaw topFirm hconc hsupply hmass hclear hmono_cutoff
  have hmono_lt_one_region :
      ∀ v ∈ region,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff 0) (topFirm 0) < 1 := by
    intro v hv
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_lt_one_of_lowerCDFMass_pos
        baseNoiseLaw (topFirm 0) (hmono_lowerCDF_pos v hv)
  exact
    theorem2_topChoiceAndPositiveRegion_of_cutoffComparison_and_wisdomProbability
      (noiseLaw := fun m : ℕ =>
        Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
      topFirm hprob hcutoff hwisdom hregion_positive hregion_above
      hmono_lt_one_region

/--
PG23 Theorem 2 source route from the shared-cutoff Chebyshev proof of
Theorem 1.  Theorem 1 supplies the high-value polyculture match convergence;
the cutoff comparison supplies the top-choice probability inequality.
-/
theorem theorem2_topChoiceAndMatch_of_cutoffComparison_and_chebyshev_expected_max_shared_cutoff
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoCutoff polyCutoff varianceBound : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hcutoff : ∀ m, monoCutoff m ≤ polyCutoff m)
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          polyCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      vS := by
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        monoMatch vS :=
    theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_threshold
      (sampleLaw := noiseLaw)
      (varianceBound := varianceBound)
      (cutoff := polyCutoff)
      hprob hvariance_zero hchebyshev hthreshold hmono
  exact
    theorem2_topChoiceAndMatch_of_cutoffComparison_and_wisdomProbability
      topFirm hprob hcutoff hwisdom hmono_lt_one

/--
PG23 Theorem 2 source route from aggregate demand.  The source proves the
cutoff comparison via Corollary 4: both regimes clear the same supply, the
monoculture demand curve is weakly decreasing in the scalar cutoff, and
polyculture demand is strictly larger at the polyculture cutoff.  This theorem
packages that comparison before applying the shared-cutoff Chebyshev route.
-/
theorem theorem2_topChoiceAndMatch_of_aggregate_demand_and_chebyshev_expected_max_shared_cutoff
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hstrict_at_poly :
      ∀ m, monoDemand m (polyCutoff m) < polyDemand m (polyCutoff m))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          polyCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      vS := by
  have hcutoff : ∀ m, monoCutoff m ≤ polyCutoff m := by
    intro m
    exact
      (corollary4_mono_cutoff_lt_poly_cutoff_of_same_supply
        (monoDemand := monoDemand m)
        (polyDemand := polyDemand m)
        (Pmono := monoCutoff m)
        (Ppoly := polyCutoff m)
        (supply := supply m)
        (hmono_clear m) (hpoly_clear m)
        (hmono_antitone m) (hstrict_at_poly m)).le
  exact
    theorem2_topChoiceAndMatch_of_cutoffComparison_and_chebyshev_expected_max_shared_cutoff
      (topFirm := topFirm)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (varianceBound := varianceBound)
      (monoMatch := monoMatch)
      (vS := vS)
      hprob hcutoff hvariance_zero hchebyshev hthreshold hmono
      hmono_lt_one

/--
PG23 Theorem 2 source route from aggregate demand, Chebyshev concentration,
and the source one-sided threshold-location estimates.
-/
theorem theorem2_topChoiceAndMatch_of_aggregate_demand_and_chebyshev_expected_max_shared_cutoff_one_sided
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hstrict_at_poly :
      ∀ m, monoDemand m (polyCutoff m) < polyDemand m (polyCutoff m))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold_upper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n -
            vS < ε)
    (hthreshold_lower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n) <
            ε)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      vS :=
  theorem2_topChoiceAndMatch_of_aggregate_demand_and_chebyshev_expected_max_shared_cutoff
    (topFirm := topFirm)
    (monoDemand := monoDemand) (polyDemand := polyDemand)
    (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
    (supply := supply) (varianceBound := varianceBound)
    (monoMatch := monoMatch) (vS := vS)
    hprob hmono_clear hpoly_clear hmono_antitone hstrict_at_poly
    hvariance_zero hchebyshev
    (lemma10_threshold_tendsto_of_one_sided_eventual_bounds
      hthreshold_upper hthreshold_lower)
    hmono hmono_lt_one

/--
PG23 Theorem 2 source route with the aggregate-demand strict gap derived from
the integrated applicant-level access comparison at the polyculture cutoff.
-/
theorem theorem2_topChoiceAndMatch_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold :
      Tendsto
        (fun n : ℕ =>
          polyCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
        atTop (nhds vS))
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      vS := by
  have hstrict_at_poly :
      ∀ m, monoDemand m (polyCutoff m) < polyDemand m (polyCutoff m) := by
    intro m
    exact
      corollary4_strict_demand_gap_of_pointwise_access
        μ (hmono_int m) (hpoly_int m) (hmono_eq m) (hpoly_eq m)
        (hle m) (hstrict_pos m)
  exact
    theorem2_topChoiceAndMatch_of_aggregate_demand_and_chebyshev_expected_max_shared_cutoff
      (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply) (varianceBound := varianceBound)
      (monoMatch := monoMatch) (vS := vS)
      hprob hmono_clear hpoly_clear hmono_antitone hstrict_at_poly
      hvariance_zero hchebyshev hthreshold hmono hmono_lt_one

/--
PG23 Theorem 2 source route with both major analytic reductions exposed:
aggregate-demand strictness comes from the integrated applicant-level access
comparison, and Lemma 10's threshold convergence is supplied by the two
one-sided source estimates.
-/
theorem theorem2_topChoiceAndMatch_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_one_sided
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold_upper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n -
            vS < ε)
    (hthreshold_lower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n) <
            ε)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hmono_lt_one : ∀ v, vS < v → monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      vS :=
  theorem2_topChoiceAndMatch_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff
    (μ := μ) (topFirm := topFirm)
    (monoDemand := monoDemand) (polyDemand := polyDemand)
    (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
    (supply := supply) (varianceBound := varianceBound)
    (monoAccessAtPoly := monoAccessAtPoly)
    (polyAccessAtPoly := polyAccessAtPoly)
    (monoMatch := monoMatch) (vS := vS)
    hprob hmono_clear hpoly_clear hmono_antitone
    hmono_int hpoly_int hmono_eq hpoly_eq hle hstrict_pos
    hvariance_zero hchebyshev
    (lemma10_threshold_tendsto_of_one_sided_eventual_bounds
      hthreshold_upper hthreshold_lower)
    hmono hmono_lt_one

/--
PG23 Theorem 2 source-region route from integrated access dominance.  This is
the source-shaped version of part (iii): after the Corollary 4 cutoff
comparison and the Chebyshev/shared-cutoff Theorem 1 route, the eventual
strict polyculture match advantage is concluded on the positive-measure region
specified by the paper, rather than for every value above `vS`.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_one_sided
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    {η : Measure ℝ} {region : Set ℝ}
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hthreshold_upper :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n -
            vS < ε)
    (hthreshold_lower :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          vS -
            (polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n) <
            ε)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lt_one_region : ∀ v ∈ region, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hcutoff :
      ∀ m, monoCutoff m < polyCutoff m := by
    intro m
    exact
      corollary4_mono_cutoff_lt_poly_cutoff_of_integrated_access_gap
        (μ := μ)
        (monoDemand := monoDemand m) (polyDemand := polyDemand m)
        (Pmono := monoCutoff m) (Ppoly := polyCutoff m)
        (supply := supply m)
        (monoAccessAtPoly := monoAccessAtPoly m)
        (polyAccessAtPoly := polyAccessAtPoly m)
        (hmono_clear m) (hpoly_clear m) (hmono_antitone m)
        (hmono_int m) (hpoly_int m) (hmono_eq m) (hpoly_eq m)
        (hle m) (hstrict_pos m)
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        monoMatch vS :=
    theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_one_sided_threshold
      (sampleLaw := noiseLaw)
      (varianceBound := varianceBound)
      (cutoff := polyCutoff)
      hprob hvariance_zero hchebyshev
      hthreshold_upper hthreshold_lower hmono
  have htop :
      ∀ m v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) ≤
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) := by
    intro m v
    haveI : MeasureTheory.IsFiniteMeasure (noiseLaw m) := by
      haveI : MeasureTheory.IsProbabilityMeasure (noiseLaw m) := hprob m
      infer_instance
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_constant_mono_cutoff
        (noiseLaw m) v (topFirm m) (le_of_lt (hcutoff m))
  exact
    theorem2_topChoiceAndMatchPositiveRegion_of_wisdomProbability
      (monoTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (polyTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (monoMatch := monoMatch)
      (polyMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (η := η) (region := region) (vS := vS)
      htop hwisdom hregion_positive hregion_above hmono_lt_one_region

/--
PG23 Theorem 2 source-region route from integrated access dominance and the
source market-clearing proof of Lemma 10.  The cutoff comparison is still
derived from the integrated applicant-level access gap; the high-value
polyculture match limit is derived from supply clearing at `vS`.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ}
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS valueSupply : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (noiseLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq noiseLaw n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lt_one_region : ∀ v ∈ region, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hcutoff :
      ∀ m, monoCutoff m < polyCutoff m := by
    intro m
    exact
      corollary4_mono_cutoff_lt_poly_cutoff_of_integrated_access_gap
        (μ := μ)
        (monoDemand := monoDemand m) (polyDemand := polyDemand m)
        (Pmono := monoCutoff m) (Ppoly := polyCutoff m)
        (supply := supply m)
        (monoAccessAtPoly := monoAccessAtPoly m)
        (polyAccessAtPoly := polyAccessAtPoly m)
        (hmono_clear m) (hpoly_clear m) (hmono_antitone m)
        (hmono_int m) (hpoly_int m) (hmono_eq m) (hpoly_eq m)
        (hle m) (hstrict_pos m)
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        monoMatch vS :=
    theorem1_wisdomProbability_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η) (sampleLaw := noiseLaw) (varianceBound := varianceBound)
      (cutoff := polyCutoff) (monoMatch := monoMatch) (vS := vS)
      (supply := valueSupply)
      hprob hvariance_zero hchebyshev hsupply hmass hclear hmono
  have htop :
      ∀ m v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) ≤
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) := by
    intro m v
    haveI : MeasureTheory.IsFiniteMeasure (noiseLaw m) := by
      haveI : MeasureTheory.IsProbabilityMeasure (noiseLaw m) := hprob m
      infer_instance
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_constant_mono_cutoff
        (noiseLaw m) v (topFirm m) (le_of_lt (hcutoff m))
  exact
    theorem2_topChoiceAndMatchPositiveRegion_of_wisdomProbability
      (monoTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (polyTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (monoMatch := monoMatch)
      (polyMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (η := η) (region := region) (vS := vS)
      htop hwisdom hregion_positive hregion_above hmono_lt_one_region

/--
PG23 Theorem 2 source-region route from integrated access dominance and the
source market-clearing proof of Lemma 10, using Definition 2 maximum
concentration directly.  This is the preferred source-facing route over the
Chebyshev sufficient condition when Definition 2 is available as the paper
primitive.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ}
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS valueSupply : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc : maximumOrderStatisticConcentratingAroundExpected noiseLaw)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lt_one_region : ∀ v ∈ region, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hcutoff :
      ∀ m, monoCutoff m < polyCutoff m := by
    intro m
    exact
      corollary4_mono_cutoff_lt_poly_cutoff_of_integrated_access_gap
        (μ := μ)
        (monoDemand := monoDemand m) (polyDemand := polyDemand m)
        (Pmono := monoCutoff m) (Ppoly := polyCutoff m)
        (supply := supply m)
        (monoAccessAtPoly := monoAccessAtPoly m)
        (polyAccessAtPoly := polyAccessAtPoly m)
        (hmono_clear m) (hpoly_clear m) (hmono_antitone m)
        (hmono_int m) (hpoly_int m) (hmono_eq m) (hpoly_eq m)
        (hle m) (hstrict_pos m)
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        monoMatch vS :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η) (sampleLaw := noiseLaw) (cutoff := polyCutoff)
      (monoMatch := monoMatch) (vS := vS) (supply := valueSupply)
      hprob hconc hsupply hmass hclear hmono
  have htop :
      ∀ m v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) ≤
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) := by
    intro m v
    haveI : MeasureTheory.IsFiniteMeasure (noiseLaw m) := by
      haveI : MeasureTheory.IsProbabilityMeasure (noiseLaw m) := hprob m
      infer_instance
    exact
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_constant_mono_cutoff
        (noiseLaw m) v (topFirm m) (le_of_lt (hcutoff m))
  exact
    theorem2_topChoiceAndMatchPositiveRegion_of_wisdomProbability
      (monoTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (polyTop := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (monoMatch := monoMatch)
      (polyMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (η := η) (region := region) (vS := vS)
      htop hwisdom hregion_positive hregion_above hmono_lt_one_region

/--
PG23 Theorem 2 source-region route from weak integrated access dominance.
Top-choice dominance only needs the weak cutoff comparison `P_mono <= P_poly`;
this route derives that comparison from pointwise weak access dominance at the
polyculture cutoff plus strict monotonicity of the monoculture demand curve.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_weak_access_and_expected_max_shared_cutoff_marketClearing_supply_cutoff
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ}
    {noiseLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {monoMatch : ℕ → ℝ → ℝ} {vS valueSupply : ℝ}
    (hprob : ∀ m, MeasureTheory.IsProbabilityMeasure (noiseLaw m))
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_strict :
      ∀ m, ∀ a b : ℝ, a < b → monoDemand m b < monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hconc : maximumOrderStatisticConcentratingAroundExpected noiseLaw)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono : ∀ v : ℝ, ∀ m n : ℕ, monoMatch m v = monoMatch n v)
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hmono_lt_one_region : ∀ v ∈ region, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (noiseLaw m) v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      monoMatch
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hcutoff :
      ∀ m, monoCutoff m ≤ polyCutoff m := by
    intro m
    exact
      corollary4_mono_cutoff_le_poly_cutoff_of_integrated_weak_access_strict_mono
        (μ := μ)
        (monoDemand := monoDemand m) (polyDemand := polyDemand m)
        (Pmono := monoCutoff m) (Ppoly := polyCutoff m)
        (supply := supply m)
        (monoAccessAtPoly := monoAccessAtPoly m)
        (polyAccessAtPoly := polyAccessAtPoly m)
        (hmono_clear m) (hpoly_clear m) (hmono_strict m)
        (hmono_int m) (hpoly_int m) (hmono_eq m) (hpoly_eq m)
        (hle m)
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        monoMatch vS :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η) (sampleLaw := noiseLaw) (cutoff := polyCutoff)
      (monoMatch := monoMatch) (vS := vS) (supply := valueSupply)
      hprob hconc hsupply hmass hclear hmono
  exact
    theorem2_topChoiceAndPositiveRegion_of_cutoffComparison_and_wisdomProbability
      (topFirm := topFirm)
      (noiseLaw := noiseLaw)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (monoMatch := monoMatch)
      (polyMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (noiseLaw m) (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (η := η) (region := region) (vS := vS)
      hprob hcutoff hwisdom hregion_positive hregion_above
      hmono_lt_one_region

/--
PG23 Theorem 2 source-region route with the monoculture region bound derived
from iid support assumptions.  The remaining source invariance premise states
that the concrete monoculture single-cutoff match probability does not depend
on the number of colleges; the strict-below-one condition on the positive
region is proved here from strict CDF increase and endpoint values on the
noise-support interval.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {vS valueSupply xMin xMax : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hprob :
      ∀ m,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) := by
    intro m
    infer_instance
  have hmono_lt_one_region :
      ∀ v ∈ region,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff 0) (topFirm 0) < 1 :=
    by
      intro v hv
      exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_lt_one_of_lowerCDFMass_pos
          baseNoiseLaw (topFirm 0)
          ((AppliedModelingLib.Probability.lowerCDFMass_mem_Ioo_of_strictMonoOn_Icc_endpoint_values
            baseNoiseLaw hcdf_strict hleft hright
            (hregion_support v hv)).1)
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (μ := μ) (η := η)
      (region := region)
      (noiseLaw := fun m : ℕ =>
        Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
      (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply) (varianceBound := varianceBound)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (monoMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (vS := vS) (valueSupply := valueSupply)
      hprob hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hvariance_zero hchebyshev
      hsupply hmass hclear hmono hregion_positive hregion_above
      hmono_lt_one_region

/--
PG23 Theorem 2 source-region route with the monoculture region bound derived
from iid support assumptions, using Definition 2 maximum concentration
directly.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {vS valueSupply xMin xMax : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
    (hregion_positive : 0 < η.real region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hprob :
      ∀ m,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) := by
    intro m
    infer_instance
  have hmono_lt_one_region :
      ∀ v ∈ region,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff 0) (topFirm 0) < 1 :=
    by
      intro v hv
      exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_lt_one_of_lowerCDFMass_pos
          baseNoiseLaw (topFirm 0)
          ((AppliedModelingLib.Probability.lowerCDFMass_mem_Ioo_of_strictMonoOn_Icc_endpoint_values
            baseNoiseLaw hcdf_strict hleft hright
            (hregion_support v hv)).1)
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (μ := μ) (η := η)
      (region := region)
      (noiseLaw := fun m : ℕ =>
        Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
      (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (monoMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (vS := vS) (valueSupply := valueSupply)
      hprob hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hconc
      hsupply hmass hclear hmono hregion_positive hregion_above
      hmono_lt_one_region

/--
PG23 Theorem 2 source-region route with both source-region facts derived:
positive measure of the region comes from a support subinterval, and
monoculture strict-below-one on the region comes from iid noise support.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hregion_positive : 0 < η.real region :=
    by
      have hstrict : valueCDF a < valueCDF b :=
        hvalue_cdf_strict ha hb hab
      have hinterval_pos : 0 < η.real (Set.Ioo a b) := by
        rw [hvalue_measure_eq]
        linarith
      exact lt_of_lt_of_le hinterval_pos
        (measureReal_mono (μ := η) hsub (measure_ne_top η region))
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply) (varianceBound := varianceBound)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hvariance_zero hchebyshev
      hsupply hmass hclear hmono hregion_positive hregion_above
      hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with both source-region facts derived,
using Definition 2 maximum concentration directly.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hregion_positive : 0 < η.real region :=
    by
      have hstrict : valueCDF a < valueCDF b :=
        hvalue_cdf_strict ha hb hab
      have hinterval_pos : 0 < η.real (Set.Ioo a b) := by
        rw [hvalue_measure_eq]
        linarith
      exact lt_of_lt_of_le hinterval_pos
        (measureReal_mono (μ := η) hsub (measure_ne_top η region))
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hconc
      hsupply hmass hclear hmono hregion_positive hregion_above
      hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-interval route from Theorem 1.  This specializes the
positive-region statement to the paper's interval form `(vS, upper)`.
-/
theorem theorem2_topChoiceAndMatchPositiveInterval_of_wisdomProbability
    {monoTop polyTop monoMatch polyMatch : ℕ → ℝ → ℝ}
    {η : Measure ℝ} {vS upper : ℝ}
    (htop : ∀ m v, polyTop m v ≤ monoTop m v)
    (hwisdom : theorem1_wisdomProbabilityConclusion polyMatch monoMatch vS)
    (hinterval_positive : 0 < η.real (Set.Ioo vS upper))
    (hmono_lt_one_interval :
      ∀ v ∈ Set.Ioo vS upper, monoMatch 0 v < 1) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      monoTop polyTop monoMatch polyMatch η (Set.Ioo vS upper) :=
  theorem2_topChoiceAndMatchPositiveRegion_of_wisdomProbability
    htop hwisdom hinterval_positive
    (by
      intro v hv
      exact hv.1)
    hmono_lt_one_interval

/--
PG23 Theorem 2 region ingredient: for a concrete iid single-college
monoculture match probability, positive CDF mass below the shifted cutoff
implies the match probability is strictly below one throughout the source
region.
-/
theorem theorem2_monoSingleCutoffMatch_lt_one_on_region_of_iid_lowerCDFMass_pos
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : Fin n) {monoCutoff : ℝ} {region : Set ℝ}
    (hpos :
      ∀ v ∈ region,
        0 < AppliedModelingLib.Probability.lowerCDFMass noiseLaw (monoCutoff - v)) :
    ∀ v ∈ region,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => monoCutoff) topFirm < 1 := by
  intro v hv
  exact
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_lt_one_of_lowerCDFMass_pos
      noiseLaw topFirm (hpos v hv)

/--
PG23 Theorem 2 region ingredient from the source support condition.  If the
shifted monoculture cutoff lies in the interior of the noise support
throughout the source region, then the one-dimensional lower CDF mass is
strictly positive there, so the concrete iid monoculture match probability is
strictly below one.
-/
theorem theorem2_monoSingleCutoffMatch_lt_one_on_region_of_iid_strict_support
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : Fin n) {monoCutoff xMin xMax : ℝ} {region : Set ℝ}
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff - v ∈ Set.Ioo xMin xMax) :
    ∀ v ∈ region,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          v (fun _ : Fin n => monoCutoff) topFirm < 1 :=
  theorem2_monoSingleCutoffMatch_lt_one_on_region_of_iid_lowerCDFMass_pos
    noiseLaw topFirm
    (fun v hv =>
      (AppliedModelingLib.Probability.lowerCDFMass_mem_Ioo_of_strictMonoOn_Icc_endpoint_values
        noiseLaw hcdf_strict hleft hright (hregion_support v hv)).1)

/--
PG23 monoculture common-cutoff derivation.  If every monoculture cutoff across
market sizes clears the same scalar demand equation, and that equation is
strictly decreasing in the common cutoff, then all monoculture scalar cutoffs
are equal.
-/
theorem theorem2_commonMonoCutoff_of_common_scalar_clearing
    {monoCutoff : ℕ → ℝ} {monoDemand : ℝ → ℝ} {supply : ℝ}
    (hclear : ∀ m : ℕ, monoDemand (monoCutoff m) = supply)
    (hstrict : ∀ x y : ℝ, x < y → monoDemand y < monoDemand x) :
    ∀ m n : ℕ, monoCutoff m = monoCutoff n := by
  intro m n
  exact
    scalarClearing_unique_of_strict_antitone_demand
      hstrict (hclear m) (hclear n)

/--
PG23 Theorem 1 full welfare route with the common monoculture cutoff derived
from the source scalar clearing equation.  This is the strongest current
Theorem 1 route: Chebyshev and market clearing derive the polyculture
step-function limit, the scalar clearing equation derives monoculture
invariance, and explicit welfare integrals derive the welfare conclusion.
-/
theorem theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_scalar_mono_clearing_and_integral_welfare
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {varianceBound polyCutoff monoCutoff : ℕ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {vS supply commonMonoSupply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hcommon_clear :
      ∀ n : ℕ, commonMonoDemand (monoCutoff n) = commonMonoSupply)
    (hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_integral_welfare
    η baseNoiseLaw topFirm hvariance_zero hchebyshev hsupply hmass
    hclear
    (theorem2_commonMonoCutoff_of_common_scalar_clearing
      hcommon_clear hcommon_strict)
    hno_atom habs_integrable hpolyWelfare_eq hmonoWelfare_eq
    hoptimalWelfare_eq hmono_suboptimal

/--
PG23 Theorem 1 full welfare route with the common monoculture cutoff derived
from the source scalar clearing equation, using Definition 2 maximum
concentration directly.
-/
theorem theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_scalar_mono_clearing_and_integral_welfare
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {polyCutoff monoCutoff : ℕ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {vS supply commonMonoSupply : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hcommon_clear :
      ∀ n : ℕ, commonMonoDemand (monoCutoff n) = commonMonoSupply)
    (hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare :=
  theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_integral_welfare
    η baseNoiseLaw topFirm hconc hsupply hmass hclear
    (theorem2_commonMonoCutoff_of_common_scalar_clearing
      hcommon_clear hcommon_strict)
    hno_atom habs_integrable hpolyWelfare_eq hmonoWelfare_eq
    hoptimalWelfare_eq hmono_suboptimal

/--
PG23 Theorem 1 full welfare route where the common monoculture scalar
clearing curve is the concrete iid single-cutoff demand curve.  The common
cutoff equality is derived from the source scalar clearing equation after Lean
derives strict demand monotonicity from the iid integral representation and
connected-support CDF witness.
-/
theorem theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_iid_scalar_mono_clearing_and_integral_welfare
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {polyCutoff monoCutoff : ℕ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS supply commonMonoSupply vMin vMax : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hcommon_clear :
      ∀ n : ℕ, commonMonoDemand (monoCutoff n) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hcommon_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (y - v)) ∧
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare := by
  have hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x :=
    strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
      (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
      (demand := commonMonoDemand) (valueCDF := valueCDF)
      (vMin := vMin) (vMax := vMax)
      hcommon_int hcommon_eq hvalue_cdf_strict hcommon_witness
  exact
    theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_scalar_mono_clearing_and_integral_welfare
      η baseNoiseLaw topFirm hconc hsupply hmass hclear hcommon_clear
      hcommon_strict hno_atom habs_integrable hpolyWelfare_eq
      hmonoWelfare_eq hoptimalWelfare_eq hmono_suboptimal

/--
PG23 Theorem 1 full welfare route where the common monoculture scalar
clearing curve is the concrete iid single-cutoff demand curve, and the
strictness needed for common-cutoff equality is derived only for the actual
clearing-cutoff pairs from primitive support endpoint bounds.
-/
theorem theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_iid_scalar_mono_clearing_lower_support_bounds_and_integral_welfare
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ n : ℕ, Fin (n + 1))
    {polyCutoff monoCutoff : ℕ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS supply commonMonoSupply vMin vMax xMin xMax : ℝ}
    {polyWelfare monoWelfare : ℕ → ℝ} {optimalWelfare : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ n,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ∂η = supply)
    (hcommon_clear :
      ∀ n : ℕ, commonMonoDemand (monoCutoff n) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hmono_cutoff_bounds :
      ∀ m n : ℕ, monoCutoff m < monoCutoff n →
        vMin + xMin < monoCutoff m ∧ monoCutoff m < vMax + xMax)
    (hno_atom : η {vS} = 0)
    (habs_integrable : Integrable (fun v : ℝ => |v|) η)
    (hpolyWelfare_eq :
      ∀ n : ℕ, polyWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) ∂η)
    (hmonoWelfare_eq :
      ∀ n : ℕ, monoWelfare n =
        ∫ v : ℝ,
          v *
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) ∂η)
    (hoptimalWelfare_eq :
      optimalWelfare =
        ∫ v : ℝ, v * theorem1_optimalStepMatchProbability vS v ∂η)
    (hmono_suboptimal : monoWelfare 0 < optimalWelfare) :
    theorem1_wisdomFullConclusion
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (n + 1))) v
          (fun _ => polyCutoff n))
      (fun n : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n))
      vS polyWelfare monoWelfare optimalWelfare := by
  have hmono_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n := by
    intro m n
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict :
          commonMonoDemand (monoCutoff n) <
            commonMonoDemand (monoCutoff m) :=
        iid_single_cutoff_demand_lt_of_lower_support_bounds
          (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
          (demand := commonMonoDemand) (valueCDF := valueCDF)
          (vMin := vMin) (vMax := vMax) (xMin := xMin) (xMax := xMax)
          (x := monoCutoff m) (y := monoCutoff n)
          hcommon_int hcommon_eq hvalue_cdf_strict hnoise_cdf_strict
          hleft hright hvalue_measure_eq hvalue_nonempty hnoise_nonempty
          hlt (hmono_cutoff_bounds m n hlt)
      rw [hcommon_clear n, hcommon_clear m] at hstrict
      exact (lt_irrefl commonMonoSupply) hstrict
    · have hstrict :
          commonMonoDemand (monoCutoff m) <
            commonMonoDemand (monoCutoff n) :=
        iid_single_cutoff_demand_lt_of_lower_support_bounds
          (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
          (demand := commonMonoDemand) (valueCDF := valueCDF)
          (vMin := vMin) (vMax := vMax) (xMin := xMin) (xMax := xMax)
          (x := monoCutoff n) (y := monoCutoff m)
          hcommon_int hcommon_eq hvalue_cdf_strict hnoise_cdf_strict
          hleft hright hvalue_measure_eq hvalue_nonempty hnoise_nonempty
          hgt (hmono_cutoff_bounds n m hgt)
      rw [hcommon_clear m, hcommon_clear n] at hstrict
      exact (lt_irrefl commonMonoSupply) hstrict
  exact
    theorem1_wisdomFull_of_expected_max_shared_cutoff_marketClearing_supply_cutoff_common_mono_cutoff_and_integral_welfare
      η baseNoiseLaw topFirm hconc hsupply hmass hclear hmono_cutoff
      hno_atom habs_integrable hpolyWelfare_eq hmonoWelfare_eq
      hoptimalWelfare_eq hmono_suboptimal

/--
PG23 Theorem 2 monoculture invariance for the concrete iid single-cutoff
model.  If the source equal-cutoff argument gives the same scalar monoculture
cutoff for every market size, then a named firm's affordability probability is
independent of the number of firms, because the iid product coordinate event
reduces to the same one-dimensional upper-tail probability.
-/
theorem theorem2_monocultureSingleCutoffProbability_invariant_of_common_cutoff
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoCutoff : ℕ → ℝ}
    (hcutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n) :
    ∀ v : ℝ, ∀ m n : ℕ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) := by
  intro v m n
  rw [
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass,
    hcutoff m n]

/--
PG23 Theorem 2 source-region route with the remaining monoculture-invariance
premise reduced to a source common-cutoff statement.  Positive measure of the
region and the strict-below-one monoculture bound are still derived from the
support/CDF assumptions; monoculture invariance is derived from the iid
single-cutoff formula and `monoCutoff m = monoCutoff n`.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_mono_cutoff
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono_cutoff :
      ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply) (varianceBound := varianceBound)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hvariance_zero hchebyshev
      hsupply hmass hclear
      (theorem2_monocultureSingleCutoffProbability_invariant_of_common_cutoff
        baseNoiseLaw topFirm hmono_cutoff)
      ha hb hab hsub hvalue_cdf_strict hvalue_measure_eq
      hregion_above hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with the remaining monoculture-invariance
premise reduced to a source common-cutoff statement, using Definition 2
maximum concentration directly.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_mono_cutoff
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hmono_cutoff :
      ∀ m n : ℕ, monoCutoff m = monoCutoff n)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hconc
      hsupply hmass hclear
      (theorem2_monocultureSingleCutoffProbability_invariant_of_common_cutoff
        baseNoiseLaw topFirm hmono_cutoff)
      ha hb hab hsub hvalue_cdf_strict hvalue_measure_eq
      hregion_above hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with the common monoculture cutoff derived
from the source scalar clearing equation.  This replaces the raw
`monoCutoff m = monoCutoff n` premise by the paper's observation that
monoculture cutoffs solve one market-size-independent, strictly decreasing
scalar clearing equation.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_scalar_mono_clearing
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply varianceBound : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ =>
                  Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)) n)
              ε ≤
            varianceBound n / ε ^ 2)
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_chebyshev_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_mono_cutoff
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply) (varianceBound := varianceBound)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hvariance_zero hchebyshev
      hsupply hmass hclear
      (theorem2_commonMonoCutoff_of_common_scalar_clearing
        hcommon_clear hcommon_strict)
      ha hb hab hsub hvalue_cdf_strict hvalue_measure_eq
      hregion_above hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with the common monoculture cutoff derived
from the source scalar clearing equation, using Definition 2 maximum
concentration directly.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_scalar_mono_clearing
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_mono_cutoff
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hconc
      hsupply hmass hclear
      (theorem2_commonMonoCutoff_of_common_scalar_clearing
        hcommon_clear hcommon_strict)
      ha hb hab hsub hvalue_cdf_strict hvalue_measure_eq
      hregion_above hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route where the common monoculture scalar
clearing curve is the concrete iid single-cutoff demand curve.  This removes
the abstract strict-demand premise from the common-cutoff step: strictness is
derived from the source integral representation and the same connected-support
CDF witness used in the Lemma 2 equal-cutoff route.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_antitone :
      ∀ m, ∀ a b : ℝ, a ≤ b → monoDemand m b ≤ monoDemand m a)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hcommon_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (y - v)) ∧
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x :=
    strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
      (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
      (demand := commonMonoDemand) (valueCDF := valueCDF)
      (vMin := vMin) (vMax := vMax)
      hcommon_int hcommon_eq hvalue_cdf_strict hcommon_witness
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_scalar_mono_clearing
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (commonMonoDemand := commonMonoDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (commonMonoSupply := commonMonoSupply)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hconc
      hsupply hmass hclear hcommon_clear hcommon_strict ha hb hab hsub
      hvalue_cdf_strict hvalue_measure_eq hregion_above hcdf_strict
      hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with the monoculture demand antitonicity
derived from the concrete iid single-cutoff demand formula.  This removes the
abstract monotone-demand premise used in Corollary 4 while preserving the
existing integrated-access proof of the strict polyculture demand gap.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_mono_iid_antitone
    {Applicant : Type*} [MeasurableSpace Applicant]
    (μ : Measure Applicant) [IsProbabilityMeasure μ]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {monoAccessAtPoly polyAccessAtPoly : ℕ → Applicant → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_demand_int :
      ∀ m : ℕ, ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m)) η)
    (hmono_demand_eq :
      ∀ m : ℕ, ∀ z : ℝ,
        monoDemand m z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η)
    (hmono_int : ∀ m, Integrable (monoAccessAtPoly m) μ)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) μ)
    (hmono_eq :
      ∀ m, monoDemand m (polyCutoff m) =
        ∫ a, monoAccessAtPoly m a ∂μ)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ a, polyAccessAtPoly m a ∂μ)
    (hle :
      ∀ m a, monoAccessAtPoly m a ≤ polyAccessAtPoly m a)
    (hstrict_pos :
      ∀ m, 0 < μ {a | monoAccessAtPoly m a < polyAccessAtPoly m a})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hcommon_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (y - v)) ∧
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hmono_antitone :
      ∀ m, ∀ x y : ℝ, x ≤ y → monoDemand m y ≤ monoDemand m x := by
    intro m
    exact
      antitone_demand_of_iid_single_cutoff_integrated_access
        (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm m)
        (demand := monoDemand m)
        (hmono_demand_int m)
        (hmono_demand_eq m)
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing
      (μ := μ) (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (commonMonoDemand := commonMonoDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (commonMonoSupply := commonMonoSupply)
      (monoAccessAtPoly := monoAccessAtPoly)
      (polyAccessAtPoly := polyAccessAtPoly)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_antitone hmono_int hpoly_int
      hmono_eq hpoly_eq hle hstrict_pos hconc hsupply hmass hclear
      hcommon_clear hcommon_int hcommon_eq hcommon_witness
      ha hb hab hsub hvalue_cdf_strict hvalue_measure_eq hregion_above
      hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with the monoculture access-at-poly term
identified with the concrete iid single-cutoff probability.  The remaining
integrated-access comparison is now only the paper's polyculture-vs-concrete
monoculture access comparison at the polyculture cutoff.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_mono_iid_antitone_mono_access_iid
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {polyAccessAtPoly : ℕ → ℝ → ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_demand_int :
      ∀ m : ℕ, ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m)) η)
    (hmono_demand_eq :
      ∀ m : ℕ, ∀ z : ℝ,
        monoDemand m z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η)
    (hpoly_int : ∀ m, Integrable (polyAccessAtPoly m) η)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ v, polyAccessAtPoly m v ∂η)
    (hle :
      ∀ m v,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) ≤
          polyAccessAtPoly m v)
    (hstrict_pos :
      ∀ m,
        0 < η {v |
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) <
            polyAccessAtPoly m v})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hcommon_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (y - v)) ∧
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region :=
  theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_mono_iid_antitone
    (μ := η) (η := η) (baseNoiseLaw := baseNoiseLaw)
    (region := region) (topFirm := topFirm)
    (monoDemand := monoDemand) (polyDemand := polyDemand)
    (commonMonoDemand := commonMonoDemand)
    (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
    (supply := supply)
    (commonMonoSupply := commonMonoSupply)
    (monoAccessAtPoly := fun m v =>
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
        v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
    (polyAccessAtPoly := polyAccessAtPoly)
    (valueCDF := valueCDF)
    (vS := vS) (valueSupply := valueSupply)
    (xMin := xMin) (xMax := xMax)
    (vMin := vMin) (vMax := vMax) (a := a) (b := b)
    hmono_clear hpoly_clear hmono_demand_int hmono_demand_eq
    (fun m => hmono_demand_int m (polyCutoff m)) hpoly_int
    (fun m => hmono_demand_eq m (polyCutoff m)) hpoly_eq hle
    hstrict_pos hconc hsupply hmass hclear hcommon_clear hcommon_int
    hcommon_eq hcommon_witness ha hb hab hsub hvalue_cdf_strict
    hvalue_measure_eq hregion_above hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route with both access-at-poly terms identified
with concrete iid cutoff-crossing probabilities.  The monoculture term is the
named top firm's single-cutoff crossing probability at the polyculture cutoff;
the polyculture term is the probability of crossing at least one of all
colleges' polyculture cutoffs.  The weak access comparison is then just event
inclusion.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_mono_iid_antitone_mono_access_iid_poly_access_iid
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_demand_int :
      ∀ m : ℕ, ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m)) η)
    (hmono_demand_eq :
      ∀ m : ℕ, ∀ z : ℝ,
        monoDemand m z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η)
    (hstrict_pos :
      ∀ m,
        0 < η {v |
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) <
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (m + 1))) v
              (fun _ => polyCutoff m)})
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hcommon_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (y - v)) ∧
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_access_gap_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_mono_iid_antitone_mono_access_iid
      (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (commonMonoDemand := commonMonoDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (commonMonoSupply := commonMonoSupply)
      (polyAccessAtPoly := fun m v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_demand_int hmono_demand_eq
      (fun m =>
        AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) η
          (Finset.univ : Finset (Fin (m + 1)))
          (fun _ : Fin (m + 1) => polyCutoff m))
      hpoly_eq
      (fun m v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) (by simp)
          v (fun _ : Fin (m + 1) => polyCutoff m))
      hstrict_pos hconc hsupply hmass hclear hcommon_clear hcommon_int
      hcommon_eq hcommon_witness ha hb hab hsub hvalue_cdf_strict
      hvalue_measure_eq hregion_above hcdf_strict hleft hright hregion_support

/--
PG23 Theorem 2 source-region route using only weak all-college-versus-single
access dominance for the cutoff comparison.  This avoids requiring the strict
polyculture access gap at every finite market size; strictness is only needed
for the monoculture scalar demand curve, where it follows from the same
single-cutoff CDF/support argument used in Lemma 2.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_weak_access_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_mono_access_iid_poly_access_iid
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_demand_int :
      ∀ m : ℕ, ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m)) η)
    (hmono_demand_eq :
      ∀ m : ℕ, ∀ z : ℝ,
        monoDemand m z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η)
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hcommon_witness :
      ∀ x y : ℝ, x < y →
        ∃ a b : ℝ,
          a ∈ Set.Ioo vMin vMax ∧ b ∈ Set.Ioo vMin vMax ∧ a < b ∧
          (∀ v ∈ Set.Ioo a b,
            AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (x - v) <
              AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw (y - v)) ∧
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hvalue_measure_eq : η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hprob :
      ∀ m,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) := by
    intro m
    infer_instance
  have hmono_strict :
      ∀ m, ∀ x y : ℝ, x < y → monoDemand m y < monoDemand m x := by
    intro m
    exact
      strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
        (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm m)
        (demand := monoDemand m)
        (valueCDF := valueCDF) (vMin := vMin) (vMax := vMax)
        (hmono_demand_int m) (hmono_demand_eq m)
        hvalue_cdf_strict hcommon_witness
  have hcommon_strict :
      ∀ x y : ℝ, x < y → commonMonoDemand y < commonMonoDemand x :=
    strict_antitone_demand_of_iid_single_cutoff_integrated_access_gap
      (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
      (demand := commonMonoDemand)
      (valueCDF := valueCDF) (vMin := vMin) (vMax := vMax)
      hcommon_int hcommon_eq hvalue_cdf_strict hcommon_witness
  have hcommon_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n :=
    theorem2_commonMonoCutoff_of_common_scalar_clearing
      hcommon_clear hcommon_strict
  have hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) :=
    theorem2_monocultureSingleCutoffProbability_invariant_of_common_cutoff
      baseNoiseLaw topFirm hcommon_cutoff
  have hregion_positive : 0 < η.real region := by
    have hstrict : valueCDF a < valueCDF b :=
      hvalue_cdf_strict ha hb hab
    have hinterval_pos : 0 < η.real (Set.Ioo a b) := by
      rw [hvalue_measure_eq]
      linarith
    exact
      lt_of_lt_of_le hinterval_pos
        (measureReal_mono (μ := η) hsub (measure_ne_top η region))
  have hmono_lt_one_region :
      ∀ v ∈ region,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff 0) (topFirm 0) < 1 :=
    theorem2_monoSingleCutoffMatch_lt_one_on_region_of_iid_strict_support
      baseNoiseLaw (topFirm 0) hcdf_strict hleft hright hregion_support
  exact
    theorem2_topChoiceAndPositiveRegion_of_integrated_weak_access_and_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (μ := η) (η := η)
      (noiseLaw := fun m : ℕ => Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (monoAccessAtPoly := fun m v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (polyAccessAtPoly := fun m v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (monoMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (vS := vS) (valueSupply := valueSupply)
      hprob hmono_clear hpoly_clear hmono_strict
      (fun m => hmono_demand_int m (polyCutoff m))
      (fun m =>
        AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) η
          (Finset.univ : Finset (Fin (m + 1)))
          (fun _ : Fin (m + 1) => polyCutoff m))
      (fun m => hmono_demand_eq m (polyCutoff m)) hpoly_eq
      (fun m v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) (by simp)
          v (fun _ : Fin (m + 1) => polyCutoff m))
      hconc hsupply hmass hclear hmono hregion_positive hregion_above
      hmono_lt_one_region

/--
PG23 Theorem 2 source-region route using weak concrete access dominance, with
the monoculture strictness obligations derived from primitive support endpoint
bounds rather than a global CDF witness.  The pairwise strict decrease needed
for Corollary 4 is proved only at the actual polyculture/monoculture cutoff
pair, and the common monoculture cutoff is proved by the same lower-support
argument used in the strengthened Theorem 1 route.
-/
theorem theorem2_topChoiceAndPositiveRegion_of_integrated_weak_access_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_lower_support_bounds_mono_access_iid_poly_access_iid
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_demand_int :
      ∀ m : ℕ, ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m)) η)
    (hmono_demand_eq :
      ∀ m : ℕ, ∀ z : ℝ,
        monoDemand m z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η)
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcommon_cutoff_bounds :
      ∀ m n : ℕ, monoCutoff m < monoCutoff n →
        vMin + xMin < monoCutoff m ∧ monoCutoff m < vMax + xMax)
    (hmono_poly_cutoff_bounds :
      ∀ m : ℕ, polyCutoff m < monoCutoff m →
        vMin + xMin < polyCutoff m ∧ polyCutoff m < vMax + xMax)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    Theorem2TopChoiceAndMatchPositiveRegionConclusion
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      η region := by
  have hprob :
      ∀ m,
        MeasureTheory.IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) := by
    intro m
    infer_instance
  have hmono_pair_strict :
      ∀ m : ℕ, polyCutoff m < monoCutoff m →
        monoDemand m (monoCutoff m) < monoDemand m (polyCutoff m) := by
    intro m hlt
    exact
      iid_single_cutoff_demand_lt_of_lower_support_bounds
        (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm m)
        (demand := monoDemand m) (valueCDF := valueCDF)
        (vMin := vMin) (vMax := vMax) (xMin := xMin) (xMax := xMax)
        (x := polyCutoff m) (y := monoCutoff m)
        (hmono_demand_int m) (hmono_demand_eq m)
        hvalue_cdf_strict hnoise_cdf_strict hleft hright
        hvalue_measure_eq hvalue_nonempty hnoise_nonempty
        hlt (hmono_poly_cutoff_bounds m hlt)
  have hcommon_cutoff : ∀ m n : ℕ, monoCutoff m = monoCutoff n := by
    intro m n
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict :
          commonMonoDemand (monoCutoff n) <
            commonMonoDemand (monoCutoff m) :=
        iid_single_cutoff_demand_lt_of_lower_support_bounds
          (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
          (demand := commonMonoDemand) (valueCDF := valueCDF)
          (vMin := vMin) (vMax := vMax) (xMin := xMin) (xMax := xMax)
          (x := monoCutoff m) (y := monoCutoff n)
          hcommon_int hcommon_eq hvalue_cdf_strict hnoise_cdf_strict
          hleft hright hvalue_measure_eq hvalue_nonempty hnoise_nonempty
          hlt (hcommon_cutoff_bounds m n hlt)
      rw [hcommon_clear n, hcommon_clear m] at hstrict
      exact (lt_irrefl commonMonoSupply) hstrict
    · have hstrict :
          commonMonoDemand (monoCutoff m) <
            commonMonoDemand (monoCutoff n) :=
        iid_single_cutoff_demand_lt_of_lower_support_bounds
          (μ := η) (noiseLaw := baseNoiseLaw) (college := topFirm 0)
          (demand := commonMonoDemand) (valueCDF := valueCDF)
          (vMin := vMin) (vMax := vMax) (xMin := xMin) (xMax := xMax)
          (x := monoCutoff n) (y := monoCutoff m)
          hcommon_int hcommon_eq hvalue_cdf_strict hnoise_cdf_strict
          hleft hright hvalue_measure_eq hvalue_nonempty hnoise_nonempty
          hgt (hcommon_cutoff_bounds n m hgt)
      rw [hcommon_clear m, hcommon_clear n] at hstrict
      exact (lt_irrefl commonMonoSupply) hstrict
  have hmono :
      ∀ v : ℝ, ∀ m n : ℕ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw))
            v (fun _ : Fin (n + 1) => monoCutoff n) (topFirm n) :=
    theorem2_monocultureSingleCutoffProbability_invariant_of_common_cutoff
      baseNoiseLaw topFirm hcommon_cutoff
  have hregion_positive : 0 < η.real region := by
    have hstrict : valueCDF a < valueCDF b :=
      hvalue_cdf_strict ha hb hab
    have hinterval_pos : 0 < η.real (Set.Ioo a b) := by
      rw [hvalue_measure_eq a b ha hb hab]
      linarith
    exact
      lt_of_lt_of_le hinterval_pos
        (measureReal_mono (μ := η) hsub (measure_ne_top η region))
  have hmono_lt_one_region :
      ∀ v ∈ region,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
            v (fun _ : Fin (0 + 1) => monoCutoff 0) (topFirm 0) < 1 :=
    theorem2_monoSingleCutoffMatch_lt_one_on_region_of_iid_strict_support
      baseNoiseLaw (topFirm 0) hnoise_cdf_strict hleft hright hregion_support
  have hcutoff :
      ∀ m, monoCutoff m ≤ polyCutoff m := by
    intro m
    exact
      corollary4_mono_cutoff_le_poly_cutoff_of_integrated_weak_access_pair_strict
        (μ := η)
        (monoDemand := monoDemand m) (polyDemand := polyDemand m)
        (Pmono := monoCutoff m) (Ppoly := polyCutoff m)
        (supply := supply m)
        (monoAccessAtPoly := fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m))
        (polyAccessAtPoly := fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        (hmono_clear m) (hpoly_clear m) (hmono_pair_strict m)
        (hmono_demand_int m (polyCutoff m))
        (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw)) η
          (Finset.univ : Finset (Fin (m + 1)))
          (fun _ : Fin (m + 1) => polyCutoff m))
        (hmono_demand_eq m (polyCutoff m)) (hpoly_eq m)
        (fun v =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) (by simp)
            v (fun _ : Fin (m + 1) => polyCutoff m))
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m))
        (fun m : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
        vS :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
      (η := η)
      (sampleLaw := fun m : ℕ =>
        Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
      (cutoff := polyCutoff)
      (monoMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (vS := vS) (supply := valueSupply)
      hprob hconc hsupply hmass hclear hmono
  exact
    theorem2_topChoiceAndPositiveRegion_of_cutoffComparison_and_wisdomProbability
      (topFirm := topFirm)
      (noiseLaw := fun m : ℕ =>
        Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (monoMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (polyMatch := fun m : ℕ => fun v : ℝ =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ => polyCutoff m))
      (η := η) (region := region) (vS := vS)
      hprob hcutoff hwisdom hregion_positive hregion_above
      hmono_lt_one_region

/--
PG23 Theorem 2 positive-region source clauses from the lower-support
endpoint-bounds route.

This projects the strongest current concrete iid route into the three
paper-facing clauses: weak top-choice comparison, positive-measure region, and
eventual strict match-probability improvement on that region.
-/
theorem theorem2_topChoiceAndMatchPositiveRegion_source_clauses_of_integrated_weak_access_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_lower_support_bounds_mono_access_iid_poly_access_iid
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (baseNoiseLaw : Measure ℝ) [IsProbabilityMeasure baseNoiseLaw]
    {region : Set ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoDemand polyDemand : ℕ → ℝ → ℝ}
    {commonMonoDemand : ℝ → ℝ}
    {monoCutoff polyCutoff supply : ℕ → ℝ}
    {commonMonoSupply : ℝ}
    {valueCDF : ℝ → ℝ}
    {vS valueSupply xMin xMax vMin vMax a b : ℝ}
    (hmono_clear :
      ∀ m, monoDemand m (monoCutoff m) = supply m)
    (hpoly_clear :
      ∀ m, polyDemand m (polyCutoff m) = supply m)
    (hmono_demand_int :
      ∀ m : ℕ, ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m)) η)
    (hmono_demand_eq :
      ∀ m : ℕ, ∀ z : ℝ,
        monoDemand m z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => z) (topFirm m) ∂η)
    (hpoly_eq :
      ∀ m, polyDemand m (polyCutoff m) =
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η)
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ =>
          Measure.pi (fun _ : Fin (n + 1) => baseNoiseLaw)))
    (hsupply :
      AppliedModelingLib.Probability.UpperTailThresholdCertificate η valueSupply vS)
    (hmass :
      AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS)
    (hclear :
      ∀ m,
        ∫ v,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ => polyCutoff m) ∂η = valueSupply)
    (hcommon_clear :
      ∀ m : ℕ, commonMonoDemand (monoCutoff m) = commonMonoSupply)
    (hcommon_int :
      ∀ z : ℝ,
        Integrable
          (fun v : ℝ =>
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0)) η)
    (hcommon_eq :
      ∀ z : ℝ,
        commonMonoDemand z =
          ∫ v,
            AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (0 + 1) => baseNoiseLaw))
              v (fun _ : Fin (0 + 1) => z) (topFirm 0) ∂η)
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass baseNoiseLaw xMax = 1)
    (hvalue_measure_eq :
      ∀ a b : ℝ,
        a ∈ Set.Ioo vMin vMax → b ∈ Set.Ioo vMin vMax → a < b →
          η.real (Set.Ioo a b) = valueCDF b - valueCDF a)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcommon_cutoff_bounds :
      ∀ m n : ℕ, monoCutoff m < monoCutoff n →
        vMin + xMin < monoCutoff m ∧ monoCutoff m < vMax + xMax)
    (hmono_poly_cutoff_bounds :
      ∀ m : ℕ, polyCutoff m < monoCutoff m →
        vMin + xMin < polyCutoff m ∧ polyCutoff m < vMax + xMax)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ region)
    (hregion_above : ∀ v ∈ region, vS < v)
    (hregion_support :
      ∀ v ∈ region, monoCutoff 0 - v ∈ Set.Ioo xMin xMax) :
    (∀ m v,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) ≤
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m)) ∧
      0 < η.real region ∧
      (∀ v ∈ region,
        ∀ᶠ m : ℕ in atTop,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) <
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (m + 1) => baseNoiseLaw))
              (Finset.univ : Finset (Fin (m + 1))) v
              (fun _ => polyCutoff m)) := by
  have h :=
    theorem2_topChoiceAndPositiveRegion_of_integrated_weak_access_and_expected_max_shared_cutoff_marketClearing_supply_cutoff_iid_support_positive_interval_common_iid_scalar_mono_clearing_lower_support_bounds_mono_access_iid_poly_access_iid
      (η := η) (baseNoiseLaw := baseNoiseLaw)
      (region := region) (topFirm := topFirm)
      (monoDemand := monoDemand) (polyDemand := polyDemand)
      (commonMonoDemand := commonMonoDemand)
      (monoCutoff := monoCutoff) (polyCutoff := polyCutoff)
      (supply := supply)
      (commonMonoSupply := commonMonoSupply)
      (valueCDF := valueCDF)
      (vS := vS) (valueSupply := valueSupply)
      (xMin := xMin) (xMax := xMax)
      (vMin := vMin) (vMax := vMax) (a := a) (b := b)
      hmono_clear hpoly_clear hmono_demand_int hmono_demand_eq
      hpoly_eq hconc hsupply hmass hclear hcommon_clear
      hcommon_int hcommon_eq hvalue_cdf_strict hnoise_cdf_strict
      hleft hright hvalue_measure_eq hvalue_nonempty hnoise_nonempty
      hcommon_cutoff_bounds hmono_poly_cutoff_bounds ha hb hab hsub
      hregion_above hregion_support
  exact theorem2_topChoiceAndMatchPositiveRegion_source_clauses h

/--
PG23 Theorem 2(i) strict scalar top-choice comparison.  The source proof uses
the formula `Pr[v + X > P] = 1 - F_X(P - v)`: if the monoculture cutoff is
strictly below the polyculture cutoff and the CDF is strictly increasing on the
two shifted cutoff values, monoculture gives a strictly higher top-choice
probability.
-/
theorem theorem2_topChoiceProbability_strict_of_cdf_formula
    {monoTop polyTop : ℕ → ℝ → ℝ}
    {cdf : ℝ → ℝ} {monoCutoff polyCutoff : ℕ → ℝ}
    (hmono_formula :
      ∀ m v, monoTop m v = 1 - cdf (monoCutoff m - v))
    (hpoly_formula :
      ∀ m v, polyTop m v = 1 - cdf (polyCutoff m - v))
    (hcdf_strict :
      ∀ m v, monoCutoff m - v < polyCutoff m - v →
        cdf (monoCutoff m - v) < cdf (polyCutoff m - v))
    (hcutoff_strict : ∀ m, monoCutoff m < polyCutoff m) :
    ∀ m v, polyTop m v < monoTop m v := by
  intro m v
  rw [hmono_formula m v, hpoly_formula m v]
  have hshift : monoCutoff m - v < polyCutoff m - v := by
    linarith [hcutoff_strict m]
  have hcdf := hcdf_strict m v hshift
  linarith

/--
PG23 Theorem 2(i) strict scalar top-choice comparison for iid noise.  The
single-college CDF formula `Pr[v + X > P] = 1 - F(P - v)` is derived from the
product noise model rather than assumed.
-/
theorem theorem2_topChoiceProbability_strict_of_iidProduct_lowerCDFMass
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {monoCutoff polyCutoff : ℕ → ℝ}
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (hcdf_strict :
      ∀ m v, monoCutoff m - v < polyCutoff m - v →
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (monoCutoff m - v) <
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw (polyCutoff m - v))
    (hcutoff_strict : ∀ m, monoCutoff m < polyCutoff m) :
    ∀ m v,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) <
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) := by
  intro m v
  rw [
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass,
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass]
  have hshift : monoCutoff m - v < polyCutoff m - v := by
    linarith [hcutoff_strict m]
  have hcdf := hcdf_strict m v hshift
  linarith

/--
PG23 Proposition 7(iii), CDF powers on connected support.  If the noise CDF is
strictly increasing on the interior support interval and takes values in
`(0,1)` there, then every positive natural power of the CDF is also strictly
increasing on the interval and still takes values in `(0,1)`.
-/
theorem proposition7_cdf_power_strictMonoOn_and_mem_Ioo
    {cdf : ℝ → ℝ} {xMin xMax : ℝ} {k : ℕ}
    (hk : 0 < k)
    (hcdf_strict : StrictMonoOn cdf (Set.Ioo xMin xMax))
    (hcdf_mem : ∀ x ∈ Set.Ioo xMin xMax, cdf x ∈ Set.Ioo (0 : ℝ) 1) :
    StrictMonoOn (fun x : ℝ => cdf x ^ k) (Set.Ioo xMin xMax) ∧
      ∀ x ∈ Set.Ioo xMin xMax, cdf x ^ k ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · intro a ha b hb hab
    have hlt : cdf a < cdf b := hcdf_strict ha hb hab
    have hnonneg : 0 ≤ cdf a := le_of_lt (hcdf_mem a ha).1
    exact pow_lt_pow_left₀ hlt hnonneg (Nat.ne_of_gt hk)
  · intro x hx
    rcases hcdf_mem x hx with ⟨hpos, hlt_one⟩
    have hlt_pow : cdf x ^ k < (1 : ℝ) ^ k :=
      pow_lt_pow_left₀ hlt_one (le_of_lt hpos) (Nat.ne_of_gt hk)
    exact ⟨pow_pos hpos k, by simpa using hlt_pow⟩

/--
PG23 Proposition 8, positive measure from connected support, in the form used
downstream.  If the target interval contains an open subinterval `(a,b)` inside
the interior support, the CDF is strictly increasing there, and open-interval
mass is given by the CDF difference, then the target interval has positive
real-valued measure.
-/
theorem proposition8_positive_measure_of_support_subinterval
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {cdf : ℝ → ℝ} {I : Set ℝ} {vMin vMax a b : ℝ}
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ I)
    (hcdf_strict : StrictMonoOn cdf (Set.Ioo vMin vMax))
    (hmeasure_eq : μ.real (Set.Ioo a b) = cdf b - cdf a) :
    0 < μ.real I := by
  have hstrict : cdf a < cdf b := hcdf_strict ha hb hab
  have hinterval_pos : 0 < μ.real (Set.Ioo a b) := by
    rw [hmeasure_eq]
    linarith
  exact lt_of_lt_of_le hinterval_pos
    (measureReal_mono (μ := μ) hsub (measure_ne_top μ I))

/--
PG23 Theorem 2(i), strict top-choice comparison on a positive-measure witness
interval.  The pointwise strict comparison comes from the source CDF formulas
and strict cutoff inequality; positivity of the interval comes from the
connected-support Proposition 8 bridge.
-/
theorem theorem2_topChoice_strict_on_positive_measure_interval_of_cdf_formula
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {monoTop polyTop : ℕ → ℝ → ℝ}
    {cdf : ℝ → ℝ} {monoCutoff polyCutoff : ℕ → ℝ}
    {I : Set ℝ} {vMin vMax a b : ℝ} {m : ℕ}
    (hmono_formula :
      ∀ m v, monoTop m v = 1 - cdf (monoCutoff m - v))
    (hpoly_formula :
      ∀ m v, polyTop m v = 1 - cdf (polyCutoff m - v))
    (hcdf_cross_strict :
      ∀ v, monoCutoff m - v < polyCutoff m - v →
        cdf (monoCutoff m - v) < cdf (polyCutoff m - v))
    (hcutoff_strict : monoCutoff m < polyCutoff m)
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ I)
    (hcdf_support_strict : StrictMonoOn cdf (Set.Ioo vMin vMax))
    (hmeasure_eq : μ.real (Set.Ioo a b) = cdf b - cdf a) :
    (∀ v ∈ I, polyTop m v < monoTop m v) ∧ 0 < μ.real I := by
  constructor
  · intro v _hv
    rw [hmono_formula m v, hpoly_formula m v]
    have hshift : monoCutoff m - v < polyCutoff m - v := by
      linarith
    have hcdf := hcdf_cross_strict v hshift
    linarith
  · exact proposition8_positive_measure_of_support_subinterval
      ha hb hab hsub hcdf_support_strict hmeasure_eq

/--
PG23 Theorem 2(i), strict top-choice comparison on a positive-measure witness
interval for the concrete iid noise model.  The single-college CDF formula is
derived from iid product noise; strictness follows from strict monotonicity of
the one-dimensional noise CDF on the source support interval.
-/
theorem theorem2_topChoice_strict_on_positive_measure_interval_of_iidProduct_support
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {monoCutoff polyCutoff : ℕ → ℝ}
    {I : Set ℝ} {vMin vMax a b xMin xMax : ℝ} {m : ℕ}
    (hcutoff_strict : monoCutoff m < polyCutoff m)
    (hshift_mem :
      ∀ v ∈ I,
        monoCutoff m - v ∈ Set.Ioo xMin xMax ∧
          polyCutoff m - v ∈ Set.Ioo xMin xMax)
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (ha : a ∈ Set.Ioo vMin vMax)
    (hb : b ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hsub : Set.Ioo a b ⊆ I)
    {valueCDF : ℝ → ℝ}
    (hvalue_cdf_strict : StrictMonoOn valueCDF (Set.Ioo vMin vMax))
    (hmeasure_eq : μ.real (Set.Ioo a b) = valueCDF b - valueCDF a) :
    (∀ v ∈ I,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) <
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m)) ∧
      0 < μ.real I := by
  constructor
  · intro v hv
    rw [
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass]
    have hshift : monoCutoff m - v < polyCutoff m - v := by
      linarith
    have hmono_mem := (hshift_mem v hv).1
    have hpoly_mem := (hshift_mem v hv).2
    have hcdf :
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (monoCutoff m - v) <
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw (polyCutoff m - v) :=
      hnoise_cdf_strict hmono_mem hpoly_mem hshift
    linarith
  · exact proposition8_positive_measure_of_support_subinterval
      ha hb hab hsub hvalue_cdf_strict hmeasure_eq

/--
PG23 Theorem 2 aggregate-demand strictness input for polyculture access.
For at least two colleges, iid product noise makes the all-college
polyculture crossing probability strictly larger than one named college's
crossing probability on any positive-measure interval where the shifted
one-dimensional CDF mass is interior.
-/
theorem theorem2_polyculture_access_strict_measure_pos_of_iidProduct_support_region
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {m : ℕ} (hm : 0 < m) (topFirm : Fin (m + 1))
    {polyCutoff : ℕ → ℝ} {region : Set ℝ}
    (hregion_positive : 0 < μ.real region)
    (hcdf_mem :
      ∀ v ∈ region,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (polyCutoff m - v) ∈
          Set.Ioo (0 : ℝ) 1) :
    0 < μ {v |
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) topFirm <
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ : Fin (m + 1) => polyCutoff m)} := by
  let strictSet : Set ℝ :=
    {v |
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff m) topFirm <
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ : Fin (m + 1) => polyCutoff m)}
  have hn : 1 < m + 1 := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ hm
  have hsub : region ⊆ strictSet := by
    intro v hv
    exact
      singleCutoffCrossingProbability_lt_cutoffCrossingProbability_univ_constant_iidProduct
        noiseLaw (v := v) (P := polyCutoff m) topFirm hn
        (hcdf_mem v hv)
  have hreal : 0 < μ.real strictSet :=
    lt_of_lt_of_le hregion_positive
      (measureReal_mono (μ := μ) hsub (measure_ne_top μ strictSet))
  exact AppliedModelingLib.measure_pos_of_measureReal_pos μ strictSet hreal

/--
Eventual version of the iid strict polyculture-access premise.  This is the
asymptotic form needed by PG23: once the market has at least two colleges, the
strict all-versus-single comparison follows from the support-interior CDF
condition on the source region.
-/
theorem theorem2_polyculture_access_strict_eventually_of_iidProduct_support_region
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    {polyCutoff : ℕ → ℝ} {region : Set ℝ}
    (hregion_positive : 0 < μ.real region)
    (hcdf_mem :
      ∀ m v, v ∈ region →
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (polyCutoff m - v) ∈
          Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ m : ℕ in atTop,
      0 < μ {v |
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
            v (fun _ : Fin (m + 1) => polyCutoff m) (topFirm m) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ : Fin (m + 1) => polyCutoff m)} := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  exact
    theorem2_polyculture_access_strict_measure_pos_of_iidProduct_support_region
      μ noiseLaw hm (topFirm m) hregion_positive
      (fun v hv => hcdf_mem m v hv)

/--
PG23 Theorem 3, paper-facing differential-access skeleton: in monoculture the
match probability is application-access invariant, while in polyculture it is
monotone in application access.
-/
structure Theorem3DifferentialAccessConclusion
    (monoAccess polyAccess : ℕ → ℕ → ℝ → ℝ) : Prop where
  monoculture_access_invariant :
    ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v
  polyculture_access_monotone :
    ∀ m k₁ k₂ v, k₁ ≤ k₂ → polyAccess m k₁ v ≤ polyAccess m k₂ v

/--
PG23 Theorem 3 with the strict source interval exposed: monoculture access is
invariant, polyculture access is weakly monotone in application access, and on
the interval where the CDF term lies strictly between zero and one, the
polyculture access probability is strictly increasing in the number of
applications.
-/
structure Theorem3DifferentialAccessStrictConclusion
    (monoAccess polyAccess : ℕ → ℕ → ℝ → ℝ)
    (strictRegion : ℕ → ℝ → Prop) : Prop where
  monoculture_access_invariant :
    ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v
  polyculture_access_monotone :
    ∀ m k₁ k₂ v, k₁ ≤ k₂ → polyAccess m k₁ v ≤ polyAccess m k₂ v
  polyculture_access_strict :
    ∀ m v, strictRegion m v →
      ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
        polyAccess m k₁ v < polyAccess m k₂ v

/--
PG23 Theorem 3 source clauses.  This projection exposes the three
paper-facing conclusions carried by the strict differential-access theorem:
monoculture invariance in application access, weak polyculture monotonicity,
and strict polyculture improvement on the support-interior region.
-/
theorem theorem3_differentialAccessStrict_source_clauses
    {monoAccess polyAccess : ℕ → ℕ → ℝ → ℝ}
    {strictRegion : ℕ → ℝ → Prop}
    (h :
      Theorem3DifferentialAccessStrictConclusion
        monoAccess polyAccess strictRegion) :
    (∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v) ∧
      (∀ m k₁ k₂ v, k₁ ≤ k₂ →
        polyAccess m k₁ v ≤ polyAccess m k₂ v) ∧
      (∀ m v, strictRegion m v →
        ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
          polyAccess m k₁ v < polyAccess m k₂ v) :=
  ⟨h.monoculture_access_invariant, h.polyculture_access_monotone,
    h.polyculture_access_strict⟩

/--
PG23 Theorem 3 strict scalar formula: when `0 < F < 1`, the source
probability `1 - F^k` is strictly increasing in the number of applications
`k`.
-/
theorem theorem3_polycultureAccessProbability_strict_of_cdf_pow
    {F : ℝ} (hF_pos : 0 < F) (hF_lt_one : F < 1) :
    ∀ {k₁ k₂ : ℕ}, k₁ < k₂ → 1 - F ^ k₁ < 1 - F ^ k₂ := by
  intro k₁ k₂ hk
  have hpow : F ^ k₂ < F ^ k₁ :=
    pow_lt_pow_right_of_lt_one₀ hF_pos hF_lt_one hk
  linarith

/--
PG23 Theorem 3 strict polyculture access consequence from the paper's scalar
CDF formula.  On the source interval where `F_X(P - v) ∈ (0,1)`, the formula
`Pr[match | k] = 1 - F_X(P - v)^k` is strictly increasing in `k`.
-/
theorem theorem3_polycultureAccess_strict_of_cdf_formula
    {polyAccess : ℕ → ℕ → ℝ → ℝ}
    {cdfAtCutoff : ℕ → ℝ → ℝ}
    {strictRegion : ℕ → ℝ → Prop}
    (hformula :
      ∀ m k v, polyAccess m k v = 1 - (cdfAtCutoff m v) ^ k)
    (hcdf :
      ∀ m v, strictRegion m v →
        0 < cdfAtCutoff m v ∧ cdfAtCutoff m v < 1) :
    ∀ m v, strictRegion m v →
      ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
        polyAccess m k₁ v < polyAccess m k₂ v := by
  intro m v hregion k₁ k₂ hk
  rcases hcdf m v hregion with ⟨hpos, hlt⟩
  rw [hformula m k₁ v, hformula m k₂ v]
  exact theorem3_polycultureAccessProbability_strict_of_cdf_pow hpos hlt hk

/--
PG23 Theorem 3 strict polyculture access consequence in the source support
form.  On values satisfying `P - v ∈ (X_-, X_+)`, the CDF term in
`1 - F_X(P - v)^k` lies in `(0,1)`, so access probability is strictly
increasing in `k`.
-/
theorem theorem3_polycultureAccess_strict_of_cdf_support_formula
    {polyAccess : ℕ → ℕ → ℝ → ℝ}
    {cdf : ℝ → ℝ} {cutoff : ℕ → ℝ} {xMin xMax : ℝ}
    (hformula :
      ∀ m k v, polyAccess m k v = 1 - (cdf (cutoff m - v)) ^ k)
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax, cdf x ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ m v, cutoff m - v ∈ Set.Ioo xMin xMax →
      ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
        polyAccess m k₁ v < polyAccess m k₂ v :=
  theorem3_polycultureAccess_strict_of_cdf_formula
    hformula
    (by
      intro m v hregion
      exact hcdf_mem (cutoff m - v) hregion)

/--
PG23 Theorem 3 probability implication from explicit active application
sets.  If monoculture access is invariant in the number of applications and
the polyculture active college sets are nested as `k` grows, then the
polyculture affordance probability is monotone in application access.
-/
theorem theorem3_differentialAccess_of_activeSet_monotone
    {monoAccess : ℕ → ℕ → ℝ → ℝ}
    {sampleLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (active : ∀ m _k : ℕ, Finset (Fin (m + 1)))
    (cutoff : ∀ m : ℕ, Fin (m + 1) → ℝ)
    (hfinite : ∀ m, IsFiniteMeasure (sampleLaw m))
    (hmono : ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v)
    (hsubset :
      ∀ m k₁ k₂, k₁ ≤ k₂ → active m k₁ ⊆ active m k₂) :
    Theorem3DifferentialAccessConclusion
      monoAccess
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw m) (active m k) v (cutoff m)) := by
  refine ⟨hmono, ?_⟩
  intro m k₁ k₂ v hk
  haveI : IsFiniteMeasure (sampleLaw m) := hfinite m
  exact
    AppliedModelingLib.Matching.cutoffCrossingProbability_mono_active
      (sampleLaw m) (hsubset m k₁ k₂ hk)

/--
PG23 Theorem 3 full source route: nested active sets give weak polyculture
monotonicity, the monoculture equality premise gives access invariance, and
the displayed CDF formula gives strict polyculture improvement on the source
interior interval.
-/
theorem theorem3_differentialAccess_strict_of_activeSet_and_cdf_formula
    {monoAccess : ℕ → ℕ → ℝ → ℝ}
    {sampleLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (active : ∀ m _k : ℕ, Finset (Fin (m + 1)))
    (cutoff : ∀ m : ℕ, Fin (m + 1) → ℝ)
    {cdfAtCutoff : ℕ → ℝ → ℝ}
    {strictRegion : ℕ → ℝ → Prop}
    (hfinite : ∀ m, IsFiniteMeasure (sampleLaw m))
    (hmono : ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v)
    (hsubset :
      ∀ m k₁ k₂, k₁ ≤ k₂ → active m k₁ ⊆ active m k₂)
    (hformula :
      ∀ m k v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw m) (active m k) v (cutoff m) =
          1 - (cdfAtCutoff m v) ^ k)
    (hcdf :
      ∀ m v, strictRegion m v →
        0 < cdfAtCutoff m v ∧ cdfAtCutoff m v < 1) :
    Theorem3DifferentialAccessStrictConclusion
      monoAccess
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw m) (active m k) v (cutoff m))
      strictRegion := by
  have hweak :=
    theorem3_differentialAccess_of_activeSet_monotone
      (monoAccess := monoAccess)
      (sampleLaw := sampleLaw)
      active cutoff hfinite hmono hsubset
  refine ⟨hweak.monoculture_access_invariant, hweak.polyculture_access_monotone, ?_⟩
  exact theorem3_polycultureAccess_strict_of_cdf_formula hformula hcdf

/--
PG23 Theorem 3 full source route in support-interval form: nested active sets
give weak polyculture monotonicity, monoculture access is invariant, and the
source formula `1 - F_X(P - v)^k` gives strict improvement exactly when
`P - v` lies inside the noise support interval.
-/
theorem theorem3_differentialAccess_strict_of_activeSet_and_cdf_support_formula
    {monoAccess : ℕ → ℕ → ℝ → ℝ}
    {sampleLaw : ∀ m : ℕ, Measure (Fin (m + 1) → ℝ)}
    (active : ∀ m _k : ℕ, Finset (Fin (m + 1)))
    (cutoffVector : ∀ m : ℕ, Fin (m + 1) → ℝ)
    {cdf : ℝ → ℝ} {cutoffScalar : ℕ → ℝ} {xMin xMax : ℝ}
    (hfinite : ∀ m, IsFiniteMeasure (sampleLaw m))
    (hmono : ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v)
    (hsubset :
      ∀ m k₁ k₂, k₁ ≤ k₂ → active m k₁ ⊆ active m k₂)
    (hformula :
      ∀ m k v,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw m) (active m k) v (cutoffVector m) =
          1 - (cdf (cutoffScalar m - v)) ^ k)
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax, cdf x ∈ Set.Ioo (0 : ℝ) 1) :
    Theorem3DifferentialAccessStrictConclusion
      monoAccess
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw m) (active m k) v (cutoffVector m))
      (fun m v => cutoffScalar m - v ∈ Set.Ioo xMin xMax) := by
  have hweak :=
    theorem3_differentialAccess_of_activeSet_monotone
      (monoAccess := monoAccess)
      (sampleLaw := sampleLaw)
      active cutoffVector hfinite hmono hsubset
  refine ⟨hweak.monoculture_access_invariant, hweak.polyculture_access_monotone, ?_⟩
  exact
    theorem3_polycultureAccess_strict_of_cdf_support_formula
      (polyAccess := fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (sampleLaw m) (active m k) v (cutoffVector m))
      (cdf := cdf) (cutoff := cutoffScalar)
      (xMin := xMin) (xMax := xMax)
      hformula hcdf_mem

/--
PG23 Theorem 3 polyculture monotonicity from an explicit iid source model.
With `k + 1` accessible colleges, iid noise, and a constant polyculture
cutoff, the source CDF formula is derived from the order-statistics library;
no separate CDF-formula premise is needed.
-/
theorem theorem3_polycultureAccess_iidProduct_positive_monotone
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : ℕ → ℝ) :
    ∀ m k₁ k₂ v, k₁ ≤ k₂ →
      AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₁ + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k₁ + 1))) v
          (fun _ : Fin (k₁ + 1) => cutoff m) ≤
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₂ + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k₂ + 1))) v
          (fun _ : Fin (k₂ + 1) => cutoff m) := by
  intro m k₁ k₂ v hk
  rw [
    AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow,
    AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow]
  have hF_le_one :
      AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff m - v) ≤ 1 :=
    AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw (cutoff m - v)
  have hF_nonneg :
      0 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff m - v) :=
    AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw (cutoff m - v)
  have hpow :
      (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff m - v)) ^ (k₂ + 1) ≤
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff m - v)) ^ (k₁ + 1) :=
    pow_le_pow_of_le_one hF_nonneg hF_le_one (Nat.succ_le_succ hk)
  linarith

/--
PG23 Theorem 3 strict polyculture improvement from an explicit iid source
model.  On the source support interior where the CDF mass is strictly between
zero and one, adding an accessible college strictly increases the match
probability.
-/
theorem theorem3_polycultureAccess_iidProduct_positive_strict_of_cdf_support
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw x ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ m v, cutoff m - v ∈ Set.Ioo xMin xMax →
      ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁ + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (k₁ + 1))) v
            (fun _ : Fin (k₁ + 1) => cutoff m) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂ + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (k₂ + 1))) v
            (fun _ : Fin (k₂ + 1) => cutoff m) := by
  intro m v hregion k₁ k₂ hk
  rcases hcdf_mem (cutoff m - v) hregion with ⟨hpos, hlt⟩
  rw [
    AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow,
    AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow]
  exact
    theorem3_polycultureAccessProbability_strict_of_cdf_pow
      hpos hlt (Nat.succ_lt_succ hk)

/--
PG23 Theorem 3 full positive-access source route.  Monoculture invariance is
kept as the paper's source equality, while the polyculture weak and strict
access comparisons are derived from iid noise, a constant polyculture cutoff,
and the source support-interior CDF condition.
-/
theorem theorem3_differentialAccess_strict_of_positive_iidProduct_cdf_support
    {monoAccess : ℕ → ℕ → ℝ → ℝ}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hmono : ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v)
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw x ∈ Set.Ioo (0 : ℝ) 1) :
    Theorem3DifferentialAccessStrictConclusion
      monoAccess
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k + 1))) v
          (fun _ : Fin (k + 1) => cutoff m))
      (fun m v => cutoff m - v ∈ Set.Ioo xMin xMax) := by
  refine ⟨hmono, ?_, ?_⟩
  · exact theorem3_polycultureAccess_iidProduct_positive_monotone noiseLaw cutoff
  · exact theorem3_polycultureAccess_iidProduct_positive_strict_of_cdf_support
      noiseLaw cutoff hcdf_mem

/--
PG23 Theorem 3 full positive-access source route with the exact source
interior-CDF condition.  This avoids requiring global strict-CDF endpoint data
when the theorem only needs that every shifted cutoff in the support interior
has one-dimensional CDF mass strictly between zero and one.
-/
theorem theorem3_differentialAccess_strict_of_constant_mono_positive_iidProduct_cdf_support
    (monoAccess : ℕ → ℝ → ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw x ∈ Set.Ioo (0 : ℝ) 1) :
    Theorem3DifferentialAccessStrictConclusion
      (fun m _k v => monoAccess m v)
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k + 1))) v
          (fun _ : Fin (k + 1) => cutoff m))
      (fun m v => cutoff m - v ∈ Set.Ioo xMin xMax) :=
  theorem3_differentialAccess_strict_of_positive_iidProduct_cdf_support
    noiseLaw cutoff
    (by intro m k₁ k₂ v; rfl)
    hcdf_mem

/--
PG23 Theorem 3 full positive-access source route with the CDF-interior
condition derived from strict support monotonicity and endpoint CDF values.
-/
theorem theorem3_differentialAccess_strict_of_positive_iidProduct_cdf_strict_support
    {monoAccess : ℕ → ℕ → ℝ → ℝ}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hmono : ∀ m k₁ k₂ v, monoAccess m k₁ v = monoAccess m k₂ v)
    (hcdf_strict :
      StrictMonoOn
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1) :
    Theorem3DifferentialAccessStrictConclusion
      monoAccess
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k + 1))) v
          (fun _ : Fin (k + 1) => cutoff m))
      (fun m v => cutoff m - v ∈ Set.Ioo xMin xMax) :=
  theorem3_differentialAccess_strict_of_positive_iidProduct_cdf_support
    noiseLaw cutoff hmono
    (fun _ hx =>
      AppliedModelingLib.Probability.lowerCDFMass_mem_Ioo_of_strictMonoOn_Icc_endpoint_values
        noiseLaw hcdf_strict hleft hright hx)

/--
PG23 Theorem 3 full positive-access source route with monoculture invariance
derived from the source representation that monoculture access does not
depend on application count.
-/
theorem theorem3_differentialAccess_strict_of_constant_mono_positive_iidProduct_cdf_strict_support
    (monoAccess : ℕ → ℝ → ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hcdf_strict :
      StrictMonoOn
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1) :
    Theorem3DifferentialAccessStrictConclusion
      (fun m _k v => monoAccess m v)
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k + 1))) v
          (fun _ : Fin (k + 1) => cutoff m))
      (fun m v => cutoff m - v ∈ Set.Ioo xMin xMax) :=
  theorem3_differentialAccess_strict_of_positive_iidProduct_cdf_strict_support
    noiseLaw cutoff
    (by intro m k₁ k₂ v; rfl)
    hcdf_strict hleft hright

/--
PG23 Theorem 3 full positive-access source route with monoculture access
instantiated by the concrete iid single-cutoff probability.  This removes the
remaining abstract monoculture-access function from the iid Theorem 3 route:
application-access invariance is definitional for monoculture, while weak and
strict polyculture access are derived from iid product noise and the exact
interior-CDF condition.
-/
theorem theorem3_differentialAccess_strict_of_iidProduct_mono_singleCutoff_positive_iidProduct_cdf_support
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoCutoff polyCutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw x ∈ Set.Ioo (0 : ℝ) 1) :
    Theorem3DifferentialAccessStrictConclusion
      (fun m _k v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k + 1))) v
          (fun _ : Fin (k + 1) => polyCutoff m))
      (fun m v => polyCutoff m - v ∈ Set.Ioo xMin xMax) :=
  theorem3_differentialAccess_strict_of_constant_mono_positive_iidProduct_cdf_support
    (fun m v =>
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
        v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
    noiseLaw polyCutoff hcdf_mem

/--
PG23 Theorem 3 source clauses from the concrete iid cutoff model with the
exact interior-CDF condition.  This is the closest source-shaped version of
the differential-access theorem: the only CDF premise is that the relevant
support-interior mass lies in `(0,1)`.
-/
theorem theorem3_differentialAccessStrict_source_clauses_of_iidProduct_mono_singleCutoff_positive_iidProduct_cdf_support
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoCutoff polyCutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hcdf_mem :
      ∀ x ∈ Set.Ioo xMin xMax,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw x ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ (m : ℕ) (_k₁ _k₂ : ℕ) (v : ℝ),
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m) =
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m)) ∧
      (∀ (m k₁ k₂ : ℕ) (v : ℝ), k₁ ≤ k₂ →
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁ + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (k₁ + 1))) v
            (fun _ : Fin (k₁ + 1) => polyCutoff m) ≤
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂ + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (k₂ + 1))) v
            (fun _ : Fin (k₂ + 1) => polyCutoff m)) ∧
      (∀ (m : ℕ) (v : ℝ), polyCutoff m - v ∈ Set.Ioo xMin xMax →
        ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
          AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (k₁ + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (k₁ + 1))) v
              (fun _ : Fin (k₁ + 1) => polyCutoff m) <
            AppliedModelingLib.Matching.cutoffCrossingProbability
              (Measure.pi (fun _ : Fin (k₂ + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (k₂ + 1))) v
              (fun _ : Fin (k₂ + 1) => polyCutoff m)) :=
  theorem3_differentialAccessStrict_source_clauses
    (theorem3_differentialAccess_strict_of_iidProduct_mono_singleCutoff_positive_iidProduct_cdf_support
      noiseLaw topFirm monoCutoff polyCutoff hcdf_mem)

/--
PG23 Theorem 3 full positive-access source route with monoculture access
instantiated by the concrete iid single-cutoff probability.  This removes the
remaining abstract monoculture-access function from the iid Theorem 3 route:
application-access invariance is definitional for monoculture, while weak and
strict polyculture access are derived from iid product noise and support CDF
monotonicity.
-/
theorem theorem3_differentialAccess_strict_of_iidProduct_mono_singleCutoff_positive_iidProduct_cdf_strict_support
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : ∀ m : ℕ, Fin (m + 1))
    (monoCutoff polyCutoff : ℕ → ℝ) {xMin xMax : ℝ}
    (hcdf_strict :
      StrictMonoOn
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Icc xMin xMax))
    (hleft : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hright : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1) :
    Theorem3DifferentialAccessStrictConclusion
      (fun m _k v =>
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
      (fun m k v =>
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (k + 1))) v
          (fun _ : Fin (k + 1) => polyCutoff m))
      (fun m v => polyCutoff m - v ∈ Set.Ioo xMin xMax) :=
  theorem3_differentialAccess_strict_of_constant_mono_positive_iidProduct_cdf_strict_support
    (fun m v =>
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
        v (fun _ : Fin (m + 1) => monoCutoff m) (topFirm m))
    noiseLaw polyCutoff hcdf_strict hleft hright

/--
Strict growth of a lower CDF from a point in the open support interval to any
larger point.  The right point need not itself lie in the open support: if it
is beyond the upper endpoint, strict growth to an intermediate interior point
and CDF monotonicity suffice.

This is the precise source step used in PG23 Theorem 2(i), where
`P_poly - v` may lie beyond `X_+`.
-/
theorem lowerCDFMass_lt_of_left_mem_open_support_of_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {xMin xMax x y : ℝ}
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass μ) (Set.Ioo xMin xMax))
    (hx : x ∈ Set.Ioo xMin xMax)
    (hxy : x < y) :
    AppliedModelingLib.Probability.lowerCDFMass μ x <
      AppliedModelingLib.Probability.lowerCDFMass μ y := by
  by_cases hy : y < xMax
  · have hy_mem : y ∈ Set.Ioo xMin xMax :=
      ⟨lt_trans hx.1 hxy, hy⟩
    exact hcdf_strict hx hy_mem hxy
  · have hxMax_le_y : xMax ≤ y := le_of_not_gt hy
    let z : ℝ := (x + xMax) / 2
    have hx_lt_z : x < z := by
      dsimp [z]
      linarith [hx.2]
    have hz_lt_xMax : z < xMax := by
      dsimp [z]
      linarith [hx.2]
    have hz : z ∈ Set.Ioo xMin xMax :=
      ⟨lt_trans hx.1 hx_lt_z, hz_lt_xMax⟩
    exact
      (hcdf_strict hx hz hx_lt_z).trans_le
        (AppliedModelingLib.Probability.lowerCDFMass_mono μ
          (le_trans (le_of_lt hz_lt_xMax) hxMax_le_y))

/--
An open interval has positive mass when it intersects an open value-support
interval on which the actual lower CDF is strictly increasing.  The proof uses
an interior right-closed subinterval, so it does not assume a false open-CDF
mass identity in the presence of endpoint atoms.
-/
theorem positive_measure_open_interval_of_intersects_open_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b vMin vMax : ℝ}
    (hintersects :
      (Set.Ioo a b ∩ Set.Ioo vMin vMax).Nonempty)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass μ) (Set.Ioo vMin vMax)) :
    0 < μ.real (Set.Ioo a b) := by
  rcases hintersects with ⟨x, hx_interval, hx_support⟩
  let lo : ℝ := max a vMin
  let hi : ℝ := min b vMax
  have hlo_lt_x : lo < x := by
    dsimp [lo]
    exact max_lt hx_interval.1 hx_support.1
  have hx_lt_hi : x < hi := by
    dsimp [hi]
    exact lt_min hx_interval.2 hx_support.2
  let c : ℝ := (lo + x) / 2
  let d : ℝ := (x + hi) / 2
  have hlo_lt_c : lo < c := by
    dsimp [c]
    linarith
  have hc_lt_x : c < x := by
    dsimp [c]
    linarith
  have hx_lt_d : x < d := by
    dsimp [d]
    linarith
  have hd_lt_hi : d < hi := by
    dsimp [d]
    linarith
  have hac : a < c :=
    lt_of_le_of_lt (le_max_left a vMin) hlo_lt_c
  have hdb : d < b :=
    lt_of_lt_of_le hd_lt_hi (min_le_left b vMax)
  have hc_support : c ∈ Set.Ioo vMin vMax := by
    constructor
    · exact lt_of_le_of_lt (le_max_right a vMin) hlo_lt_c
    · exact lt_trans hc_lt_x hx_support.2
  have hd_support : d ∈ Set.Ioo vMin vMax := by
    constructor
    · exact lt_trans hx_support.1 hx_lt_d
    · exact lt_of_lt_of_le hd_lt_hi (min_le_right b vMax)
  have hcd : c < d := lt_trans hc_lt_x hx_lt_d
  have hsub : Set.Ioc c d ⊆ Set.Ioo a b := by
    intro z hz
    exact ⟨lt_trans hac hz.1, lt_of_le_of_lt hz.2 hdb⟩
  have hIoc_pos : 0 < μ.real (Set.Ioc c d) := by
    change 0 < AppliedModelingLib.Probability.intervalOCMass μ c d
    rw [AppliedModelingLib.Probability.intervalOCMass_eq_cdf_sub μ hcd.le]
    rw [← AppliedModelingLib.Probability.lowerCDFMass_eq_cdf μ d,
      ← AppliedModelingLib.Probability.lowerCDFMass_eq_cdf μ c]
    exact sub_pos.mpr (hcdf_strict hc_support hd_support hcd)
  exact
    lt_of_lt_of_le hIoc_pos
      (measureReal_mono (μ := μ) hsub (measure_ne_top μ _))

/--
The source cutoff bounds imply that the exact PG23 Theorem 2 noise interval
intersects the interior value support.  This is the geometric content of the
source proof preceding equation `interval-mono`.
-/
theorem source_interval_intersects_value_support_of_sum_bounds
    {vMin vMax xMin xMax cutoff : ℝ}
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hlower : vMin + xMin < cutoff)
    (hupper : cutoff < vMax + xMax) :
    (Set.Ioo (cutoff - xMax) (cutoff - xMin) ∩
      Set.Ioo vMin vMax).Nonempty := by
  rcases
      exists_lower_support_point_of_sum_bounds hvalue_nonempty hnoise_nonempty
        hlower hupper with
    ⟨v, hv_support, hv_shift⟩
  refine ⟨v, ?_, hv_support⟩
  constructor <;> linarith [hv_shift.1, hv_shift.2]

/--
The positive-measure clause of PG23 Theorem 2(i) under the finite-endpoint
specialization used by the existing clearing development.  The cutoff bounds
are visible rather than being hidden in a source-model record.
-/
theorem theorem2_source_interval_positive_measure_of_sum_bounds
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {vMin vMax xMin xMax monoCutoff : ℝ}
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hcutoff_lower : vMin + xMin < monoCutoff)
    (hcutoff_upper : monoCutoff < vMax + xMax)
    (hvalue_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass η) (Set.Ioo vMin vMax)) :
    0 < η.real (Set.Ioo (monoCutoff - xMax) (monoCutoff - xMin)) :=
  positive_measure_open_interval_of_intersects_open_support η
    (source_interval_intersects_value_support_of_sum_bounds
      hvalue_nonempty hnoise_nonempty hcutoff_lower hcutoff_upper)
    hvalue_cdf_strict

/--
PG23 Theorem 2(i), weak top-choice comparison for every value in the concrete
iid model.  This is the source formula plus cutoff order, with no support
restriction because lower-CDF mass is monotone globally.
-/
theorem theorem2_topChoice_weak_of_iidProduct
    {m : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : Fin (m + 1)) {monoCutoff polyCutoff : ℝ}
    (hcutoff : monoCutoff ≤ polyCutoff) :
    ∀ v : ℝ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff) topFirm ≤
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff) topFirm := by
  intro v
  rw [
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass,
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass]
  have hshift : monoCutoff - v ≤ polyCutoff - v := by
    linarith
  have hcdf := AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw hshift
  linarith

/--
PG23 Theorem 2(i), strict top-choice comparison on the exact printed interval
`(P_mono - X_+, P_mono - X_-)`.  Only the monoculture shifted cutoff must be
inside the noise support; the polyculture shifted cutoff can be above `X_+`.
-/
theorem theorem2_topChoice_strict_on_source_interval_of_iidProduct
    {m : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : Fin (m + 1)) {monoCutoff polyCutoff xMin xMax : ℝ}
    (hcutoff_strict : monoCutoff < polyCutoff)
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax)) :
    ∀ v ∈ Set.Ioo (monoCutoff - xMax) (monoCutoff - xMin),
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => polyCutoff) topFirm <
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff) topFirm := by
  intro v hv
  rw [
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass,
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass]
  have hmono_shift : monoCutoff - v ∈ Set.Ioo xMin xMax := by
    constructor <;> linarith [hv.1, hv.2]
  have hshift : monoCutoff - v < polyCutoff - v := by
    linarith
  have hcdf :=
    lowerCDFMass_lt_of_left_mem_open_support_of_lt noiseLaw hnoise_cdf_strict
      hmono_shift hshift
  linarith

/--
Strict CDF growth on an open support interval implies positive lower-CDF mass
at every point strictly to the right of its lower endpoint.  This does not
assume that the CDF vanishes at that endpoint, so endpoint atoms are handled
correctly.
-/
theorem lowerCDFMass_pos_of_gt_left_open_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {xMin xMax y : ℝ}
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass μ) (Set.Ioo xMin xMax))
    (hsupport_nonempty : xMin < xMax)
    (hy : xMin < y) :
    0 < AppliedModelingLib.Probability.lowerCDFMass μ y := by
  let hi : ℝ := min y xMax
  have hxMin_lt_hi : xMin < hi := by
    dsimp [hi]
    exact lt_min hy hsupport_nonempty
  let d : ℝ := (xMin + hi) / 2
  let c : ℝ := (xMin + d) / 2
  have hxMin_lt_d : xMin < d := by
    dsimp [d]
    linarith
  have hd_lt_hi : d < hi := by
    dsimp [d]
    linarith
  have hxMin_lt_c : xMin < c := by
    dsimp [c]
    linarith
  have hc_lt_d : c < d := by
    dsimp [c]
    linarith
  have hc : c ∈ Set.Ioo xMin xMax := by
    constructor
    · exact hxMin_lt_c
    · exact
        lt_trans hc_lt_d
          (lt_of_lt_of_le hd_lt_hi (min_le_right y xMax))
  have hd : d ∈ Set.Ioo xMin xMax := by
    constructor
    · exact hxMin_lt_d
    · exact lt_of_lt_of_le hd_lt_hi (min_le_right y xMax)
  have hstrict :
      AppliedModelingLib.Probability.lowerCDFMass μ c <
        AppliedModelingLib.Probability.lowerCDFMass μ d :=
    hcdf_strict hc hd hc_lt_d
  have hd_pos : 0 < AppliedModelingLib.Probability.lowerCDFMass μ d :=
    lt_of_le_of_lt (AppliedModelingLib.Probability.lowerCDFMass_nonneg μ c) hstrict
  exact
    lt_of_lt_of_le hd_pos
      (AppliedModelingLib.Probability.lowerCDFMass_mono μ
        (le_trans (le_of_lt hd_lt_hi) (min_le_left y xMax)))

/--
PG23 Theorem 2(iii)'s monoculture support step.  Below `P_mono - X_-`, the
single-cutoff iid monoculture match probability is strictly below one.
-/
theorem theorem2_monoSingleCutoffMatch_lt_one_below_source_upper_of_iidProduct
    {m : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : Fin (m + 1)) {monoCutoff xMin xMax : ℝ}
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hnoise_nonempty : xMin < xMax) :
    ∀ v : ℝ, v < monoCutoff - xMin →
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff) topFirm < 1 := by
  intro v hv
  apply
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_lt_one_of_lowerCDFMass_pos
      noiseLaw topFirm
  apply lowerCDFMass_pos_of_gt_left_open_support noiseLaw hnoise_cdf_strict
    hnoise_nonempty
  linarith

/--
Any interval beginning at an interior value-support point has positive mass
when it is nonempty.  This is the exact positive-measure mechanism used for
the Theorem 2(iii) interval after the source threshold inequality is proved.
-/
theorem positive_measure_open_interval_of_left_mem_open_support_of_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {vMin vMax a b : ℝ}
    (ha : a ∈ Set.Ioo vMin vMax)
    (hab : a < b)
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass μ) (Set.Ioo vMin vMax)) :
    0 < μ.real (Set.Ioo a b) := by
  let z : ℝ := (a + min b vMax) / 2
  have ha_lt_min : a < min b vMax :=
    lt_min hab ha.2
  have ha_lt_z : a < z := by
    dsimp [z]
    linarith
  have hz_lt_min : z < min b vMax := by
    dsimp [z]
    linarith
  have hz_interval : z ∈ Set.Ioo a b :=
    ⟨ha_lt_z, lt_of_lt_of_le hz_lt_min (min_le_left b vMax)⟩
  have hz_support : z ∈ Set.Ioo vMin vMax :=
    ⟨lt_trans ha.1 ha_lt_z, lt_of_lt_of_le hz_lt_min (min_le_right b vMax)⟩
  exact
    positive_measure_open_interval_of_intersects_open_support μ
      ⟨z, hz_interval, hz_support⟩ hcdf_strict

/--
The positive-measure clause of PG23 Theorem 2(iii), once the source proof's
threshold bound `v_S < P_mono - X_-` has been established.
-/
theorem theorem2_eventual_source_interval_positive_measure_of_threshold_bound
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {vMin vMax vS monoCutoff xMin : ℝ}
    (hthreshold_interior : vS ∈ Set.Ioo vMin vMax)
    (hthreshold_lt : vS < monoCutoff - xMin)
    (hvalue_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass η) (Set.Ioo vMin vMax)) :
    0 < η.real (Set.Ioo vS (monoCutoff - xMin)) :=
  positive_measure_open_interval_of_left_mem_open_support_of_lt η
    hthreshold_interior hthreshold_lt hvalue_cdf_strict

/--
PG23 Theorem 2(iii), pointwise eventual strict mono-versus-poly match
comparison on the exact printed interval.  The source's Theorem 1 provides
the high-value polyculture limit; the concrete iid monoculture formula is
strictly below one below `P_mono - X_-`.
-/
theorem theorem2_match_strict_eventually_on_source_interval_of_iidProduct
    {polyMatch : ℕ → ℝ → ℝ}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (topFirm : Fin 1) {vS monoCutoff xMin xMax : ℝ}
    (hpoly_tendsto_one :
      ∀ v : ℝ, vS < v → Tendsto (fun m : ℕ => polyMatch m v) atTop (nhds 1))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hnoise_nonempty : xMin < xMax) :
    ∀ v ∈ Set.Ioo vS (monoCutoff - xMin),
      ∀ᶠ m : ℕ in atTop,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin 1 => noiseLaw))
            v (fun _ : Fin 1 => monoCutoff) topFirm <
          polyMatch m v := by
  intro v hv
  let monoMatch : ℝ :=
    AppliedModelingLib.Matching.singleCutoffCrossingProbability
      (Measure.pi (fun _ : Fin 1 => noiseLaw))
      v (fun _ : Fin 1 => monoCutoff) topFirm
  have hmono_lt_one : monoMatch < 1 := by
    dsimp [monoMatch]
    exact
      theorem2_monoSingleCutoffMatch_lt_one_below_source_upper_of_iidProduct
        noiseLaw topFirm hnoise_cdf_strict hnoise_nonempty v hv.2
  let gap : ℝ := (1 - monoMatch) / 2
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  have hlimit_event : ∀ᶠ m : ℕ in atTop, 1 - gap < polyMatch m v := by
    apply hpoly_tendsto_one v hv.1
    apply isOpen_Ioi.mem_nhds
    exact sub_lt_self (1 : ℝ) hgap_pos
  filter_upwards [hlimit_event] with m hm
  have hmono_lt_threshold : monoMatch < 1 - gap := by
    dsimp [gap]
    linarith
  change monoMatch < polyMatch m v
  linarith

/--
Strict CDF growth on an open support interval puts the lower CDF strictly below
one at every point to the left of the upper endpoint.  This is the atom-safe
counterpart to `lowerCDFMass_pos_of_gt_left_open_support`.
-/
theorem lowerCDFMass_lt_one_of_lt_right_open_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {xMin xMax y : ℝ}
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass μ) (Set.Ioo xMin xMax))
    (hsupport_nonempty : xMin < xMax)
    (hy : y < xMax) :
    AppliedModelingLib.Probability.lowerCDFMass μ y < 1 := by
  let lo : ℝ := max y xMin
  have hlo_lt_xMax : lo < xMax := by
    dsimp [lo]
    exact max_lt hy hsupport_nonempty
  let c : ℝ := (lo + xMax) / 2
  let d : ℝ := (c + xMax) / 2
  have hlo_lt_c : lo < c := by
    dsimp [c]
    linarith
  have hc_lt_xMax : c < xMax := by
    dsimp [c]
    linarith
  have hc_lt_d : c < d := by
    dsimp [d]
    linarith
  have hd_lt_xMax : d < xMax := by
    dsimp [d]
    linarith
  have hc : c ∈ Set.Ioo xMin xMax := by
    constructor
    · exact lt_of_le_of_lt (le_max_right y xMin) hlo_lt_c
    · exact hc_lt_xMax
  have hd : d ∈ Set.Ioo xMin xMax := by
    constructor
    · exact lt_trans hc.1 hc_lt_d
    · exact hd_lt_xMax
  have hstrict :
      AppliedModelingLib.Probability.lowerCDFMass μ c <
        AppliedModelingLib.Probability.lowerCDFMass μ d :=
    hcdf_strict hc hd hc_lt_d
  have hy_le_c : y ≤ c :=
    le_trans (le_max_left y xMin) (le_of_lt hlo_lt_c)
  exact
    (AppliedModelingLib.Probability.lowerCDFMass_mono μ hy_le_c).trans_lt
      (hstrict.trans_le (AppliedModelingLib.Probability.lowerCDFMass_le_one μ d))

/--
At an interior point of an open support interval, the actual lower CDF lies in
`(0, 1)`.  No endpoint CDF convention is assumed, so atoms at support
endpoints do not affect this fact.
-/
theorem lowerCDFMass_mem_Ioo_zero_one_of_mem_open_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {xMin xMax y : ℝ}
    (hcdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass μ) (Set.Ioo xMin xMax))
    (hy : y ∈ Set.Ioo xMin xMax) :
    AppliedModelingLib.Probability.lowerCDFMass μ y ∈ Set.Ioo (0 : ℝ) 1 := by
  have hsupport_nonempty : xMin < xMax := lt_trans hy.1 hy.2
  constructor
  · exact
      lowerCDFMass_pos_of_gt_left_open_support μ hcdf_strict
        hsupport_nonempty hy.1
  · exact
      lowerCDFMass_lt_one_of_lt_right_open_support μ hcdf_strict
        hsupport_nonempty hy.2

/--
PG23 Corollary 4's strict cutoff comparison from the literal iid matching
formulas and the two market-clearing equalities.  The positive interval is the
printed `(P_poly - X_+, P_poly - X_-)` region; its source derivation remains a
separate visible premise rather than a conclusion-bearing source-model record.
-/
theorem corollary4_mono_cutoff_lt_poly_cutoff_of_iid_clearings
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {m : ℕ} (hm : 0 < m) (topFirm : Fin (m + 1))
    {Pmono Ppoly supply xMin xMax : ℝ}
    (hmono_clear :
      (∫ v : ℝ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => Pmono) topFirm ∂η) = supply)
    (hpoly_clear :
      (∫ v : ℝ,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ : Fin (m + 1) => Ppoly) ∂η) = supply)
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hinterval_positive :
      0 < η.real (Set.Ioo (Ppoly - xMax) (Ppoly - xMin))) :
    Pmono < Ppoly := by
  let monoDemand : ℝ → ℝ := fun P =>
    ∫ v : ℝ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
        v (fun _ : Fin (m + 1) => P) topFirm ∂η
  let polyDemand : ℝ → ℝ := fun P =>
    ∫ v : ℝ,
      AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (m + 1))) v
        (fun _ : Fin (m + 1) => P) ∂η
  have hmono_antitone :
      ∀ a b : ℝ, a ≤ b → monoDemand b ≤ monoDemand a := by
    intro a b hab
    dsimp [monoDemand]
    exact
      MeasureTheory.integral_mono
        (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
          noiseLaw η b topFirm)
        (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
          noiseLaw η a topFirm)
        (fun v =>
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_mono_lowerCutoff
            (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
            (c := topFirm)
            (by simpa using hab))
  have hstrict_pos :
      0 < η {v |
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
            v (fun _ : Fin (m + 1) => Ppoly) topFirm <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (m + 1))) v
            (fun _ : Fin (m + 1) => Ppoly)} := by
    exact
      theorem2_polyculture_access_strict_measure_pos_of_iidProduct_support_region
        η noiseLaw hm topFirm
        (polyCutoff := fun _ : ℕ => Ppoly)
        (region := Set.Ioo (Ppoly - xMax) (Ppoly - xMin))
        hinterval_positive
        (fun v hv =>
          lowerCDFMass_mem_Ioo_zero_one_of_mem_open_support noiseLaw
            hnoise_cdf_strict (by
              constructor <;> linarith [hv.1, hv.2]))
  have hstrict_at_poly : monoDemand Ppoly < polyDemand Ppoly := by
    apply corollary4_strict_demand_gap_of_pointwise_access η
    · exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_integrable
          noiseLaw η Ppoly topFirm
    · exact
        AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw)) η
          (Finset.univ : Finset (Fin (m + 1)))
          (fun _ : Fin (m + 1) => Ppoly)
    · rfl
    · rfl
    · intro v
      exact
        AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) (by simp)
          v (fun _ : Fin (m + 1) => Ppoly)
    · exact hstrict_pos
  exact
    corollary4_mono_cutoff_lt_poly_cutoff_of_same_supply
      (by simpa [monoDemand] using hmono_clear)
      (by simpa [polyDemand] using hpoly_clear)
      hmono_antitone hstrict_at_poly

/--
Finite-real-endpoint specialization of the Corollary 4 iid clearing proof.
Here the exact positive `P_poly` interval is derived from the polyculture
clearing equation and interior supply, rather than passed separately.  The
unrestricted source permits infinite support endpoints, so this remains a
proof-level specialization rather than the paper-facing source statement.
-/
theorem corollary4_mono_cutoff_lt_poly_cutoff_of_iid_clearings_finite_support
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {m : ℕ} (hm : 0 < m) (topFirm : Fin (m + 1))
    {Pmono Ppoly supply vMin vMax xMin xMax : ℝ}
    (hmono_clear :
      (∫ v : ℝ,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => Pmono) topFirm ∂η) = supply)
    (hpoly_clear :
      (∫ v : ℝ,
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (m + 1))) v
          (fun _ : Fin (m + 1) => Ppoly) ∂η) = supply)
    (hvalue_support : ∀ᵐ v ∂η, v ∈ Set.Icc vMin vMax)
    (hsupply_pos : 0 < supply)
    (hsupply_lt_one : supply < 1)
    (hvalue_nonempty : vMin < vMax)
    (hnoise_nonempty : xMin < xMax)
    (hvalue_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass η) (Set.Ioo vMin vMax))
    (hnoise_cdf_strict :
      StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass noiseLaw)
        (Set.Ioo xMin xMax))
    (hnoise_left : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMin = 0)
    (hnoise_right : AppliedModelingLib.Probability.lowerCDFMass noiseLaw xMax = 1) :
    Pmono < Ppoly := by
  have hpoly_bounds :
      vMin + xMin < Ppoly ∧ Ppoly < vMax + xMax :=
    cutoff_crossing_clearing_cutoff_sum_bounds_of_support
      η noiseLaw hvalue_support hsupply_pos hsupply_lt_one hpoly_clear
      hnoise_left hnoise_right
  exact
    corollary4_mono_cutoff_lt_poly_cutoff_of_iid_clearings
      η noiseLaw hm topFirm hmono_clear hpoly_clear hnoise_cdf_strict
      (theorem2_source_interval_positive_measure_of_sum_bounds
        η hvalue_nonempty hnoise_nonempty hpoly_bounds.1 hpoly_bounds.2
        hvalue_cdf_strict)

/--
The high-value half of PG23 Theorem 1 for the actual all-college iid matching
probability.  This projects the pointwise source conclusion directly from
maximum concentration, the value-supply threshold, local value mass, and the
literal polyculture clearing integrals; it does not expose the broader
Theorem 1 conclusion package at the theorem boundary.
-/
theorem theorem1_high_value_match_tendsto_one_of_iid_maximum_concentration
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {polyCutoff : ℕ → ℝ} {vS supply : ℝ}
    (hconc :
      maximumOrderStatisticConcentratingAroundExpected
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (htail_eq_capacity : AppliedModelingLib.Probability.upperTailMass η vS = supply)
    (hmass_left :
      ∀ ε : ℝ, 0 < ε → 0 < η (Set.Ioc (vS - ε) vS))
    (hmass_right :
      ∀ ε : ℝ, 0 < ε → 0 < η (Set.Ioc vS (vS + ε)))
    (hclear :
      ∀ n : ℕ,
        (∫ v : ℝ,
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ : Fin (n + 1) => polyCutoff n) ∂η) = supply) :
    ∀ v : ℝ, vS < v →
      Tendsto
        (fun n : ℕ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ : Fin (n + 1) => polyCutoff n))
        atTop (nhds 1) := by
  have hprob :
      ∀ n : ℕ,
        IsProbabilityMeasure
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) := by
    intro n
    infer_instance
  let hsupply : AppliedModelingLib.Probability.UpperTailThresholdCertificate η supply vS :=
    ⟨htail_eq_capacity⟩
  let hmass : AppliedModelingLib.Probability.TwoSidedPositiveIntervalMass η vS :=
    ⟨hmass_left, hmass_right⟩
  have hwisdom :
      theorem1_wisdomProbabilityConclusion
        (fun n : ℕ => fun v : ℝ =>
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ : Fin (n + 1) => polyCutoff n))
        (fun _ _ => (0 : ℝ)) vS :=
    theorem1_wisdomProbability_of_expected_max_shared_cutoff_marketClearing_supply_cutoff
      η hprob hconc hsupply hmass hclear (by
        intro v m n
        rfl)
  intro v hv
  exact hwisdom.2.1 v hv

end PG23MonocultureMatching

import GN21DriverSurgePricing.DomainBridge
import GN21DriverSurgePricing.CTMCVerification
import GN21DriverSurgePricing.Theorem3LowBranch
import GN21DriverSurgePricing.Theorem3Frontier
import GN21DriverSurgePricing.CutoffAttainment
import GN21DriverSurgePricing.Lemma5Variational
import GN21DriverSurgePricing.Lemma5Frontier
import GN21DriverSurgePricing.ZeroDensityBridge
import GN21DriverSurgePricing.Theorem4FixedMarginal
import GN21DriverSurgePricing.Theorem4LiteralEndpointCases
import GN21DriverSurgePricing.Theorem2ContinuousInstance
import GN21DriverSurgePricing.RawCalendarCycleConstruction

/-!
# Paper Interface: Driver Surge Pricing

This is the compact human-review surface for the GN21 driver surge-pricing
formalization.  It mirrors the source-paper definitions and named results in
DAG order.  The larger compatibility alias layer lives in `InterfaceAliases.lean`;
the source-numbered importable audit ledger lives in `PostPaperAudit.lean`.
-/

namespace GN21DriverSurgePricing
namespace ProofBridge

open MeasureTheory
open scoped ENNReal

universe u_1

/-- A source-model payout function. Payments on positive-length trips are
nonnegative, while the underlying real-valued function remains available to
the reward definitions. -/
structure GN21PayoutFunction where
  toPricingFunction : PricingFunction
  nonnegative_on_trip : ∀ tau : TripLength, 0 < tau → 0 ≤ toPricingFunction tau

/-- Appendix D's source convention that policy equalities are read modulo the
trip-length law.  It is stated here directly so the proof bridge does not
depend on the legacy alias layer. -/
abbrev policyEqualitiesModuloNullSets
    (mu : Measure TripLength) (Rhat : SingleStateReward) : Prop :=
  ∀ {left right : TripPolicy},
    policyAlmostEverywhereEq mu left right → Rhat left = Rhat right

/-! ## Section 2 model definitions -/

/--
Definition: single-state incentive compatibility.  Accepting all feasible trips
is optimal: every measurable feasible one-state trip policy earns no more than
accept-all.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 269--275.
-/
def review_definition_single_state_ic (R : SingleStateReward) : Prop :=
  ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ → R σ ≤ R acceptAllPolicy

/--
Definition: two-state dynamic incentive compatibility.  Accepting all feasible
trips in both CTMC states is optimal against dynamic policy deviations.

The source restricts every dynamic policy to an open subset of the positive
trip-length domain; openness supplies the required Borel measurability in the
Lean model.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 269--275.
-/
def review_definition_dynamic_ic (R : DynamicReward) : Prop :=
  dynamicFeasibleOpenPolicy acceptAllDynamicPolicy ∧
    ∀ σ : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy σ →
        R σ ≤ R acceptAllDynamicPolicy

/--
Definition: surge state. State 2 is the surge state when some feasible open
state-2 policy earns a strictly higher state reward rate than every feasible
open state-1 policy.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 377--381.
-/
def review_definition_surge_state
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (w : Fin 2 → PricingFunction) : Prop :=
  gn21SourceSurgeStateDominance mu arrival w

/--
Definition: threshold policies.  A trip policy accepts exactly the positive
trip lengths whose payment-per-time `w τ / τ` is at least the cutoff `c`.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 2149--2152.
-/
def review_definition_threshold_policy (w : PricingFunction) (c : ℝ) (sigma : TripPolicy) :
    Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ sigma ↔ c ≤ w τ / τ)

/--
Definition: dynamic reward with positive-mass denominators.  The Appendix D
reward formulas are formalized as a reward value defined on feasible dynamic
policies where the accepted-trip mass denominators are positive.

Source status: source-domain formalization
Source note: Paper source map uses `source.txt` lines 308--319; this row makes the paper's implicit positive-denominator domain explicit.
-/
def review_definition_dynamic_defined_reward (mu : Fin 2 → MeasureTheory.Measure TripLength) :
    Type :=
  (σ : Fin 2 → TripPolicy) →
    ((∀ i : Fin 2, σ i ⊆ acceptAllPolicy ∧ MeasurableSet (σ i)) ∧
      ∀ i : Fin 2, 0 < singleStateTripMass (mu i) (σ i)) →
      ℝ

/--
Section 2.2: IID renewal-reward bridge for the single-state result.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 279--292.
-/
theorem review_section2_single_state_renewal_reward_iid_bridge {Ω : Type u_1}
  [MeasurableSpace Ω] {PΩ : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure TripLength} {arrivalRate : ℝ}
  {w : PricingFunction} {σ : TripPolicy} (C : SingleStateRenewalIIDCycleModel PΩ μ arrivalRate w σ) :
  ∀ᵐ (ω : Ω) ∂PΩ,
    Filter.Tendsto (fun n => (∑ k ∈ Finset.range n, C.cyclePayment k ω) / ∑ k ∈ Finset.range n, C.cycleTime k ω)
      Filter.atTop (nhds (singleStateRenewalReward μ arrivalRate w σ)) := by
  apply paper_section2_single_state_renewal_reward_iid_stochastic_bridge

/-! ## Single-state results -/

/--
Proposition 3.1: affine single-state pricing is incentive compatible.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` line 499.
-/
theorem review_proposition3_1_affine_single_state_ic (mu : MeasureTheory.Measure TripLength)
  (arrivalRate m a : ℝ)
  (haccept_mass : singleStateTripMass mu acceptAllPolicy = 1)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy mu)
  (hlambda : 0 < arrivalRate) (ha_nonneg : 0 ≤ a)
  (ha_le_wait_value : a ≤ m / arrivalRate) :
  singleStateMeasurableIncentiveCompatible (affineSingleStateRenewalReward mu arrivalRate m a) := by
  exact paper_proposition3_1_affine_single_state_measurable_ic_of_standard_measure
    mu arrivalRate m a haccept_mass
    (singleStateTripMass_ne_top_of_eq_one haccept_mass)
    htime_integrable_acceptAll hlambda ha_nonneg ha_le_wait_value

/--
Theorem 1: optimal single-state policies are threshold policies.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 455--459.  The
zero-positive-payout case is discharged rather than assumed away.
-/
theorem review_theorem1_single_state_threshold_best_response
  (μ : MeasureTheory.Measure TripLength) (arrivalRate : ℝ) (w : GN21PayoutFunction)
  (hrate_measurable : Measurable fun τ => w.toPricingFunction τ / τ)
  (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
  (hw_integrable_acceptAll :
    MeasureTheory.IntegrableOn w.toPricingFunction acceptAllPolicy μ)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ => τ) acceptAllPolicy μ) (hlambda : 0 < arrivalRate) :
  ∃ c,
    0 ≤ c ∧ ∃ σ,
      thresholdRatePolicy w.toPricingFunction c σ ∧
        singleStateMeasurableOptimal
          (singleStateRenewalReward μ arrivalRate w.toPricingFunction) σ := by
  have hrate_nonneg : ∀ tau : TripLength, 0 < tau →
      0 ≤ w.toPricingFunction tau / tau := by
    intro tau htau
    exact div_nonneg (w.nonnegative_on_trip tau htau) (le_of_lt htau)
  exact
    paper_theorem1_single_state_threshold_best_response_measurable_of_nonnegative_rate
      μ arrivalRate w.toPricingFunction hrate_measurable hrate_nonneg hfinite_acceptAll
      hw_integrable_acceptAll htime_integrable_acceptAll hlambda

/--
Lemma 4: threshold optimizer uniqueness up to null sets.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2375--2379.  The
zero-positive-payout case is discharged rather than assumed away.
-/
theorem review_lemma4_single_state_threshold_uniqueness (μ : MeasureTheory.Measure TripLength)
  (arrivalRate : ℝ) (w : PricingFunction) (hrate_measurable : Measurable fun τ => w τ / τ)
  (hrate_nonneg : ∀ (τ : TripLength), 0 < τ → 0 ≤ w τ / τ) (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
  (hw_integrable_acceptAll : MeasureTheory.IntegrableOn w acceptAllPolicy μ)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ => τ) acceptAllPolicy μ) (hlambda : 0 < arrivalRate) :
  ∃ cstar,
    0 ≤ cstar ∧
      ∃ σstar,
        thresholdRatePolicy w cstar σstar ∧
          singleStateRenewalReward μ arrivalRate w σstar = cstar ∧
            singleStateMeasurableOptimal (singleStateRenewalReward μ arrivalRate w) σstar ∧
              ∀ ρ ⊆ acceptAllPolicy,
                MeasurableSet ρ →
                  singleStateMeasurableOptimal (singleStateRenewalReward μ arrivalRate w) ρ →
                    singleStateTripMass μ (strictThresholdPolicy w cstar \ ρ) = 0 ∧
                      singleStateTripMass μ (ρ \ completeThresholdPolicy w cstar) = 0 := by
  exact
    paper_lemma4_single_state_threshold_mass_zero_uniqueness_measurable_of_nonnegative_rate
      μ arrivalRate w hrate_measurable hrate_nonneg hfinite_acceptAll
      hw_integrable_acceptAll htime_integrable_acceptAll hlambda

/-! ## CTMC reward and probability lemmas -/

/--
Lemma 1: dynamic reward decomposition, with the paper's probability-one
claim represented as an almost-sure renewal-cycle convergence statement.

Source status: source-facing theorem summary
Source note: `GN21DynamicIIDCycleModel` explicitly carries the renewal-cycle
construction and its IID/integrability facts. This row does not infer that
construction from bare CTMC primitives; the companion endpoint below proves
the same source result from the literal raw-calendar construction.
-/
theorem review_lemma1_measured_dynamic_reward_decomposition
    {Omega : Type u_1} [MeasurableSpace Omega]
    {POmega : Measure Omega}
    {muI muJ : Measure TripLength}
    {arrivalI arrivalJ switchIJ switchJI : ℝ}
    {wI wJ : PricingFunction} {sigmaI sigmaJ : TripPolicy}
    (C : GN21DynamicIIDCycleModel POmega muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ) :
    ∀ᵐ omega ∂POmega,
      Filter.Tendsto
        (fun n : ℕ =>
          ((∑ k ∈ Finset.range n, C.stateEarningI k omega) +
              (∑ k ∈ Finset.range n, C.stateEarningJ k omega)) /
            ((∑ k ∈ Finset.range n, C.stateTimeI k omega) +
              (∑ k ∈ Finset.range n, C.stateTimeJ k omega)))
        Filter.atTop
        (nhds
          (gn21MeasuredDynamicReward muI muJ arrivalI arrivalJ switchIJ
            switchJI wI wJ sigmaI sigmaJ)) := by
  exact paper_lemma1_stochastic_dynamic_reward_decomposition_of_iid_cycles C

/-- Lemma 1 from the literal source calendar.  The observations are successive
deterministic post-exit tails of one raw path, not independently resampled
cycle proposals.  The measurable-payment facts are technical observability
facts supplied by the paper's pricing regularity, not a new main-text
economic premise. -/
abbrev review_lemma1_measured_dynamic_reward_decomposition_of_actual_calendar :=
  @paper_lemma1_stochastic_dynamic_reward_decomposition_of_actual_calendar

/--
Lemma 2: CTMC switch-probability formula.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2470--2474.
-/
theorem review_lemma2_switch_probability_formula (lambdaIJ lambdaJI s : ℝ) :
  gn21SwitchProb lambdaIJ lambdaJI s = lambdaIJ / (lambdaIJ + lambdaJI) * (1 - Real.exp (-(lambdaIJ + lambdaJI) * s)) := by
  apply paper_lemma2_switch_probability_formula

/--
Lemma 3: state time-fraction formula, with the paper's renewal-cycle argument
represented as an almost-sure IID-cycle convergence statement.

Source status: source-facing theorem summary
Source note: `GN21TimeFractionIIDCycleModel` explicitly carries the renewal
cycle variables and their IID/integrability facts. This row does not infer
that construction from bare CTMC primitives; the companion endpoint below
proves the same source result from the literal raw-calendar construction.
-/
theorem review_lemma3_measured_time_fraction_formula
    {Omega : Type u_1} [MeasurableSpace Omega]
    {POmega : Measure Omega}
    {muI muJ : Measure TripLength}
    {arrivalI arrivalJ switchIJ switchJI : ℝ}
    {sigmaI sigmaJ : TripPolicy}
    (C : GN21TimeFractionIIDCycleModel POmega muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ) :
    ∀ᵐ omega ∂POmega,
      Filter.Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n, C.stateTimeI k omega) /
            ((∑ k ∈ Finset.range n, C.stateTimeI k omega) +
              (∑ k ∈ Finset.range n, C.stateTimeJ k omega)))
        Filter.atTop
        (nhds
          (gn21MeasuredTimeFraction muI muJ arrivalI arrivalJ switchIJ
            switchJI sigmaI sigmaJ)) := by
  exact paper_lemma3_stochastic_time_fraction_formula_of_iid_cycles C

/-- Lemma 3 from the literal source calendar.  Every time summand is read
from one raw seed path through deterministic post-exit tails, thereby
discharging the renewal construction used in the source argument. -/
abbrev review_lemma3_measured_time_fraction_formula_of_actual_calendar :=
  @paper_lemma3_stochastic_time_fraction_formula_of_actual_calendar

/--
Remark 1: switch probability per unit time is strictly decreasing.

Source status: source-facing theorem summary
Source note: `source.txt:3747-3768`.
-/
theorem review_remark1_switch_probability_per_time_strictAntiOn (lambdaIJ lambdaJI : ℝ)
  (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) :
  StrictAntiOn (fun u => gn21SwitchProb lambdaIJ lambdaJI u / u) (Set.Ioi 0) := by
  apply paper_remark1_switch_probability_per_time_strictAntiOn <;> assumption

/--
Remark 1: for a fixed policy summary, the displayed Lemma 6 response is
continuous in positive trip length whenever the source price is continuous
there.  This is a continuity statement about the explicit response formula;
the model does not give `TripPolicy` a topology, so it does not purport to be
a policy-space continuity claim.

Source status: direct source conditional.
Source note: `source.txt:3747-3753`.
-/
theorem review_remark1_response_continuousOn_positive_trip_lengths_of_continuous_price
    (w : PricingFunction)
    (Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hw : ContinuousOn w (Set.Ioi 0)) :
    ContinuousOn
      (fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (w u)
          Qi Qj Ti Tj Ri Rj)
      (Set.Ioi 0) := by
  have hq :
      ContinuousOn (fun u : TripLength => gn21SwitchProb lambdaIJ lambdaJI u)
        (Set.Ioi 0) :=
    (continuous_gn21SwitchProb lambdaIJ lambdaJI).continuousOn
  have hid : ContinuousOn (fun u : TripLength => u) (Set.Ioi 0) :=
    continuous_id.continuousOn
  have hu_ne : ∀ u ∈ Set.Ioi (0 : ℝ), u ≠ 0 := by
    intro u hu
    exact ne_of_gt hu
  unfold gn21Lemma6Response
  exact
    (((hq.div hid hu_ne).mul continuousOn_const).add
        ((hw.div hid hu_ne).mul continuousOn_const)).sub continuousOn_const

/--
Remark 1 surge-state response direction.  A negative `Delta_{j,i}=R_j-R_i`,
strictly decreasing CTMC switch probability per time, and nondecreasing
payment per time make the displayed response strictly increasing.

Source status: direct source conditional.
Source note: `source.txt:3758-3763`.
-/
theorem review_remark1_response_strictMonoOn_of_surge_gap_negative_and_per_time_mono
    (w : PricingFunction)
    (Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hQi_pos : 0 < Qi) (hQj_pos : 0 < Qj)
    (hTi_pos : 0 < Ti) (hTj_pos : 0 < Tj)
    (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI)
    (hdelta_ji_neg : Rj - Ri < 0)
    (hpayment_per_time_mono :
      MonotoneOn (fun u : TripLength => w u / u) (Set.Ioi 0)) :
    StrictMonoOn
      (fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (w u)
          Qi Qj Ti Tj Ri Rj)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hq_anti :=
    paper_remark1_switch_probability_per_time_strictAntiOn
      lambdaIJ lambdaJI hlambdaIJ hsum
  have hqxy :
      gn21SwitchProb lambdaIJ lambdaJI y / y <
        gn21SwitchProb lambdaIJ lambdaJI x / x :=
    hq_anti hx hy hxy
  have hstate_weight_pos : 0 < Qi / Ti + Qj / Tj :=
    add_pos (div_pos hQi_pos hTi_pos) (div_pos hQj_pos hTj_pos)
  have hwxy : w x / x ≤ w y / y :=
    hpayment_per_time_mono hx hy (le_of_lt hxy)
  have hq_term :
      (gn21SwitchProb lambdaIJ lambdaJI x / x) * (Rj - Ri) <
        (gn21SwitchProb lambdaIJ lambdaJI y / y) * (Rj - Ri) := by
    exact mul_lt_mul_of_neg_right hqxy hdelta_ji_neg
  have hw_term :
      (w x / x) * (Qi / Ti + Qj / Tj) ≤
        (w y / y) * (Qi / Ti + Qj / Tj) := by
    exact mul_le_mul_of_nonneg_right hwxy (le_of_lt hstate_weight_pos)
  unfold gn21Lemma6Response
  nlinarith

/--
Remark 1 non-surge-state response direction.  A positive
`Delta_{j,i}=R_j-R_i`, strictly decreasing CTMC switch probability per time,
and nonincreasing payment per time make the displayed response strictly
decreasing.

Source status: direct source conditional.
Source note: `source.txt:3764-3768`.
-/
theorem review_remark1_response_strictAntiOn_of_nonsurge_gap_positive_and_per_time_anti
    (w : PricingFunction)
    (Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hQi_pos : 0 < Qi) (hQj_pos : 0 < Qj)
    (hTi_pos : 0 < Ti) (hTj_pos : 0 < Tj)
    (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI)
    (hdelta_ji_pos : 0 < Rj - Ri)
    (hpayment_per_time_anti :
      AntitoneOn (fun u : TripLength => w u / u) (Set.Ioi 0)) :
    StrictAntiOn
      (fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (w u)
          Qi Qj Ti Tj Ri Rj)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hq_anti :=
    paper_remark1_switch_probability_per_time_strictAntiOn
      lambdaIJ lambdaJI hlambdaIJ hsum
  have hqxy :
      gn21SwitchProb lambdaIJ lambdaJI y / y <
        gn21SwitchProb lambdaIJ lambdaJI x / x :=
    hq_anti hx hy hxy
  have hstate_weight_pos : 0 < Qi / Ti + Qj / Tj :=
    add_pos (div_pos hQi_pos hTi_pos) (div_pos hQj_pos hTj_pos)
  have hwxy : w y / y ≤ w x / x :=
    hpayment_per_time_anti hx hy (le_of_lt hxy)
  have hq_term :
      (gn21SwitchProb lambdaIJ lambdaJI y / y) * (Rj - Ri) <
        (gn21SwitchProb lambdaIJ lambdaJI x / x) * (Rj - Ri) := by
    exact mul_lt_mul_of_pos_right hqxy hdelta_ji_pos
  have hw_term :
      (w y / y) * (Qi / Ti + Qj / Tj) ≤
        (w x / x) * (Qi / Ti + Qj / Tj) := by
    exact mul_le_mul_of_nonneg_right hwxy (le_of_lt hstate_weight_pos)
  unfold gn21Lemma6Response
  nlinarith

/--
Remark 2: structured-price scaled earning algebra
`W_i = m(T_i-1)+z(Q_i-lambda_{i,j})`.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3017--3036.
-/
theorem review_remark2_structured_scaled_earning_algebra
    (μ : Measure TripLength) (arrivalRate m z switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable : IntegrableOn (fun τ : TripLength => τ) σ μ) :
    gn21ScaledStateEarning μ arrivalRate
        (ctmcStructuredSurgePrice m z switchIJ switchJI) σ =
      m * (gn21ScaledStateTime μ arrivalRate σ - 1) +
        z * (gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ - switchIJ) := by
  have hq_integrable :
      IntegrableOn (fun τ : TripLength =>
        gn21SwitchProb switchIJ switchJI τ) σ μ :=
    have hswitch_nonneg : 0 ≤ switchIJ := le_of_lt hswitchIJ_pos
    have hswitch_sum_pos : 0 < switchIJ + switchJI := by
      linarith [hswitchIJ_pos, hswitchJI_pos]
    integrableOn_gn21SwitchProb_of_time_integrable μ switchIJ switchJI σ
      hswitch_nonneg hswitch_sum_pos hσ_subset hσ_measurable htime_integrable
  exact paper_remark2_structured_scaled_earning_algebra μ arrivalRate m z
    switchIJ switchJI σ htime_integrable hq_integrable

/--
Remark 2: substituting the structured price and scaled earning formulas into
the endpoint derivative kernel gives the displayed structured derivative
expression.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3017--3036.
-/
theorem review_remark2_structured_derivative_kernel_algebra (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ) :
  gn21DerivativeSignKernel q u (m * u + z * q) Qi Qj Ti Tj (m * (Ti - 1) + z * (Qi - switchIJ)) (Rj * Tj) =
    gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj := by
  apply paper_remark2_structured_derivative_kernel_algebra

/--
Remark 3: small-time switch probability per unit time tends to the switch rate.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` line 3089.
-/
theorem review_remark3_switch_probability_per_time_tendsto_at_zero (lambdaIJ lambdaJI : ℝ)
  (hsum : lambdaIJ + lambdaJI ≠ 0) :
  Filter.Tendsto (fun u => gn21SwitchProb lambdaIJ lambdaJI u / u) (nhdsWithin 0 {0}ᶜ) (nhds lambdaIJ) := by
  apply paper_remark3_switch_probability_per_time_tendsto_at_zero
  assumption

/--
Remark 4: `lambda * t - q(t)` is nonnegative.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3091--3092.
-/
theorem review_remark4_switch_time_minus_switch_probability_nonneg (lambdaIJ lambdaJI τ : ℝ)
  (hlambdaIJ : 0 ≤ lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (_hτ : 0 ≤ τ) :
  0 ≤ lambdaIJ * τ - gn21SwitchProb lambdaIJ lambdaJI τ := by
  apply paper_remark4_switch_time_minus_switch_probability_nonneg <;> assumption

/--
Remark 4: for every feasible accepted-trip set, both `lambda*T - Q` and `Q`
are nonnegative and no larger than their values at the accept-all policy.

This is the full aggregate statement in the source, rather than only its
pointwise integrand inequality.  The integrability assumptions make the
source's distributional integrals explicit.

Source status: direct source-facing theorem summary.
Source note: `source.txt:3799-3800` and proof `source.txt:4538-4570`.
-/
theorem review_remark4_ctmc_aggregate_nonnegative_and_maximized_acceptAll
    (mu : MeasureTheory.Measure TripLength)
    (arrivalRate switchIJ switchJI : ℝ) (sigma : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_nonneg : 0 ≤ switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (htime_integrable :
      IntegrableOn (fun tau : TripLength => tau) sigma mu)
    (hq_integrable :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        sigma mu)
    (htime_acceptAll_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy mu)
    (hq_acceptAll_integrable :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        acceptAllPolicy mu) :
    0 ≤ switchIJ * gn21ScaledStateTime mu arrivalRate sigma -
        gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma ∧
      switchIJ * gn21ScaledStateTime mu arrivalRate sigma -
          gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma ≤
        switchIJ * gn21ScaledStateTime mu arrivalRate acceptAllPolicy -
          gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI
            acceptAllPolicy ∧
      0 ≤ gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma ∧
      gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma ≤
        gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI
          acceptAllPolicy := by
  constructor
  · rw [paper_remark4_scaled_time_minus_exit_weight_eq_integral
      mu arrivalRate switchIJ switchJI sigma htime_integrable hq_integrable]
    exact paper_remark4_scaled_time_minus_exit_weight_nonneg
      mu arrivalRate switchIJ switchJI sigma harrival_nonneg hswitch_nonneg
      hsum hsigma_measurable hsigma_subset
  constructor
  · exact paper_remark4_scaled_time_minus_exit_weight_measured_le_acceptAll
      mu arrivalRate switchIJ switchJI sigma harrival_nonneg hswitch_nonneg
      hsum htime_integrable hq_integrable htime_acceptAll_integrable
      hq_acceptAll_integrable hsigma_subset
  constructor
  · have hswitch_le : switchIJ ≤
        gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma :=
      gn21ExitWeightIntegral_ge_switch_of_nonneg
        mu arrivalRate switchIJ switchJI sigma harrival_nonneg hswitch_nonneg
        hsum hsigma_measurable hsigma_subset
    linarith
  · exact paper_remark4_exit_weight_integral_le_acceptAll
      mu arrivalRate switchIJ switchJI sigma harrival_nonneg hswitch_nonneg
      hsum hq_acceptAll_integrable hsigma_subset

/-! ## Lemma 5--10 response-shape chain -/

/--
Auxiliary policy-form component from explicit positive-response shape data.

This is not the printed Lemma 5: it assumes the zero-crossing and side-sign
facts that the source variational argument derives from its continuity and
derivative hypotheses.  It is retained only as a component for the active
source-exact Lemma 5 proof obligation.
-/
theorem lemma5_policy_form_of_explicit_positive_response_shape (mu : MeasureTheory.Measure TripLength)
  [MeasureTheory.NoAtoms mu] (response : TripLength → ℝ) {shape : Lemma5DerivativeShape} (sigma : TripPolicy)
  (D : Lemma5PositiveResponseShapeData response shape) (hresponse_measurable : Measurable response)
  (hresponse_integrable_acceptAll : MeasureTheory.IntegrableOn response acceptAllPolicy mu)
  (hsigma_measurable : MeasurableSet sigma) (hsigma_subset : sigma ⊆ acceptAllPolicy)
  (hoptimal :
    ∀ sigma' ⊆ acceptAllPolicy,
      MeasurableSet sigma' → lemma5MarginalSetReward mu response sigma' ≤ lemma5MarginalSetReward mu response sigma) :
  lemma5PolicyFormAlmostEverywhere mu shape sigma := by
  apply paper_lemma5_fixed_response_policy_form_ae_of_response_shape <;> assumption

/--
Appendix D's explicit convention that policy equality is modulo the trip-length
law makes an endpoint traversal through a null interval reward-invariant.  This
is the source-model bridge used to interpret the ``except where f(u)=0''
derivative-sign notation; it does not assert an optimizer or a policy form.

Source status: direct source-model convention at `source.txt:3660-3692`.
-/
theorem review_lemma5_null_interval_reward_invariance
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward) (context : TripPolicy)
    {lower left right : TripLength}
    (hleft_right : left ≤ right)
    (hnull : mu (Set.Ioo left right) = 0)
    (hpolicy_ae : policyEqualitiesModuloNullSets mu Rhat) :
    Rhat (context ∪ Set.Ioo lower left) =
      Rhat (context ∪ Set.Ioo lower right) := by
  exact hpolicy_ae
    (policyAlmostEverywhereEq_union_interval_expand_of_null
      mu context hleft_right hnull)

/--
The endpoint-calculus realization consumed by the existing finite-variation
engine for Lemma 5.  It is deliberately a transparent collection of local
calculus facts: it supplies no optimizer, policy-form, or conclusion.

For the source model, these are the authorized finite-endpoint implementation
regularity behind the printed ``same sign except where `f(u) = 0`'' convention.
The component paths are tied to the current policy's connected components;
they do not assert derivative facts for an arbitrary background union.  The
a.e. policy-equality convention does not derive any of these raw sign facts at
a zero-density endpoint.  They must be reviewed by their expanded mathematical
content, not by this structure's name.
-/
structure GN21Lemma5EndpointSignRealization
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (shape : Lemma5DerivativeShape)
    (sigma : TripPolicy)
    (margin : ℝ) where
  upper_derivative :
    ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
      (i : Fin extra) {value : ℝ},
      endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
        ∃ derivativeValue : ℝ,
          HasDerivAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21Lemma5GapUpperIndex i) x)))
            derivativeValue value ∧
          sameStrictSign derivativeValue
            (response (gn21EndpointVectorPolicy endpoints) value)
  lower_derivative :
    ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
      (slot : Fin (extra + 1)) {value : ℝ},
      endpoints (gn21LowerEndpointIndex slot) = ENNReal.ofReal value →
        ∃ derivativeValue : ℝ,
          HasDerivAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21LowerEndpointIndex slot) x)))
            derivativeValue value ∧
          sameStrictSign derivativeValue
            (-response (gn21EndpointVectorPolicy endpoints) value)
  upper_right_derivative :
    ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
      (i : Fin extra),
      endpoints (gn21Lemma5GapUpperIndex i) = 0 →
        ∃ derivativeValue : ℝ,
          HasDerivWithinAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue (Set.Ici 0) 0 ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) 0)
  lower_right_derivative :
    ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
      (slot : Fin (extra + 1)),
      endpoints (gn21LowerEndpointIndex slot) = 0 →
        ∃ derivativeValue : ℝ,
          HasDerivWithinAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue (Set.Ici 0) 0 ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) 0)
  positive_path_continuous :
    ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
      endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
        ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
          ContinuousOn
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21Lemma5GapUpperIndex i) x)))
            (Set.Icc 0 upper)
  positive_path_derivative :
    ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
      (i : Fin extra) (upper : ℝ) (x : ℝ),
      x ∈ Set.Ioo 0 upper →
        ∃ derivativeValue : ℝ,
          HasDerivAt
            (fun y =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21Lemma5GapUpperIndex i) y)))
            derivativeValue x ∧
          sameStrictSign derivativeValue
            (response
              (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21Lemma5GapUpperIndex i) x)) x)
  right_top_witness :
    shape = .strictlyQuasiConvex →
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
        Rhat sigma - margin ≤
            Rhat (gn21EndpointVectorPolicy endpoints) →
          ∀ (j : Fin extra),
            endpoints (gn21Lemma5GapLowerIndex j) = ∞ →
              ∃ rightValue : ℝ,
                endpoints (gn21Lemma5GapUpperIndex j) <
                    ENNReal.ofReal rightValue ∧
                  response
                    (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0
  component_upper_derivative :
    GN21Lemma5ComponentUpperDerivativeCondition Rhat response
  component_lower_derivative :
    GN21Lemma5ComponentLowerDerivativeCondition Rhat response
  component_lower_right_derivative :
    GN21Lemma5ComponentLowerRightDerivativeCondition Rhat response
  component_tail_lower_derivative :
    GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response
  open_split_lower_derivative :
    ∀ (policy : TripPolicy) (pivot : ℝ),
      IsOpen policy → policy ⊆ acceptAllPolicy →
        pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)

/--
The approved source-model route for Lemma 5's zero-density endpoints.

Appendix D identifies policies up to the trip-length law and explicitly reads
the derivative-sign notation only away from `f(u) = 0`
(`source.txt:3660-3692`).  Lemma 6 then exposes the density factor in the
endpoint derivative calculation (`source.txt:4110-4148`).  This data makes
both parts visible: zero-density interval changes are quotient-invariant, and
the finite-variation implementation receives its explicit endpoint-calculus
realization.  It is not a full-support assumption.
-/
structure GN21Lemma5AENullEndpointVariation
    (mu : Measure TripLength)
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (shape : Lemma5DerivativeShape)
    (sigma : TripPolicy)
    (margin : ℝ) where
  densityNN : TripLength → NNReal
  measure_eq_withDensity :
    mu = volume.withDensity (fun tau => (densityNN tau : ENNReal))
  density_measurable : Measurable densityNN
  policy_equalities_modulo_null_sets :
    policyEqualitiesModuloNullSets mu Rhat
  endpoint_sign_realization :
    GN21Lemma5EndpointSignRealization Rhat response shape sigma margin

/--
The source-model zero-density route proves the endpoint traversal equality
actually used to interpret Lemma 5 modulo the trip-length law.
-/
theorem GN21Lemma5AENullEndpointVariation.zero_density_interval_reward_eq
    {mu : Measure TripLength}
    [NoAtoms mu]
    {Rhat : SingleStateReward}
    {response : TripPolicy → TripLength → ℝ}
    {shape : Lemma5DerivativeShape}
    {sigma : TripPolicy}
    {margin : ℝ}
    (H : GN21Lemma5AENullEndpointVariation
      mu Rhat response shape sigma margin)
    (context : TripPolicy) {lower left right : TripLength}
    (hleft_right : left ≤ right)
    (hzero : ∀ tau, tau ∈ Set.Ioo left right → H.densityNN tau = 0) :
    Rhat (context ∪ Set.Ioo lower left) =
      Rhat (context ∪ Set.Ioo lower right) := by
  exact H.policy_equalities_modulo_null_sets
    (policyAlmostEverywhereEq_union_interval_expand_of_null
      mu context hleft_right
      (measure_Ioo_eq_zero_of_densityNN_eq_zero_on
        mu H.densityNN H.measure_eq_withDensity H.density_measurable hzero))

/--
Lemma 5's direct variational statement, including all five response-shape cases,
endpoint-complete policy forms, weak dominance, and strict improvement unless
the starting policy already has that form a.e.  The declaration writes endpoint
variation facts explicitly; null endpoint traversals are separately discharged
through the source's equality-modulo-null-sets convention.

Source status: direct source theorem under the Appendix-D a.e. policy convention.
-/
theorem lemma5_full_variational_policy_forms
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (shape : Lemma5DerivativeShape)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain shape extra))
    (hresponse_positive :
      shape = .positive →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ u : TripLength, 0 < u → 0 < response tau u)
    (hresponse_increasing :
      shape = .strictlyIncreasing →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            StrictMonoOn (response tau) (Set.Ici 0))
    (hresponse_decreasing :
      shape = .strictlyDecreasing →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            StrictAntiOn (response tau) (Set.Ici 0))
    (hresponse_quasiConvex :
      shape = .strictlyQuasiConvex →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            strictQuasiConvexOnPositive (response tau))
    (hzero_quasiConvex :
      shape = .strictlyQuasiConvex →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ {middleLower middleUpper right : ℝ},
              0 < middleLower → middleLower < middleUpper →
                middleUpper < right →
                  response tau middleLower <
                    max (response tau 0) (response tau right))
    (hresponse_quasiConcave :
      shape = .strictlyQuasiConcave →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            strictQuasiConcaveOnPositive (response tau))
    (hzero_quasiConcave :
      shape = .strictlyQuasiConcave →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ {middle right : ℝ}, 0 < middle → middle < right →
              min (response tau 0) (response tau right) <
                response tau middle)
    (H : GN21Lemma5AENullEndpointVariation
      mu Rhat response shape sigma margin) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm shape policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere mu shape sigma →
          Rhat sigma < Rhat policy) := by
  exact GN21DriverSurgePricing.paper_lemma5_source_policy_replacement_open
    (mu := mu) (Rhat := Rhat) (response := response) (shape := shape)
    (sigma := sigma) (margin := margin)
    hsigma_open hsigma_subset hempty_lt_sigma hmargin hcontinuous
    hendpoint_continuous hresponse_positive hresponse_increasing
    hresponse_decreasing hresponse_quasiConvex hzero_quasiConvex
    hresponse_quasiConcave hzero_quasiConcave
    H.endpoint_sign_realization.upper_derivative
    H.endpoint_sign_realization.lower_derivative
    H.endpoint_sign_realization.upper_right_derivative
    H.endpoint_sign_realization.lower_right_derivative
    H.endpoint_sign_realization.positive_path_continuous
    H.endpoint_sign_realization.positive_path_derivative
    H.endpoint_sign_realization.right_top_witness
    H.endpoint_sign_realization.component_upper_derivative
    H.endpoint_sign_realization.component_lower_derivative
    H.endpoint_sign_realization.component_lower_right_derivative
    H.endpoint_sign_realization.component_tail_lower_derivative
    H.endpoint_sign_realization.open_split_lower_derivative

/--
Lemma 6: upper-endpoint derivative formula.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3786--3808. This row
proves the exact endpoint derivative formula without assuming positive endpoint
density; positive density is only the conditional premise for the strict
sign-transfer corollary in the conclusion.
-/
theorem review_lemma6_upper_endpoint_derivative_formula
  (arrivalRate switchRate lowerEndpoint u Qj Tj Wj Ri Rj : ℝ) (density switchProb payment : ℝ → ℝ)
  (harrival_pos : 0 < arrivalRate) (hu : 0 < u) (hQj_pos : 0 < Qj)
  (hTi_pos : 0 < gn21EndpointTiPath arrivalRate lowerEndpoint density u) (hTj_pos : 0 < Tj)
  (hWi :
    gn21EndpointWiPath arrivalRate lowerEndpoint density payment u =
      Ri * gn21EndpointTiPath arrivalRate lowerEndpoint density u)
  (hWj : Wj = Rj * Tj)
  (hden :
    gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
        Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠
      0)
  (hq_int : IntervalIntegrable (fun τ => switchProb τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hq_meas : StronglyMeasurableAtFilter (fun τ => switchProb τ * density τ) (nhds u) MeasureTheory.volume)
  (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
  (hw_int : IntervalIntegrable (fun τ => payment τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hw_meas : StronglyMeasurableAtFilter (fun τ => payment τ * density τ) (nhds u) MeasureTheory.volume)
  (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
  (ht_int : IntervalIntegrable (fun τ => τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (ht_meas : StronglyMeasurableAtFilter (fun τ => τ * density τ) (nhds u) MeasureTheory.volume)
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u) :
  HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb x) Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density x) Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment x) Wj)
      (arrivalRate * density u * Qj *
          gn21DerivativeSignKernel (switchProb u) u (payment u)
            (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u) Qj
            (gn21EndpointTiPath arrivalRate lowerEndpoint density u) Tj
            (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u) Wj /
        (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
            Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u) ^
          2)
      u ∧
    (0 < density u →
      sameStrictSign
        (arrivalRate * density u * Qj *
            gn21DerivativeSignKernel (switchProb u) u (payment u)
              (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u) Qj
              (gn21EndpointTiPath arrivalRate lowerEndpoint density u) Tj
              (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u) Wj /
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
              Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u) ^
            2)
        (gn21Lemma6Response (switchProb u) u (payment u)
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u) Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u) Tj Ri Rj)) := by
  apply paper_lemma6_upper_endpoint_interval_density_response_formula_no_density_premise <;> assumption

/--
Lemma 7: positive-additive affine response is quasi-convex.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3072--3073.
-/
theorem review_lemma7_affine_positive_additive_response_quasi_convex
  (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ) (hm_pos : 0 < m) (ha_pos : 0 < a) (hdelta_ji_nonpos : Rj - Ri ≤ 0)
  (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj) (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (hTi : Ti ≠ 0)
  (hTj : Tj ≠ 0) :
  strictQuasiConvexOnPositive fun u =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a) Qi Qj Ti Tj Ri Rj := by
  apply paper_lemma7_affine_positive_additive_response_strict_quasi_convex <;> assumption

/--
Lemma 8: negative-additive affine response is quasi-concave.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3075--3076.
-/
theorem review_lemma8_affine_negative_additive_response_quasi_concave
  (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ) (hm_pos : 0 < m) (ha_neg : a < 0) (hdelta_ji_nonneg : 0 ≤ Rj - Ri)
  (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj) (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (hTi : Ti ≠ 0)
  (hTj : Tj ≠ 0) :
  strictQuasiConcaveOnPositive fun u =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a) Qi Qj Ti Tj Ri Rj := by
  apply paper_lemma8_affine_negative_additive_response_strict_quasi_concave <;> assumption

/--
Lemma 9: surge-state derivative positivity under accept-all bounds.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 704--708, 3809--3833,
and 4587--4588.
-/
theorem review_lemma9_surge_derivative_positive_of_acceptAll_bounds
  (arrivalRate lowerEndpoint u T1 Q1 T2 Q2 Tbar2 Qbar2 switch21 switch12 m R1 z ratio : ℝ) (density : ℝ → ℝ)
  (harrival_pos : 0 < arrivalRate) (hdensity_pos : 0 < density u) (hQ1_pos : 0 < Q1)
  (hden :
    gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠
      0)
  (hq_int :
    IntervalIntegrable (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hq_meas :
    StronglyMeasurableAtFilter (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (nhds u) MeasureTheory.volume)
  (hq_cont : ContinuousAt (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
  (hw_int :
    IntervalIntegrable (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ * density τ) MeasureTheory.volume
      lowerEndpoint u)
  (hw_meas :
    StronglyMeasurableAtFilter (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ * density τ) (nhds u)
      MeasureTheory.volume)
  (hw_cont : ContinuousAt (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ * density τ) u)
  (ht_int : IntervalIntegrable (fun τ => τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (ht_meas : StronglyMeasurableAtFilter (fun τ => τ * density τ) (nhds u) MeasureTheory.volume)
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
  (hQ2 : gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density (gn21SwitchProb switch21 switch12) u = Q2)
  (hT2 : gn21EndpointTiPath arrivalRate lowerEndpoint density u = T2)
  (hW2 :
    gn21EndpointWiPath arrivalRate lowerEndpoint density (ctmcStructuredSurgePrice m z switch21 switch12) u =
      m * (T2 - 1) + z * (Q2 - switch21))
  (hbounds_bar : lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21) (hz_nonneg : 0 ≤ z)
  (hz : z = ratio * (m - R1))
  (hmR_pos : 0 < m - R1) (hR1_nonneg : 0 ≤ R1) (hT1_nonneg : 0 ≤ T1) (hswitch21_pos : 0 < switch21)
  (hsum : 0 < switch21 + switch12) (hu : 0 < u) (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
  (hgap_le : switch21 * T2 - Q2 ≤ switch21 * Tbar2 - Qbar2) (hswitch_lt_Q2 : switch21 < Q2) (hQ2_le : Q2 ≤ Qbar2) :
  0 <
    (lemma6EndpointDerivativeData_of_interval_density_paths arrivalRate switch21 lowerEndpoint u Q1 T1 (R1 * T1) density
        (gn21SwitchProb switch21 switch12) (ctmcStructuredSurgePrice m z switch21 switch12) harrival_pos hdensity_pos
        hQ1_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont).derivativeValue := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switch21 lowerEndpoint u Q1 T1 (R1 * T1) density
      (gn21SwitchProb switch21 switch12)
      (ctmcStructuredSurgePrice m z switch21 switch12)
      harrival_pos hdensity_pos hQ1_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  have hbounds_current :
      lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21 :=
    lemma9StructuredBounds_of_acceptAll_tightening
      ratio T1 Q1 T2 Q2 Tbar2 Qbar2 switch21 hbounds_bar
      hT1_nonneg hQ1_pos hswitch21_pos hgap_nonneg hgap_le
      hswitch_lt_Q2 hQ2_le
  have hpos : 0 < D.derivativeValue :=
    paper_lemma9_derivative_value_pos_of_current_bounds_certificate
      (lemma6DerivativeFormulaCertificate_of_endpoint_data D)
      ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z
      (by rfl)
      (by rfl)
      (by rfl)
      (by simpa [D] using hQ2)
      (by rfl)
      (by simpa [D] using hT2)
      (by rfl)
      (by simpa [D] using hW2)
      (by rfl)
      hbounds_current hz hmR_pos hR1_nonneg hT1_nonneg hQ1_pos
      hswitch21_pos hsum hu hswitch_lt_Q2 hgap_nonneg
  simpa [D] using hpos

/--
Lemma 10: non-surge-state derivative positivity under accept-all bounds.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3828--3853 and
4729--4751.
-/
theorem review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds
  (arrivalRate lowerEndpoint u T2 Q2 T1 Q1 Tbar1 Qbar1 switch12 switch21 R2 z ratio : ℝ) (density : ℝ → ℝ)
  (harrival_pos : 0 < arrivalRate) (hdensity_pos : 0 < density u) (hQ2_pos : 0 < Q2)
  (hden :
    gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠
      0)
  (hq_int :
    IntervalIntegrable (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hq_meas :
    StronglyMeasurableAtFilter (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (nhds u) MeasureTheory.volume)
  (hq_cont : ContinuousAt (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
  (hw_int :
    IntervalIntegrable (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ * density τ) MeasureTheory.volume
      lowerEndpoint u)
  (hw_meas :
    StronglyMeasurableAtFilter (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ * density τ) (nhds u)
      MeasureTheory.volume)
  (hw_cont : ContinuousAt (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ * density τ) u)
  (ht_int : IntervalIntegrable (fun τ => τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (ht_meas : StronglyMeasurableAtFilter (fun τ => τ * density τ) (nhds u) MeasureTheory.volume)
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
  (hQ1 : gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density (gn21SwitchProb switch12 switch21) u = Q1)
  (hT1 : gn21EndpointTiPath arrivalRate lowerEndpoint density u = T1)
  (hW1 :
    gn21EndpointWiPath arrivalRate lowerEndpoint density (ctmcStructuredSurgePrice R2 z switch12 switch21) u =
      R2 * (T1 - 1) + z * (Q1 - switch12))
  (hbounds_bar : lemma10StructuredBounds ratio T2 Q2 Tbar1 Qbar1 switch12) (hz_nonpos : z ≤ 0)
  (hz : z = ratio * R2) (hR2_pos : 0 < R2)
  (hswitch12_pos : 0 < switch12) (hsum : 0 < switch12 + switch21) (hu : 0 < u) (hA_pos : 0 < T2 * switch12 + Q2)
  (hgap_nonneg : 0 ≤ switch12 * T1 - Q1) (hgap_le : switch12 * T1 - Q1 ≤ switch12 * Tbar1 - Qbar1)
  (hswitch_lt_Q1 : switch12 < Q1) (hQ1_le : Q1 ≤ Qbar1) :
  0 <
    (lemma6EndpointDerivativeData_of_interval_density_paths arrivalRate switch12 lowerEndpoint u Q2 T2 (R2 * T2) density
        (gn21SwitchProb switch12 switch21) (ctmcStructuredSurgePrice R2 z switch12 switch21) harrival_pos hdensity_pos
        hQ2_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont).derivativeValue := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switch12 lowerEndpoint u Q2 T2 (R2 * T2) density
      (gn21SwitchProb switch12 switch21)
      (ctmcStructuredSurgePrice R2 z switch12 switch21)
      harrival_pos hdensity_pos hQ2_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  have hbounds_current :
      lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12 :=
    lemma10StructuredBounds_of_acceptAll_tightening
      ratio T2 Q2 T1 Q1 Tbar1 Qbar1 switch12 hbounds_bar
      hA_pos (le_of_lt hQ2_pos) hswitch12_pos hgap_nonneg hgap_le
      hswitch_lt_Q1 hQ1_le
  have hpos : 0 < D.derivativeValue :=
    paper_lemma10_derivative_value_pos_of_current_bounds_certificate
      (lemma6DerivativeFormulaCertificate_of_endpoint_data D)
      ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z
      (by rfl)
      (by rfl)
      (by rfl)
      (by simpa [D] using hQ1)
      (by rfl)
      (by simpa [D] using hT1)
      (by rfl)
      (by simpa [D] using hW1)
      (by rfl)
      hbounds_current hz hR2_pos hQ2_pos hswitch12_pos hsum hu
      hswitch_lt_Q1 hgap_nonneg hA_pos
  simpa [D] using hpos

/-! ## Main dynamic theorems -/

/--
Legacy quotient-domain route for Theorem 2's multiplicative policy shape.

This helper is not the canonical source-facing row: it assumes strict
dominance of every policy with a zero-mass component, whereas the source
permits the `t = 0` non-surge endpoint.  The primitive all-empty improvement
does not discharge that stronger premise. It remains available for
quotient-domain subproofs.
-/
theorem theorem2_multiplicative_policy_shape_ae_quotient_domain
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (hm0_pos : 0 < m 0)
    (hm1_pos : 0 < m 1)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 1))
    (exists_optimal :
      ∃ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
            (fun i : Fin 2 => multiplicativePricing (m i)))
          ρ)
    (zero_mass_strict_dominance :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          dynamicHasZeroAcceptedMass mu σ →
            ∃ τ : Fin 2 → TripPolicy,
              dynamicFeasibleMeasurablePositiveMassPolicy mu τ ∧
                (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
                  (fun i : Fin 2 => multiplicativePricing (m i))) σ <
                (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
                  (fun i : Fin 2 => multiplicativePricing (m i))) τ)
    (nonsurge_response_branch :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
            (fun i : Fin 2 => multiplicativePricing (m i)))
          ρ →
        let base_response :=
          gn21MeasuredLeftLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (ρ 0) (ρ 1)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
        (∀ τ : TripLength, 0 < τ → 0 < base_response τ) ∨
          ∃ t : ℝ,
            0 < t ∧
              StrictAntiOn base_response (Set.Ioi 0) ∧
              base_response t = 0)
    (nonsurge_candidate_mass_pos :
      ∀ ρ : Fin 2 → TripPolicy,
        ∀ _hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
              (fun i : Fin 2 => multiplicativePricing (m i)))
            ρ,
        let marginal_response :=
          gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1)
        0 < singleStateTripMass (mu 0)
          (lemma5PositiveResponsePolicy marginal_response))
    (surge_response_branch :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
            (fun i : Fin 2 => multiplicativePricing (m i)))
          ρ →
        let base_response :=
          gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
        (∀ τ : TripLength, 0 < τ → 0 < base_response τ) ∨
          ∃ t : ℝ,
            0 < t ∧
              StrictMonoOn base_response (Set.Ioi 0) ∧
              base_response t = 0)
    (surge_candidate_mass_pos :
      ∀ ρ : Fin 2 → TripPolicy,
        ∀ _hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
              (fun i : Fin 2 => multiplicativePricing (m i)))
            ρ,
        let marginal_response :=
          gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1)
        0 < singleStateTripMass (mu 1)
          (lemma5PositiveResponsePolicy marginal_response)) :
    GN21Theorem2MeasuredMultiplicativePolicyShapeStatement
      mu arrival switch12 switch21 m := by
  let zero_mass_strict_dominance_certificate :
      DynamicZeroMassStrictDominanceCertificate mu
        (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
          (fun i : Fin 2 => multiplicativePricing (m i))) :=
    { improve_zero_mass := zero_mass_strict_dominance }
  let C :
      Theorem4AllMeasurableGN21MultiplicativeFixedResponsePolicyFormSourceData
        mu arrival switch12 switch21 m :=
    { arrival0_pos := harrival0_pos
      arrival1_pos := harrival1_pos
      switch12_pos := hswitch12_pos
      switch21_pos := hswitch21_pos
      exists_optimal := exists_optimal
      nonsurge := by
        intro ρ hρ
        let base_response : TripLength → ℝ :=
          gn21MeasuredLeftLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (ρ 0) (ρ 1)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
        let htime_integrable :
            ∀ σ : TripPolicy,
              σ ⊆ acceptAllPolicy →
              MeasurableSet σ →
                IntegrableOn (fun τ : TripLength => τ) σ (mu 0) := by
          intro σ hσ_subset _hσ_measurable
          exact htime0_integrable_acceptAll.mono_set hσ_subset
        have hρ_positive_mass :
            dynamicFeasibleMeasurablePositiveMassPolicy mu ρ :=
          (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
            zero_mass_strict_dominance_certificate hρ).1
        have hshape_exists :
            ∃ shape : Lemma5DerivativeShape,
              theorem2MultiplicativeNonsurgeAllowedLemma5Shape shape ∧
                Lemma5PositiveResponseShapeData base_response shape := by
          rcases nonsurge_response_branch ρ hρ with hpositive | hdecreasing
          · refine ⟨.positive, ?_, ?_⟩
            · simp [theorem2MultiplicativeNonsurgeAllowedLemma5Shape]
            · exact
                Lemma5PositiveResponseShapeData.positive
                  (response := base_response)
                  (by
                    intro τ hτ
                    simpa [base_response] using hpositive τ hτ)
          · rcases hdecreasing with ⟨t, ht_pos, hanti, hzero⟩
            refine ⟨.strictlyDecreasing, ?_, ?_⟩
            · simp [theorem2MultiplicativeNonsurgeAllowedLemma5Shape]
            · exact
                Lemma5PositiveResponseShapeData.strictlyDecreasing
                  (response := base_response) t ht_pos
                  (by simpa [base_response] using hanti)
                  (by simpa [base_response] using hzero)
        classical
        let shape_value : Lemma5DerivativeShape := Classical.choose hshape_exists
        have hshape_spec :
            theorem2MultiplicativeNonsurgeAllowedLemma5Shape shape_value ∧
              Lemma5PositiveResponseShapeData base_response shape_value := by
          simpa [shape_value] using Classical.choose_spec hshape_exists
        let shape :
            {shape : Lemma5DerivativeShape //
              theorem2MultiplicativeNonsurgeAllowedLemma5Shape shape} :=
          ⟨shape_value, hshape_spec.1⟩
        exact
          ⟨shape,
            { base_policy_form_data :=
                Lemma5PositiveResponsePolicyFormData.of_shapeData
                  (by simpa [shape, shape_value] using hshape_spec.2)
              current_massI_pos := hρ_positive_mass.2 0
              current_massJ_pos := hρ_positive_mass.2 1
              candidate_mass_pos := by
                simpa using nonsurge_candidate_mass_pos ρ hρ
              time_integrable := htime_integrable }⟩
      surge := by
        intro ρ hρ
        let base_response : TripLength → ℝ :=
          gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
        let htime_integrable :
            ∀ σ : TripPolicy,
              σ ⊆ acceptAllPolicy →
              MeasurableSet σ →
                IntegrableOn (fun τ : TripLength => τ) σ (mu 1) := by
          intro σ hσ_subset _hσ_measurable
          exact htime1_integrable_acceptAll.mono_set hσ_subset
        have hρ_positive_mass :
            dynamicFeasibleMeasurablePositiveMassPolicy mu ρ :=
          (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
            zero_mass_strict_dominance_certificate hρ).1
        have hshape_exists :
            ∃ shape : Lemma5DerivativeShape,
              theorem2MultiplicativeSurgeAllowedLemma5Shape shape ∧
                Lemma5PositiveResponseShapeData base_response shape := by
          rcases surge_response_branch ρ hρ with hpositive | hincreasing
          · refine ⟨.positive, ?_, ?_⟩
            · simp [theorem2MultiplicativeSurgeAllowedLemma5Shape]
            · exact
                Lemma5PositiveResponseShapeData.positive
                  (response := base_response)
                  (by
                    intro τ hτ
                    simpa [base_response] using hpositive τ hτ)
          · rcases hincreasing with ⟨t, ht_pos, hmono, hzero⟩
            refine ⟨.strictlyIncreasing, ?_, ?_⟩
            · simp [theorem2MultiplicativeSurgeAllowedLemma5Shape]
            · exact
                Lemma5PositiveResponseShapeData.strictlyIncreasing
                  (response := base_response) t ht_pos
                  (by simpa [base_response] using hmono)
                  (by simpa [base_response] using hzero)
        classical
        let shape_value : Lemma5DerivativeShape := Classical.choose hshape_exists
        have hshape_spec :
            theorem2MultiplicativeSurgeAllowedLemma5Shape shape_value ∧
              Lemma5PositiveResponseShapeData base_response shape_value := by
          simpa [shape_value] using Classical.choose_spec hshape_exists
        let shape :
            {shape : Lemma5DerivativeShape //
              theorem2MultiplicativeSurgeAllowedLemma5Shape shape} :=
          ⟨shape_value, hshape_spec.1⟩
        exact
          ⟨shape,
            { base_policy_form_data :=
                Lemma5PositiveResponsePolicyFormData.of_shapeData
                  (by simpa [shape, shape_value] using hshape_spec.2)
              current_massI_pos := hρ_positive_mass.2 0
              current_massJ_pos := hρ_positive_mass.2 1
              candidate_mass_pos := by
                simpa using surge_candidate_mass_pos ρ hρ
              time_integrable := htime_integrable }⟩ }
  exact
    GN21Theorem2MeasuredMultiplicativePolicyShapeStatement.of_fixed_response_source_data
      mu arrival switch12 switch21 m C

/--
Auxiliary measurable-domain route for Theorem 2's multiplicative policy shape.

The source's empty-acceptance endpoint is represented directly through the
Appendix-D aggregate `Q,T,W` formula: zero accepted mass contributes zero
earning while retaining its waiting-time contribution.  Aggregate dynamic
optimality itself supplies the Lemma 5 marginal comparisons; the remaining
positive-mass obligation is the source derivative argument for the response
shape branches.

This is retained for compatibility with older measurable-policy work.  The
canonical source-facing row below uses the paper's open policy domain instead.
-/
theorem theorem2_multiplicative_policy_shape_ae_measurable_auxiliary
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)]
    [MeasureTheory.IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (hm0_pos : 0 < m 0)
    (hm1_pos : 0 < m 1)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 1))
    (exists_optimal :
      ∃ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
          ρ)
    (nonsurge_response_branch :
      ∀ ρ : Fin 2 → TripPolicy,
        ∀ hρ :
          dynamicMeasurableOptimal
            (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
            ρ,
        ∀ hmass : 0 < singleStateTripMass (mu 0) (ρ 0),
          let response :=
            gn21MeasuredLeftLemma6ResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0))
              (ρ 0) (ρ 1)
              (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0))
              (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1))
          (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
            ∃ t : ℝ,
              0 < t ∧ StrictAntiOn response (Set.Ioi 0) ∧ response t = 0)
    (surge_response_branch :
      ∀ ρ : Fin 2 → TripPolicy,
        ∀ hρ :
          dynamicMeasurableOptimal
            (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
            ρ,
        ∀ hmass : 0 < singleStateTripMass (mu 1) (ρ 1),
          let response :=
            gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)
              (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0))
              (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1))
          (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
            ∃ t : ℝ,
              0 < t ∧ StrictMonoOn response (Set.Ioi 0) ∧ response t = 0)
    :
    GN21Theorem2AggregateMultiplicativePolicyShapeStatement
      mu arrival switch12 switch21 m := by
  have hswitch_sum_pos : 0 < switch12 + switch21 :=
    add_pos hswitch12_pos hswitch21_pos
  have hswitch_sum_pos_comm : 0 < switch21 + switch12 :=
    add_pos hswitch21_pos hswitch12_pos
  have htime0_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (mu 0) := by
    intro σ hσ_subset _hσ_measurable
    exact htime0_integrable_acceptAll.mono_set hσ_subset
  have htime1_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (mu 1) := by
    intro σ hσ_subset _hσ_measurable
    exact htime1_integrable_acceptAll.mono_set hσ_subset
  have hq0_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn
          (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
          σ (mu 0) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_gn21SwitchProb_of_time_integrable (mu 0) switch12 switch21
        σ (le_of_lt hswitch12_pos) hswitch_sum_pos hσ_subset hσ_measurable
        (htime0_integrable σ hσ_subset hσ_measurable)
  have hq1_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn
          (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
          σ (mu 1) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_gn21SwitchProb_of_time_integrable (mu 1) switch21 switch12
        σ (le_of_lt hswitch21_pos) hswitch_sum_pos_comm hσ_subset hσ_measurable
        (htime1_integrable σ hσ_subset hσ_measurable)
  have hw0_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (multiplicativePricing (m 0)) σ (mu 0) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_multiplicativePricing (mu 0) (m 0) σ
        (htime0_integrable σ hσ_subset hσ_measurable)
  have hw1_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (multiplicativePricing (m 1)) σ (mu 1) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_multiplicativePricing (mu 1) (m 1) σ
        (htime1_integrable σ hσ_subset hσ_measurable)
  change GN21Theorem2EndpointAwarePolicyShapeStatement mu
    (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
  have hforms :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
            (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
            ρ →
          rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (ρ 0) ∧
            rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (ρ 1) := by
    intro ρ hρ
    constructor
    · by_cases hmass_zero : singleStateTripMass (mu 0) (ρ 0) = 0
      · exact
          rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_mass_zero
            (mu 0) (ρ 0) hmass_zero
      · have hmass_pos : 0 < singleStateTripMass (mu 0) (ρ 0) :=
          lt_of_le_of_ne (singleStateTripMass_nonneg (mu 0) (ρ 0))
            (Ne.symm hmass_zero)
        have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ.1 0).1
        have hρ0_measurable : MeasurableSet (ρ 0) := (hρ.1 0).2
        have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ.1 1).1
        have hρ1_measurable : MeasurableSet (ρ 1) := (hρ.1 1).2
        have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
          gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (ρ 0)
            (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
        have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) :=
          gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (ρ 1)
            (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
        have hQ0_pos :
            0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
              (ρ 0) :=
          gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
            switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos
            hswitch_sum_pos hρ0_measurable hρ0_subset
        have hQ1_pos :
            0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
              (ρ 1) :=
          gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21
            switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos
            hswitch_sum_pos_comm hρ1_measurable hρ1_subset
        have hden_pos :
            0 <
              gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
                  (ρ 0) *
                  gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) +
                gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
                  (ρ 1) *
                  gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
          add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
        have hW0 :
            gn21ScaledStateEarning (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0) =
              gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                  (multiplicativePricing (m 0)) (ρ 0) *
                gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
          gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
            (mu 0) (arrival 0)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (multiplicativePricing (m 0)) (ρ 0) harrival0_pos hρ0_measurable
            hρ0_subset rfl
        have hW1 :
            gn21ScaledStateEarning (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1) =
              gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                  (multiplicativePricing (m 1)) (ρ 1) *
                gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) :=
          gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
            (mu 1) (arrival 1)
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
            (multiplicativePricing (m 1)) (ρ 1) harrival1_pos hρ1_measurable
            hρ1_subset rfl
        let base : TripLength → ℝ :=
          gn21MeasuredLeftLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (ρ 0) (ρ 1)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
        let response : TripLength → ℝ :=
          gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1)
        have hresponse_measurable : Measurable response := by
          dsimp [response]
          exact
            measurable_gn21MeasuredLeftMarginalResponseAtCurrent
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1) (continuous_multiplicativePricing (m 0)).measurable
        have hresponse_integrable :
            IntegrableOn response acceptAllPolicy (mu 0) := by
          dsimp [response]
          exact
            integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1) acceptAllPolicy
              (hq0_integrable acceptAllPolicy (fun _ hτ => hτ)
                measurableSet_acceptAllPolicy)
              (hw0_integrable acceptAllPolicy (fun _ hτ => hτ)
                measurableSet_acceptAllPolicy)
              (htime0_integrable acceptAllPolicy (fun _ hτ => hτ)
                measurableSet_acceptAllPolicy)
        have hresponse_optimal :
            ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
              lemma5MarginalSetReward (mu 0) response σ ≤
                lemma5MarginalSetReward (mu 0) response (ρ 0) := by
          intro σ hσ_subset hσ_measurable
          dsimp [response]
          exact
            lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_zero
              mu arrival switch12 switch21
              (fun i => multiplicativePricing (m i)) hρ harrival0_pos
              harrival1_pos hswitch12_pos hswitch21_pos hq0_integrable
              hw0_integrable htime0_integrable σ hσ_subset hσ_measurable
        rcases nonsurge_response_branch ρ hρ hmass_pos with hpositive | hdecreasing
        · have hbase : Lemma5PositiveResponsePolicyFormData base .positive :=
            Lemma5PositiveResponsePolicyFormData.positive base (by
              simpa [base] using hpositive)
          have hscaled :
              Lemma5PositiveResponsePolicyFormData response .positive := by
            simpa [base, response] using
              gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
                (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
                (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
                (ρ 0) (ρ 1)
                (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                  (multiplicativePricing (m 0)) (ρ 0))
                (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                  (multiplicativePricing (m 1)) (ρ 1))
                hbase hQ1_pos hT0_pos hT1_pos hden_pos hW0 hW1
          have hform :=
            paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
              (mu 0) response (ρ 0) hscaled hresponse_measurable
              hresponse_integrable hρ0_measurable hρ0_subset hresponse_optimal
          exact
            rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_multiplicative_nonsurge_lemma5_formAE
              (Or.inl rfl) hform.to_policyFormAlmostEverywhere
        · rcases hdecreasing with ⟨t, ht_pos, hanti, hzero⟩
          have hbase :
              Lemma5PositiveResponsePolicyFormData base .strictlyDecreasing :=
            Lemma5PositiveResponsePolicyFormData.of_shapeData
              (Lemma5PositiveResponseShapeData.strictlyDecreasing
                (response := base) t ht_pos (by simpa [base] using hanti)
                (by simpa [base] using hzero))
          have hscaled :
              Lemma5PositiveResponsePolicyFormData response .strictlyDecreasing := by
            simpa [base, response] using
              gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
                (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
                (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
                (ρ 0) (ρ 1)
                (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                  (multiplicativePricing (m 0)) (ρ 0))
                (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                  (multiplicativePricing (m 1)) (ρ 1))
                hbase hQ1_pos hT0_pos hT1_pos hden_pos hW0 hW1
          have hform :=
            paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
              (mu 0) response (ρ 0) hscaled hresponse_measurable
              hresponse_integrable hρ0_measurable hρ0_subset hresponse_optimal
          exact
            rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_multiplicative_nonsurge_lemma5_formAE
              (Or.inr rfl) hform.to_policyFormAlmostEverywhere
    · by_cases hmass_zero : singleStateTripMass (mu 1) (ρ 1) = 0
      · exact
          rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_mass_zero
            (mu 1) (ρ 1) hmass_zero
      · have hmass_pos : 0 < singleStateTripMass (mu 1) (ρ 1) :=
          lt_of_le_of_ne (singleStateTripMass_nonneg (mu 1) (ρ 1))
            (Ne.symm hmass_zero)
        have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ.1 0).1
        have hρ0_measurable : MeasurableSet (ρ 0) := (hρ.1 0).2
        have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ.1 1).1
        have hρ1_measurable : MeasurableSet (ρ 1) := (hρ.1 1).2
        have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
          gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (ρ 0)
            (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
        have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) :=
          gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (ρ 1)
            (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
        have hQ0_pos :
            0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
              (ρ 0) :=
          gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
            switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos
            hswitch_sum_pos hρ0_measurable hρ0_subset
        have hQ1_pos :
            0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
              (ρ 1) :=
          gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21
            switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos
            hswitch_sum_pos_comm hρ1_measurable hρ1_subset
        have hden_pos :
            0 <
              gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
                  (ρ 0) *
                  gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) +
                gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
                  (ρ 1) *
                  gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
          add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
        have hW0 :
            gn21ScaledStateEarning (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0) =
              gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                  (multiplicativePricing (m 0)) (ρ 0) *
                gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
          gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
            (mu 0) (arrival 0)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (multiplicativePricing (m 0)) (ρ 0) harrival0_pos hρ0_measurable
            hρ0_subset rfl
        have hW1 :
            gn21ScaledStateEarning (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1) =
              gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                  (multiplicativePricing (m 1)) (ρ 1) *
                gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) :=
          gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
            (mu 1) (arrival 1)
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
            (multiplicativePricing (m 1)) (ρ 1) harrival1_pos hρ1_measurable
            hρ1_subset rfl
        let base : TripLength → ℝ :=
          gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (multiplicativePricing (m 0)) (ρ 0))
            (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (multiplicativePricing (m 1)) (ρ 1))
        let response : TripLength → ℝ :=
          gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1)
        have hresponse_measurable : Measurable response := by
          dsimp [response]
          exact
            measurable_gn21MeasuredRightMarginalResponseAtCurrent
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1) (continuous_multiplicativePricing (m 1)).measurable
        have hresponse_integrable :
            IntegrableOn response acceptAllPolicy (mu 1) := by
          dsimp [response]
          exact
            integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1) acceptAllPolicy
              (hq1_integrable acceptAllPolicy (fun _ hτ => hτ)
                measurableSet_acceptAllPolicy)
              (hw1_integrable acceptAllPolicy (fun _ hτ => hτ)
                measurableSet_acceptAllPolicy)
              (htime1_integrable acceptAllPolicy (fun _ hτ => hτ)
                measurableSet_acceptAllPolicy)
        have hresponse_optimal :
            ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
              lemma5MarginalSetReward (mu 1) response σ ≤
                lemma5MarginalSetReward (mu 1) response (ρ 1) := by
          intro σ hσ_subset hσ_measurable
          dsimp [response]
          exact
            lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_one
              mu arrival switch12 switch21
              (fun i => multiplicativePricing (m i)) hρ harrival0_pos
              harrival1_pos hswitch12_pos hswitch21_pos hq1_integrable
              hw1_integrable htime1_integrable σ hσ_subset hσ_measurable
        rcases surge_response_branch ρ hρ hmass_pos with hpositive | hincreasing
        · have hbase : Lemma5PositiveResponsePolicyFormData base .positive :=
            Lemma5PositiveResponsePolicyFormData.positive base (by
              simpa [base] using hpositive)
          have hscaled :
              Lemma5PositiveResponsePolicyFormData response .positive := by
            simpa [base, response] using
              gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
                (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
                (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
                (ρ 0) (ρ 1)
                (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                  (multiplicativePricing (m 0)) (ρ 0))
                (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                  (multiplicativePricing (m 1)) (ρ 1))
                hbase hQ0_pos hT0_pos hT1_pos hden_pos hW0 hW1
          have hform :=
            paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
              (mu 1) response (ρ 1) hscaled hresponse_measurable
              hresponse_integrable hρ1_measurable hρ1_subset hresponse_optimal
          exact
            rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_finite
              (rejectsShortTripsAlmostEverywhere_of_multiplicative_surge_lemma5_formAE
                (Or.inl rfl) hform.to_policyFormAlmostEverywhere)
        · rcases hincreasing with ⟨t, ht_pos, hmono, hzero⟩
          have hbase :
              Lemma5PositiveResponsePolicyFormData base .strictlyIncreasing :=
            Lemma5PositiveResponsePolicyFormData.of_shapeData
              (Lemma5PositiveResponseShapeData.strictlyIncreasing
                (response := base) t ht_pos (by simpa [base] using hmono)
                (by simpa [base] using hzero))
          have hscaled :
              Lemma5PositiveResponsePolicyFormData response .strictlyIncreasing := by
            simpa [base, response] using
              gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
                (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
                (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
                (ρ 0) (ρ 1)
                (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                  (multiplicativePricing (m 0)) (ρ 0))
                (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                  (multiplicativePricing (m 1)) (ρ 1))
                hbase hQ0_pos hT0_pos hT1_pos hden_pos hW0 hW1
          have hform :=
            paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
              (mu 1) response (ρ 1) hscaled hresponse_measurable
              hresponse_integrable hρ1_measurable hρ1_subset hresponse_optimal
          exact
            rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_finite
              (rejectsShortTripsAlmostEverywhere_of_multiplicative_surge_lemma5_formAE
                (Or.inr rfl) hform.to_policyFormAlmostEverywhere)
  refine ⟨?_, hforms⟩
  rcases exists_optimal with ⟨ρ, hρ⟩
  exact ⟨ρ, hρ, (hforms ρ hρ).1, (hforms ρ hρ).2⟩

/-- Source-open single-optimum Theorem 2 policy-shape route.  The proof uses the source surge definition, lifts the open optimum only to justify measurable variations, and then derives both cutoff forms from the primitive response calculations. -/
theorem gn21_multiplicative_open_optimal_policy_shapes
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ) (m : Fin 2 → ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival
      (fun i => multiplicativePricing (m i)))
    {ρ : Fin 2 → TripPolicy}
    (hρopen : dynamicOpenOptimal
      (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m) ρ) :
    rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (ρ 0) ∧
      rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (ρ 1) := by
  have hswitch_sum_pos : 0 < switch12 + switch21 :=
    add_pos hswitch12_pos hswitch21_pos
  have hswitch_sum_pos_comm : 0 < switch21 + switch12 :=
    add_pos hswitch21_pos hswitch12_pos
  have htime0_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (mu 0) := by
    intro σ hσ_subset _hσ_measurable
    exact htime0_integrable_acceptAll.mono_set hσ_subset
  have htime1_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (mu 1) := by
    intro σ hσ_subset _hσ_measurable
    exact htime1_integrable_acceptAll.mono_set hσ_subset
  have hq0_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn
          (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
          σ (mu 0) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_gn21SwitchProb_of_time_integrable (mu 0) switch12 switch21
        σ (le_of_lt hswitch12_pos) hswitch_sum_pos hσ_subset hσ_measurable
        (htime0_integrable σ hσ_subset hσ_measurable)
  have hq1_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn
          (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
          σ (mu 1) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_gn21SwitchProb_of_time_integrable (mu 1) switch21 switch12
        σ (le_of_lt hswitch21_pos) hswitch_sum_pos_comm hσ_subset hσ_measurable
        (htime1_integrable σ hσ_subset hσ_measurable)
  have hw0_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (multiplicativePricing (m 0)) σ (mu 0) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_multiplicativePricing (mu 0) (m 0) σ
        (htime0_integrable σ hσ_subset hσ_measurable)
  have hw1_integrable :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (multiplicativePricing (m 1)) σ (mu 1) := by
    intro σ hσ_subset hσ_measurable
    exact
      integrableOn_multiplicativePricing (mu 1) (m 1) σ
        (htime1_integrable σ hσ_subset hσ_measurable)
  have hρ : dynamicMeasurableOptimal
      (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m) ρ :=
    dynamicMeasurableOptimal_of_dynamicOpenOptimal mu
      (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
      hρopen (fun σ hσ =>
        gn21AggregateMultiplicativeDynamicReward_symmDiffContinuousAt mu arrival m
          switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos
          htime0_integrable_acceptAll htime1_integrable_acceptAll hσ)
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ.1 0).1
  have hρ0_measurable : MeasurableSet (ρ 0) := (hρ.1 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ.1 1).1
  have hρ1_measurable : MeasurableSet (ρ 1) := (hρ.1 1).2
  have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
      switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hswitch_sum_pos
      hρ0_measurable hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21
      switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hswitch_sum_pos_comm
      hρ1_measurable hρ1_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  have hW0 :
      gn21ScaledStateEarning (mu 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0) =
        gn21MeasuredStateRewardRate (mu 0) (arrival 0)
            (multiplicativePricing (m 0)) (ρ 0) *
          gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 0) (arrival 0)
      (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
        (multiplicativePricing (m 0)) (ρ 0))
      (multiplicativePricing (m 0)) (ρ 0) harrival0_pos hρ0_measurable
      hρ0_subset rfl
  have hW1 :
      gn21ScaledStateEarning (mu 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1) =
        gn21MeasuredStateRewardRate (mu 1) (arrival 1)
            (multiplicativePricing (m 1)) (ρ 1) *
          gn21ScaledStateTime (mu 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 1) (arrival 1)
      (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
        (multiplicativePricing (m 1)) (ρ 1))
      (multiplicativePricing (m 1)) (ρ 1) harrival1_pos hρ1_measurable
      hρ1_subset rfl
  constructor
  · by_cases hmass_zero : singleStateTripMass (mu 0) (ρ 0) = 0
    · exact
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_mass_zero
          (mu 0) (ρ 0) hmass_zero
    · have hmass_pos : 0 < singleStateTripMass (mu 0) (ρ 0) :=
        lt_of_le_of_ne (singleStateTripMass_nonneg (mu 0) (ρ 0))
          (Ne.symm hmass_zero)
      let base : TripLength → ℝ :=
        gn21MeasuredLeftLemma6ResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (ρ 0) (ρ 1)
          (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
            (multiplicativePricing (m 0)) (ρ 0))
          (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
            (multiplicativePricing (m 1)) (ρ 1))
      let response : TripLength → ℝ :=
        gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
          (ρ 0) (ρ 1)
      have hresponse_measurable : Measurable response := by
        dsimp [response]
        exact measurable_gn21MeasuredLeftMarginalResponseAtCurrent
          (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
          (ρ 0) (ρ 1) (continuous_multiplicativePricing (m 0)).measurable
      have hresponse_integrable : IntegrableOn response acceptAllPolicy (mu 0) := by
        dsimp [response]
        exact integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
          (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
          (ρ 0) (ρ 1) acceptAllPolicy
          (hq0_integrable acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
          (hw0_integrable acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
          (htime0_integrable acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
      have hresponse_optimal :
          ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
            lemma5MarginalSetReward (mu 0) response σ ≤
              lemma5MarginalSetReward (mu 0) response (ρ 0) := by
        intro σ hσ_subset hσ_measurable
        dsimp [response]
        exact
          lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_zero
            mu arrival switch12 switch21 (fun i => multiplicativePricing (m i)) hρ
            harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hq0_integrable
            hw0_integrable htime0_integrable σ hσ_subset hσ_measurable
      rcases
          gn21MultiplicativeNonsurgeResponseBranch_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
            mu arrival switch12 switch21 m harrival0_pos harrival1_pos
            hswitch12_pos hswitch21_pos htime0_integrable_acceptAll
            htime1_integrable_acceptAll hsurge hρopen hmass_pos with
          hpositive | hdecreasing
      · have hbase : Lemma5PositiveResponsePolicyFormData base .positive :=
          Lemma5PositiveResponsePolicyFormData.positive base (by
            simpa [base] using hpositive)
        have hscaled :
            Lemma5PositiveResponsePolicyFormData response .positive := by
          simpa [base, response] using
            gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)
              (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0))
              (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1))
              hbase hQ1_pos hT0_pos hT1_pos hden_pos hW0 hW1
        have hform :=
          paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
            (mu 0) response (ρ 0) hscaled hresponse_measurable
            hresponse_integrable hρ0_measurable hρ0_subset hresponse_optimal
        exact
          rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_multiplicative_nonsurge_lemma5_formAE
            (Or.inl rfl) hform.to_policyFormAlmostEverywhere
      · rcases hdecreasing with ⟨t, ht_pos, hanti, hzero⟩
        have hbase :
            Lemma5PositiveResponsePolicyFormData base .strictlyDecreasing :=
          Lemma5PositiveResponsePolicyFormData.of_shapeData
            (Lemma5PositiveResponseShapeData.strictlyDecreasing
              (response := base) t ht_pos (by simpa [base] using hanti)
              (by simpa [base] using hzero))
        have hscaled :
            Lemma5PositiveResponsePolicyFormData response .strictlyDecreasing := by
          simpa [base, response] using
            gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)
              (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0))
              (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1))
              hbase hQ1_pos hT0_pos hT1_pos hden_pos hW0 hW1
        have hform :=
          paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
            (mu 0) response (ρ 0) hscaled hresponse_measurable
            hresponse_integrable hρ0_measurable hρ0_subset hresponse_optimal
        exact
          rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_multiplicative_nonsurge_lemma5_formAE
            (Or.inr rfl) hform.to_policyFormAlmostEverywhere
  · by_cases hmass_zero : singleStateTripMass (mu 1) (ρ 1) = 0
    · exact
        rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_mass_zero
          (mu 1) (ρ 1) hmass_zero
    · have hmass_pos : 0 < singleStateTripMass (mu 1) (ρ 1) :=
        lt_of_le_of_ne (singleStateTripMass_nonneg (mu 1) (ρ 1))
          (Ne.symm hmass_zero)
      let base : TripLength → ℝ :=
        gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
          (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
            (multiplicativePricing (m 0)) (ρ 0))
          (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
            (multiplicativePricing (m 1)) (ρ 1))
      let response : TripLength → ℝ :=
        gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
          (ρ 0) (ρ 1)
      have hresponse_measurable : Measurable response := by
        dsimp [response]
        exact measurable_gn21MeasuredRightMarginalResponseAtCurrent
          (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
          (ρ 0) (ρ 1) (continuous_multiplicativePricing (m 1)).measurable
      have hresponse_integrable : IntegrableOn response acceptAllPolicy (mu 1) := by
        dsimp [response]
        exact integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
          (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
          (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
          (ρ 0) (ρ 1) acceptAllPolicy
          (hq1_integrable acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
          (hw1_integrable acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
          (htime1_integrable acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
      have hresponse_optimal :
          ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
            lemma5MarginalSetReward (mu 1) response σ ≤
              lemma5MarginalSetReward (mu 1) response (ρ 1) := by
        intro σ hσ_subset hσ_measurable
        dsimp [response]
        exact
          lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_one
            mu arrival switch12 switch21 (fun i => multiplicativePricing (m i)) hρ
            harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hq1_integrable
            hw1_integrable htime1_integrable σ hσ_subset hσ_measurable
      rcases
          gn21MultiplicativeSurgeResponseBranch_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
            mu arrival switch12 switch21 m harrival0_pos harrival1_pos
            hswitch12_pos hswitch21_pos htime0_integrable_acceptAll
            htime1_integrable_acceptAll hsurge hρopen hmass_pos with
          hpositive | hincreasing
      · have hbase : Lemma5PositiveResponsePolicyFormData base .positive :=
          Lemma5PositiveResponsePolicyFormData.positive base (by
            simpa [base] using hpositive)
        have hscaled :
            Lemma5PositiveResponsePolicyFormData response .positive := by
          simpa [base, response] using
            gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)
              (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0))
              (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1))
              hbase hQ0_pos hT0_pos hT1_pos hden_pos hW0 hW1
        have hform :=
          paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
            (mu 1) response (ρ 1) hscaled hresponse_measurable
            hresponse_integrable hρ1_measurable hρ1_subset hresponse_optimal
        exact
          rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_finite
            (rejectsShortTripsAlmostEverywhere_of_multiplicative_surge_lemma5_formAE
              (Or.inl rfl) hform.to_policyFormAlmostEverywhere)
      · rcases hincreasing with ⟨t, ht_pos, hmono, hzero⟩
        have hbase :
            Lemma5PositiveResponsePolicyFormData base .strictlyIncreasing :=
          Lemma5PositiveResponsePolicyFormData.of_shapeData
            (Lemma5PositiveResponseShapeData.strictlyIncreasing
              (response := base) t ht_pos (by simpa [base] using hmono)
              (by simpa [base] using hzero))
        have hscaled :
            Lemma5PositiveResponsePolicyFormData response .strictlyIncreasing := by
          simpa [base, response] using
            gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
              (ρ 0) (ρ 1)
              (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                (multiplicativePricing (m 0)) (ρ 0))
              (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
                (multiplicativePricing (m 1)) (ρ 1))
              hbase hQ0_pos hT0_pos hT1_pos hden_pos hW0 hW1
        have hform :=
          paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
            (mu 1) response (ρ 1) hscaled hresponse_measurable
            hresponse_integrable hρ1_measurable hρ1_subset hresponse_optimal
        exact
          rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere_of_finite
            (rejectsShortTripsAlmostEverywhere_of_multiplicative_surge_lemma5_formAE
              (Or.inr rfl) hform.to_policyFormAlmostEverywhere)

/-- The exact source-facing Theorem 2 statement, kept as a proposition alias
so the attainment bridge can be reused without a conclusion-bearing record. -/
def theorem2_multiplicative_policy_shape_source_statement
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hmass0_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass1_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival
      (fun i => multiplicativePricing (m i))) : Prop :=
  (∃ rho : Fin 2 → TripPolicy,
    dynamicOpenOptimal
        (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
        rho ∧
      rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
        rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1)) ∧
    ∀ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
          rho →
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
          rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1)

/-- Auxiliary bridge from explicit open-policy optimizer attainment. -/
theorem theorem2_multiplicative_policy_shape_ae_of_open_optimal_exists_auxiliary
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hmass0_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass1_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival
      (fun i => multiplicativePricing (m i)))
    (exists_optimal :
      ∃ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
          (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
          rho) :
    theorem2_multiplicative_policy_shape_source_statement
      mu arrival switch12 switch21 m hm0_nonneg hm1_nonneg harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos hmass0_eq_one hmass1_eq_one htime0_integrable_acceptAll
      htime1_integrable_acceptAll hsurge := by
  dsimp [theorem2_multiplicative_policy_shape_source_statement]
  have hforms :
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
            rho →
          rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
            rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1) := by
    intro rho hrho
    exact
      gn21_multiplicative_open_optimal_policy_shapes mu arrival switch12 switch21 m
        harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos
        htime0_integrable_acceptAll htime1_integrable_acceptAll hsurge hrho
  rcases exists_optimal with ⟨rho, hrho⟩
  exact ⟨⟨rho, hrho, (hforms rho hrho).1, (hforms rho hrho).2⟩, hforms⟩

/--
Theorem 2's multiplicative policy-shape clause on the paper's actual
open-policy domain.

Source anchors: `source.txt:264-285` defines the open policy domain,
`:3710-3714` defines the surge state, and `:560-597` states Theorem 2.

Source status: direct source-facing theorem. Optimizer attainment is proved by
compactifying the exact cutoff family with the source's accept-all and empty
endpoints, proving continuity of the Appendix-D aggregate reward, and combining
the resulting maximum with the direct cutoff-canonicalization proof.
-/
theorem review_theorem2_multiplicative_policy_shape_source_claim
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hmass0_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass1_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival
      (fun i => multiplicativePricing (m i))) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
          rho ∧
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
          rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
            rho →
          rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
            rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1) := by
  have hexists :
      ∃ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
          (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
          rho :=
    gn21_exists_dynamicOpenOptimal_multiplicative_of_source_primitives
      mu arrival m switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0_integrable_acceptAll htime1_integrable_acceptAll hsurge
  simpa [theorem2_multiplicative_policy_shape_source_statement] using
    theorem2_multiplicative_policy_shape_ae_of_open_optimal_exists_auxiliary
      mu arrival switch12 switch21 m hm0_nonneg hm1_nonneg harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos hmass0_eq_one hmass1_eq_one htime0_integrable_acceptAll
      htime1_integrable_acceptAll hsurge hexists

/--
Theorem 2: explicit multiplicative-pricing instance with positive finite
cutoff deviations in both states, and hence measured dynamic non-IC.

Source status: source-facing theorem split
Source note: Paper source map uses `source.txt` lines 516--539; Lean supplies a
concrete bounded-density continuous witness for the paper's non-IC existence
claim.
-/
theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states :
    (((0 < (2 : ℝ) ∧
        rejectsLongTrips 2 (theorem2BothStatesContinuousNonsurgeDeviation 0)) ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
          theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
        theorem2BothStatesContinuousNonsurgeDeviation) ∧
      ((0 < (2 : ℝ) ∧
          rejectsShortTrips 2 (theorem2BothStatesContinuousSurgeDeviation 1)) ∧
        dynamicProfitableDeviation
          (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
            theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
            (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
          theorem2BothStatesContinuousSurgeDeviation)) ∧
      ¬ dynamicIncentiveCompatible
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
          theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesContinuousM i))) :=
    ⟨paper_theorem2_multiplicative_measured_profitable_positive_finite_cutoff_deviations_in_both_states_explicit_continuous,
      paper_theorem2_multiplicative_measured_not_ic_both_states_explicit_continuous⟩

/--
One-threshold structured component used by the historical Theorem 4 route.

This is not the printed Theorem 4.  It assumes optimizer existence and the
bracket data for every optimizer, whereas the source theorem derives those
facts from its Lemma 5 and derivative hypotheses.  It remains an internal
component while the source-exact Theorem 4 target is an audited proof
obligation.
-/
theorem theorem4_one_threshold_structured_component_of_explicit_brackets
  (μ : Fin 2 → MeasureTheory.Measure TripLength) [MeasureTheory.NoAtoms (μ 0)] [MeasureTheory.NoAtoms (μ 1)]
  (arrival m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
  (D : Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData μ arrival switch12 switch21 m z) :
  ∃ ρstar,
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρstar ∧
      (∃ σstar, theorem4NonsurgeShape σstar ∧ policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar, theorem4SurgeShape σstar ∧ policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
          ∀ (ρ : Fin 2 → TripPolicy),
            dynamicMeasurableOptimal
                (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
                  (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
                ρ →
              (∃ σstar, theorem4NonsurgeShape σstar ∧ policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
                ∃ σstar, theorem4SurgeShape σstar ∧ policyAlmostEverywhereEq (μ 1) (ρ 1) σstar := by
  apply paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_bracket_source_data
  assumption

/--
The endpoint-calculus realization used by the finite-variation part of the
Theorem 4 proof.  This is a transparent package of local derivative and sign
facts; it supplies neither optimality nor a policy-form conclusion.

The source writes these calculations with the qualification "except where
`f(u) = 0`".  The companion a.e. source-model package below pairs this
authorized raw finite-endpoint regularity with the null-set convention.  The
latter does not derive the former; both must be reviewed by expanded content
rather than treated as ordinary theorem conclusions or inferred from names.
-/
structure GN21Theorem4EndpointSignRealization
    (R : DynamicReward)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (response : Fin 2 → (Fin 2 → TripPolicy) → TripLength → ℝ)
    (margin : Fin 2 → (Fin 2 → TripPolicy) → TripPolicy → ℝ) where
  upper_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (extra : Nat)
          (endpoints : GN21Lemma5EndpointVector extra)
          (gap : Fin extra) {value : ℝ},
            endpoints (gn21Lemma5GapUpperIndex gap) =
                ENNReal.ofReal value →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i
                      (gn21EndpointVectorPolicy
                        (gn21UpdateEndpoint endpoints
                          (gn21Lemma5GapUpperIndex gap) x))))
                  derivativeValue value ∧
                sameStrictSign derivativeValue
                  (response i
                    (Function.update rho i
                      (gn21EndpointVectorPolicy endpoints)) value)
  lower_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (extra : Nat)
          (endpoints : GN21Lemma5EndpointVector extra)
          (slot : Fin (extra + 1)) {value : ℝ},
            endpoints (gn21LowerEndpointIndex slot) =
                ENNReal.ofReal value →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i
                      (gn21EndpointVectorPolicy
                        (gn21UpdateEndpoint endpoints
                          (gn21LowerEndpointIndex slot) x))))
                  derivativeValue value ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i
                      (gn21EndpointVectorPolicy endpoints)) value)
  upper_right_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (extra : Nat)
          (endpoints : GN21Lemma5EndpointVector extra)
          (gap : Fin extra),
            endpoints (gn21Lemma5GapUpperIndex gap) = 0 →
              ∃ derivativeValue : ℝ,
                HasDerivWithinAt
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))))
                    derivativeValue (Set.Ici 0) 0 ∧
                  sameStrictSign derivativeValue
                    (response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) 0)
  lower_right_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (extra : Nat)
          (endpoints : GN21Lemma5EndpointVector extra)
          (slot : Fin (extra + 1)),
            endpoints (gn21LowerEndpointIndex slot) = 0 →
              ∃ derivativeValue : ℝ,
                HasDerivWithinAt
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21LowerEndpointIndex slot) x))))
                    derivativeValue (Set.Ici 0) 0 ∧
                  sameStrictSign derivativeValue
                    (-response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) 0)
  positive_path_continuous :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (extra : Nat)
          (endpoints : GN21Lemma5EndpointVector extra),
            endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
              ∀ (gap : Fin extra) (upper : ℝ), 0 < upper →
                ContinuousOn
                  (fun x =>
                    R (Function.update rho i
                      (gn21EndpointVectorPolicy
                        (gn21UpdateEndpoint endpoints
                          (gn21Lemma5GapUpperIndex gap) x))))
                  (Set.Icc 0 upper)
  positive_path_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (extra : Nat)
          (endpoints : GN21Lemma5EndpointVector extra)
          (gap : Fin extra) (upper x : ℝ),
            x ∈ Set.Ioo 0 upper →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun y =>
                    R (Function.update rho i
                      (gn21EndpointVectorPolicy
                        (gn21UpdateEndpoint endpoints
                          (gn21Lemma5GapUpperIndex gap) y))))
                  derivativeValue x ∧
                sameStrictSign derivativeValue
                  (response i
                    (Function.update rho i
                      (gn21EndpointVectorPolicy
                        (gn21UpdateEndpoint endpoints
                          (gn21Lemma5GapUpperIndex gap) x))) x)
  right_top_witness :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (source : TripPolicy),
          shape i = .strictlyQuasiConvex →
            ∀ (extra : Nat)
              (endpoints : GN21Lemma5EndpointVector extra),
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i
                      (gn21EndpointVectorPolicy endpoints)) →
                  ∀ gap : Fin extra,
                    endpoints (gn21Lemma5GapLowerIndex gap) = ∞ →
                      ∃ rightValue : ℝ,
                        endpoints (gn21Lemma5GapUpperIndex gap) <
                            ENNReal.ofReal rightValue ∧
                          response i
                            (Function.update rho i
                              (gn21EndpointVectorPolicy endpoints))
                            rightValue ≤ 0
  open_interval_upper_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (context : TripPolicy) (lower upper : ℝ),
          0 ≤ lower → lower < upper →
            ∃ derivativeValue : ℝ,
              HasDerivAt
                (fun x =>
                  R (Function.update rho i
                    (context ∪ Set.Ioo lower x)))
                derivativeValue upper ∧
              sameStrictSign derivativeValue
                (response i
                  (Function.update rho i
                    (context ∪ Set.Ioo lower upper)) upper)
  open_interval_lower_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (context : TripPolicy) (lower upper : ℝ),
          0 < lower → lower < upper →
            ∃ derivativeValue : ℝ,
              HasDerivAt
                (fun x =>
                  R (Function.update rho i
                    (context ∪ Set.Ioo x upper)))
                derivativeValue lower ∧
              sameStrictSign derivativeValue
                (-response i
                  (Function.update rho i
                    (context ∪ Set.Ioo lower upper)) lower)
  open_interval_lower_right_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (context : TripPolicy) (upper : ℝ),
          0 < upper →
            ∃ derivativeValue : ℝ,
              HasDerivWithinAt
                (fun x =>
                  R (Function.update rho i
                    (context ∪ Set.Ioo x upper)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response i
                  (Function.update rho i
                    (context ∪ Set.Ioo 0 upper)) 0)
  open_tail_lower_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (context : TripPolicy) (lower : ℝ),
          0 < lower →
            ∃ derivativeValue : ℝ,
              HasDerivAt
                (fun x => R (Function.update rho i (context ∪ Set.Ioi x)))
                derivativeValue lower ∧
              sameStrictSign derivativeValue
                (-response i (Function.update rho i (context ∪ Set.Ioi lower)) lower)
  open_split_lower_derivative :
    ∀ (rho : Fin 2 → TripPolicy),
      dynamicFeasibleOpenPolicy rho →
        ∀ (i : Fin 2) (policy : TripPolicy) (pivot : ℝ),
          IsOpen policy → policy ⊆ acceptAllPolicy →
            pivot ∈ policy →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                    (fun cutoff =>
                      R (Function.update rho i
                        (gn21InteriorSplitLowerPolicy
                          policy pivot cutoff)))
                    derivativeValue pivot ∧
                  sameStrictSign derivativeValue
                    (-response i (Function.update rho i policy) pivot)

/--
The approved a.e. source-model route for Theorem 4's endpoint variation.

The source treats policies modulo the continuous trip-length law and qualifies
the derivative-sign argument at zero density (`source.txt:3660-3692`); Lemma
6 exposes the density factor in the derivative itself (`source.txt:4110-4148`).
The transparent endpoint-calculus field is the finite-variation implementation
obligation, while the density and policy-equality fields state the source
semantics that make zero-density endpoint moves irrelevant.  This does not
assert full support and does not contain an optimizer conclusion.
-/
structure GN21Theorem4AENullEndpointVariation
    (mu : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (response : Fin 2 → (Fin 2 → TripPolicy) → TripLength → ℝ)
    (margin : Fin 2 → (Fin 2 → TripPolicy) → TripPolicy → ℝ) where
  densityNN : Fin 2 → TripLength → NNReal
  measure_eq_withDensity :
    ∀ i : Fin 2,
      mu i = volume.withDensity (fun tau => (densityNN i tau : ENNReal))
  density_measurable : ∀ i : Fin 2, Measurable (densityNN i)
  policy_equalities_modulo_null_sets :
    ∀ (rho : Fin 2 → TripPolicy), dynamicFeasibleOpenPolicy rho →
      ∀ i : Fin 2,
        policyEqualitiesModuloNullSets (mu i)
          (fun policy => R (Function.update rho i policy))
  endpoint_sign_realization :
    GN21Theorem4EndpointSignRealization R shape response margin

/--
The Theorem 4 a.e. source model identifies endpoint changes over a density-zero
interval.  This is the checked zero-density traversal fact, not a policy-form
or optimizer assumption.
-/
theorem GN21Theorem4AENullEndpointVariation.zero_density_interval_reward_eq
    {mu : Fin 2 → Measure TripLength}
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    {R : DynamicReward}
    {shape : Fin 2 → Lemma5DerivativeShape}
    {response : Fin 2 → (Fin 2 → TripPolicy) → TripLength → ℝ}
    {margin : Fin 2 → (Fin 2 → TripPolicy) → TripPolicy → ℝ}
    (H : GN21Theorem4AENullEndpointVariation mu R shape response margin)
    (rho : Fin 2 → TripPolicy) (hfeasible : dynamicFeasibleOpenPolicy rho)
    (i : Fin 2) (context : TripPolicy) {lower left right : TripLength}
    (hleft_right : left ≤ right)
    (hzero : ∀ tau, tau ∈ Set.Ioo left right → H.densityNN i tau = 0) :
    R (Function.update rho i (context ∪ Set.Ioo lower left)) =
      R (Function.update rho i (context ∪ Set.Ioo lower right)) := by
  haveI : NoAtoms (mu i) := by
    exact Fin.cases (inferInstance : NoAtoms (mu 0))
      (fun j =>
        Fin.cases (inferInstance : NoAtoms (mu 1))
          (fun k => Fin.elim0 k) j) i
  exact H.policy_equalities_modulo_null_sets rho hfeasible i
    (policyAlmostEverywhereEq_union_interval_expand_of_null
      (mu i) context hleft_right
      (measure_Ioo_eq_zero_of_densityNN_eq_zero_on
        (mu i) (H.densityNN i) (H.measure_eq_withDensity i)
        (H.density_measurable i) hzero))

/--
The endpoint-sign formulation of the structural-policy conclusion.  It
packages the two price cases with the response and marginal hypotheses used by
the argument.
-/
private theorem theorem4_full_structural_policy_forms_open_corrected_raw_endpoint_engine
    (mu : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (R : DynamicReward)
    (hreward_model :
      R = gn21AggregateDynamicRewardFunctional
        mu arrival switch12 switch21 w)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (response : Fin 2 → (Fin 2 → TripPolicy) → TripLength → ℝ)
    (margin : Fin 2 → (Fin 2 → TripPolicy) → TripPolicy → ℝ)
    (hnonsurge_price_case :
      (∃ m a : ℝ,
        0 ≤ a ∧ w 0 = affinePricing m a ∧
          shape 0 = .strictlyDecreasing) ∨
      (∃ m a : ℝ,
        0 < a ∧ w 0 = affinePricing m (-a) ∧
          shape 0 = .strictlyQuasiConcave) ∨
      ((∀ rho : Fin 2 → TripPolicy,
          dynamicFeasibleOpenPolicy rho →
            ∀ u : TripLength, 0 < u → 0 < response 0 rho u) ∧
        shape 0 = .positive))
    (hsurge_price_case :
      (∃ m a : ℝ,
        0 ≤ a ∧ w 1 = affinePricing m (-a) ∧
          shape 1 = .strictlyIncreasing) ∨
      (∃ m a : ℝ,
        0 < a ∧ w 1 = affinePricing m a ∧
          shape 1 = .strictlyQuasiConvex) ∨
      ((∀ rho : Fin 2 → TripPolicy,
          dynamicFeasibleOpenPolicy rho →
            ∀ u : TripLength, 0 < u → 0 < response 1 rho u) ∧
        shape 1 = .positive))
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hnontrivial :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ i : Fin 2,
            ∃ seed : TripPolicy,
              IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
                R (Function.update rho i ∅) <
                  R (Function.update rho i seed))
    (hmargin_pos :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            IsOpen source → source ⊆ acceptAllPolicy →
              R (Function.update rho i ∅) <
                  R (Function.update rho i source) →
                0 < margin i rho source)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat),
            ContinuousOn
              (fun endpoints : GN21Lemma5EndpointVector extra =>
                R (Function.update rho i
                  (gn21EndpointVectorPolicy endpoints)))
              (gn21Lemma5EndpointDomain (shape i) extra))
    (hresponse_positive :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .positive →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ u : TripLength, 0 < u →
                    0 < response i (Function.update rho i tau) u)
    (hresponse_increasing :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyIncreasing →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  StrictMonoOn
                    (response i (Function.update rho i tau)) (Set.Ici 0))
    (hresponse_decreasing :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyDecreasing →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  StrictAntiOn
                    (response i (Function.update rho i tau)) (Set.Ici 0))
    (hresponse_quasiConvex :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  strictQuasiConvexOnPositive
                    (response i (Function.update rho i tau)))
    (hzero_quasiConvex :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ {middleLower middleUpper right : ℝ},
                    0 < middleLower → middleLower < middleUpper →
                      middleUpper < right →
                        response i (Function.update rho i tau) middleLower <
                          max
                            (response i (Function.update rho i tau) 0)
                            (response i (Function.update rho i tau) right))
    (hresponse_quasiConcave :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConcave →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  strictQuasiConcaveOnPositive
                    (response i (Function.update rho i tau)))
    (hzero_quasiConcave :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConcave →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ {middle right : ℝ},
                    0 < middle → middle < right →
                      min
                          (response i (Function.update rho i tau) 0)
                          (response i (Function.update rho i tau) right) <
                        response i (Function.update rho i tau) middle)
    (hupper_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (gap : Fin extra) {value : ℝ},
              endpoints (gn21Lemma5GapUpperIndex gap) =
                  ENNReal.ofReal value →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))))
                    derivativeValue value ∧
                  sameStrictSign derivativeValue
                    (response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) value))
    (hlower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (slot : Fin (extra + 1)) {value : ℝ},
              endpoints (gn21LowerEndpointIndex slot) =
                  ENNReal.ofReal value →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21LowerEndpointIndex slot) x))))
                    derivativeValue value ∧
                  sameStrictSign derivativeValue
                    (-response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) value))
    (hupper_right_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (gap : Fin extra),
              endpoints (gn21Lemma5GapUpperIndex gap) = 0 →
                ∃ derivativeValue : ℝ,
                  HasDerivWithinAt
                      (fun x =>
                        R (Function.update rho i
                          (gn21EndpointVectorPolicy
                            (gn21UpdateEndpoint endpoints
                              (gn21Lemma5GapUpperIndex gap) x))))
                      derivativeValue (Set.Ici 0) 0 ∧
                    sameStrictSign derivativeValue
                      (response i
                        (Function.update rho i
                          (gn21EndpointVectorPolicy endpoints)) 0))
    (hlower_right_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (slot : Fin (extra + 1)),
              endpoints (gn21LowerEndpointIndex slot) = 0 →
                ∃ derivativeValue : ℝ,
                  HasDerivWithinAt
                      (fun x =>
                        R (Function.update rho i
                          (gn21EndpointVectorPolicy
                            (gn21UpdateEndpoint endpoints
                              (gn21LowerEndpointIndex slot) x))))
                      derivativeValue (Set.Ici 0) 0 ∧
                    sameStrictSign derivativeValue
                      (-response i
                        (Function.update rho i
                          (gn21EndpointVectorPolicy endpoints)) 0))
    (hpositive_path_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra),
              endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
                ∀ (gap : Fin extra) (upper : ℝ), 0 < upper →
                  ContinuousOn
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))))
                    (Set.Icc 0 upper))
    (hpositive_path_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (gap : Fin extra) (upper x : ℝ),
              x ∈ Set.Ioo 0 upper →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun y =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) y))))
                    derivativeValue x ∧
                  sameStrictSign derivativeValue
                    (response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))) x))
    (hright_top_witness :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ (extra : Nat)
                (endpoints : GN21Lemma5EndpointVector extra),
                  R (Function.update rho i source) - margin i rho source ≤
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) →
                    ∀ gap : Fin extra,
                      endpoints (gn21Lemma5GapLowerIndex gap) = ∞ →
                        ∃ rightValue : ℝ,
                          endpoints (gn21Lemma5GapUpperIndex gap) <
                              ENNReal.ofReal rightValue ∧
                            response i
                              (Function.update rho i
                                (gn21EndpointVectorPolicy endpoints))
                              rightValue ≤ 0)
    (hopen_interval_upper_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (lower upper : ℝ),
            0 ≤ lower → lower < upper →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i
                      (context ∪ Set.Ioo lower x)))
                  derivativeValue upper ∧
                sameStrictSign derivativeValue
                  (response i
                    (Function.update rho i
                      (context ∪ Set.Ioo lower upper)) upper))
    (hopen_interval_lower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (lower upper : ℝ),
            0 < lower → lower < upper →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i
                      (context ∪ Set.Ioo x upper)))
                  derivativeValue lower ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i
                      (context ∪ Set.Ioo lower upper)) lower))
    (hopen_interval_lower_right_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (upper : ℝ),
            0 < upper →
              ∃ derivativeValue : ℝ,
                HasDerivWithinAt
                  (fun x =>
                    R (Function.update rho i
                      (context ∪ Set.Ioo x upper)))
                  derivativeValue (Set.Ici 0) 0 ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i
                      (context ∪ Set.Ioo 0 upper)) 0))
    (hopen_tail_lower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (lower : ℝ),
            0 < lower →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i (context ∪ Set.Ioi x)))
                  derivativeValue lower ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i (context ∪ Set.Ioi lower)) lower))
    (hopen_split_lower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (policy : TripPolicy) (pivot : ℝ),
            IsOpen policy → policy ⊆ acceptAllPolicy →
              pivot ∈ policy →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun cutoff =>
                      R (Function.update rho i
                        (gn21InteriorSplitLowerPolicy
                          policy pivot cutoff)))
                    derivativeValue pivot ∧
                  sameStrictSign derivativeValue
                    (-response i (Function.update rho i policy) pivot)) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional
            mu arrival switch12 switch21 w) rho ∧
        lemma5SourcePolicyForm (shape 0) (rho 0) ∧
        lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w) rho →
          lemma5SourcePolicyFormAlmostEverywhere
              (mu 0) (shape 0) (rho 0) ∧
            lemma5SourcePolicyFormAlmostEverywhere
              (mu 1) (shape 1) (rho 1) := by
  exact GN21DriverSurgePricing.paper_theorem4_source_structural_policy_forms_open_corrected
    (mu := mu) (arrival := arrival) (switch12 := switch12)
    (switch21 := switch21) (w := w) (R := R)
    (hreward_model := hreward_model) (shape := shape)
    (response := response) (margin := margin)
    (hnonsurge_price_case := hnonsurge_price_case)
    (hsurge_price_case := hsurge_price_case)
    (hpair_continuous := hpair_continuous)
    (hnontrivial := hnontrivial) (hmargin_pos := hmargin_pos)
    (hcontinuous := hcontinuous)
    (hendpoint_continuous := hendpoint_continuous)
    (hresponse_positive := hresponse_positive)
    (hresponse_increasing := hresponse_increasing)
    (hresponse_decreasing := hresponse_decreasing)
    (hresponse_quasiConvex := hresponse_quasiConvex)
    (hzero_quasiConvex := hzero_quasiConvex)
    (hresponse_quasiConcave := hresponse_quasiConcave)
    (hzero_quasiConcave := hzero_quasiConcave)
    (hupper_derivative := hupper_derivative)
    (hlower_derivative := hlower_derivative)
    (hupper_right_derivative := hupper_right_derivative)
    (hlower_right_derivative := hlower_right_derivative)
    (hpositive_path_continuous := hpositive_path_continuous)
    (hpositive_path_derivative := hpositive_path_derivative)
    (hright_top_witness := hright_top_witness)
    (hopen_interval_upper_derivative := hopen_interval_upper_derivative)
    (hopen_interval_lower_derivative := hopen_interval_lower_derivative)
    (hopen_interval_lower_right_derivative :=
      hopen_interval_lower_right_derivative)
    (hopen_tail_lower_derivative := hopen_tail_lower_derivative)
    (hopen_split_lower_derivative := hopen_split_lower_derivative)

/-- The non-surge positive-left-marginal condition: every feasible policy has
a strictly positive measured left marginal response at every positive trip
length. -/
def legacy_theorem4_nonsurge_positive_derivative_source_condition_bridge
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction) : Prop :=
  forall rho : Fin 2 -> TripPolicy,
    dynamicFeasibleOpenPolicy rho ->
      forall tau : TripLength, 0 < tau ->
        0 <
          gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1) tau

/-- The surge positive-right-marginal condition: every feasible policy has a
strictly positive measured right marginal response at every positive trip
length. -/
def legacy_theorem4_surge_positive_derivative_source_condition_bridge
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction) : Prop :=
  forall rho : Fin 2 -> TripPolicy,
    dynamicFeasibleOpenPolicy rho ->
      forall tau : TripLength, 0 < tau ->
        0 <
          gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1) tau

/-- The structural-policy conclusion derived from global marginal-response
hypotheses.  It yields an optimal feasible policy in the Lemma 5 policy form,
and the same form almost everywhere for every optimum. -/
theorem legacy_review_theorem4_full_structural_policy_forms_marginal_bridge
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      (legacy_theorem4_nonsurge_positive_derivative_source_condition_bridge
          mu arrival switch12 switch21 w /\
        shape 0 = .positive))
    (hsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      (legacy_theorem4_surge_positive_derivative_source_condition_bridge
          mu arrival switch12 switch21 w /\
        shape 1 = .positive)) :
    (exists rho : Fin 2 -> TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
          rho /\
        lemma5SourcePolicyForm (shape 0) (rho 0) /\
          lemma5SourcePolicyForm (shape 1) (rho 1)) /\
      forall rho : Fin 2 -> TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
            rho ->
          lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) /\
            lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  have hnonsurge_price_case_actual :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 0 = .positive) := by
    simpa only [legacy_theorem4_nonsurge_positive_derivative_source_condition_bridge]
      using hnonsurge_price_case
  have hsurge_price_case_actual :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 1 = .positive) := by
    simpa only [legacy_theorem4_surge_positive_derivative_source_condition_bridge]
      using hsurge_price_case
  exact paper_theorem4_affine_source_price_cases_direct
    mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
    hw0 hw1 hsurge hnonsurge_price_case_actual hsurge_price_case_actual

/-- The literal positive-endpoint row of Theorem 4 for one specified state.

Its premise is the paper's actual derivative along the upper endpoint of a
component of that state, not pointwise positivity of a separately named
marginal-response function.  The displayed continuity-in-policy condition is
the Lemma 5 condition; finite-endpoint continuity is derived below from the
integrable aggregate model. -/
theorem review_theorem4_positive_endpoint_branch_accept_all
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (state : Fin 2)
    (hpositive :
      gn21SourceUpperEndpointDerivativePositiveAt
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) state)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy =>
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                  (Function.update rho i policy)) tau)
    (rho : Fin 2 → TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho ≤
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho state acceptAllPolicy) := by
  have hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i) := by
    intro i
    exact Fin.cases (inferInstance : IsFiniteMeasure (mu 0))
      (fun j =>
        Fin.cases (inferInstance : IsFiniteMeasure (mu 1))
          (fun k => Fin.elim0 k) j) i
  have hinner : ∀ i : Fin 2, (mu i).InnerRegularCompactLTTop := by
    intro i
    fin_cases i <;> infer_instance
  have hatomless : ∀ i : Fin 2, NoAtoms (mu i) := by
    intro i
    exact Fin.cases (inferInstance : NoAtoms (mu 0))
      (fun j =>
        Fin.cases (inferInstance : NoAtoms (mu 1))
          (fun k => Fin.elim0 k) j) i
  have hdominance :=
    gn21SourceUpperEndpointDerivativePositive_state_reward_le_acceptAll
      mu hfinite hinner hatomless
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
      state hpositive hrho hcontinuous
      (continuousOn_gn21AggregateDynamicRewardFunctional_update_endpointPolicy
        mu arrival switch12 switch21 w harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos htime0 htime1 hw0 hw1 rho hrho state)
      (rho state) (hrho state).2 (hrho state).1
  simpa [Function.update_eq_self] using hdominance

/-- The audited source-facing review surface for printed Theorem 4.

The third alternative in each price table is the literal, state-local source
endpoint derivative condition: state `0` for non-surge and state `1` for
surge.  Mixed affine/positive combinations are handled statewise by the
underlying proof.  No global marginal-response positivity bridge appears in
this theorem. -/
theorem review_theorem4_full_structural_policy_forms_direct
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0)) (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      gn21Theorem4NonsurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hsurge_price_case :
      gn21Theorem4SurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy =>
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                  (Function.update rho i policy)) tau) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho ∧
        lemma5SourcePolicyForm (shape 0) (rho 0) ∧
          lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho →
          lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) ∧
            lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  exact paper_theorem4_literal_endpoint_price_cases_direct
    mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
    hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case hcontinuous

/-- The endpoint-sign formulation of the structural-policy conclusion.  It
uses an aggregate-reward representation, endpoint price cases, and the
response and marginal hypotheses of the argument. -/
theorem theorem4_full_structural_policy_forms_open_corrected
    (mu : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (R : DynamicReward)
    (hreward_model :
      R = gn21AggregateDynamicRewardFunctional
        mu arrival switch12 switch21 w)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (response : Fin 2 → (Fin 2 → TripPolicy) → TripLength → ℝ)
    (margin : Fin 2 → (Fin 2 → TripPolicy) → TripPolicy → ℝ)
    (hnonsurge_price_case :
      (∃ m a : ℝ,
        0 ≤ a ∧ w 0 = affinePricing m a ∧
          shape 0 = .strictlyDecreasing) ∨
      (∃ m a : ℝ,
        0 < a ∧ w 0 = affinePricing m (-a) ∧
          shape 0 = .strictlyQuasiConcave) ∨
      ((∀ rho : Fin 2 → TripPolicy,
          dynamicFeasibleOpenPolicy rho →
            ∀ u : TripLength, 0 < u → 0 < response 0 rho u) ∧
        shape 0 = .positive))
    (hsurge_price_case :
      (∃ m a : ℝ,
        0 ≤ a ∧ w 1 = affinePricing m (-a) ∧
          shape 1 = .strictlyIncreasing) ∨
      (∃ m a : ℝ,
        0 < a ∧ w 1 = affinePricing m a ∧
          shape 1 = .strictlyQuasiConvex) ∨
      ((∀ rho : Fin 2 → TripPolicy,
          dynamicFeasibleOpenPolicy rho →
            ∀ u : TripLength, 0 < u → 0 < response 1 rho u) ∧
        shape 1 = .positive))
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hnontrivial :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ i : Fin 2,
            ∃ seed : TripPolicy,
              IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
                R (Function.update rho i ∅) <
                  R (Function.update rho i seed))
    (hmargin_pos :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            IsOpen source → source ⊆ acceptAllPolicy →
              R (Function.update rho i ∅) <
                  R (Function.update rho i source) →
                0 < margin i rho source)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat),
            ContinuousOn
              (fun endpoints : GN21Lemma5EndpointVector extra =>
                R (Function.update rho i
                  (gn21EndpointVectorPolicy endpoints)))
              (gn21Lemma5EndpointDomain (shape i) extra))
    (hresponse_positive :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .positive →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ u : TripLength, 0 < u →
                    0 < response i (Function.update rho i tau) u)
    (hresponse_increasing :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyIncreasing →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  StrictMonoOn
                    (response i (Function.update rho i tau)) (Set.Ici 0))
    (hresponse_decreasing :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyDecreasing →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  StrictAntiOn
                    (response i (Function.update rho i tau)) (Set.Ici 0))
    (hresponse_quasiConvex :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  strictQuasiConvexOnPositive
                    (response i (Function.update rho i tau)))
    (hzero_quasiConvex :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ {middleLower middleUpper right : ℝ},
                    0 < middleLower → middleLower < middleUpper →
                      middleUpper < right →
                        response i (Function.update rho i tau) middleLower <
                          max
                            (response i (Function.update rho i tau) 0)
                            (response i (Function.update rho i tau) right))
    (hresponse_quasiConcave :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConcave →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  strictQuasiConcaveOnPositive
                    (response i (Function.update rho i tau)))
    (hzero_quasiConcave :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConcave →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ {middle right : ℝ},
                    0 < middle → middle < right →
                      min
                          (response i (Function.update rho i tau) 0)
                          (response i (Function.update rho i tau) right) <
                        response i (Function.update rho i tau) middle)
    (H : GN21Theorem4AENullEndpointVariation
      mu R shape response margin) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional
            mu arrival switch12 switch21 w) rho ∧
        lemma5SourcePolicyForm (shape 0) (rho 0) ∧
        lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w) rho →
          lemma5SourcePolicyFormAlmostEverywhere
              (mu 0) (shape 0) (rho 0) ∧
            lemma5SourcePolicyFormAlmostEverywhere
              (mu 1) (shape 1) (rho 1) := by
  exact theorem4_full_structural_policy_forms_open_corrected_raw_endpoint_engine
    (mu := mu) (arrival := arrival) (switch12 := switch12)
    (switch21 := switch21) (w := w) (R := R)
    (hreward_model := hreward_model) (shape := shape)
    (response := response) (margin := margin)
    (hnonsurge_price_case := hnonsurge_price_case)
    (hsurge_price_case := hsurge_price_case)
    (hpair_continuous := hpair_continuous)
    (hnontrivial := hnontrivial) (hmargin_pos := hmargin_pos)
    (hcontinuous := hcontinuous)
    (hendpoint_continuous := hendpoint_continuous)
    (hresponse_positive := hresponse_positive)
    (hresponse_increasing := hresponse_increasing)
    (hresponse_decreasing := hresponse_decreasing)
    (hresponse_quasiConvex := hresponse_quasiConvex)
    (hzero_quasiConvex := hzero_quasiConvex)
    (hresponse_quasiConcave := hresponse_quasiConcave)
    (hzero_quasiConcave := hzero_quasiConcave)
    (hupper_derivative := H.endpoint_sign_realization.upper_derivative)
    (hlower_derivative := H.endpoint_sign_realization.lower_derivative)
    (hupper_right_derivative := H.endpoint_sign_realization.upper_right_derivative)
    (hlower_right_derivative := H.endpoint_sign_realization.lower_right_derivative)
    (hpositive_path_continuous := H.endpoint_sign_realization.positive_path_continuous)
    (hpositive_path_derivative := H.endpoint_sign_realization.positive_path_derivative)
    (hright_top_witness := H.endpoint_sign_realization.right_top_witness)
    (hopen_interval_upper_derivative := H.endpoint_sign_realization.open_interval_upper_derivative)
    (hopen_interval_lower_derivative := H.endpoint_sign_realization.open_interval_lower_derivative)
    (hopen_interval_lower_right_derivative :=
      H.endpoint_sign_realization.open_interval_lower_right_derivative)
    (hopen_tail_lower_derivative := H.endpoint_sign_realization.open_tail_lower_derivative)
    (hopen_split_lower_derivative := H.endpoint_sign_realization.open_split_lower_derivative)

/--
Theorem 3, general existence clause: for target earning rates with `R1 < R2`,
structured CTMC prices attain both accept-all target-rate calibrations and admit
an open optimal policy that accepts all surge trips and has the source's
finite-or-infinite reject-long non-surge cutoff form.  The checked proof splits
at the direct Bellman threshold: the lower branch is the literal zero cutoff
and the upper branch is accept-all.

Source status: direct source-facing theorem.
Source anchors: `source.txt:704-711`, `:3944-4091`, and `:4571-4728`.
-/
theorem review_theorem3_structured_general_policy_source_claim
    (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 : NNReal) (R2 switch12 switch21 : ℝ)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
    (hR1_lt_R2 : (R1 : ℝ) < R2)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime2_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1) :
    ∃ m z : Fin 2 → ℝ, ∃ rho : Fin 2 → TripPolicy,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        gn21MeasuredStateRewardRate (mu 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            acceptAllPolicy = R1 ∧
        gn21MeasuredStateRewardRate (mu 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy = R2 ∧
        rho 1 = acceptAllPolicy ∧
        rejectsLongTripsFiniteOrInfiniteCutoff (rho 0) ∧
        dynamicOpenOptimal
          (gn21AggregateCTMCStructuredDynamicReward
            mu arrival switch12 switch21 m z)
          rho := by
  exact gn21_theorem3_structured_open_optimal_of_nonnegative_target_rates
    mu arrival R1 R2 switch12 switch21 R1.property hR1_lt_R2
    harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one

/--
Theorem 3 furthermore clause: structured CTMC prices attain the two target state
reward rates, make accept-all open-policy optimal, and have no other optimal
policy except up to statewise null sets.  The open-policy objective is the
Appendix-D aggregate reward, which remains meaningful at the source domain's
empty open policy.

Source status: direct source-facing theorem.  The checked proof does not use
the printed Lemma 9 per-policy interval as a uniform fixed-price argument.
Instead, it selects the structured price once from the accept-all primitives,
derives the non-surge Bellman slack from the source ratio condition, and proves
the aggregate reward bound and strict a.e.-uniqueness directly for every open
deviation.

Source anchors: `source.txt:704-720`, `:3944-4091`, and `:4571-4728`.
-/
theorem review_theorem3_structured_ic_source_claim
    (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
    (hR2_pos : 0 < R2)
    (hC_lt_ratio :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < R1 / R2)
    (hratio_lt_one : R1 / R2 < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime2_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1) :
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      gn21MeasuredStateRewardRate (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy = R1 ∧
      gn21MeasuredStateRewardRate (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy = R2 ∧
      dynamicOpenOptimal
        (gn21AggregateCTMCStructuredDynamicReward
          mu arrival switch12 switch21 m z)
        acceptAllDynamicPolicy ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
          (gn21AggregateCTMCStructuredDynamicReward
            mu arrival switch12 switch21 m z)
          rho →
          dynamicAcceptAllAlmostEverywhere mu rho := by
  exact gn21_theorem3_structured_open_ic_of_source_primitives
    mu arrival R1 R2 switch12 switch21 hR2_pos hC_lt_ratio hratio_lt_one
    harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one

/--
Legacy auxiliary Theorem 3 route under an explicit policy-uniform
current-bound premise.  It is retained for comparison with the original
Lemma 9 proof route and is not used by the direct source theorem above.
-/
theorem theorem3_defined_reward_ic_of_uniform_current_bounds_auxiliary
    (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (hR2_pos : 0 < R2)
    (hC_lt_ratio :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < R1 / R2)
    (hratio_lt_one : R1 / R2 < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 1))
    (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1)
    (surge_current_lower_reward_bound_fixed_upper_primitives :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          (hparams :
            theorem3AcceptAllStructuredParameterEvidence
              mu arrival R1 R2 switch12 switch21 m z) →
            0 < (Theorem3AcceptAllStructuredParameterData.of_evidence
              hparams).surgeRatio ∧
              ∀ ρ : Fin 2 → TripPolicy,
                dynamicFeasibleMeasurablePositiveMassPolicy mu ρ →
                  ∃ R1_current : ℝ,
                    R1_current ≤ R1 ∧
                      gn21MeasuredStateRewardRate (mu 0) (arrival 0)
                        (ctmcStructuredSurgePrice (m 0) (z 0)
                          switch12 switch21)
                        (ρ 0) = R1_current ∧
                      lemma9StructuredLower
                        (gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0))
                        (gn21ExitWeightIntegral (mu 0) (arrival 0)
                          switch12 switch21 (ρ 0))
                        (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
                        (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
                          switch21 switch12)
                        switch21 ≤ 0 ∧
                      gn21AcceptAllScaledStateTime (mu 0) (arrival 0) *
                          gn21ExitWeightIntegral (mu 0) (arrival 0)
                            switch12 switch21 (ρ 0) ≤
                        gn21ScaledStateTime (mu 0) (arrival 0) (ρ 0) *
                          gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0)
                            switch12 switch21) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicDefinedMeasurableIncentiveCompatible
          (DynamicDefinedReward.of_total mu
            (gn21MeasuredCTMCStructuredDynamicReward
              mu arrival switch12 switch21 m z)) ∧
        (∀ ρ : Fin 2 → TripPolicy,
          dynamicDefinedMeasurableOptimal
            (DynamicDefinedReward.of_total mu
              (gn21MeasuredCTMCStructuredDynamicReward
                mu arrival switch12 switch21 m z)) ρ →
            dynamicAcceptAllAlmostEverywhere mu ρ) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        theorem3AcceptAllStructuredParameterEvidence
          mu arrival R1 R2 switch12 switch21 m z := by
  let rho : ℝ := R1 / R2
  have hR1_eq : R1 = rho * R2 := by
    dsimp [rho]
    field_simp [ne_of_gt hR2_pos]
  have hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < rho := by
    simpa [rho] using hC_lt_ratio
  have hrho_lt_one : rho < 1 := by
    simpa [rho] using hratio_lt_one
  have hswitch_sum_pos : 0 < switch12 + switch21 := by
    linarith [hswitch12_pos, hswitch21_pos]
  have hswitch_sum_pos_comm : 0 < switch21 + switch12 := by
    simpa [add_comm] using hswitch_sum_pos
  have hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (mu 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (mu 0) switch12 switch21
      acceptAllPolicy (le_of_lt hswitch12_pos) hswitch_sum_pos
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime1_integrable
  have hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (mu 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (mu 1) switch21 switch12
      acceptAllPolicy (le_of_lt hswitch21_pos) hswitch_sum_pos_comm
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime2_integrable
  have hmass1_pos : 0 < singleStateTripMass (mu 0) acceptAllPolicy := by
    rw [hmass1_eq_one]
    norm_num
  have hmass2_pos : 0 < singleStateTripMass (mu 1) acceptAllPolicy := by
    rw [hmass2_eq_one]
    norm_num
  have hmeasure1_pos : 0 < (mu 0) acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos (mu 0) acceptAllPolicy hmass1_pos
  rcases theorem3_acceptAll_ratio_source_scalar_consequences
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      rho R1 R2 hR1_eq hR2_pos hC_lt_rho hrho_lt_one
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable hq1_integrable hmeasure1_pos with
    ⟨_, hR1_pos, hR1_lt_R2⟩
  let A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        mu arrival rho R1 R2 switch12 switch21 :=
    { hR1_eq := hR1_eq
      hR1_pos := hR1_pos
      hR1_lt_R2 := hR1_lt_R2
      hR2_pos := hR2_pos
      hC_lt_rho := hC_lt_rho
      hrho_lt_one := hrho_lt_one
      harrival1_pos := harrival1_pos
      harrival2_pos := harrival2_pos
      hswitch12_pos := hswitch12_pos
      hswitch21_pos := hswitch21_pos
      htime1_integrable := htime1_integrable
      htime2_integrable := htime2_integrable
      hq1_integrable := hq1_integrable
      hq2_integrable := hq2_integrable
      hmass1_pos := hmass1_pos
      hmass2_pos := hmass2_pos
      surge_reward_rate_data := by
        intro m z hnonneg hparams ρ hρ
        let P := Theorem3AcceptAllStructuredParameterData.of_evidence hparams
        rcases
            surge_current_lower_reward_bound_fixed_upper_primitives
              m z hnonneg hparams with
          ⟨hsurgeRatio_pos, hcurrent_data⟩
        rcases hcurrent_data ρ hρ with
          ⟨R1_current, hRcurrent_le, hfixed_reward_rate,
            hcurrent_lower_nonpos, hfixed_upper_cross⟩
        have hR_nonneg : 0 ≤ R1_current :=
          theorem3CurrentNonsurgeRewardRate_nonneg_of_acceptAllLemma10
            harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
            hR2_pos htime1_integrable htime2_integrable hq1_integrable
            hq2_integrable P hρ
            (by
              simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
                using hfixed_reward_rate)
        have hT2_ge_one :
            1 ≤ gn21AcceptAllScaledStateTime (mu 1) (arrival 1) :=
          gn21ScaledStateTime_ge_one_of_nonneg (mu 1) (arrival 1)
            acceptAllPolicy (le_of_lt harrival2_pos)
            measurableSet_acceptAllPolicy (fun _ hτ => hτ)
        have hsum21 : 0 < switch21 + switch12 := by
          linarith [hswitch21_pos, hswitch12_pos]
        have hswitch_lt_Q2 :
            switch21 <
              gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
                switch21 switch12 :=
          paper_remark4_exit_weight_gt_switch_of_positive_measure
            (mu 1) (arrival 1) switch21 switch12 acceptAllPolicy
            harrival2_pos hswitch21_pos hsum21 measurableSet_acceptAllPolicy
            (fun _ hτ => hτ) hq2_integrable
            (measure_pos_of_singleStateTripMass_pos (mu 1) acceptAllPolicy
              hmass2_pos)
        have hmRtarget_pos : 0 < m 1 - R1 :=
          P.m1_sub_R1_pos_of_surgeRatio_pos hR1_pos hR1_lt_R2
            hT2_ge_one hswitch_lt_Q2 hsurgeRatio_pos
        rcases
            exists_effectiveRatio_pos_le_targetRatio_of_reward_le
              (z 1) P.surgeRatio (m 1) R1 R1_current
              P.surge_z_eq_ratio_m_sub_R1 hsurgeRatio_pos
              hmRtarget_pos hRcurrent_le with
          ⟨effectiveRatio, hz_effective, _heffective_pos,
            _heffective_le⟩
        let D :
            GN21SurgeLemma9AcceptAllAggregateRewardRateData
              (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) effectiveRatio (m 0) (z 0)
              (ρ 0) (ρ 1) :=
          GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_target_ratio_reward_le_current_lower_fixed_upper
            (hρ.1 0).1 (hρ.1 0).2 (hρ.1 1).1 (hρ.1 1).2
            harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
            htime2_integrable hq2_integrable hmass2_pos (hρ.2 1)
            (by
              simpa [gn21AcceptAllScaledStateTime,
                gn21AcceptAllExitWeightIntegral] using
                P.surge_acceptAll_bounds)
            (by
              simpa [gn21AcceptAllScaledStateTime,
                gn21AcceptAllExitWeightIntegral] using
                hcurrent_lower_nonpos)
            P.surge_z_eq_ratio_m_sub_R1 hsurgeRatio_pos hmRtarget_pos
            hz_effective hRcurrent_le hR_nonneg
            (by
              simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
                using hfixed_reward_rate)
            (by
              simpa [gn21AcceptAllScaledStateTime,
                gn21AcceptAllExitWeightIntegral] using
                hfixed_upper_cross)
        exact
          ⟨R1_current, effectiveRatio, D⟩ }
  simpa [theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion] using
    paper_theorem3_measured_structured_defined_reward_ic_ae_unique_prices_of_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 proved small-surge-gap subcase, not an unrestricted replacement.

The paper's fixed-price construction is in `source.txt` lines 3944--3990, and
the policy-dependent Lemma 9 interval calculation is in lines 4571--4728.
In addition to the paper's primitive target-rate and CTMC conditions, this row
exposes the nonsurge reward-envelope inequality and the accept-all surge gap
bound `lambda_21 * Tbar_2 - Qbar_2 <= lambda_21`.  Those strengthenings make
one constructed price work for all positive-mass measurable deviations.  The
conclusion is positive-mass measurable IC only; it does not claim the source
theorem's unrestricted uniform intersection or a.e.-uniqueness conclusion.
-/
theorem review_theorem3_positive_mass_ic_small_surge_gap_subcase
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (hR2_pos : 0 < R2)
    (hC_lt_ratio :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < R1 / R2)
    (hratio_lt_one : R1 / R2 < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (mu 1))
    (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1)
    (arrival_nonsurge_ratio_numerator_bound :
      (arrival 0) *
          ((R1 / R2) * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
            (gn21AcceptAllScaledStateTime (mu 0) (arrival 0) - 1)) ≤
        gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 -
          switch12)
    (surge_acceptAll_gap_le_switch :
      switch21 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1) -
          gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 ≤
        switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      mu arrival R1 R2 switch12 switch21 := by
  let rho : ℝ := R1 / R2
  have hR1_eq : R1 = rho * R2 := by
    dsimp [rho]
    field_simp [ne_of_gt hR2_pos]
  have hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < rho := by
    simpa [rho] using hC_lt_ratio
  have hrho_lt_one : rho < 1 := by
    simpa [rho] using hratio_lt_one
  have arrival_nonsurge_ratio_numerator_bound_rho :
      (arrival 0) *
          (rho * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
            (gn21AcceptAllScaledStateTime (mu 0) (arrival 0) - 1)) ≤
        gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 -
          switch12 := by
    simpa [rho] using arrival_nonsurge_ratio_numerator_bound
  have hswitch_sum_pos : 0 < switch12 + switch21 := by
    linarith [hswitch12_pos, hswitch21_pos]
  have hswitch_sum_pos_comm : 0 < switch21 + switch12 := by
    simpa [add_comm] using hswitch_sum_pos
  have hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (mu 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (mu 0) switch12 switch21
      acceptAllPolicy (le_of_lt hswitch12_pos) hswitch_sum_pos
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime1_integrable
  have hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (mu 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (mu 1) switch21 switch12
      acceptAllPolicy (le_of_lt hswitch21_pos) hswitch_sum_pos_comm
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime2_integrable
  let A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeGapDataAssumptions
        mu arrival rho R1 R2 switch12 switch21 :=
    { hR1_eq := hR1_eq
      hR2_pos := hR2_pos
      hC_lt_rho := hC_lt_rho
      hrho_lt_one := hrho_lt_one
      harrival1_pos := harrival1_pos
      harrival2_pos := harrival2_pos
      hswitch12_pos := hswitch12_pos
      hswitch21_pos := hswitch21_pos
      htime1_integrable := htime1_integrable
      htime2_integrable := htime2_integrable
      hq1_integrable := hq1_integrable
      hq2_integrable := hq2_integrable
      hmass1_eq_one := hmass1_eq_one
      hmass2_eq_one := hmass2_eq_one
      arrival_nonsurge_ratio_numerator_bound :=
        arrival_nonsurge_ratio_numerator_bound_rho
      surge_acceptAll_gap_le_switch := surge_acceptAll_gap_le_switch }
  exact
    theorem3_positive_mass_measurable_ic_of_small_surge_gap
      mu arrival rho R1 R2 switch12 switch21 A

end ProofBridge
end GN21DriverSurgePricing

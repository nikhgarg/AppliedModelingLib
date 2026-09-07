import PRPKG24AccuracyDiversity.ProofInterface
import PRPKG24AccuracyDiversity.SourcePreferenceMixture

/-!
# Paper Assumptions: PRPKG24 Accuracy-Diversity

This file records source theorem-domain conditions and validation notes used by
the paper-facing review surface. Proposition 4's concrete sphere/uniform-measure
argument is proved; its ledger row records the regularity and paper-`Gamma`
interpretation used to read the displayed limit as the compact supremum
objective used by the Lean theorem.
-/

namespace PRPKG24AccuracyDiversity

/-- Example 1 uses a calibrated two-type exponential mixture with positive parameters. -/
-- audit-premise: hp1 : 0 < p1
-- audit-premise: hp2 : 0 < p2
-- audit-premise: hlambda : 0 < lambda
-- audit-premise: hp_sum : p1 + p2 = 1
abbrev assumption_example1_positive_calibrated_exponential_parameters
    (p1 p2 lambda : ℝ) : Prop :=
  0 < p1 ∧ 0 < p2 ∧ 0 < lambda ∧ p1 + p2 = 1

/-- Theorem 1(i) finite-discrete endpoint separates a top value from lower values. -/
-- audit-premise: hk_pos : 0 < k
-- audit-premise: hxTop_pos : 0 < xTop
-- audit-premise: hxSecond_nonneg : 0 ≤ xSecond
-- audit-premise: hsecond_le_top : xSecond ≤ xTop
-- audit-premise: hsecond_lt_top : xSecond < xTop
-- audit-premise: hvalue_nonneg : ∀ ω, 0 ≤ value ω
-- audit-premise: hvalue_le : ∀ ω, value ω ≤ xTop
-- audit-premise: hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond
abbrev assumption_finite_discrete_top_value_domain {Ω : Type*}
    (k : ℕ) (value : Ω → ℝ) (xTop xSecond : ℝ) : Prop :=
  0 < k ∧
    0 < xTop ∧
      0 ≤ xSecond ∧
        xSecond ≤ xTop ∧
          xSecond < xTop ∧
            (∀ ω, 0 ≤ value ω) ∧
              (∀ ω, value ω ≤ xTop) ∧
                (∀ ω, value ω = xTop ∨ value ω ≤ xSecond)

/-- A source preference PMF has positive support when every type is selectable. -/
-- audit-premise: hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal
abbrev assumption_positive_source_preference_law {T : ℕ}
    (preferenceLaw : SourcePreferenceLaw T) : Prop :=
  ∀ t : ItemType T, 0 < (preferenceLaw t).toReal

/-- Type-likelihood weights in the optimization model are positive. -/
-- audit-premise: hlike_pos : ∀ t : ItemType T, 0 < likelihood t
-- audit-premise: hlike_pos : ∀ t, 0 < likelihood t
-- audit-premise: hlike_pos : ∀ t, 0 < B.likelihood t
abbrev assumption_positive_type_likelihoods {T : ℕ}
    (likelihood : ItemType T → ℝ) : Prop :=
  ∀ t : ItemType T, 0 < likelihood t

/-- Theorem 1(ii) and Lemma 1 use the bounded-support upper-endpoint density domain. -/
-- audit-premise: h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M
-- audit-premise: h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y
-- audit-premise: hM_pos : 0 < M
-- audit-premise: hbeta_pos : 0 < beta
-- audit-premise: hc_pos : 0 < c
-- audit-premise: hwidth_pos : 0 < M - L
abbrev assumption_bounded_upper_endpoint_density_domain
    (baseMeasure : MeasureTheory.Measure ℝ) (L M beta c : ℝ) : Prop :=
  (∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M) ∧
    (∀ᵐ y ∂baseMeasure, 0 ≤ y) ∧
      0 < M ∧ 0 < beta ∧ 0 < c ∧ 0 < M - L

/-- Theorem 1(iii)/Lemma D.3 use positive exponential rate and top-k size. -/
-- audit-premise: hlambda_pos : 0 < lambda
-- audit-premise: hk_pos : 0 < k
abbrev assumption_exponential_order_statistic_domain
    (lambda : ℝ) (k : ℕ) : Prop :=
  0 < lambda ∧ 0 < k

/-- Theorem 1(iv)/Lemma D.4 use the finite-mean Pareto domain. -/
-- audit-premise: halpha : 1 < alpha
-- audit-premise: hk : 0 < k
abbrev assumption_pareto_finite_mean_domain (alpha : ℝ) (k : ℕ) : Prop :=
  1 < alpha ∧ 0 < k

/-- Theorem 1(v) common-mean all-consumed endpoint uses an argmax condition. -/
-- audit-premise: hmean_nonneg : 0 ≤ mean
-- audit-premise: hbest : ∀ t, likelihood t ≤ likelihood best
abbrev assumption_common_mean_argmax_domain {T : ℕ}
    (likelihood : ItemType T → ℝ) (mean : ℝ) (best : ItemType T) : Prop :=
  0 ≤ mean ∧ ∀ t, likelihood t ≤ likelihood best

/-- Theorem 1(v) converse uses a positive mean and unique likelihood maximizer. -/
-- audit-premise: hmean_pos : 0 < mean
-- audit-premise: hbest_strict : ∀ t, t ≠ best → likelihood t < likelihood best
abbrev assumption_unique_common_mean_argmax_domain {T : ℕ}
    (likelihood : ItemType T → ℝ) (mean : ℝ) (best : ItemType T) : Prop :=
  0 < mean ∧ ∀ t, t ≠ best → likelihood t < likelihood best

/-- Corollary 1 ranges over nonnegative homogeneity exponents. -/
-- audit-premise: hgamma_nonneg : 0 ≤ gamma
abbrev assumption_nonnegative_homogeneity_exponent (gamma : ℝ) : Prop :=
  0 ≤ gamma

/-
Theorem 2's literal finite rank-varying Bernoulli law.  The source's phrase
"i.i.d. Bernoulli" is not used here: different ranks have different success
parameters, so the checked model is independent across ranks rather than iid.
-/
-- audit-premise: halpha_nonneg : 0 ≤ alpha
-- audit-premise: hc_nonneg : 0 ≤ c
-- audit-premise: hd_nonneg : 0 ≤ d
-- audit-premise: hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1
abbrev assumption_decaying_bernoulli_probability_domain
    (alpha c d : ℝ) : Prop :=
  0 ≤ alpha ∧
    0 ≤ c ∧
      0 ≤ d ∧
        decayingBernoulliSuccess c d alpha 0 ≤ 1

/-
The universal-optimum top-one branches additionally need a nonflat first
rank.  At `c = 0` or first-rank success probability one, non-homogeneous
optimal selections can exist; this is a visible corrected-source condition.
-/
-- audit-premise: halpha_nonneg : 0 ≤ alpha
-- audit-premise: hc_pos : 0 < c
-- audit-premise: hd_nonneg : 0 ≤ d
-- audit-premise: hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1
abbrev assumption_decaying_bernoulli_top_one_nondegenerate_domain
    (alpha c d : ℝ) : Prop :=
  0 ≤ alpha ∧
    0 < c ∧
      0 ≤ d ∧
        decayingBernoulliSuccess c d alpha 0 < 1

/-- Backward-compatible audit alias for the literal finite-law domain. -/
abbrev assumption_decaying_bernoulli_parameter_domain
    (alpha c d : ℝ) : Prop :=
  assumption_decaying_bernoulli_probability_domain alpha c d

/-- Every source Bernoulli probability lies in its probability range. -/
-- audit-premise: hprob_valid : ∀ t, 0 ≤ B.successProb t ∧ B.successProb t ≤ 1
abbrev assumption_bernoulli_success_probability_range {T : ℕ}
    (B : BernoulliSatisfactionModel T) : Prop :=
  ∀ t, 0 ≤ B.successProb t ∧ B.successProb t ≤ 1

/-- Theorem 3's top-one conclusion uses typewise probabilities in `(0,1)`. -/
-- audit-premise: hprob_pos : ∀ t, 0 < B.successProb t
-- audit-premise: hprob_lt_one : ∀ t, B.successProb t < 1
abbrev assumption_theorem3_varying_bernoulli_probability_domain {T : ℕ}
    (B : BernoulliSatisfactionModel T) : Prop :=
  assumption_bernoulli_success_probability_range B ∧
    (∀ t, 0 < B.successProb t) ∧
      (∀ t, B.successProb t < 1)

/-- Corollary 3 additionally specializes Theorem 3 to a common probability. -/
-- audit-premise: hprob_pos : ∀ t, 0 < B.successProb t
-- audit-premise: hprob_lt_one : ∀ t, B.successProb t < 1
-- audit-premise: hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j
abbrev assumption_corollary3_iid_bernoulli_probability_domain {T : ℕ}
    (B : BernoulliSatisfactionModel T) : Prop :=
  assumption_theorem3_varying_bernoulli_probability_domain B ∧
      (∀ i j : ItemType T, B.successProb i = B.successProb j)

/-- Proposition 2's corrected uniform route uses positive type likelihoods and top-k counts. -/
-- audit-premise: hkpos : ∀ N, 0 < N → 0 < kseq N
abbrev assumption_uniform_top_k_positive_count_domain (kseq : ℕ → ℕ) : Prop :=
  ∀ N, 0 < N → 0 < kseq N

/--
Lemma D.2 uses the bounded-tail CDF power sandwich, monotonicity/range facts,
and bounded-support saturation for the reflected CDF.
-/
-- audit-premise: tail : BoundedTailCDFPowerSandwich G β c
-- audit-premise: k_pos : 0 < k
-- audit-premise: hM_pos : 0 < M
-- audit-premise: hG_measurable : Measurable G
-- audit-premise: hG_mono : Monotone G
-- audit-premise: hG_nonneg : ∀ x : ℝ, 0 ≤ G x
-- audit-premise: hG_le_one : ∀ x : ℝ, G x ≤ 1
-- audit-premise: hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1
abbrev assumption_lemmaD2_cdf_power_sandwich_monotone_bounded_support
    {G : ℝ → ℝ} (β c M : ℝ) (k : ℕ) : Prop :=
  BoundedTailCDFPowerSandwich G β c ∧
    0 < k ∧
      0 < M ∧
        Measurable G ∧
          Monotone G ∧
            (∀ x : ℝ, 0 ≤ G x) ∧
              (∀ x : ℝ, G x ≤ 1) ∧
                (∀ x : ℝ, M ≤ x → G x = 1)

/--
Proposition 4's source radial kernel is nonconstant on distances realized by
the unit sphere and takes values in `(0, 1]` there.  The two witnessed radii
make "nonconstant" an explicit property of the realized distance range rather
than of irrelevant values of `q` outside `[0, 2]`.
-/
-- audit-premise: hp_nonconstant : ∃ r ∈ Set.Icc (0 : ℝ) 2, ∃ s ∈ Set.Icc (0 : ℝ) 2, q r ≠ q s
-- audit-premise: hp_range : ∀ r ∈ Set.Icc (0 : ℝ) 2, 0 < q r ∧ q r ≤ 1
abbrev assumption_proposition4_radial_nonsatisfaction_kernel
    (q : ℝ → ℝ) : Prop :=
  (∃ r ∈ Set.Icc (0 : ℝ) 2,
      ∃ s ∈ Set.Icc (0 : ℝ) 2, q r ≠ q s) ∧
    ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < q r ∧ q r ≤ 1

/--
The compact-sphere Laplace step uses continuity of the radial kernel. Together
with the positive-a.e. preference-density clarification, this is the approved
regularity domain under which the Proposition 4 Laplace display is read as its
pointwise supremum.
-/
-- audit-premise: hp : Continuous q
abbrev assumption_proposition4_continuous_sphere_laplace_boundary
    (q : ℝ → ℝ) : Prop :=
  Continuous q

/--
The Proposition 4 preference law is represented by a measurable density with
respect to normalized sphere volume, positive almost everywhere.  This makes
the preference and geometric volume null sets compatible in the averaging
argument; continuity of the density is not required.
-/
-- audit-premise: hdensity : AEMeasurable density (Proposition4Sphere.sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E))
-- audit-premise: hdensity_pos : ∀ᵐ u ∂Proposition4Sphere.sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E), density u ≠ 0
-- audit-premise: hpreference : preferenceMeasure = (Proposition4Sphere.sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)).withDensity density
abbrev assumption_proposition4_positive_preference_density
    {X : Type*} [MeasurableSpace X]
    (baseMeasure preferenceMeasure : MeasureTheory.Measure X)
    (density : X → ENNReal) : Prop :=
  AEMeasurable density baseMeasure ∧
    (∀ᵐ u ∂baseMeasure, density u ≠ 0) ∧
      preferenceMeasure =
        baseMeasure.withDensity density

/-- Lemma D.5's finite rounding endpoint is stated for positive `N`. -/
-- audit-premise: hNpos : 0 < N
abbrev assumption_positive_rounding_population_size (N : ℕ) : Prop :=
  0 < N

end PRPKG24AccuracyDiversity

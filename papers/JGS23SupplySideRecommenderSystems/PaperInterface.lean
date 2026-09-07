import JGS23SupplySideRecommenderSystems.LegacyPaperInterface

/-!
# Source-facing interface for Supply-Side Equilibria in Recommender Systems

This module deliberately contains only transparent source specifications and
source vocabulary.  The checked theorems that realize those specifications are
in `ProofInterface`; the pre-v11 proof-facing convenience wrappers remain in
`LegacyPaperInterface` while downstream clients migrate.

The source uses `p / ‖p‖` even when zero can lie in topological support.  The
formal source-facing results therefore use the zero-safe nonzero-support genre
set.  This is a recorded corrected-target convention, not an implicit change
to the game model.
-/

namespace JGS23SupplySideRecommenderSystems

open scoped Topology
open AppliedModelingLib.Optimization
open MeasureTheory

/-- Source model vocabulary: uniform-tie symmetric mixed Nash equilibrium. -/
def symmetricMixedNashModelSpec {D N P : ℕ}
    (users : Fin N → Content D) (cost : Content D → ℝ)
    (μ : MixedContentStrategy D) : Prop :=
  IsProbabilityMeasure μ ∧
    μ.support ⊆ {p : Content D | NonnegativeContent p} ∧
      ∀ (j : Fin P) (p : Content D), p ∈ μ.support →
        ∀ q : Content D, NonnegativeContent q →
          SourceMixedPurePayoff
              (ExpectedUsersWonAgainstSymmetricMixed users j) cost q μ ≤
            SourceMixedPurePayoff
              (ExpectedUsersWonAgainstSymmetricMixed users j) cost p μ

/-- Source vocabulary for the genre set, excluding the undefined zero ray. -/
def nonzeroSupportGenresSpec {D : ℕ} (ν : SourceNorm D)
    (μ : MixedContentStrategy D) : Set (Content D) :=
  {genre | ∃ p : Content D, p ∈ μ.support ∧ NonzeroContent p ∧
    genre = SourceNorm.normalizedContent ν p}

/-- Source vocabulary for arbitrary-norm powered production cost. -/
noncomputable def normPowerCostSpec {D : ℕ} (ν : SourceNorm D) (β : ℝ) :
    Content D → ℝ :=
  normRpowCost ν β

/-- Governing finite market model from the source model section. -/
def globalMarketModelSpec {D N P : ℕ} [Nonempty (Fin N)]
    (users : Fin N → Content D) (ν : SourceNorm D) (β : ℝ)
    (μ : MixedContentStrategy D) : Prop :=
  2 ≤ P ∧ 1 ≤ β ∧
    (∀ i : Fin N, NonnegativeContent (users i)) ∧
    (∀ i : Fin N, NonzeroContent (users i)) ∧
    symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ

/-- Source quality-and-genre vocabulary, represented by its zero-safe genre set. -/
def qualityAndGenreModelSpec {D : ℕ} (ν : SourceNorm D)
    (μ : MixedContentStrategy D) : Set (Content D) :=
  {genre | ∃ p : Content D, p ∈ μ.support ∧ NonzeroContent p ∧
    genre = SourceNorm.normalizedContent ν p}

/-- Source regime vocabulary for one genre versus necessarily many genres. -/
def singleAndMultiGenreRegimesSpec {D N P : ℕ} (users : Fin N → Content D)
    (ν : SourceNorm D) (β : ℝ) : Prop :=
  (∃ (μ : MixedContentStrategy D) (genre : Content D),
    symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ ∧
      nonzeroSupportGenresSpec ν μ = ({genre} : Set (Content D))) ∨
  (∀ (μ : MixedContentStrategy D) (genre : Content D),
    symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ →
      nonzeroSupportGenresSpec ν μ ≠ ({genre} : Set (Content D)))

/-- The powered nonnegative unit-ball score image used by the product condition. -/
def poweredScoreGeometrySpec {D N : ℕ} (users : Fin N → Content D)
    (ν : SourceNorm D) (β : ℝ) : Set (Fin N → ℝ) :=
  {y : Fin N → ℝ | paper_powered_unit_image users
    (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y}

/-- The source beta-star threshold, including `⊤` when its exponent set is unbounded. -/
noncomputable def betaStarDefinitionSpec {D N : ℕ} (users : Fin N → Content D)
    (ν : SourceNorm D) : WithTop ℝ :=
  sSup ((fun β : ℝ => (β : WithTop ℝ)) ''
    {β : ℝ | 1 ≤ β ∧ SingleGenreProductSupCondition
      (poweredScoreGeometrySpec users ν β)})

/-- Equal-population, linearly independent two-user L2 market used in Section 4. -/
def twoPopulationModelSpec {D K P : ℕ} (users : Fin 2 → Content D)
    (β : ℝ) (μ : MixedContentStrategy D) : Prop :=
  0 < K ∧ 2 ≤ P ∧ 1 ≤ β ∧ LinearIndependent ℝ users ∧
    (∀ i : Fin 2, NonnegativeContent (users i)) ∧
    symmetricMixedNashModelSpec (P := P) (twoPopulationUsers K users)
      (normPowerCostSpec (SourceNorm.l2 D) β) μ

/--
Tie-aware score-space reparameterization.  The strict-score expression equals
the actual expected-winner payoff precisely under the displayed score-level
nullness hypothesis; retaining both clauses prevents a silent tie-breaking
convention from entering the source model.
-/
def reparameterizedEquilibriumModelSpec {D N P : ℕ}
    (users : Fin N → Content D) (μ : MixedContentStrategy D)
    (cost : Content D → ℝ) : Prop :=
  (∀ (i : Fin N) (z : ℝ), μ {q : Content D | score (users i) q = z} = 0) ∧
    ∀ (j : Fin P) (p : Content D),
      SourceMixedPurePayoff (ExpectedUsersWonAgainstSymmetricMixed users j) cost p μ =
        (∑ i : Fin N,
          (μ.real {q : Content D | score (users i) q < score (users i) p}) ^ (P - 1)) -
          cost p

/--
Common expected profit and the source's normalized-user alignment quantity
`Q`.  The latter is stated as the supremum form of the paper's max--min
display, so no unproved attainment is hidden in the vocabulary itself.
-/
noncomputable def equilibriumProfitModelSpec {D N P : ℕ} (users : Fin N → Content D)
    (ν : SourceNorm D) (cost : Content D → ℝ) (μ : MixedContentStrategy D)
    (profit Q : ℝ) : Prop :=
  symmetricMixedNashModelSpec (P := P) users cost μ ∧
    (∀ i : Fin N, NonzeroContent (users i)) ∧
    (∀ j : Fin P,
      (∫ p, SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j) cost p μ ∂μ) = profit) ∧
    Q = sSup {q : ℝ | ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
        ∀ i : Fin N,
          q ≤ score p (ν.normalizedContent (users i))}

/-- The source C1 objective for a two-genre infinite-producer candidate. -/
noncomputable def infiniteTwoGenreContentObjectiveSpec
    (cdf : ℝ → ℝ) (β θ : ℝ) (firstGenre secondGenre p : Content 2) : ℝ :=
  Real.sqrt
      (cdf (score canonicalTwoUserFirst p / score canonicalTwoUserFirst firstGenre) *
        cdf (score canonicalTwoUserFirst p / score canonicalTwoUserFirst secondGenre)) +
    Real.sqrt
      (cdf (score (canonicalTwoUserSecond θ) p /
          score (canonicalTwoUserSecond θ) firstGenre) *
        cdf (score (canonicalTwoUserSecond θ) p /
          score (canonicalTwoUserSecond θ) secondGenre)) -
    normPowerCostSpec (SourceNorm.l2 2) β p

/--
The corrected finite-genre infinite-producer objective.  The source display
uses the genre weight indexed by the user in the product exponent; the
approved corrected target uses the genre index, so that each conditional
quality law is weighted by its own genre probability.
-/
noncomputable def infiniteGenreContentObjectiveSpec {D N G : ℕ}
    (users : Fin N → Content D) (cost : Content D → ℝ)
    (genres : Fin G → Content D) (maximumQualityCdf : Fin G → ℝ → ℝ)
    (weights : Fin G → ℝ) (p : Content D) : ℝ :=
  (∑ i : Fin N,
    ∏ g : Fin G,
      (maximumQualityCdf g
        (score (users i) p / score (users i) (genres g))) ^ (weights g)) - cost p

/--
Corrected source definition of a finite-genre equilibrium in the
infinite-producer limit: normalized nonnegative genres, conditional maximum
quality laws, probability weights, and support-wise global best responses.
The object is deliberately general in the number of genres; the later
two-genre construction is an instantiated candidate, not the definition.
-/
def infiniteGenreDefinitionSpec {D N G : ℕ} (users : Fin N → Content D)
    (cost : Content D → ℝ) (genres : Fin G → Content D)
    (conditionalQuality : Fin G → Measure ℝ)
    (maximumQualityCdf : Fin G → ℝ → ℝ) (weights : Fin G → ℝ) : Prop :=
  (∀ g : Fin G,
    NonnegativeContent (genres g) ∧ (SourceNorm.l2 D).norm (genres g) = 1) ∧
  (∀ g : Fin G,
    IsProbabilityMeasure (conditionalQuality g) ∧
      (∀ q : ℝ,
        conditionalQuality g (Set.Iic q) = ENNReal.ofReal (maximumQualityCdf g q)) ∧
      (conditionalQuality g).support ⊆ Set.Ici 0) ∧
  (∀ g : Fin G, 0 ≤ weights g) ∧
  (∑ g : Fin G, weights g) = 1 ∧
  ∀ (g : Fin G) ⦃r : ℝ⦄, r ∈ (conditionalQuality g).support →
    scaleContent r (genres g) ∈ {p : Content D | NonnegativeContent p} ∧
      IsMaxOn
        (infiniteGenreContentObjectiveSpec users cost genres maximumQualityCdf weights)
        {p : Content D | NonnegativeContent p}
        (scaleContent r (genres g))

/--
Transparent source model for the corrected two-genre infinite-producer
construction: two unit nonnegative genres, a common conditional-quality law,
equal weights, and the C1 best-response property on the nonnegative cone.
-/
def correctedInfiniteTwoGenreContentEquilibriumSpec
    (cdf : ℝ → ℝ) (β θ : ℝ) : Prop :=
  ∃ (firstGenre secondGenre : Content 2) (conditionalQuality : Measure ℝ)
      (firstWeight secondWeight : ℝ),
    NonnegativeContent firstGenre ∧
    NonnegativeContent secondGenre ∧
    (SourceNorm.l2 2).norm firstGenre = 1 ∧
    (SourceNorm.l2 2).norm secondGenre = 1 ∧
    IsProbabilityMeasure conditionalQuality ∧
    (∀ q : ℝ, conditionalQuality (Set.Iic q) = ENNReal.ofReal (cdf q)) ∧
    conditionalQuality.support ⊆ Set.Ici 0 ∧
    0 ≤ firstWeight ∧ 0 ≤ secondWeight ∧
    firstWeight = 1 / 2 ∧ secondWeight = 1 / 2 ∧
    firstWeight + secondWeight = 1 ∧
    (∀ ⦃r : ℝ⦄, r ∈ conditionalQuality.support →
      scaleContent r firstGenre ∈ {p : Content 2 | NonnegativeContent p} ∧
        IsMaxOn
          (infiniteTwoGenreContentObjectiveSpec cdf β θ firstGenre secondGenre)
          {p : Content 2 | NonnegativeContent p}
          (scaleContent r firstGenre)) ∧
    ∀ ⦃r : ℝ⦄, r ∈ conditionalQuality.support →
      scaleContent r secondGenre ∈ {p : Content 2 | NonnegativeContent p} ∧
        IsMaxOn
          (infiniteTwoGenreContentObjectiveSpec cdf β θ firstGenre secondGenre)
          {p : Content 2 | NonnegativeContent p}
          (scaleContent r secondGenre)

/--
Corrected finite-genre infinite-producer model predicate, repeated at the
paper-facing boundary so its weights, conditional CDF, and support-wise global
optimality condition remain inspectable without following an implementation
alias.
-/
def infiniteProducerModelSpec (cdf : ℝ → ℝ) (β θ : ℝ) : Prop :=
  ∃ (firstGenre secondGenre : Content 2) (conditionalQuality : Measure ℝ)
      (firstWeight secondWeight : ℝ),
    NonnegativeContent firstGenre ∧
    NonnegativeContent secondGenre ∧
    (SourceNorm.l2 2).norm firstGenre = 1 ∧
    (SourceNorm.l2 2).norm secondGenre = 1 ∧
    IsProbabilityMeasure conditionalQuality ∧
    (∀ q : ℝ, conditionalQuality (Set.Iic q) = ENNReal.ofReal (cdf q)) ∧
    conditionalQuality.support ⊆ Set.Ici 0 ∧
    0 ≤ firstWeight ∧ 0 ≤ secondWeight ∧
    firstWeight = 1 / 2 ∧ secondWeight = 1 / 2 ∧
    firstWeight + secondWeight = 1 ∧
    (∀ ⦃r : ℝ⦄, r ∈ conditionalQuality.support →
      scaleContent r firstGenre ∈ {p : Content 2 | NonnegativeContent p} ∧
        IsMaxOn
          (infiniteTwoGenreContentObjectiveSpec cdf β θ firstGenre secondGenre)
          {p : Content 2 | NonnegativeContent p}
          (scaleContent r firstGenre)) ∧
    ∀ ⦃r : ℝ⦄, r ∈ conditionalQuality.support →
      scaleContent r secondGenre ∈ {p : Content 2 | NonnegativeContent p} ∧
        IsMaxOn
          (infiniteTwoGenreContentObjectiveSpec cdf β θ firstGenre secondGenre)
          {p : Content 2 | NonnegativeContent p}
          (scaleContent r secondGenre)

/--
Transparent finite-genre radial-law hypothesis in the upper phase-transition
branch.  This is the paper's finite mixture, including positivity, CDF
regularity, and its polar decomposition.
-/
structure finiteGenreConditionalNormLawSpec {G : ℕ}
    (μ : MixedContentStrategy 2) (angle : Fin G → ℝ) where
  weight : Fin G → ℝ
  radial : Fin G → Measure ℝ
  weight_pos : ∀ i, 0 < weight i
  weights_sum : (∑ i, weight i) = 1
  radial_probability : ∀ i, IsProbabilityMeasure (radial i)
  radial_support_nonnegative : ∀ i, (radial i).support ⊆ Set.Ici 0
  radial_has_positive_support : ∀ i, ∃ r ∈ (radial i).support, 0 < r
  radial_cdf_c1 : ∀ i, ContDiff ℝ 1
    (AppliedModelingLib.Probability.lowerCDFMass (radial i))
  decomposition : μ = ∑ i, ENNReal.ofReal (weight i) •
    Measure.map
      (fun r : ℝ => scaleContent r
        (content2 (Real.cos (angle i)) (Real.sin (angle i))))
      (radial i)

/-- Corrected Proposition `pure`: nonzero users rule out a pure equilibrium. -/
def propositionPureSpec : Prop :=
  ∀ {D N P : ℕ} [Nontrivial (Fin P)]
    {users : Fin N → Content D} {profile : Fin P → Content D}
    (ν : SourceNorm D) {β : ℝ},
    0 < β →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∃ i : Fin N, NonzeroContent (users i)) →
    SourceNormPerturbationContinuous ν →
    ¬ paper_pure_nash_equilibrium users (normRpowCost ν β) profile

/-- Corrected Proposition `existence` on compact continuous norm sublevels. -/
def propositionExistenceSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {β : ℝ},
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormCompactSublevels ν →
    Continuous ν.norm →
    SourceNormPerturbationContinuous ν →
    1 ≤ β →
    ∃ μ, symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ

/-- Corrected Proposition `atom`: a nondegenerate source equilibrium is atomless. -/
def propositionAtomSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {i0 : Fin N},
    symmetricMixedNashModelSpec (P := P) users cost μ →
    PerturbationCostContinuous cost →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    NonzeroContent (users i0) →
    paper_mixed_content_strategy_atomless μ

/-- Corrected Corollary `onepopulation`, including its exact radial CDF. -/
def corollaryOnePopulationSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {u genre : Content D},
    (ν : SourceNorm D) → 0 < β →
    NonnegativeContent u → NonnegativeContent genre → ν.norm genre = 1 →
    0 < paper_inferred_user_value u genre →
    (∀ d : Content D, NonnegativeContent d → ν.norm d = 1 →
      paper_inferred_user_value u d ≤ paper_inferred_user_value u genre) →
    Measurable ν.norm →
    symmetricMixedNashModelSpec (P := P) (fun _ : Fin N => u) (normPowerCostSpec ν β)
      (singleGenreContentLaw N P β genre) ∧
    (singleGenreContentLaw N P β genre).support ⊆
      {p : Content D | ∃ q ∈ Set.Icc (0 : ℝ) ((N : ℝ) ^ β⁻¹),
        p = scaleContent q genre} ∧
    ∀ z : ℝ, 0 ≤ z →
      Measure.map ν.norm (singleGenreContentLaw N P β genre) (Set.Iic z) =
        ENNReal.ofReal (min 1 (((z ^ β) / (N : ℝ)) ^ (((P : ℝ) - 1)⁻¹)))

/--
Corrected Example `1d`: the source's one-dimensional construction is the
one-user specialization of the homogeneous-population ray law.  The endpoint
checks the displayed equilibrium and its corrected radial CDF under the
explicit unit-genre and score-maximization hypotheses.  The archival
uniqueness assertion is deliberately not folded into this construction route;
it is recorded as a separate source clarification.
-/
def exampleOneDimensionalSetupSpec : Prop :=
  ∀ {P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {u genre : Content 1},
    (ν : SourceNorm 1) → 0 < β →
    NonnegativeContent u → NonnegativeContent genre → ν.norm genre = 1 →
    0 < paper_inferred_user_value u genre →
    (∀ d : Content 1, NonnegativeContent d → ν.norm d = 1 →
      paper_inferred_user_value u d ≤ paper_inferred_user_value u genre) →
    Measurable ν.norm →
    symmetricMixedNashModelSpec (P := P) (fun _ : Fin 1 => u)
      (normPowerCostSpec ν β) (singleGenreContentLaw 1 P β genre) ∧
    (singleGenreContentLaw 1 P β genre).support ⊆
      {p : Content 1 | ∃ q ∈ Set.Icc (0 : ℝ) (1 : ℝ),
        p = scaleContent q genre} ∧
    ∀ z : ℝ, 0 ≤ z →
      Measure.map ν.norm (singleGenreContentLaw 1 P β genre) (Set.Iic z) =
        ENNReal.ofReal (min 1 (((z ^ β) / (1 : ℝ)) ^ (((P : ℝ) - 1)⁻¹)))

/-- Corrected Theorem `singlegenre`: a zero-safe, nondegenerate iff. -/
def theoremSingleGenreSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} (ν : SourceNorm D) {β : ℝ},
    1 ≤ β →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormPerturbationContinuous ν →
    SourceNormCompactSublevels ν →
    Continuous ν.norm →
    ((∃ (μ : MixedContentStrategy D) (genre : Content D),
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ ∧
      nonzeroSupportGenresSpec ν μ = ({genre} : Set (Content D))) ↔
      SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y}) ∧
    (¬ SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y} →
      ∀ (μ : MixedContentStrategy D) (genre : Content D),
        symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ →
          nonzeroSupportGenresSpec ν μ ≠ ({genre} : Set (Content D))) ∧
    ∀ {β' : ℝ}, 0 < β' → β' ≤ β →
      SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y} →
        SingleGenreProductSupCondition
          {y : Fin N → ℝ | paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β' y}

/--
The attained, positive feasible-ray certificate used to repair the source
optimization-program displays.  It keeps the source's `Ball_m` domain
explicit and records the concrete ray-law equilibrium produced by an
attained optimization witness.  This is deliberately not an unqualified
extended-real infimum/supremum expression: the archival ratios are undefined
on zero score rows, and the archival `supinf` lemma needs an attainment
bridge.
-/
def optimizationProgramCertificate {D N P : ℕ}
    (users : Fin N → Content D) (ν : SourceNorm D) (β : ℝ) : Prop :=
  ∃ p : Content D,
    NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
    (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
    symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β)
      (singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p))

/--
Corrected informal Lemma `optimizationprogram`: on the compact positive-score
source domain, the source product condition is equivalent to an attained
positive feasible-ray certificate.  The checked certificate is the
well-defined operational replacement for the printed minimax equality.
-/
def lemmaOptimizationProgramSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} (ν : SourceNorm D) {β : ℝ},
    0 < β →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormCompactSublevels ν →
    ((∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β)
        (singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p))) ↔
      SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y})

/--
Corrected formal Lemma `optimizationprogramrestated`: the source's `Ball_m`
parameterization is exactly the positive feasible-ray certificate above.  It
therefore has the same compact-domain product-condition equivalence as the
informal display, while retaining a distinct source-facing route for the
appendix restatement.
-/
def lemmaOptimizationProgramRestatedSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} (ν : SourceNorm D) {β : ℝ},
    0 < β →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormCompactSublevels ν →
    ((∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β)
        (singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p))) ↔
      SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y})

/-- Corrected Corollary `2users`: the exact finite equal-population threshold. -/
def corollaryTwoUsersSpec : Prop :=
  ∀ {D K P : ℕ} [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin 2 → Content D} {β θ : ℝ},
    0 < K →
    (∀ i, NonnegativeContent (users i)) →
    NonzeroContent (users 0) → NonzeroContent (users 1) →
    paper_inferred_user_value (users 0) (users 1) /
        (AppliedModelingLib.FiniteDimensionalNorms.l2 (users 0) *
          AppliedModelingLib.FiniteDimensionalNorms.l2 (users 1)) = Real.cos θ →
    1 ≤ β → 0 < θ → θ ≤ Real.pi / 2 →
    ((∃ (μ : MixedContentStrategy D) (genre : Content D),
      symmetricMixedNashModelSpec (P := P) (twoPopulationUsers K users)
        (normPowerCostSpec (SourceNorm.l2 D) β) μ ∧
      nonzeroSupportGenresSpec (SourceNorm.l2 D) μ = ({genre} : Set (Content D))) ↔
      β ≤ twoUserPhaseThreshold θ)

/--
Source Proposition `Ptwo`: the displayed law is an equilibrium, its
standard-basis value law has the literal quarter-circle support, and it is the
quarter-circle parameterization of the stated angle-density measure.

The content space is represented as functions `Fin 2 → ℝ`; therefore the
geometric support is stated for the score/value map, which is the identity
coordinate representation in this standard-basis model.
-/
def propositionPTwoSpec : Prop :=
  ∀ {β : ℝ}, 2 ≤ β →
    symmetricMixedNashModelSpec (P := 2) pTwoStandardBasisUsers
      (normPowerCostSpec (SourceNorm.l2 2) β) (pTwoSourceContentMeasure β) ∧
    Measure.map pTwoStandardBasisValueMap (pTwoSourceContentMeasure β) =
      pTwoSourceCircleMeasure β ∧
    (pTwoSourceCircleMeasure β).support =
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧
        z.1 ^ 2 + z.2 ^ 2 = (2 / β) ^ (2 / β)} ∧
    pTwoSourceCircleMeasure β =
      Measure.map (fun θ : ℝ =>
        ((2 / β) ^ (1 / β) * Real.cos θ,
          (2 / β) ^ (1 / β) * Real.sin θ))
        ((volume : Measure ℝ).withDensity
          ((Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
            fun θ => ENNReal.ofReal (2 * Real.cos θ * Real.sin θ))) ∧
    ∀ z : ℝ, pTwoSourceCircleMeasure β {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal
        (if z < 0 then 0 else min ((2 / β) ^ (-(2 / β)) * z ^ 2) 1)

/--
Source Proposition `finiteP`: the displayed finite-producer law is an
equilibrium, with its literal coordinate-curve support and CDF.
-/
def propositionFinitePSpec : Prop :=
  ∀ {P : ℕ}, 2 ≤ P →
    symmetricMixedNashModelSpec (P := P) pTwoStandardBasisUsers
      (normPowerCostSpec (SourceNorm.l2 2) 2) (finitePSourceContentMeasure P) ∧
    Measure.map pTwoStandardBasisValueMap (finitePSourceContentMeasure P) =
      finitePSourceCurveMeasure P ∧
    (finitePSourceCurveMeasure P).support =
      {z : ℝ × ℝ | z.1 ∈ Set.Icc (0 : ℝ) 1 ∧
        z.2 = (1 - z.1 ^ (2 / ((P : ℝ) - 1))) ^ (((P : ℝ) - 1) / 2)} ∧
    ∀ z : ℝ, finitePSourceCurveMeasure P {point : ℝ × ℝ | point.1 ≤ z} =
      ENNReal.ofReal
        (if z < 0 then 0 else min 1 (z ^ (2 / ((P : ℝ) - 1))))

/-- Corrected Claim `necessarysuff`: uniform ties require score-level nullness. -/
def claimNecessarySufficientSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin P)]
    {users : Fin N → Content D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} [IsProbabilityMeasure μ],
    (∀ i : Fin N, Measurable (fun q : Content D => score (users i) q)) →
    (∀ (i : Fin N) (z : ℝ), μ {q : Content D | score (users i) q = z} = 0) →
    (symmetricMixedNashModelSpec (P := P) users cost μ ↔
      μ.support ⊆ {p : Content D | NonnegativeContent p} ∧
      ∀ (j : Fin P) (p : Content D), p ∈ μ.support → ∀ q : Content D,
        NonnegativeContent q →
          (∑ i : Fin N,
            (μ.real {r : Content D | score (users i) r < score (users i) q}) ^ (P - 1)) -
              cost q ≤
            (∑ i : Fin N,
              (μ.real {r : Content D | score (users i) r < score (users i) p}) ^ (P - 1)) -
              cost p)

/-- Corrected two-user phase transition: below-threshold uniqueness and above-threshold finite-genre exclusion. -/
def theoremPhaseTransitionSpec : Prop :=
  ∀ {P : ℕ} [Nonempty (Fin P)] {β θ : ℝ}
    {μ : MixedContentStrategy 2} [IsProbabilityMeasure μ],
    1 < P → 1 ≤ β → 0 < θ → θ ≤ Real.pi / 2 →
    SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (normPowerCostSpec (SourceNorm.l2 2) β) μ →
    (∀ i : Fin 2,
      (Measure.map (fun q => score
        (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ).AbsolutelyContinuous volume) →
    (∀ x ∈ (Measure.map (fun q => score canonicalTwoUserFirst q) μ).support,
      ContDiffAt ℝ 2
        (AppliedModelingLib.Probability.lowerCDFMass
          (Measure.map (fun q => score canonicalTwoUserFirst q) μ)) x) →
    (∀ x ∈ (Measure.map (fun q => score (canonicalTwoUserSecond θ) q) μ).support,
      ContDiffAt ℝ 2
        (AppliedModelingLib.Probability.lowerCDFMass
          (Measure.map (fun q => score (canonicalTwoUserSecond θ) q) μ)) x) →
    (β < twoUserPhaseThreshold θ →
      SourceNonzeroSupportGenres (SourceNorm.l2 2) μ =
        {(SourceNorm.l2 2).normalizedContent
          (canonicalTwoUserContentOfValues θ 1 1)}) ∧
    (twoUserPhaseThreshold θ < β →
      ∀ {G : ℕ}, Nonempty (Fin G) →
        ∀ (angle : Fin G → ℝ) (weight : Fin G → ℝ)
          (radial : Fin G → Measure ℝ),
          (∀ i, 0 < weight i) →
          (∑ i, weight i) = 1 →
          (∀ i, IsProbabilityMeasure (radial i)) →
          (∀ i, (radial i).support ⊆ Set.Ici 0) →
          (∀ i, ∃ r ∈ (radial i).support, 0 < r) →
          (∀ i, ContDiff ℝ 1
            (AppliedModelingLib.Probability.lowerCDFMass (radial i))) →
          μ = ∑ i, ENNReal.ofReal (weight i) •
            Measure.map
              (fun r : ℝ => scaleContent r
                (content2 (Real.cos (angle i)) (Real.sin (angle i))))
              (radial i) →
          Function.Injective angle →
          (∀ i : Fin G, angle i ∈ Set.Icc 0 (Real.pi / 2)) → False)

/--
Corrected Theorem `infinitegenreformal`: a coherent two-genre
infinite-producer equilibrium exists in the strictly acute, strictly
above-threshold regime.  Its conditional law is a probability law with
weights one half, rather than the inconsistent archival angle and weight data.
-/
def theoremInfiniteGenreSpec : Prop :=
  ∀ {β θ : ℝ},
    0 < θ → θ < Real.pi / 2 → twoUserPhaseThreshold θ < β →
    ∃ a C1 C2 A B phi : ℝ,
      infiniteProducerModelSpec
        (fun q : ℝ =>
          if q ≤ 0 then 0
          else if a ≤ q then 1
          else
            let k : ℕ := by
              classical
              exact if h : ∃ n : ℕ, a * C2 ^ n ≤ q then Nat.find h else 0
            if Even k then C2 ^ ((k : ℝ) * β)
            else C1 ^ (-2 : ℝ) * C2 ^ (-2 * ((k / 2 : ℕ) : ℝ) * β) *
              q ^ (2 * β)) β θ ∧
      phi ∈ Set.Icc 0 (θ / 2) ∧
      IsMaxOn (fun x : ℝ =>
        (Real.cos x) ^ β + (Real.cos (θ - x)) ^ β) (Set.Icc 0 (θ / 2)) phi ∧
      0 < a ∧ 0 < C2 ∧ C2 < 1 ∧
      C1 = a ^ β ∧ C1 = 1 + C2 ^ β ∧
      A = Real.cos phi ∧ B = Real.cos (θ - phi) ∧ C2 = B / A

/-- Corrected informal Theorem `infinitegenre`: the same coherent two-genre limit conclusion. -/
def theoremInfiniteGenreInformalSpec : Prop :=
  ∀ {β θ : ℝ},
    0 < θ → θ < Real.pi / 2 → twoUserPhaseThreshold θ < β →
    ∃ a C1 C2 A B phi : ℝ,
      infiniteProducerModelSpec
        (fun q : ℝ =>
          if q ≤ 0 then 0
          else if a ≤ q then 1
          else
            let k : ℕ := by
              classical
              exact if h : ∃ n : ℕ, a * C2 ^ n ≤ q then Nat.find h else 0
            if Even k then C2 ^ ((k : ℝ) * β)
            else C1 ^ (-2 : ℝ) * C2 ^ (-2 * ((k / 2 : ℕ) : ℝ) * β) *
              q ^ (2 * β)) β θ ∧
      phi ∈ Set.Icc 0 (θ / 2) ∧
      IsMaxOn (fun x : ℝ =>
        (Real.cos x) ^ β + (Real.cos (θ - x)) ^ β) (Set.Icc 0 (θ / 2)) phi ∧
      0 < a ∧ 0 < C2 ∧ C2 < 1 ∧
      C1 = a ^ β ∧ C1 = 1 + C2 ^ β ∧
      A = Real.cos phi ∧ B = Real.cos (θ - phi) ∧ C2 = B / A

/-- Corrected Lemma `cdf`: the ray law's source-norm pushforward has the radial CDF. -/
def lemmaCdfSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)] {β z : ℝ}
    (ν : SourceNorm D) {genre : Content D},
    Measurable ν.norm → ν.norm genre = 1 → 0 < β → 0 ≤ z →
    Measure.map ν.norm (singleGenreContentLaw N P β genre) (Set.Iic z) =
      ENNReal.ofReal (min 1 (((z ^ β) / (N : ℝ)) ^ (((P : ℝ) - 1)⁻¹)))

/--
Reusable fixed-ray form of Lemma `optsingledirection`: the canonical ray law
is Nash exactly when its source ratio condition holds.
-/
def singleRayNashRatioSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D),
    0 < β → ν.norm genre = 1 → NonnegativeContent genre →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre) →
    (symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β)
      (singleGenreContentLaw N P β genre) ↔
      ∀ y' : Fin N → ℝ,
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y' →
          (∑ i : Fin N,
            y' i / (paper_inferred_user_value (users i) genre) ^ β) ≤ (N : ℝ))

/--
Corrected Lemma `optsingledirection`: under the explicit finite-dimensional
regularity package used by the source CDF argument, an arbitrary singleton
nonzero-genre equilibrium in direction `genre` is the canonical ray law.  The
unit, nonnegative, and positive-score conditions spell out that `genre` lies
in the source's displayed positive unit-direction domain.
-/
def lemmaOptSingleDirectionSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D} {genre : Content D}
    (ν : SourceNorm D),
    0 < β → ν.norm genre = 1 → NonnegativeContent genre →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    (∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre) →
    SourceNormPerturbationContinuous ν →
    SourceNormCompactSublevels ν → Continuous ν.norm →
    ((∃ μ : MixedContentStrategy D,
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ ∧
        nonzeroSupportGenresSpec ν μ = ({genre} : Set (Content D))) ↔
      ∀ y' : Fin N → ℝ,
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y' →
          (∑ i : Fin N,
            y' i / (paper_inferred_user_value (users i) genre) ^ β) ≤ (N : ℝ))

/-- Corrected Corollary `singlegenrestructure`: positive-score log-welfare maximization. -/
def corollarySingleGenreStructureSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {genre : Content D} {β : ℝ},
    symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ →
    nonzeroSupportGenresSpec ν μ ⊆ ({genre} : Set (Content D)) →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormPerturbationContinuous ν → 0 < β →
    SourceNormCompactSublevels ν → Continuous ν.norm →
    IsMaximizerOn
      (fun z => z ∈ {y' : Fin N → ℝ |
        paper_powered_unit_image users
          (fun p => NonnegativeContent p ∧ ν.norm p = 1) β y'} ∧
        ∀ i, 0 < z i)
      (fun y => ∑ i : Fin N, Real.log (y i))
      (fun i => (paper_inferred_user_value (users i) genre) ^ β)

/--
Corrected Lemma `conditiongen`: a singleton nonzero-genre equilibrium exists
iff a positive feasible source-ball point satisfies the displayed ratio bound.
The compactness and continuity bridges make the source's optimization argument
and its zero-safe genre conclusion explicit.
-/
def lemmaConditionGenSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β : ℝ} {users : Fin N → Content D}
    (ν : SourceNorm D),
    0 < β →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormPerturbationContinuous ν →
    SourceNormCompactSublevels ν → Continuous ν.norm →
    ((∃ (μ : MixedContentStrategy D) (genre : Content D),
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ ∧
      nonzeroSupportGenresSpec ν μ = ({genre} : Set (Content D))) ↔
      ∃ p : Content D, NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
        (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
        (∀ y' : Fin N → ℝ,
          paper_powered_unit_image users
            (fun q => NonnegativeContent q ∧ ν.norm q ≤ 1) β y' →
            (∑ i : Fin N,
              y' i / (paper_inferred_user_value (users i) p) ^ β) ≤ (N : ℝ)))

/-- Corrected Corollary `betaone`: compact convex source norms admit the ray equilibrium. -/
def corollaryBetaOneSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} (ν : SourceNorm D),
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormCompactSublevels ν → SourceNormConvexSublevels ν →
    ∃ p : Content D, NonnegativeContent p ∧ ν.norm p ≤ 1 ∧
      (∀ i : Fin N, 0 < paper_inferred_user_value (users i) p) ∧
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν 1)
        (singleGenreContentLaw N P 1 (SourceNorm.normalizedContent ν p))

/-- Corrected Corollary `betap`: Lq cost has a singleton nonzero-genre equilibrium below q. -/
def corollaryBetaPSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {q β : ℝ} {users : Fin N → Content D} (hq : 1 ≤ q),
    0 < β → β ≤ q →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    ∃ (μ : MixedContentStrategy D) (genre : Content D),
      symmetricMixedNashModelSpec (P := P) users
        (normPowerCostSpec (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) β) μ ∧
      nonzeroSupportGenresSpec (SourceNorm.lp D (lt_of_lt_of_le zero_lt_one hq)) μ =
        ({genre} : Set (Content D))

/--
Corrected Corollary `beta`: above the explicit finite logarithmic threshold,
no compact regular symmetric equilibrium can have exactly one nonzero support
genre.  This is a fixed-exponent exclusion, not an assertion that the source
supremum `beta-star` is attained.
-/
def corollaryBetaSpec : Prop :=
  ∀ {D N P : ℕ} [Nontrivial (Fin N)] [Nonempty (Fin P)] [Nontrivial (Fin P)]
    {β Z : ℝ} {users : Fin N → Content D} (ν : SourceNorm D),
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceNormPerturbationContinuous ν → SourceNormCompactSublevels ν →
    Continuous ν.norm →
    (∀ p : Content D, NonnegativeContent p → ν.norm p ≤ 1 →
      (∑ i : Fin N, paper_inferred_user_value (users i) p) ≤ Z) →
    (∀ i : Fin N, ∃ p : Content D,
      NonnegativeContent p ∧ ν.norm p = 1 ∧
        paper_inferred_user_value (users i) p = 1) →
    1 < Z → Z < (N : ℝ) →
    Real.log (N : ℝ) / (Real.log (N : ℝ) - Real.log Z) < β →
    ¬ ∃ (μ : MixedContentStrategy D) (genre : Content D),
      symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ ∧
      nonzeroSupportGenresSpec ν μ = ({genre} : Set (Content D))

/--
Corrected Proposition `supportrestriction`: after the source's harmless
per-user score normalization, a nondegenerate normalized two-user L2 source
equilibrium cannot have a positive open content ball in its topological
support.  The normalization data are explicit because the printed proposition
states arbitrary user magnitudes.
-/
def propositionSupportRestrictionSpec : Prop :=
  ∀ {P : ℕ} [Nonempty (Fin P)] {α β θ ε : ℝ}
    {u v p0 : Content 2} {μ : Measure (Content 2)} [IsProbabilityMeasure μ],
    1 < P →
    (∀ i : Fin 2, NonnegativeContent (if i = 0 then u else v)) →
    0 < ε →
    (∀ p : Content 2,
      (p 0 - p0 0) ^ 2 + (p 1 - p0 1) ^ 2 < ε ^ 2 → p ∈ μ.support) →
    score u u = 1 → score v v = 1 → score u v = Real.cos θ →
    0 < α → 0 < β → 0 < Real.sin θ → 0 ≤ θ → θ ≤ Real.pi / 2 →
    (β ≠ 2 ∨ θ ≠ Real.pi / 2) →
    SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then u else v)
      (fun q => α * normPowerCostSpec (SourceNorm.l2 2) β q) μ →
    (∀ i : Fin 2,
      Measure.map (fun q : Content 2 => score (if i = 0 then u else v) q) μ ≪
        volume) →
    False

/--
Corrected Proposition `utility`: in the normalized Euclidean source game,
the geometric bound makes every support action's common equilibrium payoff
strictly positive.  This direct support-payoff formulation avoids silently
adding an expectation/integrability bridge to the source's profit notation.
-/
def propositionUtilitySpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {j : Fin P}
    {μ : MixedContentStrategy D} {p0 : Content D} {β Q : ℝ},
    symmetricMixedNashModelSpec (P := P) users
      (normPowerCostSpec (SourceNorm.l2 D) β) μ →
    p0 ∈ μ.support →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    SourceUnitDirectionQUpperBound
      (l2NormalizedUsers users) (SourceNorm.l2 D) Q →
    0 < β → 0 ≤ Q → Q < (1 / (N : ℝ)) ^ ((P : ℝ) / β) →
    0 < SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed users j)
      (normPowerCostSpec (SourceNorm.l2 D) β) p0 μ

/--
Corrected Lemma `nonzero`: in a singleton nonzero-genre equilibrium, that
genre scores every nonzero nonnegative user strictly positively.  The source's
parenthetical inference from linear-span membership is not used.
-/
def lemmaNonzeroSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D} {cost : Content D → ℝ}
    {μ : MixedContentStrategy D} {genre : Content D},
    symmetricMixedNashModelSpec (P := P) users cost μ →
    nonzeroSupportGenresSpec ν μ ⊆ ({genre} : Set (Content D)) →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    (∀ i : Fin N, NonzeroContent (users i)) →
    PerturbationCostContinuous cost →
    ∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre

/--
Corrected Proposition `zeroutilitysinglegenre`: every support action in the
regular singleton-nonzero-genre source equilibrium has zero actual payoff.
The displayed source profit conclusion additionally needs the usual
integrability bridge from support-action payoff to expected profit.
-/
def propositionZeroUtilitySingleGenreSpec : Prop :=
  ∀ {D N P : ℕ} [Nonempty (Fin N)] [Nontrivial (Fin P)]
    {users : Fin N → Content D} {ν : SourceNorm D}
    {μ : MixedContentStrategy D} {j : Fin P} {p genre : Content D} {β : ℝ},
    symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ →
    MeasureTheory.NoAtoms μ →
    nonzeroSupportGenresSpec ν μ ⊆ ({genre} : Set (Content D)) →
    (∀ i : Fin N, 0 < paper_inferred_user_value (users i) genre) →
    Measurable ν.norm →
    (∀ i : Fin N, NonnegativeContent (users i)) →
    0 < β → SourceNormCompactSublevels ν → Continuous ν.norm →
    p ∈ μ.support →
    SourceMixedPurePayoff (ExpectedUsersWonAgainstSymmetricMixed users j)
      (normPowerCostSpec ν β) p μ = 0

/--
Corrected Lemma `inducedcost`: in the canonical two-user cone, the actual
nonnegative-fibre minimum equals the displayed Gram quadratic.  This is not
the source's false arbitrary-dimensional equality for every score fibre.
-/
def lemmaInducedCostSpec : Prop :=
  ∀ {θ z1 z2 : ℝ}, 0 < Real.sin θ →
    NonnegativeContent (canonicalTwoUserContentOfValues θ z1 z2) →
    sInf {t : ℝ | ∃ p : Content 2,
      NonnegativeContent p ∧ score canonicalTwoUserFirst p = z1 ∧
        score (canonicalTwoUserSecond θ) p = z2 ∧ t = score p p} =
      (z1 ^ 2 + z2 ^ 2 - 2 * z1 * z2 * Real.cos θ) / (Real.sin θ) ^ 2

/--
Corrected Lemma `FOC`: away from the singular power base (or at the stated
regular exponent), the two canonical partial derivatives have the displayed
formula.  Identifying these derivatives with marginal CDF densities remains a
separate equilibrium regularity step.
-/
def lemmaFocSpec : Prop :=
  ∀ {α β θ z1 z2 : ℝ},
    (twoUserInducedCostNumerator θ z1 z2 ≠ 0 ∨ 1 ≤ β / 2) →
    HasDerivAt (fun x : ℝ => paper_two_user_induced_cost α β θ x z2)
      (β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
          (z1 - z2 * Real.cos θ)) z1 ∧
    HasDerivAt (fun y : ℝ => paper_two_user_induced_cost α β θ z1 y)
      (β * α * (Real.sin θ) ^ (-β) *
        (twoUserInducedCostNumerator θ z1 z2) ^ (β / 2 - 1) *
          (z2 - z1 * Real.cos θ)) z2

/--
Corrected Lemma `secondderiv`: at a nonsingular positive-radius canonical
point, the mixed partial is the stated nonzero scalar factor times the source
bracket.  This explicit equality is the valid form of the source's sign
comparison.
-/
def lemmaSecondDerivativeSpec : Prop :=
  ∀ {α β θ φ r : ℝ}, β ≠ 0 → 0 < r ^ 2 * (Real.sin θ) ^ 2 →
    paper_two_user_induced_cost_cross_partial α β θ
      (r * Real.cos φ) (r * Real.cos (θ - φ)) =
      β * α * (Real.sin θ) ^ (-β) *
        ((r ^ 2 * (Real.sin θ) ^ 2) ^ (β / 2 - 1) *
          ((β / 2) * paper_two_user_second_deriv_sign_bracket β θ φ))

/--
Corrected Lemma `regionscolor`: a local graph-SOC and its two differentiated
FOC identities imply the source slope/bracket inequality.  The graph and
regularity hypotheses are explicit rather than inferred from C1--C3.
-/
def lemmaRegionsColorSpec : Prop :=
  ∀ {α β θ φ r slope c11 c22 h1prime h2prime : ℝ},
    0 < α → 0 < β → 0 < Real.sin θ →
    0 < r ^ 2 * (Real.sin θ) ^ 2 →
    paper_negative_semidefinite_quadratic2
      (h1prime - c11)
      (-(paper_two_user_induced_cost_cross_partial α β θ
        (r * Real.cos φ) (r * Real.cos (θ - φ))))
      (h2prime - c22) →
    h1prime = c11 + slope * paper_two_user_induced_cost_cross_partial α β θ
      (r * Real.cos φ) (r * Real.cos (θ - φ)) →
    h2prime = c22 + slope⁻¹ * paper_two_user_induced_cost_cross_partial α β θ
      (r * Real.cos φ) (r * Real.cos (θ - φ)) →
    slope * paper_two_user_second_deriv_sign_bracket β θ φ ≤ 0

/--
Corrected Proposition `uniqueness`: the lower branch of the two-user phase
transition, with the score-law regularity needed by the source proof made
explicit.
-/
def propositionUniquenessSpec : Prop :=
  ∀ {P : ℕ} [Nonempty (Fin P)] {β θ : ℝ}
    {μ : MixedContentStrategy 2} [IsProbabilityMeasure μ],
    1 < P → 1 ≤ β → 0 < θ → θ ≤ Real.pi / 2 →
    SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (normPowerCostSpec (SourceNorm.l2 2) β) μ →
    (∀ i : Fin 2,
      (Measure.map (fun q => score
        (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ).AbsolutelyContinuous volume) →
    (∀ x ∈ (Measure.map (fun q => score canonicalTwoUserFirst q) μ).support,
      ContDiffAt ℝ 2
        (AppliedModelingLib.Probability.lowerCDFMass
          (Measure.map (fun q => score canonicalTwoUserFirst q) μ)) x) →
    (∀ x ∈ (Measure.map (fun q => score (canonicalTwoUserSecond θ) q) μ).support,
      ContDiffAt ℝ 2
        (AppliedModelingLib.Probability.lowerCDFMass
          (Measure.map (fun q => score (canonicalTwoUserSecond θ) q) μ)) x) →
    β < twoUserPhaseThreshold θ →
    SourceNonzeroSupportGenres (SourceNorm.l2 2) μ =
      {(SourceNorm.l2 2).normalizedContent
        (canonicalTwoUserContentOfValues θ 1 1)}

/--
Corrected Proposition `finitegenre`: the upper branch of the two-user phase
transition, with the finite conditional radial-law representation explicit.
-/
def propositionFiniteGenreSpec : Prop :=
  ∀ {P : ℕ} [Nonempty (Fin P)] {β θ : ℝ}
    {μ : MixedContentStrategy 2} [IsProbabilityMeasure μ],
    1 < P → 1 ≤ β → 0 < θ → θ ≤ Real.pi / 2 →
    SourceSymmetricMixedNash (P := P)
      (fun i : Fin 2 => if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ)
      (normPowerCostSpec (SourceNorm.l2 2) β) μ →
    (∀ i : Fin 2,
      (Measure.map (fun q => score
        (if i = 0 then canonicalTwoUserFirst else canonicalTwoUserSecond θ) q) μ).AbsolutelyContinuous volume) →
    (∀ x ∈ (Measure.map (fun q => score canonicalTwoUserFirst q) μ).support,
      ContDiffAt ℝ 2
        (AppliedModelingLib.Probability.lowerCDFMass
          (Measure.map (fun q => score canonicalTwoUserFirst q) μ)) x) →
    (∀ x ∈ (Measure.map (fun q => score (canonicalTwoUserSecond θ) q) μ).support,
      ContDiffAt ℝ 2
        (AppliedModelingLib.Probability.lowerCDFMass
          (Measure.map (fun q => score (canonicalTwoUserSecond θ) q) μ)) x) →
    twoUserPhaseThreshold θ < β →
    ∀ {G : ℕ}, Nonempty (Fin G) →
      ∀ (angle : Fin G → ℝ) (law : finiteGenreConditionalNormLawSpec μ angle),
        Function.Injective angle →
        (∀ i : Fin G, angle i ∈ Set.Icc 0 (Real.pi / 2)) → False

/--
Corrected Lemma `supinf`: an attained coordinate-product maximum in a
positive feasible row set attains the corresponding ratio minimum, at the
source value N.  The archival arbitrary-set formula is not valid without an
attainment or compactness bridge.
-/
def lemmaSupInfSpec : Prop :=
  ∀ {N : ℕ} [Nonempty (Fin N)] {R : Set (Fin N → ℝ)} {yStar : Fin N → ℝ},
    IsCoordinateProductMaximizer R yStar →
    (∀ z ∈ R, ∀ i, 0 < z i) →
    IsMinimizerOn (fun y => y ∈ R) (fun y => paper_ratio_objective y yStar)
      yStar ∧ paper_ratio_objective yStar yStar = (N : ℝ)

/--
Claim `equivalence`: equal two-population replication rescales cost by one
over `K`; the two-user reduction uses L2-normalized nonzero user vectors, as
in the source statement.
-/
def claimEquivalenceSpec : Prop :=
  ∀ {D K P : ℕ} (users : Fin 2 → Content D) {cost : Content D → ℝ}
    {μ : MixedContentStrategy D},
    0 < K →
    (∀ i : Fin 2, NonzeroContent (users i)) →
    (symmetricMixedNashModelSpec (P := P) (twoPopulationUsers K users) cost μ ↔
      symmetricMixedNashModelSpec (P := P) (l2NormalizedUsers users)
        (fun q => (2 : ℝ) / ((2 * K : ℕ) : ℝ) * cost q) μ)

/-- Corollary `2usersprofit`: the P=2 quarter-circle equilibrium payoff. -/
def corollaryTwoUsersProfitSpec : Prop :=
  ∀ {β : ℝ}, 2 ≤ β →
    symmetricMixedNashModelSpec (P := 2) pTwoStandardBasisUsers
      (normPowerCostSpec (SourceNorm.l2 2) β) (pTwoSourceContentMeasure β) ∧
    (∫ p, SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed pTwoStandardBasisUsers (0 : Fin 2))
      (normPowerCostSpec (SourceNorm.l2 2) β) p
      (pTwoSourceContentMeasure β) ∂pTwoSourceContentMeasure β) =
      1 - 2 / β

/-- Lemma `standardbasismax`: every displayed-radius point globally maximizes the source objective. -/
def lemmaStandardBasisMaxSpec : Prop :=
  ∀ {β z1 z2 w1 w2 : ℝ}, 2 ≤ β →
    0 ≤ z1 → 0 ≤ z2 → 0 ≤ w1 → 0 ≤ w2 →
    z1 ^ 2 + z2 ^ 2 = (2 / β) ^ (2 / β) →
    (min ((2 / β) ^ (-(2 / β)) * w1 ^ 2) 1 +
        min ((2 / β) ^ (-(2 / β)) * w2 ^ 2) 1) -
        (w1 ^ 2 + w2 ^ 2) ^ (β / 2) ≤
      (min ((2 / β) ^ (-(2 / β)) * z1 ^ 2) 1 +
        min ((2 / β) ^ (-(2 / β)) * z2 ^ 2) 1) -
        (z1 ^ 2 + z2 ^ 2) ^ (β / 2)

end JGS23SupplySideRecommenderSystems

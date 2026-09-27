import GolzHaghtalabYang2025Distortion.MainTheorems
import GolzHaghtalabYang2025Distortion.Assumptions
import GolzHaghtalabYang2025Distortion.Theorem2FiniteSample
import GolzHaghtalabYang2025Distortion.Theorem2UserBatch
import GolzHaghtalabYang2025Distortion.Lemma10FiniteSample
import GolzHaghtalabYang2025Distortion.Lemma11FiniteSample
import GolzHaghtalabYang2025Distortion.Theorem2Quantitative
import GolzHaghtalabYang2025Distortion.Theorem2Expected
import GolzHaghtalabYang2025Distortion.Theorem5FiniteSample
import GolzHaghtalabYang2025Distortion.Theorem6
import GolzHaghtalabYang2025Distortion.Theorem7FiniteSample

/-!
# Paper interface: Distortion of AI Alignment

**Authoritative source.** Gölz, Haghtalab, and Yang, NeurIPS 2025 published
conference PDF, Lemma 1 and Theorem 2 in §3 with their proofs in Appendices C
and E.1. The SHA-256
pinned source and its one-time transcript are recorded in
`docs/AML_001_FIRST_WAVE_SOURCE_PIN_LEDGER.md`; the arXiv record is a
discovery cross-check rather than the source authority.

This interface contains finite, unit-interval specializations of Lemma 1 and
the population-limit Borda conclusion of Theorem 2, together with its
deterministic finite-score bridge. It additionally exposes the literal
fixed-`d` iid-user selection bridge: independently sampled pair labels within
each user and arbitrarily correlated response-table entries yield asymptotic
selection of every strict population Borda winner. Its source-rate finite
endpoint uses the literal latent response-table and label product law, with
the Appendix-D minimum-mass condition and explicit conservative constants.
It also exposes Appendix D's exact fixed-pair
label-count second moment, but not its response-dependent Bernstein rate. It
also exposes the full
finite `d = 1` source construction used for Theorem 3: exact observational
indistinguishability, its infinite pigeonhole subsequence, its welfare-optimal
hidden alternative on the source parameter range, and Eq. (11)'s ratio. It
also represents the source's `m → ∞`, `ε = 1 / m` `d = 1` construction in its
large-`m` tolerance form. The `d ≥ 2` Condorcet-loser branch is represented by
the source-facing theorem
`theorem3_d2_asymptotic_lower_bound_of_sourceReportMarginals` reexported from
`MainTheorems`; its report-coordinate marginal assumption is the precise
formal source model for arbitrary within-user correlation. Appendix E.2's
Theorem 12 is represented with its literal three-type utilities, all-`m`
candidate splitting, and finite normalized-count Borda selection under the
source's one-comparison-per-user experiment. As in the source theorem, this
endpoint is asymptotic rather than a claimed explicit finite-sample rate.
Theorem 7 is represented at the population limit over the source finite KL
ball; the finite-sample term is outside this theory-only interface.
Corollary 8 is represented for finite real regularization weights through the
source regularized-to-constrained argument. Propositions 13 and 14 additionally
record their source context-free converses with explicit extended-weight
zero-radius boundaries. Appendix F.2's Theorem 6 now also
has its full literal population endpoint: an attained population MLE, its
deduced common type-`c` normalization, and two attained finite-KL policy
maxima imply the source welfare-ratio lower bound with the corrected welfare
gap threshold. Literal finite report counts now have an attained logistic
MLE with probability tending to one, and the literal raw-likelihood MLE-order
failure probability tends to zero.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Probability
open scoped Topology

/--
Finite source-facing Lemma 1.  The chord coefficient is exactly
`ℓ_β = (σ(β) - 1 / 2) / β`, represented by `sigmoidChordSlope`.
-/
def lemma1_population_bradleyTerry_linearization_finiteSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
      ∀ first second : Alternative,
        btScale *
              (sigmoidChordSlope btScale * populationAverageUtility population utility first -
                (1 : ℝ) / 4 * populationAverageUtility population utility second) ≤
            (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
              first second - (1 : ℝ) / 2 ∧
          (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
              first second - (1 : ℝ) / 2 ≤
            btScale *
              ((1 : ℝ) / 4 * populationAverageUtility population utility first -
                sigmoidChordSlope btScale * populationAverageUtility population utility second)

/--
Finite population-limit target for source Theorem 2. `winner` is any maximizer
of the limiting Borda score under the source's explicit sampling PMF. The
source's finite-sample convergence term is not part of this interface.
-/
def theorem2_borda_population_limit_finiteSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative)
      {btScale : ℝ}, 0 < btScale → ∀ (winner : Alternative),
        (∀ alternative,
          pairwiseBordaScore.{0, 0} sampling
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) alternative ≤
            pairwiseBordaScore.{0, 0} sampling
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) winner) →
          ∀ alternative,
            (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
                populationAverageUtility population utility alternative ≤
              populationAverageUtility population utility winner

/--
Finite-score bridge for source Theorem 2.  This isolates the deterministic
consequence of a uniform empirical-Borda error; source Lemma 11 is responsible
for establishing that error under the literal multi-comparison user model.
-/
def theorem2_borda_finiteScore_finiteSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative)
      {btScale : ℝ}, 0 < btScale → ∀
        (empiricalScore : Alternative → ℝ) (winner : Alternative) (scoreError : ℝ),
        (∀ alternative, empiricalScore alternative ≤ empiricalScore winner) →
        (∀ alternative,
          |empiricalScore alternative -
            pairwiseBordaScore.{0, 0} sampling
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) alternative| ≤
            scoreError) →
        ∀ alternative,
          (sigmoidChordSlope btScale) ^ 2 * populationAverageUtility population utility alternative ≤
            ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
              ((1 : ℝ) / 4) * (2 * scoreError) / btScale

/--
Literal fixed-`d` user-batch selection bridge for source Theorem 2. A user
draws one response table and independently sampled ordered-pair labels; only
the response-table pairwise marginals are calibrated. Thus this proposition
does not replace within-user outcome correlation with independent comparisons.
It establishes asymptotic strict-winner selection, not Appendix D's explicit
finite-sample rate.
-/
def theorem2_borda_userBatch_strictSelection_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (comparisonsPerUser : ℕ),
    0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ (winner : Alternative),
      (∀ alternative, 0 < (sampling alternative).toReal) →
      (∀ ordinary, ordinary ≠ winner →
        pairwiseBordaScore sampling preference ordinary <
          pairwiseBordaScore sampling preference winner) →
      Filter.Tendsto
        (fun users => pmfProb (theorem12IidBordaReportBatchLaw
          (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
        (fun sample => theorem12IidEmpiricalBordaFailure theorem2UserBatchBordaWins
            theorem2UserBatchBordaIncidences winner sample))
        Filter.atTop (𝓝 0)

/--
Finite literal-user Theorem 2 endpoint.  It bounds the event that an
empirical normalized-Borda maximizer violates the source welfare inequality;
the explicit tail is the checked range-based Appendix D Borda concentration.
-/
def theorem2_borda_userBatch_welfare_finiteSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative) {btScale : ℝ},
      0 < btScale → ∀ (responseLaw : PMF (theorem2UserResponseTable Alternative)),
      theorem2UserResponseCalibrated responseLaw
        (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) →
      ∀ (users comparisonsPerUser : ℕ), 0 < users → 0 < comparisonsPerUser →
      ∀ (minimumMass cutoff : ℝ), 0 < minimumMass →
      (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
      0 ≤ cutoff → cutoff ≤
        (users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass →
      pmfProb (theorem12IidBordaReportBatchLaw
        (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
        (fun sample => ∃ winner : Alternative,
          (∀ alternative,
            theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample ≤
            theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              winner sample) ∧
          ∃ alternative,
            ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
                ((1 : ℝ) / 4) *
                  (2 * (2 * cutoff /
                    ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass))) / btScale <
              (sigmoidChordSlope btScale) ^ 2 *
                populationAverageUtility population utility alternative) ≤
        ∑ _alternative : Alternative,
          4 * Real.exp (-cutoff ^ 2 /
            (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
              (2 * comparisonsPerUser : ℝ) * cutoff)))

/--
Source-rate finite Theorem 2 endpoint.  The `sample` is the literal source
data: one response table and `d` iid pair labels for every iid user.  The
Appendix-D minimum-mass condition yields a uniform normalized-Borda envelope
with explicit constants and the source's `log (8m² / δ)` union allocation.
-/
def theorem2_borda_userBatch_welfare_sourceRate_finiteSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative) {btScale : ℝ},
      0 < btScale → ∀ (responseLaw : PMF (theorem2UserResponseTable Alternative)),
      theorem2UserResponseCalibrated responseLaw
        (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) →
      ∀ (users comparisonsPerUser : ℕ), 0 < users → 0 < comparisonsPerUser →
      ∀ (minimumMass delta : ℝ), 0 < minimumMass →
      (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
      0 < delta → delta ≤ 1 →
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) ^ 2 / delta)
          let scoreError :=
            20 * Real.sqrt ((users : ℝ) * logLevel /
              min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
              8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
                ((users : ℝ) * minimumMass)
          ∃ winner : Alternative,
            (∀ alternative,
              theorem11IidUserLatentBordaScore alternative sample ≤
                theorem11IidUserLatentBordaScore winner sample) ∧
            ∃ alternative,
              ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
                  ((1 : ℝ) / 4) * (2 * scoreError) / btScale <
                (sigmoidChordSlope btScale) ^ 2 *
                  populationAverageUtility population utility alternative) ≤ delta

/--
Expected-welfare form of the finite source-rate Theorem 2 route.  It applies
to every deterministic rule selecting an empirical normalized-Borda maximizer
for each literal response-table/label sample; `benchmark` may in particular be
a population-welfare maximizer.
-/
def theorem2_borda_userBatch_expectedWelfare_sourceRate_finiteSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative) {btScale : ℝ},
      0 < btScale → ∀ (responseLaw : PMF (theorem2UserResponseTable Alternative)),
      theorem2UserResponseCalibrated responseLaw
        (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) →
      ∀ (users comparisonsPerUser : ℕ), 0 < users → 0 < comparisonsPerUser →
      ∀ (minimumMass delta : ℝ), 0 < minimumMass →
      (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
      0 < delta → delta ≤ 1 →
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta →
      ∀ (winner : (Fin users →
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))) → Alternative),
      (∀ sample alternative,
        theorem11IidUserLatentBordaScore alternative sample ≤
          theorem11IidUserLatentBordaScore (winner sample) sample) →
      ∀ benchmark : Alternative,
      (1 - delta) *
        ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
            populationAverageUtility population utility benchmark -
          2 * theorem2SourceRate (Fintype.card Alternative) users comparisonsPerUser
            minimumMass delta / (btScale * ((1 : ℝ) / 4))) ≤
        pmfExp
          (pmfProduct (Fin users)
            (theorem2UserResponseTable Alternative ×
              (Fin comparisonsPerUser → Alternative × Alternative))
            (pmfProd responseLaw
              (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                (theorem2UserPairLabelLaw sampling))))
          (fun sample => populationAverageUtility population utility (winner sample))

/--
The fixed-pair label-count component of Appendix D, Lemma 10.  It is the exact
second moment of the `d` iid ordered-pair labels; response-table outcomes and
the later concentration ratio are deliberately not part of this statement.
-/
def lemma10_fixedPairLabelCountSecondMoment_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative), first ≠ second →
      let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
      pmfExp
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels => (theorem10UserUnorderedPairCount first second labels) ^ 2) =
        (comparisonsPerUser : ℝ) * q +
          (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2

/-- Appendix D's calibrated fixed-pair centered-statistic variance proxy. -/
def lemma10_centeredPairWinVariance_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit.{1} Alternative)
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative), first ≠ second →
      theorem2UserResponseCalibrated responseLaw preference →
      pmfVariance
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling)))
        (fun source => theorem10UserCenteredPairWin first second
          (preference.prob PUnit.unit first second) source.1 source.2) ≤
        (comparisonsPerUser : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) ^ 2

/--
Appendix D's fixed-pair Chernoff denominator step for the literal iid label
product. This is the unspecialized direct lower-tail exponential inequality.
-/
def lemma10_fixedPairLabelCountLowerTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative), first ≠ second → ∀ (cutoff t : ℝ), 0 ≤ t →
      pmfProb
        (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels =>
          (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤ cutoff) ≤
      Real.exp
          (t * cutoff +
            (users * comparisonsPerUser : ℝ) *
              ((Real.exp (-t) - 1) *
                (2 * (sampling first).toReal * (sampling second).toReal)))

/--
The source's `ndq / 2` denominator event has its displayed `exp (-ndq / 8)`
failure bound under the literal iid ordered-pair label model.
-/
def lemma10_fixedPairLabelCountHalfMean_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative), first ≠ second →
      let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
      pmfProb
        (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels =>
          (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤
            ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) ≤
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8)

/--
Appendix D's minimum-mass algebra for the fixed-pair Bernstein radius.  This
is the source rate dependence with explicit conservative constants, before
the all-pairs union and the paper's big-O notation.  `minimumMass` need only
lower-bound the two displayed alternatives, so a global minimum mass is an
immediate specialization.
-/
def lemma10_fixedPairConfidenceRadiusMinMassEnvelope_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (minimumMass logLevel : ℝ),
    0 < users → 0 < comparisonsPerUser → 0 < minimumMass →
    minimumMass ≤ (sampling first).toReal →
    minimumMass ≤ (sampling second).toReal →
    0 ≤ logLevel →
    theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser first second logLevel /
        ((((users * comparisonsPerUser : ℕ) : ℝ) *
          theorem10FixedPairIncidenceProbability sampling first second) / 2) ≤
      8 * Real.sqrt (logLevel /
        ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
        16 * logLevel / ((users : ℝ) * minimumMass ^ 2)

/--
Appendix D's centered fixed-pair numerator tail under the literal iid-user
model. The source variance proxy is retained and no independence is imposed
between different responses in an individual user's table.
-/
def lemma10_iidUserCenteredPairWinUpperTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit.{1} Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative), first ≠ second → ∀ (cutoff : ℝ), 0 ≤ cutoff →
      (0 <
        (users : ℝ) *
          ((comparisonsPerUser : ℝ) *
            (2 * (sampling first).toReal * (sampling second).toReal) +
          (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
            (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
          (comparisonsPerUser : ℝ) * cutoff) →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => cutoff ≤ ∑ index,
          theorem10UserCenteredPairWin first second
            (preference.prob PUnit.unit first second) (sample index).1 (sample index).2) ≤
        Real.exp
          (-cutoff ^ 2 /
            (4 * ((users : ℝ) *
              ((comparisonsPerUser : ℝ) *
                (2 * (sampling first).toReal * (sampling second).toReal) +
              (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
                (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
              (comparisonsPerUser : ℝ) * cutoff)))

/--
Appendix D's complete fixed-pair count-ratio conclusion.  Both concentration
events live on the literal iid user-batch source law; the conclusion is an
explicit exponential bound before the paper's all-pairs union and big-O rate
simplification.
-/
def lemma10_iidUserEmpiricalWinRateTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit.{1} Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative), first ≠ second → ∀ (cutoff : ℝ), 0 ≤ cutoff →
      (0 <
        (users : ℝ) *
          ((comparisonsPerUser : ℝ) *
            (2 * (sampling first).toReal * (sampling second).toReal) +
          (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
            (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
          (comparisonsPerUser : ℝ) * cutoff) →
      (0 < ((users * comparisonsPerUser : ℕ) : ℝ) *
        (2 * (sampling first).toReal * (sampling second).toReal) / 2) →
      let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
      let varianceProxy : ℝ :=
        (comparisonsPerUser : ℝ) * q +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2
      let denominator : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => cutoff / denominator <
          |theorem10IidUserEmpiricalWinRate first second sample -
            preference.prob PUnit.unit first second|) ≤
        2 * Real.exp (-cutoff ^ 2 /
          (4 * ((users : ℝ) * varianceProxy + (comparisonsPerUser : ℝ) * cutoff))) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8)

/--
Appendix D's exact all-distinct-pairs union before the source's `μ_min`
algebraic simplification.  Keeping this sum explicit makes every pairwise
tail and its literal iid-user probability space visible.
-/
def lemma10_iidUserEmpiricalWinRateUniformOffDiag_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit.{1} Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    (∀ alternative, 0 < (sampling alternative).toReal) →
    ∀ (epsilon : ℝ), 0 ≤ epsilon →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) ≤
        ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          theorem10FixedPairRateTailBound sampling users comparisonsPerUser
            pair.1 pair.2 epsilon

/--
All-pairs source form of Lemma 10's exact finite union.  The empirical
diagonal convention is `1 / 2`, matching preference complementarity, so only
distinct pairs contribute to the displayed tail sum.
-/
def lemma10_iidUserPaperWinRateUniform_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit.{1} Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    (∀ alternative, 0 < (sampling alternative).toReal) →
    ∀ (epsilon : ℝ), 0 ≤ epsilon →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample : Fin users →
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative)) =>
          ∃ pair : Alternative × Alternative,
            epsilon < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
              preference.prob PUnit.unit pair.1 pair.2|) ≤
        ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          theorem10FixedPairRateTailBound sampling users comparisonsPerUser
            pair.1 pair.2 epsilon

/--
Source-sharp Appendix-D numerator tail before normalized-Borda division.  It
retains the literal response-table user model and exposes the source rate
`√(L/(n min {1,d μ_min²})) + mL/(n μ(x))` after the eventual normalization.
-/
def lemma11_iidUserSharpCenteredBordaMinMassTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit.{1} Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (minimumMass logLevel : ℝ),
    0 < users → 0 < comparisonsPerUser → 0 < minimumMass →
    (∀ opponent, minimumMass ≤ (sampling opponent).toReal) → 0 ≤ logLevel →
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
            Real.sqrt ((users : ℝ) * logLevel /
              min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
          8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel)

/--
Source-sharp finite normalized-Borda tail for Appendix D, Lemma 11.  It keeps
the raw Borda numerator's pairwise variance calculation and the denominator's
exact `2nd` endpoint-label law separate through the final ratio step.
-/
def lemma11_iidUserSharpNormalizedBordaMinMassTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ (alternative : Alternative) (minimumMass logLevel incidenceCutoff : ℝ),
      0 < minimumMass →
      (∀ opponent, minimumMass ≤ (sampling opponent).toReal) →
      0 ≤ logLevel → 0 ≤ incidenceCutoff →
      0 < (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal + incidenceCutoff →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          2 *
              (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                  Real.sqrt ((users : ℝ) * logLevel /
                    min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
                8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
                incidenceCutoff) /
              ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
                (sampling alternative).toReal) <
            |theorem11IidUserLatentBordaScore alternative sample -
              pairwiseBordaScore sampling preference alternative|) ≤
        2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
          2 * Real.exp (-incidenceCutoff ^ 2 /
            (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
              (sampling alternative).toReal + incidenceCutoff))) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
            (sampling alternative).toReal / 4)

/--
Closed-form Appendix-D confidence consequence of the source-sharp Lemma 11
tail.  It states explicit constants for the source's final big-O rate while
retaining its printed minimum-mass denominator condition.
-/
def lemma11_iidUserSharpNormalizedBordaSourceRateConfidence_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ (alternative : Alternative) (minimumMass delta : ℝ),
      0 < minimumMass →
      (∀ opponent, minimumMass ≤ (sampling opponent).toReal) →
      0 < delta → delta ≤ 1 →
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) / delta)
          20 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
            8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
              ((users : ℝ) * minimumMass) <
            |theorem11IidUserLatentBordaScore alternative sample -
              pairwiseBordaScore sampling preference alternative|) ≤ delta

/--
Simultaneous source-rate Lemma 11 confidence statement.  The source's
`δ/(4m²)` allocation is represented explicitly by `log (8m²/δ)`.
-/
def lemma11_iidUserSharpNormalizedBordaSourceRateUniformConfidence_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ (minimumMass delta : ℝ),
      0 < minimumMass →
      (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
      0 < delta → delta ≤ 1 →
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) ^ 2 / delta)
          ∃ alternative,
            20 * Real.sqrt ((users : ℝ) * logLevel /
              min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
              8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
                ((users : ℝ) * minimumMass) <
              |theorem11IidUserLatentBordaScore alternative sample -
                pairwiseBordaScore sampling preference alternative|) ≤ delta

/--
Appendix D's normalized-Borda concentration route for one alternative.  This
is an exact finite literal-user statement: user-level answers may be
arbitrarily correlated, while users are iid.  Its bounded-count Bernstein
constant is intentionally kept explicit rather than identified with the
source's later minimum-mass/big-O simplification.
-/
def lemma11_iidUserNormalizedBordaTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ alternative, 0 < (sampling alternative).toReal → ∀ cutoff : ℝ, 0 ≤ cutoff →
      cutoff ≤ (users : ℝ) *
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
          (theorem2UserBatchBordaIncidences alternative) / 2 →
      0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
        (2 * comparisonsPerUser : ℝ) * cutoff →
      pmfProb (theorem12IidBordaReportBatchLaw
        (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
        (fun sample =>
          4 * cutoff /
              ((users : ℝ) *
                pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                  (theorem2UserBatchBordaIncidences alternative)) <
            |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
                alternative sample - pairwiseBordaScore sampling preference alternative|) ≤
        4 * Real.exp (-cutoff ^ 2 /
          (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
            (2 * comparisonsPerUser : ℝ) * cutoff)))

/--
Uniform finite minimum-mass specialization of the literal Appendix D Borda
tail.  This exact range-based bound is intentionally distinct from the
source's sharper asymptotic Borda simplification.
-/
def lemma11_iidUserNormalizedBordaUniformMinMassTail_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ minimumMass cutoff : ℝ, 0 < minimumMass →
      (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
      0 ≤ cutoff → cutoff ≤
        (users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass →
      pmfProb (theorem12IidBordaReportBatchLaw
        (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
        (fun sample => ∃ alternative,
          2 * cutoff / ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) <
            |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins
                theorem2UserBatchBordaIncidences alternative sample -
              pairwiseBordaScore sampling preference alternative|) ≤
        ∑ _alternative : Alternative,
          4 * Real.exp (-cutoff ^ 2 /
            (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
              (2 * comparisonsPerUser : ℝ) * cutoff)))

/--
Finite population endpoint for source Theorem 6. In the literal Appendix-F.2
construction with the documented stronger copy count, the attained population
logistic MLE and its reward/welfare policy witnesses have an explicit
exponential distortion ratio. The finite-report MLE-order convergence question
is intentionally separate from this population theorem.
-/
def theorem6_rlhf_population_lower_boundSpec : Prop :=
  ∀ {beta : ℝ}, 10 ≤ beta →
    ∃ reward : theorem6Alternative (theorem6CopyCount beta) → ℝ,
      (∀ candidate,
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward) ∧
      ∃ rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)),
        Real.exp beta / (44 * beta) ≤
          pmfExp welfarePolicy (theorem6Welfare beta) /
            pmfExp rewardPolicy (theorem6Welfare beta)

/-- Literal finite-report MLE ordering target from Appendix F.2. -/
def theorem6_iidFiniteMLEOrder_finiteSpec : Prop :=
  ∀ {beta : ℝ}, 2 ≤ beta →
    Filter.Tendsto (theorem6FiniteMLEBadOrderProbability beta) Filter.atTop (𝓝 0)

/--
Finite population-limit target for source Theorem 7. `hnlhf` is the paper's
attained constrained `argmax min` definition on its explicit finite KL ball.
The checked finite minimax bridge derives the zero-value equilibrium inequality
used by the welfare proof, whose conclusion applies to every feasible policy,
including a welfare maximizer.
-/
def theorem7_nlhf_population_limitSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
      ∀ (reference : PMF Alternative) (klBudget : ℝ)
        (nlhfPolicy benchmark : PMF Alternative),
        IsConstrainedPopulationBradleyTerryMaximin
          population utility btScale reference klBudget nlhfPolicy →
        InFiniteKLBall reference klBudget benchmark →
          (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
              policyAverageUtility population utility benchmark ≤
            policyAverageUtility population utility nlhfPolicy

/--
Finite population-limit target for source Corollary 4. In the context-free
case, the source maximal-lottery condition is the nonnegative centered margin
against every alternative lottery.
-/
def corollary4_maximalLottery_population_limitSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
      ∀ (maximalLottery benchmark : PMF Alternative),
        (∀ opponent,
          0 ≤ populationBradleyTerryPolicyMargin population utility btScale maximalLottery opponent) →
          (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
              policyAverageUtility population utility benchmark ≤
            policyAverageUtility population utility maximalLottery

/--
Finite population-limit target for source Corollary 8. The explicit
regularized-equilibrium premise is the finite real-weight source game, and the
benchmark has no greater ordinary finite KL divergence from the reference.
-/
def corollary8_regularizedNlhf_population_limitSpec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
      ∀ (reference policy : PMF Alternative) (klRegularization : ℝ),
        0 ≤ klRegularization →
        AppliedModelingLib.GameTheory.PreferenceGame.IsRegularizedPreferenceGameEquilibrium
          (PMF.pure PUnit.unit.{1})
          (populationBradleyTerryPreference population utility btScale)
          (contextFreeAlternativePolicy reference) (contextFreeAlternativePolicy policy)
          klRegularization →
        ∀ benchmark : PMF Alternative,
          AppliedModelingLib.finiteKLDivergence benchmark reference ≤
            AppliedModelingLib.finiteKLDivergence policy reference →
            (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
                policyAverageUtility population utility benchmark ≤
              policyAverageUtility population utility policy

/--
Source-facing finite `d = 1` core of Theorem 3.  The rule sees the sampled
ordered comparison pairs and their binary outcomes, and may randomize its
output.  Some special alternative is nevertheless selected with at most
uniform probability along infinitely many horizons, yielding Eq. (11)'s
finite welfare estimate.
-/
def theorem3_d1_finiteSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon),
    ∀ (rule : ∀ horizon,
      (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative),
      ∃ special : Alternative,
        Set.Infinite {horizon : ℕ |
          let policy := theorem3ObservationSelectionLaw
            (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon
              hbeta hepsilon special horizon)
            (rule horizon)
          (policy special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹ ∧
            policyAverageUtility (theorem3TwoTypePopulation beta epsilon
              hbeta hepsilon)
              (theorem3ManyAlternativeUtility epsilon 1 special) policy ≤
                (Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
                  epsilon * theorem3OrdinaryTypeMass beta epsilon}

/--
Finite source-facing distortion endpoint for Theorem 3 with one comparison per
user.  It carries the source's `m ≥ 2` and `0 < epsilon ≤ 1 / 2` hypotheses,
identifies the hidden special alternative as welfare-maximizing, and proves the
exact Eq. (11) ratio on an infinite subsequence of horizons.
-/
def theorem3_d1_finite_distortionSpec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative],
    ∀ (hcard : 2 ≤ Fintype.card Alternative),
    ∀ (pairSampling : PMF (Alternative × Alternative))
      (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon),
      epsilon ≤ (1 : ℝ) / 2 →
      ∀ (rule : ∀ horizon,
        (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative),
        ∃ special : Alternative,
          Set.Infinite {horizon : ℕ |
            let policy := theorem3ObservationSelectionLaw
              (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon
                hbeta hepsilon special horizon)
              (rule horizon)
            (∀ alternative,
              populationAverageUtility
                (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
                (theorem3ManyAlternativeUtility epsilon 1 special) alternative ≤
                populationAverageUtility
                  (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
                  (theorem3ManyAlternativeUtility epsilon 1 special) special) ∧
              theorem3SpecialTypeMass beta epsilon /
                  ((Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
                    epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
                theorem3SpecialTypeMass beta epsilon /
                  policyAverageUtility
                    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
                    (theorem3ManyAlternativeUtility epsilon 1 special) policy}

/--
Source-facing asymptotic `d = 1` conclusion of Theorem 3.  For every
size-indexed voting-rule family and positive tolerance, all sufficiently large
alternative-set sizes contain a welfare-maximizing hidden alternative whose
distortion exceeds the stated coefficient minus that tolerance along
infinitely many sample horizons.
-/
def theorem3_d1_asymptoticSpec : Prop :=
  ∀ {beta : ℝ} (hbeta : 0 < beta),
    ∀ (pairSampling : ∀ n : ℕ, PMF (Fin (n + 2) × Fin (n + 2)))
      (rule : ∀ n horizon,
        (Fin horizon → ((Fin (n + 2) × Fin (n + 2)) × Bool)) → PMF (Fin (n + 2)))
      (delta : ℝ),
      0 < delta →
      ∃ N : ℕ, ∀ n ≥ N, ∃ special : Fin (n + 2),
        Set.Infinite {horizon : ℕ |
          let policy := theorem3ObservationSelectionLaw
            (theorem3ManyAlternativeObservationLaw (pairSampling n) beta
              (theorem3DiagonalEpsilon n) hbeta (theorem3DiagonalEpsilon_pos n)
              special horizon)
            (rule n horizon)
          (∀ alternative,
            populationAverageUtility
              (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                (theorem3DiagonalEpsilon_pos n))
              (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special)
                alternative ≤
              populationAverageUtility
                (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                  (theorem3DiagonalEpsilon_pos n))
                (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special)
                  special) ∧
            beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
              theorem3SpecialTypeMass beta (theorem3DiagonalEpsilon n) /
                policyAverageUtility
                  (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                    (theorem3DiagonalEpsilon_pos n))
                  (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special)
                  policy}

/--
Source-facing finite-sample lower-bound target for Appendix-E.2's Theorem 12.
For every `m ≥ 3` and every strict sub-bound below its Eq. (10) coefficient,
there is a literal unit-interval split instance where the low-welfare `c`
becomes the unique empirical normalized-count Borda winner with probability
tending to one under iid one-comparison user reports.
-/
def theorem12_all_m_iidBorda_lower_boundSpec : Prop :=
  ∀ {beta gamma q : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1),
    q < theorem12Eq10Coefficient beta gamma → ∀ m : ℕ, 3 ≤ m →
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
      (sampling : PMF (Fin 3 ⊕ Fin (m - 3))),
      epsilon ^ 2 < 1 - epsilon ∧ Fintype.card (Fin 3 ⊕ Fin (m - 3)) = m ∧
        let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
        let splitUtility := theorem12SplitUtility (theorem12Utility epsilon (epsilon ^ 2) gamma)
          collapse
        let population := theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
          hgamma hgamma_lt_one
        let preference := populationBradleyTerryPreference.{0, 0, 0} population splitUtility beta
        UnitIntervalUtilityProfile splitUtility ∧
          PMFFullSupport sampling ∧
          q <
            populationAverageUtility population splitUtility (Sum.inl (0 : Fin 3)) /
              populationAverageUtility population splitUtility (Sum.inl (2 : Fin 3)) ∧
          Filter.Tendsto
            (fun horizon =>
              AppliedModelingLib.pmfProb (theorem12IidBordaReportBatchLaw
                (theorem12OneComparisonReportLaw sampling preference) horizon)
                (fun sample => theorem12IidEmpiricalBordaFailure theorem12OneComparisonWins
                  theorem12OneComparisonIncidences (Sum.inl (2 : Fin 3)) sample))
            Filter.atTop (𝓝 0)

end GolzHaghtalabYang2025Distortion

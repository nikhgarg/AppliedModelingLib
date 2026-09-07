import GJ19OptimalBinaryRatingSystems.MainTheorems
import AppliedModelingLib.Foundations.Optimization.Certificate

/-!
# Source model and implementation definitions for Garg--Johari (2019)

This file records the literal model objects that were left implicit in the
earlier rate-centered development: the normalized quality space, floor match
counts, empirical scores and state measures, the atomic Appendix B.1 update,
and the finite-question design problem from Section 4.

The Appendix B.1 source writes a two-atom transition as though it had a
Lebesgue density and mixes the labels `k` and `k+1` in the displayed state
update.  We use the mathematically equivalent atomic measure and index the
transition explicitly from time `k` to time `k+1`.
-/

open scoped BigOperators ENNReal

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open MeasureTheory

/-- The source-normalized quality/rank domain: a unit mass continuum `[0,1]`. -/
def sourceQualityDomain : Set ℝ := Set.Icc (0 : ℝ) 1

/--
Source assumptions on the matching function: it is nondecreasing, bounded by
one, and bounded strictly away from zero on the quality domain.
-/
def SourceMatchingFunction (g : ℝ → ℝ) : Prop :=
  MonotoneOn g sourceQualityDomain ∧
    (∀ θ ∈ sourceQualityDomain, g θ ≤ 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ sourceQualityDomain, c < g θ

/-- The source match count `n_k(θ) = floor(k g(θ))`. -/
noncomputable def sourceMatchingCount (k : ℕ) (g : ℝ → ℝ) (θ : ℝ) : ℕ :=
  Nat.floor ((k : ℝ) * g θ)

/-- Literal source match-count formula. -/
theorem sourceMatchingCount_eq_floor (k : ℕ) (g : ℝ → ℝ) (θ : ℝ) :
    sourceMatchingCount k g θ = Nat.floor ((k : ℝ) * g θ) := rfl

/--
Theorem 3.1 cell sample rate `g_i`: the infimum of the source matching
function over the closed quality cell selected by adjacent cutpoints.
-/
noncomputable def sourceCellMatchingRate
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ) (i : Fin (m + 2)) : ℝ :=
  sInf (g '' Set.Icc (cut i.val) (cut (i.val + 1)))

/--
For a nondecreasing matching function, the cell infimum is attained at the
cell's lower cutpoint.  This closes the source bridge
`g_i = inf_{θ ∈ S_i} g(θ)` for ordered interval cells.
-/
theorem sourceCellMatchingRate_eq_lower_cutpoint
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ) (i : Fin (m + 2))
    (hcut : cut i.val ≤ cut (i.val + 1))
    (hg : MonotoneOn g (Set.Icc (cut i.val) (cut (i.val + 1)))) :
    sourceCellMatchingRate cut g i = g (cut i.val) := by
  exact hg.sInf_image_Icc hcut

/-- Ordered source cells inherit a nondecreasing finite sample-rate vector. -/
theorem sourceCellMatchingRate_mono
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ)
    (hcut : Monotone cut) (hg : Monotone g)
    {i j : Fin (m + 2)} (hij : i.val ≤ j.val) :
    sourceCellMatchingRate cut g i ≤ sourceCellMatchingRate cut g j := by
  rw [sourceCellMatchingRate_eq_lower_cutpoint cut g i
      (hcut (Nat.le_succ i.val)) (hg.monotoneOn _),
    sourceCellMatchingRate_eq_lower_cutpoint cut g j
      (hcut (Nat.le_succ j.val)) (hg.monotoneOn _)]
  exact hg (hcut hij)

/-- Source lower-bound assumptions make every selected cell rate positive. -/
theorem sourceCellMatchingRate_pos
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ) (i : Fin (m + 2))
    (hgSource : SourceMatchingFunction g)
    (hcut : cut i.val ≤ cut (i.val + 1))
    (hcut_mem : cut i.val ∈ sourceQualityDomain)
    (hcell :
      Set.Icc (cut i.val) (cut (i.val + 1)) ⊆ sourceQualityDomain) :
    0 < sourceCellMatchingRate cut g i := by
  rw [sourceCellMatchingRate_eq_lower_cutpoint cut g i
      hcut (hgSource.1.mono hcell)]
  rcases hgSource.2.2 with ⟨c, hc, hc_lower⟩
  exact hc.trans (hc_lower (cut i.val) hcut_mem)

/-- The fraction of positive ratings among the first `n` binary observations. -/
def sourceEmpiricalReputationScore (rating : ℕ → Bool) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else
    (∑ ℓ ∈ Finset.range n, if rating ℓ then (1 : ℝ) else 0) / (n : ℝ)

/-- The source convention fixes every item's initial reputation score at zero. -/
theorem sourceEmpiricalReputationScore_zero (rating : ℕ → Bool) :
    sourceEmpiricalReputationScore rating 0 = 0 := by
  simp [sourceEmpiricalReputationScore]

/-- A source system state is a measure on `(quality, reputation score)`. -/
abbrev SourceSystemState := Measure (ℝ × ℝ)

/-- The source mass notation `μ_k(Θ,X)`. -/
def sourceSystemStateMass
    (state : SourceSystemState) (Θ X : Set ℝ) : ℝ≥0∞ :=
  state (Θ ×ˢ X)

/--
Appendix B.1 active set for the transition from `k` to `k+1`: precisely the
qualities whose floor match count increases by one.
-/
def sourceAppendixBActiveSet (k : ℕ) (g : ℝ → ℝ) : Set ℝ :=
  {θ | sourceMatchingCount (k + 1) g θ = sourceMatchingCount k g θ + 1}

/-- Score after appending a binary observation to `n` previous observations. -/
def sourceScoreAfterRating (n : ℕ) (oldScore outcome : ℝ) : ℝ :=
  ((n : ℝ) * oldScore + outcome) / ((n : ℝ) + 1)

/-- Positive-outcome branch of the Appendix B.1 atomic transition. -/
theorem sourceScoreAfterRating_positive (n : ℕ) (oldScore : ℝ) :
    sourceScoreAfterRating n oldScore 1 =
      ((n : ℝ) * oldScore + 1) / ((n : ℝ) + 1) := rfl

/-- Negative-outcome branch of the Appendix B.1 atomic transition. -/
theorem sourceScoreAfterRating_negative (n : ℕ) (oldScore : ℝ) :
    sourceScoreAfterRating n oldScore 0 =
      ((n : ℝ) * oldScore) / ((n : ℝ) + 1) := by
  simp [sourceScoreAfterRating]

/--
The source transition kernel as the intended two-atom measure, replacing the
printed pseudo-density `ω(θ,x,x') dx`.
-/
def sourceAppendixBTransitionKernel
    (n : ℕ) (β : ℝ → ℝ) (θ oldScore : ℝ) : Measure ℝ :=
  ENNReal.ofReal (β θ) •
      Measure.dirac (sourceScoreAfterRating n oldScore 1) +
    ENNReal.ofReal (1 - β θ) •
      Measure.dirac (sourceScoreAfterRating n oldScore 0)

/-- The transition probability assigned to a measurable score set. -/
def sourceAppendixBTransitionMass
    (n : ℕ) (β : ℝ → ℝ) (θ oldScore : ℝ) (X : Set ℝ) : ℝ≥0∞ :=
  sourceAppendixBTransitionKernel n β θ oldScore X

/--
Appendix B.1 state-update equation, evaluated on a quality-score rectangle.
Active items are integrated against the atomic transition; inactive items
retain their old score.  This definition is the displayed source equation
with its transition/time indices repaired as described in the module note.
-/
def sourceAppendixBStateUpdateMass
    (k : ℕ) (g β : ℝ → ℝ) (state : SourceSystemState)
    (Θ X : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ z in ((Θ ∩ sourceAppendixBActiveSet k g) ×ˢ Set.univ),
      sourceAppendixBTransitionMass
        (sourceMatchingCount k g z.1) β z.1 z.2 X ∂state +
    state ((Θ \ sourceAppendixBActiveSet k g) ×ˢ X)

/-- A finite question-frequency vector is a probability distribution. -/
def SourceQuestionDistribution {Y : Type*} [Fintype Y] (H : Y → ℝ) : Prop :=
  (∀ y : Y, 0 ≤ H y) ∧ ∑ y : Y, H y = 1

/--
Section 4 induced binary response
`β̃(θ) = ∑_y ψ(θ,y) H(y)` for a finite question set.
-/
def sourceInducedBinaryResponse {Y : Type*} [Fintype Y]
    (ψ : ℝ → Y → ℝ) (H : Y → ℝ) (θ : ℝ) : ℝ :=
  ∑ y : Y, ψ θ y * H y

/-- Literal finite-mixture formula from Section 4. -/
theorem sourceInducedBinaryResponse_eq_sum {Y : Type*} [Fintype Y]
    (ψ : ℝ → Y → ℝ) (H : Y → ℝ) (θ : ℝ) :
    sourceInducedBinaryResponse ψ H θ = ∑ y : Y, ψ θ y * H y := rfl

/--
Equation (5): finite-representative `L¹` discrepancy between a target
response function and the response induced by the question mixture.
-/
def sourceQuestionDesignL1Objective
    {Representative Y : Type*} [Fintype Representative] [Fintype Y]
    (quality : Representative → ℝ) (β : ℝ → ℝ)
    (ψHat : Representative → Y → ℝ) (H : Y → ℝ) : ℝ :=
  ∑ i : Representative,
    |β (quality i) - ∑ y : Y, ψHat i y * H y|

/--
A solution of the source Section 4 design heuristic is a probability vector
minimizing equation (5).
-/
def SourceQuestionDesignSolution
    {Representative Y : Type*} [Fintype Representative] [Fintype Y]
    (quality : Representative → ℝ) (β : ℝ → ℝ)
    (ψHat : Representative → Y → ℝ) (H : Y → ℝ) : Prop :=
  AppliedModelingLib.Optimization.IsMinimizerOn
    (SourceQuestionDistribution : (Y → ℝ) → Prop)
    (sourceQuestionDesignL1Objective quality β ψHat) H

/--
Raw data from the source experiment: on every match, each item receives one
randomly selected question and a binary response to that question.
-/
structure SourceRandomQuestionExperiment
    (Ω Item Y : Type*) where
  question : Item → ℕ → Ω → Y
  positiveResponse : Item → ℕ → Ω → Bool

/-- Indicator that match `n` of item `i` used question `y`. -/
def sourceQuestionAskedIndicator
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (n : ℕ) (ω : Ω) : ℝ :=
  if E.question i n ω = y then 1 else 0

/-- Indicator that question `y` was asked and received a positive response. -/
def sourceQuestionPositiveIndicator
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (n : ℕ) (ω : Ω) : ℝ :=
  if E.question i n ω = y ∧ E.positiveResponse i n ω = true then 1 else 0

/-- Binary positive-score indicator, irrespective of which question was drawn. -/
def sourceAggregatePositiveIndicator
    {Ω Item Y : Type*}
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (n : ℕ) (ω : Ω) : ℝ :=
  if E.positiveResponse i n ω then 1 else 0

/-- Number of the first `N` matches of item `i` assigned to question `y`. -/
def sourceExperimentQuestionCount
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range N, sourceQuestionAskedIndicator E i y n ω

/-- Number of positive responses among those question-`y` matches. -/
def sourceExperimentPositiveQuestionCount
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range N, sourceQuestionPositiveIndicator E i y n ω

/--
The empirical response frequency tracked by the source experiments: positive
question-`y` responses divided by the number of times question `y` was asked.
Lean's total division convention makes the value zero before the first such
question; positive question mass makes that transient convention irrelevant.
-/
def sourceExperimentEmpiricalQuestionResponse
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (N : ℕ) (ω : Ω) : ℝ :=
  sourceExperimentPositiveQuestionCount E i y N ω /
    sourceExperimentQuestionCount E i y N ω

/-- Expected aggregate positive score under a finite question mixture. -/
def sourceExpectedAggregateScore {Y : Type*} [Fintype Y]
    (ψ : ℝ → Y → ℝ) (H : Y → ℝ) (θ : ℝ) : ℝ :=
  ∑ y : Y, H y * ψ θ y

/--
The source KnownTypeExperiment data: known representative qualities and their
empirical question-response frequencies.
-/
structure SourceKnownTypeExperiment
    (Representative Y : Type*) [Fintype Representative] [Fintype Y] where
  quality : Representative → ℝ
  empiricalResponse : ℕ → Representative → Y → ℝ

/--
The source UnknownTypeExperiment data: unknown true qualities, empirical
question responses, empirical aggregate scores, and the resulting rank order.
The rank map sends a percentile position to the item occupying that rank.
-/
structure SourceUnknownTypeExperiment
    (Item Y : Type*) [Fintype Item] [Fintype Y] where
  trueQuality : Item → ℝ
  empiricalResponse : ℕ → Item → Y → ℝ
  empiricalAverageScore : ℕ → Item → ℝ
  rankedItem : ℕ → Item → Item

end

end GJ19OptimalBinaryRatingSystems
